//! Literal lowering of every currently admitted pure expression. No AST runtime.
use crate::{check, syntax::*, LangResult};
use std::collections::BTreeMap;
type Env = BTreeMap<String, (String, Type)>;
struct Emitter<'a> {
    p: &'a Program,
    next: usize,
}
impl Emitter<'_> {
    fn fresh(&mut self) -> String {
        let n = format!("ink_local_{}", self.next);
        self.next += 1;
        n
    }
    fn infer(&self, e: &Expr, env: &Env, want: Option<&Type>) -> LangResult<Type> {
        check::infer_context(
            e,
            &env.iter()
                .map(|(k, (_, t))| (k.clone(), t.clone()))
                .collect(),
            self.p,
            want,
        )
    }
    fn arithmetic(op: &str, a: &str, b: &str, t: &Type) -> String {
        if check::is_word(t) {
            format!(
                "({a}).{}({b})",
                match op {
                    "+" => "wrapping_add",
                    "-" => "wrapping_sub",
                    _ => "wrapping_mul",
                }
            )
        } else {
            format!("(({a}) {op} ({b}))")
        }
    }
    fn zero(t: &Type) -> String {
        match t {
            Type::F32 => "0.0f32".into(),
            Type::I32 => "0i32".into(),
            Type::U32 => "0u32".into(),
            _ => "0u64".into(),
        }
    }
    fn lambda(
        &mut self,
        e: &Expr,
        env: &Env,
        params: &[Type],
        result: &Type,
    ) -> LangResult<(Vec<String>, String)> {
        let mut local = env.clone();
        let mut vars = vec![];
        let mut body = e;
        for t in params {
            let Expr::Lambda(n, b) = body else {
                return Err("typed lambda required".into());
            };
            let v = self.fresh();
            local.insert(n.clone(), (v.clone(), t.clone()));
            vars.push(v);
            body = b;
        }
        Ok((vars, self.expr(body, &local, Some(result))?))
    }
    fn expr(&mut self, e: &Expr, env: &Env, want: Option<&Type>) -> LangResult<String> {
        let t = self.infer(e, env, want)?;
        Ok(match e {
            Expr::Num(n) => match t {
                Type::U32 => format!("{n}u32"),
                Type::I32 => format!("{n}i32"),
                Type::F32 => format!("f32::from_bits({}u32)", (*n as f32).to_bits()),
                _ => format!("{n}u64"),
            },
            Expr::Float(b) => format!("f32::from_bits({b}u32)"),
            Expr::Bool(b) => b.to_string(),
            Expr::Var(n) => {
                let v = &env.get(n).ok_or("missing binding")?.0;
                if ink_core::local_collections::owned(&t, self.p) {
                    v.clone()
                } else {
                    format!("{v}.clone()")
                }
            }
            Expr::Neg(x) => {
                if let (Type::I32, Expr::Num(2147483648)) = (&t, x.as_ref()) {
                    return Ok("i32::MIN".into());
                }
                let x = self.expr(x, env, Some(&t))?;
                if t == Type::F32 {
                    format!("f32::from_bits(({x}).to_bits() ^ 0x80000000)")
                } else {
                    format!("({x}).wrapping_neg()")
                }
            }
            Expr::Let(n, annotation, a, b) => {
                let at = self.infer(a, env, annotation.as_deref())?;
                let a = self.expr(a, env, Some(&at))?;
                let v = self.fresh();
                let mut local = env.clone();
                let annotation = crate::state_native::ty(&at)?;
                local.insert(n.clone(), (v.clone(), at));
                let b = self.expr(b, &local, Some(&t))?;
                format!("{{let {v}:{annotation}={a};{b}}}")
            }
            Expr::Record(n, fields) => {
                // Evaluate in source order, even when declaration order differs.
                let mut bindings = String::new();
                let mut fs = vec![];
                for (k, e) in fields {
                    let ft = &self.p.records[n]
                        .iter()
                        .find(|(f, _)| f == k)
                        .ok_or("record field")?
                        .1;
                    let value = self.expr(e, env, Some(ft))?;
                    let value = if crate::state_native::boxed_field(n, ft, self.p) {
                        format!("Box::new({value})")
                    } else {
                        value
                    };
                    let v = self.fresh();
                    bindings.push_str(&format!("let {v}={value};"));
                    fs.push(format!("l_{k}:{v}"));
                }
                format!("{{{bindings}l_{n}{{{}}}}}", fs.join(","))
            }
            Expr::Field(x, n) => {
                let xt = self.infer(x, env, None)?;
                let x = self.expr(x, env, None)?;
                if matches!(xt, Type::Vector(..)) {
                    let i = ["x", "y", "z", "w"]
                        .iter()
                        .position(|f| *f == n)
                        .ok_or("component")?;
                    format!("({x})[{i}].clone()")
                } else {
                    let Type::Named(owner) = xt else {
                        return Err("record type".into());
                    };
                    let ft = &self.p.records[&owner]
                        .iter()
                        .find(|(f, _)| f == n)
                        .ok_or("field")?
                        .1;
                    if ink_core::local_collections::owned(ft, self.p) {
                        if crate::state_native::boxed_field(&owner, ft, self.p) {
                            format!("*({x}).l_{n}")
                        } else {
                            format!("({x}).l_{n}")
                        }
                    } else if crate::state_native::boxed_field(&owner, ft, self.p) {
                        format!("(*({x}).l_{n}).clone()")
                    } else {
                        format!("({x}).l_{n}.clone()")
                    }
                }
            }
            Expr::Binary(op, a, b) => {
                let types = env
                    .iter()
                    .map(|(n, (_, t))| (n.clone(), t.clone()))
                    .collect();
                let at = if check::is_number(&t) {
                    t.clone()
                } else {
                    self.infer(
                        a,
                        env,
                        check::hint(a, &types, self.p)
                            .or_else(|| check::hint(b, &types, self.p))
                            .as_ref(),
                    )?
                };
                let a = self.expr(a, env, Some(&at))?;
                let b = self.expr(b, env, Some(&at))?;
                if ["+", "-", "*"].contains(&op.as_str()) {
                    Self::arithmetic(op, &a, &b, &at)
                } else {
                    format!("(({a}) {op} ({b}))")
                }
            }
            Expr::Call(n, args) if ["vec2", "vec3", "vec4"].contains(&n.as_str()) => {
                let Type::Vector(inner, _) = &t else {
                    return Err("vector type".into());
                };
                format!(
                    "[{}]",
                    args.iter()
                        .map(|e| self.expr(e, env, Some(inner)))
                        .collect::<LangResult<Vec<_>>>()?
                        .join(",")
                )
            }
            Expr::Call(n, args) if n == "choose" => format!(
                "if {} {{{}}} else {{{}}}",
                self.expr(&args[0], env, Some(&Type::Bool))?,
                self.expr(&args[1], env, Some(&t))?,
                self.expr(&args[2], env, Some(&t))?
            ),
            Expr::Call(n, args) if n == "quot_or" || n == "rem_or" => {
                let a = self.expr(&args[0], env, Some(&t))?;
                let b = self.expr(&args[1], env, Some(&t))?;
                let fallback = self.expr(&args[2], env, Some(&t))?;
                let av = self.fresh();
                let bv = self.fresh();
                let overflow = if t == Type::I32 {
                    format!("||({av}==i32::MIN && {bv} == -1)")
                } else {
                    String::new()
                };
                format!("{{let {av}={a};let {bv}={b};if {bv}==0 {overflow} {{{fallback}}} else {{{av} {} {bv}}}}}",if n=="quot_or"{"/"}else{"%"})
            }
            Expr::Call(n, args) if n == "length" => {
                let xs = if let Expr::Var(n) = &args[0] {
                    env.get(n).ok_or("list binding")?.0.clone()
                } else {
                    self.expr(&args[0], env, None)?
                };
                format!("({xs}).len() as u32")
            }
            Expr::Call(n, args) if n == "repeat_until" => {
                let limit = self.expr(&args[0], env, Some(&Type::U32))?;
                let initial = self.expr(&args[1], env, Some(&t))?;
                let (stopvars, stop) = self.lambda(&args[2], env, &[t.clone()], &Type::Bool)?;
                let (vs, body) = self.lambda(&args[3], env, &[Type::U32, t.clone()], &t)?;
                let acc = self.fresh();
                let bound = self.fresh();
                let observed = if ink_core::local_collections::owned(&t, self.p) {
                    format!("&{acc}")
                } else {
                    format!("{acc}.clone()")
                };
                format!("{{let {bound}={limit};let mut {acc}={initial};for {} in 0..{bound} {{let {}={observed};if {stop} {{break;}}let {}={acc};{acc}={body};}}{acc}}}",vs[0],stopvars[0],vs[1])
            }
            Expr::Call(n, args) if n == "buffer" || n == "buffer_fill" => {
                let Type::Buffer(inner) = &t else {
                    unreachable!()
                };
                if n == "buffer" {
                    format!(
                        "OwnedBuffer::new({})",
                        self.expr(&args[0], env, Some(&Type::List(inner.clone())))?
                    )
                } else {
                    let len = self.expr(&args[0], env, Some(&Type::U32))?;
                    let value = self.expr(&args[1], env, Some(inner))?;
                    let lv = self.fresh();
                    let vv = self.fresh();
                    format!("{{let {lv}={len};let {vv}={value};OwnedBuffer::new(vec![{vv};{lv} as usize])}}")
                }
            }
            Expr::Method(x, n, args) if matches!(x.as_ref(),Expr::Var(v) if v=="Buffer" || v=="Map") =>
            {
                format!(
                    "{}::new({})",
                    if matches!(t, Type::Buffer(_)) {
                        "OwnedBuffer"
                    } else {
                        "OwnedMap"
                    },
                    if matches!(t, Type::Buffer(_)) {
                        "vec![]"
                    } else {
                        ""
                    }
                )
            }
            Expr::Method(x, n, args)
                if matches!(self.infer(x, env, None)?, Type::Buffer(_) | Type::Map(..)) =>
            {
                let xt = self.infer(x, env, None)?;
                let xv = self.expr(x, env, None)?;
                let (key, value) = match &xt {
                    Type::Buffer(inner) => (Type::U32, inner.as_ref()),
                    Type::Map(k, v) => (*k.clone(), v.as_ref()),
                    _ => unreachable!(),
                };
                match n.as_str() {
                    "len" | "pop" | "freeze" | "keys" | "values" => format!("({xv}).{n}()"),
                    "at_or" | "get_or" => {
                        let k = self.expr(&args[0], env, Some(&key))?;
                        let fallback = self.expr(&args[1], env, Some(value))?;
                        format!(
                            "({xv}).get({}{k}).unwrap_or_else(||{fallback})",
                            if matches!(xt, Type::Map(..)) { "&" } else { "" }
                        )
                    }
                    "set" => {
                        let k = self.expr(&args[0], env, Some(&key))?;
                        let v = self.expr(&args[1], env, Some(value))?;
                        format!("({xv}).set({k},{v})")
                    }
                    "swap" => {
                        let a = self.expr(&args[0], env, Some(&Type::U32))?;
                        let b = self.expr(&args[1], env, Some(&Type::U32))?;
                        format!("({xv}).swap({a},{b})")
                    }
                    "push" => format!("({xv}).push({})", self.expr(&args[0], env, Some(value))?),
                    "truncate" => format!(
                        "({xv}).truncate({})",
                        self.expr(&args[0], env, Some(&Type::U32))?
                    ),
                    "contains" | "remove" => {
                        format!("({xv}).{n}(&{})", self.expr(&args[0], env, Some(&key))?)
                    }
                    _ => return Err("temporary method".into()),
                }
            }
            Expr::Call(n, args) if n == "repeat" => {
                let Expr::Num(bound) = args[0] else {
                    return Err("loop bound".into());
                };
                let initial = self.expr(&args[1], env, Some(&t))?;
                let (vs, body) = self.lambda(&args[2], env, &[Type::U32, t.clone()], &t)?;
                let acc = self.fresh();
                format!("{{let mut {acc}={initial};for {} in 0..{bound}u32 {{let {}={acc};{acc}={body};}}{acc}}}",vs[0],vs[1])
            }
            Expr::Call(n, args) if n == "foldr" => {
                let Type::List(inner) = self.infer(&args[0], env, None)? else {
                    return Err("fold input".into());
                };
                let xs = self.expr(&args[0], env, None)?;
                let initial = self.expr(&args[1], env, Some(&t))?;
                let (vs, body) = self.lambda(&args[2], env, &[*inner, t.clone()], &t)?;
                let list = self.fresh();
                let acc = self.fresh();
                format!("{{let {list}={xs};let mut {acc}={initial};for {} in {list}.into_iter().rev() {{let {}={acc};{acc}={body};}}{acc}}}",vs[0],vs[1])
            }
            Expr::Call(n, args) if n == "sum" || n == "count" => {
                let context = if n == "sum" {
                    Some(Type::List(Box::new(t.clone())))
                } else {
                    None
                };
                let xs = self.expr(&args[0], env, context.as_ref())?;
                if n == "count" {
                    format!("({xs}).len() as u64")
                } else {
                    let acc = self.fresh();
                    let item = self.fresh();
                    format!(
                        "({xs}).into_iter().fold({},|{acc},{item}|{})",
                        Self::zero(&t),
                        Self::arithmetic("+", &acc, &item, &t)
                    )
                }
            }
            Expr::Call(n, args) => {
                let f = self
                    .p
                    .functions
                    .iter()
                    .find(|f| &f.name == n)
                    .ok_or("unknown function")?
                    .clone();
                let mut bindings = String::new();
                let mut argv = vec![];
                for (e, (_, t)) in args.iter().zip(&f.params) {
                    let e = self.expr(e, env, Some(t))?;
                    let v = self.fresh();
                    bindings.push_str(&format!("let {v}={e};"));
                    argv.push(v)
                }
                format!("{{{bindings}self.function_l_{n}({})}}", argv.join(","))
            }
            Expr::Method(xs, n, args) => {
                let Type::List(inner) =
                    self.infer(xs, env, if n == "filter" { Some(&t) } else { None })?
                else {
                    return Err("list receiver".into());
                };
                let xs = self.expr(xs, env, None)?;
                match n.as_str() {
                    "at_or" => {
                        let index = self.expr(&args[0], env, Some(&Type::U32))?;
                        let fallback = self.expr(&args[1], env, Some(&t))?;
                        let list = self.fresh();
                        let i = self.fresh();
                        let xs = if let Expr::Method(input, _, _) = e {
                            if let Expr::Var(n) = input.as_ref() {
                                format!("&{}", env.get(n).ok_or("list binding")?.0)
                            } else {
                                xs
                            }
                        } else {
                            xs
                        };
                        format!("{{let {list}={xs};let {i}={index};match {list}.get({i} as usize){{Some(v)=>v.clone(),None=>{fallback}}}}}")
                    }
                    "sort" => {
                        let list = self.fresh();
                        format!("{{let mut {list}={xs};{list}.sort();{list}}}")
                    }
                    "scan" => {
                        let list = self.fresh();
                        let acc = self.fresh();
                        let item = self.fresh();
                        format!("{{let {list}={xs};let mut {acc}={};{list}.into_iter().map(|{item}|{{{acc}={};{acc}}}).collect::<Vec<_>>()}}",Self::zero(&inner),Self::arithmetic("+",&acc,&item,&inner))
                    }
                    "map" | "filter" | "map_indexed" => {
                        let output = if n == "filter" {
                            Type::Bool
                        } else {
                            let Type::List(out) = &t else {
                                return Err("map output".into());
                            };
                            *out.clone()
                        };
                        let params = if n == "map_indexed" {
                            vec![Type::U32, *inner]
                        } else {
                            vec![*inner]
                        };
                        let (vs, body) = self.lambda(&args[0], env, &params, &output)?;
                        if n == "filter" {
                            format!("({xs}).into_iter().filter(|ink_ref|{{let {}=ink_ref.clone();{body}}}).collect::<Vec<_>>()",vs[0])
                        } else if n == "map_indexed" {
                            format!("({xs}).into_iter().enumerate().map(|(ink_i,{})|{{let {}=ink_i as u32;{body}}}).collect::<Vec<_>>()",vs[1],vs[0])
                        } else {
                            format!(
                                "({xs}).into_iter().map(|{}|{body}).collect::<Vec<_>>()",
                                vs[0]
                            )
                        }
                    }
                    "zip" => {
                        let Type::List(other) = self.infer(&args[0], env, None)? else {
                            return Err("zip input".into());
                        };
                        let Type::List(out) = &t else {
                            return Err("zip output".into());
                        };
                        let ys = self.expr(&args[0], env, None)?;
                        let (vs, body) = self.lambda(&args[1], env, &[*inner, *other], out)?;
                        let a = self.fresh();
                        let b = self.fresh();
                        format!("{{let {a}={xs};let {b}={ys};{a}.into_iter().zip({b}).map(|({},{})|{body}).collect::<Vec<_>>()}}",vs[0],vs[1])
                    }
                    _ => return Err(format!("unsupported pure method {n}")),
                }
            }
            _ => return Err("expression outside pure checked language".into()),
        })
    }
}
pub fn body(p: &Program, f: &Function) -> LangResult<String> {
    let env = f
        .params
        .iter()
        .map(|(n, t)| (n.clone(), (format!("l_{n}"), t.clone())))
        .collect();
    Emitter { p, next: 0 }.expr(&f.body, &env, Some(&f.result))
}
