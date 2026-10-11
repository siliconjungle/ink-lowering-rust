//! Literal lowering of every currently admitted pure expression. No AST runtime.
use crate::{check, syntax::*, LangResult};
use std::collections::BTreeMap;
type Env = BTreeMap<String, (String, Type)>;
fn references(e: &Expr, name: &str) -> bool {
    match e {
        Expr::Var(n) => n == name,
        Expr::Let(n, _, a, b) => references(a, name) || (n != name && references(b, name)),
        Expr::Lambda(n, b) => n != name && references(b, name),
        Expr::Neg(a) | Expr::Field(a, _) | Expr::Try(a) => references(a, name),
        Expr::Binary(_, a, b) => references(a, name) || references(b, name),
        Expr::Call(_, a) => a.iter().any(|a| references(a, name)),
        Expr::Method(a, _, b) => references(a, name) || b.iter().any(|b| references(b, name)),
        Expr::Record(_, fs) => fs.iter().any(|(_, e)| references(e, name)),
        Expr::Num(_) | Expr::Float(_) | Expr::Bool(_) | Expr::String(_) | Expr::Unit => false,
    }
}
struct Emitter<'a> {
    p: &'a Program,
    next: usize,
    prefix: String,
    tasks: Vec<(String, String)>,
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
        } else if *t == Type::F32 {
            format!("temporary::ink_f32(({a}) {op} ({b}))")
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
    // Read-only traversals borrow a lexical list instead of cloning the entire
    // vector. Computed receivers still finish eagerly and are consumed once.
    fn read_iterator(e: &Expr, value: &str, env: &Env) -> LangResult<String> {
        Ok(if let Expr::Var(n) = e {
            format!("({}).iter().cloned()", env.get(n).ok_or("list binding")?.0)
        } else {
            format!("({value}).into_iter()")
        })
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
    fn parallel(
        &mut self,
        xs: String,
        grain: String,
        callback: &Expr,
        env: &Env,
        input: &Type,
        output: &Type,
        update: bool,
    ) -> LangResult<String> {
        let (vars, body) = self.lambda(callback, env, &[Type::U32, input.clone()], output)?;
        let fresh = self.fresh();
        let name = format!("{}_{fresh}", self.prefix);
        let captures: Vec<_> = env
            .iter()
            .filter(|(n, (_, t))| {
                references(callback, n) && !ink_core::local_collections::owned(t, self.p)
            })
            .collect();
        let mut local = Env::new();
        let mut bindings = String::new();
        for (i, (n, (_, t))) in captures.iter().enumerate() {
            let v = self.fresh();
            bindings.push_str(&format!(
                "let {v}=<{} as Wire>::from_json(&captures[{i}])?;",
                crate::state_native::ty(t)?
            ));
            local.insert((*n).clone(), (v, t.clone()));
        }
        let (worker_vars, worker_body) =
            self.lambda(callback, &local, &[Type::U32, input.clone()], output)?;
        let method = format!("parallel_task_{name}");
        self.tasks.push((name.clone(),format!("#[cfg(target_arch=\"wasm32\")] fn {method}(&self,start:u32,items:&[Json],captures:&[Json])->Result<Json,String>{{if captures.len()!={}{{return Err(\"parallel capture count\".into());}}{bindings}let mut out=Vec::with_capacity(items.len());for (i,item) in items.iter().enumerate(){{let {}=start.checked_add(i.try_into().map_err(|_|\"parallel index\")?).ok_or(\"parallel index\")?;let {}=<{} as Wire>::from_json(item)?;let value:{}={worker_body};out.push(value.to_json());}}Ok(Json::Array(out))}}",captures.len(),worker_vars[0],worker_vars[1],crate::state_native::ty(input)?,crate::state_native::ty(output)?)));
        let native = format!(
            "{}(xs,grain,|{},{}|{{{body}}})",
            if update {
                "ink_parallel_update"
            } else {
                "ink_parallel_map"
            },
            vars[0],
            vars[1]
        );
        let captured = captures
            .iter()
            .map(|(_, (v, _))| format!("({v}).to_json()"))
            .collect::<Vec<_>>()
            .join(",");
        let wasm=format!("if temporary::ink_parallel_nested()||xs.len()<2||xs.len()/(grain.max(1) as usize)<2{{{native}}}else{{let result=__ink_parallel_host(json!({{\"callback\":{name:?},\"items\":xs.iter().map(Wire::to_json).collect::<Vec<_>>(),\"captures\":[{captured}],\"grain\":grain}})).expect(\"parallel host failed\");result.as_array().expect(\"parallel result array\").iter().map(<{} as Wire>::from_json).collect::<Result<Vec<_>,_>>().expect(\"parallel result value\")}}",crate::state_native::ty(output)?);
        let native_block = format!("#[cfg(not(target_arch=\"wasm32\"))]{{{native}}}");
        let wasm_block = format!("#[cfg(target_arch=\"wasm32\")]{{{wasm}}}");
        Ok(format!(
            "{{let xs={xs};let grain={grain};{native_block}{wasm_block}}}"
        ))
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
            Expr::Call(n, args) if n == "parallel_map" => {
                let Type::List(input) = self.infer(&args[0], env, None)? else {
                    unreachable!()
                };
                let Type::List(output) = &t else {
                    unreachable!()
                };
                let xs = self.expr(&args[0], env, None)?;
                let grain = self.expr(&args[1], env, Some(&Type::U32))?;
                self.parallel(xs, grain, &args[2], env, &input, output, false)?
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
                    "map_parallel" => {
                        let grain = self.expr(&args[0], env, Some(&Type::U32))?;
                        let mapped = self.parallel(
                            format!("({xv}).freeze()"),
                            grain,
                            &args[1],
                            env,
                            value,
                            value,
                            true,
                        )?;
                        format!("OwnedBuffer::new({mapped})")
                    }
                    "split_at" => {
                        let at = self.expr(&args[0], env, Some(&Type::U32))?;
                        let (vs, body) =
                            self.lambda(&args[1], env, &[xt.clone(), xt.clone()], &xt)?;
                        format!("{{let ({},{})=({xv}).split({at});{body}}}", vs[0], vs[1])
                    }
                    "append" => format!("({xv}).append({})", self.expr(&args[0], env, Some(&xt))?),
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
                let iterator = Self::read_iterator(&args[0], &xs, env)?;
                let initial = self.expr(&args[1], env, Some(&t))?;
                let (vs, body) = self.lambda(&args[2], env, &[*inner, t.clone()], &t)?;
                let acc = self.fresh();
                let list = self.fresh();
                format!("{{let {list}={iterator};let mut {acc}={initial};for {} in {list}.rev() {{let {}={acc};{acc}={body};}}{acc}}}",vs[0],vs[1])
            }
            Expr::Call(n, args) if n == "sum" || n == "count" => {
                let context = if n == "sum" {
                    Some(Type::List(Box::new(t.clone())))
                } else {
                    None
                };
                let xs = self.expr(&args[0], env, context.as_ref())?;
                if n == "count" {
                    let value = if let Expr::Var(n) = &args[0] {
                        env.get(n).ok_or("list binding")?.0.clone()
                    } else { xs };
                    format!("({value}).len() as u64")
                } else {
                    let iterator = Self::read_iterator(&args[0], &xs, env)?;
                    let acc = self.fresh();
                    let item = self.fresh();
                    format!(
                        "({iterator}).fold({},|{acc},{item}|{})",
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
            Expr::Method(xs, n, args) if n == "concat" => {
                // Borrow variable operands directly. Computed operands are evaluated
                // once and their temporaries live through the two result copies.
                let left = if let Expr::Var(n) = xs.as_ref() {
                    format!("&{}", env.get(n).ok_or("list binding")?.0)
                } else {
                    format!("&({})", self.expr(xs, env, Some(&t))?)
                };
                let right = if let Expr::Var(n) = &args[0] {
                    format!("&{}", env.get(n).ok_or("list binding")?.0)
                } else {
                    format!("&({})", self.expr(&args[0], env, Some(&t))?)
                };
                let a = self.fresh();
                let b = self.fresh();
                let out = self.fresh();
                format!("{{let {a}={left};let {b}={right};let mut {out}=Vec::with_capacity({a}.len().checked_add({b}.len()).expect(\"concat allocation size overflow\"));{out}.extend_from_slice({a});{out}.extend_from_slice({b});{out}}}")
            }
            Expr::Method(xs, n, args) => {
                let reuse = ink_core::collection_facts::reusable_private_receiver(
                    self.p, e, &env.iter().map(|(n, (_, t))| (n.clone(), t.clone())).collect(), Some(&t)
                );
                let Type::List(inner) =
                    self.infer(xs, env, if n == "filter" { Some(&t) } else { None })?
                else {
                    return Err("list receiver".into());
                };
                let receiver = xs.as_ref();
                let xs = self.expr(receiver, env, None)?;
                let iterator = Self::read_iterator(receiver, &xs, env)?;
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
                    "drop" | "take" => {
                        let k = self.expr(&args[0], env, Some(&Type::U32))?;
                        let list = self.fresh();
                        let count = self.fresh();
                        let edit = if n == "drop" {
                            format!("{list}.drain(..{count});")
                        } else {
                            format!("{list}.truncate({count});")
                        };
                        format!("{{let mut {list}={xs};let {count}=({k} as usize).min({list}.len());{edit}{list}}}")
                    }
                    "sort" => {
                        let list = self.fresh();
                        format!("{{let mut {list}={xs};{list}.sort();{list}}}")
                    }
                    "scan" => {
                        let list = self.fresh();
                        let acc = self.fresh();
                        let item = self.fresh();
                        if reuse {
                            format!("{{let mut {list}={xs};let mut {acc}={};for {item} in {list}.iter_mut(){{{acc}={};*{item}={acc};}}{list}}}",Self::zero(&inner),Self::arithmetic("+",&acc,&format!("*{item}"),&inner))
                        } else {
                            format!("{{let mut {acc}={};({iterator}).map(|{item}|{{{acc}={};{acc}}}).collect::<Vec<_>>()}}",Self::zero(&inner),Self::arithmetic("+",&acc,&item,&inner))
                        }
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
                        if reuse {
                            let list = self.fresh();
                            if n == "filter" {
                                format!("{{let mut {list}={xs};{list}.retain(|ink_ref|{{let {}=ink_ref.clone();{body}}});{list}}}",vs[0])
                            } else {
                                let i = self.fresh();
                                let index = if n == "map_indexed" { format!("let {}={i} as u32;",vs[0]) } else { String::new() };
                                let item = if n == "map_indexed" { &vs[1] } else { &vs[0] };
                                format!("{{let mut {list}={xs};for {i} in 0..{list}.len(){{{index}let {item}={list}[{i}].clone();{list}[{i}]={body};}}{list}}}")
                            }
                        } else if n == "filter" {
                            format!("({iterator}).filter(|ink_ref|{{let {}=ink_ref.clone();{body}}}).collect::<Vec<_>>()",vs[0])
                        } else if n == "map_indexed" {
                            format!("({iterator}).enumerate().map(|(ink_i,{})|{{let {}=ink_i as u32;{body}}}).collect::<Vec<_>>()",vs[1],vs[0])
                        } else {
                            format!(
                                "({iterator}).map(|{}|{body}).collect::<Vec<_>>()",
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
                        let right_iterator = Self::read_iterator(&args[0], &ys, env)?;
                        let (vs, body) = self.lambda(&args[1], env, &[*inner, *other], out)?;
                        let a = self.fresh();
                        let b = self.fresh();
                        format!("{{let {a}={iterator};let {b}={right_iterator};{a}.zip({b}).map(|({},{})|{body}).collect::<Vec<_>>()}}",vs[0],vs[1])
                    }
                    _ => return Err(format!("unsupported pure method {n}")),
                }
            }
            _ => return Err("expression outside pure checked language".into()),
        })
    }
}
impl Emitter<'_> {
    fn tail(&mut self, e: &Expr, env: &Env, f: &Function) -> LangResult<String> {
        Ok(match e {
            Expr::Let(n, annotation, a, b) => {
                let t = self.infer(a, env, annotation.as_deref())?;
                let value = self.expr(a, env, Some(&t))?;
                let v = self.fresh();
                let mut local = env.clone();
                local.insert(n.clone(), (v.clone(), t));
                format!("let {v}={value};{}", self.tail(b, &local, f)?)
            }
            Expr::Call(n, a) if n == "choose" => format!(
                "if {} {{{}}}else{{{}}}",
                self.expr(&a[0], env, Some(&Type::Bool))?,
                self.tail(&a[1], env, f)?,
                self.tail(&a[2], env, f)?
            ),
            Expr::Call(n, a) if n == &f.name => {
                let mut out = String::new();
                let mut vs = vec![];
                for (a, (_, t)) in a.iter().zip(&f.params) {
                    let value = self.expr(a, env, Some(t))?;
                    let v = self.fresh();
                    out.push_str(&format!("let {v}={value};"));
                    vs.push(v);
                }
                for ((n, _), v) in f.params.iter().zip(vs) {
                    out.push_str(&format!("l_{n}={v};"));
                }
                out.push_str("continue;");
                out
            }
            _ => format!("return {};", self.expr(e, env, Some(&f.result))?),
        })
    }
}

#[cfg(test)]
pub fn body(p: &Program, f: &Function) -> LangResult<String> {
    Ok(body_with_tasks(p, f)?.0)
}
pub fn body_with_tasks(p: &Program, f: &Function) -> LangResult<(String, Vec<(String, String)>)> {
    let env = f
        .params
        .iter()
        .map(|(n, t)| (n.clone(), (format!("l_{n}"), t.clone())))
        .collect();
    let mut emitter = Emitter {
        p,
        next: 0,
        prefix: f.name.clone(),
        tasks: Vec::new(),
    };
    if !ink_core::recursion::recursive(f) {
        let body = emitter.expr(&f.body, &env, Some(&f.result))?;
        return Ok((body, emitter.tasks));
    }
    let binds = f
        .params
        .iter()
        .map(|(n, _)| format!("let mut l_{n}=l_{n};"))
        .collect::<String>();
    let tail = emitter.tail(&f.body, &env, f)?;
    Ok((format!("{{{binds}loop{{{tail}}}}}"), emitter.tasks))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{
        fs,
        process::Command,
        time::{SystemTime, UNIX_EPOCH},
    };

    #[test]
    fn concat_borrows_operands_and_copies_each_element_once_into_a_fresh_vec() {
        let p = parse(r#"module concatenate;
            record Item { key: u32, }
            fn words(a: List<u32>, b: List<u32>) -> List<u32> { return a.concat(b); }
            fn wide(a: List<u64>, b: List<u64>) -> List<u64> { return a.concat(b); }
            fn flags(a: List<Bool>, b: List<Bool>) -> List<Bool> { return a.concat(b); }
            fn texts(a: List<String>, b: List<String>) -> List<String> { return a.concat(b); }
            fn nested(a: List<List<u32>>, b: List<List<u32>>) -> List<List<u32>> { return a.concat(b); }
            fn records(a: List<Item>, b: List<Item>) -> List<Item> { return a.concat(b); }
            fn computed(a: List<u32>, b: List<u32>, flag: Bool) -> List<u32> { return choose(flag,a,b).concat(b); }
            fn contextual(a: List<u32>, b: List<u32>) -> List<u32> { return a.map(fn(x) => 0).concat(b); }
        "#).unwrap();
        check::check(&p).unwrap();
        let mut rust = String::from(
            r#"
#![allow(non_camel_case_types)]
use std::sync::atomic::{AtomicUsize, Ordering};
static COPIES: AtomicUsize = AtomicUsize::new(0);
#[derive(Debug, PartialEq)] struct l_Item { l_key:u32 }
impl Clone for l_Item { fn clone(&self)->Self { COPIES.fetch_add(1,Ordering::Relaxed);Self{l_key:self.l_key} } }
"#,
        );
        for (name, t) in [
            ("words", "u32"),
            ("wide", "u64"),
            ("flags", "bool"),
            ("texts", "String"),
            ("nested", "Vec<u32>"),
            ("records", "l_Item"),
        ] {
            let f = p.functions.iter().find(|f| f.name == name).unwrap();
            let emitted = body(&p, f).unwrap();
            assert!(!emitted.contains(".clone()"), "{emitted}");
            assert_eq!(emitted.matches("Vec::with_capacity").count(), 1);
            rust.push_str(&format!(
                "fn {name}(l_a:&Vec<{t}>,l_b:&Vec<{t}>)->Vec<{t}>{{{emitted}}}\n"
            ));
        }
        let f = p.functions.iter().find(|f| f.name == "computed").unwrap();
        rust.push_str(&format!(
            "fn computed(l_a:Vec<u32>,l_b:Vec<u32>,l_flag:bool)->Vec<u32>{{{}}}\n",
            body(&p, f).unwrap()
        ));
        let f = p.functions.iter().find(|f| f.name == "contextual").unwrap();
        rust.push_str(&format!(
            "fn contextual(l_a:Vec<u32>,l_b:Vec<u32>)->Vec<u32>{{{}}}\n",
            body(&p, f).unwrap()
        ));
        rust.push_str(r#"
fn main() {
    let a=vec![0,u32::MAX,17];let b=vec![23,u32::MAX];
    let mut output=words(&a,&b);assert_eq!(output,vec![0,u32::MAX,17,23,u32::MAX]);
    assert_ne!(output.as_ptr(),a.as_ptr());assert_ne!(output.as_ptr(),b.as_ptr());
    output[0]=9;assert_eq!(a,vec![0,u32::MAX,17]);assert_eq!(b,vec![23,u32::MAX]);
    assert_eq!(words(&a,&a),vec![0,u32::MAX,17,0,u32::MAX,17]);
    assert_eq!(words(&vec![],&a),a);assert_eq!(words(&a,&vec![]),a);assert!(words(&vec![],&vec![]).is_empty());
    assert_eq!(wide(&vec![u64::MAX,1<<32],&vec![0]),vec![u64::MAX,1<<32,0]);
    assert_eq!(flags(&vec![false,true],&vec![true]),vec![false,true,true]);
    assert_eq!(texts(&vec!["left".into()],&vec!["right".into()]),vec!["left","right"]);
    let outer=vec![vec![1,2],vec![]];let mut nested_output=nested(&outer,&outer);
    nested_output[0][0]=99;assert_eq!(outer,vec![vec![1,2],vec![]]);assert_eq!(nested_output.len(),4);
    let left=vec![l_Item{l_key:0},l_Item{l_key:u32::MAX}];let right=vec![l_Item{l_key:17}];
    COPIES.store(0,Ordering::Relaxed);let joined=records(&left,&right);
    assert_eq!(COPIES.load(Ordering::Relaxed),3);assert_eq!(joined.iter().map(|x|x.l_key).collect::<Vec<_>>(),vec![0,u32::MAX,17]);
    assert_eq!(left[1].l_key,u32::MAX);assert_eq!(right[0].l_key,17);
    assert_eq!(computed(a.clone(),b.clone(),true),vec![0,u32::MAX,17,23,u32::MAX]);
    assert_eq!(computed(a.clone(),b.clone(),false),vec![23,u32::MAX,23,u32::MAX]);
    assert_eq!(contextual(a.clone(),b.clone()),vec![0,0,0,23,u32::MAX]);
}
"#);
        let tag = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let dir =
            std::env::temp_dir().join(format!("ink-rust-concat-{}-{tag}", std::process::id()));
        fs::create_dir_all(&dir).unwrap();
        let source = dir.join("concat.rs");
        let binary = dir.join("concat");
        fs::write(&source, rust).unwrap();
        let compiled = Command::new("rustc")
            .args(["--edition=2021", "-O"])
            .arg(&source)
            .arg("-o")
            .arg(&binary)
            .output()
            .unwrap();
        assert!(
            compiled.status.success(),
            "{}",
            String::from_utf8_lossy(&compiled.stderr)
        );
        let run = Command::new(&binary).output().unwrap();
        assert!(
            run.status.success(),
            "{}",
            String::from_utf8_lossy(&run.stderr)
        );
        fs::remove_dir_all(dir).unwrap();
    }
}

#[cfg(test)]
mod parallel_tests {
    #[test]
    fn workers_are_bounded_nested_work_is_sequential_and_updates_reuse_allocation() {
        use std::{fs, process::Command};
        let root = std::env::temp_dir().join(format!("ink-parallel-{}", std::process::id()));
        fs::create_dir_all(&root).unwrap();
        let mut source = include_str!("temporary.rs.txt").to_owned();
        source.push_str(r#"
fn main(){
 std::env::set_var("INK_THREADS","4");
 let seen=std::sync::Mutex::new(std::collections::HashSet::new());
 let mut xs=Vec::with_capacity(512);xs.extend(0..256u32);let pointer=xs.as_ptr();let capacity=xs.capacity();
 let output=ink_parallel_update(xs,16,|i,x|{
  seen.lock().unwrap().insert(std::thread::current().id());
  let nested=ink_parallel_map(vec![x,1],1,|j,y|{assert_eq!(ink_parallel_workers(1000,1),1);y+j});
  i+nested[0]
 });
 assert_eq!(output.as_ptr(),pointer);assert_eq!(output.capacity(),capacity);
 assert_eq!(output,(0..256u32).map(|x|x*2).collect::<Vec<_>>());
 assert_eq!(seen.lock().unwrap().len(),4);
 assert!(ink_parallel_map(Vec::<u32>::new(),0,|i,x|i+x).is_empty());
 assert_eq!(ink_parallel_map(vec![3],u32::MAX,|i,x|i+x),vec![3]);
}
"#);
        fs::write(root.join("test.rs"), source).unwrap();
        let out = Command::new("rustc")
            .args(["--edition=2021", "-O"])
            .arg(root.join("test.rs"))
            .arg("-o")
            .arg(root.join("test"))
            .output()
            .unwrap();
        assert!(
            out.status.success(),
            "{}",
            String::from_utf8_lossy(&out.stderr)
        );
        let out = Command::new(root.join("test")).output().unwrap();
        assert!(
            out.status.success(),
            "{}",
            String::from_utf8_lossy(&out.stderr)
        );
        fs::remove_dir_all(root).unwrap();
    }
}
