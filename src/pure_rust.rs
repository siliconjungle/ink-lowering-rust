//! Literal lowering of every currently admitted pure expression. No AST runtime.
use crate::{check, syntax::*, LangResult};
use std::collections::BTreeMap;
type Env = BTreeMap<String, (String, Type)>;
fn references(e: &Expr, name: &str) -> bool {
    ink_core::analysis::references_free(e, name)
}

struct Emitter<'a> {
    p: &'a Program,
    physical: Option<&'a ink_core::physical::CheckedPhysicalPlan>,
    last_uses: ink_core::last_use::LastUses,
    borrowed_bindings: std::collections::BTreeSet<String>,
    paths: BTreeMap<usize,Vec<usize>>,
    next: usize,
    prefix: String,
    tasks: Vec<(String, String)>,
    reservation: Option<(String,String)>,
    reserved: bool,
}
impl Emitter<'_> {
    fn collect(&mut self, e: &Expr, iterator: String, collection: &str) -> LangResult<String> {
        if self.reservation.as_ref().is_some_and(|(site,_)|ink_core::registry::identity(e).is_ok_and(|id|id==*site)) {
            self.reserved=true;
            let capacity=&self.reservation.as_ref().unwrap().1;
            let conversion=if collection.starts_with("Vec<"){""}else{".into()"};
            Ok(format!("({{let mut ink_reserved=Vec::with_capacity({capacity});ink_reserved.extend({iterator});ink_reserved}}){conversion}"))
        } else { Ok(format!("({iterator}).collect::<{collection}>()")) }
    }
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
            Type::Int => "BigInt::from(0u8)".into(),
            _ => "0u64".into(),
        }
    }
    // Read-only traversals borrow a lexical list instead of cloning the entire
    // vector. Computed receivers still finish eagerly and are consumed once.
    fn borrowed_place(&self, e: &Expr, env: &Env) -> Option<String> {
        if !self.physical.is_some_and(|plan| ink_core::registry::identity(e).is_ok_and(|id| plan.borrows_read(&id))) {return None;}
        self.lexical_place(e, env)
    }
    // Field projection copies the field value, not its containing record.
    // This is literal access to a checked place; it retains no borrowed value
    // and does not choose borrowed collection traversal or parameter ownership.
    fn lexical_place(&self, e:&Expr, env:&Env)->Option<String> {
        let (root, fields) = ink_core::collection_facts::lexical_projection(e)?;
        let mut place = env.get(root)?.0.clone();
        for field in fields {place=format!("({place}).l_{field}");}
        Some(place)
    }

    fn read_iterator(&self, e: &Expr, value: &str, env: &Env) -> LangResult<String> {
        Ok(if let Some(place) = self.borrowed_place(e, env) {
            // Lexical record projections have no evaluation side effects.
            // Borrow only for this traversal; subsequent source uses survive.
            if matches!(self.infer(e,env,None)?,Type::List(ref t)if crate::columns::names(t).is_some()){format!("({place}).iter()")}else{format!("({place}).iter().cloned()")}
        } else {
            format!("({value}).into_iter()")
        })
    }
    fn lambda(&mut self,e:&Expr,env:&Env,params:&[Type],result:&Type)->LangResult<(Vec<String>,String)> {
        self.lambda_mode(e,env,params,result,false)
    }
    fn lambda_mode(
        &mut self,e:&Expr,env:&Env,params:&[Type],result:&Type,borrowed:bool,
    ) -> LangResult<(Vec<String>,String)> {
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
        // The primitive invokes the flattened callback once per item. Its
        // formal parameters are owned within that invocation; outer captures
        // remain absent from these facts and therefore cannot move.
        let mut formal = Vec::new();
        let mut current = e;
        for _ in params {
            let Expr::Lambda(name, nested) = current else {unreachable!()};
            formal.push(name.as_str());current=nested;
        }
        let facts=ink_core::last_use::analyse(body,formal);
        let outer=std::mem::replace(&mut self.last_uses,facts);
        let previous_borrows=self.borrowed_bindings.clone();
        if borrowed {self.borrowed_bindings.extend(vars.iter().cloned());}
        let emitted=self.expr(body,&local,Some(result));
        self.borrowed_bindings=previous_borrows;
        self.last_uses=outer;
        Ok((vars,emitted?))
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
        let xs=if crate::columns::names(input).is_some(){format!("({xs}).into_rows()")}else{xs};
        let convert=if crate::columns::names(output).is_some(){".into()"}else{""};
        Ok(format!("({{let xs={xs};let grain={grain};{native_block}{wasm_block}}}){convert}"))
    }
    fn source_path(&self,e:&Expr)->Option<&[usize]>{self.paths.get(&(e as *const Expr as usize)).map(Vec::as_slice)}
    fn unchecked(&self,e:&Expr)->bool{self.physical.is_some_and(|p|self.source_path(e).is_some_and(|path|p.bounds().allows(&self.prefix,path)))}
    fn column_mask(&self,e:&Expr,element:&Type)->u16{
        let Some(p)=self.physical else{return 0};let Some(path)=self.source_path(e)else{return 0};
        let record=match element{Type::Named(n)=>n.clone(),Type::U32=>"@U32".into(),Type::U64=>"@U64".into(),Type::Bool=>"@Bool".into(),_=>return 0};
        let Ok(schema)=ink_core::column_codec::schema(self.p,&record)else{return 0};
        schema.fields.iter().enumerate().filter(|(_, (n,_))|p.column_maps().fields(&self.prefix,path).contains(n)).fold(0,|mask,(i,_)|mask|(1<<i))
    }
    fn expr(&mut self, e: &Expr, env: &Env, want: Option<&Type>) -> LangResult<String> {
        let t = self.infer(e, env, want)?;
        Ok(match e {
            Expr::Num(n) => match t {
                Type::Int => format!("BigInt::from({n}u64)"),
                Type::U32 => format!("{n}u32"),
                Type::I32 => format!("{n}i32"),
                Type::F32 => format!("f32::from_bits({}u32)", (*n as f32).to_bits()),
                _ => format!("{n}u64"),
            },
            Expr::Float(b) => format!("f32::from_bits({b}u32)"),
            Expr::Bool(b) => b.to_string(),
            Expr::String(s) => format!("{s:?}.to_owned()"),
            Expr::Unit => "()".into(),
            Expr::Var(n) if n == "None" => "None".into(),
            Expr::Var(n) => {
                let v = &env.get(n).ok_or("missing binding")?.0;
                if !self.borrowed_bindings.contains(v) && (ink_core::local_collections::owned(&t, self.p) || self.last_uses.contains(e)) {
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
                if t == Type::Int {
                    format!("-({x})")
                } else if t == Type::F32 {
                    format!("f32::from_bits(({x}).to_bits() ^ 0x80000000)")
                } else {
                    format!("({x}).wrapping_neg()")
                }
            }
            Expr::Let(n, annotation, a, b) => {
                let at = self.infer(a, env, annotation.as_deref())?;
                // An immutable lexical argument has already been evaluated.
                // Keep a local alias and copy only when its value is observed.
                // Exclude owned handles and any body that could separately move
                // the containing root; large bodies retain the copying path.
                let alias = if !ink_core::local_collections::owned(&at,self.p)
                    && !(matches!(a.as_ref(),Expr::Var(_)) && self.last_uses.contains(a))
                    && matches!(&at,Type::Named(_)|Type::List(_))
                    && ink_core::analysis::node_count(b,256).is_some() {
                    ink_core::collection_facts::lexical_projection(a).and_then(|(root,_)|
                        if root!=n && !ink_core::analysis::references_free(b,root){self.lexical_place(a,env)}else{None})
                } else {None};
                let initial = match &alias {Some(place)=>format!("&({place})"),None=>self.expr(a,env,Some(&at))?};
                let v = self.fresh();
                let mut local = env.clone();
                let annotation = format!("{}{}",if alias.is_some(){"&"}else{""},crate::state_native::ty(&at)?);
                local.insert(n.clone(), (v.clone(), at));
                if alias.is_some(){self.borrowed_bindings.insert(v.clone());}
                let body=self.expr(b,&local,Some(&t));
                self.borrowed_bindings.remove(&v);
                format!("{{let {v}:{annotation}={initial};{}}}",body?)
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
                if let Expr::Var(en) = x.as_ref() {
                    if !env.contains_key(en) && self.p.enums.contains_key(en) {
                        return Ok(format!("l_{en}::l_{n}"));
                    }
                }
                let xt = self.infer(x, env, None)?;
                if let Type::Named(owner) = &xt {
                    if let Some(place) = self.lexical_place(e, env) {
                        let ft = &self.p.records[owner]
                            .iter()
                            .find(|(field, _)| field == n)
                            .ok_or("field")?
                            .1;
                        if !ink_core::local_collections::owned(ft, self.p) {
                            return Ok(if crate::state_native::boxed_field(owner, ft, self.p) {
                                format!("(*({place})).clone()")
                            } else {
                                format!("({place}).clone()")
                            });
                        }
                    }
                }
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
                let at = if check::is_numeric_value(&t) {
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
                } else if (op == "==" || op == "!=") && at != Type::F32 {
                    format!(
                        "{}InkDataEq::ink_data_eq(&({a}),&({b}))",
                        if op == "!=" { "!" } else { "" }
                    )
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
            Expr::Call(n,args)if n=="list"=>{
                let Type::List(inner)=&t else{return Err("list type".into())};
                let items=args.iter().map(|e|self.expr(e,env,Some(inner))).collect::<LangResult<Vec<_>>>()?.join(",");
                if crate::columns::names(inner).is_some(){format!("vec![{items}].into()")}else{format!("vec![{items}]")}
            }
            Expr::Call(n, args) if ink_core::word::primitive(n) => {
                let ts = ink_core::word::arguments(n, &t);
                let args = args
                    .iter()
                    .zip(ts)
                    .map(|(a, t)| self.expr(a, env, Some(&t)))
                    .collect::<LangResult<Vec<_>>>()?;
                crate::state_native::word_expression(n, &args)
            }
            Expr::Call(n, args) if ["Some", "Ok", "Err"].contains(&n.as_str()) => {
                let inner = match (&t, n.as_str()) {
                    (Type::Option(t), "Some")
                    | (Type::Result(t, _), "Ok")
                    | (Type::Result(_, t), "Err") => t.as_ref(),
                    _ => return Err("variant type".into()),
                };
                format!("{n}({})", self.expr(&args[0], env, Some(inner))?)
            }
            Expr::Call(n, args) if n == "Int" => {
                format!("BigInt::from({})", self.expr(&args[0], env, None)?)
            }
            Expr::Call(n, args)
                if ["checked_add", "checked_sub", "checked_mul"].contains(&n.as_str()) =>
            {
                let Type::Result(inner, _) = &t else {
                    return Err("checked type".into());
                };
                format!(
                    "({}).{n}({}).ok_or(InkArithmeticError::Overflow)",
                    self.expr(&args[0], env, Some(inner))?,
                    self.expr(&args[1], env, Some(inner))?
                )
            }
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
                        "<{}>::new({})",
                        crate::state_native::ty(&t)?,self.expr(&args[0], env, Some(&Type::List(inner.clone())))?
                    )
                } else {
                    let len = self.expr(&args[0], env, Some(&Type::U32))?;
                    let value = self.expr(&args[1], env, Some(inner))?;
                    let lv = self.fresh();
                    let vv = self.fresh();
                    format!("{{let {lv}={len};let {vv}={value};<{}>::new(vec![{vv};{lv} as usize].into())}}",crate::state_native::ty(&t)?)
                }
            }
            Expr::Method(x, n, args) if matches!(x.as_ref(),Expr::Var(v) if v=="Buffer" || v=="Map") =>
            {
                format!(
                    "{}::new({})",
                    if matches!(t, Type::Buffer(_)) {
                        format!("<{}>",crate::state_native::ty(&t)?)
                    } else {
                        "OwnedMap".into()
                    },
                    if matches!(t, Type::Buffer(_)) {
                        "Default::default()"
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
                    "map" | "map_indexed" => {
                        let params = if n == "map" {
                            vec![value.clone()]
                        } else {
                            vec![Type::U32, value.clone()]
                        };
                        let (vs, body) = self.lambda(&args[0], env, &params, value)?;
                        if n == "map" {
                            if crate::columns::names(value).is_some(){let mask=self.column_mask(e,value);format!("({xv}).map_masked(|{}|{{{body}}},{mask})",vs[0])}else{format!("({xv}).map_inplace(|{}|{{{body}}})", vs[0])}
                        } else {
                            format!(
                                "({xv}).map_indexed_inplace(|{},{}|{{{body}}})",
                                vs[0], vs[1]
                            )
                        }
                    }
                    "filter" => {
                        let (vs, body) =
                            self.lambda(&args[0], env, &[value.clone()], &Type::Bool)?;
                        format!("({xv}).filter_inplace(|{}|{{{body}}})", vs[0])
                    }
                    "scan" => {
                        let add = Self::arithmetic("+", "acc", "item", value);
                        format!(
                            "({xv}).scan_inplace({},|acc,item|{{{add}}})",
                            Self::zero(value)
                        )
                    }
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
                        format!("<{}>::new({mapped})",crate::state_native::ty(&xt)?)
                    }
                    "split_at" => {
                        let at = self.expr(&args[0], env, Some(&Type::U32))?;
                        let (vs, body) =
                            self.lambda(&args[1], env, &[xt.clone(), xt.clone()], &xt)?;
                        format!("{{let ({},{})=({xv}).split({at});{body}}}", vs[0], vs[1])
                    }
                    "append" => format!("({xv}).append({})", self.expr(&args[0], env, Some(&xt))?),
                    "len" | "pop" | "freeze" => format!("({xv}).{n}()"),
                    "keys"|"values" => format!("({xv}).{n}().into()"),
                    "at_or" | "get_or" => {
                        let k = self.expr(&args[0], env, Some(&key))?;
                        let fallback = self.expr(&args[1], env, Some(value))?;
                        if matches!(xt,Type::Buffer(_)) && self.unchecked(e) {format!("unsafe{{({xv}).get_unchecked({k})}}")}
                        else {format!("({xv}).get({}{k}).unwrap_or_else(||{fallback})",if matches!(xt,Type::Map(..)){"&"}else{""})}
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
                    "fill_range" | "copy_within" => {
                        let a = self.expr(&args[0], env, Some(&Type::U32))?;
                        let b = self.expr(&args[1], env, Some(&Type::U32))?;
                        let c = self.expr(
                            &args[2],
                            env,
                            Some(if n == "fill_range" { value } else { &Type::U32 }),
                        )?;
                        format!("({xv}).{n}({a},{b},{c})")
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
            Expr::Call(n, args) if n == "fold_until" => {
                let Type::List(inner) = self.infer(&args[0], env, None)? else {
                    return Err("fold input".into());
                };
                let xs = self.expr(&args[0], env, None)?;
                let initial = self.expr(&args[1], env, Some(&t))?;
                let read_only = !ink_core::local_collections::owned(&inner,self.p) && !ink_core::local_collections::owned(&t,self.p);
                let (stopvars, stop) = self.lambda_mode(&args[2],env,&[inner.as_ref().clone(),t.clone()],&Type::Bool,read_only)?;
                let (vs, body) = self.lambda(&args[3], env, &[*inner, t.clone()], &t)?;
                let list = self.fresh();
                let acc = self.fresh();
                let item = self.fresh();
                let flag = self.fresh();
                let observed_item=if read_only{format!("&{item}")}else{format!("{item}.clone()")};
                let observed_acc=if read_only{format!("&{acc}")}else{format!("{acc}.clone()")};
                format!("{{let {list}={xs};let mut {acc}={initial};for {item} in {list}.into_iter() {{let {}={observed_item};let {}={observed_acc};let {flag}={stop};let {}={item};let {}={acc};{acc}={body};if {flag} {{break;}}}}{acc}}}",stopvars[0],stopvars[1],vs[0],vs[1])
            }
            Expr::Call(n, args) if n == "foldr" || n == "foldl" => {
                let Type::List(inner) = self.infer(&args[0], env, None)? else {
                    return Err("fold input".into());
                };
                let xs = self.expr(&args[0], env, None)?;
                let iterator = self.read_iterator(&args[0], &xs, env)?;
                let initial = self.expr(&args[1], env, Some(&t))?;
                let (vs, body) = self.lambda(&args[2], env, &[*inner, t.clone()], &t)?;
                let acc = self.fresh();
                let list = self.fresh();
                let direction = if n == "foldr" { ".rev()" } else { "" };
                format!("{{let {list}={iterator};let mut {acc}={initial};for {} in {list}{direction} {{let {}={acc};{acc}={body};}}{acc}}}",vs[0],vs[1])
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
                    } else {
                        xs
                    };
                    if t == Type::Int {
                        format!("BigInt::from(({value}).len())")
                    } else {
                        format!("({value}).len() as u64")
                    }
                } else {
                    let iterator = self.read_iterator(&args[0], &xs, env)?;
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
            Expr::Method(xs, n, args)
                if matches!(
                    self.infer(xs, env, None)?,
                    Type::Option(_) | Type::Result(..)
                ) =>
            {
                let input = self.infer(xs, env, None)?;
                let value = self.expr(xs, env, Some(&input))?;
                if n == "fold" {
                    let (a, b, tag_a, tag_b) = match &input {
                        Type::Option(a) => (a.as_ref().clone(), Type::Unit, "Some", "None"),
                        Type::Result(a, b) => (a.as_ref().clone(), b.as_ref().clone(), "Ok", "Err"),
                        _ => unreachable!(),
                    };
                    let (va, body_a) = self.lambda(&args[0], env, &[a], &t)?;
                    let (vb, body_b) = self.lambda(&args[1], env, &[b], &t)?;
                    let right = if tag_b == "None" {
                        format!("None=>{{let {}=();{body_b}}}", vb[0])
                    } else {
                        format!("Err({})=>{{{body_b}}}", vb[0])
                    };
                    format!("match {value} {{{tag_a}({})=>{{{body_a}}},{right}}}", va[0])
                } else if n == "ok_or" {
                    format!("({value}).ok_or({})", self.expr(&args[0], env, None)?)
                } else {
                    let (inner, out) = match (&input, &t, n.as_str()) {
                        (Type::Option(a), Type::Option(b), "map")
                        | (Type::Result(a, _), Type::Result(b, _), "map")
                        | (Type::Result(_, a), Type::Result(_, b), "map_err") => {
                            (a.as_ref(), b.as_ref())
                        }
                        _ => return Err("variant method".into()),
                    };
                    let (vars, body) = self.lambda(&args[0], env, &[inner.clone()], out)?;
                    format!("({value}).{n}(|{}|{{{body}}})", vars[0])
                }
            }
            Expr::Method(xs, n, args) if n == "concat" => {
                if matches!(&t,Type::List(inner)if crate::columns::names(inner).is_some()){
                    let left=self.expr(xs,env,Some(&t))?;let right=self.expr(&args[0],env,Some(&t))?;
                    let a=self.fresh();let b=self.fresh();return Ok(format!("{{let mut {a}={left};let mut {b}={right};{a}.append(&mut {b});{a}}}"));
                }
                // Borrow variable operands directly. Computed operands are evaluated
                // once and their temporaries live through the two result copies.
                let left = if let Some(place) = self.borrowed_place(xs, env) {
                    format!("&({place})")
                } else {
                    format!("&({})", self.expr(xs, env, Some(&t))?)
                };
                let right = if let Some(place) = self.borrowed_place(&args[0], env) {
                    format!("&({place})")
                } else {
                    format!("&({})", self.expr(&args[0], env, Some(&t))?)
                };
                let a = self.fresh();
                let b = self.fresh();
                let collected=self.collect(e,format!("{a}.iter().chain({b}.iter()).cloned()"),&crate::state_native::ty(&t)?)?;
                format!("{{let {a}={left};let {b}={right};{collected}}}")
            }
            Expr::Method(xs, n, args) => {
                let Type::List(inner) =
                    self.infer(xs, env, if n == "filter" { Some(&t) } else { None })?
                else {
                    return Err("list receiver".into());
                };
                let receiver = xs.as_ref();
                let xs = self.expr(receiver, env, None)?;
                let iterator = self.read_iterator(receiver, &xs, env)?;
                let collection=crate::state_native::ty(&t)?;
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
                        if self.unchecked(e){format!("{{let {list}={xs};let {i}={index};unsafe{{{list}.get_unchecked({i} as usize).clone()}}}}") }else{format!("{{let {list}={xs};let {i}={index};match {list}.get({i} as usize){{Some(v)=>v.clone(),None=>{fallback}}}}}")}
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
                        let acc = self.fresh();
                        let item = self.fresh();
                        {
                            format!("{{let mut {acc}={};({iterator}).map(|{item}|{{{acc}={};{acc}}}).collect::<{collection}>()}}",Self::zero(&inner),Self::arithmetic("+",&acc,&item,&inner))
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
                        if n=="map"&&self.infer(xs_receiver(e),env,None)?==t&&crate::columns::names(&output).is_some()&&self.borrowed_place(xs_receiver(e),env).is_none()&&!self.reservation.as_ref().is_some_and(|(site,_)|ink_core::registry::identity(e).is_ok_and(|id|id==*site)){
                            let mask=self.column_mask(e,&output);format!("({xs}).map_rows(|{}|{{{body}}},{mask})",vs[0])
                        }else if n == "filter" {
                            self.collect(e,format!("({iterator}).filter(|ink_ref|{{let {}=ink_ref.clone();{body}}})",vs[0]),&collection)?
                        } else if n == "map_indexed" {
                            self.collect(e,format!("({iterator}).enumerate().map(|(ink_i,{})|{{let {}=ink_i as u32;{body}}})",vs[1],vs[0]),&collection)?
                        } else {
                            self.collect(e,format!("({iterator}).map(|{}|{body})", vs[0]),&collection)?
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
                        let right_iterator = self.read_iterator(&args[0], &ys, env)?;
                        let (vs, body) = self.lambda(&args[1], env, &[*inner, *other], out)?;
                        let a = self.fresh();
                        let b = self.fresh();
                        format!("{{let {a}={iterator};let {b}={right_iterator};{}}}",self.collect(e,format!("{a}.zip({b}).map(|({},{})|{body})",vs[0],vs[1]),&collection)?)
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
#[cfg(test)]
pub fn body_with_tasks(p: &Program, f: &Function) -> LangResult<(String, Vec<(String, String)>)> {
    body_with_tasks_planned(p,f,None)
}
pub fn body_with_tasks_planned(p: &Program, f: &Function, physical: Option<&ink_core::physical::CheckedPhysicalPlan>) -> LangResult<(String, Vec<(String, String)>)> {
    let env = f
        .params
        .iter()
        .map(|(n, t)| (n.clone(), (format!("l_{n}"), t.clone())))
        .collect();
    let mut emitter = Emitter {
        p,
        physical,
        paths:ink_core::analysis::paths(&f.body),
        last_uses: ink_core::last_use::analyse(&f.body, f.params.iter().map(|(n, _)| n.as_str())),
        borrowed_bindings: Default::default(),
        next: 0,
        prefix: f.name.clone(),
        tasks: Vec::new(),
        reservation: physical.and_then(|p|p.plan().reservations.iter().find(|r|r.function==f.name)).map(|_|Ok::<_,String>((ink_core::registry::identity(&f.body)?,"ink_reserved_capacity".into()))).transpose()?,
        reserved: false,
    };
    if !ink_core::recursion::recursive(f) {
        let body = emitter.expr(&f.body, &env, Some(&f.result))?;
        if let Some(reservation)=physical.and_then(|p|p.plan().reservations.iter().find(|r|r.function==f.name)) {
            if !emitter.reserved { return Err("literal backend lacks a reservation collector at this result site".into()); }
            let capacity=if let Some(expression)=&reservation.capacity {
                let value=emitter.expr(expression,&env,None)?;
                format!("usize::try_from({value}).unwrap_or(0)")
            }else{
                let place=reservation.fields.iter().fold(format!("l_{}",reservation.parameter),|p,f|format!("({p}).l_{f}"));
                format!("({place}).len()")
            };
            return Ok((format!("{{let ink_reserved_capacity={capacity};{body}}}"),emitter.tasks));
        }
        return Ok((body, emitter.tasks));
    }
    if emitter.reservation.is_some() { return Err("recursive reservation collector unsupported".into()); }
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
    fn nested_record_reads_clone_only_observed_elements() {
        let p=parse(r#"module fields;
record Item{key:u32,} record Inner{first:List<Item>,second:List<Item>,id:u32,} record Outer{nested:Inner,}
fn key(r:Outer)->u32{return r.nested.id;}
fn mapped(r:Outer)->List<u32>{return r.nested.first.map(fn(x)=>x.key+1);}
fn joined(r:Outer)->List<Item>{return r.nested.first.concat(r.nested.first);}
fn selected(r:Outer)->List<Item>{return r.nested.first;}
"#).unwrap();
        check::check(&p).unwrap();
        let module=ink_core::core::CheckedModule::from_source(p.clone()).unwrap();
        let mut sites=std::collections::BTreeSet::new();
        for f in &p.functions {let env=ink_core::check::params_env(&f.params).unwrap();ink_core::analysis::walk(&f.body,|e|if matches!(e,Expr::Var(_)|Expr::Field(..))&&ink_core::check::infer(e,&env,&p).is_ok(){sites.insert(ink_core::registry::identity(e).unwrap());});}
        sites.insert(ink_core::registry::identity(&Expr::Field(Box::new(Expr::Var("x".into())),"key".into())).unwrap());
        let physical=ink_core::physical::check(&module,None,&ink_core::physical::Plan{schema:1,semantics:ink_core::physical::SEMANTICS.into(),input_core_sha256:module.identity().unwrap(),representation:None,tables:Default::default(), buffers:Default::default(), bounds:None, columns:vec![],column_maps:None,borrow_reads:sites.into_iter().collect(),borrow_rows:vec![],definitions:Default::default(),packed_datatypes:vec![],memo_functions:vec![],reservations:vec![]}).unwrap();

        let mut source = String::from(
            r#"
#![allow(non_camel_case_types)]
use std::sync::atomic::{AtomicUsize,Ordering};
static COPIES:AtomicUsize=AtomicUsize::new(0);
struct l_Item{l_key:u32}
impl Clone for l_Item{fn clone(&self)->Self{COPIES.fetch_add(1,Ordering::Relaxed);Self{l_key:self.l_key}}}
#[derive(Clone)]struct l_Inner{l_first:Vec<l_Item>,l_second:Vec<l_Item>,l_id:u32}
#[derive(Clone)]struct l_Outer{l_nested:l_Inner}
"#,
        );
        for (name, result) in [
            ("key", "u32"),
            ("mapped", "Vec<u32>"),
            ("joined", "Vec<l_Item>"),
            ("selected", "Vec<l_Item>"),
        ] {
            let f = p.functions.iter().find(|f| f.name == name).unwrap();
            source.push_str(&format!(
                "fn {name}(l_r:&l_Outer)->{result}{{{}}}\n",
                body_with_tasks_planned(&p,f,Some(&physical)).unwrap().0
            ));
        }
        source.push_str(r#"
fn main(){
let r=l_Outer{l_nested:l_Inner{l_first:vec![l_Item{l_key:0},l_Item{l_key:u32::MAX},l_Item{l_key:9}],l_second:(0..1000).map(|i|l_Item{l_key:i}).collect(),l_id:17}};
assert_eq!(key(&r),17);assert_eq!(COPIES.load(Ordering::Relaxed),0);
assert_eq!(mapped(&r),vec![1,0,10]);assert_eq!(COPIES.swap(0,Ordering::Relaxed),3);
let mut a=joined(&r);assert_eq!(a.len(),6);assert_eq!(COPIES.swap(0,Ordering::Relaxed),6);
a[0].l_key=42;assert_eq!(r.l_nested.l_first[0].l_key,0);
let a=selected(&r);assert_eq!(a.len(),3);assert_eq!(COPIES.swap(0,Ordering::Relaxed),3);assert_eq!(r.l_nested.l_second.len(),1000);
}
"#);
        let dir = std::env::temp_dir().join(format!("ink-record-read-{}", std::process::id()));
        fs::create_dir_all(&dir).unwrap();
        fs::write(dir.join("test.rs"), source).unwrap();
        let output = Command::new("rustc")
            .args(["--edition=2021", "-O"])
            .arg(dir.join("test.rs"))
            .arg("-o")
            .arg(dir.join("test"))
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(Command::new(dir.join("test")).status().unwrap().success());
        fs::remove_dir_all(dir).unwrap();
    }

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
        let module=ink_core::core::CheckedModule::from_source(p.clone()).unwrap();
        let mut sites=vec![ink_core::registry::identity(&Expr::Var("a".into())).unwrap(),ink_core::registry::identity(&Expr::Var("b".into())).unwrap()];sites.sort();
        let physical=ink_core::physical::check(&module,None,&ink_core::physical::Plan{schema:1,semantics:ink_core::physical::SEMANTICS.into(),input_core_sha256:module.identity().unwrap(),representation:None,tables:Default::default(), buffers:Default::default(), bounds:None, columns:vec![],column_maps:None,borrow_reads:sites,borrow_rows:vec![],definitions:Default::default(),packed_datatypes:vec![],memo_functions:vec![],reservations:vec![]}).unwrap();

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
            let emitted = body_with_tasks_planned(&p,f,Some(&physical)).unwrap().0;
            assert!(!emitted.contains(".clone()"), "{emitted}");

            rust.push_str(&format!(
                "fn {name}(l_a:&Vec<{t}>,l_b:&Vec<{t}>)->Vec<{t}>{{{emitted}}}\n"
            ));
        }
        let f = p.functions.iter().find(|f| f.name == "computed").unwrap();
        rust.push_str(&format!(
            "fn computed(l_a:Vec<u32>,l_b:Vec<u32>,l_flag:bool)->Vec<u32>{{{}}}\n",
            body_with_tasks_planned(&p,f,Some(&physical)).unwrap().0
        ));
        let f = p.functions.iter().find(|f| f.name == "contextual").unwrap();
        rust.push_str(&format!(
            "fn contextual(l_a:Vec<u32>,l_b:Vec<u32>)->Vec<u32>{{{}}}\n",
            body_with_tasks_planned(&p,f,Some(&physical)).unwrap().0
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
        let mut source = ink_native_support::OWNED_VALUES_RUST_SOURCE.to_owned();
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

fn xs_receiver(e:&Expr)->&Expr {if let Expr::Method(xs,_,_)=e{xs}else{unreachable!()}}

#[cfg(test)]
mod callback_ownership_tests {
    use super::*;
    #[test]
    fn curried_formals_move_once_read_only_stop_borrows_and_captures_survive() {
        let program=parse(r#"module Copies;
record Row{key:u32,label:String,}
fn total(xs:List<Row>)->u32{return foldr(xs,0,fn(x)=>fn(acc)=>x.key+acc);}
fn until(xs:List<Row>,cut:u32)->u32{return fold_until(xs,0,fn(x)=>fn(acc)=>x.key>=cut,fn(x)=>fn(acc)=>x.key+acc);}
fn whole(xs:List<Row>,seed:Row)->Row{return foldr(xs,seed,fn(x)=>fn(acc)=>choose(x.key>0,x,acc));}
fn captured(xs:List<Row>,seed:Row)->List<Row>{return xs.map(fn(x)=>choose(x.key>0,seed,x));}
fn repeated(row:Row)->u32{return row.key+row.key;}
fn escaping(row:Row)->Row{return row;}
fn moving(row:Row)->Row{return row;}
"#).unwrap();
        let mut program=program;
        let row_ty=Some(Box::new(Type::Named("Row".into())));
        let value=||Box::new(Expr::Var("row".into()));
        program.functions.iter_mut().find(|f|f.name=="repeated").unwrap().body=Expr::Binary("+".into(),Box::new(Expr::Let("alias".into(),row_ty.clone(),value(),Box::new(Expr::Field(Box::new(Expr::Var("alias".into())),"key".into())))),Box::new(Expr::Field(value(),"key".into())));
        program.functions.iter_mut().find(|f|f.name=="escaping").unwrap().body=Expr::Let("alias".into(),row_ty.clone(),value(),Box::new(Expr::Var("alias".into())));
        program.functions.iter_mut().find(|f|f.name=="moving").unwrap().body=Expr::Let("alias".into(),row_ty.clone(),value(),Box::new(Expr::Let("gone".into(),row_ty,value(),Box::new(Expr::Var("alias".into())))));
        check::check(&program).unwrap();
        let mut code=String::from(r#"
#![allow(non_camel_case_types,unused_variables,unused_parens)]
use std::sync::atomic::{AtomicUsize,Ordering};
static COPIES:AtomicUsize=AtomicUsize::new(0);
#[derive(Debug,PartialEq)]struct l_Row{l_key:u32,l_label:String}
impl Clone for l_Row{fn clone(&self)->Self{COPIES.fetch_add(1,Ordering::Relaxed);Self{l_key:self.l_key,l_label:self.l_label.clone()}}}
"#);
        for f in &program.functions {
            let params=f.params.iter().map(|(n,t)|format!("l_{n}:{}",crate::state_native::ty(t).unwrap())).collect::<Vec<_>>().join(",");
            code.push_str(&format!("fn {}({params})->{}{{{}}}\n",f.name,crate::state_native::ty(&f.result).unwrap(),body(&program,f).unwrap()));
        }
        code.push_str(r#"
fn row(key:u32)->l_Row{l_Row{l_key:key,l_label:format!("row-{key}")}}
fn main(){
assert_eq!(total(vec![row(1),row(2),row(3)]),6);assert_eq!(COPIES.load(Ordering::Relaxed),0);
assert_eq!(until(vec![row(1),row(2),row(3)],2),3);assert_eq!(COPIES.load(Ordering::Relaxed),0);
assert_eq!(whole(vec![row(1),row(2)],row(99)),row(1));assert_eq!(COPIES.load(Ordering::Relaxed),0);
let xs=captured(vec![row(1),row(2),row(0)],row(77));assert_eq!(xs,vec![row(77),row(77),row(0)]);assert_eq!(COPIES.load(Ordering::Relaxed),2);
COPIES.store(0,Ordering::Relaxed);assert_eq!(repeated(row(7)),14);assert_eq!(COPIES.load(Ordering::Relaxed),0);
assert_eq!(escaping(row(7)),row(7));assert_eq!(COPIES.load(Ordering::Relaxed),0);
assert_eq!(moving(row(7)),row(7));assert_eq!(COPIES.load(Ordering::Relaxed),1);
}
"#);
        let dir=std::env::temp_dir().join(format!("ink-callback-ownership-{}",std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();std::fs::write(dir.join("main.rs"),code).unwrap();
        let output=std::process::Command::new("rustc").args(["--edition=2021","-O"]).arg(dir.join("main.rs")).arg("-o").arg(dir.join("run")).output().unwrap();
        assert!(output.status.success(),"{}",String::from_utf8_lossy(&output.stderr));
        let output=std::process::Command::new(dir.join("run")).output().unwrap();std::fs::remove_dir_all(dir).unwrap();
        assert!(output.status.success(),"{}",String::from_utf8_lossy(&output.stderr));
    }
}
