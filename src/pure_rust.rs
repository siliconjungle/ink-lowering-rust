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
    live_loans: std::collections::BTreeSet<String>,
    paths: BTreeMap<usize,Vec<usize>>,
    next: usize,
    prefix: String,
    task_prefix: String,
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
        } else if *t == Type::F64 {
            format!("temporary::ink_f64(({a}) {op} ({b}))")
        } else {
            format!("(({a}) {op} ({b}))")
        }
    }
    fn zero(t: &Type) -> String {
        match t {
            Type::F32 => "0.0f32".into(),
            Type::F64 => "0.0f64".into(),
            Type::I32 => "0i32".into(),
            Type::U32 => "0u32".into(),
            Type::Int => "BigInt::from(0u8)".into(),
            _ => "0u64".into(),
        }
    }
    // Read-only traversals borrow a lexical list instead of cloning the entire
    // vector. Computed receivers still finish eagerly and are consumed once.
    fn borrowed_place(&self, e: &Expr, env: &Env) -> Option<String> {
        // A checked borrowed binding already has an immutable lifetime. Its
        // read-only field observations need no second, globally named marker.
        let borrowed=ink_core::collection_facts::lexical_projection(e).is_some_and(|(root,_)|
            env.get(root).is_some_and(|(binding,_)|self.borrowed_bindings.contains(binding)));
        let mut root=e;while let Expr::Field(parent,_)=root{root=parent;}
        let final_move=matches!(root,Expr::Var(name)if env.get(name).is_some_and(|(binding,_)|!self.borrowed_bindings.contains(binding)&&!self.live_loans.contains(binding)))
            && (self.last_uses.contains(root)||self.last_uses.contains_field(e));
        if self.physical.is_none() && !borrowed && final_move {return None;}
        if !borrowed && self.physical.is_some() && !self.physical.is_some_and(|plan| ink_core::registry::identity(e).is_ok_and(|id| plan.borrows_read(&id))
            || (!final_move&&ink_core::physical::expression_read_site(&self.prefix,e).is_ok_and(|id|plan.borrows_read(&id)))) {return None;}
        self.lexical_place(e, env)
    }
    fn reserved(&self, e: &Expr) -> bool {
        self.reservation.as_ref().is_some_and(|(site,_)|ink_core::registry::identity(e).is_ok_and(|id|id==*site))
    }
    /// An iterator over a list expression and whether it yields `&T`.
    /// Lexical places are borrowed; map/filter stages feeding another
    /// traversal stay lazy instead of materialising an intermediate vector.
    /// Pure callbacks cannot observe the interleaving.
    fn iterate(&mut self, e: &Expr, env: &Env, want: Option<&Type>) -> LangResult<(String, bool)> {
        let t = self.infer(e, env, want)?;
        let Type::List(inner) = &t else { return Err("list receiver".into()) };
        let plain = |me: &Self, item: &Type| crate::columns::names(item).is_none() && !ink_core::local_collections::owned(item, me.p);
        if let Some(place) = self.borrowed_place(e, env) {
            return Ok(if crate::columns::names(inner).is_some() {
                (format!("({place}).iter()"), false)
            } else if !plain(self, inner) {
                (format!("({place}).iter().cloned()"), false)
            } else {
                (format!("({place}).iter()"), true)
            });
        }
        if let Expr::Method(receiver, n, args) = e {
            if matches!(n.as_str(), "map" | "filter") && !self.reserved(e) && plain(self, inner) {
                let rt = self.infer(receiver, env, if n == "filter" { Some(&t) } else { None })?;
                if let Type::List(rin) = rt {
                    if plain(self, &rin) {
                        let (it, borrowed) = self.iterate(receiver, env, if n == "filter" { Some(&t) } else { None })?;
                        if n == "map" {
                            let (vs, body) = self.lambda_mode(&args[0], env, &[*rin], inner, &[borrowed])?;
                            return Ok((format!("({it}).map(|{}|{{{body}}})", vs[0]), false));
                        }
                        let (vs, body) = self.lambda_mode(&args[0], env, &[*rin], &Type::Bool, &[true])?;
                        let bind = if borrowed { "*ink_ref" } else { "ink_ref" };
                        return Ok((format!("({it}).filter(|ink_ref|{{let {}={bind};{body}}})", vs[0]), borrowed));
                    }
                }
            }
        }
        let value = self.expr(e, env, want)?;
        Ok((format!("({value}).into_iter()"), false))
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

    // Computed arguments already produce an owning value. A lexical argument
    // can transfer ownership only at a checked final use outside active loans.
    fn final_owned_argument(&self,e:&Expr,env:&Env)->bool{
        let mut root=e;while let Expr::Field(parent,_)=root{root=parent;}
        let Expr::Var(name)=root else{return true;};
        env.get(name).is_some_and(|(binding,_)|
            !self.borrowed_bindings.contains(binding)&&!self.live_loans.contains(binding))
            &&(self.last_uses.contains(root)||self.last_uses.contains_field(e))
    }

    // Observe a field of a lookup without first cloning the containing row.
    // Finish the short storage borrow before evaluating a missing-row fallback:
    // that fallback may write another scoped range of the same allocation.
    fn projected_item(&mut self,e:&Expr,env:&Env)->LangResult<Option<String>>{
        let Expr::Field(lookup,field)=e else{return Ok(None);};
        let Expr::Method(receiver,method,args)=lookup.as_ref()else{return Ok(None);};
        if method!="at_or"||args.len()!=2{return Ok(None);}
        let container=self.infer(receiver,env,None)?;
        let (Type::List(row)|Type::Buffer(row))=&container else{return Ok(None);};
        let Type::Named(owner)=row.as_ref()else{return Ok(None);};
        if ink_core::local_collections::owned(row,self.p)||crate::columns::names(row).is_some(){return Ok(None);}
        let Some((_,field_ty))=self.p.records.get(owner).and_then(|fs|fs.iter().find(|(name,_)|name==field))else{return Ok(None);};
        let field_ty=field_ty.clone();
        // Moving the receiver's root while computing the index needs an owning
        // snapshot; leave that case on the established literal path.
        if ink_core::collection_facts::lexical_projection(receiver).is_some_and(|(root,_)|references(&args[0],root)){return Ok(None);}
        let receiver_value=if let Some(place)=self.lexical_place(receiver,env){format!("&({place})")}else{self.expr(receiver,env,Some(&container))?};
        let index=self.expr(&args[0],env,Some(&Type::U32))?;
        let fallback=self.expr(&args[1],env,Some(row))?;
        let storage=self.fresh();let position=self.fresh();let selected=self.fresh();let missing=self.fresh();
        let boxed=crate::state_native::boxed_field(owner,&field_ty,self.p);
        let value=if boxed{format!("(*v.l_{field}).clone()")}else{format!("v.l_{field}.clone()")};
        let read=if matches!(container,Type::List(_)){format!("{storage}.get({position} as usize).map(|v|{value})")}else{format!("{storage}.with_item({position},|item|item.map(|v|{value}))")};
        let absent=if boxed{format!("*{missing}.l_{field}")}else{format!("{missing}.l_{field}")};
        Ok(Some(format!("{{let {selected}={{let {storage}={receiver_value};let {position}={index};{read}}};match {selected}{{Some(value)=>value,None=>{{let {missing}={fallback};{absent}}}}}}}")))
    }

    fn lambda(&mut self,e:&Expr,env:&Env,params:&[Type],result:&Type)->LangResult<(Vec<String>,String)> {
        self.lambda_borrows(e,env,params,result,&vec![false;params.len()])
    }
    /// `borrowed[i]` binds parameter `i` to a shared reference: every use
    /// copies the observed value, so it is never moved out of its owner.
    fn lambda_mode(
        &mut self,e:&Expr,env:&Env,params:&[Type],result:&Type,borrowed:&[bool],
    ) -> LangResult<(Vec<String>,String)> {
        self.lambda_borrows(e,env,params,result,borrowed)
    }
    fn lambda_borrows(
        &mut self,e:&Expr,env:&Env,params:&[Type],result:&Type,borrowed:&[bool],
    ) -> LangResult<(Vec<String>,String)> {
        self.lambda_ownership(e,env,params,result,borrowed,false)
    }
    fn lambda_once(&mut self,e:&Expr,env:&Env,params:&[Type],result:&Type)->LangResult<(Vec<String>,String)>{
        self.lambda_ownership(e,env,params,result,&vec![false;params.len()],true)
    }
    fn lambda_ownership(
        &mut self,e:&Expr,env:&Env,params:&[Type],result:&Type,borrowed:&[bool],once:bool,
    )->LangResult<(Vec<String>,String)>{
        if borrowed.len()!=params.len(){return Err("callback borrow arity".into());}
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
        // formal parameters have independent ownership modes. Outer captures
        // remain absent from final-use facts and therefore cannot move.
        let mut formal = Vec::new();
        let mut current = e;
        for _ in params {
            let Expr::Lambda(name, nested) = current else {unreachable!()};
            formal.push(name.as_str());current=nested;
        }
        let mut facts=ink_core::last_use::analyse(body,formal);
        if once{facts.inherit_once(&self.last_uses);}
        let outer=std::mem::replace(&mut self.last_uses,facts);
        let previous_borrows=self.borrowed_bindings.clone();
        self.borrowed_bindings.extend(vars.iter().zip(borrowed).filter(|(_,b)|**b).map(|(v,_)|v.clone()));
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
        let name = format!("{}_{fresh}", self.task_prefix);
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
                Type::F64 => format!("f64::from_bits({}u64)", (*n as f64).to_bits()),
                _ => format!("{n}u64"),
            },
            Expr::Float(b) => format!("f32::from_bits({b}u32)"),
            Expr::Double(b) => format!("f64::from_bits({b}u64)"),
            Expr::Bool(b) => b.to_string(),
            Expr::String(s) => format!("{s:?}.to_owned()"),
            Expr::Unit => "()".into(),
            Expr::Var(n) if n == "None" => "None".into(),
            Expr::Var(n) => {
                let v = &env.get(n).ok_or("missing binding")?.0;
                if self.borrowed_bindings.contains(v) {
                    // Source values remain owned when passed or returned whole.
                    // Clone the referent, not the Rust reference itself.
                    format!("(*{v}).clone()")
                } else if ink_core::local_collections::owned(&t, self.p) || (self.last_uses.contains(e) && !self.live_loans.contains(v)) {
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
                } else if t == Type::F64 {
                    format!("f64::from_bits(({x}).to_bits() ^ 0x8000000000000000)")
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
                    && !(matches!(a.as_ref(),Expr::Var(root) if env.get(root).is_some_and(|(v,_)|!self.borrowed_bindings.contains(v) && !self.live_loans.contains(v))) && self.last_uses.contains(a))
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
                if let Some(projected)=self.projected_item(e,env)?{return Ok(projected);}
                let xt = self.infer(x, env, None)?;
                if let Type::Named(owner) = &xt {
                    if let Some(place) = self.lexical_place(e, env) {
                        let ft = &self.p.records[owner]
                            .iter()
                            .find(|(field, _)| field == n)
                            .ok_or("field")?
                            .1;
                        if !ink_core::local_collections::owned(ft, self.p) {
                            let mut root=e;
                            while let Expr::Field(parent,_)=root {root=parent;}
                            let movable=matches!(root,Expr::Var(name)if env.get(name).is_some_and(|(binding,_)|!self.borrowed_bindings.contains(binding) && !self.live_loans.contains(binding)))
                                && (self.last_uses.contains(root) || self.last_uses.contains_field(e));
                            // A read capability permits borrowing at an earlier
                            // observation; it is not a live loan. Final owning
                            // projections still transfer their field. Borrowed
                            // parameters, captures and pending call loans are
                            // excluded by the binding checks above.
                            if movable {
                                return Ok(if crate::state_native::boxed_field(owner,ft,self.p){format!("*({place})")}else{place});
                            }
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
                } else if (op == "==" || op == "!=") && !matches!(at,Type::F32|Type::F64) {
                    format!(
                        "{}InkDataEq::ink_data_eq(&({a}),&({b}))",
                        if op == "!=" { "!" } else { "" }
                    )
                } else {
                    format!("(({a}) {op} ({b}))")
                }
            }
            Expr::Call(n,args) if ink_core::primitives::primitive(n) => {
                let first=ink_core::primitives::input_type(n,args.first(),|a|self.infer(a,env,None))?;
                let (params,_)=ink_core::primitives::signature(n,first.as_ref())?;
                // Fixed read-only primitives borrow immutable lexical scalar
                // places for this call. Their result never retains the loan;
                // evaluating a computed argument still produces its own value.
                let values=args.iter().zip(params).map(|(a,t)|{
                    if matches!(t,Type::String|Type::Int) {
                        if let Some(place)=self.lexical_place(a,env){return Ok(place);}
                    }
                    self.expr(a,env,Some(&t))
                }).collect::<LangResult<Vec<_>>>()?;
                crate::primitive_emit::expression(n,&values,first.as_ref())?
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
                let xs = if let Some(place) = self.lexical_place(&args[0], env) {
                    place
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
                    "borrow_range" => {
                        let start=self.expr(&args[0],env,Some(&Type::U32))?;
                        let count=self.expr(&args[1],env,Some(&Type::U32))?;
                        let (vars,body)=self.lambda(&args[2],env,&[xt.clone()],&t)?;
                        format!("({xv}).with_range({start},{count},|{}|{{{body}}})",vars[0])
                    }
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
                        let method=if n=="copy_within" && matches!(value,Type::U32|Type::U64|Type::I32|Type::F32|Type::F64|Type::Bool){"copy_within_copy"}else{n.as_str()};
                        format!("({xv}).{method}({a},{b},{c})")
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
                // Each readonly formal can observe the original through a
                // lexical loan. Consumed affine values retain eager copying.
                let params=[inner.as_ref().clone(),t.clone()];
                let types=env.iter().map(|(name,(_,ty))|(name.clone(),ty.clone())).collect();
                let loans=ink_core::local_collections::callback_parameter_loans(&args[2],&types,self.p,&params,&Type::Bool)?;
                let (stopvars, stop) = self.lambda_borrows(&args[2],env,&params,&Type::Bool,&loans)?;
                let (vs, body) = self.lambda(&args[3], env, &[*inner, t.clone()], &t)?;
                let list = self.fresh();
                let acc = self.fresh();
                let item = self.fresh();
                let flag = self.fresh();
                let observed_item=if loans[0]{format!("&{item}")}else{format!("{item}.clone()")};
                let observed_acc=if loans[1]{format!("&{acc}")}else{format!("{acc}.clone()")};
                format!("{{let {list}={xs};let mut {acc}={initial};for {item} in {list}.into_iter() {{let {}={observed_item};let {}={observed_acc};let {flag}={stop};let {}={item};let {}={acc};{acc}={body};if {flag} {{break;}}}}{acc}}}",stopvars[0],stopvars[1],vs[0],vs[1])
            }
            Expr::Call(n, args) if n == "foldr" || n == "foldl" => {
                let Type::List(inner) = self.infer(&args[0], env, None)? else {
                    return Err("fold input".into());
                };
                // The source takes the input value before evaluating the
                // accumulator. An owning accumulator may consume that same
                // root, so preserve a snapshot rather than retaining a loan.
                let initial_alias=ink_core::collection_facts::lexical_projection(&args[0]).is_some_and(|(root,_)|
                    references(&args[1],root)&&env.get(root).is_some_and(|(binding,_)|!self.borrowed_bindings.contains(binding)));
                let (iterator,borrowed)=if initial_alias {
                    (format!("({}).into_iter()",self.expr(&args[0],env,None)?),false)
                } else {self.iterate(&args[0],env,None)?};
                let initial = self.expr(&args[1], env, Some(&t))?;
                let (vs, body) = self.lambda_mode(&args[2], env, &[*inner, t.clone()], &t, &[borrowed, false])?;
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
                if n == "sum" {
                    let (iterator, borrowed) = self.iterate(&args[0], env, context.as_ref())?;
                    let iterator = if borrowed { format!("({iterator}).cloned()") } else { iterator };
                    let acc = self.fresh();
                    let item = self.fresh();
                    return Ok(format!(
                        "({iterator}).fold({},|{acc},{item}|{})",
                        Self::zero(&t),
                        Self::arithmetic("+", &acc, &item, &t)
                    ));
                }
                // count: a lexical list has its length; a computed list
                // is counted without being materialised.
                let length = if let Expr::Var(n) = &args[0] {
                    format!("({}).len()", env.get(n).ok_or("list binding")?.0)
                } else {
                    format!("({}).count()", self.iterate(&args[0], env, context.as_ref())?.0)
                };
                if t == Type::Int {
                    format!("BigInt::from({length})")
                } else {
                    format!("{length} as u64")
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
                let loans=parameter_loans(self.p,&f,self.physical);
                // A loan capability is optional. When every eligible argument
                // can move, keep the owning call so a returned or transferred
                // aggregate does not get cloned inside the borrowed helper.
                let use_loans=args.iter().zip(&loans).any(|(arg,loan)|*loan&&!self.final_owned_argument(arg,env));
                let loan_places:Vec<_>=args.iter().zip(&loans).map(|(e,loan)|{
                    if !*loan{return None;}
                    let (root,_)=ink_core::collection_facts::lexical_projection(e)?;
                    if ink_core::local_collections::owned(&env.get(root)?.1,self.p){return None;}
                    self.lexical_place(e,env)
                }).collect();
                let previous=self.live_loans.clone();
                if use_loans {
                    for (e,place)in args.iter().zip(&loan_places){if place.is_some() {
                        let (root,_)=ink_core::collection_facts::lexical_projection(e).unwrap();
                        self.live_loans.insert(env[root].0.clone());
                    }}
                }
                let emitted=(||->LangResult<String>{
                    for (((e,(_,t)),loan),place)in args.iter().zip(&f.params).zip(&loans).zip(&loan_places){
                        let value=if use_loans && *loan{
                            if let Some(place)=place{format!("&({place})")}
                            else{
                                // Preserve argument order and keep the owning
                                // result alive until this synchronous call ends.
                                let temporary=self.fresh();let computed=self.expr(e,env,Some(t))?;
                                bindings.push_str(&format!("let {temporary}={computed};"));format!("&{temporary}")
                            }
                        }else{self.expr(e,env,Some(t))?};
                        let v=self.fresh();bindings.push_str(&format!("let {v}={value};"));argv.push(v);
                    }
                    Ok(format!("{{{bindings}self.{}function_l_{n}({})}}",if use_loans{"ink_borrowed_"}else{""},argv.join(",")))
                })();
                self.live_loans=previous;
                emitted?
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
                    let (va, body_a) = self.lambda_once(&args[0], env, &[a], &t)?;
                    let (vb, body_b) = self.lambda_once(&args[1], env, &[b], &t)?;
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
                let collection=crate::state_native::ty(&t)?;
                match n.as_str() {
                    "at_or" => {
                        let xs = self.expr(receiver, env, None)?;
                        let index = self.expr(&args[0], env, Some(&Type::U32))?;
                        let fallback = self.expr(&args[1], env, Some(&t))?;
                        let list = self.fresh();
                        let i = self.fresh();
                        // A lexical projection has no evaluation effects. Read
                        // one element without copying its containing list. If
                        // another argument uses the root, retain the ordinary
                        // owned receiver: that argument may consume the root at
                        // its final use while this lookup still needs the list.
                        let xs = if let Some((root, _)) = ink_core::collection_facts::lexical_projection(receiver) {
                            if args.iter().all(|arg| !references(arg, root)) {
                                self.lexical_place(receiver, env).map(|place| format!("&({place})")).unwrap_or(xs)
                            } else { xs }
                        } else { xs };
                        if self.unchecked(e){format!("{{let {list}={xs};let {i}={index};unsafe{{{list}.get_unchecked({i} as usize).clone()}}}}") }else{format!("{{let {list}={xs};let {i}={index};match {list}.get({i} as usize){{Some(v)=>v.clone(),None=>{fallback}}}}}")}
                    }
                    "drop" | "take" => {
                        let xs = self.expr(receiver, env, None)?;
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
                        let xs = self.expr(receiver, env, None)?;
                        let list = self.fresh();
                        format!("{{let mut {list}={xs};{list}.sort();{list}}}")
                    }
                    "scan" => {
                        let (iterator, borrowed) = self.iterate(receiver, env, None)?;
                        let iterator = if borrowed { format!("({iterator}).cloned()") } else { iterator };
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
                        if n=="map"&&self.infer(xs_receiver(e),env,None)?==t&&crate::columns::names(&output).is_some()&&self.borrowed_place(xs_receiver(e),env).is_none()&&!self.reserved(e){
                            let xs = self.expr(receiver, env, None)?;
                            let (vs, body) = self.lambda(&args[0], env, &params, &output)?;
                            let mask=self.column_mask(e,&output);format!("({xs}).map_rows(|{}|{{{body}}},{mask})",vs[0])
                        }else if n=="map" && self.infer(xs_receiver(e),env,None)?==t
                            && matches!(&output,Type::Named(name) if self.p.records.get(name).is_some_and(|fields| fields.iter().all(|(_,ty)| matches!(ty,Type::U32|Type::U64|Type::I32|Type::F32|Type::F64|Type::Bool|Type::Unit))))
                            && self.borrowed_place(xs_receiver(e),env).is_none()
                            && !self.reserved(e) {
                            // Fixed scalar records have no ownership-bearing fields.
                            // Preserve ordered callback evaluation while making the
                            // already-owned input allocation explicit to the host
                            // optimizer. Captured source lists retain their normal
                            // lexical copies; only this private receiver is mutated.
                            let xs = self.expr(receiver, env, None)?;
                            let (vs, body) = self.lambda(&args[0], env, &params, &output)?;
                            let values=self.fresh();let slot=self.fresh();
                            format!("{{let mut {values}={xs};for {slot} in &mut {values}{{let {}=({slot}).clone();*{slot}={body};}}{values}}}",vs[0])
                        }else {
                            let (iterator, borrowed) = self.iterate(receiver, env, if n == "filter" { Some(&t) } else { None })?;
                            if n == "filter" {
                                // The predicate reads each item by reference; only
                                // retained items are copied into the result.
                                let (vs, body) = self.lambda_mode(&args[0], env, &params, &output, &[true])?;
                                let bind = if borrowed { "*ink_ref" } else { "ink_ref" };
                                let retained = if borrowed { ".cloned()" } else { "" };
                                self.collect(e,format!("({iterator}).filter(|ink_ref|{{let {}={bind};{body}}}){retained}",vs[0]),&collection)?
                            } else if n == "map_indexed" {
                                let (vs, body) = self.lambda_mode(&args[0], env, &params, &output, &[false, borrowed])?;
                                self.collect(e,format!("({iterator}).enumerate().map(|(ink_i,{})|{{let {}=ink_i as u32;{body}}})",vs[1],vs[0]),&collection)?
                            } else {
                                let (vs, body) = self.lambda_mode(&args[0], env, &params, &output, &[borrowed])?;
                                self.collect(e,format!("({iterator}).map(|{}|{body})", vs[0]),&collection)?
                            }
                        }
                    }
                    "zip" => {
                        let Type::List(other) = self.infer(&args[0], env, None)? else {
                            return Err("zip input".into());
                        };
                        let Type::List(out) = &t else {
                            return Err("zip output".into());
                        };
                        // Both iterators are alive together. When the operands
                        // share a variable, one may move it while the other
                        // still borrows it, so evaluate both eagerly instead.
                        let shared = ink_core::analysis::free_variables(receiver)
                            .intersection(&ink_core::analysis::free_variables(&args[0]))
                            .next()
                            .is_some();
                        let (left, left_borrowed) = if shared {
                            (format!("({}).into_iter()", self.expr(receiver, env, None)?), false)
                        } else {
                            self.iterate(receiver, env, None)?
                        };
                        let (right, right_borrowed) = if shared {
                            (format!("({}).into_iter()", self.expr(&args[0], env, None)?), false)
                        } else {
                            self.iterate(&args[0], env, None)?
                        };
                        let (vs, body) = self.lambda_mode(&args[1], env, &[*inner, *other], out, &[left_borrowed, right_borrowed])?;
                        let a = self.fresh();
                        let b = self.fresh();
                        format!("{{let {a}={left};let {b}={right};{}}}",self.collect(e,format!("{a}.zip({b}).map(|({},{})|{body})",vs[0],vs[1]),&collection)?)
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
    body_with_tasks_loans(p,f,physical,&vec![false;f.params.len()])
}
// Public entry points retain their owning ABI. A private implementation can
// borrow immutable parameters whose lexical reads were independently admitted.
// Computed arguments and projections out of affine owners are materialised
// before borrowing; their owning temporaries live for the complete call.
pub(crate) fn parameter_loans(p:&Program,f:&Function,physical:Option<&ink_core::physical::CheckedPhysicalPlan>)->Vec<bool>{
    f.params.iter().map(|(n,t)|!ink_core::recursion::recursive(f) && matches!(t,Type::List(_)|Type::Named(_)) && !ink_core::local_collections::owned(t,p)
        && physical.is_some_and(|plan|ink_core::physical::parameter_read_site(&f.name,n).is_ok_and(|id|plan.borrows_read(&id))
            || ink_core::registry::identity(&Expr::Var(n.clone())).is_ok_and(|id|plan.borrows_read(&id)))).collect()
}
pub(crate) fn body_with_tasks_loans(p:&Program,f:&Function,physical:Option<&ink_core::physical::CheckedPhysicalPlan>,loans:&[bool])->LangResult<(String,Vec<(String,String)>)>{
    if loans.len()!=f.params.len(){return Err("function borrow arity".into());}
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
        borrowed_bindings:f.params.iter().zip(loans).filter(|(_,loan)|**loan).map(|((n,_),_)|format!("l_{n}")).collect(),
        live_loans:Default::default(),
        next: 0,
        prefix: f.name.clone(),
        task_prefix:if loans.iter().any(|b|*b){format!("__ink_borrowed_{}",f.name)}else{f.name.clone()},
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
    fn borrowed_fold_rows_preserve_owned_accumulators_captures_and_escaping_values() {
        let mut p=parse(r#"module folds;
record Item{key:u32,payload:List<u32>,}
record Owner{rows:List<Item>,data:Buffer<u32>,}
fn observed(xs:List<Item>)->u32{return foldl(xs,0,fn(item,acc)=>acc+item.key);}
fn aliased(xs:List<Item>)->u32{return foldl(xs,0,fn(item,acc)=>acc+item.key);}
fn left(xs:List<Item>)->u32{return foldl(xs,0,fn(item,acc)=>acc*10+item.key);}
fn right(xs:List<Item>)->u32{return foldr(xs,0,fn(item,acc)=>acc*10+item.key);}
fn collected(xs:List<Item>,offset:u32)->List<u32>{let out:Buffer<u32>=foldl(xs,Buffer.empty(),fn(item,out)=>out.push(item.key+offset));return out.freeze();}
fn escaped(xs:List<Item>)->List<Item>{let out:Buffer<Item>=foldl(xs,Buffer.empty(),fn(item,out)=>out.push(item));return out.freeze();}
fn whole(item:Item)->u32{return item.key+length(item.payload);}
fn called(xs:List<Item>)->u32{return foldl(xs,0,fn(item,acc)=>acc+whole(item));}
fn captured(xs:List<Item>,offsets:List<u32>)->u32{return foldl(xs,0,fn(item,acc)=>foldl(offsets,acc,fn(offset,total)=>total+offset+item.key));}
fn two(a:List<Item>,b:List<Item>)->u32{return observed(a)+observed(b);}
fn repeated(xs:List<Item>)->u32{return two(xs,xs);}
fn computed()->u32{return observed([Item{key:4,payload:[]}]);}
fn mixed(rows:List<Item>,owner:Owner)->u32{return observed(rows)+sum(owner.data.freeze());}
fn from_owner(xs:List<Item>)->u32{let owner=Owner{rows:xs,data:buffer([9])};return mixed(owner.rows,owner);}
"#).unwrap();
        // The executable core also admits lexical bindings within callbacks.
        // Its surface expression grammar does not currently expose a block.
        let f=p.functions.iter_mut().find(|f|f.name=="aliased").unwrap();
        let sum=Expr::Binary("+".into(),Box::new(Expr::Var("acc".into())),Box::new(Expr::Field(Box::new(Expr::Var("alias".into())),"key".into())));
        let binding=Expr::Let("alias".into(),None,Box::new(Expr::Var("item".into())),Box::new(sum));
        let callback=Expr::Lambda("item".into(),Box::new(Expr::Lambda("acc".into(),Box::new(binding))));
        f.body=Expr::Call("foldl".into(),vec![Expr::Var("xs".into()),Expr::Num(0),callback]);
        check::check(&p).unwrap();
        let module=ink_core::core::CheckedModule::from_source(p.clone()).unwrap();
        let mut sites=std::collections::BTreeSet::new();
        for f in &p.functions {
            ink_core::analysis::typed_walk(&p,f,|e,env|{
                if ink_core::collection_facts::lexical_projection(e).is_some_and(|(root,_)|matches!(env.get(root),Some(Type::Named(_)|Type::List(_)))) && ink_core::check::infer(e,env,&p).is_ok(){sites.insert(ink_core::registry::identity(e).unwrap());}
            }).unwrap();
        }
        let physical=ink_core::physical::check(&module,None,&ink_core::physical::Plan{schema:1,semantics:ink_core::physical::SEMANTICS.into(),input_core_sha256:module.identity().unwrap(),representation:None,tables:Default::default(),buffers:Default::default(),bounds:None,columns:vec![],column_maps:None,borrow_reads:sites.into_iter().collect(),borrow_rows:vec![],definitions:Default::default(),packed_datatypes:vec![],memo_functions:vec![],reservations:vec![],inline_functions:vec![],record_elisions:vec![],sum_spines:vec![],dense_prefixes:vec![],dictionary_tables:vec![],boundary_readers:vec![]}).unwrap();
        let mut source=String::from(r#"
#![allow(non_camel_case_types)]
use std::sync::atomic::{AtomicUsize,Ordering};
static COPIES:AtomicUsize=AtomicUsize::new(0);
struct l_Item{l_key:u32,l_payload:Vec<u32>}
impl Clone for l_Item{fn clone(&self)->Self{COPIES.fetch_add(1,Ordering::Relaxed);Self{l_key:self.l_key,l_payload:self.l_payload.clone()}}}
// Intentionally not Clone: a fold must transfer this accumulator by ownership.
struct OwnedBuffer<T:Clone>(Vec<T>);
impl<T:Clone> OwnedBuffer<T>{fn new(xs:Vec<T>)->Self{Self(xs)}fn push(mut self,x:T)->Self{self.0.push(x);self}fn freeze(self)->Vec<T>{self.0}}
struct l_Owner{l_rows:Vec<l_Item>,l_data:OwnedBuffer<u32>}
struct Test;
impl Test{
"#);
        for (name,params,result)in [
            ("observed","l_xs:Vec<l_Item>","u32"),("aliased","l_xs:Vec<l_Item>","u32"),
            ("left","l_xs:Vec<l_Item>","u32"),("right","l_xs:Vec<l_Item>","u32"),
            ("collected","l_xs:Vec<l_Item>,l_offset:u32","Vec<u32>"),
            ("escaped","l_xs:Vec<l_Item>","Vec<l_Item>"),
            ("whole","l_item:l_Item","u32"),("called","l_xs:Vec<l_Item>","u32"),
            ("captured","l_xs:Vec<l_Item>,l_offsets:Vec<u32>","u32"),
            ("two","l_a:Vec<l_Item>,l_b:Vec<l_Item>","u32"),("repeated","l_xs:Vec<l_Item>","u32"),
            ("computed","","u32"),("mixed","l_rows:Vec<l_Item>,l_owner:l_Owner","u32"),("from_owner","l_xs:Vec<l_Item>","u32"),
        ] {
            let f=p.functions.iter().find(|f|f.name==name).unwrap();
            source.push_str(&format!("fn function_l_{name}(&self,{params})->{result}{{{}}}\n",body_with_tasks_planned(&p,f,Some(&physical)).unwrap().0));
            let loans=parameter_loans(&p,f,Some(&physical));
            if loans.iter().any(|b|*b){
                let params=f.params.iter().zip(&loans).map(|((n,t),loan)|format!("l_{n}:{}{}",if *loan{"&"}else{""},crate::state_native::ty(t).unwrap())).collect::<Vec<_>>().join(",");
                source.push_str(&format!("fn ink_borrowed_function_l_{name}(&self,{params})->{result}{{{}}}\n",body_with_tasks_loans(&p,f,Some(&physical),&loans).unwrap().0));
            }

        }
        source.push_str(r#"}
fn main(){
let xs=(1..=3).map(|key|l_Item{l_key:key,l_payload:vec![7;1000]}).collect::<Vec<_>>();let t=Test;
assert_eq!(t.ink_borrowed_function_l_observed(&xs),6);assert_eq!(t.ink_borrowed_function_l_aliased(&xs),6);
assert_eq!(t.ink_borrowed_function_l_left(&xs),123);assert_eq!(t.ink_borrowed_function_l_right(&xs),321);
assert_eq!(t.ink_borrowed_function_l_collected(&xs,9),vec![10,11,12]);
assert_eq!(t.ink_borrowed_function_l_captured(&xs,&vec![1,2]),21);
assert_eq!(t.ink_borrowed_function_l_repeated(&xs),12);assert_eq!(t.function_l_computed(),4);
assert_eq!(COPIES.swap(0,Ordering::Relaxed),0);
let escaped=t.ink_borrowed_function_l_escaped(&xs);assert_eq!(escaped.iter().map(|x|x.l_key).collect::<Vec<_>>(),vec![1,2,3]);
assert_eq!(COPIES.swap(0,Ordering::Relaxed),3);
assert_eq!(t.ink_borrowed_function_l_called(&xs),3006);assert_eq!(COPIES.swap(0,Ordering::Relaxed),0);
assert_eq!(xs[0].l_payload.len(),1000);
let fresh=(1..=3).map(|key|l_Item{l_key:key,l_payload:vec![7;1000]}).collect();
assert_eq!(t.function_l_from_owner(fresh),15);assert_eq!(COPIES.swap(0,Ordering::Relaxed),3);
}
"#);
        let dir=std::env::temp_dir().join(format!("ink-fold-row-read-{}",std::process::id()));
        fs::create_dir_all(&dir).unwrap();fs::write(dir.join("test.rs"),source).unwrap();
        let out=Command::new("rustc").args(["--edition=2021","-O"]).arg(dir.join("test.rs")).arg("-o").arg(dir.join("test")).output().unwrap();
        assert!(out.status.success(),"{}",String::from_utf8_lossy(&out.stderr));
        assert!(Command::new(dir.join("test")).status().unwrap().success());fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn record_rebuild_moves_disjoint_vectors_but_repeated_and_captured_fields_copy(){
        let p=parse(r#"module field_moves;
record Item{value:u32,}
record Copies{a:List<Item>,b:List<Item>,}
record Frame{first:List<Item>,second:List<Item>,storage:Buffer<u32>,marker:u32,}
fn changed(frame:Frame)->Frame{return Frame{..frame,marker:frame.marker+1};}
fn repeated(frame:Frame)->Copies{return Copies{a:frame.first,b:frame.first};}
fn captured(frame:Frame)->List<List<Item>>{return [0,1].map(fn(i)=>frame.first);}
"#).unwrap();check::check(&p).unwrap();
        let module=ink_core::core::CheckedModule::from_source(p.clone()).unwrap();
        let mut sites=std::collections::BTreeSet::new();
        for f in &p.functions {
            ink_core::analysis::typed_walk(&p,f,|e,env|{
                if ink_core::collection_facts::lexical_projection(e).is_some_and(|(root,_)|matches!(env.get(root),Some(Type::Named(_)|Type::List(_)))) && ink_core::check::infer(e,env,&p).is_ok(){sites.insert(ink_core::registry::identity(e).unwrap());}
            }).unwrap();
        }
        let physical=ink_core::physical::check(&module,None,&ink_core::physical::Plan{schema:1,semantics:ink_core::physical::SEMANTICS.into(),input_core_sha256:module.identity().unwrap(),representation:None,tables:Default::default(),buffers:Default::default(),bounds:None,columns:vec![],column_maps:None,borrow_reads:sites.into_iter().collect(),borrow_rows:vec![],definitions:Default::default(),packed_datatypes:vec![],memo_functions:vec![],reservations:vec![],inline_functions:vec![],record_elisions:vec![],sum_spines:vec![],dense_prefixes:vec![],dictionary_tables:vec![],boundary_readers:vec![]}).unwrap();
        let mut source=String::from(r#"
#![allow(non_camel_case_types,dead_code,unused_variables)]
use std::sync::atomic::{AtomicUsize,Ordering};
static COPIES:AtomicUsize=AtomicUsize::new(0);
struct l_Item{l_value:u32}
impl Clone for l_Item{fn clone(&self)->Self{COPIES.fetch_add(1,Ordering::Relaxed);Self{l_value:self.l_value}}}
struct OwnedBuffer<T>(Vec<T>);
struct l_Copies{l_a:Vec<l_Item>,l_b:Vec<l_Item>}
struct l_Frame{l_first:Vec<l_Item>,l_second:Vec<l_Item>,l_storage:OwnedBuffer<u32>,l_marker:u32}
struct Test;
impl Test{
"#);
        for (name,result)in [("changed","l_Frame"),("repeated","l_Copies"),("captured","Vec<Vec<l_Item>>")]{
            let f=p.functions.iter().find(|f|f.name==name).unwrap();
            source.push_str(&format!("fn function_l_{name}(&self,l_frame:l_Frame)->{result}{{{}}}\n",body_with_tasks_planned(&p,f,Some(&physical)).unwrap().0));
        }
        source.push_str(r#"}
fn fresh()->l_Frame{l_Frame{l_first:(0..3).map(|value|l_Item{l_value:value}).collect(),l_second:(3..6).map(|value|l_Item{l_value:value}).collect(),l_storage:OwnedBuffer(vec![7]),l_marker:8}}
fn main(){
 let t=Test;let frame=fresh();let a=frame.l_first.as_ptr();let b=frame.l_second.as_ptr();
 let changed=t.function_l_changed(frame);assert_eq!(changed.l_first.as_ptr(),a);assert_eq!(changed.l_second.as_ptr(),b);assert_eq!(changed.l_marker,9);
 assert_eq!(COPIES.swap(0,Ordering::Relaxed),0);
 let repeated=t.function_l_repeated(fresh());assert_eq!(repeated.l_a.len()+repeated.l_b.len(),6);assert_eq!(COPIES.swap(0,Ordering::Relaxed),3);
 let captured=t.function_l_captured(fresh());assert_eq!(captured.len(),2);assert_eq!(COPIES.swap(0,Ordering::Relaxed),6);
}
"#);
        let dir=std::env::temp_dir().join(format!("ink-field-move-{}",std::process::id()));fs::create_dir_all(&dir).unwrap();fs::write(dir.join("test.rs"),source).unwrap();
        let compiled=Command::new("rustc").args(["--edition=2021","-O"]).arg(dir.join("test.rs")).arg("-o").arg(dir.join("test")).output().unwrap();
        assert!(compiled.status.success(),"{}",String::from_utf8_lossy(&compiled.stderr));
        assert!(Command::new(dir.join("test")).status().unwrap().success());fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn nested_record_reads_clone_only_observed_elements() {
        let p=parse(r#"module fields;
record Item{key:u32,} record Inner{first:List<Item>,second:List<Item>,id:u32,} record Outer{nested:Inner,}
fn key(r:Outer)->u32{return r.nested.id;}
fn mapped(r:Outer)->List<u32>{return r.nested.first.map(fn(x)=>x.key+1);}
fn joined(r:Outer)->List<Item>{return r.nested.first.concat(r.nested.first);}
fn selected(r:Outer)->List<Item>{return r.nested.first;}
fn observed_length(r:Outer)->u32{return length(r.nested.first);}
fn item(r:Outer,i:u32)->Item{return r.nested.first.at_or(i,Item{key:99});}
"#).unwrap();
        check::check(&p).unwrap();
        let module=ink_core::core::CheckedModule::from_source(p.clone()).unwrap();
        let mut sites=std::collections::BTreeSet::new();
        for f in &p.functions {ink_core::analysis::typed_walk(&p,f,|e,env|if ink_core::collection_facts::lexical_projection(e).is_some_and(|(root,_)|matches!(env.get(root),Some(Type::Named(_)|Type::List(_))))&&ink_core::check::infer(e,env,&p).is_ok(){sites.insert(ink_core::registry::identity(e).unwrap());}).unwrap();}
        sites.insert(ink_core::registry::identity(&Expr::Field(Box::new(Expr::Var("x".into())),"key".into())).unwrap());
        let physical=ink_core::physical::check(&module,None,&ink_core::physical::Plan{schema:1,semantics:ink_core::physical::SEMANTICS.into(),input_core_sha256:module.identity().unwrap(),representation:None,tables:Default::default(), buffers:Default::default(), bounds:None, columns:vec![],record_elisions:vec![],sum_spines:vec![],column_maps:None,borrow_reads:sites.into_iter().collect(),borrow_rows:vec![],definitions:Default::default(),packed_datatypes:vec![],memo_functions:vec![],reservations:vec![],dense_prefixes:vec![],dictionary_tables:vec![],boundary_readers:vec![],inline_functions:vec![]}).unwrap();

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
            ("observed_length", "u32"),
        ] {
            let f = p.functions.iter().find(|f| f.name == name).unwrap();
            source.push_str(&format!(
                "fn {name}(l_r:&l_Outer)->{result}{{{}}}\n",
                body_with_tasks_loans(&p,f,Some(&physical),&[true]).unwrap().0
            ));
        }
        let f=p.functions.iter().find(|f|f.name=="item").unwrap();
        source.push_str(&format!("fn item(l_r:&l_Outer,l_i:u32)->l_Item{{{}}}\n",body_with_tasks_loans(&p,f,Some(&physical),&[true,false]).unwrap().0));
        source.push_str(r#"
fn main(){
let r=l_Outer{l_nested:l_Inner{l_first:vec![l_Item{l_key:0},l_Item{l_key:u32::MAX},l_Item{l_key:9}],l_second:(0..1000).map(|i|l_Item{l_key:i}).collect(),l_id:17}};
assert_eq!(key(&r),17);assert_eq!(COPIES.load(Ordering::Relaxed),0);
// The callback reads one field through a borrow; no element is copied.
assert_eq!(mapped(&r),vec![1,0,10]);assert_eq!(COPIES.swap(0,Ordering::Relaxed),0);
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
        let physical=ink_core::physical::check(&module,None,&ink_core::physical::Plan{schema:1,semantics:ink_core::physical::SEMANTICS.into(),input_core_sha256:module.identity().unwrap(),representation:None,tables:Default::default(), buffers:Default::default(), bounds:None, columns:vec![],record_elisions:vec![],sum_spines:vec![],column_maps:None,borrow_reads:sites,borrow_rows:vec![],definitions:Default::default(),packed_datatypes:vec![],memo_functions:vec![],reservations:vec![],dense_prefixes:vec![],dictionary_tables:vec![],boundary_readers:vec![],inline_functions:vec![]}).unwrap();

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
mod projected_list_read_tests {
    use super::*;

    #[test]
    fn nested_reads_copy_only_the_selected_value_and_preserve_consuming_arguments() {
        let p=parse(r#"module projected_reads;
record Item { value:u32, }
record Inner { items:List<Item>, }
record Outer { inner:Inner, }
fn size(r:Outer)->u32{return length(r.inner.items);}
fn pick(r:Outer,i:u32)->Item{return r.inner.items.at_or(i,fallback());}
fn captured(r:Outer)->List<u32>{let ids:List<u32>=[0,1,2];return ids.map(fn(i)=>r.inner.items.at_or(i,Item{value:99}).value+length(r.inner.items));}
fn consume(r:Outer)->u32{return length(r.inner.items)-1;}
fn index_consumes(r:Outer)->Item{return r.inner.items.at_or(consume(r),fallback());}
fn fallback_consumes(r:Outer)->Item{return r.inner.items.at_or(99,Item{value:consume(r)});}
fn consume_list(xs:List<Item>)->u32{return length(xs)-1;}
fn plain_index_consumes(xs:List<Item>)->Item{return xs.at_or(consume_list(xs),fallback());}
fn identity(r:Outer)->Outer{return r;}
fn computed(r:Outer)->Item{return identity(r).inner.items.at_or(1,fallback());}
fn fallback()->Item{return Item{value:99};}
"#).unwrap();
        check::check(&p).unwrap();
        let mut code=String::from(r#"
#![allow(non_camel_case_types,unused_variables,unused_parens)]
use std::sync::atomic::{AtomicUsize,Ordering};
static COPIES:AtomicUsize=AtomicUsize::new(0);
static FALLBACKS:AtomicUsize=AtomicUsize::new(0);
static COMPUTED:AtomicUsize=AtomicUsize::new(0);
#[derive(Debug,PartialEq)]struct l_Item{l_value:u32}
impl Clone for l_Item{fn clone(&self)->Self{COPIES.fetch_add(1,Ordering::Relaxed);Self{l_value:self.l_value}}}
#[derive(Clone)]struct l_Inner{l_items:Vec<l_Item>}
#[derive(Clone)]struct l_Outer{l_inner:l_Inner}
struct State;
impl State {
fn function_l_fallback(&self)->l_Item{FALLBACKS.fetch_add(1,Ordering::Relaxed);l_Item{l_value:99}}
fn function_l_identity(&self,r:l_Outer)->l_Outer{COMPUTED.fetch_add(1,Ordering::Relaxed);r}
"#);
        for f in &p.functions {
            if ["fallback","identity"].contains(&f.name.as_str()){continue;}
            let params=f.params.iter().map(|(n,t)|format!("l_{n}:{}",crate::state_native::ty(t).unwrap())).collect::<Vec<_>>().join(",");
            code.push_str(&format!("fn function_l_{}(&self,{params})->{}{{{}}}\n",f.name,crate::state_native::ty(&f.result).unwrap(),body(&p,f).unwrap()));
        }
        code.push_str(r#"
}
fn record(n:u32)->l_Outer{l_Outer{l_inner:l_Inner{l_items:(0..n).map(|v|l_Item{l_value:v+10}).collect()}}}
fn main(){
let state=State;
assert_eq!(state.function_l_size(record(4096)),4096);assert_eq!(COPIES.load(Ordering::Relaxed),0);
assert_eq!(state.function_l_size(record(0)),0);assert_eq!(COPIES.load(Ordering::Relaxed),0);
assert_eq!(state.function_l_pick(record(4096),17).l_value,27);assert_eq!(COPIES.load(Ordering::Relaxed),1);
assert_eq!(FALLBACKS.load(Ordering::Relaxed),0);
assert_eq!(state.function_l_pick(record(0),0).l_value,99);assert_eq!(FALLBACKS.load(Ordering::Relaxed),1);
assert_eq!(state.function_l_pick(record(4),u32::MAX).l_value,99);assert_eq!(FALLBACKS.load(Ordering::Relaxed),2);
COPIES.store(0,Ordering::Relaxed);
// Read-only callback rows borrow each item; the full output is unchanged.
assert_eq!(state.function_l_captured(record(2)),vec![12,13,101]);assert_eq!(COPIES.load(Ordering::Relaxed),0);
assert_eq!(state.function_l_index_consumes(record(3)).l_value,12);
assert_eq!(state.function_l_fallback_consumes(record(3)).l_value,2);
assert_eq!(state.function_l_plain_index_consumes(record(3).l_inner.l_items).l_value,12);
assert_eq!(state.function_l_computed(record(3)).l_value,11);assert_eq!(COMPUTED.load(Ordering::Relaxed),1);
assert_eq!(FALLBACKS.load(Ordering::Relaxed),2);
}
"#);
        let dir=std::env::temp_dir().join(format!("ink-projected-list-reads-{}",std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();std::fs::write(dir.join("main.rs"),code).unwrap();
        let output=std::process::Command::new("rustc").args(["--edition=2021","-O"]).arg(dir.join("main.rs")).arg("-o").arg(dir.join("run")).output().unwrap();
        assert!(output.status.success(),"{}",String::from_utf8_lossy(&output.stderr));
        let output=std::process::Command::new(dir.join("run")).output().unwrap();std::fs::remove_dir_all(dir).unwrap();
        assert!(output.status.success(),"{}",String::from_utf8_lossy(&output.stderr));
    }
}

#[cfg(test)]
mod callback_ownership_tests {
    use super::*;
    #[test]
    fn owned_stop_observations_avoid_copies_and_keep_terminal_step() {
        let program=parse(r#"module StopLoans;
record Row{key:u32,label:String,}
record Inner{rows:Buffer<Row>,done:Bool,}
record State{inner:Inner,total:u32,}
fn observed(xs:List<u32>,seed:State)->State{
 return fold_until(xs,seed,fn(x)=>fn(s)=>s.inner.done,
  fn(x)=>fn(s)=>State{inner:Inner{rows:s.inner.rows,done:x>=2 && x<=2},total:s.total+x});
}
fn consumed(xs:List<u32>,seed:State)->State{
 return fold_until(xs,seed,fn(x)=>fn(s)=>consume(s),
  fn(x)=>fn(s)=>State{inner:s.inner,total:s.total+x});
}
fn consume(s:State)->Bool{let rows=s.inner.rows.freeze();return length(rows)>0;}
fn mutated(xs:List<u32>,seed:Buffer<u32>)->Buffer<u32>{
 return fold_until(xs,seed,fn(x)=>fn(s)=>s.push(99).len()>0,
  fn(x)=>fn(s)=>s.push(x));
}
"#).unwrap();
        for (name,want) in [("observed",vec![true,true]),("consumed",vec![true,false]),("mutated",vec![true,false])] {
            let f=program.functions.iter().find(|f|f.name==name).unwrap();
            let Expr::Call(_,args)=&f.body else{panic!("fold body");};
            let Type::List(item)=&f.params[0].1 else{panic!("list parameter");};
            let types=f.params.iter().cloned().collect();
            assert_eq!(ink_core::local_collections::callback_parameter_loans(&args[2],&types,&program,&[item.as_ref().clone(),f.result.clone()],&Type::Bool).unwrap(),want,"{name}");
        }
        assert!(check::check(&program).unwrap_err().contains("borrowed temporary storage"));
        let mut program=program;
        program.functions.retain(|f|f.name=="observed");
        check::check(&program).unwrap();
        let mut code=String::from(r#"
#![allow(non_camel_case_types,unused_variables,unused_parens,dead_code)]
use std::sync::atomic::{AtomicUsize,Ordering};
static COPIES:AtomicUsize=AtomicUsize::new(0);
#[derive(Debug,PartialEq)]struct l_Row{l_key:u32,l_label:String}
impl Clone for l_Row{fn clone(&self)->Self{COPIES.fetch_add(1,Ordering::Relaxed);Self{l_key:self.l_key,l_label:self.l_label.clone()}}}
#[derive(Clone)]struct l_Inner{l_rows:OwnedBuffer<l_Row>,l_done:bool}
#[derive(Clone)]struct l_State{l_inner:l_Inner,l_total:u32}
"#);
        code.push_str(ink_native_support::OWNED_VALUES_RUST_SOURCE);
        for f in &program.functions {
            let params=f.params.iter().map(|(n,t)|format!("l_{n}:{}",crate::state_native::ty(t).unwrap())).collect::<Vec<_>>().join(",");
            let emitted=body(&program,f).unwrap().replace("self.function_l_","");
            code.push_str(&format!("fn {}({params})->{}{{{emitted}}}\n",f.name,crate::state_native::ty(&f.result).unwrap()));
        }
        code.push_str(r#"
fn seed(done:bool)->l_State{l_State{l_inner:l_Inner{l_rows:OwnedBuffer::new(vec![l_Row{l_key:7,l_label:"row".into()}]),l_done:done},l_total:0}}
fn main(){
 let result=observed(vec![1,2,3,4],seed(false));
 assert_eq!(result.l_total,6);assert_eq!(result.l_inner.l_rows.len(),1);
 assert_eq!(COPIES.load(Ordering::Relaxed),0);
 assert_eq!(observed(vec![1,2],seed(true)).l_total,1);
 assert_eq!(observed(vec![],seed(true)).l_total,0);
 assert_eq!(COPIES.load(Ordering::Relaxed),0);
}
"#);
        let dir=std::env::temp_dir().join(format!("ink-owned-stop-loans-{}",std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();std::fs::write(dir.join("main.rs"),code).unwrap();
        let output=std::process::Command::new("rustc").args(["--edition=2021","-O"]).arg(dir.join("main.rs")).arg("-o").arg(dir.join("run")).output().unwrap();
        assert!(output.status.success(),"{}",String::from_utf8_lossy(&output.stderr));
        let output=std::process::Command::new(dir.join("run")).output().unwrap();std::fs::remove_dir_all(dir).unwrap();
        assert!(output.status.success(),"{}",String::from_utf8_lossy(&output.stderr));
    }
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
record Bag{rows:List<Row>,}
fn projected_field(bag:Bag)->List<Row>{return bag.rows;}
fn repeated_field(bag:Bag)->List<Row>{let keep=bag.rows;return bag.rows;}
fn branch(xs:List<Row>,yes:Bool)->List<Row>{return choose(yes,xs,xs);}
fn branch_followed(xs:List<Row>,yes:Bool)->List<Row>{let temporary=choose(yes,xs,xs);return xs;}
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
#[derive(Clone)]struct l_Bag{l_rows:Vec<l_Row>}
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
COPIES.store(0,Ordering::Relaxed);assert_eq!(projected_field(l_Bag{l_rows:vec![row(1),row(2)]}),vec![row(1),row(2)]);assert_eq!(COPIES.load(Ordering::Relaxed),0);
assert_eq!(repeated_field(l_Bag{l_rows:vec![row(1),row(2)]}),vec![row(1),row(2)]);assert_eq!(COPIES.load(Ordering::Relaxed),2);
for yes in [true,false]{
 COPIES.store(0,Ordering::Relaxed);assert_eq!(branch(vec![row(1),row(2)],yes),vec![row(1),row(2)]);assert_eq!(COPIES.load(Ordering::Relaxed),0);
 assert_eq!(branch_followed(vec![row(1),row(2)],yes),vec![row(1),row(2)]);assert_eq!(COPIES.load(Ordering::Relaxed),2);
}
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

#[cfg(test)]
mod scalar_record_map_tests {
    use super::*;
    use std::{fs,process::Command};

    #[test]
    fn ordered_maps_reuse_private_storage_and_keep_captured_inputs_unchanged() {
        let p=crate::syntax::parse(r#"module scalar_maps;
record R { value:u32, wide:u64, signed:i32, flag:Bool, raw:f32, unit:Unit, }
fn update(xs:List<R>,amount:u32)->List<R>{
 return xs.map(fn(x)=>R{value:x.value+amount,wide:x.wide,signed:x.signed,flag:!x.flag,raw:x.raw,unit:()});
}
fn captured(xs:List<R>)->List<R>{
 return xs.map(fn(x)=>R{value:x.value+xs.at_or(0,x).value,wide:x.wide,signed:x.signed,flag:x.flag,raw:xs.at_or(1,x).raw,unit:()});
}
fn branches(xs:List<R>)->List<R>{
 return xs.map(fn(x)=>if x.flag {x} else {R{value:x.value+1,wide:x.wide,signed:x.signed,flag:true,raw:x.raw,unit:()}});
}
"#).unwrap();
        check::check(&p).unwrap();
        let mut source=String::from("#![allow(non_camel_case_types,unused_parens)]\n#[derive(Clone)]struct l_R{l_value:u32,l_wide:u64,l_signed:i32,l_flag:bool,l_raw:f32,l_unit:()}\n");
        source.push_str("trait InkDataEq{fn ink_data_eq(&self,other:&Self)->bool;}impl InkDataEq for bool{fn ink_data_eq(&self,other:&Self)->bool{self==other}}\n");
        for f in &p.functions {
            let args=f.params.iter().map(|(n,t)|format!("l_{n}:{}",crate::state_native::ty(t).unwrap())).collect::<Vec<_>>().join(",");
            source.push_str(&format!("fn {}({args})->Vec<l_R>{{{}}}\n",f.name,body_with_tasks_planned(&p,f,None).unwrap().0));
        }
        source.push_str(r#"
fn row(value:u32,raw:u32)->l_R{l_R{l_value:value,l_wide:u64::MAX,l_signed:i32::MIN,l_flag:false,l_raw:f32::from_bits(raw),l_unit:()}}
fn main(){
 for bits in [0,0x80000000,1,0x7f800000,0xff800000,0x7fa12345,0xff812345]{
  let mut xs=Vec::with_capacity(17);xs.extend([row(u32::MAX,bits),row(3,bits)]);let storage=xs.as_ptr();
  let out=update(xs,2);assert_eq!(storage,out.as_ptr());assert_eq!(out[0].l_value,1);assert_eq!(out[1].l_value,5);
  assert!(out.iter().all(|x|x.l_raw.to_bits()==bits&&x.l_wide==u64::MAX&&x.l_signed==i32::MIN&&x.l_flag));
 }
 let xs=vec![row(2,0),row(3,0x7fa12345),row(4,0x80000000)];
 let out=captured(xs.clone());assert_eq!(out.iter().map(|x|x.l_value).collect::<Vec<_>>(),vec![4,5,6]);
 assert!(out.iter().all(|x|x.l_raw.to_bits()==0x7fa12345));
 assert_eq!(xs.iter().map(|x|x.l_value).collect::<Vec<_>>(),vec![2,3,4]);
 let mut xs=vec![row(u32::MAX,0x80000000),row(9,0x7fa12345)];xs[1].l_flag=true;
 let out=branches(xs);assert_eq!(out[0].l_value,0);assert_eq!(out[1].l_value,9);
 assert_eq!(out[0].l_raw.to_bits(),0x80000000);assert_eq!(out[1].l_raw.to_bits(),0x7fa12345);
 assert!(update(Vec::new(),0).is_empty());assert!(captured(Vec::new()).is_empty());
}
"#);
        let dir=std::env::temp_dir().join(format!("ink-scalar-map-{}",std::process::id()));
        fs::create_dir_all(&dir).unwrap();fs::write(dir.join("main.rs"),source).unwrap();
        let out=Command::new("rustc").args(["--edition=2021","-O"]).arg(dir.join("main.rs")).arg("-o").arg(dir.join("run")).output().unwrap();
        assert!(out.status.success(),"{}",String::from_utf8_lossy(&out.stderr));
        assert!(Command::new(dir.join("run")).status().unwrap().success());fs::remove_dir_all(dir).unwrap();
    }
}

#[cfg(test)]
mod primitive_loan_tests {
    use super::*;
    use std::{fs,process::Command};

    #[test]
    fn readonly_string_primitives_do_not_clone_lexical_bytes() {
        let program=crate::syntax::parse(r#"module text_loans;
record Pair{text:String,needle:String,}
fn sizes(text:String)->u32{return string_byte_len(text)+string_byte_len(text);}
fn locate(pair:Pair,start:u32)->Option<u32>{return string_find(pair.text,pair.needle,start);}
fn self_find(text:String)->Option<u32>{return string_find(text,text,0);}
"#).unwrap();
        check::check(&program).unwrap();
        let mut source=String::from(r#"#![allow(non_camel_case_types,unused_parens)]
use std::alloc::{GlobalAlloc,Layout,System};use std::sync::atomic::{AtomicUsize,Ordering};
static ALLOCS:AtomicUsize=AtomicUsize::new(0);
struct Alloc;unsafe impl GlobalAlloc for Alloc{
 unsafe fn alloc(&self,l:Layout)->*mut u8{ALLOCS.fetch_add(1,Ordering::SeqCst);System.alloc(l)}
 unsafe fn dealloc(&self,p:*mut u8,l:Layout){System.dealloc(p,l)}
 unsafe fn realloc(&self,p:*mut u8,l:Layout,n:usize)->*mut u8{ALLOCS.fetch_add(1,Ordering::SeqCst);System.realloc(p,l,n)}
}#[global_allocator]static A:Alloc=Alloc;
#[derive(Clone)]struct l_Pair{l_text:String,l_needle:String}
mod temporary{
 pub fn ink_string_byte_len(s:&str)->u32{s.len().try_into().unwrap()}
 pub fn ink_string_find(s:&str,n:&str,from:u32)->Option<u32>{s.get(from as usize..).and_then(|tail|tail.find(n).map(|i|from+i as u32))}
}
"#);
        for f in &program.functions {
            let args=f.params.iter().map(|(name,t)|format!("l_{name}:{}",crate::state_native::ty(t).unwrap())).collect::<Vec<_>>().join(",");
            let body=body_with_tasks_planned(&program,f,None).unwrap().0;
            source.push_str(&format!("fn {}({args})->{}{{{body}}}\n",f.name,crate::state_native::ty(&f.result).unwrap()));
        }
        source.push_str(r#"
fn main(){
 let text="aé😀\u{feff}\0".repeat(4096);let want=(text.len()*2)as u32;
 ALLOCS.store(0,Ordering::SeqCst);assert_eq!(sizes(text),want);assert_eq!(ALLOCS.load(Ordering::SeqCst),0);
 for start in [0,1,2,3,7,10,u32::MAX]{
  let text="aé😀\u{feff}\0erroréerror".to_owned();let needle="error".to_owned();
  let want=text.get(start as usize..).and_then(|tail|tail.find(&needle).map(|i|start+i as u32));
  let pair=l_Pair{l_text:text,l_needle:needle};
  ALLOCS.store(0,Ordering::SeqCst);assert_eq!(locate(pair,start),want);assert_eq!(ALLOCS.load(Ordering::SeqCst),0);
 }
 let text="é😀".repeat(4096);ALLOCS.store(0,Ordering::SeqCst);
 assert_eq!(self_find(text),Some(0));assert_eq!(ALLOCS.load(Ordering::SeqCst),0);
}
"#);
        let dir=std::env::temp_dir().join(format!("ink-primitive-loans-{}",std::process::id()));
        fs::create_dir_all(&dir).unwrap();fs::write(dir.join("main.rs"),source).unwrap();
        let out=Command::new("rustc").args(["--edition=2021","-O"]).arg(dir.join("main.rs")).arg("-o").arg(dir.join("run")).output().unwrap();
        assert!(out.status.success(),"{}",String::from_utf8_lossy(&out.stderr));
        assert!(Command::new(dir.join("run")).status().unwrap().success());
        fs::remove_dir_all(dir).unwrap();
    }
}
