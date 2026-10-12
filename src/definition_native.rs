//! Straightforward lowering of checked first-order definitions, with no
//! optimisation laws. Explicit scalar-spine storage preserves each constructor
//! through chunks and borrowed views. Rust/LLVM remain trusted.
use crate::{
    library::{self, Bundle, Object},
    logic::{Constructor, Declaration, Sort, Term},
    LangResult,
};
use serde::Serialize;
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};

pub const SEMANTICS: &str = "ink-definition-rust-v1";
pub use ink_core::definition::{Replacement, SelectionPackage, SELECTION_SEMANTICS};
#[derive(Debug, Serialize)]
pub struct Receipt {
    pub schema: u32,
    pub semantics: String,
    pub definition_semantics: String,
    pub bundle_sha256: String,
    pub source_sha256: String,
    pub exports: Vec<String>,
    pub checked_closure: Vec<String>,
    pub executable_closure: Vec<String>,
    pub selections: Vec<(String, String)>,
    pub selection_package_sha256: Option<String>,
    pub scope: String,
}
pub struct Emission {
    pub source: String,
    pub receipt: Receipt,
}
#[derive(Clone)]
struct Expression {
    code: String,
    sort: Sort,
    borrowed: bool,
    packed_view: bool,
    /// A borrowed data field may already have an immutable shared owner.
    /// Reuse that edge when constructing another value instead of allocating
    /// an identical shallow node around a clone of its payload.
    shared_owner: Option<String>,
    shared_argument: Option<String>,
}
impl Expression {
    fn owned(&self) -> String {
        if self.packed_view {
            format!("({}).to_owned()", self.code)
        } else if self.borrowed {
            format!("({}).clone()", self.code)
        } else {
            self.code.clone()
        }
    }
    fn argument(&self) -> String {
        if matches!(self.sort, Sort::Data(_)) && !self.borrowed {
            format!("&({})", self.code)
        } else {
            self.code.clone()
        }
    }
}
struct Lower<'a> {
    objects: &'a BTreeMap<String, Object>,
    selected: BTreeSet<String>,
    binder: usize,
    nodes: usize,
    shared: bool,
    typed_only: bool,
    packed_spines: bool,
    identity_memo: bool,
    physical: Option<&'a ink_core::physical::CheckedPhysicalPlan>,
    linear_step: bool,
    recursive_sites: usize,
    recursive_site: usize,
}
pub(crate) fn ty(sort: &Sort) -> LangResult<String> {
    Ok(match sort {
        Sort::Bool => "bool".into(),
        Sort::U64 => "u64".into(),
        Sort::Data(id) => format!("D_{id}"),
        Sort::SelfType => return Err("unresolved definition sort".into()),
    })
}
fn field_sort(sort: &Sort, id: &str) -> Sort {
    if *sort == Sort::SelfType {
        Sort::Data(id.into())
    } else {
        sort.clone()
    }
}
// An empty base and one recursive edge per nonempty constructor permit an
// iterative release. Option uses Arc's null niche: it adds no pointer-sized
// storage, and None is used only after detaching an edge during destruction.
pub(crate) fn detachable_spine(cs: &[Constructor]) -> bool {
    cs.len() > 1
        && cs[0].fields.is_empty()
        && cs
            .iter()
            .skip(1)
            .all(|c| c.fields.iter().filter(|s| **s == Sort::SelfType).count() == 1)
}
impl Lower<'_> {
    fn storage(&self) -> &'static str {
        if self.shared {
            "std::sync::Arc"
        } else {
            "Box"
        }
    }
    fn fresh(&mut self) -> String {
        let name = format!("v{}", self.binder);
        self.binder += 1;
        name
    }
    fn declaration(&self, id: &str) -> LangResult<&Declaration> {
        self.objects
            .get(id)
            .map(|o| &o.declaration)
            .ok_or_else(|| "missing checked definition".into())
    }
    fn constructors(&self, id: &str) -> LangResult<Vec<Constructor>> {
        match self.declaration(id)? {
            Declaration::Datatype { constructors } => Ok(constructors.clone()),
            _ => Err("definition is not a datatype".into()),
        }
    }
    fn packed_cell(&self, id: &str) -> LangResult<Option<Sort>> {
        if !self.packed_spines || self.physical.is_some_and(|p| !p.plan().packed_datatypes.iter().any(|x|x==id)) {
            return Ok(None);
        }
        let cs = self.constructors(id)?;
        Ok(
            if cs.len() == 2
                && cs[0].fields.is_empty()
                && cs[1].fields.len() == 2
                && cs[1].fields[1] == Sort::SelfType
                && matches!(cs[1].fields[0], Sort::Bool | Sort::U64 | Sort::Data(_))
            {
                Some(cs[1].fields[0].clone())
            } else {
                None
            },
        )
    }
    fn packed_cell_type(&self, sort: &Sort) -> LangResult<String> {
        let t = ty(sort)?;
        Ok(if matches!(sort, Sort::Data(_)) {
            format!("std::sync::Arc<{t}>")
        } else {
            t
        })
    }
    fn is_packed(&self, sort: &Sort) -> LangResult<bool> {
        if let Sort::Data(id) = sort {
            Ok(self.packed_cell(id)?.is_some())
        } else {
            Ok(false)
        }
    }
    fn input_type(&self, sort: &Sort) -> LangResult<String> {
        if let Sort::Data(id) = sort {
            if let Some(cell) = self.packed_cell(id)? {
                return Ok(format!(
                    "PackedView<'_,PackedTag_{id},{}>",
                    self.packed_cell_type(&cell)?
                ));
            }
        }
        Ok(format!(
            "{}{}",
            if matches!(sort, Sort::Data(_)) {
                "&"
            } else {
                ""
            },
            ty(sort)?
        ))
    }
    fn argument(&self, e: &Expression) -> LangResult<String> {
        Ok(if self.is_packed(&e.sort)? && !e.packed_view {
            format!("({}).as_view()", e.argument())
        } else {
            e.argument()
        })
    }
    fn select_sort(&mut self, sort: &Sort) -> LangResult<()> {
        if let Sort::Data(id) = sort {
            self.select(id)?;
        }
        Ok(())
    }
    fn select(&mut self, id: &str) -> LangResult<()> {
        if !self.selected.insert(id.into()) {
            return Ok(());
        }
        match self.declaration(id)?.clone() {
            Declaration::Datatype { constructors } => {
                for constructor in constructors {
                    for s in constructor.fields {
                        self.select_sort(&s)?;
                    }
                }
            }
            Declaration::Function {
                params,
                result,
                body,
                ..
            } => {
                for (_, s) in params {
                    self.select_sort(&s)?;
                }
                self.select_sort(&result)?;
                self.select_term(&body, 0)?;
            }
            Declaration::Theorem { .. } => {
                return Err("theorems are not executable definitions".into())
            }
            Declaration::AbstractSort { .. }
            | Declaration::AbstractFunction { .. }
            | Declaration::Assumption { .. } => {
                return Err("abstract declarations are not executable definitions".into())
            }
        }
        Ok(())
    }
    fn step(&mut self, depth: usize) -> LangResult<()> {
        self.nodes += 1;
        if depth > 128 || self.nodes > 100_000 {
            return Err("definition lowering resource limit".into());
        }
        Ok(())
    }
    fn select_term(&mut self, t: &Term, depth: usize) -> LangResult<()> {
        self.step(depth)?;
        match t {
            Term::Construct {
                datatype,
                arguments,
                ..
            } => {
                self.select(datatype)?;
                for a in arguments {
                    self.select_term(a, depth + 1)?;
                }
            }
            Term::Call {
                function,
                arguments,
            } => {
                self.select(function)?;
                for a in arguments {
                    self.select_term(a, depth + 1)?;
                }
            }
            Term::SelfCall(args) => {
                for a in args {
                    self.select_term(a, depth + 1)?;
                }
            }
            Term::Binary { left, right, .. } => {
                self.select_term(left, depth + 1)?;
                self.select_term(right, depth + 1)?;
            }
            Term::If {
                condition,
                on_true,
                on_false,
            } => {
                self.select_term(condition, depth + 1)?;
                self.select_term(on_true, depth + 1)?;
                self.select_term(on_false, depth + 1)?;
            }
            Term::Match {
                scrutinee,
                branches,
            } => {
                self.select_term(scrutinee, depth + 1)?;
                for b in branches {
                    self.select_term(&b.body, depth + 1)?;
                }
            }
            _ => (),
        }
        Ok(())
    }
    fn expression(
        &mut self,
        t: &Term,
        env: &BTreeMap<String, Expression>,
        current: &str,
        depth: usize,
    ) -> LangResult<Expression> {
        self.step(depth)?;
        let (code, sort) = match t {
            Term::Var(name) => {
                return env
                    .get(name)
                    .cloned()
                    .ok_or_else(|| "unbound lowered variable".into())
            }
            Term::Bool(b) => (b.to_string(), Sort::Bool),
            Term::U64(n) => (format!("{n}u64"), Sort::U64),
            Term::Binary { op, left, right } => {
                let l = self.expression(left, env, current, depth + 1)?;
                let r = self.expression(right, env, current, depth + 1)?;
                let (code, sort) = if let Some(operator) = op.strip_prefix("f32:") {
                    let a = format!("f32::from_bits(({}) as u32)", l.code);
                    let b = format!("f32::from_bits(({}) as u32)", r.code);
                    match operator {
                        "neg" => (
                            format!("(({} as u32) ^ 0x80000000u32) as u64", l.code),
                            Sort::U64,
                        ),
                        "+" | "-" | "*" => (
                            format!("ink_def_f32_word(({a}) {operator} ({b}))"),
                            Sort::U64,
                        ),
                        "==" | "!=" | "<" | "<=" | ">" | ">=" => {
                            (format!("(({a}) {operator} ({b}))"), Sort::Bool)
                        }
                        _ => return Err("unsupported binary32 primitive".into()),
                    }
                } else {
                    match op.as_str() {
                        "+" | "-" | "*" => {
                            let method = match op.as_str() {
                                "+" => "wrapping_add",
                                "-" => "wrapping_sub",
                                _ => "wrapping_mul",
                            };
                            (format!("({}).{method}({})", l.code, r.code), Sort::U64)
                        }
                        "quot" | "rem" => (
                            format!(
                                "({}).checked_{}({}).unwrap_or(0)",
                                l.code,
                                if op == "quot" { "div" } else { "rem" },
                                r.code
                            ),
                            Sort::U64,
                        ),
                        "&" => (format!("(({}) & ({}))", l.code, r.code), Sort::U64),
                        "&&" | "||" => (
                            format!(
                                "(({}) {} ({}))",
                                l.code,
                                if op == "&&" { "&" } else { "|" },
                                r.code
                            ),
                            Sort::Bool,
                        ),
                        "==" | "!=" | "<" | "<=" | ">" | ">=" => {
                            (format!("(({}) {op} ({}))", l.code, r.code), Sort::Bool)
                        }
                        _ => return Err("unsupported lowered primitive".into()),
                    }
                };
                (code, sort)
            }
            Term::Call {
                function,
                arguments,
            } => self.call(function, arguments, env, current, depth + 1)?,
            Term::SelfCall(arguments) if self.linear_step => {
                let result = match self.declaration(current)? {Declaration::Function {result,..} => result.clone(),_=>unreachable!()};
                let mut next = Vec::new();
                for a in arguments {
                    let e=self.expression(a,env,current,depth+1)?;
                    next.push(if matches!(e.sort,Sort::Data(_)) {e.shared_owner.clone().unwrap_or_else(||format!("std::sync::Arc::new({})",e.owned()))} else {e.owned()});
                }
                let code=if self.recursive_sites==1 {
                    format!("match ink_resume.take(){{Some(value)=>value,None=>return Err(({},))}}",next.join(","))
                } else {
                    let site=self.recursive_site;self.recursive_site+=1;
                    format!("match &ink_resume[{site}]{{Some(value)=>value.clone(),None=>return Err(({site},({},)))}}",next.join(","))
                };
                (code,result)
            }
            Term::SelfCall(arguments) => self.call(current, arguments, env, current, depth + 1)?,
            Term::Construct {
                datatype,
                constructor,
                arguments,
            } => {
                if *constructor == 1 && self.packed_cell(datatype)?.is_some() {
                    let head = self.expression(&arguments[0], env, current, depth + 1)?;
                    let tail = self.expression(&arguments[1], env, current, depth + 1)?;
                    return Ok(Expression {
                        code: format!(
                            "({}).prepend({})",
                            tail.owned(),
                            if matches!(head.sort, Sort::Data(_)) {
                                if let Some(owner) = &head.shared_owner {
                                    owner.clone()
                                } else {
                                    format!("std::sync::Arc::new({})", head.owned())
                                }
                            } else {
                                head.owned()
                            }
                        ),
                        sort: Sort::Data(datatype.clone()),
                        borrowed: false,
                        packed_view: false,
                        shared_owner: None,
                        shared_argument: None,
                    });
                }
                let cs = self.constructors(datatype)?;
                let c = cs.get(*constructor).ok_or("invalid lowered constructor")?;
                let detachable = self.typed_only && detachable_spine(&cs);
                let mut args = Vec::new();
                for (t, s) in arguments.iter().zip(&c.fields) {
                    let e = self.expression(t, env, current, depth + 1)?;
                    args.push(if matches!(field_sort(s, datatype), Sort::Data(_)) {
                        let value = if self.shared {
                            e.shared_owner
                                .as_ref()
                                .map(|owner| owner.clone())
                                .unwrap_or_else(|| {
                                    format!("{}::new({})", self.storage(), e.owned())
                                })
                        } else {
                            format!("{}::new({})", self.storage(), e.owned())
                        };
                        if detachable && *s == Sort::SelfType {
                            format!("Some({value})")
                        } else {
                            value
                        }
                    } else {
                        e.owned()
                    });
                }
                (
                    format!(
                        "D_{datatype}::C{constructor}{}",
                        if args.is_empty() {
                            String::new()
                        } else {
                            format!("({})", args.join(","))
                        }
                    ),
                    Sort::Data(datatype.clone()),
                )
            }
            Term::If {
                condition,
                on_true,
                on_false,
            } => {
                let c = self.expression(condition, env, current, depth + 1)?;
                let a = self.expression(on_true, env, current, depth + 1)?;
                let b = self.expression(on_false, env, current, depth + 1)?;
                (
                    format!("if {} {{ {} }} else {{ {} }}", c.code, a.owned(), b.owned()),
                    a.sort,
                )
            }
            Term::Match {
                scrutinee,
                branches,
            } => {
                let e = self.expression(scrutinee, env, current, depth + 1)?;
                let Sort::Data(id) = &e.sort else {
                    return Err("invalid lowered match".into());
                };
                let cs = self.constructors(id)?;
                let packed = self.packed_cell(id)?.is_some();
                let detachable = self.typed_only && detachable_spine(&cs);
                let mut arms = Vec::new();
                let mut result = None;
                for (i, (branch, constructor)) in branches.iter().zip(cs).enumerate() {
                    let mut local = env.clone();
                    let mut fields = Vec::new();
                    for (field_index, (name, s)) in
                        branch.bindings.iter().zip(constructor.fields).enumerate()
                    {
                        let binder = self.fresh();
                        let sort = field_sort(&s, id);
                        let data = matches!(sort, Sort::Data(_));
                        local.insert(
                            name.clone(),
                            Expression {
                                code: if packed && data && field_index == 1 {binder.clone()}
                                else if packed && data {format!("{binder}.as_ref()")}
                                else if packed {binder.clone()}
                                else if data {if detachable && s==Sort::SelfType{format!("{binder}.as_deref().expect(\"live recursive edge\")")}else{format!("{binder}.as_ref()")}
                                } else {
                                    format!("*{binder}")
                                },
                                sort,
                                borrowed: data,
                                packed_view: packed && data && field_index == 1,
                                shared_owner: if data
                                    && self.shared
                                    && (!packed || field_index == 0)
                                {
                                    Some(format!("std::sync::Arc::clone({})",if packed {format!("&{binder}")} else if detachable && s==Sort::SelfType {format!("{binder}.as_ref().expect(\"live recursive edge\")")}else{binder.clone()}))
                                } else {
                                    None
                                },
                                shared_argument: if data && self.shared && self.typed_only && !self.packed_spines && !self.identity_memo {
                                    let owner = if detachable && s==Sort::SelfType {format!("{binder}.as_ref().expect(\"live recursive edge\")")}else{binder.clone()};
                                    Some(format!("InkBorrowed::edge({owner})"))
                                } else {None},
                            },
                        );
                        fields.push(binder);
                    }
                    let b = self.expression(&branch.body, &local, current, depth + 1)?;
                    result = Some(b.sort.clone());
                    arms.push(if packed {
                        format!(
                            "{}=>{{{}}}",
                            if i == 0 {
                                "None".into()
                            } else {
                                format!("Some(({}))", fields.join(","))
                            },
                            b.owned()
                        )
                    } else {
                        format!(
                            "D_{id}::C{i}{} => {{ {} }}",
                            if fields.is_empty() {
                                String::new()
                            } else {
                                format!("({})", fields.join(","))
                            },
                            b.owned()
                        )
                    });
                }
                (
                    format!(
                        "match {} {{ {} }}",
                        if packed {
                            format!("({}).view()", self.argument(&e)?)
                        } else {
                            e.argument()
                        },
                        arms.join(",")
                    ),
                    result.ok_or("empty lowered match")?,
                )
            }
        };
        fn closed_value(t: &Term) -> bool {
            match t {
                Term::Bool(_) | Term::U64(_) => true,
                Term::Construct { arguments, .. } => arguments.iter().all(closed_value),
                _ => false,
            }
        }
        let shared_owner = if self.shared
            && self.typed_only
            && matches!(sort, Sort::Data(_))
            && closed_value(t)
        {
            let name = self.fresh();
            let ty = ty(&sort)?;
            Some(format!("std::sync::Arc::clone({{static {name}:std::sync::OnceLock<std::sync::Arc<{ty}>>=std::sync::OnceLock::new();{name}.get_or_init(||std::sync::Arc::new({code}))}})"))
        } else {
            None
        };
        Ok(Expression {
            code,
            sort,
            borrowed: false,
            packed_view: false,
            shared_owner,
            shared_argument: None,
        })
    }
    fn call(
        &mut self,
        id: &str,
        args: &[Term],
        env: &BTreeMap<String, Expression>,
        current: &str,
        depth: usize,
    ) -> LangResult<(String, Sort)> {
        let Declaration::Function {
            result,
            body,
            recursive,
            ..
        } = self.declaration(id)?.clone()
        else {
            return Err("invalid lowered call".into());
        };
        let expressions = args
            .iter()
            .map(|a| self.expression(a, env, current, depth + 1))
            .collect::<LangResult<Vec<_>>>()?;
        let values = expressions
            .iter()
            .map(|e| {let argument=self.argument(e)?;Ok(if self.shared && self.typed_only && !self.packed_spines && !self.identity_memo && matches!(e.sort,Sort::Data(_)) {e.shared_argument.clone().unwrap_or_else(||format!("InkBorrowed::root({argument})"))}else{argument})})
            .collect::<LangResult<Vec<_>>>()?;
        let direct = format!("d_{id}({})", values.join(","));
        if self.identity_memo
            && id != current
            && self.physical.map_or(recursive.is_some() && contains_self_call(&body),|p|p.plan().memo_functions.iter().any(|x|x==id))
            && matches!(result, Sort::U64 | Sort::Bool)
            && expressions.len() <= 5
        {
            let data = expressions
                .iter()
                .enumerate()
                .filter(|(_, e)| matches!(e.sort, Sort::Data(_)))
                .collect::<Vec<_>>();
            if data.len() == 1 && !data[0].1.packed_view {
                if let Some(owner) = &data[0].1.shared_owner {
                    let memo_input=self.fresh();
                    let mut locals = format!("let {memo_input}=&{owner};");
                    let mut call_args = values.clone();
                    call_args[data[0].0]=format!("{memo_input}.as_ref()");
                    let mut words = Vec::new();
                    for (i, e) in expressions.iter().enumerate() {
                        if matches!(e.sort, Sort::Data(_)) {
                            continue;
                        }
                        let local = self.fresh();
                        locals.push_str(&format!("let {local}={};", e.code));
                        call_args[i] = local.clone();
                        words.push(if e.sort == Sort::Bool {
                            format!("u64::from({local})")
                        } else {
                            local
                        });
                    }
                    words.resize(4, "0u64".into());
                    let compute = format!("d_{id}({})", call_args.join(","));
                    return Ok((
                        format!(
                            "{{{locals}ink_identity_memo({memo_input},{id:?},[{}],||{compute})}}",
                            words.join(",")
                        ),
                        result,
                    ));
                }
            }
        }
        Ok((direct, result))
    }
    fn datatype(&self, id: &str, cs: &[Constructor]) -> LangResult<String> {
        if let Some(cell) = self.packed_cell(id)? {
            return Ok(format!("#[derive(Debug)]pub struct PackedTag_{id};\npub type D_{id}=PackedSpine<PackedTag_{id},{}>;\n",self.packed_cell_type(&cell)?));
        }
        let detachable = self.typed_only && detachable_spine(cs);
        let mut variants = Vec::new();
        let mut decode = Vec::new();
        let mut encode = Vec::new();
        for (i, c) in cs.iter().enumerate() {
            let sorts: Vec<_> = c.fields.iter().map(|s| field_sort(s, id)).collect();
            let types = sorts
                .iter()
                .zip(&c.fields)
                .map(|(s, source_sort)| {
                    let t = ty(s)?;
                    Ok(if matches!(s, Sort::Data(_)) {
                        let value = format!("{}<{t}>", self.storage());
                        if detachable && *source_sort == Sort::SelfType {
                            format!("Option<{value}>")
                        } else {
                            value
                        }
                    } else {
                        t
                    })
                })
                .collect::<LangResult<Vec<_>>>()?;
            variants.push(format!(
                "C{i}{}",
                if types.is_empty() {
                    String::new()
                } else {
                    format!("({})", types.join(","))
                }
            ));
            let mut ds = Vec::new();
            let mut es = Vec::new();
            let mut bs = Vec::new();
            for (j, s) in sorts.iter().enumerate() {
                let decoded = decode_value(s, &format!("&arguments[{j}]"));
                ds.push(if matches!(s, Sort::Data(_)) {
                    format!("{}::new({decoded})", self.storage())
                } else {
                    decoded
                });
                bs.push(format!("b{j}"));
                es.push(encode_value(s, &format!("b{j}"), true));
            }
            decode.push(format!(
                "{i} if arguments.len() == {} => Ok(Self::C{i}{}),",
                sorts.len(),
                if ds.is_empty() {
                    String::new()
                } else {
                    format!("({})", ds.join(","))
                }
            ));
            encode.push(format!("Self::C{i}{} => Value::Data {{ datatype: \"{id}\".into(), constructor: {i}, arguments: vec![{}] }},", if bs.is_empty() { String::new() } else { format!("({})", bs.join(",")) }, es.join(",")));
        }
        // Literal codecs for a linear inductive spine use a loop. This is a
        // structural ABI lowering, independent of database algorithm identity.
        if self.typed_only {
            let mut code = format!(
                "#[derive(Clone, Debug, PartialEq, Eq)]\npub enum D_{id} {{ {} }}\n",
                variants.join(",")
            );
            // A linear inductive spine must also be released iteratively. In
            // Wasm, ordinary Arc drop glue otherwise consumes the engine's
            // call stack even when literal evaluation itself fits its limits.
            if detachable {
                code.push_str(&format!("impl D_{id}{{fn take_tail(&mut self)->Option<std::sync::Arc<Self>>{{match self{{Self::C0=>None,"));
                for (i, c) in cs.iter().enumerate().skip(1) {
                    let bs = c
                        .fields
                        .iter()
                        .map(|s| if *s == Sort::SelfType { "tail" } else { "_" })
                        .collect::<Vec<_>>()
                        .join(",");
                    code.push_str(&format!("Self::C{i}({bs})=>tail.take(),"));
                }
                code.push_str("}}}\n");
                code.push_str(&format!("impl Drop for D_{id}{{fn drop(&mut self){{let mut pending=self.take_tail();while let Some(tail)=pending{{match std::sync::Arc::try_unwrap(tail){{Ok(mut node)=>pending=node.take_tail(),Err(_)=>break,}}}}}}}}\n"));
            }
            return Ok(code);
        }
        if cs.len() == 2
            && cs[0].fields.is_empty()
            && cs[1].fields.last() == Some(&Sort::SelfType)
            && cs[1].fields[..cs[1].fields.len() - 1]
                .iter()
                .all(|s| *s != Sort::SelfType)
        {
            let fields = &cs[1].fields[..cs[1].fields.len() - 1];
            let ds = fields
                .iter()
                .enumerate()
                .map(|(j, s)| {
                    let d = decode_value(s, &format!("&arguments[{j}]"));
                    if matches!(s, Sort::Data(_)) {
                        format!("{}::new({d})", self.storage())
                    } else {
                        d
                    }
                })
                .collect::<Vec<_>>();
            let bs = (0..fields.len())
                .map(|j| format!("b{j}"))
                .collect::<Vec<_>>();
            let es = fields
                .iter()
                .zip(&bs)
                .map(|(s, b)| encode_value(s, b, true))
                .collect::<Vec<_>>();
            let n = fields.len();
            return Ok(format!("#[derive(Clone, Debug, PartialEq, Eq)]\npub enum D_{id} {{ {} }}\nimpl D_{id} {{
fn decode(v:&Value)->Result<Self,&'static str>{{let mut cursor=v;let mut rows=Vec::new();loop{{match cursor{{Value::Data{{datatype,constructor,arguments}} if datatype==\"{id}\"=>match (*constructor,arguments.len()){{(0,0)=>break,(1,{})=>{{if rows.len()>=4096{{return Err(\"inductive spine limit\");}}rows.push(arguments);cursor=&arguments[{n}];}},_=>return Err(\"constructor or field count mismatch\")}},_=>return Err(\"datatype mismatch\")}}}}let mut tail=Self::C0;for arguments in rows.into_iter().rev(){{tail=Self::C1({}{}::new(tail));}}Ok(tail)}}
fn encode(&self)->Value{{let mut cursor=self;let mut rows=Vec::new();loop{{match cursor{{Self::C0=>break,Self::C1({}tail)=>{{rows.push(vec![{}]);cursor=tail.as_ref();}}}}}}let mut tail=Value::Data{{datatype:\"{id}\".into(),constructor:0,arguments:vec![]}};for mut arguments in rows.into_iter().rev(){{arguments.push(tail);tail=Value::Data{{datatype:\"{id}\".into(),constructor:1,arguments}};}}tail}}
}}\n",variants.join(","),n+1, if ds.is_empty(){String::new()}else{format!("{},",ds.join(","))},self.storage(),if bs.is_empty(){String::new()}else{format!("{},",bs.join(","))},es.join(",")));
        }
        Ok(format!("#[derive(Clone, Debug, PartialEq, Eq)]\npub enum D_{id} {{ {} }}\nimpl D_{id} {{\n fn decode(v: &Value) -> Result<Self, &'static str> {{ match v {{ Value::Data {{ datatype, constructor, arguments }} if datatype == \"{id}\" => match constructor {{ {} _ => Err(\"constructor or field count mismatch\") }}, _ => Err(\"datatype mismatch\") }} }}\n fn encode(&self) -> Value {{ match self {{ {} }} }}\n}}\n", variants.join(","), decode.join("\n"), encode.join("\n")))
    }
}
fn contains_self_call(term: &Term) -> bool {
    match term {
        Term::SelfCall(_) => true,
        Term::Call { arguments, .. } | Term::Construct { arguments, .. } => {
            arguments.iter().any(contains_self_call)
        }
        Term::Binary { left, right, .. } => contains_self_call(left) || contains_self_call(right),
        Term::If {
            condition,
            on_true,
            on_false,
        } => {
            contains_self_call(condition)
                || contains_self_call(on_true)
                || contains_self_call(on_false)
        }
        Term::Match {
            scrutinee,
            branches,
        } => contains_self_call(scrutinee) || branches.iter().any(|b| contains_self_call(&b.body)),
        _ => false,
    }
}
pub(crate) fn decode_value(sort: &Sort, value: &str) -> String {
    match sort {
        Sort::Bool => format!("decode_bool({value})?"),
        Sort::U64 => format!("decode_u64({value})?"),
        Sort::Data(id) => format!("D_{id}::decode({value})?"),
        Sort::SelfType => unreachable!("sorts resolved before codec lowering"),
    }
}
pub(crate) fn encode_value(sort: &Sort, value: &str, borrowed: bool) -> String {
    match sort {
        Sort::Bool => format!("Value::Bool({}{value})", if borrowed { "*" } else { "" }),
        Sort::U64 => format!("Value::U64({}{value})", if borrowed { "*" } else { "" }),
        Sort::Data(_) => format!("({value}).encode()"),
        Sort::SelfType => unreachable!("sorts resolved before codec lowering"),
    }
}

/// Check the whole bundle before lowering; selecting exports cannot hide an
/// invalid theorem. Only explicitly public function roots may be exported.
pub fn emit(bundle: &Bundle, exports: &[String]) -> LangResult<Emission> {
    emit_selected(bundle, exports, None)
}
/// Entry selections preserve total returned values over the entire parameter
/// domain. Internal calls continue to name original immutable definitions;
/// redirecting those calls could introduce cycles even for equal candidates.
pub fn emit_selected(
    bundle: &Bundle,
    exports: &[String],
    selection: Option<&SelectionPackage>,
) -> LangResult<Emission> {
    let checked = ink_core::definition::check(bundle, exports, selection)?;
    lower(&checked)
}
/// Only a core-checked witness may enter this backend.
pub fn lower(checked: &ink_core::definition::CheckedDefinition) -> LangResult<Emission> {
    lower_with_storage(checked, false, false, true, &BTreeMap::new())
}
/// Typed shared functions from a checked witness, without extra definitions.
pub fn lower_typed_shared(
    checked: &ink_core::definition::CheckedDefinition,
) -> LangResult<Emission> {
    lower_with_storage(checked, true, true, true, &BTreeMap::new())
}
/// Literal typed functions only: no generic constructor carrier or dispatcher.
pub(crate) fn lower_typed_shared_projected(
    checked: &ink_core::definition::CheckedDefinition,
    extras: &BTreeMap<String, Declaration>,
) -> LangResult<Emission> {
    lower_with_storage(checked, true, true, true, extras)
}
pub(crate) fn lower_typed_planned(checked: &ink_core::definition::CheckedDefinition, extras: &BTreeMap<String, Declaration>, physical: &ink_core::physical::CheckedPhysicalPlan) -> LangResult<Emission> {
    lower_with_storage_mode(checked,true,true,true,physical.plan().definitions==ink_core::physical::Definitions::Packed,physical.plan().definitions==ink_core::physical::Definitions::Memo,extras,Some(physical))
}
/// Exact chunked scalar spines, selected explicitly by the standalone target.
pub(crate) fn lower_typed_packed(
    checked: &ink_core::definition::CheckedDefinition,
    extras: &BTreeMap<String, Declaration>,
) -> LangResult<Emission> {
    lower_with_storage_mode(checked, true, true, true, true, false, extras, None)
}
pub(crate) fn lower_typed_memo(
    checked: &ink_core::definition::CheckedDefinition,
    extras: &BTreeMap<String, Declaration>,
) -> LangResult<Emission> {
    lower_with_storage_mode(checked, true, true, true, false, true, extras, None)
}
/// Typed immutable storage for literal foreign functions. The generated C ABI
/// borrows these objects directly; it never serialises physical state.
pub(crate) fn lower_typed_shared_datatypes(
    checked: &ink_core::definition::CheckedDefinition,
    extras: &BTreeMap<String, Declaration>,
) -> LangResult<Emission> {
    lower_with_storage(checked, true, true, false, extras)
}
fn lower_with_storage(
    checked: &ink_core::definition::CheckedDefinition,
    shared: bool,
    typed_only: bool,
    functions: bool,
    extras: &BTreeMap<String, Declaration>,
) -> LangResult<Emission> {
    lower_with_storage_mode(checked, shared, typed_only, functions, false, false, extras, None)
}
fn lower_with_storage_mode(
    checked: &ink_core::definition::CheckedDefinition,
    shared: bool,
    typed_only: bool,
    functions: bool,
    packed_spines: bool,
    identity_memo: bool,
    extras: &BTreeMap<String, Declaration>,
    physical: Option<&ink_core::physical::CheckedPhysicalPlan>,
) -> LangResult<Emission> {
    if packed_spines && (!shared || !typed_only) {
        return Err("packed spines require typed immutable storage".into());
    }
    let bundle = checked.bundle();
    let exports = checked
        .exports()
        .iter()
        .chain(extras.keys())
        .cloned()
        .collect::<Vec<_>>();
    let choices = checked.choices();
    let bundle_sha256 = checked.bundle_sha256().to_owned();
    let mut objects = bundle
        .objects
        .iter()
        .map(|(id, raw)| {
            Ok((
                id.clone(),
                serde_json::from_str::<Object>(raw).map_err(|e| e.to_string())?,
            ))
        })
        .collect::<LangResult<BTreeMap<_, _>>>()?;
    for (id, declaration) in extras {
        objects.insert(
            id.clone(),
            Object {
                schema: 1,
                semantics: library::SEMANTICS.into(),
                name: "compiler-demand-projection".into(),
                dependencies: vec![],
                declaration: declaration.clone(),
            },
        );
    }
    let mut lower = Lower {
        objects: &objects,
        selected: BTreeSet::new(),
        binder: 0,
        nodes: 0,
        shared,
        typed_only,
        packed_spines,
        identity_memo,
        physical,
        linear_step: false,
        recursive_sites: 0,
        recursive_site: 0,
    };
    for id in &exports {
        if !matches!(lower.declaration(id)?, Declaration::Function { .. }) {
            return Err("definition export must be a function".into());
        }
        lower.select(choices.get(id).unwrap_or(id))?;
    }
    let mut source = String::from("// ink-definition-rust-v1: checked bodies; Rust/backend are trusted.\n#![allow(non_camel_case_types, non_snake_case, non_upper_case_globals, dead_code, unused_variables, unused_parens, unused_unsafe, improper_ctypes_definitions)]\n");
    if packed_spines {
        source.push_str(include_str!("packed_spine.rs.txt"));
    }
    if identity_memo {
        source.push_str(include_str!("identity_memo.rs.txt"));
    }
    source.push_str("#[inline(never)] fn ink_def_f32_word(v:f32)->u64{if v.is_nan(){0x7fc00000}else{v.to_bits() as u64}}\n");
    if !typed_only {
        source.push_str(include_str!("definition_value.rs.txt"));
    }
    if shared && typed_only && functions {
        source.push_str("struct InkBorrowed<'a,T>{value:&'a T,owner:Option<&'a std::sync::Arc<T>>}\nimpl<'a,T> Copy for InkBorrowed<'a,T>{}\nimpl<'a,T> Clone for InkBorrowed<'a,T>{fn clone(&self)->Self{*self}}\nimpl<'a,T:Clone> InkBorrowed<'a,T>{fn root(value:&'a T)->Self{Self{value,owner:None}}fn edge(owner:&'a std::sync::Arc<T>)->Self{Self{value:owner.as_ref(),owner:Some(owner)}}fn share(self)->std::sync::Arc<T>{self.owner.map(std::sync::Arc::clone).unwrap_or_else(||std::sync::Arc::new(self.value.clone()))}}\n");
    }
    let selected: Vec<_> = lower.selected.iter().cloned().collect();
    for id in &selected {
        match lower.declaration(id)?.clone() {
            Declaration::Datatype { constructors } => {
                source.push_str(&lower.datatype(id, &constructors)?)
            }
            Declaration::Function {
                params,
                result,
                body,
                ..
            } => {
                if !functions {
                    continue;
                }
                let mut recursive_sites=0;
                ink_core::logic::walk_term(&body,|t|if matches!(t,Term::SelfCall(_)){recursive_sites+=1});
                let linear = shared && typed_only && !packed_spines && !identity_memo && (1..=64).contains(&recursive_sites);
                lower.linear_step=linear;
                lower.recursive_sites=recursive_sites;
                lower.recursive_site=0;
                let mut env = BTreeMap::new();
                let mut inputs = Vec::new();
                let mut step_inputs = Vec::new();
                let mut initial = Vec::new();
                let mut frame_types = Vec::new();
                let mut frame_args = Vec::new();
                for (i,(n, s)) in params.into_iter().enumerate() {
                    let binder = lower.fresh();
                    let data = matches!(s, Sort::Data(_));
                    let packed_view = lower.is_packed(&s)?;
                    let shared_data = data && shared && typed_only && !packed_spines && !identity_memo;
                    inputs.push(if shared_data {
                        format!("{binder}: InkBorrowed<'_,{}>",ty(&s)?)
                    } else { format!("{binder}: {}", lower.input_type(&s)?) });
                    initial.push(if data {format!("{binder}.share()")}else{binder.clone()});
                    frame_types.push(if data {format!("std::sync::Arc<{}>",ty(&s)?)}else{ty(&s)?});
                    step_inputs.push(format!("{binder}: {}{}",if data {"&std::sync::Arc<"}else{""},if data {format!("{}>",ty(&s)?)}else{ty(&s)?}));
                    frame_args.push(format!("{}ink_frame.{i}",if data {"&"}else{""}));
                    env.insert(n, Expression {
                        code: if linear && data {format!("{binder}.as_ref()")}else if shared_data {format!("{binder}.value")} else {binder.clone()},
                        sort: s,
                        borrowed: data,
                        packed_view,
                        shared_owner: shared_data.then(||if linear {format!("std::sync::Arc::clone({binder})")}else{format!("{binder}.share()")}),
                        shared_argument: shared_data.then(||if linear {format!("InkBorrowed::edge({binder})")}else{binder.clone()}),
                    });
                }
                let body = lower.expression(&body, &env, id, 0)?;
                lower.linear_step=false;
                if linear {
                    let result_type=ty(&result)?;
                    let frame_type=format!("({},)",frame_types.join(","));
                    let arguments=frame_args.join(",");
                    if recursive_sites==1 {
                    // Defunctionalise one recursive call site. Replaying a frame
                    // recomputes only pure checked terms; it adds no semantic law.
                    source.push_str(&format!("fn s_{id}({},mut ink_resume:Option<{result_type}>)->Result<{result_type},{frame_type}>{{Ok({})}}\n",step_inputs.join(","),body.owned()));
                    source.push_str(&format!("fn d_{id}({})->{result_type}{{let mut ink_frame=({},);let mut ink_frames=Vec::new();let ink_frame_limit=1_000_000usize.min(64_000_000/std::mem::size_of::<{frame_type}>().max(1));let mut ink_result=loop{{match s_{id}({arguments},None){{Ok(value)=>break value,Err(next)=>{{assert!(ink_frames.len()<ink_frame_limit,\"definition continuation frame limit\");if ink_frames.len()==ink_frames.capacity(){{let capacity=ink_frames.capacity();let next=capacity.max(32).saturating_mul(2).min(ink_frame_limit);ink_frames.reserve_exact(next-capacity);}}ink_frames.push(ink_frame);ink_frame=next;}}}}}};while let Some(ink_frame)=ink_frames.pop(){{ink_result=match s_{id}({arguments},Some(ink_result)){{Ok(value)=>value,Err(_)=>unreachable!(\"checked single recursive call site\")}};}}ink_result}}\n",inputs.join(","),initial.join(",")));
                    } else {
                        let full_frame_type=format!("({frame_type},[Option<{result_type}>;{recursive_sites}],usize)");
                        source.push_str(&format!("fn s_{id}({},ink_resume:&[Option<{result_type}>;{recursive_sites}])->Result<{result_type},(usize,{frame_type})>{{Ok({})}}\n",step_inputs.join(","),body.owned()));
                        source.push_str(&format!("fn d_{id}({})->{result_type}{{let mut ink_frame=({},);let mut ink_resume=[const{{None}};{recursive_sites}];let mut ink_frames:Vec<{full_frame_type}>=Vec::new();let ink_frame_limit=1_000_000usize.min(64_000_000/std::mem::size_of::<{full_frame_type}>().max(1));loop{{match s_{id}({arguments},&ink_resume){{Ok(value)=>{{if let Some((parent,results,site))=ink_frames.pop(){{ink_frame=parent;ink_resume=results;ink_resume[site]=Some(value);}}else{{return value;}}}},Err((site,next))=>{{assert!(ink_frames.len()<ink_frame_limit,\"definition continuation frame limit\");if ink_frames.len()==ink_frames.capacity(){{let capacity=ink_frames.capacity();let next=capacity.max(32).saturating_mul(2).min(ink_frame_limit);ink_frames.reserve_exact(next-capacity);}}ink_frames.push((ink_frame,ink_resume,site));ink_frame=next;ink_resume=[const{{None}};{recursive_sites}];}}}}}}}}\n",inputs.join(","),initial.join(",")));
                    }
                } else {
                    source.push_str(&format!("fn d_{id}({}) -> {} {{ {} }}\n",inputs.join(","),ty(&result)?,body.owned()));
                }
            }
            _ => return Err("non-executable dependency selected".into()),
        }
        if source.len() > 16_000_000 {
            return Err("definition source size limit".into());
        }
    }
    // Typed exports are wrappers, not mutable definition identities.
    for id in exports.iter().filter(|_| functions) {
        let Declaration::Function { params, result, .. } = &objects[id].declaration else {
            unreachable!()
        };
        let target = choices.get(id).unwrap_or(id);
        let mut inputs = Vec::new();
        let mut args = Vec::new();
        for (_, s) in params {
            let binder = lower.fresh();
            inputs.push(format!(
                "{binder}: {}{}",
                if matches!(s, Sort::Data(_)) { "&" } else { "" },
                ty(s)?
            ));
            args.push(if lower.is_packed(s)? {
                format!("{binder}.as_view()")
            } else if shared && typed_only && !packed_spines && !identity_memo && matches!(s, Sort::Data(_)) {
                format!("InkBorrowed::root({binder})")
            } else {
                binder
            });
        }
        source.push_str(&format!(
            "pub fn f_{id}({}) -> {} {{ d_{target}({}) }}\n",
            inputs.join(","),
            ty(result)?,
            args.join(",")
        ));
    }
    if !typed_only {
        source.push_str("pub fn invoke(function: &str, args: &[Value]) -> Result<Value, &'static str> { validate_inputs(args)?; match function {\n");
        for id in &exports {
            let Declaration::Function { params, result, .. } = &objects[id].declaration else {
                unreachable!()
            };
            let mut inputs = Vec::new();
            source.push_str(&format!(
                "\"{id}\" if args.len() == {} => {{\n",
                params.len()
            ));
            for (i, (_, s)) in params.iter().enumerate() {
                source.push_str(&format!(
                    "let a{i} = {};\n",
                    decode_value(s, &format!("&args[{i}]"))
                ));
                inputs.push(format!(
                    "{}a{i}",
                    if matches!(s, Sort::Data(_)) { "&" } else { "" }
                ));
            }
            source.push_str(&format!(
                "let result = f_{id}({}); Ok({}) }},\n",
                inputs.join(","),
                encode_value(result, "result", false)
            ));
        }
        source.push_str("_ => Err(\"unknown export or argument count mismatch\") } }\n");
    }
    if source.len() > 16_000_000 {
        return Err("definition source size limit".into());
    }
    let receipt = Receipt {
        schema: 1, semantics: SEMANTICS.into(), definition_semantics: library::SEMANTICS.into(),
        bundle_sha256,
        source_sha256: format!("{:x}", Sha256::digest(source.as_bytes())), exports: exports.to_vec(), checked_closure: checked.closure().to_vec(),
        executable_closure: selected,
        selections: exports.iter().map(|id| (id.clone(), choices.get(id).unwrap_or(id).clone())).collect(),
        selection_package_sha256: checked.selection_sha256().map(str::to_owned),
        scope: format!("checked first-order definitions and admitted observer choices; trusted Rust lowering, codecs and Rust/LLVM backend; {} storage; {}; no stateful source admission, physical storage refinement, host-failure preservation or execution-cost bound",if packed_spines{"immutable scalar and shared-data chunks; checked u32 narrowing with exact u64 promotion; Boolean bitsets"}else if shared{"immutable shared Arc"}else{"boxed"},if typed_only{"typed entry points without a ground dispatcher"}else{"ground transport dispatcher"}),
    };
    Ok(Emission { source, receipt })
}

#[cfg(test)]
#[path = "definition_sharing_tests.rs"]
mod sharing_tests;
/// Export the same sealed definitions through the C/Wasm ground-value word ABI.
/// Scheduling and transport do not select or reinterpret implementation bodies.
pub fn lower_portable(
    checked: &ink_core::definition::CheckedDefinition,
) -> LangResult<(Emission, serde_json::Value)> {
    let mut emission = lower(checked)?;
    let mut datatypes = Vec::new();
    for id in &emission.receipt.executable_closure {
        let object: Object =
            serde_json::from_str(&checked.bundle().objects[id]).map_err(|e| e.to_string())?;
        if matches!(object.declaration, Declaration::Datatype { .. }) {
            datatypes.push(id.clone());
        }
    }
    emission.source.push_str(&format!(
        "\nconst WORD_DATATYPES:&[&str]=&{:?};\nconst WORD_EXPORTS:&[&str]=&{:?};\n",
        datatypes,
        checked.exports()
    ));
    emission
        .source
        .push_str(include_str!("definition_word_abi.rs.txt"));
    emission.receipt.source_sha256 = format!("{:x}", Sha256::digest(emission.source.as_bytes()));
    let identity = ink_core::registry::identity(&(
        "ink-sealed-executable-v1",
        checked.bundle_sha256(),
        checked.exports(),
        checked.choices(),
    ))?;
    let manifest = serde_json::json!({"schema":1,"semantics":"ink-definition-rust-words-v1","executable":identity,"exports":checked.exports(),"datatypes":datatypes,"checked_closure":checked.closure(),"executable_closure":emission.receipt.executable_closure});
    Ok((emission, manifest))
}
