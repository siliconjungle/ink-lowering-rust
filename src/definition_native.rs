//! Straightforward lowering of checked first-order definitions, with no
//! optimisation laws or representation recognisers. Rust/LLVM remain trusted.
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
}
impl Expression {
    fn owned(&self) -> String {
        if self.borrowed {
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
            Term::SelfCall(arguments) => self.call(current, arguments, env, current, depth + 1)?,
            Term::Construct {
                datatype,
                constructor,
                arguments,
            } => {
                let cs = self.constructors(datatype)?;
                let c = cs.get(*constructor).ok_or("invalid lowered constructor")?;
                let mut args = Vec::new();
                for (t, s) in arguments.iter().zip(&c.fields) {
                    let e = self.expression(t, env, current, depth + 1)?;
                    args.push(if matches!(field_sort(s, datatype), Sort::Data(_)) {
                        format!("{}::new({})", self.storage(), e.owned())
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
                let mut arms = Vec::new();
                let mut result = None;
                for (i, (branch, constructor)) in branches.iter().zip(cs).enumerate() {
                    let mut local = env.clone();
                    let mut fields = Vec::new();
                    for (name, s) in branch.bindings.iter().zip(constructor.fields) {
                        let binder = self.fresh();
                        let sort = field_sort(&s, id);
                        let data = matches!(sort, Sort::Data(_));
                        local.insert(
                            name.clone(),
                            Expression {
                                code: if data {
                                    format!("{binder}.as_ref()")
                                } else {
                                    format!("*{binder}")
                                },
                                sort,
                                borrowed: data,
                            },
                        );
                        fields.push(binder);
                    }
                    let b = self.expression(&branch.body, &local, current, depth + 1)?;
                    result = Some(b.sort.clone());
                    arms.push(format!(
                        "D_{id}::C{i}{} => {{ {} }}",
                        if fields.is_empty() {
                            String::new()
                        } else {
                            format!("({})", fields.join(","))
                        },
                        b.owned()
                    ));
                }
                (
                    format!("match {} {{ {} }}", e.argument(), arms.join(",")),
                    result.ok_or("empty lowered match")?,
                )
            }
        };
        Ok(Expression {
            code,
            sort,
            borrowed: false,
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
        let Declaration::Function { result, .. } = self.declaration(id)?.clone() else {
            return Err("invalid lowered call".into());
        };
        let args = args
            .iter()
            .map(|a| {
                self.expression(a, env, current, depth + 1)
                    .map(|e| e.argument())
            })
            .collect::<LangResult<Vec<_>>>()?;
        Ok((format!("d_{id}({})", args.join(",")), result))
    }
    fn datatype(&self, id: &str, cs: &[Constructor]) -> LangResult<String> {
        let mut variants = Vec::new();
        let mut decode = Vec::new();
        let mut encode = Vec::new();
        for (i, c) in cs.iter().enumerate() {
            let sorts: Vec<_> = c.fields.iter().map(|s| field_sort(s, id)).collect();
            let types = sorts
                .iter()
                .map(|s| {
                    let t = ty(s)?;
                    Ok(if matches!(s, Sort::Data(_)) {
                        format!("{}<{t}>", self.storage())
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
            if cs[0].fields.is_empty()
                && cs
                    .iter()
                    .skip(1)
                    .all(|c| c.fields.iter().filter(|s| **s == Sort::SelfType).count() == 1)
            {
                code.push_str(&format!("impl D_{id}{{fn take_tail(&mut self)->Option<std::sync::Arc<Self>>{{match self{{Self::C0=>None,"));
                for (i, c) in cs.iter().enumerate().skip(1) {
                    let bs = c
                        .fields
                        .iter()
                        .map(|s| if *s == Sort::SelfType { "tail" } else { "_" })
                        .collect::<Vec<_>>()
                        .join(",");
                    code.push_str(&format!("Self::C{i}({bs})=>Some(std::mem::replace(tail,std::sync::Arc::new(Self::C0))),"));
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
    lower_with_storage(checked, false, false, true)
}
/// Pure immutable constructor fields may share storage. Equality and dynamic
/// transport stay structural; no pointer identity acquires semantic meaning.
pub(crate) fn lower_shared(
    checked: &ink_core::definition::CheckedDefinition,
) -> LangResult<Emission> {
    lower_with_storage(checked, true, false, true)
}
/// Literal typed functions only: no generic constructor carrier or dispatcher.
pub(crate) fn lower_typed_shared(
    checked: &ink_core::definition::CheckedDefinition,
) -> LangResult<Emission> {
    lower_with_storage(checked, true, true, true)
}
/// Typed immutable storage for literal foreign functions. The generated C ABI
/// borrows these objects directly; it never serialises physical state.
pub(crate) fn lower_typed_shared_datatypes(
    checked: &ink_core::definition::CheckedDefinition,
) -> LangResult<Emission> {
    lower_with_storage(checked, true, true, false)
}
fn lower_with_storage(
    checked: &ink_core::definition::CheckedDefinition,
    shared: bool,
    typed_only: bool,
    functions: bool,
) -> LangResult<Emission> {
    let bundle = checked.bundle();
    let exports = checked.exports();
    let choices = checked.choices();
    let bundle_sha256 = checked.bundle_sha256().to_owned();
    let objects = bundle
        .objects
        .iter()
        .map(|(id, raw)| {
            Ok((
                id.clone(),
                serde_json::from_str::<Object>(raw).map_err(|e| e.to_string())?,
            ))
        })
        .collect::<LangResult<BTreeMap<_, _>>>()?;
    let mut lower = Lower {
        objects: &objects,
        selected: BTreeSet::new(),
        binder: 0,
        nodes: 0,
        shared,
        typed_only,
    };
    for id in exports {
        if !matches!(lower.declaration(id)?, Declaration::Function { .. }) {
            return Err("definition export must be a function".into());
        }
        lower.select(choices.get(id).unwrap_or(id))?;
    }
    let mut source = String::from("// ink-definition-rust-v1: checked bodies; Rust/backend are trusted.\n#![allow(non_camel_case_types, non_snake_case, non_upper_case_globals, dead_code, unused_variables, unused_parens, unused_unsafe, improper_ctypes_definitions)]\n");
    source.push_str("#[inline(never)] fn ink_def_f32_word(v:f32)->u64{if v.is_nan(){0x7fc00000}else{v.to_bits() as u64}}\n");
    if !typed_only {
        source.push_str(include_str!("definition_value.rs.txt"));
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
                let mut env = BTreeMap::new();
                let mut inputs = Vec::new();
                for (n, s) in params {
                    let binder = lower.fresh();
                    let data = matches!(s, Sort::Data(_));
                    inputs.push(format!(
                        "{binder}: {}{}",
                        if data { "&" } else { "" },
                        ty(&s)?
                    ));
                    env.insert(
                        n,
                        Expression {
                            code: binder,
                            sort: s,
                            borrowed: data,
                        },
                    );
                }
                let body = lower.expression(&body, &env, id, 0)?;
                source.push_str(&format!(
                    "fn d_{id}({}) -> {} {{ {} }}\n",
                    inputs.join(","),
                    ty(&result)?,
                    body.owned()
                ));
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
            args.push(binder);
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
        for id in exports {
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
        scope: "exact checked first-order definition bodies; trusted Rust lowering, codecs and Rust/LLVM backend; boxed baseline; no stateful source admission, physical storage refinement, host-failure preservation or execution-cost bound".into(),
    };
    Ok(Emission { source, receipt })
}

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
