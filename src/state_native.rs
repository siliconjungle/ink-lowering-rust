//! Typed Rust lowering for the checked stateful subset. Generated programs do
//! not depend on this crate and do not carry an AST or expression evaluator.
use crate::ownership::{self, Uses};
use crate::{aggregate, syntax::*, LangResult};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write;

fn ident(s: &str) -> String {
    format!("l_{s}")
}
pub(crate) fn ty(t: &Type) -> LangResult<String> {
    Ok(match t {
        Type::I32 => "i32".into(),
        Type::F32 => "f32".into(),
        Type::Vector(t, n) => format!("[{};{}]", ty(t)?, n),
        Type::U64 => "u64".into(),
        Type::U32 => "u32".into(),
        Type::Int => "BigInt".into(),
        Type::Unit => "()".into(),
        Type::String => "String".into(),
        Type::Bool => "bool".into(),
        Type::Named(n) if n == "ArithmeticError" => "InkArithmeticError".into(),
        Type::Named(n) => ident(n),
        Type::List(a) => format!("Vec<{}>", ty(a)?),
        Type::Buffer(a) => format!("OwnedBuffer<{}>", ty(a)?),
        Type::Map(k, v) => format!("OwnedMap<{},{}>", ty(k)?, ty(v)?),
        Type::Option(a) => format!("Option<{}>", ty(a)?),
        Type::Result(a, b) => format!("Result<{},{}>", ty(a)?, ty(b)?),
        Type::Table(a, b) => format!("BTreeMap<{},{}>", ty(a)?, ty(b)?),
        Type::Unknown => {
            return Err("native state backend needs a resolved type; add an annotation".into())
        }
    })
}
// Box only record fields whose inline representation reaches the enclosing
// record again. Ink types and JSON shapes remain unchanged.
pub(crate) fn boxed_field(owner: &str, t: &Type, p: &Program) -> bool {
    fn reaches(owner: &str, t: &Type, p: &Program, seen: &mut BTreeSet<String>) -> bool {
        match t {
            Type::Named(n) if n == owner => true,
            Type::Named(n) if seen.insert(n.clone()) => p
                .records
                .get(n)
                .is_some_and(|fs| fs.iter().any(|(_, t)| reaches(owner, t, p, seen))),
            Type::Option(t) | Type::Vector(t, _) => reaches(owner, t, p, seen),
            Type::Result(a, b) => reaches(owner, a, p, seen) || reaches(owner, b, p, seen),
            _ => false, // Vec and BTreeMap already provide indirection.
        }
    }
    reaches(owner, t, p, &mut BTreeSet::new())
}
fn field_ty(owner: &str, t: &Type, p: &Program) -> LangResult<String> {
    let tname = ty(t)?;
    Ok(if boxed_field(owner, t, p) {
        format!("Box<{tname}>")
    } else {
        tname
    })
}
type Env = BTreeMap<String, Type>;
// Certificates inhabit exact arithmetic at every subexpression, including
// constant-only subtrees. Never infer their literals as modular u64 values.
fn exact_expression(e: &Expr) -> LangResult<String> {
    // Bindings are borrowed exact integers. Read them directly as operands;
    // arithmetic temporaries remain owned so BigInt may reuse their storage.
    // A root variable still produces the owned result required by the cache.
    fn operand(e: &Expr) -> LangResult<String> {
        if let Expr::Var(n) = e {
            Ok(ident(n))
        } else {
            exact_expression(e)
        }
    }
    match e {
        Expr::Num(n) => Ok(format!("BigInt::from({n}u64)")),
        Expr::Var(n) => Ok(format!("(*{}).clone()", ident(n))),
        Expr::Binary(op, a, b) if ["+", "-", "*"].contains(&op.as_str()) => {
            Ok(format!("({} {op} {})", operand(a)?, operand(b)?))
        }
        _ => Err("invalid exact certificate expression".into()),
    }
}
// Ownership lowering preserves the AST and its evaluation order. Earlier
// reads of the consumed binding copy it; its final read moves the allocation.
fn exact_owned_expression(e: &Expr, owner: &str) -> LangResult<String> {
    fn occurrences(e: &Expr, owner: &str) -> usize {
        match e {
            Expr::Var(n) => usize::from(n == owner),
            Expr::Binary(_, a, b) => occurrences(a, owner) + occurrences(b, owner),
            _ => 0,
        }
    }
    fn emit(e: &Expr, owner: &str, remaining: &mut usize, operand: bool) -> LangResult<String> {
        match e {
            Expr::Var(n) if n == owner => {
                *remaining -= 1;
                Ok(if *remaining == 0 {
                    ident(n)
                } else {
                    format!("{}.clone()", ident(n))
                })
            }
            Expr::Var(n) if operand => Ok(ident(n)),
            Expr::Var(n) => Ok(format!("(*{}).clone()", ident(n))),
            Expr::Num(n) => Ok(format!("BigInt::from({n}u64)")),
            Expr::Binary(op, a, b) if ["+", "-", "*"].contains(&op.as_str()) => {
                let a = emit(a, owner, remaining, true)?;
                let b = emit(b, owner, remaining, true)?;
                Ok(format!("({a} {op} {b})"))
            }
            _ => Err("invalid owned exact certificate expression".into()),
        }
    }
    emit(e, owner, &mut occurrences(e, owner), false)
}
struct Emitter<'a> {
    p: &'a Program,
    execution: &'a ink_core::action_ir::Execution,
    plans: BTreeMap<String, aggregate::Plan>,
    bounded: BTreeMap<String, BoundEvidence>,
    serial: usize,
    /// Lexical ownership state for the action body being emitted.
    uses: Uses,
    binders: BTreeMap<String, usize>,
    /// >0 while an expression is emitted only to learn its type.
    probe: usize,
    /// Locals currently holding a shared borrow of a table row.
    borrowed: BTreeSet<String>,
    /// Field snapshots taken when a borrowed row had to be released.
    aliases: BTreeMap<(String, String), String>,
}

#[derive(Clone, Debug, serde::Serialize)]
pub struct BoundEvidence {
    pub root: String,
    pub field: String,
    pub key_bits: u32,
    pub value_bits: u32,
    pub maximum_total: String,
    pub justification: &'static str,
}

/// Conservative range analysis for one exact sum of an unsigned row field.
/// Full key-domain cardinality is used, not an observed size or host RAM bound.
pub fn bounded_caches(p: &Program) -> BTreeMap<String, BoundEvidence> {
    use num_bigint::BigInt;
    let mut result = BTreeMap::new();
    for k in &p.keeps {
        let Some(plan) = aggregate::plan(k) else {
            continue;
        };
        if plan.count || plan.stages.len() != 1 {
            continue;
        }
        let (op, binder, body) = &plan.stages[0];
        if op != "map" {
            continue;
        }
        let Expr::Call(conversion, args) = body else {
            continue;
        };
        if conversion != "Int" || args.len() != 1 {
            continue;
        }
        let Expr::Field(base, field) = &args[0] else {
            continue;
        };
        if !matches!(&**base,Expr::Var(v) if v==binder) {
            continue;
        }
        let Some(root) = p.states.iter().find(|s| s.name == plan.root) else {
            continue;
        };
        let Type::Table(key, row) = &root.ty else {
            continue;
        };
        let key_bits = match &**key {
            Type::U32 => 32,
            Type::U64 => 64,
            Type::Named(n) if p.ids.contains(n) => 128,
            _ => continue,
        };
        let Type::Named(record) = &**row else {
            continue;
        };
        let Some(fields) = p.records.get(record) else {
            continue;
        };
        let Some((_, field_type)) = fields.iter().find(|(f, _)| f == field) else {
            continue;
        };
        let value_bits = match field_type {
            Type::U32 => 32,
            Type::U64 => 64,
            _ => continue,
        };
        let maximum = (BigInt::from(1u8) << key_bits) * ((BigInt::from(1u8) << value_bits) - 1u8);
        if maximum > BigInt::from(u128::MAX) {
            continue;
        }
        result.insert(k.name.clone(),BoundEvidence{root:root.name.clone(),field:field.clone(),key_bits,value_bits,maximum_total:maximum.to_string(),justification:"nonnegative unsigned field; finite map has at most 2^key_bits entries; maximum = 2^key_bits * (2^value_bits - 1) < 2^128"});
    }
    result
}

fn modular128_expression(e: &Expr) -> LangResult<String> {
    match e {
        Expr::Num(n) => Ok(format!("{n}u128")),
        Expr::Var(n) => Ok(ident(n)),
        Expr::Binary(op, a, b) => {
            let method = match op.as_str() {
                "+" => "wrapping_add",
                "-" => "wrapping_sub",
                "*" => "wrapping_mul",
                _ => return Err("invalid polynomial operator".into()),
            };
            Ok(format!(
                "({}).{method}({})",
                modular128_expression(a)?,
                modular128_expression(b)?
            ))
        }
        _ => Err("invalid polynomial expression".into()),
    }
}
impl Emitter<'_> {
    fn cache_type(&self, n: &str) -> &'static str {
        if self.bounded.contains_key(n) {
            "u128"
        } else {
            "BigInt"
        }
    }
    fn movable(&self, n: &str) -> bool {
        self.binders.get(n) == Some(&1) && !self.borrowed.contains(n)
    }
    /// Records one emitted read of local `n`; true when it is the final read
    /// of the whole local, so the generated code may move it.
    fn read(&mut self, n: &str) -> bool {
        if self.probe > 0 {
            return false;
        }
        let Some(left) = self.uses.var.get_mut(n) else {
            return false;
        };
        *left = left.saturating_sub(1);
        *left == 0 && self.movable(n)
    }
    fn reset_ownership(&mut self, params: &[(String, Type)], body: &[Statement]) {
        self.uses = Uses::of_block(self.p, body);
        self.binders = ownership::binders(params, body);
        self.probe = 0;
        self.borrowed.clear();
        self.aliases.clear();
    }
    fn clear_ownership(&mut self) {
        self.uses = Uses::default();
        self.binders.clear();
        self.borrowed.clear();
        self.aliases.clear();
    }
    fn fresh(&mut self) -> String {
        self.serial += 1;
        format!("tmp_{}", self.serial)
    }
    fn expr(&mut self, e: &Expr, env: &Env, want: Option<&Type>) -> LangResult<(String, Type)> {
        let resolved = self.execution.type_of(e).cloned();
        let want = want.or(resolved.as_ref());
        use Type as T;
        let (code, t) = match e {
            Expr::Float(bits) => (format!("f32::from_bits({bits}u32)"), T::F32),
            Expr::Neg(value) => {
                if want == Some(&T::I32) && matches!(value.as_ref(), Expr::Num(2147483648)) {
                    return Ok(("i32::MIN".into(), T::I32));
                }
                let (v, t) = self.expr(value, env, want)?;
                let code = if t == T::F32 {
                    format!("f32::from_bits(({v}).to_bits()^0x80000000)")
                } else if t == T::Int {
                    format!("-({v})")
                } else {
                    format!("({v}).wrapping_neg()")
                };
                (code, t)
            }
            Expr::Let(..) => return Err("compute expression belongs in a pure function".into()),
            Expr::Num(n) => {
                let t = want
                    .filter(|t| matches!(t, T::U32 | T::Int | T::I32 | T::F32))
                    .cloned()
                    .unwrap_or(T::U64);
                let s = match t {
                    T::Int => format!("BigInt::from({n}u64)"),
                    T::U32 => format!("{n}u32"),
                    T::I32 => format!("{n}i32"),
                    T::F32 => format!("f32::from_bits({}u32)", (*n as f32).to_bits()),
                    _ => format!("{n}u64"),
                };
                (s, t)
            }
            Expr::Bool(v) => (v.to_string(), T::Bool),
            Expr::String(v) => (format!("{:?}.to_owned()", v), T::String),
            Expr::Unit => ("()".into(), T::Unit),
            Expr::Var(n) => {
                if let Some(t) = env.get(n) {
                    if self.read(n) {
                        // Final read of an owned local: move instead of clone.
                        (ident(n), t.clone())
                    } else {
                        (
                            format!("<{} as Clone>::clone(&{})", ty(t)?, ident(n)),
                            t.clone(),
                        )
                    }
                } else if n == "None" {
                    (
                        "None".into(),
                        want.cloned().unwrap_or(T::Option(Box::new(T::Unknown))),
                    )
                } else if let Some(k) = self.p.keeps.iter().find(|k| &k.name == n) {
                    (format!("self.keep_{}()", ident(n)), k.ty.clone())
                } else {
                    return Err(format!("native: unsupported variable {n}"));
                }
            }
            Expr::Field(base, f) => {
                if let Expr::Var(n) = &**base {
                    if self.p.enums.contains_key(n) {
                        return Ok((format!("{}::{}", ident(n), ident(f)), T::Named(n.clone())));
                    }
                    if let Some(alias) = self.aliases.get(&(n.clone(), f.clone())).cloned() {
                        return self.expr(&Expr::Var(alias), env, want);
                    }
                    // Avoid copying an entire record just to access one field.
                    if let Some(T::Named(n)) = env.get(n) {
                        if let Some(fields) = self.p.records.get(n) {
                            if let Some((_, t)) = fields.iter().find(|(s, _)| s == f) {
                                if let Expr::Var(v) = &**base {
                                    // The final read of an owned record may move
                                    // the field out (a partial move).
                                    let code = if self.read(v) {
                                        format!("{}.{}", ident(v), ident(f))
                                    } else {
                                        format!("{}.{}.clone()", ident(v), ident(f))
                                    };
                                    return Ok((code, t.clone()));
                                }
                            }
                        }
                    }
                }
                let (b, t) = self.expr(base, env, None)?;
                if let T::Vector(t, _) = t {
                    let i = ["x", "y", "z", "w"]
                        .iter()
                        .position(|s| *s == f)
                        .ok_or("vector component")?;
                    return Ok((format!("({b})[{i}].clone()"), *t));
                }
                let T::Named(n) = t else {
                    return Err("native field requires record".into());
                };
                let t = self
                    .p
                    .records
                    .get(&n)
                    .and_then(|fs| fs.iter().find(|(s, _)| s == f))
                    .ok_or("native: unknown field")?
                    .1
                    .clone();
                (
                    if boxed_field(&n, &t, self.p) {
                        format!("(*({b}).{}).clone()", ident(f))
                    } else {
                        format!("({b}).{}.clone()", ident(f))
                    },
                    t,
                )
            }
            Expr::Record(n, fs) => {
                let mut fields = vec![];
                for (f, e) in fs {
                    let t = &self.p.records[n].iter().find(|(x, _)| x == f).unwrap().1;
                    let (s, _) = self.expr(e, env, Some(t))?;
                    fields.push(format!(
                        "{}:{}",
                        ident(f),
                        if boxed_field(n, t, self.p) {
                            format!("Box::new({s})")
                        } else {
                            s
                        }
                    ))
                }
                (
                    format!("{}{{{}}}", ident(n), fields.join(",")),
                    T::Named(n.clone()),
                )
            }
            Expr::Try(e) => {
                let (s, t) = self.expr(e, env, None)?;
                let T::Result(a, _) = t else {
                    return Err("native: ? requires Result".into());
                };
                (format!("({s})?"), *a)
            }
            Expr::Binary(op, a, b) => {
                let (mut ac, mut at) = self.expr(a, env, None)?;
                if matches!(&**a, Expr::Num(_)) {
                    self.probe += 1;
                    let probed = self.expr(b, env, None);
                    self.probe -= 1;
                    let (_, bt) = probed?;
                    if matches!(bt, T::U32 | T::Int | T::I32 | T::F32) {
                        (ac, at) = self.expr(a, env, Some(&bt))?
                    }
                }
                let (bc, _) = self.expr(b, env, Some(&at))?;
                let arithmetic = ["+", "-", "*"].contains(&op.as_str());
                let s = if (op == "==" || op == "!=") && at != T::F32 {
                    format!(
                        "{}InkDataEq::ink_data_eq(&({ac}),&({bc}))",
                        if op == "!=" { "!" } else { "" }
                    )
                } else if arithmetic && matches!(at, T::U32 | T::U64 | T::I32) {
                    let method = match op.as_str() {
                        "+" => "wrapping_add",
                        "-" => "wrapping_sub",
                        _ => "wrapping_mul",
                    };
                    format!("({ac}).{method}({bc})")
                } else if arithmetic && at == T::F32 {
                    format!("temporary::ink_f32(({ac}) {op} ({bc}))")
                } else {
                    format!("(({ac}) {op} ({bc}))")
                };
                (s, if arithmetic { at } else { T::Bool })
            }
            Expr::Call(n, args) => match n.as_str() {
                "vec2" | "vec3" | "vec4" => {
                    let t = resolved.as_ref().or(want).ok_or("vector type")?;
                    let code = args
                        .iter()
                        .map(|e| self.expr(e, env, None).map(|(s, _)| s))
                        .collect::<LangResult<Vec<_>>>()?;
                    (format!("[{}]", code.join(",")), t.clone())
                }
                "Ok" | "Err" | "Some" => {
                    let inner = match (n.as_str(), want) {
                        ("Ok", Some(T::Result(a, _)))
                        | ("Err", Some(T::Result(_, a)))
                        | ("Some", Some(T::Option(a))) => Some(&**a),
                        _ => None,
                    };
                    let (s, t) = self.expr(&args[0], env, inner)?;
                    let out = want.cloned().unwrap_or_else(|| match n.as_str() {
                        "Ok" => T::Result(Box::new(t), Box::new(T::Unknown)),
                        "Err" => T::Result(Box::new(T::Unknown), Box::new(t)),
                        _ => T::Option(Box::new(t)),
                    });
                    (format!("{n}({s})"), out)
                }
                "Int" => {
                    let (s, _) = self.expr(&args[0], env, None)?;
                    (format!("BigInt::from({s})"), T::Int)
                }
                "checked_add" | "checked_sub" | "checked_mul" => {
                    let (a, t) = self.expr(&args[0], env, None)?;
                    let (b, _) = self.expr(&args[1], env, Some(&t))?;
                    (
                        format!("({a}).{n}({b}).ok_or(InkArithmeticError::Overflow)"),
                        T::Result(Box::new(t), Box::new(T::Named("ArithmeticError".into()))),
                    )
                }
                "sum" | "count" => {
                    let (s, t) = self.expr(&args[0], env, None)?;
                    let T::List(t) = t else {
                        return Err("native aggregate requires list".into());
                    };
                    if n == "count" {
                        (format!("BigInt::from(({s}).len())"), T::Int)
                    } else {
                        let zero = if *t == T::Int {
                            "BigInt::from(0u8)".into()
                        } else {
                            format!("0{}", ty(&t)?)
                        };
                        let add = if *t == T::F32 {
                            "temporary::ink_f32(a+b)"
                        } else if *t == T::Int {
                            "a+b"
                        } else {
                            "a.wrapping_add(b)"
                        };
                        (format!("({s}).into_iter().fold({zero},|a,b|{add})"), *t)
                    }
                }
                _ => {
                    let (params, result, is_change, prefix) =
                        if let Some(a) = self.p.actions.iter().find(|a| &a.name == n) {
                            (&a.params, &a.result, a.kind == ActionKind::Change, "action")
                        } else if let Some(f) = self.p.functions.iter().find(|a| &a.name == n) {
                            (&f.params, &f.result, false, "function")
                        } else {
                            return Err(format!("native unknown call {n}"));
                        };
                    let mut bindings = String::new();
                    let mut values = vec![];
                    for (e, (_, t)) in args.iter().zip(params) {
                        let (s, _) = self.expr(e, env, Some(t))?;
                        let v = self.fresh();
                        write!(bindings, "let {v}:{rt}={s};", rt = ty(t)?).unwrap();
                        values.push(v)
                    }
                    let call = format!("self.{prefix}_{}({})", ident(n), values.join(","));
                    let call = if is_change {
                        format!("transaction::nested_change({call})?")
                    } else {
                        call
                    };
                    (format!("{{{bindings}{call}}}"), result.clone())
                }
            },
            Expr::Method(base, n, args) => {
                let root = if let Expr::Var(v) = &**base {
                    self.p.states.iter().find(|s| &s.name == v)
                } else {
                    None
                };
                if let Some(root) = root {
                    let T::Table(k, v) = &root.ty else {
                        unreachable!()
                    };
                    let field = ident(&root.name);
                    if n == "values" {
                        (
                            format!("self.{field}.values().cloned().collect::<Vec<_>>()"),
                            T::List(v.clone()),
                        )
                    } else {
                        // Lookups only need the key by reference.
                        let borrowed_key = match &args[0] {
                            Expr::Var(kn)
                                if matches!(n.as_str(), "get" | "contains")
                                    && env.get(kn) == Some(k.as_ref())
                                    && !self.borrowed.contains(kn) =>
                            {
                                self.read(kn);
                                Some(ident(kn))
                            }
                            _ => None,
                        };
                        let key = match borrowed_key {
                            Some(key) => key,
                            None => self.expr(&args[0], env, Some(k))?.0,
                        };
                        match n.as_str() {
                            "get" => (
                                format!("self.{field}.get(&({key})).cloned()"),
                                T::Option(v.clone()),
                            ),
                            "contains" => (format!("self.{field}.contains_key(&({key}))"), T::Bool),
                            "remove" => (
                                format!("{{let key={key};self.set_{field}(key,None,true)}}"),
                                T::Option(v.clone()),
                            ),
                            "insert" | "replace" => {
                                let (value, _) = self.expr(&args[1], env, Some(v))?;
                                (format!("{{let key={key};let value={value};self.set_{field}(key,Some(value),false);}}"),T::Unit)
                            }
                            _ => return Err(format!("native unsupported table method {n}")),
                        }
                    }
                } else {
                    // A pipeline stage applied directly to stored rows can read
                    // them by reference instead of cloning every row first.
                    let mut by_ref = None;
                    // Generated helpers, queries and derived reads currently
                    // take &mut self. Such a closure cannot run while the table
                    // iterator holds a shared borrow; keep the owned baseline.
                    let closure_borrows_self = args
                        .iter()
                        .any(|arg| ownership::expr_mutates_state(self.p, arg));
                    if let Expr::Method(r, m, margs) = base.as_ref() {
                        if let Expr::Var(root) = r.as_ref() {
                            if let Some(state) = self.p.states.iter().find(|s| &s.name == root) {
                                let T::Table(k, v) = &state.ty else {
                                    unreachable!()
                                };
                                match (m.as_str(), margs.as_slice(), n.as_str()) {
                                    ("values", [], "map" | "filter") if !closure_borrows_self => {
                                        by_ref = Some((
                                            format!("self.{}.values()", ident(root)),
                                            T::List(v.clone()),
                                        ))
                                    }
                                    ("get", [key], "map") if !closure_borrows_self => {
                                        let key = match key {
                                            Expr::Var(kn)
                                                if env.get(kn) == Some(k.as_ref())
                                                    && !self.borrowed.contains(kn) =>
                                            {
                                                self.read(kn);
                                                ident(kn)
                                            }
                                            _ => self.expr(key, env, Some(k))?.0,
                                        };
                                        by_ref = Some((
                                            format!("self.{}.get(&({key}))", ident(root)),
                                            T::Option(v.clone()),
                                        ))
                                    }
                                    _ => {}
                                }
                            }
                        }
                    }
                    let borrowed_rows = by_ref.is_some();
                    let (s, t) = match by_ref {
                        Some(found) => found,
                        None => self.expr(base, env, None)?,
                    };
                    if n == "ok_or" {
                        let T::Option(inner) = t else {
                            return Err("native ok_or needs Option".into());
                        };
                        let (e, et) = self.expr(&args[0], env, None)?;
                        (format!("({s}).ok_or({e})"), T::Result(inner, Box::new(et)))
                    } else {
                        let Expr::Lambda(v, b) = &args[0] else {
                            return Err("native method needs lambda".into());
                        };
                        let inner = match (&t, n.as_str()) {
                            (T::List(t), "map" | "filter")
                            | (T::Option(t), "map")
                            | (T::Result(t, _), "map")
                            | (T::Result(_, t), "map_err") => t,
                            _ => return Err(format!("native unsupported method {n}")),
                        };
                        let mut local = env.clone();
                        local.insert(v.clone(), *inner.clone());
                        let (code, out) = self.expr(b, &local, None)?;
                        let (s, out) = match t {
                            T::List(t) => {
                                let mapped = if !borrowed_rows {
                                    format!(
                                        "({s}).into_iter().{n}(|{}|{{{code}}}).collect::<Vec<_>>()",
                                        ident(v)
                                    )
                                } else if n == "filter" {
                                    // Only the retained rows are cloned.
                                    format!(
                                        "{s}.filter(|{}|{{{code}}}).cloned().collect::<Vec<_>>()",
                                        ident(v)
                                    )
                                } else {
                                    format!("{s}.map(|{}|{{{code}}}).collect::<Vec<_>>()", ident(v))
                                };
                                (
                                    mapped,
                                    if n == "filter" {
                                        T::List(t)
                                    } else {
                                        T::List(Box::new(out))
                                    },
                                )
                            }
                            T::Option(_) => (
                                format!("({s}).map(|{}|{{{code}}})", ident(v)),
                                T::Option(Box::new(out)),
                            ),
                            T::Result(a, b) => (
                                format!("({s}).{n}(|{}|{{{code}}})", ident(v)),
                                if n == "map_err" {
                                    T::Result(a, Box::new(out))
                                } else {
                                    T::Result(Box::new(out), b)
                                },
                            ),
                            _ => unreachable!(),
                        };
                        (s, out)
                    }
                }
            }
            Expr::Lambda(..) => return Err("native lambda outside operator".into()),
        };
        Ok((code, t))
    }
    /// Ends every live row borrow before a statement that may take `&mut
    /// self`. A row still read whole is cloned; otherwise only the fields that
    /// are still read are copied into snapshot locals.
    fn release_borrows(
        &mut self,
        rest: &[Statement],
        env: &mut Env,
        out: &mut String,
    ) -> LangResult<()> {
        let live: Vec<String> = self
            .borrowed
            .iter()
            .filter(|b| env.contains_key(*b))
            .cloned()
            .collect();
        if live.is_empty() {
            return Ok(());
        }
        let later = Uses::of_block(self.p, rest);
        for b in live {
            self.borrowed.remove(&b);
            if later.var.get(&b).copied().unwrap_or(0) == 0 {
                continue;
            }
            let row_ty = env[&b].clone();
            let fields: Vec<(String, usize)> = later
                .field
                .iter()
                .filter(|((v, _), _)| *v == b)
                .map(|((_, f), c)| (f.clone(), *c))
                .collect();
            let collides = fields
                .iter()
                .any(|(f, _)| self.binders.contains_key(&format!("{b}__{f}")));
            let record = match &row_ty {
                Type::Named(r) => self.p.records.get(r),
                _ => None,
            };
            if later.whole.get(&b).copied().unwrap_or(0) > 0 || collides || record.is_none() {
                writeln!(
                    out,
                    "let {0}:{1}=<{1} as Clone>::clone({0});",
                    ident(&b),
                    ty(&row_ty)?
                )
                .unwrap();
                continue;
            }
            for (f, count) in fields {
                let field_ty = record
                    .unwrap()
                    .iter()
                    .find(|(x, _)| *x == f)
                    .ok_or("native: unknown field")?
                    .1
                    .clone();
                let alias = format!("{b}__{f}");
                writeln!(
                    out,
                    "let {}:{}={}.{}.clone();",
                    ident(&alias),
                    ty(&field_ty)?,
                    ident(&b),
                    ident(&f)
                )
                .unwrap();
                env.insert(alias.clone(), field_ty);
                self.binders.insert(alias.clone(), 1);
                self.uses.var.insert(alias.clone(), count);
                self.uses.whole.insert(alias.clone(), count);
                self.aliases.insert((b.clone(), f), alias);
            }
        }
        Ok(())
    }
    /// `let row = T.get(key).ok_or(error)?;` may hold a shared borrow of the
    /// stored row instead of cloning it, until `release_borrows` ends it.
    fn borrowed_row<'e>(&self, n: &str, e: &'e Expr) -> Option<(&'e str, &'e Expr, &'e Expr)> {
        let Expr::Try(inner) = e else { return None };
        let Expr::Method(base, m, args) = inner.as_ref() else {
            return None;
        };
        let (m, [err]) = (m.as_str(), args.as_slice()) else {
            return None;
        };
        let Expr::Method(root, get, keys) = base.as_ref() else {
            return None;
        };
        let (Expr::Var(r), [key]) = (root.as_ref(), keys.as_slice()) else {
            return None;
        };
        let ok = m == "ok_or"
            && get == "get"
            && self.p.states.iter().any(|s| &s.name == r)
            && self.binders.get(n) == Some(&1)
            && !ownership::expr_mutates_state(self.p, key)
            && !ownership::expr_mutates_state(self.p, err);
        ok.then_some((r.as_str(), key, err))
    }
    fn block(&mut self, stmts: &[Statement], env: &mut Env, result: &Type) -> LangResult<String> {
        let mut out = String::new();
        for (i, stmt) in stmts.iter().enumerate() {
            if ownership::mutates_state(self.p, stmt) {
                self.release_borrows(&stmts[i..], env, &mut out)?;
            }
            match stmt {
                Statement::Let(n, annotation, e) if self.borrowed_row(n, e).is_some() => {
                    let (root, key, err) = self.borrowed_row(n, e).unwrap();
                    let state = self.p.states.iter().find(|s| s.name == root).unwrap();
                    let Type::Table(k, v) = &state.ty else {
                        unreachable!()
                    };
                    if annotation.as_ref().is_some_and(|a| a != v.as_ref()) {
                        return Err("native: row binding annotation mismatch".into());
                    }
                    let key = match key {
                        Expr::Var(kn)
                            if env.get(kn) == Some(k.as_ref()) && !self.borrowed.contains(kn) =>
                        {
                            self.read(kn);
                            ident(kn)
                        }
                        _ => self.expr(key, env, Some(k))?.0,
                    };
                    let (err, _) = self.expr(err, env, None)?;
                    writeln!(
                        out,
                        "let {}:&{}=self.{}.get(&({key})).ok_or({err})?;",
                        ident(n),
                        ty(v)?,
                        ident(root)
                    )
                    .unwrap();
                    env.insert(n.clone(), *v.clone());
                    self.borrowed.insert(n.clone());
                }
                Statement::Let(n, annotation, e) => {
                    let (s, inferred) = self.expr(e, env, annotation.as_ref())?;
                    let t = annotation.as_ref().unwrap_or(&inferred);
                    writeln!(out, "let {}:{}={s};", ident(n), ty(t)?).unwrap();
                    env.insert(n.clone(), t.clone());
                }
                Statement::Return(e) => {
                    let (s, _) = self.expr(e, env, Some(result))?;
                    writeln!(out, "return {s};").unwrap();
                }
                Statement::If(e, a, b) => {
                    let (s, _) = self.expr(e, env, Some(&Type::Bool))?;
                    let yes = self.block(a, &mut env.clone(), result)?;
                    let no = self.block(b, &mut env.clone(), result)?;
                    writeln!(out, "if {s} {{{yes}}} else {{{no}}}").unwrap();
                }
                Statement::Emit(n, e) => {
                    let (s, _) = self.expr(e, env, Some(&self.p.events[n]))?;
                    writeln!(
                        out,
                        "{{let value={s};self.staged.push(EventData::{}(value));}}",
                        ident(n)
                    )
                    .unwrap();
                }
                Statement::Expr(e) => {
                    // A discarded remove result need not clone the row already
                    // owned by undo. Used results retain their independent value.
                    let discarded_remove = if let Expr::Method(base, n, args) = e {
                        if let Expr::Var(root) = base.as_ref() {
                            self.p
                                .states
                                .iter()
                                .find(|s| s.name == *root)
                                .and_then(|s| {
                                    if n == "remove" && args.len() == 1 {
                                        Some((s, &args[0]))
                                    } else {
                                        None
                                    }
                                })
                        } else {
                            None
                        }
                    } else {
                        None
                    };
                    let (s, t) = if let Some((root, key)) = discarded_remove {
                        let Type::Table(k, v) = &root.ty else {
                            unreachable!()
                        };
                        let (key, _) = self.expr(key, env, Some(k))?;
                        (
                            format!(
                                "{{let key={key};self.set_{}(key,None,false)}}",
                                ident(&root.name)
                            ),
                            Type::Option(v.clone()),
                        )
                    } else {
                        self.expr(e, env, None)?
                    };
                    writeln!(out, "let _:{}={s};", ty(&t)?).unwrap();
                }
            }
        }
        Ok(out)
    }
    fn contribution(&mut self, name: &str, plan: &aggregate::Plan) -> LangResult<String> {
        let root = self
            .p
            .states
            .iter()
            .find(|s| s.name == plan.root)
            .ok_or("unknown plan root")?;
        let Type::Table(_, row) = &root.ty else {
            unreachable!()
        };
        if let Some(bound) = self.bounded.get(name) {
            return Ok(format!(
                "fn contribution_{}(row:&{})->u128{{row.{} as u128}}\n",
                ident(name),
                ty(row)?,
                ident(&bound.field)
            ));
        }
        let mut current = "row".to_string();
        let mut current_ty = *row.clone();
        let mut out = String::new();
        for (op, v, body) in &plan.stages {
            let env = [(v.clone(), current_ty.clone())].into();
            let (e, t) = self.expr(body, &env, None)?;
            if op == "filter" {
                write!(
                    out,
                    "{{let {}=&{current};if !({e}){{return BigInt::from(0u8)}}}}",
                    ident(v)
                )
                .unwrap();
            } else {
                let next = self.fresh();
                write!(out, "let {next}={{let {}=&{current};{e}}};", ident(v)).unwrap();
                current = next;
                current_ty = t;
            }
        }
        let result = if plan.count {
            "BigInt::from(1u8)".into()
        } else {
            if current_ty != Type::Int {
                return Err("native maintenance needs exact Int contributions".into());
            }
            current
        };
        Ok(format!(
            "fn contribution_{}(row:&{})->BigInt{{{out}{result}}}\n",
            ident(name),
            ty(row)?
        ))
    }
}

pub fn emit_selected(
    selected: &ink_core::optimisation::CheckedSelection,
    certificate: Option<&aggregate::Certificate>,
) -> LangResult<String> {
    emit_selected_with_storage(selected, certificate, false, None)
}
pub fn emit_selected_with_storage(
    selected: &ink_core::optimisation::CheckedSelection,
    certificate: Option<&aggregate::Certificate>,
    narrow: bool,
    storage: Option<&crate::storage::Policy>,
) -> LangResult<String> {
    let layout = crate::snapshot::selected_layout(selected)?;
    emit_with_layout(
        selected.module().program(),
        certificate,
        narrow,
        storage,
        &layout,
    )
}
fn floating(t: &Type, p: &Program, seen: &mut BTreeSet<String>) -> bool {
    match t {
        Type::F32 => true,
        Type::Named(n) if seen.insert(n.clone()) => p
            .records
            .get(n)
            .is_some_and(|fs| fs.iter().any(|(_, t)| floating(t, p, seen))),
        Type::List(t) | Type::Buffer(t) | Type::Vector(t, _) | Type::Option(t) => {
            floating(t, p, seen)
        }
        Type::Result(a, b) | Type::Map(a, b) | Type::Table(a, b) => {
            floating(a, p, seen) || floating(b, p, seen)
        }
        _ => false,
    }
}
pub fn emit(p: &Program, certificate: Option<&aggregate::Certificate>) -> LangResult<String> {
    emit_with_bounds(p, certificate, false)
}

pub fn bounded_caches_with_certificate(
    p: &Program,
    c: &aggregate::Certificate,
) -> BTreeMap<String, BoundEvidence> {
    let mut bounds = bounded_caches(p);
    bounds.retain(|n, _| {
        p.keeps
            .iter()
            .find(|k| &k.name == n)
            .is_some_and(|k| aggregate::plan_with_certificate(p, k, c).is_some())
    });
    bounds
}

pub fn emit_with_bounds(
    p: &Program,
    certificate: Option<&aggregate::Certificate>,
    narrow: bool,
) -> LangResult<String> {
    emit_with_storage(p, certificate, narrow, None)
}

pub fn emit_with_storage(
    p: &Program,
    certificate: Option<&aggregate::Certificate>,
    narrow: bool,
    storage: Option<&crate::storage::Policy>,
) -> LangResult<String> {
    let layout = crate::snapshot::layout(p)?;
    emit_with_layout(p, certificate, narrow, storage, &layout)
}
fn emit_with_layout(
    p: &Program,
    certificate: Option<&aggregate::Certificate>,
    narrow: bool,
    storage: Option<&crate::storage::Policy>,
    layout: &crate::snapshot_wire::Layout,
) -> LangResult<String> {
    if narrow && certificate.is_none() {
        return Err("bounded cache admission requires a source-bound representation entry".into());
    }
    let module = ink_core::core::CheckedModule::from_source(p.clone())?;
    let action_ir = ink_core::action_ir::CheckedActions::elaborate(&module)?;
    let execution = action_ir.execution()?;
    if let Some(c) = certificate {
        aggregate::verify(c)?;
    }
    if let Some(policy) = storage {
        policy.check(p, certificate)?;
    }
    let plans = if let Some(c) = certificate {
        p.keeps
            .iter()
            .filter_map(|k| aggregate::plan_with_certificate(p, k, c).map(|v| (k.name.clone(), v)))
            .collect()
    } else {
        BTreeMap::new()
    };
    let mut emitter = Emitter {
        p,
        execution: &execution,
        plans,
        bounded: if narrow && certificate.is_some() {
            bounded_caches_with_certificate(p, certificate.unwrap())
        } else {
            BTreeMap::new()
        },
        serial: 0,
        uses: Uses::default(),
        binders: BTreeMap::new(),
        probe: 0,
        borrowed: BTreeSet::new(),
        aliases: BTreeMap::new(),
    };
    let mut out = String::from(
        "#![allow(non_camel_case_types,non_snake_case,unused_variables,unused_parens,dead_code)]\n",
    );
    out.push_str(include_str!("state_native_support.txt"));
    out.push_str("\nmod temporary {\n");
    out.push_str(include_str!("temporary.rs.txt"));
    out.push_str(
        "\n}\nuse temporary::{OwnedBuffer,OwnedMap,ink_parallel_map,ink_parallel_update};\n",
    );
    out.push_str(r#"
impl<T:Clone> Wire for OwnedBuffer<T>{fn from_json(_: &Json)->Result<Self,String>{Err("temporary storage is internal to a pure invocation".into())}fn to_json(&self)->Json{Json::Null}}
impl<K:Ord+Clone,V:Clone> Wire for OwnedMap<K,V>{fn from_json(_: &Json)->Result<Self,String>{Err("temporary storage is internal to a pure invocation".into())}fn to_json(&self)->Json{Json::Null}}
impl<T:Clone> InkDataEq for OwnedBuffer<T>{fn ink_data_eq(&self,_:&Self)->bool{panic!("temporary storage has no value equality")}}
impl<K:Ord+Clone,V:Clone> InkDataEq for OwnedMap<K,V>{fn ink_data_eq(&self,_:&Self)->bool{panic!("temporary storage has no value equality")}}
"#);

    out.push_str("\nmod transaction {\n");
    out.push_str(ink_core::TRANSACTION_RUST_SOURCE);
    out.push_str("\n}\n");
    if storage.is_some() {
        out.push_str("\nmod ordered_storage {\n");
        out.push_str(include_str!("ordered_storage.rs"));
        out.push_str("\n}\nuse ordered_storage::OrderedStorage;\n");
    }
    out.push_str("\nmod portable {\n");
    out.push_str(ink_core::SNAPSHOT_WIRE_RUST_SOURCE);
    out.push_str("\n}\npub use portable::Limits as SnapshotLimits;\n");
    writeln!(out,"fn snapshot_layout()->portable::Layout{{portable::Layout{{program:{:?},schema:{:?},roots:vec![",layout.program,layout.schema).unwrap();
    for (n, k, v) in &layout.roots {
        writeln!(
            out,
            "({n:?}.into(),{},{}),",
            crate::snapshot_code::schema_code(k),
            crate::snapshot_code::schema_code(v)
        )
        .unwrap();
    }
    out.push_str("],events:vec![");
    for (n, t) in &layout.events {
        writeln!(
            out,
            "({n:?}.into(),{}),",
            crate::snapshot_code::schema_code(t)
        )
        .unwrap();
    }
    out.push_str("]}}\n");
    // Nominal IDs remain distinct types even though their native storage is u128.
    for n in &p.ids {
        let id = ident(n);
        writeln!(out,r#"
#[derive(Clone,Copy,Debug,PartialEq,Eq,PartialOrd,Ord)] pub struct {id}(pub u128);
impl Wire for {id} {{
 fn to_json(&self)->Json{{json!(format!("{{:032x}}",self.0))}}
 fn from_json(v:&Json)->Result<Self,String>{{let s=v.as_str().ok_or("expected ID")?;if s.len()!=32 || !s.bytes().all(|b|b.is_ascii_hexdigit()){{return Err("invalid ID".into())}} Ok(Self(u128::from_str_radix(s,16).map_err(|e|e.to_string())?))}}
}}
"#).unwrap();
    }
    for (n, fs) in &p.records {
        let id = ident(n);
        let fields = fs
            .iter()
            .map(|(f, t)| Ok(format!("pub {}:{}", ident(f), field_ty(n, t, p)?)))
            .collect::<LangResult<Vec<_>>>()?
            .join(",");
        let eq = if fs.iter().any(|(_, t)| floating(t, p, &mut BTreeSet::new())) {
            ""
        } else {
            ",Eq"
        };
        writeln!(out,"#[derive(Clone,Debug,PartialEq{eq})] pub struct {id}{{{fields}}}\nimpl Wire for {id} {{fn to_json(&self)->Json{{json!({{").unwrap();
        for (f, _) in fs {
            writeln!(out, "{f:?}:self.{}.to_json(),", ident(f)).unwrap();
        }
        writeln!(out,"}})}} fn from_json(v:&Json)->Result<Self,String>{{let obj=v.as_object().ok_or(\"expected record\")?;if obj.len()!={}{{return Err(\"record field mismatch\".into())}}Ok(Self{{",fs.len()).unwrap();
        for (f, t) in fs {
            writeln!(
                out,
                "{}:<{} as Wire>::from_json(obj.get({f:?}).ok_or(\"missing field\")?)?,",
                ident(f),
                field_ty(n, t, p)?
            )
            .unwrap();
        }
        out.push_str("})}}\n");
    }
    for (n, variants) in &p.enums {
        let id = ident(n);
        writeln!(out,"#[derive(Clone,Copy,Debug,PartialEq,Eq)] pub enum {id}{{{}}}\nimpl Wire for {id}{{fn to_json(&self)->Json{{match self{{",variants.iter().map(|v|ident(v)).collect::<Vec<_>>().join(",")).unwrap();
        for v in variants {
            writeln!(out, "Self::{}=>json!({:?}),", ident(v), format!("{n}.{v}")).unwrap();
        }
        out.push_str("}}fn from_json(v:&Json)->Result<Self,String>{match v.as_str(){");
        for v in variants {
            writeln!(
                out,
                "Some({:?})=>Ok(Self::{}),",
                format!("{n}.{v}"),
                ident(v)
            )
            .unwrap();
        }
        out.push_str("_=>Err(\"invalid enum\".into())}}}\n");
    }
    for n in p.ids.iter().chain(p.enums.keys()) {
        writeln!(
            out,
            "impl InkDataEq for {} {{fn ink_data_eq(&self,other:&Self)->bool{{self==other}}}}",
            ident(n)
        )
        .unwrap();
    }
    for (n, fields) in &p.records {
        let comparisons = fields
            .iter()
            .map(|(f, _)| format!("self.{}.ink_data_eq(&other.{})", ident(f), ident(f)))
            .collect::<Vec<_>>();
        writeln!(
            out,
            "impl InkDataEq for {} {{fn ink_data_eq(&self,other:&Self)->bool{{{}}}}}",
            ident(n),
            if comparisons.is_empty() {
                "true".into()
            } else {
                comparisons.join("&&")
            }
        )
        .unwrap();
    }
    out.push_str("#[derive(Clone,Debug)] pub enum EventData {\n");
    for (n, t) in &p.events {
        writeln!(out, "{}({}),", ident(n), ty(t)?).unwrap();
    }
    out.push_str("}\nimpl EventData {fn wire(&self)->(&'static str,Json){match *self {\n");
    for (n, _) in &p.events {
        writeln!(out, "Self::{}(ref v)=>({n:?},v.to_json()),", ident(n)).unwrap();
    }
    out.push_str("}}}\n");
    out.push_str("enum Undo {\n");
    for s in &p.states {
        let Type::Table(k, v) = &s.ty else {
            unreachable!()
        };
        write!(
            out,
            "{} {{key:{},old:Option<{}>",
            ident(&s.name),
            ty(k)?,
            ty(v)?
        )
        .unwrap();
        for (n, plan) in &emitter.plans {
            if plan.root == s.name {
                let cache_ty = if aggregate::journal(certificate.unwrap()).is_some()
                    && !emitter.bounded.contains_key(n)
                {
                    "Option<(u8,BigInt)>"
                } else {
                    emitter.cache_type(n)
                };
                write!(out, ",cache_{}:{}", ident(n), cache_ty).unwrap();
            }
        }
        out.push_str("},\n");
    }
    out.push_str("}\n");
    out.push_str(
        "pub struct State {version:u64,staged:Vec<EventData>,outbox:Vec<Event>,undo:Vec<Undo>,\n",
    );
    for s in &p.states {
        let row_type = if storage.is_some_and(|policy| policy.roots.contains_key(&s.name)) {
            let Type::Table(k, v) = &s.ty else {
                unreachable!()
            };
            format!("OrderedStorage<{},{}>", ty(k)?, ty(v)?)
        } else {
            ty(&s.ty)?
        };
        writeln!(out, "{}:{row_type},", ident(&s.name)).unwrap();
    }
    for n in emitter.plans.keys() {
        writeln!(out, "cache_{}:{},", ident(n), emitter.cache_type(n)).unwrap();
    }
    out.push_str("}\nimpl Default for State {fn default()->Self{Self::new()}}\nimpl State {pub fn parallel_statistics()->Json{let(n,ids)=temporary::ink_parallel_statistics();json!({\"workers\":n,\"workerIds\":ids})} pub fn new()->Self{Self{version:0,staged:vec![],outbox:vec![],undo:vec![],\n");
    for s in &p.states {
        let constructor = if let Some(config) = storage.and_then(|policy| policy.roots.get(&s.name))
        {
            let mode = match config.layout {
                crate::storage::Layout::InlineRows => "rows",
                crate::storage::Layout::Columns => "columns",
            };
            let limit = match config.promote_at {
                Some(n) => format!("Some({n})"),
                None => "None".into(),
            };
            format!("OrderedStorage::{mode}({limit})")
        } else {
            "BTreeMap::new()".into()
        };
        writeln!(out, "{}:{constructor},", ident(&s.name)).unwrap();
    }
    for n in emitter.plans.keys() {
        writeln!(
            out,
            "cache_{}:{}::from(0u8),",
            ident(n),
            emitter.cache_type(n)
        )
        .unwrap();
    }
    out.push_str("}}\n");
    out.push_str("pub fn version(&self)->u64{self.version}\npub fn outbox(&self)->&[Event]{&self.outbox}\npub fn acknowledge_through(&mut self,commit:u64,position:u64){self.outbox.retain(|e|(e.commit,e.position)>(commit,position));}\n");
    out.push_str("pub fn checkpoint(&self)->Result<Vec<u8>,String>{self.checkpoint_with_limits(SnapshotLimits::default())}\npub fn checkpoint_with_limits(&self,limits:SnapshotLimits)->Result<Vec<u8>,String>{if !self.undo.is_empty()||!self.staged.is_empty(){return Err(\"checkpoint requires transaction boundary\".into())}let layout=snapshot_layout();let tables=vec![");
    for (n, _, _) in &layout.roots {
        writeln!(
            out,
            "self.{}.iter().map(|(k,v)|(k.to_json(),v.to_json())).collect(),",
            ident(n)
        )
        .unwrap();
    }
    out.push_str("];let outbox=self.outbox.iter().map(|e|{let(channel,value)=match e.data{");
    for (i, (n, _)) in layout.events.iter().enumerate() {
        writeln!(out, "EventData::{}(ref v)=>({i},v.to_json()),", ident(n)).unwrap();
    }
    out.push_str("};portable::Event{commit:e.commit,position:e.position,channel,value}}).collect();portable::encode(&layout,&portable::Logical{version:self.version,tables,outbox},limits)}\n");
    out.push_str("pub fn restore(bytes:&[u8])->Result<Self,String>{Self::restore_with_limits(bytes,SnapshotLimits::default())}\npub fn restore_with_limits(bytes:&[u8],limits:SnapshotLimits)->Result<Self,String>{let layout=snapshot_layout();let logical=portable::decode(&layout,bytes,limits)?;let mut state=Self::new();state.version=logical.version;let mut tables=logical.tables.into_iter();");
    for (n, _, _) in &layout.roots {
        let s = p.states.iter().find(|s| &s.name == n).unwrap();
        let Type::Table(k, v) = &s.ty else {
            unreachable!()
        };
        writeln!(out,"for(k,v)in tables.next().unwrap(){{state.{}.insert(<{} as Wire>::from_json(&k)?,<{} as Wire>::from_json(&v)?);}}",ident(n),ty(k)?,ty(v)?).unwrap();
    }
    out.push_str("state.outbox=logical.outbox.into_iter().map(|e|{let data=match e.channel{");
    for (i, (n, _)) in layout.events.iter().enumerate() {
        writeln!(
            out,
            "{i}=>EventData::{}(<{} as Wire>::from_json(&e.value)?),",
            ident(n),
            ty(&p.events[n])?
        )
        .unwrap();
    }
    out.push_str("_=>return Err(\"unknown event channel\".into())};Ok(Event{commit:e.commit,position:e.position,data})}).collect::<Result<Vec<_>,String>>()?;");
    for (n, plan) in &emitter.plans {
        let id = ident(n);
        let root = ident(&plan.root);
        if emitter.bounded.contains_key(n) {
            writeln!(out,"for row in state.{root}.values(){{state.cache_{id}=state.cache_{id}.checked_add(Self::contribution_{id}(row)).ok_or(\"restored aggregate violates range\")?;}}").unwrap();
        } else {
            writeln!(out,"for row in state.{root}.values(){{state.cache_{id}+=Self::contribution_{id}(row);}}").unwrap();
        }
    }
    out.push_str("Ok(state)}\n");
    for (n, plan) in emitter.plans.clone() {
        out.push_str(&emitter.contribution(&n, &plan)?);
    }
    // A single typed write primitive per root owns its undo and cache entries.
    for s in &p.states {
        let field = ident(&s.name);
        let Type::Table(k, v) = &s.ty else {
            unreachable!()
        };
        // Ordered-map insertion/removal returns the actual previous value.
        // Reuse it for rollback instead of performing a separate lookup.
        writeln!(
            out,
            "fn set_{field}(&mut self,key:{},value:Option<{}>,return_old:bool)->Option<{}>{{",
            ty(k)?,
            ty(v)?,
            ty(v)?
        )
        .unwrap();
        for (n, plan) in &emitter.plans {
            if plan.root == s.name {
                writeln!(
                    out,
                    "let new_part_{}=value.as_ref().map(Self::contribution_{});",
                    ident(n),
                    ident(n)
                )
                .unwrap();
            }
        }
        writeln!(out,"let old=match value{{Some(v)=>self.{field}.insert(key.clone(),v),None=>self.{field}.remove(&key)}};").unwrap();
        for (n, plan) in emitter.plans.clone() {
            if plan.root != s.name {
                continue;
            }
            let id = ident(&n);
            let c = certificate.unwrap();
            let bounded = emitter.bounded.contains_key(&n);
            let journal = aggregate::journal(c).filter(|_| !bounded);
            let total = if bounded {
                format!("self.cache_{id}.clone()")
            } else {
                format!("&self.cache_{id}")
            };
            if journal.is_none() {
                writeln!(out, "let undo_{id}=self.cache_{id}.clone();").unwrap();
            }
            writeln!(out,"let (next_{id}, saved_{id})={{let total={total};let old_part=old.as_ref().map(Self::contribution_{id});match (old_part,new_part_{id}){{").unwrap();
            for (kind, pattern, e, vars) in [
                (0, "(None,Some(new))", &c.insert, vec!["total", "new"]),
                (
                    1,
                    "(Some(old),Some(new))",
                    &c.replace,
                    vec!["total", "old", "new"],
                ),
                (2, "(Some(old),None)", &c.remove, vec!["total", "old"]),
            ] {
                write!(out, "{pattern}=>{{").unwrap();
                for v in vars {
                    let borrow = if bounded || v == "total" { "" } else { "&" };
                    write!(out, "let {}={borrow}{v};", ident(v)).unwrap();
                }
                if let Some(journal) = journal {
                    let action = journal.action(kind);
                    writeln!(out,"let saved={};let l_saved=&saved;let l_total=std::mem::take(&mut self.cache_{id});let next={};(next,Some(({kind}u8,saved))) }},", exact_expression(&action.save)?,exact_owned_expression(&action.apply,"total")?).unwrap();
                } else {
                    let expr = if bounded {
                        modular128_expression(e)?
                    } else {
                        write!(out, "let l_total=std::mem::take(&mut self.cache_{id});").unwrap();
                        exact_owned_expression(e, "total")?
                    };
                    writeln!(out, "({expr},None::<(u8,BigInt)>) }},").unwrap();
                }
            }
            let identity = if bounded {
                "total".into()
            } else {
                format!("std::mem::take(&mut self.cache_{id})")
            };
            writeln!(
                out,
                "(None,None)=>({identity},None)}}}};self.cache_{id}=next_{id};"
            )
            .unwrap();
            if journal.is_some() {
                writeln!(out, "let undo_{id}=saved_{id};").unwrap();
            }
        }
        write!(
            out,
            "let result=if return_old{{old.clone()}}else{{None}};self.undo.push(Undo::{field}{{key,old"
        )
        .unwrap();
        for (n, plan) in &emitter.plans {
            if plan.root == s.name {
                write!(out, ",cache_{}:undo_{}", ident(n), ident(n)).unwrap();
            }
        }
        out.push_str("});\n");
        out.push_str("result}\n");
    }
    out.push_str("fn rollback(&mut self){for undo in self.undo.drain(..).rev(){match undo{\n");
    for s in &p.states {
        let id = ident(&s.name);
        write!(out, "Undo::{id}{{key,old").unwrap();
        for (n, plan) in &emitter.plans {
            if plan.root == s.name {
                write!(out, ",cache_{}", ident(n)).unwrap();
            }
        }
        write!(out,"}}=>{{match old{{Some(v)=>{{self.{id}.insert(key,v);}},None=>{{self.{id}.remove(&key);}}}}").unwrap();
        for (n, plan) in &emitter.plans {
            if plan.root == s.name {
                let cache = ident(n);
                if let Some(journal) = certificate
                    .and_then(aggregate::journal)
                    .filter(|_| !emitter.bounded.contains_key(n))
                {
                    write!(out,"if let Some((kind,saved))=cache_{cache}{{let l_total=std::mem::take(&mut self.cache_{cache});let l_saved=&saved;self.cache_{cache}=match kind{{").unwrap();
                    for kind in 0..3 {
                        write!(
                            out,
                            "{kind}=>{},",
                            exact_owned_expression(&journal.action(kind).restore, "total")?
                        )
                        .unwrap();
                    }
                    out.push_str("_=>unreachable!(\"internal journal operation\")};}");
                } else {
                    write!(out, "self.cache_{cache}=cache_{cache};").unwrap();
                }
            }
        }
        out.push_str("},\n");
    }
    out.push_str("}}self.staged.clear();}\n");
    for k in execution.keeps() {
        let body = if emitter.plans.contains_key(&k.name) {
            if emitter.bounded.contains_key(&k.name) {
                format!("BigInt::from(self.cache_{})", ident(&k.name))
            } else {
                format!("self.cache_{}.clone()", ident(&k.name))
            }
        } else {
            emitter.expr(&k.value, &Env::new(), Some(&k.ty))?.0
        };
        writeln!(
            out,
            "fn keep_{}(&mut self)->{}{{{body}}}",
            ident(&k.name),
            ty(&k.ty)?
        )
        .unwrap();
    }
    let mut parallel_tasks = Vec::new();
    for f in &p.functions {
        let (body, tasks) = crate::pure_rust::body_with_tasks(p, f)?;
        parallel_tasks.extend(tasks);
        let params = f
            .params
            .iter()
            .map(|(n, t)| Ok(format!("{}:{}", ident(n), ty(t)?)))
            .collect::<LangResult<Vec<_>>>()?
            .join(",");
        writeln!(
            out,
            "{}fn function_{}(&self,{params})->{}{{{body}}}",
            if ink_core::local_collections::owned(&f.result, p)
                || f.params
                    .iter()
                    .any(|(_, t)| ink_core::local_collections::owned(t, p))
            {
                ""
            } else {
                "pub "
            },
            ident(&f.name),
            ty(&f.result)?
        )
        .unwrap();
    }
    for (_, method) in &parallel_tasks {
        out.push_str(method);
        out.push('\n');
    }
    out.push_str("#[cfg(target_arch=\"wasm32\")] pub fn parallel_worker(&self,task:&Json)->Result<Json,String>{let start=task[\"start\"].as_u64().and_then(|x|u32::try_from(x).ok()).ok_or(\"parallel start\")?;let items=task[\"items\"].as_array().ok_or(\"parallel items\")?;let captures=task[\"captures\"].as_array().ok_or(\"parallel captures\")?;temporary::with_parallel_worker(||match task[\"callback\"].as_str().ok_or(\"parallel callback\")?{\n");
    for (name, _) in &parallel_tasks {
        writeln!(
            out,
            "{name:?}=>self.parallel_task_{name}(start,items,captures),"
        )
        .unwrap();
    }
    out.push_str("_=>Err(\"unknown compiled parallel callback\".into()),})}\n");
    for a in execution.actions() {
        // A direct bounded keep query admits an allocation-free exact host ABI.
        // The ordinary language/JSON API still returns Int. This extra view is
        // generated from checked structure, never an application name.
        if a.kind == ActionKind::Query && a.params.is_empty() && a.result == Type::Int {
            if let [Statement::Return(Expr::Var(keep))] = a.body.as_slice() {
                if emitter.bounded.contains_key(keep) {
                    writeln!(out,"pub fn query_words_{}(&self)->(u64,u64){{let v=self.cache_{};(v as u64,(v>>64) as u64)}}",ident(&a.name),ident(keep)).unwrap();
                }
            }
        }
        let id = ident(&a.name);
        let params = a
            .params
            .iter()
            .map(|(n, t)| Ok(format!("{}:{}", ident(n), ty(t)?)))
            .collect::<LangResult<Vec<_>>>()?
            .join(",");
        let args = a
            .params
            .iter()
            .map(|(n, _)| ident(n))
            .collect::<Vec<_>>()
            .join(",");
        let result = ty(&a.result)?;
        emitter.reset_ownership(&a.params, &a.body);
        let body = emitter.block(&a.body, &mut a.params.iter().cloned().collect(), &a.result)?;
        emitter.clear_ownership();
        writeln!(out,"fn action_{id}(&mut self,{params})->{result}{{{body}}}\npub fn invoke_view_{id}(&mut self,{params})->Result<OutcomeView<'_,{result}>,String>{{let result=self.action_{id}({args});").unwrap();
        if a.kind == ActionKind::Query {
            out.push_str(
                "Ok(OutcomeView{result,committed:false,version:self.version,events:&[]})}\n",
            );
        } else {
            out.push_str("let version=match transaction::decide(self.version,result.is_ok()){transaction::Decision::Rollback=>{self.rollback();return Ok(OutcomeView{result,committed:false,version:self.version,events:&[]})},transaction::Decision::Exhausted=>{self.rollback();return Err(\"commit sequence exhausted\".into())},transaction::Decision::Commit{version}=>version};self.version=version;self.undo.clear();let start=self.outbox.len();self.outbox.extend(transaction::publish(version,self.staged.drain(..)).map(|published|Event{commit:published.commit,position:published.position,data:published.value}));Ok(OutcomeView{result,committed:true,version,events:&self.outbox[start..]})}\n");
        }
        writeln!(out,"pub fn invoke_{id}(&mut self,{params})->Result<Outcome<{result}>,String>{{self.invoke_view_{id}({args}).map(OutcomeView::into_owned)}}").unwrap();
    }
    out.push_str("pub fn call_json(&mut self,name:&str,args:&Json)->Result<Json,String>{let args=args.as_array().ok_or(\"expected argument array\")?;match name{\n");
    for f in &p.functions {
        if ink_core::local_collections::owned(&f.result, p)
            || f.params
                .iter()
                .any(|(_, t)| ink_core::local_collections::owned(t, p))
        {
            writeln!(
                out,
                "{:?}=>Err(\"temporary storage is internal to a pure invocation\".into()),",
                f.name
            )
            .unwrap();
            continue;
        }
        write!(
            out,
            "{:?}=>{{if args.len()!={}{{return Err(\"argument count mismatch\".into())}}",
            f.name,
            f.params.len()
        )
        .unwrap();
        let mut argv = vec![];
        for (i, (_, t)) in f.params.iter().enumerate() {
            write!(
                out,
                "let a{i}=<{} as Wire>::from_json(&args[{i}])?;",
                ty(t)?
            )
            .unwrap();
            argv.push(format!("a{i}"));
        }
        writeln!(
            out,
            "Ok(self.function_{}({}).to_json())}},",
            ident(&f.name),
            argv.join(",")
        )
        .unwrap();
    }
    out.push_str("_=>Err(\"unknown function\".into())}}\n");
    out.push_str("pub fn invoke_json(&mut self,name:&str,args:&Json)->Result<Json,String>{let args=args.as_array().ok_or(\"expected argument array\")?;match name{\n");
    for a in &p.actions {
        write!(
            out,
            "{:?}=>{{if args.len()!={}{{return Err(\"argument count mismatch\".into())}}",
            a.name,
            a.params.len()
        )
        .unwrap();
        let mut argv = vec![];
        for (i, (_, t)) in a.params.iter().enumerate() {
            write!(
                out,
                "let a{i}=<{} as Wire>::from_json(&args[{i}])?;",
                ty(t)?
            )
            .unwrap();
            argv.push(format!("a{i}"));
        }
        writeln!(
            out,
            "Ok(self.invoke_view_{}({})?.to_json())}},",
            ident(&a.name),
            argv.join(",")
        )
        .unwrap();
    }
    out.push_str("_=>Err(\"unknown action\".into())}}}\n");
    Ok(out)
}
