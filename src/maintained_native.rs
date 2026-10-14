//! Literal Rust for checked maintained group folds (`ink-maintained-fold-v1`).
//!
//! The database supplies each fold's contribution, combination and inverse
//! with their proofs; the core replays them. This module emits those exact
//! definitions over native source rows (a codec/call-lowering lane, as in the
//! JavaScript emitter), never a recognised aggregate. Carriers it cannot read
//! natively make the plan unemittable for Rust, so selection fails closed.
use ink_core::{
    action_model::Projection,
    core::CheckedModule,
    logic::{Declaration, Sort, Term},
    maintained::CheckedViews,
    syntax::{Program, Type},
    LangResult,
};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write;

#[derive(Clone)]
enum Value {
    Word(String),
    Bool(String),
    Fields(usize, Vec<Value>),
    /// Unused source fields need no codec; inspecting one declines.
    Opaque,
}
impl Value {
    fn scalar(&self) -> LangResult<String> {
        match self {
            Self::Word(s) | Self::Bool(s) => Ok(s.clone()),
            _ => Err("native maintained definition result carrier".into()),
        }
    }
}

struct Emit<'a> {
    ds: &'a BTreeMap<String, Declaration>,
    active: BTreeSet<String>,
    next: usize,
    work: usize,
}
impl Emit<'_> {
    fn temp(&mut self, value: String, word: bool, out: &mut String) -> Value {
        let n = format!("m{}", self.next);
        self.next += 1;
        write!(out, "let {n}:{}={value};", if word { "u64" } else { "bool" }).unwrap();
        if word { Value::Word(n) } else { Value::Bool(n) }
    }
    fn expr(&mut self, t: &Term, env: &BTreeMap<String, Value>, out: &mut String, depth: usize) -> LangResult<Value> {
        self.work += 1;
        if self.work > 20_000 || depth > 128 {
            return Err("native maintained definition emission bound".into());
        }
        Ok(match t {
            Term::Var(n) => env.get(n).cloned().ok_or("native maintained definition variable")?,
            Term::U64(n) => Value::Word(format!("{n}u64")),
            Term::Bool(b) => Value::Bool(b.to_string()),
            Term::Construct { constructor, arguments, .. } => Value::Fields(
                *constructor,
                arguments.iter().map(|t| self.expr(t, env, out, depth + 1)).collect::<LangResult<_>>()?,
            ),
            Term::Match { scrutinee, branches } => {
                let Value::Fields(tag, fields) = self.expr(scrutinee, env, out, depth + 1)? else {
                    return Err("native maintained definition dynamic carrier".into());
                };
                let b = branches.get(tag).ok_or("native maintained definition constructor")?;
                if b.bindings.len() != fields.len() {
                    return Err("native maintained definition fields".into());
                }
                let mut local = env.clone();
                local.extend(b.bindings.iter().cloned().zip(fields));
                self.expr(&b.body, &local, out, depth + 1)?
            }
            Term::Call { function, arguments } => {
                let args = arguments.iter().map(|t| self.expr(t, env, out, depth + 1)).collect::<LangResult<Vec<_>>>()?;
                if !self.active.insert(function.clone()) {
                    return Err("native maintained definition recursive call".into());
                }
                let Declaration::Function { params, body, .. } =
                    self.ds.get(function).ok_or("native maintained definition call")?
                else {
                    return Err("native maintained definition function".into());
                };
                if params.len() != args.len() {
                    return Err("native maintained definition arity".into());
                }
                let local = params.iter().map(|p| p.0.clone()).zip(args).collect();
                let v = self.expr(body, &local, out, depth + 1)?;
                self.active.remove(function);
                v
            }
            Term::SelfCall(_) => return Err("native maintained definition recursion".into()),
            Term::If { condition, on_true, on_false } => {
                let Value::Bool(c) = self.expr(condition, env, out, depth + 1)? else {
                    return Err("native maintained definition condition".into());
                };
                let mut yes = String::new();
                let a = self.expr(on_true, env, &mut yes, depth + 1)?;
                let mut no = String::new();
                let b = self.expr(on_false, env, &mut no, depth + 1)?;
                let word = match (&a, &b) {
                    (Value::Word(..), Value::Word(..)) => true,
                    (Value::Bool(..), Value::Bool(..)) => false,
                    _ => return Err("native maintained definition branch carrier".into()),
                };
                let value = format!("if {c} {{{yes}{}}} else {{{no}{}}}", a.scalar()?, b.scalar()?);
                self.temp(value, word, out)
            }
            Term::Binary { op, left, right } => {
                let a = self.expr(left, env, out, depth + 1)?;
                let b = self.expr(right, env, out, depth + 1)?;
                match (op.as_str(), &a, &b) {
                    ("+" | "-" | "*" | "&", Value::Word(x), Value::Word(y)) => {
                        let value = match op.as_str() {
                            "+" => format!("({x}).wrapping_add({y})"),
                            "-" => format!("({x}).wrapping_sub({y})"),
                            "*" => format!("({x}).wrapping_mul({y})"),
                            _ => format!("({x})&({y})"),
                        };
                        self.temp(value, true, out)
                    }
                    ("quot" | "rem", Value::Word(x), Value::Word(y)) => {
                        let symbol = if op == "quot" { "/" } else { "%" };
                        self.temp(format!("if {y}==0 {{0}} else {{({x}){symbol}({y})}}"), true, out)
                    }
                    ("==" | "!=" | "<" | ">" | "<=" | ">=", Value::Word(x), Value::Word(y))
                    | ("==" | "!=" | "&&" | "||", Value::Bool(x), Value::Bool(y)) => {
                        self.temp(format!("({x}){op}({y})"), false, out)
                    }
                    _ => return Err("native maintained definition operator".into()),
                }
            }
        })
    }
}

/// A source value read through a borrowed place, as the projection encodes it.
fn input(p: &Program, projection: &Projection, t: &Type, place: &str, depth: usize) -> LangResult<Value> {
    if depth > 64 {
        return Err("native maintained codec depth".into());
    }
    Ok(match t {
        Type::U64 => Value::Word(format!("({place})")),
        Type::U32 => Value::Word(format!("(({place}) as u64)")),
        Type::I32 => Value::Word(format!("(({place}) as u32 as u64)")),
        Type::Bool => Value::Bool(format!("({place})")),
        Type::Unit => Value::Fields(0, vec![]),
        Type::Named(n) if p.records.contains_key(n) && !projection.recursive_records.contains_key(n) => Value::Fields(
            0,
            p.records[n]
                .iter()
                .map(|(f, t)| {
                    if crate::state_native::boxed_field(n, t, p) {
                        Ok(Value::Opaque)
                    } else {
                        input(p, projection, t, &format!("({place}).l_{f}"), depth + 1)
                    }
                })
                .collect::<LangResult<_>>()?,
        ),
        Type::Vector(t, n) => {
            Value::Fields(0, (0..*n).map(|i| input(p, projection, t, &format!("({place})[{i}]"), depth + 1)).collect::<LangResult<_>>()?)
        }
        _ => Value::Opaque,
    })
}

/// One maintained keep: its table and the emitted fold update functions.
pub(crate) struct View {
    pub keep: String,
    pub table: String,
    /// `u64` or `bool`.
    pub ty: &'static str,
    pub zero: String,
    /// Methods on `State`: `fn maintained_<i>_{insert,remove,replace}` for a
    /// group, `fn maintained_<i>_contribution` for an extremum.
    pub methods: String,
    /// A word extremum keeps the multiset of contributions instead of a total.
    pub extremum: Option<ink_core::maintained::Order>,
}
pub(crate) struct Views(pub Vec<View>);

pub(crate) fn views(module: &CheckedModule, checked: &CheckedViews) -> LangResult<Views> {
    let p = module.program();
    let projection = Projection::derive(module)?;
    let ds = checked.definition().reachable_executable_declarations()?;
    let var = |n: &str| Term::Var(n.into());
    let call = |f: &str, args: Vec<Term>| Term::Call { function: f.into(), arguments: args };
    let mut out = vec![];
    for (index, ((v, s), zero)) in checked.package().views.iter().zip(checked.subjects()).zip(checked.zeros()).enumerate() {
        let state = p.states.iter().find(|r| r.name == s.table).ok_or("maintained table")?;
        let Type::Table(key, row) = &state.ty else { return Err("maintained table type".into()) };
        let (ty, zero) = match (&s.result, zero) {
            (Sort::U64, Term::U64(n)) => ("u64", format!("{n}u64")),
            (Sort::Bool, Term::Bool(b)) => ("bool", b.to_string()),
            _ => return Err("maintained fold result sort".into()),
        };
        let contribution_id = v.contribution_choice.as_ref().map(|c| &c.function).unwrap_or(&v.contribution);
        let contribution = |r: &str| call(contribution_id, vec![var("key"), var(r)]);
        if let Some(extremum) = &v.extremum {
            let mut env = BTreeMap::new();
            env.insert("key".to_string(), input(p, &projection, key, "(*key)", 0)?);
            env.insert("row".to_string(), input(p, &projection, row, "(*row)", 0)?);
            let mut emit = Emit { ds: &ds, active: BTreeSet::new(), next: 0, work: 0 };
            let mut code = String::new();
            let value = emit.expr(&contribution("row"), &env, &mut code, 0)?;
            let Value::Word(result) = value else { return Err("maintained extremum contribution carrier".into()) };
            let methods = format!(
                "#[allow(unused_variables,unused_parens)] fn maintained_{index}_contribution(key:&{},row:&{})->u64{{{code}{result}}}\n",
                crate::state_native::ty(key)?, crate::state_native::ty(row)?
            );
            out.push(View { keep: s.keep.clone(), table: s.table.clone(), ty, zero, methods, extremum: Some(extremum.order) });
            continue;
        }
        let c = |a, b| call(&v.combine, vec![a, b]);
        let inv = |a| call(&v.inverse, vec![a]);
        let replacement = match &v.update {
            Some(u) => call(&u.function, vec![var("total"), contribution("old"), contribution("row")]),
            None => c(c(var("total"), inv(contribution("old"))), contribution("row")),
        };
        let candidates = [
            ("insert", vec!["key", "row"], c(var("total"), contribution("row"))),
            ("remove", vec!["key", "old"], c(var("total"), inv(contribution("old")))),
            ("replace", vec!["key", "old", "row"], replacement),
        ];
        let mut methods = String::new();
        for (name, params, body) in candidates {
            let mut env = BTreeMap::new();
            env.insert("total".to_string(), if ty == "u64" { Value::Word("total".into()) } else { Value::Bool("total".into()) });
            let mut signature = vec![format!("total:{ty}")];
            for param in &params {
                let source = if *param == "key" { key.as_ref() } else { row.as_ref() };
                env.insert(param.to_string(), input(p, &projection, source, &format!("(*{param})"), 0)?);
                signature.push(format!("{param}:&{}", crate::state_native::ty(source)?));
            }
            let mut emit = Emit { ds: &ds, active: BTreeSet::new(), next: 0, work: 0 };
            let mut code = String::new();
            let value = emit.expr(&body, &env, &mut code, 0)?;
            let result = value.scalar()?;
            writeln!(methods, "#[allow(unused_variables,unused_parens)] fn maintained_{index}_{name}({})->{ty}{{{code}{result}}}", signature.join(",")).unwrap();
        }
        out.push(View { keep: s.keep.clone(), table: s.table.clone(), ty, zero, methods, extremum: None });
    }
    Ok(Views(out))
}
