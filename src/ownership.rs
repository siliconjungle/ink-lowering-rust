//! Lexical ownership facts for the stateful Rust lowering.
//!
//! These are properties of the source text only (no optimisation knowledge):
//! how many times each local is still read, which reads sit inside closures,
//! which names are bound more than once, and whether a statement can take
//! `&mut self` in the generated code. The emitter uses them to move a local at
//! its final read instead of cloning it, and to keep a table row borrowed
//! until the first statement that could mutate the state.
use crate::syntax::*;
use std::collections::BTreeMap;

/// A use count that never reaches zero: the variable is never moved.
pub const NEVER: usize = usize::MAX / 4;

#[derive(Default)]
pub struct Uses {
    /// Remaining reads of a whole local (`x`) or of one of its fields (`x.f`).
    pub var: BTreeMap<String, usize>,
    /// Remaining reads of `x.f` only.
    pub field: BTreeMap<(String, String), usize>,
    /// Remaining whole-value reads of `x` (not under a field access).
    pub whole: BTreeMap<String, usize>,
}

fn bump(m: &mut BTreeMap<String, usize>, n: &str, by: usize) {
    let e = m.entry(n.to_owned()).or_insert(0);
    *e = e.saturating_add(by).min(NEVER);
}

impl Uses {
    pub fn of_block(p: &Program, stmts: &[Statement]) -> Self {
        let mut u = Self::default();
        for s in stmts {
            u.stmt(p, s, 1);
        }
        u
    }
    fn stmt(&mut self, p: &Program, s: &Statement, by: usize) {
        match s {
            Statement::Let(_, _, e) | Statement::Return(e) | Statement::Emit(_, e) => {
                self.expr(p, e, by)
            }
            Statement::Expr(e) => self.expr(p, e, by),
            Statement::If(c, a, b) => {
                self.expr(p, c, by);
                for s in a.iter().chain(b) {
                    self.stmt(p, s, by);
                }
            }
        }
    }
    fn expr(&mut self, p: &Program, e: &Expr, by: usize) {
        match e {
            Expr::Var(n) => {
                bump(&mut self.var, n, by);
                bump(&mut self.whole, n, by);
            }
            Expr::Field(base, f) => match base.as_ref() {
                Expr::Var(n) if p.enums.contains_key(n) => {}
                Expr::Var(n) => {
                    bump(&mut self.var, n, by);
                    let e = self.field.entry((n.clone(), f.clone())).or_insert(0);
                    *e = e.saturating_add(by).min(NEVER);
                }
                other => self.expr(p, other, by),
            },
            // A closure body can run any number of times: its reads never move.
            Expr::Lambda(_, body) => self.expr(p, body, NEVER),
            Expr::Binary(_, a, b) => {
                self.expr(p, a, by);
                self.expr(p, b, by)
            }
            Expr::Call(_, args) => args.iter().for_each(|a| self.expr(p, a, by)),
            Expr::Method(base, _, args) => {
                self.expr(p, base, by);
                args.iter().for_each(|a| self.expr(p, a, by))
            }
            Expr::Record(_, fs) => fs.iter().for_each(|(_, e)| self.expr(p, e, by)),
            Expr::Try(e) | Expr::Neg(e) => self.expr(p, e, by),
            Expr::Let(_, _, a, b) => {
                self.expr(p, a, by);
                self.expr(p, b, by)
            }
            _ => {}
        }
    }
}

/// Names bound by a parameter, `let`, or closure parameter anywhere in the
/// body, with their binding counts. A name bound twice is never moved or
/// borrowed, so shadowing cannot confuse the counts above.
pub fn binders(params: &[(String, Type)], stmts: &[Statement]) -> BTreeMap<String, usize> {
    fn stmt(s: &Statement, out: &mut BTreeMap<String, usize>) {
        match s {
            Statement::Let(n, _, e) => {
                bump(out, n, 1);
                expr(e, out)
            }
            Statement::Return(e) | Statement::Emit(_, e) | Statement::Expr(e) => expr(e, out),
            Statement::If(c, a, b) => {
                expr(c, out);
                a.iter().chain(b).for_each(|s| stmt(s, out))
            }
        }
    }
    fn expr(e: &Expr, out: &mut BTreeMap<String, usize>) {
        match e {
            Expr::Lambda(n, body) => {
                bump(out, n, 1);
                expr(body, out)
            }
            Expr::Let(n, _, a, b) => {
                bump(out, n, 1);
                expr(a, out);
                expr(b, out)
            }
            Expr::Binary(_, a, b) => {
                expr(a, out);
                expr(b, out)
            }
            Expr::Call(_, args) => args.iter().for_each(|a| expr(a, out)),
            Expr::Method(base, _, args) => {
                expr(base, out);
                args.iter().for_each(|a| expr(a, out))
            }
            Expr::Record(_, fs) => fs.iter().for_each(|(_, e)| expr(e, out)),
            Expr::Try(e) | Expr::Neg(e) | Expr::Field(e, _) => expr(e, out),
            _ => {}
        }
    }
    let mut out = BTreeMap::new();
    for (n, _) in params {
        bump(&mut out, n, 1);
    }
    stmts.iter().for_each(|s| stmt(s, &mut out));
    out
}

/// Whether evaluating this statement can call a generated method taking
/// `&mut self`: a table write, an emitted event, a change/function call, or a
/// derived-value read. Shared row borrows must end before such a statement.
pub fn mutates_state(p: &Program, s: &Statement) -> bool {
    match s {
        Statement::Emit(..) => true,
        Statement::Let(_, _, e) | Statement::Return(e) | Statement::Expr(e) => {
            expr_mutates_state(p, e)
        }
        Statement::If(c, a, b) => {
            expr_mutates_state(p, c) || a.iter().chain(b).any(|s| mutates_state(p, s))
        }
    }
}

pub fn expr_mutates_state(p: &Program, e: &Expr) -> bool {
    let root = |n: &str| p.states.iter().any(|s| s.name == n);
    match e {
        Expr::Var(n) => p.keeps.iter().any(|k| &k.name == n),
        Expr::Method(base, m, args) => {
            let write = matches!(base.as_ref(), Expr::Var(r) if root(r))
                && !matches!(m.as_str(), "get" | "contains" | "values" | "keys" | "intersect_keys" | "shared_keys" | "sum_by" | "count_where");
            write || expr_mutates_state(p, base) || args.iter().any(|a| expr_mutates_state(p, a))
        }
        Expr::Call(n, args) => {
            p.actions.iter().any(|a| &a.name == n)
                || p.functions.iter().any(|f| &f.name == n)
                || args.iter().any(|a| expr_mutates_state(p, a))
        }
        Expr::Binary(_, a, b) | Expr::Let(_, _, a, b) => {
            expr_mutates_state(p, a) || expr_mutates_state(p, b)
        }
        Expr::Record(_, fs) => fs.iter().any(|(_, e)| expr_mutates_state(p, e)),
        Expr::Try(e) | Expr::Neg(e) | Expr::Field(e, _) | Expr::Lambda(_, e) => {
            expr_mutates_state(p, e)
        }
        _ => false,
    }
}
