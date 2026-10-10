//! Literal pure-expression Rust lowering for functions embedded in stateful
//! projects. Shares contextual typing with the C and GPU backends.
use crate::{check, syntax::*, LangResult};
struct Emitter<'a> {
    p: &'a Program,
    next: usize,
}
impl Emitter<'_> {
    fn fresh(&mut self) -> String {
        let n = format!("ink_pure_{}", self.next);
        self.next += 1;
        n
    }
    fn expr(&mut self, e: &Expr, env: &check::Env, want: Option<&Type>) -> LangResult<String> {
        let t = check::infer_context(e, env, self.p, want)?;
        Ok(match e {
            Expr::Num(n) => format!("{n}{}", if t == Type::U32 { "u32" } else { "u64" }),
            Expr::Let(n, annotation, x, b) => {
                let xt = check::infer_context(x, env, self.p, annotation.as_deref())?;
                let value = self.expr(x, env, Some(&xt))?;
                let mut local = env.clone();
                local.insert(n.clone(), xt);
                let body = self.expr(b, &local, Some(&t))?;
                format!("{{let l_{n}={value};{body}}}")
            }
            Expr::Field(x, n) => format!("({}).l_{n}.clone()", self.expr(x, env, None)?),
            Expr::Record(n, fields) => {
                let schema = self.p.records[n].clone();
                let mut values = Vec::new();
                for (k, t) in &schema {
                    let e = &fields
                        .iter()
                        .find(|(f, _)| f == k)
                        .ok_or("missing record field")?
                        .1;
                    values.push(format!("l_{k}:{}", self.expr(e, env, Some(t))?));
                }
                format!("l_{n}{{{}}}", values.join(","))
            }
            Expr::Bool(b) => b.to_string(),
            Expr::Var(n) => format!("l_{n}.clone()"),
            Expr::Binary(op, a, b) => {
                let operand = if check::is_word(&t) {
                    Some(t.clone())
                } else {
                    check::hint(a, env, self.p).or_else(|| check::hint(b, env, self.p))
                };
                let a = self.expr(a, env, operand.as_ref())?;
                let b = self.expr(b, env, operand.as_ref())?;
                match op.as_str() {
                    "+" => format!("({a}).wrapping_add({b})"),
                    "-" => format!("({a}).wrapping_sub({b})"),
                    "*" => format!("({a}).wrapping_mul({b})"),
                    _ => format!("(({a}) {op} ({b}))"),
                }
            }
            Expr::Call(n, args) if n == "choose" => format!(
                "if {} {{{}}} else {{{}}}",
                self.expr(&args[0], env, Some(&Type::Bool))?,
                self.expr(&args[1], env, Some(&t))?,
                self.expr(&args[2], env, Some(&t))?
            ),
            Expr::Call(n, args) if n == "sum" || n == "count" => {
                let list_want = if n == "sum" {
                    Some(Type::List(Box::new(t.clone())))
                } else {
                    None
                };
                let xs = self.expr(&args[0], env, list_want.as_ref())?;
                if n == "count" {
                    format!("(({xs}).len() as u64)")
                } else {
                    format!("({xs}).into_iter().fold(0{}, |ink_acc,ink_value|ink_acc.wrapping_add(ink_value))",if t==Type::U32 {"u32"}else{"u64"})
                }
            }
            Expr::Call(n, args) if n == "foldr" => {
                let xs = self.expr(&args[0], env, None)?;
                let initial = self.expr(&args[1], env, Some(&t))?;
                let Expr::Lambda(item, inner) = &args[2] else {
                    return Err("foldr lambda".into());
                };
                let Expr::Lambda(rest, body) = inner.as_ref() else {
                    return Err("foldr nested lambda".into());
                };
                let mut local = env.clone();
                local.insert(item.clone(), t.clone());
                local.insert(rest.clone(), t.clone());
                let body = self.expr(body, &local, Some(&t))?;
                let acc = self.fresh();
                let value = self.fresh();
                format!("({xs}).into_iter().rev().fold({initial}, |{acc},{value}|{{let l_{item}={value};let l_{rest}={acc};{body}}})")
            }
            Expr::Call(n, args) => {
                let f = self
                    .p
                    .functions
                    .iter()
                    .find(|f| &f.name == n)
                    .ok_or("unknown pure function")?
                    .clone();
                let mut bindings = String::new();
                let mut names = Vec::new();
                for (e, (_, t)) in args.iter().zip(&f.params) {
                    let value = self.expr(e, env, Some(t))?;
                    let name = self.fresh();
                    bindings.push_str(&format!("let {name}={value};"));
                    names.push(name);
                }
                format!("{{{bindings}self.function_l_{n}({})}}", names.join(","))
            }
            Expr::Method(xs, n, args) if n == "concat" => {
                // Borrow variable operands directly. Computed operands are evaluated
                // once and their temporaries live through the two result copies.
                let left = if let Expr::Var(n) = xs.as_ref() {
                    format!("&l_{n}")
                } else {
                    format!("&({})", self.expr(xs, env, Some(&t))?)
                };
                let right = if let Expr::Var(n) = &args[0] {
                    format!("&l_{n}")
                } else {
                    format!("&({})", self.expr(&args[0], env, Some(&t))?)
                };
                let a = self.fresh();
                let b = self.fresh();
                let out = self.fresh();
                format!("{{let {a}={left};let {b}={right};let mut {out}=Vec::with_capacity({a}.len().checked_add({b}.len()).expect(\"concat allocation size overflow\"));{out}.extend_from_slice({a});{out}.extend_from_slice({b});{out}}}")
            }
            Expr::Method(xs, n, args) => {
                if !["map", "filter"].contains(&n.as_str()) {
                    return Err(
                        "new compute collection operations currently use the pure compute backend"
                            .into(),
                    );
                }
                let context = if n == "filter" { Some(&t) } else { None };
                let Type::List(inner) = check::infer_context(xs, env, self.p, context)? else {
                    return Err("expected list".into());
                };
                let receiver = self.expr(xs, env, context)?;
                let Expr::Lambda(var, body) = &args[0] else {
                    return Err("missing lambda".into());
                };
                let mut local = env.clone();
                local.insert(var.clone(), *inner);
                let Type::List(output) = &t else {
                    return Err("expected list result".into());
                };
                let body = self.expr(
                    body,
                    &local,
                    Some(if n == "filter" { &Type::Bool } else { output }),
                )?;
                if n == "map" {
                    format!("({receiver}).into_iter().map(|l_{var}|{body}).collect::<Vec<_>>()",)
                } else {
                    format!("({receiver}).into_iter().filter(|ink_ref|{{let l_{var}=(*ink_ref).clone();{body}}}).collect::<Vec<_>>()")
                }
            }
            _ => return Err("unsupported pure Rust expression".into()),
        })
    }
}
pub fn body(p: &Program, f: &Function) -> LangResult<String> {
    Emitter { p, next: 0 }.expr(&f.body, &check::params_env(&f.params)?, Some(&f.result))
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
