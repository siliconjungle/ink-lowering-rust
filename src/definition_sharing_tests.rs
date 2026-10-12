use super::*;
use ink_core::{content::Lock, logic::Branch};

fn add(
    bundle: &mut library::Bundle,
    declaration: Declaration,
    dependencies: Vec<String>,
) -> String {
    let object = Object {
        schema: 1,
        semantics: library::SEMANTICS.into(),
        name: "generic-sharing-fixture".into(),
        dependencies,
        declaration,
    };
    let raw = serde_json::to_string(&object).unwrap();
    let id = format!("{:x}", Sha256::digest(raw.as_bytes()));
    bundle.lock.objects.push(id.clone());
    bundle.objects.insert(id.clone(), raw);
    id
}
fn construct(id: &str, args: Vec<Term>) -> Term {
    Term::Construct {
        datatype: id.into(),
        constructor: 0,
        arguments: args,
    }
}

#[test]
fn matched_owners_and_constant_templates_retain_exact_values_and_share_storage() {
    let mut bundle = library::Bundle {
        lock: Lock {
            schema: 1,
            semantics: library::SEMANTICS.into(),
            objects: vec![],
        },
        objects: BTreeMap::new(),
    };
    let leaf = add(
        &mut bundle,
        Declaration::Datatype {
            constructors: vec![Constructor {
                name: "Leaf".into(),
                fields: vec![Sort::U64],
            }],
        },
        vec![],
    );
    let pair = add(
        &mut bundle,
        Declaration::Datatype {
            constructors: vec![Constructor {
                name: "Pair".into(),
                fields: vec![Sort::Data(leaf.clone()), Sort::Data(leaf.clone())],
            }],
        },
        vec![leaf.clone()],
    );
    let rebuild = add(
        &mut bundle,
        Declaration::Function {
            params: vec![("input".into(), Sort::Data(pair.clone()))],
            result: Sort::Data(pair.clone()),
            recursive: None,
            body: Term::Match {
                scrutinee: Box::new(Term::Var("input".into())),
                branches: vec![Branch {
                    bindings: vec!["left".into(), "right".into()],
                    body: construct(
                        &pair,
                        vec![Term::Var("left".into()), Term::Var("right".into())],
                    ),
                }],
            },
        },
        vec![pair.clone()],
    );
    let template = add(
        &mut bundle,
        Declaration::Function {
            params: vec![],
            result: Sort::Data(pair.clone()),
            recursive: None,
            body: construct(
                &pair,
                vec![
                    construct(&leaf, vec![Term::U64(11)]),
                    construct(&leaf, vec![Term::U64(13)]),
                ],
            ),
        },
        vec![pair.clone(), leaf.clone()],
    );
    let checked =
        ink_core::definition::check(&bundle, &[rebuild.clone(), template.clone()], None).unwrap();
    let emitted = lower_typed_shared(&checked).unwrap();
    let directory = std::env::temp_dir().join(format!(
        "ink-generic-sharing-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    std::fs::create_dir(&directory).unwrap();
    struct Scratch(std::path::PathBuf);
    impl Drop for Scratch {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }
    let _scratch = Scratch(directory.clone());
    std::fs::write(directory.join("definition.rs"), emitted.source).unwrap();
    let driver = format!(
        r#"mod definition;use definition::*;use std::sync::Arc;
fn main(){{
 let left=Arc::new(D_{leaf}::C0(7));let right=Arc::new(D_{leaf}::C0(13));
 let original=D_{pair}::C0(left.clone(),right.clone());
 let rebuilt=f_{rebuild}(&original);assert_eq!(rebuilt,original);
 let D_{pair}::C0(a,b)=&rebuilt;assert!(Arc::ptr_eq(a,&left));assert!(Arc::ptr_eq(b,&right));
 assert_eq!(Arc::strong_count(&left),3);drop(original);drop(rebuilt);assert_eq!(Arc::strong_count(&left),1);
 let first=f_{template}();let second=f_{template}();assert_eq!(first,second);
 let(D_{pair}::C0(a,b),D_{pair}::C0(c,d))=(&first,&second);assert!(Arc::ptr_eq(a,c));assert!(Arc::ptr_eq(b,d));
 assert_eq!(**a,D_{leaf}::C0(11));assert_eq!(**b,D_{leaf}::C0(13));
}}
"#
    );
    std::fs::write(directory.join("main.rs"), driver).unwrap();
    let compiled = std::process::Command::new("rustc")
        .current_dir(&directory)
        .args(["--edition=2021", "-O", "main.rs", "-o", "check"])
        .output()
        .unwrap();
    assert!(
        compiled.status.success(),
        "{}",
        String::from_utf8_lossy(&compiled.stderr)
    );
    let result = std::process::Command::new(directory.join("check"))
        .output()
        .unwrap();
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
}

#[test]
fn database_product_spines_pack_mixed_lanes_and_retain_shared_tails() {
    let mut bundle = library::Bundle {
        lock: Lock {
            schema: 1,
            semantics: library::SEMANTICS.into(),
            objects: vec![],
        },
        objects: BTreeMap::new(),
    };
    let leaf = add(
        &mut bundle,
        Declaration::Datatype {
            constructors: vec![Constructor {
                name: "Leaf".into(),
                fields: vec![Sort::U64],
            }],
        },
        vec![],
    );
    let spine = add(
        &mut bundle,
        Declaration::Datatype {
            constructors: vec![
                Constructor {
                    name: "Empty".into(),
                    fields: vec![],
                },
                Constructor {
                    name: "Cell".into(),
                    fields: vec![
                        Sort::Bool,
                        Sort::U64,
                        Sort::Data(leaf.clone()),
                        Sort::SelfType,
                    ],
                },
            ],
        },
        vec![leaf.clone()],
    );
    let prepend = add(
        &mut bundle,
        Declaration::Function {
            params: vec![
                ("flag".into(), Sort::Bool),
                ("word".into(), Sort::U64),
                ("leaf".into(), Sort::Data(leaf.clone())),
                ("tail".into(), Sort::Data(spine.clone())),
            ],
            result: Sort::Data(spine.clone()),
            recursive: None,
            body: Term::Construct {
                datatype: spine.clone(),
                constructor: 1,
                arguments: vec![
                    Term::Var("flag".into()),
                    Term::Var("word".into()),
                    Term::Var("leaf".into()),
                    Term::Var("tail".into()),
                ],
            },
        },
        vec![leaf.clone(), spine.clone()],
    );
    let head = add(
        &mut bundle,
        Declaration::Function {
            params: vec![("xs".into(), Sort::Data(spine.clone()))],
            result: Sort::U64,
            recursive: None,
            body: Term::Match {
                scrutinee: Box::new(Term::Var("xs".into())),
                branches: vec![
                    Branch {
                        bindings: vec![],
                        body: Term::U64(0),
                    },
                    Branch {
                        bindings: vec!["flag".into(), "word".into(), "leaf".into(), "tail".into()],
                        body: Term::Var("word".into()),
                    },
                ],
            },
        },
        vec![spine.clone()],
    );
    let checked =
        ink_core::definition::check(&bundle, &[prepend.clone(), head.clone()], None).unwrap();
    let emitted = lower_typed_packed(&checked, &BTreeMap::new()).unwrap();
    let directory = std::env::temp_dir().join(format!("ink-product-packed-{}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();

    std::fs::write(directory.join("main.rs"),emitted.source+&format!(r#"
fn main(){{
 let leaf=D_{leaf}::C0(13);let mut xs=D_{spine}::C0;
 for i in 0..193u64{{xs=f_{prepend}(i%2==0,if i==100{{u64::MAX}}else{{i}},&leaf,&xs);}}
 let retained=xs.clone();let cells:Vec<_>=xs.as_view().cells().collect();assert_eq!(cells.len(),193);
 for(i,c)in cells.iter().enumerate(){{let n=192-i as u64;assert_eq!(c.c0,n%2==0);assert_eq!(c.c1,if n==100{{u64::MAX}}else{{n}});assert_eq!(*c.c2,leaf);}}
 assert!(std::sync::Arc::ptr_eq(&cells[0].c2,&retained.as_view().cells().next().unwrap().c2));assert_eq!(f_{head}(&xs),192);
 let tail=xs.as_view().view().unwrap().1.to_owned();let changed=f_{prepend}(false,777,&leaf,&tail);
 assert_eq!(f_{head}(&changed),777);assert_eq!(f_{head}(&retained),192);
 assert_eq!(tail.as_view().cells().count(),192);assert_eq!(retained.as_view().cells().count(),193);
}}
"#)).unwrap();
    let compiled = std::process::Command::new("rustc")
        .current_dir(&directory)
        .args(["--edition=2021", "-O", "main.rs", "-o", "check"])
        .output()
        .unwrap();
    assert!(
        compiled.status.success(),
        "{}",
        String::from_utf8_lossy(&compiled.stderr)
    );
    let result = std::process::Command::new(directory.join("check"))
        .output()
        .unwrap();
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    std::fs::remove_dir_all(directory).unwrap();
}
