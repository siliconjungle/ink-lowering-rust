use ink_core::{knowledge::Lock, library::{self, Object}, logic::{Constructor, Declaration, Sort, Term}};
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;

#[test]
fn cached_subtree_measures_preserve_limits_and_release_dead_owners() {
    let mut bundle = library::Bundle {
        lock: Lock { schema: 1, semantics: library::SEMANTICS.into(), objects: vec![] },
        objects: BTreeMap::new(),
    };
    let mut add = |declaration, dependencies| {
        let object = Object { schema: 1, semantics: library::SEMANTICS.into(), name: "storage-measure-fixture".into(), dependencies, declaration };
        let raw = serde_json::to_string(&object).unwrap();
        let id = format!("{:x}", Sha256::digest(raw.as_bytes()));
        bundle.lock.objects.push(id.clone()); bundle.objects.insert(id.clone(), raw); id
    };
    let rows = add(Declaration::Datatype { constructors: vec![
        Constructor { name: "Nil".into(), fields: vec![] },
        Constructor { name: "Cons".into(), fields: vec![Sort::U64, Sort::SelfType] },
    ] }, vec![]);
    let tree = add(Declaration::Datatype { constructors: vec![
        Constructor { name: "Tip".into(), fields: vec![] },
        Constructor { name: "Pair".into(), fields: vec![Sort::SelfType, Sort::SelfType] },
    ] }, vec![]);
    let physical = add(Declaration::Datatype { constructors: vec![
        Constructor { name: "Storage".into(), fields: vec![Sort::Data(rows.clone()), Sort::Data(tree.clone())] },
    ] }, vec![rows.clone(), tree.clone()]);
    let identity = add(Declaration::Function {
        params: vec![("value".into(), Sort::Data(physical.clone()))], result: Sort::Data(physical.clone()),
        recursive: None, body: Term::Var("value".into()),
    }, vec![physical.clone()]);
    add(Declaration::Datatype { constructors: vec![Constructor { name: "ProofOnly".into(), fields: vec![] }] }, vec![]);
    let checked = ink_core::definition::check(&bundle, &[identity], None).unwrap();
    let mut source = crate::definition_native::lower_typed_shared(&checked, &std::collections::BTreeMap::new()).unwrap().source;
    source.push_str(&super::emit(&checked, Some(&physical)).unwrap());
    let scalar=super::emit(&checked,None).unwrap();
    assert!(scalar.contains("fn bounded_storage("));assert!(!scalar.contains("fn same_storage("));
    source.push_str(&format!(r#"
fn main() {{
 use std::sync::Arc;
 let mut rows=Arc::new(D_{rows}::C0);
 for i in 0..1000 {{rows=Arc::new(D_{rows}::C1(i,rows));}}
 let initial=D_{physical}::C0(rows.clone(),Arc::new(D_{tree}::C0));
 bounded_storage(Storage::D_{physical}(&initial)).unwrap();
 STORAGE_MEASURES.with(|c|assert!(c.borrow().visits>1000));
 let changed=D_{physical}::C0(Arc::new(D_{rows}::C1(1001,rows.clone())),Arc::new(D_{tree}::C0));
 bounded_storage(Storage::D_{physical}(&changed)).unwrap();
 STORAGE_MEASURES.with(|c|{{let c=c.borrow();assert!(c.visits<10);assert!(c.hits>0);}});
 // A weak cache must neither keep values alive nor permit in-place mutation.
 assert!(Arc::get_mut(&mut rows).is_none());
 let mut fresh=Arc::new(D_{rows}::C0);
 bounded_storage(Storage::A_{rows}(&fresh)).unwrap();
 assert_eq!(Arc::strong_count(&fresh),1);assert!(Arc::get_mut(&mut fresh).is_none());
 let weak=Arc::downgrade(&fresh);
 let old_ptr=Arc::as_ptr(&fresh);
 *Arc::make_mut(&mut fresh)=D_{rows}::C1(7,Arc::new(D_{rows}::C0));
 assert_ne!(old_ptr,Arc::as_ptr(&fresh));assert!(weak.upgrade().is_none());
 bounded_storage(Storage::A_{rows}(&fresh)).unwrap();
 STORAGE_MEASURES.with(|c|{{let c=c.borrow();let key=({rows_index},Arc::as_ptr(&fresh)as usize);assert_eq!(c.entries[&key].measure.nodes,3);}});
 // A shared tree is tiny physically but exceeds the original expanded limit.
 let mut tree=Arc::new(D_{tree}::C0);
 for _ in 0..15 {{tree=Arc::new(D_{tree}::C1(tree.clone(),tree));}}
 bounded_storage(Storage::A_{tree}(&tree)).unwrap();
 let oversized=D_{tree}::C1(tree.clone(),tree.clone());
 assert!(bounded_storage(Storage::D_{tree}(&oversized)).is_err());
 let leaf=D_{tree}::C0;
 // Depth is independent of the memoised subtree's starting position.
 let mut deep=Arc::new(D_{rows}::C0);
 for i in 0..8192 {{deep=Arc::new(D_{rows}::C1(i,deep));}}
 bounded_storage(Storage::A_{rows}(&deep)).unwrap();
 let too_deep=D_{physical}::C0(deep.clone(),Arc::new(leaf));
 assert!(bounded_storage(Storage::D_{physical}(&too_deep)).is_err());
 STORAGE_MEASURES.with(|c|c.borrow_mut().generation=u32::MAX);
 bounded_storage(Storage::D_{physical}(&changed)).unwrap();
 STORAGE_MEASURES.with(|c|{{let c=c.borrow();assert_eq!(c.generation,1);assert!(c.entries.len()<=MeasureCache::LIMIT);}});
 for i in 0..(MeasureCache::LIMIT*2) {{let v=Arc::new(D_{rows}::C1(i as u64,Arc::new(D_{rows}::C0)));bounded_storage(Storage::A_{rows}(&v)).unwrap();}}
 STORAGE_MEASURES.with(|c|{{let c=c.borrow();assert!(c.entries.len()<=MeasureCache::LIMIT);assert!(c.entries.values().filter(|e|e.owner.live()).count()<1100);}});
 // Generated datatypes already reclaim recursive owners iteratively.
 STORAGE_MEASURES.with(|c|c.borrow_mut().entries.clear());
 drop(initial);drop(changed);drop(rows);drop(too_deep);
 drop(deep);
}}
"#, rows_index=checked.reachable_executable_declarations().unwrap().iter().filter(|(_,d)|matches!(d,Declaration::Datatype{..})).position(|(id,_)|id==&rows).unwrap()));
    let directory=std::env::temp_dir().join(format!("ink-storage-measures-{}",std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    std::fs::write(directory.join("main.rs"),source).unwrap();
    let built=std::process::Command::new("rustc").current_dir(&directory).args(["--edition=2021","main.rs","-o","check"]).output().unwrap();
    assert!(built.status.success(),"{}",String::from_utf8_lossy(&built.stderr));
    let run=std::process::Command::new(directory.join("check")).output().unwrap();
    assert!(run.status.success(),"{}",String::from_utf8_lossy(&run.stderr));
    std::fs::remove_dir_all(directory).unwrap();
}
