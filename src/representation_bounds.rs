//! Bounded traversal of private immutable storage, without value serialization.
use ink_core::{definition::CheckedDefinition,logic::{Declaration,Sort},LangResult};
use std::fmt::Write;
pub(crate) fn emit(d:&CheckedDefinition,physical:&str)->LangResult<String>{
 // Match the datatype closure emitted by definition_native. Proof dependencies
 // remain checked, but may contain datatypes absent from selected executable code.
 let ds=d.reachable_executable_declarations()?;let mut out=String::from("enum Storage<'a>{Scalar,");
 for(id,decl)in &ds{if matches!(decl,Declaration::Datatype{..}){write!(out,"D_{id}(&'a D_{id}),").unwrap();}}
 out.push_str("}\nfn bounded_storage(root:Storage<'_>)->Result<(),&'static str>{let mut work=vec![(root,0usize)];let mut nodes=0;while let Some((value,depth))=work.pop(){nodes+=1;if nodes>100000||depth>8192{return Err(\"prepared storage resource limit\")}match value{Storage::Scalar=>{},");
 for(id,decl)in &ds{if let Declaration::Datatype{constructors}=decl{write!(out,"Storage::D_{id}(v)=>match v{{").unwrap();for(i,c)in constructors.iter().enumerate(){let names=(0..c.fields.len()).map(|i|format!("a{i}")).collect::<Vec<_>>();write!(out,"D_{id}::C{i}{}=>{{",if names.is_empty(){String::new()}else{format!("({})",names.join(","))}).unwrap();for(j,s)in c.fields.iter().enumerate(){let child=match s{Sort::SelfType=>format!("Storage::D_{id}(a{j}.as_ref())"),Sort::Data(id)=>format!("Storage::D_{id}(a{j}.as_ref())"),_=>"Storage::Scalar".into()};write!(out,"work.push(({child},depth+1));").unwrap();}out.push_str("},");}out.push_str("},");}}
 out.push_str("}}Ok(())}\n");
 let Declaration::Datatype{constructors}=&ds[physical]else{return Err("physical datatype".into())};write!(out,"fn same_storage(a:&D_{physical},b:&D_{physical})->bool{{match(a,b){{").unwrap();for(i,c)in constructors.iter().enumerate(){let names=|p:&str|(0..c.fields.len()).map(|j|format!("{p}{j}")).collect::<Vec<_>>();let args=|p:&str|if c.fields.is_empty(){String::new()}else{format!("({})",names(p).join(","))};let tests=c.fields.iter().enumerate().map(|(j,s)|if matches!(s,Sort::Data(_)|Sort::SelfType){format!("std::sync::Arc::ptr_eq(a{j},b{j})")}else{format!("a{j}==b{j}")}).collect::<Vec<_>>();write!(out,"(D_{physical}::C{i}{},D_{physical}::C{i}{})=>{},",args("a"),args("b"),if tests.is_empty(){"true".into()}else{tests.join("&&")}).unwrap();}out.push_str("_=>false}}\n");Ok(out)
}

#[cfg(test)]
mod tests {
 use super::*;
 use ink_core::{library::{Bundle,Object,SEMANTICS},knowledge::Lock,logic::{Constructor,Term}};
 use sha2::{Digest,Sha256};
 use std::{collections::BTreeMap,fs,process::Command};
 fn add(objects:&mut BTreeMap<String,String>,name:&str,dependencies:Vec<String>,declaration:Declaration)->String {
  let raw=serde_json::to_string(&Object{schema:1,semantics:SEMANTICS.into(),name:name.into(),dependencies,declaration}).unwrap();
  let id=format!("{:x}",Sha256::digest(raw.as_bytes()));objects.insert(id.clone(),raw);id
 }
 #[test]
 fn bounded_storage_uses_only_emitted_selected_datatypes_and_checks_live_children() {
  let mut objects=BTreeMap::new();
  let child=add(&mut objects,"child",vec![],Declaration::Datatype{constructors:vec![Constructor{name:"Word".into(),fields:vec![Sort::U64]}]});
  let live=add(&mut objects,"live",vec![child.clone()],Declaration::Datatype{constructors:vec![Constructor{name:"Leaf".into(),fields:vec![Sort::Data(child.clone())]},Constructor{name:"Next".into(),fields:vec![Sort::Data(child.clone()),Sort::SelfType]}]});
  let dead=add(&mut objects,"checked-but-not-executed",vec![child.clone()],Declaration::Datatype{constructors:vec![Constructor{name:"Unused".into(),fields:vec![Sort::Data(child.clone())]}]});
  let export=add(&mut objects,"identity",vec![live.clone()],Declaration::Function{params:vec![("state".into(),Sort::Data(live.clone()))],result:Sort::Data(live.clone()),body:Term::Var("state".into()),recursive:None});
  let bundle=Bundle{lock:Lock{schema:1,semantics:SEMANTICS.into(),objects:vec![export.clone(),dead.clone()]},objects};
  let checked=ink_core::definition::check(&bundle,&[export.clone()],None).unwrap();
  assert!(checked.executable_declarations().unwrap().contains_key(&dead));
  let emitted=crate::definition_native::lower_shared(&checked).unwrap();
  assert!(!emitted.receipt.executable_closure.contains(&dead));
  let bounds=emit(&checked,&live).unwrap();assert!(!bounds.contains(&format!("D_{dead}")));
  let source=format!("{}\n{}\nfn main(){{\nlet first=D_{live}::C0(std::sync::Arc::new(D_{child}::C0(7)));\nbounded_storage(Storage::D_{live}(&first)).unwrap();\nlet copy=f_{export}(&first);assert!(same_storage(&first,&copy));\nlet changed=D_{live}::C0(std::sync::Arc::new(D_{child}::C0(9)));assert!(!same_storage(&first,&changed));\nlet mut deep=first;for _ in 0..8193{{deep=D_{live}::C1(std::sync::Arc::new(D_{child}::C0(1)),std::sync::Arc::new(deep));}}\nassert_eq!(bounded_storage(Storage::D_{live}(&deep)),Err(\"prepared storage resource limit\"));std::mem::forget(deep);\n}}",emitted.source,bounds);
  let root=std::env::temp_dir().join(format!("ink-emitted-storage-{}",std::process::id()));fs::create_dir_all(&root).unwrap();let input=root.join("fixture.rs");let executable=root.join("fixture");fs::write(&input,source).unwrap();
  let compile=Command::new("rustc").args(["--edition=2021","--crate-name","storage_fixture"]).arg(&input).arg("-o").arg(&executable).output().unwrap();assert!(compile.status.success(),"{}",String::from_utf8_lossy(&compile.stderr));
  assert!(Command::new(&executable).status().unwrap().success());fs::remove_dir_all(root).unwrap();
 }
}
