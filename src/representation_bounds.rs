//! Exact expanded size/depth of immutable private storage, with bounded weak
//! identity caches. Every shared occurrence contributes its full logical size.
use ink_core::{definition::CheckedDefinition, logic::{Declaration, Sort}, LangResult};
use std::fmt::Write;
pub(crate) fn emit(d: &CheckedDefinition, physical: Option<&str>) -> LangResult<String> {
    // Proof bundles can also contain datatypes belonging only to another
    // representation. Match the literal emitter's selected executable graph.
    let ds = d.reachable_executable_declarations()?;
    let mut out = String::from("enum Storage<'a>{Scalar,");
    let ids = ds.iter().filter_map(|(id, decl)| matches!(decl, Declaration::Datatype { .. }).then_some(id)).collect::<Vec<_>>();
    for id in &ids {
        writeln!(out, "D_{id}(&'a D_{id}),A_{id}(&'a std::sync::Arc<D_{id}>),").unwrap();
    }
    out.push_str("}\nenum WeakStorage{");
    for id in &ids { writeln!(out, "D_{id}(std::sync::Weak<D_{id}>),").unwrap(); }
    out.push_str("}\nimpl WeakStorage{fn live(&self)->bool{match self{");
    for id in &ids { writeln!(out, "Self::D_{id}(v)=>v.strong_count()!=0,").unwrap(); }
    out.push_str("}}}\n");
    out.push_str(include_str!("representation_measure_cache.rs.txt"));
    out.push_str("fn bounded_storage(root:Storage<'_>)->Result<(),&'static str>{STORAGE_MEASURES.with(|cell|{let mut cache=cell.borrow_mut();cache.begin();enum Work<'a>{Visit(Storage<'a>,usize),Build(usize,Option<((usize,usize),WeakStorage)>)}let mut work=vec![Work::Visit(root,0)];let mut measures:Vec<StorageMeasure>=vec![];let mut nodes=0usize;while let Some(frame)=work.pop(){match frame{Work::Build(arity,owner)=>{let start=measures.len()-arity;let measure=StorageMeasure{nodes:measures[start..].iter().fold(1usize,|n,m|n.saturating_add(m.nodes)),depth:measures[start..].iter().map(|m|m.depth.saturating_add(1)).max().unwrap_or(0)};measures.truncate(start);if let Some((key,owner))=owner{cache.insert(key,owner,measure);}measures.push(measure);},Work::Visit(value,depth)=>{cache.visits+=1;let(owner,value)=match value{");
    for (index, id) in ids.iter().enumerate() {
        writeln!(out, "Storage::A_{id}(v)=>{{let key=({index}usize,std::sync::Arc::as_ptr(v) as usize);if let Some(measure)=cache.get(key){{nodes=nodes.saturating_add(measure.nodes);if nodes>100000||depth.saturating_add(measure.depth)>8192{{return Err(\"prepared storage resource limit\");}}measures.push(measure);continue;}}(Some((key,WeakStorage::D_{id}(std::sync::Arc::downgrade(v)))),Storage::D_{id}(v.as_ref()))}},").unwrap();
    }
    out.push_str("value=>(None,value),};nodes=nodes.saturating_add(1);if nodes>100000||depth>8192{return Err(\"prepared storage resource limit\");}match value{Storage::Scalar=>measures.push(StorageMeasure{nodes:1,depth:0}),");
    for id in &ids {
        let Declaration::Datatype { constructors } = &ds[*id] else { unreachable!() };
        writeln!(out, "Storage::D_{id}(v)=>match v{{").unwrap();
        for (i, c) in constructors.iter().enumerate() {
            let names = (0..c.fields.len()).map(|i| format!("a{i}")).collect::<Vec<_>>();
            let args = if names.is_empty() { String::new() } else { format!("({})", names.join(",")) };
            writeln!(out, "D_{id}::C{i}{args}=>{{work.push(Work::Build({},owner));", c.fields.len()).unwrap();
            for (j, sort) in c.fields.iter().enumerate().rev() {
                let child = match sort {
                    Sort::SelfType => format!("Storage::A_{id}(a{j})"),
                    Sort::Data(id) => format!("Storage::A_{id}(a{j})"),
                    _ => "Storage::Scalar".into(),
                };
                writeln!(out, "work.push(Work::Visit({child},depth+1));").unwrap();
            }
            out.push_str("},");
        }
        out.push_str("},");
        writeln!(out, "Storage::A_{id}(_)=>unreachable!(),").unwrap();
    }
    out.push_str("}}}}debug_assert_eq!(measures.len(),1);Ok(())})}\n");
    let Some(physical)=physical else{return Ok(out);};
    let Declaration::Datatype { constructors } = &ds[physical] else { return Err("physical datatype".into()) };
    write!(out, "fn same_storage(a:&D_{physical},b:&D_{physical})->bool{{match(a,b){{").unwrap();
    for (i, c) in constructors.iter().enumerate() {
        let names = |p: &str| (0..c.fields.len()).map(|j| format!("{p}{j}")).collect::<Vec<_>>();
        let args = |p: &str| if c.fields.is_empty() { String::new() } else { format!("({})", names(p).join(",")) };
        let tests = c.fields.iter().enumerate().map(|(j,s)| if matches!(s,Sort::Data(_)|Sort::SelfType) { format!("std::sync::Arc::ptr_eq(a{j},b{j})") } else { format!("a{j}==b{j}") }).collect::<Vec<_>>();
        write!(out, "(D_{physical}::C{i}{},D_{physical}::C{i}{})=>{},", args("a"), args("b"), if tests.is_empty() { "true".into() } else { tests.join("&&") }).unwrap();
    }
    out.push_str("_=>false}}\n");
    Ok(out)
}

#[cfg(test)]
#[path = "representation_bounds_tests.rs"]
mod tests;
