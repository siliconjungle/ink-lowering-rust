//! Type-specific borrowed constructor ABI for standalone C representation bodies.
//! No runtime definition registry, ground carrier or checker package is emitted.
use ink_core::{
    definition::CheckedDefinition,
    logic::{Declaration, Sort},
    LangResult,
};
use std::fmt::Write;
fn resolved(s: &Sort, id: &str) -> Sort {
    if *s == Sort::SelfType {
        Sort::Data(id.into())
    } else {
        s.clone()
    }
}

#[cfg(test)]
mod arena_tests {
    include!("constructor_arena.rs.txt");
    use std::{cell::Cell,rc::Rc};
    struct Item(Rc<Cell<usize>>,usize);
    impl Drop for Item {fn drop(&mut self){self.0.set(self.0.get()+1);}}
    #[test]
    fn stable_addresses_nested_marks_and_exact_destruction() {
        let drops=Rc::new(Cell::new(0));let mut arena=NativeArena::new();
        let first=arena.push(Item(drops.clone(),7));let outer=arena.mark();
        for i in 0..1024{arena.push(Item(drops.clone(),i));}
        assert_eq!(unsafe{(*first).1},7);
        arena.rewind(outer);assert_eq!(drops.get(),1024);
        assert_eq!(unsafe{(*first).1},7);
        assert_eq!(arena.chunks.len(),1);
        arena.rewind(0);assert_eq!(drops.get(),1025);
        let reused=arena.push(Item(drops.clone(),9));assert_eq!(first,reused);
        drop(arena);assert_eq!(drops.get(),1026);
    }
    #[test]
    fn a_large_spike_releases_excess_scratch() {
        let mut arena=NativeArena::new();for i in 0..30000{arena.push(i);}
        arena.rewind(0);assert_eq!(arena.chunks.len(),1);
        assert!(arena.chunks.capacity()<=4);
        let pointer=arena.chunks[0].as_ptr();
        for _ in 0..10{for i in 0..256{arena.push(i);}arena.rewind(0);assert_eq!(arena.chunks[0].as_ptr(),pointer);}
    }
}
fn input(s: &Sort) -> LangResult<String> {
    Ok(match s {
        Sort::Data(id) => format!("*const D_{id}"),
        _ => crate::definition_native::ty(s)?,
    })
}
pub(crate) fn emit(
    checked: &CheckedDefinition,
    queries: &std::collections::BTreeMap<String, Declaration>,
) -> LangResult<String> {
    let mut ds = checked.reachable_executable_declarations()?;
    ds.extend(queries.clone());
    let exports = checked
        .exports()
        .iter()
        .chain(queries.keys())
        .collect::<Vec<_>>();
    let mut out = String::from(
        "// Borrowed native typed objects: C never owns or packs the physical state.\n",
    );
    out.push_str(include_str!("constructor_arena.rs.txt"));
    out.push_str("thread_local!{\n");
    for (id, d) in &ds {
        if matches!(d, Declaration::Datatype { .. }) {
            writeln!(out,"static ARENA_{id}:std::cell::RefCell<NativeArena<D_{id}>>=const{{std::cell::RefCell::new(NativeArena::new())}};").unwrap();
        }
    }
    out.push_str("}\nstruct NativeCall{\n");
    for (id,d) in &ds {if matches!(d,Declaration::Datatype{..}){writeln!(out,"mark_{id}:usize,").unwrap();}}
    out.push_str("}\nimpl NativeCall{fn new()->Self{Self{\n");
    for (id,d) in &ds {if matches!(d,Declaration::Datatype{..}){writeln!(out,"mark_{id}:ARENA_{id}.with(|a|a.borrow().mark()),").unwrap();}}
    out.push_str("}}}\nimpl Drop for NativeCall{fn drop(&mut self){\n");
    for (id, d) in &ds {
        if matches!(d, Declaration::Datatype { .. }) {
            writeln!(out, "ARENA_{id}.with(|a|a.borrow_mut().rewind(self.mark_{id}));").unwrap();
        }
    }
    out.push_str("}}\n");
    for (id, d) in &ds {
        let Declaration::Datatype { constructors } = d else {
            continue;
        };
        let detachable = crate::definition_native::detachable_spine(constructors);
        writeln!(out,"#[no_mangle] unsafe extern \"C\" fn ink_rep_tag_{id}(v:*const D_{id})->u32{{match &*v{{").unwrap();
        for (i, c) in constructors.iter().enumerate() {
            writeln!(
                out,
                "D_{id}::C{i}{}=>{i},",
                if c.fields.is_empty() { "" } else { "(..)" }
            )
            .unwrap();
        }
        out.push_str("}}\n");
        for (i, c) in constructors.iter().enumerate() {
            let ss = c.fields.iter().map(|s| resolved(s, id)).collect::<Vec<_>>();
            let inputs = ss
                .iter()
                .enumerate()
                .map(|(j, s)| Ok(format!("a{j}:{}", input(s)?)))
                .collect::<LangResult<Vec<_>>>()?;
            let args = ss
                .iter()
                .enumerate()
                .map(|(j, s)| {
                    if matches!(s, Sort::Data(_)) {
                        let value = format!("std::sync::Arc::new((*a{j}).clone())");
                        if detachable && c.fields[j] == Sort::SelfType {
                            format!("Some({value})")
                        } else {
                            value
                        }
                    } else {
                        format!("a{j}")
                    }
                })
                .collect::<Vec<_>>();
            writeln!(out,"#[no_mangle] unsafe extern \"C\" fn ink_rep_new_{id}_{i}({})->*const D_{id}{{let value=D_{id}::C{i}{};ARENA_{id}.with(|a|a.borrow_mut().push(value))}}",inputs.join(","),if args.is_empty(){String::new()}else{format!("({})",args.join(","))}).unwrap();
            for (j, s) in ss.iter().enumerate() {
                let bs = (0..ss.len())
                    .map(|k| if k == j { "value" } else { "_" })
                    .collect::<Vec<_>>()
                    .join(",");
                let value = if detachable && c.fields[j] == Sort::SelfType {
                    "value.as_deref().expect(\"live recursive edge\") as *const _"
                } else if matches!(s, Sort::Data(_)) {
                    "value.as_ref() as *const _"
                } else {
                    "*value"
                };
                writeln!(out,"#[no_mangle] unsafe extern \"C\" fn ink_rep_get_{id}_{i}_{j}(v:*const D_{id})->{}{{match &*v{{D_{id}::C{i}({bs})=>{value},_=>unreachable!(\"literal C constructor projection\")}}}}",input(s)?).unwrap();
            }
        }
    }
    out.push_str("#[allow(improper_ctypes)] extern \"C\"{\n");
    for id in &exports {
        let id = *id;
        let target = checked.choices().get(id).unwrap_or(id);
        let Declaration::Function { params, result, .. } = &ds[target] else {
            return Err("foreign export function".into());
        };
        let inputs = params
            .iter()
            .enumerate()
            .map(|(i, (_, s))| Ok(format!("a{i}:{}", input(s)?)))
            .collect::<LangResult<Vec<_>>>()?;
        writeln!(
            out,
            "fn ink_rep_f_{id}({})->{};",
            inputs.join(","),
            input(result)?
        )
        .unwrap();
    }
    out.push_str("}\n");
    for id in &exports {
        let id = *id;
        let target = checked.choices().get(id).unwrap_or(id);
        let Declaration::Function { params, result, .. } = &ds[target] else {
            unreachable!()
        };
        let inputs = params
            .iter()
            .enumerate()
            .map(|(i, (_, s))| {
                Ok(format!(
                    "a{i}:{}{}",
                    if matches!(s, Sort::Data(_)) { "&" } else { "" },
                    crate::definition_native::ty(s)?
                ))
            })
            .collect::<LangResult<Vec<_>>>()?;
        let args = (0..params.len())
            .map(|i| format!("a{i}"))
            .collect::<Vec<_>>()
            .join(",");
        let value = if matches!(result, Sort::Data(_)) {
            "(*value).clone()"
        } else {
            "value"
        };
        let wrapper = format!("f_{id}");
        writeln!(out,"fn {wrapper}({})->{}{{let _call=NativeCall::new();let value=unsafe{{ink_rep_f_{id}({args})}};unsafe{{{value}}}}}",inputs.join(","),crate::definition_native::ty(result)?).unwrap();
    }
    Ok(out)
}
