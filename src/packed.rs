//! Literal Rust CPU adapters for the scalar and packed GPU host ABIs.
//! Layout conversion preserves raw float bits; source functions use the normal
//! typed emitter. No evaluator or C compiler is involved.
use ink_core::{core::CheckedModule, syntax::*, LangResult};

fn read(p: &Program, t: &Type) -> LangResult<String> {
    let word = "{let v=unsafe{input.add(cursor).read_unaligned()};cursor+=1;v}";
    Ok(match t {
        Type::U32 => word.into(),
        Type::I32 => format!("({word}) as i32"),
        Type::Bool => format!("({word})!=0"),
        Type::F32 => format!("f32::from_bits({word})"),
        Type::F64 => format!("{{let lo={word};let hi={word};f64::from_bits(u64::from(lo)|(u64::from(hi)<<32))}}"),
        Type::U64 => format!("{{let lo={word};let hi={word};u64::from(lo)|(u64::from(hi)<<32)}}"),
        Type::Vector(t, n) => format!("std::array::from_fn::<_,{n},_>(|_|{})", read(p, t)?),
        Type::Named(n) => format!(
            "l_{n}{{{}}}",
            p.records
                .get(n)
                .ok_or("packed ABI requires a fixed record")?
                .iter()
                .map(|(n, t)| Ok(format!("l_{n}:{}", read(p, t)?)))
                .collect::<LangResult<Vec<_>>>()?
                .join(",")
        ),
        _ => return Err("unsupported packed CPU element".into()),
    })
}
fn write(p: &Program, t: &Type, v: &str) -> LangResult<String> {
    Ok(match t {
        Type::U32 | Type::I32 | Type::Bool => format!("words.push(({v}) as u32);"),
        Type::F32 => format!("words.push(({v}).to_bits());"),
        Type::F64 => format!("{{let bits=({v}).to_bits();words.push(bits as u32);words.push((bits>>32)as u32);}}"),
        Type::U64 => format!("words.push(({v}) as u32);words.push((({v})>>32) as u32);"),
        Type::Vector(t, _) | Type::List(t) => {
            format!("for item in ({v}).iter(){{{}}}", write(p, t, "*item")?)
        }
        Type::Named(n) => p
            .records
            .get(n)
            .ok_or("packed ABI requires a fixed record")?
            .iter()
            .map(|(n, t)| write(p, t, &format!("({v}).l_{n}")))
            .collect::<LangResult<Vec<_>>>()?
            .join(""),
        _ => return Err("unsupported packed CPU result".into()),
    })
}
pub fn lower(module: &CheckedModule, packed: bool) -> LangResult<String> {
    lower_filtered(module, packed, None)
}
/// Expose one checked entry through the packed host ABI. Typed helper bodies
/// remain in the full program; only actual ingress/egress needs packed transport.
/// Any entry precondition callback retains its original function index/export.
pub fn lower_entry(module: &CheckedModule, packed: bool, entry: &str) -> LangResult<String> {
    lower_filtered(module, packed, Some(entry))
}
fn lower_filtered(module: &CheckedModule, packed: bool, entry: Option<&str>) -> LangResult<String> {
    let p = module.pure_program()?;
    if entry.is_some_and(|name| !p.functions.iter().any(|f| f.name == name)) {
        return Err("unknown packed CPU entry function".into());
    }
    let selected = |name: &str| entry.map_or(true, |root| name == root ||
        p.contracts.precondition_checks.get(root).is_some_and(|guard| guard == name));
    // The shared descriptor rejects recursive or variable-width elements before
    // either literal reader/writer expands their record fields.
    for f in p.functions.iter().filter(|f| selected(&f.name)) {
        for t in f.params.iter().map(|(_, t)| t).chain([&f.result]) {
            ink_abi::packed_width(&ink_abi::describe(t, &p.records, &p.enums, &p.ids)?)?;
        }
    }
    let mut out = crate::state_native::emit(p)?;
    out.push_str(include_str!("packed-runtime.rs.txt"));
    // A packed fallback has no JSON worker import. Re-enter its checked callback
    // in the existing nested-worker scope so recursive parallel calls execute
    // locally with the same ordered value semantics.
    out.push_str("#[cfg(target_arch=\"wasm32\")] fn __ink_parallel_host(mut task:Json)->Result<Json,String>{task[\"start\"]=json!(0u32);State::new().parallel_worker(&task)}\n");
    out.push_str("unsafe fn ink_packed_result(function:u32,data:*const *const std::ffi::c_void,lengths:*const usize)->Vec<u32>{match function{\n");
    for (i, f) in p.functions.iter().enumerate().filter(|(_,f)|selected(&f.name)) {
        out.push_str(&format!("{i}=>{{"));
        for (j, (_, t)) in f.params.iter().enumerate() {
            let value = match t {
                Type::List(t) => format!(
                    "(0..unsafe{{*lengths.add({j})}}).map(|_|{}).collect::<Vec<_>>().into()",
                    read(p, t)?
                ),
                _ => read(p, t)?,
            };
            out.push_str(&format!("let input=unsafe{{*data.add({j})}}.cast::<u32>();let mut cursor=0usize;let arg{j}={value};"));
        }
        let args = (0..f.params.len())
            .map(|j| format!("arg{j}"))
            .collect::<Vec<_>>()
            .join(",");
        out.push_str(&format!(
            "let result=State::new().function_l_{}({args});let mut words=Vec::new();{}words}},\n",
            f.name,
            write(p, &f.result, "result")?
        ));
    }
    out.push_str("_=>panic!(\"unknown compiled function\")}}\n");
    if !packed {
        for f in p.functions.iter().filter(|f| selected(&f.name)) {
            let mut params = vec![];
            let mut args = vec![];
            for (j, (_, t)) in f.params.iter().enumerate() {
                match t {
                    Type::List(t) if matches!(**t, Type::U32 | Type::U64) => {
                        let name = if **t == Type::U32 { "u32" } else { "u64" };
                        params.push(format!("arg{j}:*const {name},len{j}:usize"));
                        args.push(format!("if len{j}==0{{Vec::new()}}else{{unsafe{{std::slice::from_raw_parts(arg{j},len{j})}}.to_vec()}}"));
                    }
                    Type::U32 | Type::U64 | Type::Bool => {
                        let name = match t {
                            Type::U32 => "u32",
                            Type::U64 => "u64",
                            _ => "bool",
                        };
                        params.push(format!("arg{j}:{name}"));
                        args.push(format!("arg{j}"));
                    }
                    _ => return Err("unsupported scalar CPU argument".into()),
                }
            }
            let result = match f.result {
                Type::U32 => "u32",
                Type::U64 => "u64",
                Type::Bool => "bool",
                _ => return Err("unsupported scalar CPU result".into()),
            };
            out.push_str(&format!("#[cfg_attr(target_arch=\"wasm32\",no_mangle)]pub unsafe extern \"C\" fn lang_fn_{}({})->{result}{{State::new().function_l_{}({})}}\n",f.name,params.join(","),f.name,args.join(",")));
        }
        out.push_str("pub unsafe fn ink_cpu_call(function:u32,lists:*const *const std::ffi::c_void,lengths:*const usize,scalars:*const u64)->u64{match function{");
        for (i, f) in p.functions.iter().enumerate().filter(|(_,f)|selected(&f.name)) {
            let args = f
                .params
                .iter()
                .enumerate()
                .map(|(j, (_, t))| match t {
                    Type::List(_) => {
                        format!("unsafe{{*lists.add({j})}}.cast(),unsafe{{*lengths.add({j})}}")
                    }
                    Type::Bool => format!("unsafe{{*scalars.add({j})}}!=0"),
                    _ => format!("unsafe{{*scalars.add({j})}} as _"),
                })
                .collect::<Vec<_>>()
                .join(",");
            out.push_str(&format!(
                "{i}=>(unsafe{{lang_fn_{}({args})}}) as u64,",
                f.name
            ));
        }
        out.push_str("_=>panic!(\"unknown compiled function\")}}\n");
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn selected_entry_keeps_typed_helpers_and_original_transport_index() {
        let checked=CheckedModule::from_source(ink_core::syntax::parse("module Entries;fn helper(x:u32)->Buffer<u32>{return buffer_fill(4,x);}fn unused(x:String)->String{return x;}fn output(xs:List<u32>)->List<u32>{return xs.map(fn(x)=>helper(x).at_or(0,0));}").unwrap()).unwrap();
        let before=checked.bytes().unwrap();
        assert!(lower(&checked,true).is_err());
        let code=lower_entry(&checked,true,"output").unwrap();
        let adapter=code.split("unsafe fn ink_packed_result").nth(1).unwrap();
        assert!(adapter.contains("2=>{"));
        assert!(!adapter.contains("0=>{") && !adapter.contains("1=>{"));
        assert!(code.contains("function_l_helper"));
        assert_eq!(checked.bytes().unwrap(),before);
        assert!(lower_entry(&checked,true,"helper").is_err());
        assert!(lower_entry(&checked,true,"missing").unwrap_err().contains("unknown"));
    }
    #[test]
    fn selected_entry_keeps_ingress_precondition_exports() {
        let checked=CheckedModule::from_source(ink_core::syntax::parse("module Guards;spec fn positive(x:u32)->u32 requires x>0; ensures result==x;implementation direct for positive{return x;}").unwrap()).unwrap();
        let p=checked.program();
        let root="positive";
        let guard=p.contracts.precondition_checks.get(root).unwrap();
        let code=lower_entry(&checked,true,root).unwrap();
        let adapter=code.split("unsafe fn ink_packed_result").nth(1).unwrap();
        for name in [root,guard.as_str()] {
            let index=p.functions.iter().position(|f|f.name==name).unwrap();
            assert!(adapter.contains(&format!("{index}=>{{")));
        }
    }
    #[test]
    fn recursive_and_variable_width_values_reject_before_emission() {
        for source in [
            "module Recursive;record R{next:R,}fn identity(x:R)->R{return x;}",
            "module Nested;record R{xs:List<u32>,}fn identity(x:R)->R{return x;}",
            "module Text;fn identity(x:String)->String{return x;}",
        ] {
            let checked=CheckedModule::from_source(ink_core::syntax::parse(source).unwrap()).unwrap();
            assert!(lower(&checked,true).is_err());
        }
    }
}
