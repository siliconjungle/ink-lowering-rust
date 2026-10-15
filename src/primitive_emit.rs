use ink_core::LangResult;
pub fn expression(n: &str, a: &[String], first: Option<&ink_core::core::Type>) -> LangResult<String> {
    let x = &a[0];
    if first==Some(&ink_core::core::Type::F64)&&matches!(n,"sqrt"|"floor"|"ceil"|"trunc"|"round_ties_even"){
        return Ok(format!("temporary::ink_{n}_f64({x})"));
    }
    Ok(match n {
        "f64_div" => format!("temporary::ink_f64_div({x},{})",a[1]),
        "f64_bits" => format!("({x}).to_bits()"),
        "f64_from_bits" => format!("f64::from_bits({x})"),
        "f64_from_f32"|"f64_from_u32"|"f64_from_u64"|"f64_from_i32" => format!("temporary::ink_f64(({x}) as f64)"),
        "f32_from_f64" => format!("temporary::ink_f32(({x}) as f32)"),
        "f64_from_int" => format!("ink_f64_from_int(&({x}))"),
        "int_from_f64" => format!("ink_int_from_f64({x})"),
        "u32_from_f64"|"u64_from_f64"|"i32_from_f64" => format!("temporary::ink_{n}({x})"),
        "sqrt" | "floor" | "ceil" | "trunc" | "round_ties_even" | "u32_from_f32"
        | "u64_from_f32" | "i32_from_f32" => format!("temporary::ink_{n}({x})"),
        "f32_div" => format!("temporary::ink_f32_div({x},{})", a[1]),
        "is_nan" | "is_finite" => format!("({x}).{n}()"),
        "f32_bits" => format!("({x}).to_bits()"),
        "f32_from_bits" => format!("f32::from_bits({x})"),
        "f32_from_int" => format!("ink_f32_from_int(&({x}))"),
        "int_from_f32" => format!("ink_int_from_f32({x})"),
        "f32_from_u32" | "f32_from_u64" | "f32_from_i32" => format!("({x}) as f32"),
        "popcount" | "leading_zeros" | "trailing_zeros" => {
            format!("({x}).{}()", if n == "popcount" { "count_ones" } else { n })
        }
        "string_byte_len" => format!("temporary::ink_string_byte_len(&({x}))"),
        "string_byte_at" => format!("temporary::ink_string_byte_at(&({x}),{})", a[1]),
        "string_slice" => format!("temporary::ink_string_slice(&({x}),{},{})", a[1], a[2]),
        "string_concat" => format!("temporary::ink_string_concat(&({x}),&({}))", a[1]),
        "string_find" => format!("temporary::ink_string_find(&({x}),&({}),{})", a[1], a[2]),
        _ => return Err("unsupported primitive in Rust lowering".into()),
    })
}
