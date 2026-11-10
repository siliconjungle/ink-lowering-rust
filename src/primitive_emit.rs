use ink_core::LangResult;
pub fn expression(n: &str, a: &[String], first: Option<&ink_core::core::Type>) -> LangResult<String> {
    let x = &a[0];
    if first==Some(&ink_core::core::Type::F64)&&matches!(n,"sqrt"|"floor"|"ceil"|"trunc"|"round_ties_even"){
        let x = if n=="sqrt" { uncanonical(x) } else { x.as_str() };
        return Ok(format!("temporary::ink_{n}_f64({x})"));
    }
    Ok(match n {
        "f64_div" => format!("temporary::ink_f64_div({},{})",uncanonical(x),uncanonical(&a[1])),
        "f64_bits" => format!("({x}).to_bits()"),
        "f64_from_bits" => format!("f64::from_bits({x})"),
        "f64_from_f32"|"f64_from_u32"|"f64_from_u64"|"f64_from_i32" => format!("temporary::ink_f64(({x}) as f64)"),
        "f32_from_f64" => format!("temporary::ink_f32(({x}) as f32)"),
        "f64_from_int" => format!("ink_f64_from_int(&({x}))"),
        "int_from_f64" => format!("ink_int_from_f64({x})"),
        "u32_from_f64"|"u64_from_f64"|"i32_from_f64" => format!("temporary::ink_{n}({x})"),
        "sqrt" => format!("temporary::ink_sqrt({})", uncanonical(x)),
        "floor" | "ceil" | "trunc" | "round_ties_even" | "u32_from_f32"
        | "u64_from_f32" | "i32_from_f32" => format!("temporary::ink_{n}({x})"),
        "f32_div" => format!("temporary::ink_f32_div({},{})", uncanonical(x), uncanonical(&a[1])),
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
/// An operand that is itself one canonicalised float expression, without
/// that canonicalisation. `+ - * /` and the square root of a NaN are a NaN,
/// and the operation this operand feeds canonicalises its own result. So
/// canonicalising the operand first cannot change that result: when the
/// operand is not a NaN the two are the same value, and when it is, the
/// result is the canonical NaN either way.
pub(crate) fn uncanonical(operand: &str) -> &str {
    for prefix in [
        "temporary::ink_f32(",
        "temporary::ink_f64(",
        "temporary::ink_f32_carried(",
        "temporary::ink_f64_carried(",
    ] {
        let Some(rest) = operand.strip_prefix(prefix) else { continue };
        // Quotes could hide a parenthesis from the count below.
        if rest.contains(['"', '\'']) {
            return operand;
        }
        let mut depth = 1usize;
        for (i, c) in rest.char_indices() {
            match c {
                '(' => depth += 1,
                ')' => {
                    depth -= 1;
                    if depth == 0 {
                        // The call must be the whole operand.
                        return if i + 1 == rest.len() { &rest[..i] } else { operand };
                    }
                }
                _ => {}
            }
        }
    }
    operand
}

#[cfg(test)]
mod tests {
    use super::uncanonical;
    #[test]
    fn only_a_whole_canonicalised_operand_loses_its_canonicalisation() {
        assert_eq!(uncanonical("temporary::ink_f32((a) * (b))"), "(a) * (b)");
        assert_eq!(uncanonical("temporary::ink_f64_carried((a) + (f(b)))"), "(a) + (f(b))");
        // Not the whole operand, another helper, or text that may hide a parenthesis.
        for kept in [
            "temporary::ink_f32(a).max(temporary::ink_f32(b))",
            "temporary::ink_f32_div(a,b)",
            "temporary::ink_sqrt(a)",
            "temporary::ink_f32(self.f(\"(\".to_string()))",
            "temporary::ink_f32(g(')'))",
            "(temporary::ink_f32(a))",
            "x",
        ] {
            assert_eq!(uncanonical(kept), kept);
        }
    }
}
