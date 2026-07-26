// trust-clean/source_reflect.rs: reflect a function from its SOURCE-LEVEL string
// form into a kernel-checked dependent type.
//
// The source extractors (e.g. targo-trust's `ParsedFunction`) yield a function
// as strings: typed parameters `(name, type_string)`, an optional return type
// string, and `#[requires]`/`#[ensures]` expression strings. This module parses
// those strings into the `Ty` / `Formula` model and drives `reflect_function_spec`
// — the bridge a `targo trust` stage uses to obtain the Clean dependent contract
// type for a function it parsed from source, with no compiler run required.
//
// `parse_rust_type` is deliberately fail-closed: an unrecognized named type (a
// user struct whose fields the source string does not carry) returns `None`
// rather than a wrong `Ty`, so reflection never silently mismodels it.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{FnSig, FunctionSpec, Ty};

use crate::kernel_check::ProofTerm;
use crate::reflect::{ReflectError, reflect_function_spec};

/// Parse a Rust type as written in source (`"i32"`, `"&mut [u8]"`, `"(i32, bool)"`,
/// `"[u32; 4]"`) into the Trust `Ty` model.
///
/// Returns `None` for a type whose structure cannot be recovered from the string
/// alone (a named user type, a generic parameter, a path type) — fail-closed, so
/// the caller does not reflect a mismodeled type.
#[must_use]
pub fn parse_rust_type(s: &str) -> Option<Ty> {
    let s = s.trim();
    if s.is_empty() {
        return None;
    }

    // References and raw pointers (longest prefixes first).
    if let Some(rest) = s.strip_prefix("*const ") {
        return Some(Ty::RawPtr { mutable: false, pointee: Box::new(parse_rust_type(rest)?) });
    }
    if let Some(rest) = s.strip_prefix("*mut ") {
        return Some(Ty::RawPtr { mutable: true, pointee: Box::new(parse_rust_type(rest)?) });
    }
    if let Some(rest) = s.strip_prefix("&mut ") {
        return Some(Ty::Ref { mutable: true, inner: Box::new(parse_rust_type(rest)?) });
    }
    if let Some(rest) = s.strip_prefix('&') {
        // `&'a T` lifetime forms are not modeled; only `&T`.
        if rest.starts_with('\'') {
            return None;
        }
        return Some(Ty::Ref { mutable: false, inner: Box::new(parse_rust_type(rest)?) });
    }

    // Slices `[T]` and arrays `[T; N]`.
    if let Some(inner) = s.strip_prefix('[').and_then(|x| x.strip_suffix(']')) {
        if let Some((elem, len)) = inner.rsplit_once(';') {
            let len: u64 = len.trim().parse().ok()?;
            return Some(Ty::Array { elem: Box::new(parse_rust_type(elem)?), len });
        }
        return Some(Ty::Slice { elem: Box::new(parse_rust_type(inner)?) });
    }

    // Tuples `(T, U, …)` and unit `()`; parenthesized single `(T)` == `T`.
    if let Some(inner) = s.strip_prefix('(').and_then(|x| x.strip_suffix(')')) {
        let inner = inner.trim();
        if inner.is_empty() {
            return Some(Ty::Unit);
        }
        let parts = split_top_level_commas(inner);
        if parts.len() == 1 {
            return parse_rust_type(&parts[0]);
        }
        let mut tys = Vec::with_capacity(parts.len());
        for p in parts {
            tys.push(parse_rust_type(&p)?);
        }
        return Some(Ty::Tuple(tys));
    }

    // Primitive / leaf types.
    match s {
        "bool" => Some(Ty::Bool),
        "i8" => Some(Ty::Int { width: 8, signed: true }),
        "i16" => Some(Ty::Int { width: 16, signed: true }),
        "i32" => Some(Ty::Int { width: 32, signed: true }),
        "i64" => Some(Ty::Int { width: 64, signed: true }),
        "i128" => Some(Ty::Int { width: 128, signed: true }),
        "isize" => Some(Ty::Int { width: 64, signed: true }),
        "u8" => Some(Ty::Int { width: 8, signed: false }),
        "u16" => Some(Ty::Int { width: 16, signed: false }),
        "u32" => Some(Ty::Int { width: 32, signed: false }),
        "u64" => Some(Ty::Int { width: 64, signed: false }),
        "u128" => Some(Ty::Int { width: 128, signed: false }),
        "usize" => Some(Ty::Int { width: 64, signed: false }),
        "f32" => Some(Ty::Float { width: 32 }),
        "f64" => Some(Ty::Float { width: 64 }),
        "char" => Some(Ty::Int { width: 32, signed: false }),
        "!" => Some(Ty::Never),
        // A named/path/generic type whose structure the string does not carry.
        _ => None,
    }
}

/// Split a comma-separated type list at top level, respecting nesting in
/// `()`, `[]`, and `<>`.
fn split_top_level_commas(s: &str) -> Vec<String> {
    let mut parts = Vec::new();
    let mut depth = 0i32;
    let mut start = 0usize;
    for (i, c) in s.char_indices() {
        match c {
            '(' | '[' | '<' => depth += 1,
            ')' | ']' | '>' => depth -= 1,
            ',' if depth == 0 => {
                parts.push(s[start..i].trim().to_string());
                start = i + 1;
            }
            _ => {}
        }
    }
    let tail = s[start..].trim();
    if !tail.is_empty() {
        parts.push(tail.to_string());
    }
    parts
}

/// Reflect a source-extracted function — typed parameters `(name, type_string)`,
/// an optional return type string, and `#[requires]`/`#[ensures]` expression
/// strings — into its kernel-checked dependent contract type.
///
/// This is the source-level entry point a `targo trust` stage calls: it parses
/// the type strings, assembles a [`FnSig`] + [`FunctionSpec`], and delegates to
/// [`reflect_function_spec`]. A missing return type is treated as `()` (unit).
///
/// # Errors
///
/// Returns [`ReflectError::PredicateUnsupported`] if a parameter or return type
/// string is not parseable into a `Ty`, and otherwise the [`ReflectError`] from
/// reflection (non-reflectable type, out-of-subset predicate).
pub fn reflect_source_function(
    typed_params: &[(&str, &str)],
    return_type: Option<&str>,
    requires: &[String],
    ensures: &[String],
) -> Result<ProofTerm, ReflectError> {
    let mut param_tys = Vec::with_capacity(typed_params.len());
    let mut param_names = Vec::with_capacity(typed_params.len());
    for (name, ty_str) in typed_params {
        let ty = parse_rust_type(ty_str).ok_or(ReflectError::PredicateUnsupported(
            "parameter type string is not parseable into the Ty model",
        ))?;
        param_tys.push(ty);
        param_names.push(*name);
    }
    let ret_ty = match return_type {
        None => Ty::Unit,
        Some(s) => parse_rust_type(s).ok_or(ReflectError::PredicateUnsupported(
            "return type string is not parseable into the Ty model",
        ))?,
    };

    let sig = FnSig { params: param_tys, ret: Box::new(ret_ty) };
    let spec =
        FunctionSpec { requires: requires.to_vec(), ensures: ensures.to_vec(), invariants: vec![] };
    reflect_function_spec(&sig, &param_names, &spec)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_primitives() {
        assert_eq!(parse_rust_type("i32"), Some(Ty::Int { width: 32, signed: true }));
        assert_eq!(parse_rust_type("u8"), Some(Ty::Int { width: 8, signed: false }));
        assert_eq!(parse_rust_type("bool"), Some(Ty::Bool));
        assert_eq!(parse_rust_type("usize"), Some(Ty::Int { width: 64, signed: false }));
        assert_eq!(parse_rust_type("f64"), Some(Ty::Float { width: 64 }));
        assert_eq!(parse_rust_type("  i64 "), Some(Ty::Int { width: 64, signed: true }));
    }

    #[test]
    fn parse_compound() {
        assert_eq!(
            parse_rust_type("&mut [u8]"),
            Some(Ty::Ref {
                mutable: true,
                inner: Box::new(Ty::Slice { elem: Box::new(Ty::Int { width: 8, signed: false }) })
            })
        );
        assert_eq!(
            parse_rust_type("[u32; 4]"),
            Some(Ty::Array { elem: Box::new(Ty::Int { width: 32, signed: false }), len: 4 })
        );
        assert_eq!(parse_rust_type("()"), Some(Ty::Unit));
        assert_eq!(
            parse_rust_type("(i32, bool)"),
            Some(Ty::Tuple(vec![Ty::Int { width: 32, signed: true }, Ty::Bool]))
        );
        assert_eq!(parse_rust_type("(i32)"), Some(Ty::Int { width: 32, signed: true }));
    }

    #[test]
    fn parse_nested_tuple_respects_nesting() {
        // (i32, (u8, bool)) must split at the top-level comma only.
        assert_eq!(
            parse_rust_type("(i32, (u8, bool))"),
            Some(Ty::Tuple(vec![
                Ty::Int { width: 32, signed: true },
                Ty::Tuple(vec![Ty::Int { width: 8, signed: false }, Ty::Bool]),
            ]))
        );
    }

    #[test]
    fn parse_unknown_named_type_is_none() {
        // A user struct name carries no field structure in the string → fail closed.
        assert_eq!(parse_rust_type("Foo"), None);
        assert_eq!(parse_rust_type("Vec<u8>"), None);
        assert_eq!(parse_rust_type("&'a str"), None);
    }

    #[test]
    fn reflect_source_function_produces_kernel_checked_contract() {
        use crate::kernel_check::infer_type;
        use crate::reflect::carrier_context;
        // fn clamp(x: i32) -> i32  #[requires(x > 0)] #[ensures(result > x)]
        let contract = reflect_source_function(
            &[("x", "i32")],
            Some("i32"),
            &["x > 0".to_string()],
            &["result > x".to_string()],
        )
        .expect("source function should reflect to a contract");
        let inferred = infer_type(&contract, &carrier_context(), &[])
            .expect("the contract should kernel-check");
        assert_eq!(inferred, ProofTerm::Sort(1), "a contract is a well-formed Type");
    }

    #[test]
    fn reflect_source_function_no_return_is_unit() {
        let contract = reflect_source_function(&[("x", "i32")], None, &[], &[])
            .expect("unit-return function should reflect");
        use crate::kernel_check::infer_type;
        use crate::reflect::carrier_context;
        assert!(infer_type(&contract, &carrier_context(), &[]).is_ok());
    }

    #[test]
    fn reflect_source_function_unparseable_type_errors() {
        let r = reflect_source_function(&[("x", "SomeStruct")], Some("i32"), &[], &[]);
        assert!(matches!(r, Err(ReflectError::PredicateUnsupported(_))));
    }
}
