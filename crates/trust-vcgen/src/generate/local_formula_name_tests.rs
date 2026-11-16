// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
//! Trust (2026-09-25): a parameter's type range bounds the parameter's FORMULA
//! name (`crate::local_var_name`), never its source name.
//!
//! `place_to_var_name` declines a source name that is shared, reserved
//! (`result`, `old_*`, anything with `__`), projection-shaped or spelled like a
//! fallback `_<k>`, and spells the local `_<index>` instead. Every block-def,
//! guard and goal uses that spelling, so a range keyed by `decl.name` bounds a
//! term the formula does not use — or, for a parameter literally named `_2`, the
//! term of the unnamed local 2, a DIFFERENT value.

use trust_types::{BasicBlock, LocalDecl, VerifiableBody};

use super::*;

/// `fn f(<param>: u8) -> u32 { let _2: u32 = 100_000; _2 }` with the parameter
/// spelled `param_name` and local 2 unnamed.
fn param_then_unnamed_u32_temp(param_name: &str) -> VerifiableFunction {
    let u8_ty = Ty::Int { width: 8, signed: false };
    let u32_ty = Ty::Int { width: 32, signed: false };
    VerifiableFunction {
        name: "f".to_string(),
        def_path: "test::f".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: u32_ty.clone(), name: None },
                LocalDecl { index: 1, ty: u8_ty, name: Some(param_name.to_string()) },
                LocalDecl { index: 2, ty: u32_ty.clone(), name: None },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(100_000, 32))),
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: u32_ty,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// The names `conjoin_arg_type_ranges` put a bound on.
fn bounded_names(func: &VerifiableFunction) -> Vec<String> {
    let Formula::And(parts) = conjoin_arg_type_ranges(func, Formula::Bool(true)) else {
        return Vec::new();
    };
    let mut names = FxHashSet::default();
    for part in &parts[..parts.len() - 1] {
        collect_formula_var_names(part, &mut names);
    }
    let mut names: Vec<String> = names.into_iter().collect();
    names.sort();
    names
}

#[test]
fn a_parameter_spelled_like_a_fallback_bounds_itself_not_the_unnamed_local() {
    let func = param_then_unnamed_u32_temp("_2");
    // The formula spells the parameter `_1` and the u32 temp `_2`.
    assert_eq!(place_to_var_name(&func, &Place::local(1)), "_1");
    assert_eq!(place_to_var_name(&func, &Place::local(2)), "_2");
    // Keyed by source name this bounded `_2` — the temp that holds 100_000 —
    // to `[0, 255]`: a false premise under which any obligation over it is
    // vacuously proved.
    assert_eq!(bounded_names(&func), vec!["_1".to_string()]);
}

#[test]
fn a_reserved_parameter_name_bounds_its_formula_name() {
    for reserved in ["result", "old_n", "__ret"] {
        let func = param_then_unnamed_u32_temp(reserved);
        assert_eq!(place_to_var_name(&func, &Place::local(1)), "_1", "{reserved}");
        assert_eq!(bounded_names(&func), vec!["_1".to_string()], "{reserved}");
    }
}

#[test]
fn an_ordinary_parameter_name_is_unchanged() {
    // CONTROL: a unique, unreserved source name IS the formula name.
    let func = param_then_unnamed_u32_temp("n");
    assert_eq!(bounded_names(&func), vec!["n".to_string()]);
}
