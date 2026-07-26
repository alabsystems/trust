//! Result-return grounding (F3): the gate (`enum_return_grounded_model_vars`)
//! and the pin loop must agree, and the pinned `_0_discr` must follow the
//! PARSER convention (`is_ok ⟹ _0_discr != 0` — `spec_parse::map_method_call`),
//! which is INVERTED vs Result's machine variant order (Ok = variant 0).
//! A sign flip here is a simultaneous false-PROVE (`is_err()` of an Ok
//! return) and false-FAIL (`is_ok()` of an Ok return), so BOTH polarities
//! are pinned structurally below.

use trust_types::{
    AggregateKind, BasicBlock, BlockId, ConstValue, Contract, ContractKind, Formula,
    LocalDecl, Operand, Place, Rvalue, SourceSpan, Statement, Terminator, Ty, VariantDef,
    VcKind, VerifiableBody, VerifiableFunction,
};

use super::{enum_return_grounded_model_vars, generate_v2_contract_vcs_impl};

fn i64_ty() -> Ty {
    Ty::Int { width: 64, signed: true }
}

/// An opaque non-integer payload (the ny-cert `Rat` handle shape).
fn opaque_payload_ty() -> Ty {
    Ty::Adt { adt_kind: None, layout: None, 
        name: "ny::Rat".into(),
        fields: vec![("0".into(), i64_ty())],
        variants: vec![],
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, }
}

/// `core::result::Result<ok_payload, i64>` in the flattened lowering shape
/// (machine tags: Ok = 0, Err = 1 — mirrors the `std_result_ty` fixtures).
fn std_result_ty(ok_payload: Ty) -> Ty {
    Ty::Adt { adt_kind: None, layout: None, 
        name: "core::result::Result".into(),
        fields: vec![
            ("__tag".into(), i64_ty()),
            ("__v0_0".into(), ok_payload.clone()),
            ("__v1_0".into(), i64_ty()),
        ],
        variants: vec![
            VariantDef { name: "Ok".into(), discriminant: 0, fields: vec![("0".into(), ok_payload)] },
            VariantDef { name: "Err".into(), discriminant: 1, fields: vec![("0".into(), i64_ty())] },
        ],
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, }
}

/// `core::option::Option<i64>` (machine tags: None = 0, Some = 1).
fn std_option_ty() -> Ty {
    Ty::Adt { adt_kind: None, layout: None, 
        name: "core::option::Option".into(),
        fields: vec![("__tag".into(), i64_ty()), ("__v1_0".into(), i64_ty())],
        variants: vec![
            VariantDef { name: "None".into(), discriminant: 0, fields: vec![] },
            VariantDef { name: "Some".into(), discriminant: 1, fields: vec![("0".into(), i64_ty())] },
        ],
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, }
}

/// A fn whose single return path constructs `ret_ty`'s `variant` in-body:
/// `fn f() -> Result<..> { _0 = <enum>::<variant>(payload); return }`.
fn enum_return_fn(ret_ty: Ty, enum_name: &str, variant: usize, payload: Operand, ensures: &str) -> VerifiableFunction {
    VerifiableFunction {
        name: "enum_ret".to_string(),
        def_path: "test::enum_ret".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: ret_ty.clone(), name: None }],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Aggregate(
                        AggregateKind::Adt {
                            name: enum_name.to_string(),
                            variant,
                            active_field: None,
                            args: None,
                        },
                        vec![payload],
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: ret_ty,
        },
        contracts: vec![Contract {
            kind: ContractKind::Ensures,
            span: SourceSpan::default(),
            body: ensures.to_string(),
        }],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// `<name> == <int>` conjuncts on the AND-SPINE only — deliberately NOT
/// descending under `Not`: the negated obligation itself contains
/// `_0_discr == 0` atoms (`is_ok` parses to `!(_0_discr == 0)`), and mixing
/// those with the pins would blind the polarity assertions.
fn and_spine_int_pins(formula: &Formula, name: &str, out: &mut Vec<i128>) {
    match formula {
        Formula::And(cs) => {
            for c in cs {
                and_spine_int_pins(c, name, out);
            }
        }
        Formula::Eq(l, r) => {
            if let (Formula::Var(n, _), Formula::Int(v)) = (&**l, &**r) {
                if n.as_str() == name {
                    out.push(*v);
                }
            }
        }
        _ => {}
    }
}

fn postcondition_vcs(func: &VerifiableFunction) -> Vec<trust_types::VerificationCondition> {
    generate_v2_contract_vcs_impl(func, None)
        .into_iter()
        .filter(|vc| matches!(vc.kind, VcKind::Postcondition))
        .collect()
}

#[test]
fn gate_credits_result_discr_and_int_payload() {
    // Result<i64, i64>, in-body Ok construction on the only return path:
    // both `_0_discr` and `_0_value` become groundable.
    let func = enum_return_fn(
        std_result_ty(i64_ty()),
        "core::result::Result",
        0,
        Operand::Constant(ConstValue::Int(5)),
        "result.is_ok()",
    );
    let grounded = enum_return_grounded_model_vars(&func);
    assert!(grounded.contains("_0_discr"), "Result discr must be credited: {grounded:?}");
    assert!(grounded.contains("_0_value"), "Int Ok-payload must be credited: {grounded:?}");
}

#[test]
fn gate_credits_result_discr_only_for_opaque_payload() {
    // Result<Rat, i64> (the ny-cert selfcheck/crown payload shape): the
    // discriminant grounds, the payload must NOT (its `_0_value*` terms
    // must keep routing to the fail-closed SpecModelUngrounded Unknown).
    let func = enum_return_fn(
        std_result_ty(opaque_payload_ty()),
        "core::result::Result",
        0,
        Operand::Copy(Place::local(0)), // operand ty irrelevant: non-Int gate is on the VariantDef
        "result.is_ok()",
    );
    let grounded = enum_return_grounded_model_vars(&func);
    assert!(grounded.contains("_0_discr"), "{grounded:?}");
    assert!(!grounded.contains("_0_value"), "opaque payload must stay ungrounded: {grounded:?}");
}

#[test]
fn gate_stays_empty_for_unresolvable_result_return() {
    // `_0` written by something the resolver cannot see (Use of an undefined
    // local — the `?`-desugar / call-dest stand-in): NOTHING is credited.
    let mut func = enum_return_fn(
        std_result_ty(i64_ty()),
        "core::result::Result",
        0,
        Operand::Constant(ConstValue::Int(5)),
        "result.is_ok()",
    );
    func.body.blocks[0].stmts = vec![Statement::Assign {
        place: Place::local(0),
        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
        span: SourceSpan::default(),
    }];
    assert!(
        enum_return_grounded_model_vars(&func).is_empty(),
        "an unresolvable return path must credit nothing (fail-closed)"
    );
}

#[test]
fn gate_option_behavior_unchanged() {
    // Option<i64> keeps its pre-Result behavior: both names credited.
    let func = enum_return_fn(
        std_option_ty(),
        "core::option::Option",
        1,
        Operand::Constant(ConstValue::Int(5)),
        "result.is_some()",
    );
    let grounded = enum_return_grounded_model_vars(&func);
    assert!(grounded.contains("_0_discr") && grounded.contains("_0_value"), "{grounded:?}");
}

#[test]
fn ok_return_pins_model_discr_one_never_machine_index_zero() {
    // POLARITY (is_ok case): `_0 = Ok(5)` is MACHINE variant 0 but must pin
    // the PARSER-convention `_0_discr == 1` (`is_ok ⟹ _0_discr != 0`).
    // Pinning the raw variant index 0 would refute a TRUE `is_ok()`
    // postcondition and vacuously prove a FALSE `is_err()` one.
    let func = enum_return_fn(
        std_result_ty(i64_ty()),
        "core::result::Result",
        0,
        Operand::Constant(ConstValue::Int(5)),
        "result.is_ok()",
    );
    let vcs = postcondition_vcs(&func);
    assert_eq!(vcs.len(), 1, "one return path -> one body-aware Postcondition VC: {vcs:#?}");
    let mut discr_pins = Vec::new();
    and_spine_int_pins(&vcs[0].formula, "_0_discr", &mut discr_pins);
    assert_eq!(discr_pins, vec![1], "Ok must pin the MODEL discr 1: {:#?}", vcs[0].formula);
    let mut value_pins = Vec::new();
    and_spine_int_pins(&vcs[0].formula, "_0_value", &mut value_pins);
    assert_eq!(value_pins, vec![5], "Ok payload must pin _0_value: {:#?}", vcs[0].formula);
}

#[test]
fn err_return_pins_model_discr_zero_and_leaves_payload_free() {
    // POLARITY (is_err case): `_0 = Err(7)` is MACHINE variant 1 but must
    // pin `_0_discr == 0` (`is_err ⟹ _0_discr == 0`), and must NOT pin
    // `_0_value` (the Ok-payload term has no denotation on the Err path;
    // leaving it free is the sound direction).
    let func = enum_return_fn(
        std_result_ty(i64_ty()),
        "core::result::Result",
        1,
        Operand::Constant(ConstValue::Int(7)),
        "result.is_err()",
    );
    let vcs = postcondition_vcs(&func);
    assert_eq!(vcs.len(), 1, "{vcs:#?}");
    let mut discr_pins = Vec::new();
    and_spine_int_pins(&vcs[0].formula, "_0_discr", &mut discr_pins);
    assert_eq!(discr_pins, vec![0], "Err must pin the MODEL discr 0: {:#?}", vcs[0].formula);
    let mut value_pins = Vec::new();
    and_spine_int_pins(&vcs[0].formula, "_0_value", &mut value_pins);
    assert!(value_pins.is_empty(), "Err must not pin _0_value: {:#?}", vcs[0].formula);
}

#[test]
fn opaque_payload_predicate_stays_fail_closed_unknown() {
    // The ny selfcheck shape under F3: `_0_discr` grounds, but the guard's
    // `_0_value_sign` does not — the WHOLE predicate must keep routing to
    // the non-refutable SpecModelUngrounded Unknown (grounding the discr
    // alone must never flip these rows to a refutable, false-FAILing VC).
    let func = enum_return_fn(
        std_result_ty(opaque_payload_ty()),
        "core::result::Result",
        0,
        Operand::Copy(Place::local(0)),
        "!((result.is_ok()) && (result.unwrap().is_positive()))",
    );
    let vcs = generate_v2_contract_vcs_impl(&func, None);
    assert!(
        !vcs.iter().any(|vc| matches!(vc.kind, VcKind::Postcondition)),
        "must not emit a refutable Postcondition VC: {vcs:#?}"
    );
    let rows: Vec<_> = vcs
        .iter()
        .filter(|vc| {
            matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. }
                if kind == crate::contracts::SPEC_MODEL_UNGROUNDED_KIND)
        })
        .collect();
    assert_eq!(rows.len(), 1, "exactly one fail-closed row: {vcs:#?}");
    let VcKind::UnsupportedMir { detail, .. } = &rows[0].kind else { unreachable!() };
    assert!(
        detail.contains("_0_value_sign") && !detail.contains("_0_discr"),
        "the leftover ungrounded term is the sign var (discr is now groundable): {detail}"
    );
}

#[test]
fn crown_style_len_guard_text_parses_and_routes_fail_closed() {
    // The EXACT text the extended compiler lowerer emits for the ny-cert
    // crown ensures
    //   `!matches!(r, Ok(c) if c.entailment.premises.len()
    //                          != c.entailment.multipliers.len())`
    // after the pat-binding substitution (`c` -> `result.unwrap()`, fields
    // by positional index) and the `len` allow-list addition. Pins the
    // compiler->parser handshake: the text PARSES (the row leaves
    // SpecEnsuresUnparseable), the minted `_0_value.<i>.<j>_len` names
    // classify as SPEC-MODEL terms, and — with `_0_discr` groundable via
    // the Result return — the predicate still routes to the non-refutable
    // SpecModelUngrounded Unknown (the len terms have no body pin yet),
    // never to a refutable havoc'd VC.
    let func = enum_return_fn(
        std_result_ty(opaque_payload_ty()),
        "core::result::Result",
        0,
        Operand::Copy(Place::local(0)),
        "!((result.is_ok()) && ((result.unwrap().0.1.len()) != (result.unwrap().0.2.len())))",
    );
    let vcs = generate_v2_contract_vcs_impl(&func, None);
    assert!(
        !vcs.iter().any(|vc| matches!(vc.kind, VcKind::Postcondition)),
        "must not emit a refutable Postcondition VC: {vcs:#?}"
    );
    assert!(
        !vcs.iter().any(|vc| matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. }
            if kind == crate::contracts::SPEC_ENSURES_UNPARSEABLE_KIND)),
        "the lowered crown text must PARSE (no unparseable row): {vcs:#?}"
    );
    let rows: Vec<_> = vcs
        .iter()
        .filter(|vc| {
            matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. }
                if kind == crate::contracts::SPEC_MODEL_UNGROUNDED_KIND)
        })
        .collect();
    assert_eq!(rows.len(), 1, "exactly one fail-closed Unknown row: {vcs:#?}");
    let VcKind::UnsupportedMir { detail, .. } = &rows[0].kind else { unreachable!() };
    assert!(
        detail.contains("_0_value.0.1_len")
            && detail.contains("_0_value.0.2_len")
            && !detail.contains("_0_discr"),
        "leftover ungrounded terms are the len vars (discr groundable): {detail}"
    );
}
