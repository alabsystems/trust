//! INTRINSIC-RESIDUAL-1 — the generator states a 128-bit integer parameter's type
//! range itself (`missing_param_type_range_facts`), because the extractor's
//! `integer_param_range_preconditions` stops at width 64.
//!
//! THE DEFECT. Outside the arithmetic batteries every lane reads a parameter's range
//! only from `func.preconditions`, and only the extractor puts it there. Measured on
//! main 4aa65b4618 with the deterministic in-process ay router over captures of the
//! stage-2 trustc (`tests/fixtures/range_adversarial/`): `ensures result >= 0` for
//! `fn f(x: u128) -> u128 { x }` was `Failed` with `x = -1`, and `ensures result <=
//! i128::MAX` for the `i128` identity was `Failed` with `x = 2^127`. The integration
//! tests are `tests/range_fact_adversarial.rs` and
//! `tests/counterexample_type_range_guard.rs`; these pin the mechanism.

use std::borrow::Cow;

use trust_types::{Formula, LocalDecl, Sort, Ty, VcKind, VerifiableFunction};

use super::{
    missing_param_type_range_facts, producer_preconditions, with_param_type_range_facts,
    without_stated_param_ranges, without_unmodeled_contract_arithmetic,
};

fn capture(json: &str) -> VerifiableFunction {
    serde_json::from_str(json).expect("fixture must deserialize")
}

/// `fn ok_f21_u128_identity(x: u128) -> u128 ensures result >= 0 { x }`, as the
/// stage-2 trustc extracted it: `preconditions: []`.
fn u128_identity() -> VerifiableFunction {
    capture(include_str!(
        "../../tests/fixtures/range_adversarial/wide_ok_f21_u128_identity_o0.json"
    ))
}

/// `fn ok_f22_i128_identity_hi(x: i128) -> i128 ensures result <= i128::MAX { x }`.
fn i128_identity() -> VerifiableFunction {
    capture(include_str!(
        "../../tests/fixtures/range_adversarial/wide_ok_f22_i128_identity_hi_o0.json"
    ))
}

/// `ensures result >= a` over the `u32` intrinsic spelling, captured WITH the
/// extractor's facts: nothing here is 128-bit.
fn extracted_u32() -> VerifiableFunction {
    capture(include_str!("../../tests/fixtures/intrinsic_sat_add_ge_mir.json"))
}

/// The fact's shape: the extractor's `And([Ge(p, MIN), Le(p, MAX)])`.
fn range_fact(name: &str, min: Formula, max: Formula) -> Formula {
    let var = || Formula::Var(name.to_string(), Sort::Int);
    Formula::And(vec![
        Formula::Ge(Box::new(var()), Box::new(min)),
        Formula::Le(Box::new(var()), Box::new(max)),
    ])
}

fn u128_range(name: &str) -> Formula {
    range_fact(name, Formula::Int(0), Formula::UInt(u128::MAX))
}

fn i128_range(name: &str) -> Formula {
    range_fact(name, Formula::Int(i128::MIN), Formula::Int(i128::MAX))
}

#[test]
fn a_128_bit_parameter_gets_its_exact_type_range() {
    let unsigned = u128_identity();
    assert!(unsigned.preconditions.is_empty(), "the capture carries no fact for `x: u128`");
    assert_eq!(missing_param_type_range_facts(&unsigned), vec![u128_range("x")]);
    let signed = i128_identity();
    assert!(signed.preconditions.is_empty(), "the capture carries no fact for `x: i128`");
    assert_eq!(missing_param_type_range_facts(&signed), vec![i128_range("x")]);
}

/// Widths `1..=64` stay the producer's: an extracted body (which carries them) is the
/// SAME object through both views, and a body WITHOUT them is not given them here
/// either — that is `counterexample_type_range_guard`'s pinned design boundary.
#[test]
fn a_body_without_a_128_bit_parameter_is_left_untouched() {
    let func = extracted_u32();
    assert!(missing_param_type_range_facts(&func).is_empty());
    assert!(matches!(with_param_type_range_facts(&func), Cow::Borrowed(_)));
    assert!(matches!(without_unmodeled_contract_arithmetic(&func), Cow::Borrowed(_)));
    let mut stripped = func;
    stripped.preconditions.clear();
    assert!(
        missing_param_type_range_facts(&stripped).is_empty(),
        "a <= 64-bit parameter without the extractor's fact gets none from the generator"
    );
}

#[test]
fn stating_the_facts_is_idempotent() {
    let once = with_param_type_range_facts(&u128_identity()).into_owned();
    assert_eq!(once.preconditions, vec![u128_range("x")]);
    assert!(missing_param_type_range_facts(&once).is_empty());
    assert!(matches!(with_param_type_range_facts(&once), Cow::Borrowed(_)));
}

/// The lane view the per-lane helpers and the E4/E5 regeneration paths read
/// carries the facts too, so those paths see the hypothesis the first pass saw.
#[test]
fn the_shared_lane_view_carries_the_facts() {
    let func = u128_identity();
    assert_eq!(without_unmodeled_contract_arithmetic(&func).preconditions, vec![u128_range("x")]);
}

/// A caller that EMPTIED the hypothesis on purpose gets nothing restated into it.
#[test]
fn a_suspended_caller_gets_no_facts() {
    let func = u128_identity();
    assert!(without_stated_param_ranges(|| missing_param_type_range_facts(&func)).is_empty());
    assert_eq!(missing_param_type_range_facts(&func).len(), 1, "the suspension is scoped");
}

/// Only NAMED 128-bit integer PARAMETERS: no fact for a <= 64-bit width, an unnamed
/// parameter, a non-integer, or a body local.
#[test]
fn the_envelope_is_the_128_bit_parameters() {
    let mut func = u128_identity();
    let u128_ty = || Ty::Int { width: 128, signed: false };
    func.body.locals = vec![
        LocalDecl { index: 0, ty: u128_ty(), name: Some("__ret".into()) },
        LocalDecl { index: 1, ty: Ty::Int { width: 8, signed: true }, name: Some("a".into()) },
        LocalDecl { index: 2, ty: Ty::Int { width: 64, signed: false }, name: Some("b".into()) },
        LocalDecl { index: 3, ty: Ty::Int { width: 128, signed: true }, name: Some("c".into()) },
        LocalDecl { index: 4, ty: u128_ty(), name: None },
        LocalDecl { index: 5, ty: Ty::Bool, name: Some("d".into()) },
        LocalDecl { index: 6, ty: u128_ty(), name: Some("e".into()) },
        LocalDecl { index: 7, ty: u128_ty(), name: Some("f".into()) },
    ];
    func.body.arg_count = 6;
    assert_eq!(missing_param_type_range_facts(&func), vec![i128_range("c"), u128_range("e")]);
}

/// A body local sharing the parameter's source name makes `place_to_var_name` spell
/// the parameter `_<index>`; the fact must bound THAT term (the source name would
/// bound a different local, or nothing).
#[test]
fn the_fact_bounds_the_parameters_formula_name() {
    let mut func = u128_identity();
    let next = func.body.locals.len();
    func.body.locals.push(LocalDecl {
        index: next,
        ty: Ty::Int { width: 128, signed: false },
        name: Some("x".into()),
    });
    let x = crate::local_var_name(&func, &func.body.locals[1]);
    assert_ne!(x, "x", "the shared source name must force the fallback spelling");
    assert_eq!(missing_param_type_range_facts(&func), vec![u128_range(&x)]);
}

/// The measured rows: each postcondition VC now states its parameter's range.
#[test]
fn the_postcondition_rows_state_the_parameter_ranges() {
    for (func, fact) in [(u128_identity(), u128_range("x")), (i128_identity(), i128_range("x"))] {
        let vcs = crate::generate_vcs(&func);
        let post = vcs
            .iter()
            .find(|vc| matches!(vc.kind, VcKind::Postcondition))
            .expect("the ensures clause must produce a Postcondition VC");
        let mut found = false;
        post.formula.visit(&mut |node| found |= *node == fact);
        assert!(
            found,
            "{}: the postcondition row must carry {fact:?}: {:?}",
            func.name, post.formula
        );
    }
}

/// The L0 safety block lane conjoins the PRODUCER's preconditions only: it bounds every
/// integer parameter itself (`conjoin_arg_type_ranges`; the signed-128 bitvector rows
/// range over exactly the type), and the trust-ir spine reproduces those rows from
/// `func.preconditions` byte for byte (trust-ir-bridge `signed_128_bv_overflow_parity_tests`,
/// red with the stated facts in). An authored precondition is kept, in order.
#[test]
fn the_safety_lane_reads_the_producers_preconditions() {
    let mut func = u128_identity();
    let authored =
        Formula::Ge(Box::new(Formula::Var("x".to_string(), Sort::Int)), Box::new(Formula::Int(3)));
    func.preconditions = vec![authored.clone()];
    let view = with_param_type_range_facts(&func).into_owned();
    assert_eq!(view.preconditions, vec![authored.clone(), u128_range("x")]);
    assert_eq!(producer_preconditions(&view), vec![authored]);
    assert_eq!(producer_preconditions(&func), func.preconditions);
}
