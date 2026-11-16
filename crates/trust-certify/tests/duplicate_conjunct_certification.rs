// A REPEATED conjunct must not cost an obligation its kernel certificate.
//
// `∧` is idempotent: `A ∧ A ∧ G` and `A ∧ G` are the same proposition. But
// `collect_supported_atoms` fed `supported_hyps_from_atoms` 1:1, so a conjunct
// spelled twice became two DISTINCT hypotheses (`h_i`, `h_j`) carrying the same
// assertion, and ay's zero-trust reconstruction could no longer bind its premise
// to one exact hypothesis. The obligation then declined — while the identical
// single-copy obligation certified.
//
// This was not academic. Measured 2026-08-29 on stage1 `47aecd73e6`, for
//
// ```rust
// pub fn clamp_upper(v: u32, hi: u32) -> u32 ensures result <= hi {
//     if v > hi { hi } else { v }
// }
// ```
//
// the `{ hi }` arm's violation carries the return-slot definition
// `_0#s1_0 = hi` TWICE whenever `-C debuginfo != 0` — i.e. in every cargo/targo
// `dev`-profile build, and in none of the bare `trustc` probes that were used to
// develop the lane. The row lost its `clean_cic` certificate, targo's
// publication boundary withheld it ("without attachable native or clean-kernel
// proof evidence"), and `crates/trust-ratio` — every one of whose clauses is
// parameter-bounded — stopped passing the strict lane it was written for. A
// CONSTANT-bounded twin (`_0 = 15`) was unaffected, because the closed-constant
// interval lane never needed the duplicated hypothesis; that asymmetry is what
// made the regression read as "a parameter bound no longer discharges".
//
// The four assertions below are exactly the discriminator: each pair differs
// only in how many times one load-bearing conjunct is written.
//
// Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.

use trust_types::{Formula, Sort, SourceSpan, VcKind, VerificationCondition};

fn int(name: &str) -> Formula {
    Formula::Var(name.to_string(), Sort::Int)
}
fn boolean(name: &str) -> Formula {
    Formula::Var(name.to_string(), Sort::Bool)
}
fn lit(value: i128) -> Formula {
    Formula::Int(value)
}
fn gt(a: Formula, b: Formula) -> Formula {
    Formula::Gt(Box::new(a), Box::new(b))
}
fn ge(a: Formula, b: Formula) -> Formula {
    Formula::Ge(Box::new(a), Box::new(b))
}
fn le(a: Formula, b: Formula) -> Formula {
    Formula::Le(Box::new(a), Box::new(b))
}
fn eq(a: Formula, b: Formula) -> Formula {
    Formula::Eq(Box::new(a), Box::new(b))
}
fn not(a: Formula) -> Formula {
    Formula::Not(Box::new(a))
}

fn vc(formula: Formula) -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::Postcondition,
        function: "clamp_upper".into(),
        location: SourceSpan {
            file: "lib.rs".to_string(),
            line_start: 3,
            col_start: 16,
            line_end: 3,
            col_end: 18,
        },
        formula,
        contract_metadata: None,
        obligation: None,
    }
}

fn certifies(formula: Formula) -> bool {
    trust_certify::certify_vc(&vc(formula)).is_some()
}

/// The exact `{ hi }`-arm violation `trustc` emits, parameterized by how many
/// times the return-slot definition `_0#s1_0 = hi` is written. `copies = 2` is
/// what a `-C debuginfo != 0` build produces; `copies = 1` is what a
/// `-C debuginfo=0` build produces.
fn clamp_upper_hi_arm(copies: usize) -> Formula {
    let mut inner = vec![eq(int("_0#s1_0"), int("hi")); copies];
    inner.push(not(le(int("_0#s1_0"), int("hi"))));
    Formula::And(vec![
        Formula::Bool(true),
        eq(boolean("_3"), gt(int("v"), int("hi"))),
        Formula::And(vec![
            gt(int("v"), int("hi")),
            Formula::And(vec![ge(int("v"), lit(0)), le(int("v"), lit(4294967295))]),
            Formula::And(vec![ge(int("hi"), lit(0)), le(int("hi"), lit(4294967295))]),
            Formula::And(vec![eq(boolean("_3"), gt(int("v"), int("hi"))), Formula::And(inner)]),
        ]),
    ])
}

#[test]
fn a_repeated_definition_does_not_cost_the_certificate() {
    // The control: one copy. This certified before the fix and must keep doing so.
    assert!(
        certifies(clamp_upper_hi_arm(1)),
        "single-copy `{{ hi }}` arm must certify — the lane itself is intact"
    );
    // The regression: the same proposition, one conjunct written twice.
    assert!(
        certifies(clamp_upper_hi_arm(2)),
        "a REPEATED `_0#s1_0 = hi` must not cost the kernel certificate — `∧` is idempotent"
    );
    // And three copies, so the fix is deduplication rather than an off-by-one.
    assert!(certifies(clamp_upper_hi_arm(3)), "three copies must certify too");
}

#[test]
fn the_duplicate_defect_was_not_specific_to_reflexivity() {
    // The transitive twin (`else { v }` arm): `¬(v > hi) ∧ _0 = v ∧ ¬(_0 ≤ hi)`.
    // Its single-copy form always certified; the duplicated form did not.
    let arm = |copies: usize| {
        let mut conjuncts = vec![not(gt(int("v"), int("hi")))];
        conjuncts.extend(vec![eq(int("_0"), int("v")); copies]);
        conjuncts.push(not(le(int("_0"), int("hi"))));
        Formula::And(conjuncts)
    };
    assert!(certifies(arm(1)), "single-copy transitive arm must certify");
    assert!(certifies(arm(2)), "duplicated transitive arm must certify");
}

#[test]
fn a_repeated_goal_atom_does_not_cost_the_certificate() {
    let repeated_goal = Formula::And(vec![
        eq(int("_0"), int("hi")),
        not(le(int("_0"), int("hi"))),
        not(le(int("_0"), int("hi"))),
    ]);
    assert!(certifies(repeated_goal), "a repeated GOAL atom must not decline either");
}

#[test]
fn the_constant_bounded_twin_is_unaffected_in_both_directions() {
    // This is the control that explains the reported symptom: a constant bound
    // certified with or without the duplicate, which is why `trust-hex` kept
    // publishing while `trust-ratio` stopped. It must stay true after the fix.
    let arm = |copies: usize| {
        let mut conjuncts = vec![eq(int("_0"), lit(15)); copies];
        conjuncts.push(not(le(int("_0"), lit(15))));
        Formula::And(conjuncts)
    };
    assert!(certifies(arm(1)), "constant bound, one copy");
    assert!(certifies(arm(2)), "constant bound, two copies");
}

#[test]
fn deduplication_does_not_certify_a_satisfiable_obligation() {
    // Fail-closed control. `_0 = hi ∧ ¬(_0 ≤ hi + 1)` is SATISFIABLE-free only
    // by reflexivity; flip it to a genuinely satisfiable violation and no number
    // of duplicate conjuncts may mint a certificate.
    let satisfiable = |copies: usize| {
        let mut conjuncts = vec![eq(int("_0"), int("v")); copies];
        conjuncts.push(not(le(int("_0"), int("hi"))));
        Formula::And(conjuncts)
    };
    assert!(!certifies(satisfiable(1)), "`_0 = v ∧ ¬(_0 ≤ hi)` has a model — it must NOT certify");
    assert!(
        !certifies(satisfiable(2)),
        "duplicating a conjunct of a satisfiable violation must not mint a certificate"
    );
    assert!(
        !certifies(satisfiable(3)),
        "nor may three copies — deduplication is exact, never weakening"
    );
}
