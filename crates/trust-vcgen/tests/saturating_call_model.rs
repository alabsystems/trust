// Regression (over-refutation audit #5, 2026-07-04): a `#[ensures]` over the
// result of a std `saturating_add`/`saturating_sub` call was FALSELY REFUTED —
// the call result was havoc'd (uninterpreted std combinator). The fix models the
// EXACT clamped value `clamp(x±y, MIN, MAX)` and, when the function returns the
// saturating result directly, pins it under the RAW `_0` name the postcondition
// uses (the general call-dest fact names it `__ret`, which does not reach the
// postcond `_0` in the postcondition lane). Fixtures are REAL extracted MIR
// (-Ztrust-dump=mir:<dir>) for `fn f(x,y){ x.saturating_add/sub(y) }` with a spec.
use trust_types::*;
use trust_vcgen::generate_vcs;

fn postcondition_formula(json: &str) -> String {
    let func: VerifiableFunction =
        serde_json::from_str(json).expect("fixture MIR must deserialize");
    let vcs = generate_vcs(&func);
    let post = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::Postcondition))
        .expect("the #[ensures] clause should produce a Postcondition VC");
    format!("{:?}", post.formula)
}

#[test]
fn saturating_add_result_pinned_to_clamped_value_under_raw_ret() {
    let dbg = postcondition_formula(include_str!("fixtures/sat_add_ge.json"));
    // The return slot `_0` must be pinned to the EXACT saturating value: clamp of
    // `x + y` against the u32 max (4294967295). The pin is Ite-LIFTED to a
    // formula-level guard (so trust-mc/trust-wp discharge it), so the term-`Ite`
    // over `_0` must NOT appear — instead a guarded `Implies(... _0 == MAX / x+y)`.
    assert!(
        !dbg.contains("Eq(Var(\"_0\", Int), Ite("),
        "return-slot pin must be Ite-LIFTED (no term-Ite over `_0`): {dbg}"
    );
    assert!(
        dbg.contains("Implies") && dbg.contains("Eq(Var(\"_0\", Int)"),
        "return slot `_0` must be pinned via guarded (Implies) equalities: {dbg}"
    );
    assert!(dbg.contains("4294967295"), "the u32 saturation bound must appear: {dbg}");
    assert!(
        dbg.contains("Add(Var(\"x\", Int), Var(\"y\", Int))"),
        "the true sum `x + y` must appear: {dbg}"
    );
}

#[test]
fn saturating_sub_result_pinned_to_clamped_value_under_raw_ret() {
    let dbg = postcondition_formula(include_str!("fixtures/sat_sub_le.json"));
    assert!(
        !dbg.contains("Eq(Var(\"_0\", Int), Ite("),
        "return-slot pin must be Ite-LIFTED (no term-Ite over `_0`): {dbg}"
    );
    assert!(
        dbg.contains("Implies") && dbg.contains("Sub(Var(\"x\", Int), Var(\"y\", Int))"),
        "return slot `_0` must be pinned via guarded equalities over `x - y`: {dbg}"
    );
    // saturating_sub clamps the underflow to MIN (0 for unsigned).
    assert!(dbg.contains("Int(0)"), "the underflow-saturation floor (0) must appear: {dbg}");
}

#[test]
fn wrapping_neg_result_pinned_ite_free_under_raw_ret() {
    // Regression (solver-Ite, wrapping_neg): `#[ensures(|r| *r == 0 - x)]` over
    // `x.wrapping_neg()` was UNKNOWN (term-`Ite` pruned by trust-mc). The return
    // slot is now pinned to the exact two's-complement value, Ite-LIFTED to
    // guarded equalities so it discharges. Fixture is real extracted MIR.
    let dbg = postcondition_formula(include_str!("fixtures/wrapping_neg_wneg.json"));
    assert!(
        !dbg.contains("Eq(Var(\"_0\", Int), Ite("),
        "wrapping_neg return-pin must be Ite-LIFTED (no term-Ite over `_0`): {dbg}"
    );
    assert!(
        dbg.contains("Implies") && dbg.contains("Eq(Var(\"_0\", Int)"),
        "return slot `_0` must be pinned via guarded (Implies) equalities: {dbg}"
    );
}
