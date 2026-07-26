// Regression (panic-freedom coverage gap, 2026-07-06): `x.abs()` on a signed
// integer PANICS at `iN::MIN` (no positive representation), exactly like `-x`
// (which Trust already catches via NegationOverflow). But `x.abs()` lowers to an
// opaque Call to `core::num::<impl iN>::abs`, so its panic path was unmodeled and
// a genuinely-unsafe `x.abs()` compiled clean — a hole in pillar-1 panic-freedom.
//
// The abs call now flows through the guard-aware panic-freedom lane, emitting a
// `Call::abs::panic-freedom` obligation `arg == iN::MIN`: unconstrained refutes,
// a dominating `x != iN::MIN` guard proves, and `wrapping_abs` (total) emits none.
use trust_types::*;
use trust_vcgen::generate_vcs;

fn abs_panic_vcs(name: &str) -> Vec<VerificationCondition> {
    let json = std::fs::read_to_string(format!("tests/fixtures/{name}.json")).unwrap();
    let f: VerifiableFunction = serde_json::from_str(&json).unwrap();
    generate_vcs(&f)
        .into_iter()
        // abs-at-MIN carries `NegationOverflow` (it IS a negation overflow; routes like `-x`).
        .filter(|vc| matches!(vc.kind, VcKind::NegationOverflow { .. }))
        .collect()
}

#[test]
fn unconstrained_abs_emits_refutable_panic_obligation() {
    let vcs = abs_panic_vcs("abs_unconstrained");
    assert_eq!(vcs.len(), 1, "unconstrained `x.abs()` must emit exactly one panic-freedom VC");
    let dbg = format!("{:?}", vcs[0].formula);
    // Violation is `x == i32::MIN` — SAT for an unconstrained x, so it refutes.
    assert!(
        dbg.contains("Int(-2147483648)") && dbg.contains("Eq(Var(\"x\""),
        "the abs panic obligation must be `x == i32::MIN` (refutable): {dbg}"
    );
}

#[test]
fn guarded_abs_panic_obligation_carries_the_guard() {
    // `if x != i32::MIN { x.abs() }` — the guard reaches the abs block, so the
    // obligation is `(x != MIN) ∧ (x == MIN)` = UNSAT (proved).
    let vcs = abs_panic_vcs("abs_guarded");
    assert_eq!(vcs.len(), 1, "guarded `x.abs()` still emits the obligation (discharged by the guard)");
    let dbg = format!("{:?}", vcs[0].formula);
    assert!(
        dbg.contains("Not(Eq(Var(\"x\", Int), Int(-2147483648)))"),
        "the dominating `x != i32::MIN` guard must be conjoined so the obligation proves: {dbg}"
    );
}

#[test]
fn wrapping_abs_emits_no_panic_obligation() {
    // `wrapping_abs` is total (returns MIN at MIN, never panics) — no obligation.
    assert!(
        abs_panic_vcs("abs_wrapping").is_empty(),
        "`wrapping_abs` does not panic and must emit no panic-freedom obligation"
    );
}
