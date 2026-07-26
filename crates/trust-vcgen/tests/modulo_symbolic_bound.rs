// Regression: a wrapping access `s[n % s.len()]` (SYMBOLIC modulus) under a
// non-empty guard must carry the unsigned modulo bound `s.len() != 0 ⟹ k < s.len()`
// (encoded `(s.len() == 0) ∨ (k < s.len())`) on its bounds VC. The end-to-end proof
// also needs the ay bridge's nonlinear-relaxation retry (validated in trust-router's
// nonlinear_relaxation.rs); this test pins the vcgen-side fact.
use trust_types::*;
use trust_vcgen::generate_vcs;

#[test]
fn symbolic_modulo_carries_divisor_bound() {
    let func: VerifiableFunction =
        serde_json::from_str(include_str!("fixtures/modulo_guarded_mir.json"))
            .expect("fixture MIR must deserialize");
    let vc = generate_vcs(&func)
        .into_iter()
        .find(|vc| matches!(vc.kind, VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck))
        .expect("guarded modulo access must produce a bounds VC");
    let dbg = format!("{:?}", vc.formula);
    assert!(
        dbg.contains("Or([Eq(") && dbg.contains("__slice_len"),
        "symbolic-modulo bounds VC must carry the `len != 0 => k < len` fact: {dbg}"
    );
}
