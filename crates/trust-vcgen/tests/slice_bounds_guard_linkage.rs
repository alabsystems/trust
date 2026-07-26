// Regression: the guarded SLICE index VC must link the guard's slice-length
// temp to the bounds check's. Each `s.len()` produces a fresh PtrMetadata
// temp; without same-block def inlining the resolved guard `i < _4` is
// disconnected from the assert block's `_5` and the violation stays
// satisfiable — `if i < samples.len() { samples[i] }` failed closed.
//
// The fixture is the REAL extracted MIR of
// tests/trust-falsification/proved/sample_at.rs (via -Ztrust-dump=mir:<dir>).
use trust_types::*;
use trust_vcgen::generate_vcs;

#[test]
fn guarded_slice_index_vc_links_len_temps() {
    let func: VerifiableFunction =
        serde_json::from_str(include_str!("fixtures/sample_at_mir.json"))
            .expect("fixture MIR must deserialize");
    let vcs = generate_vcs(&func);
    let vc = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::SliceBoundsCheck | VcKind::IndexOutOfBounds))
        .expect("guarded slice indexing should produce a bounds VC");
    let dbg = format!("{:?}", vc.formula);
    // The dominating guard must reference the STABLE place-keyed slice-length
    // symbol (inlined through the PtrMetadata temp), so guard and violation
    // constrain the same value and the conjunction is UNSAT.
    assert!(
        dbg.matches("__slice_len").count() >= 2,
        "guard and bounds-check must share the place-keyed slice length: {dbg}"
    );
}
