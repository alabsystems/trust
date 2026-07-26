// Regression (task #31): a reverse manual index loop
//   let mut i = s.len(); while i > 0 { i -= 1; s[i] }
// must carry the downward-induction fact `i - 1 < s.len()` on its bounds VC — keyed
// to the FRESH CheckedSub result temp `_t.0` (= the decremented value) so the
// loop-variable reassignment does not clobber it. The guard `i > 0` does not bound
// `i` above; the bound is the init `s.len()` + monotone decrement.
//
// Fixture is the REAL extracted MIR (via -Ztrust-dump=mir:<dir>).
use trust_types::*;
use trust_vcgen::generate_vcs;

#[test]
fn reverse_loop_carries_decrement_bound() {
    let func: VerifiableFunction =
        serde_json::from_str(include_str!("fixtures/rev_idx_loop_mir.json"))
            .expect("fixture MIR must deserialize");
    let vc = generate_vcs(&func)
        .into_iter()
        .find(|vc| matches!(vc.kind, VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck))
        .expect("reverse loop indexing must produce a bounds VC");
    let dbg = format!("{:?}", vc.formula);
    // `Lt(_t.0, s__slice_len)` — the decrement result is strictly below the length.
    // Trust (countdown-loop piece, B1): SYMBOLIC bounds deliberately KEEP this
    // shape (the `<= B - c` strengthening applies to CONSTANT bounds only — a
    // symbolic `len - c` can be negative at runtime, colliding with the VC lane's
    // `result >= 0` type range as a phantom `len >= c` premise).
    assert!(
        dbg.contains(".0\"") && dbg.contains("__slice_len") && dbg.contains("Lt(Var(\"_"),
        "reverse-loop bounds VC must carry the `i-1 < s.len()` downward fact: {dbg}"
    );
}
