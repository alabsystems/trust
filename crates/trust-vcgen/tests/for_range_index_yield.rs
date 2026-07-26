// Regression: a `for i in 0..s.len() { s[i] }` loop must PROVE its slice-index
// bounds. The loop variable `i` is the `Some` payload of `<Range as
// Iterator>::next`; by the exclusive-range yield invariant every yielded value
// is in `[0, s.len())`, so `s[i]` is in-bounds. vcgen models this
// (build_range_yield_guard_map) by conjoining `0 <= i < s.len()` onto the bounds
// VC, making the violation `i >= s.len()` UNSAT. Without it, `i` is havoc'd
// (derived from the unmodeled `next()` call) and the bounds obligation is
// false-refuted — an inferiority case (rustc accepts the code).
//
// The fixture is the REAL extracted MIR of a `for i in 0..s.len()` body
// (via -Ztrust-dump=mir:<dir>).
use trust_types::*;
use trust_vcgen::generate_vcs;

#[test]
fn for_range_index_vc_carries_yield_bound() {
    let func: VerifiableFunction =
        serde_json::from_str(include_str!("fixtures/for_range_index_mir.json"))
            .expect("fixture MIR must deserialize");
    let vcs = generate_vcs(&func);
    let vc = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::SliceBoundsCheck | VcKind::IndexOutOfBounds))
        .expect("for-range slice indexing should produce a bounds VC");
    let dbg = format!("{:?}", vc.formula);
    // The range-yield fact constrains the payload index `i` against the SAME
    // place-keyed slice-length symbol the violation compares to. So the
    // slice-length symbol appears at least twice (violation side + yield bound),
    // and the yield's `Lt` upper bound is present — together making the
    // conjunction UNSAT (the bounds VC is dischargeable).
    assert!(
        dbg.matches("__slice_len").count() >= 2,
        "yield bound and violation must share the place-keyed slice length: {dbg}"
    );
    assert!(
        dbg.contains("Lt"),
        "the range-yield upper bound (payload < end) must be conjoined: {dbg}"
    );
}
