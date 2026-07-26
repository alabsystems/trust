// Regression: a `for i in (0..s.len()).rev() { s[i] }` reverse-range loop must
// PROVE its slice-index bounds. `Rev<Range>::next` yields EXACTLY the values of
// the inner `0..s.len()` range (reversed), so every index is in [0, s.len()) and
// `s[i]` is in bounds. vcgen treats `.rev()` as transparent for the yield
// invariant (trace_local_to_range_aggregate hops through Iterator::rev to the
// underlying Range), conjoining `0 <= i < s.len()` onto the bounds VC. Without it
// the Rev<Range> payload is havoc'd and the bounds obligation is false-refuted.
//
// The fixture is the REAL extracted MIR of the reverse-range loop (-Ztrust-dump=mir:<dir>).
use trust_types::*;
use trust_vcgen::generate_vcs;

#[test]
fn rev_range_index_vc_carries_yield_bound() {
    let func: VerifiableFunction =
        serde_json::from_str(include_str!("fixtures/rev_range_index_mir.json"))
            .expect("fixture MIR must deserialize");
    let vcs = generate_vcs(&func);
    let vc = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::SliceBoundsCheck | VcKind::IndexOutOfBounds))
        .expect("reverse-range slice indexing should produce a bounds VC");
    let dbg = format!("{:?}", vc.formula);
    assert!(
        dbg.matches("__slice_len").count() >= 2,
        "yield bound and violation must share the place-keyed slice length: {dbg}"
    );
    assert!(
        dbg.contains("Lt"),
        "the range-yield upper bound (payload < end) must be conjoined: {dbg}"
    );
}
