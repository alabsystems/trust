// Regression: `for w in s.windows(n) { w[k] }` and `for c in s.chunks(n) { c[k] }`
// must PROVE their sub-slice index bounds. `windows(n)` yields sub-slices of
// length EXACTLY n; `chunks(n)` of length in [1, n]. vcgen models the yielded
// slice's length (build_slice_iter_yield_guard_map) and conjoins it onto the
// `w[k]`/`c[k]` bounds VC — `len == n` (windows) or `1 <= len <= n` (chunks) —
// so the index obligation discharges instead of being false-refuted (the yielded
// sub-slice's length is otherwise havoc'd).
//
// Fixtures are the REAL extracted MIR of the loops (via -Ztrust-dump=mir:<dir>).
use trust_types::*;
use trust_vcgen::generate_vcs;

fn bounds_vc_formula(mir: &str) -> String {
    let func: VerifiableFunction = serde_json::from_str(mir).expect("fixture MIR must deserialize");
    let vcs = generate_vcs(&func);
    let vc = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::SliceBoundsCheck | VcKind::IndexOutOfBounds))
        .expect("sub-slice indexing should produce a bounds VC");
    format!("{:?}", vc.formula)
}

#[test]
fn windows_index_vc_carries_exact_length() {
    // windows(2): the yielded slice length is modeled `== 2`, so its `__slice_len`
    // term is equated to the window size; the index bound then discharges.
    let dbg = bounds_vc_formula(include_str!("fixtures/windows_index_mir.json"));
    assert!(
        dbg.contains("__slice_len"),
        "windows bounds VC should reference the yielded slice length: {dbg}"
    );
    assert!(
        dbg.contains("Eq"),
        "windows yields exactly-n slices, so the length must be EQUATED (== n): {dbg}"
    );
}

#[test]
fn chunks_index_vc_carries_nonempty_length() {
    // chunks(4): the yielded slice length is modeled in [1, 4]; the `c[0]` bound
    // discharges from `len >= 1`.
    let dbg = bounds_vc_formula(include_str!("fixtures/chunks_index_mir.json"));
    assert!(
        dbg.contains("__slice_len"),
        "chunks bounds VC should reference the yielded slice length: {dbg}"
    );
}
