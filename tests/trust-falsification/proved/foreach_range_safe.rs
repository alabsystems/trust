#![crate_type = "lib"]
// REGRESSION / coverage (assert-refutation + -full lowering, 2026-06-23): a
// `for i in 0..n` RANGE loop with an always-true body assert. Previously `-full`
// fail-closed the WHOLE function with a lowering error — `Call target
// std::iter::IntoIterator::into_iter is not present in the TrustIr module` — so
// even this trivially-safe loop was rejected (rc=1). Fixed by modelling an
// exclusive primitive `Range`'s total `into_iter`/`next` as a fresh `Undef`
// (`total_range_iterator_call`), so the function lowers and its real obligations
// are checked (the index is unconstrained, so an index-dependent obligation would
// fail closed, never falsely proved). `x == x` is reflexively true, so this
// verifies (exit 0).
pub fn f(x: u32, n: usize) -> u32 {
    for _ in 0..n {
        assert!(x == x);
    }
    x
}
