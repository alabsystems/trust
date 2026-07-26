#![crate_type = "lib"]
// PROVED (-full StepBy<Range> native yield bound): `for i in (0..8).step_by(2)`
// over a `[u8; 8]` yields i in {0, 2, 4, 6} — every yield is `< 8`, so `arr[i]` is
// always in bounds. Previously `-full` fail-closed the WHOLE function (the
// `StepBy::next` desugar call was unlowerable). Now the native bridge recognizes
// `StepBy<[0, 8)>::next` and models the `Some` payload `v` with
// `Assume(0 <= v < 8)` (EXCLUSIVE upper), discharging the `arr[i]` bounds
// obligation. The DEFAULT formula lane already proves this (commit f63ba12aa5);
// this fixture pins the `-full` native path. Verifies (exit 0).
pub fn f(arr: &[u8; 8]) -> u8 {
    let mut s = 0u8;
    for i in (0..8).step_by(2) {
        s ^= arr[i];
    }
    s
}
