// Fixture source for the dependence rows of
// `call_dest_refutation_scope_realmir.rs` (2026-09-29, review blocker 2):
// the D5-A screen holds a refutation only when it depends on a screened
// call's result. Captured with
//   trustc --edition 2021 --crate-type lib --crate-name fx \
//          -Ztrust-policy=advisory -Ztrust-dump=mir-only:<dir> d5_dependence_fx.rs
pub fn smax(a: u64, b: u64) -> u64
    requires b <= a
    ensures result <= a
{
    if a < b { b } else { a }
}
pub fn umax(a: u64, b: u64) -> u64
    ensures result >= a
{
    if a < b { b } else { a }
}
// Unrelated underflow after the call; the result is never read.
pub fn unused_result(a: u64) -> u64 {
    let _r = smax(20, 3);
    a - 10
}
// Unrelated underflow after the call; the result is read only AFTER it.
pub fn indep_after(a: u64) -> u64 {
    let r = smax(20, 3);
    let x = a - 10;
    if r > 0 { x } else { 0 }
}
// The call's bound shares the caller's parameter with the underflow.
pub fn indep_after_shared(a: u64) -> u64 {
    let r = umax(a, 3);
    let x = a - 10;
    if r > 0 { x } else { 0 }
}
// DATA dependence: `r - 10` never underflows (`smax(20, 3)` is 20), but the
// bound `r <= 20` lets the solver pick `r < 10`.
pub fn data_dep(a: u64) -> u64 {
    let r = smax(20, 3);
    let w = r + 1;
    if a > 0 { w - 10 } else { 0 }
}
// CONTROL dependence of a value: `v` is chosen by a branch on `r`.
// `umax(a, 3) > 100` only when `a > 100`, so `a - v` never underflows.
pub fn ctrl_dep_value(a: u64) -> u64 {
    let r = umax(a, 3);
    let v = if r > 100 { 10 } else { 0 };
    a - v
}
// CONTROL dependence of REACHABILITY: the underflow is reached only when
// `r > 100`, i.e. only when `a > 100`, where `a - 10` cannot underflow.
pub fn ctrl_dep_reach(a: u64) -> u64 {
    let r = umax(a, 3);
    if r > 100 { a - 10 } else { 0 }
}
