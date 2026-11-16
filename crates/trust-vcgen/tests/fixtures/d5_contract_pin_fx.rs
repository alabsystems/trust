// Fixture source for the "injected is not pinned" rows of
// `call_dest_refutation_scope_realmir.rs` (2026-09-28, `p_falsefail`).
pub fn smax(a: u64, b: u64) -> u64
    requires b <= a
    ensures result <= a
{
    if a < b { b } else { a }
}
pub fn dead_else_s(a: u64) -> u64 {
    if a > 3 {
        let r = smax(a, 3);
        if r == a { 0 } else { 3 - r }
    } else {
        0
    }
}
pub fn umax(a: u64, b: u64) -> u64
    ensures result >= a
{
    if a < b { b } else { a }
}
pub fn dead_else_u(a: u64) -> u64 {
    if a > 3 {
        let r = umax(a, 3);
        if r == a { 0 } else { 3 - r }
    } else {
        0
    }
}
pub fn three() -> u64
    ensures result == 3
{
    3
}
pub fn three_bad(a: u64) -> u64 {
    let r = three();
    if a > 3 { 2 - r } else { 0 }
}
pub fn four() -> u64
    ensures result == 4
{
    three()
}
pub fn smax_bad(a: u64, b: u64) -> u64
    requires b <= a
    ensures result < a
{
    if a < b { b } else { a }
}
