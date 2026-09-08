//@ run-pass
//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Trust (wave-SLM): a slice-pattern match over a shared `&[T]` lowers as a
//! LENGTH CHAIN over the fat pointer's two lanes — the wave-SM skeleton with
//! byte compares replaced by one length test per arm.
//!
//! `count_members` is the corpus body and the reason the final-miss
//! `Inst::Unreachable` leg is load-bearing: it has NO wildcard arm, so the
//! chain's last miss is unreachable only under rustc's own E0004 exhaustiveness
//! certificate (the wave-UM argument).
//!
//! `run-pass` checks the rest-binding's sub-slice value `(data + k, len - k)`
//! against real execution — a wrong GEP or a wrapped `Sub` shows up as a wrong
//! count, not as a changed tag.

pub fn count_members(v: &[usize]) -> usize {
    match *v {
        [] => 0,
        [_] => 1,
        [_, ref xs @ ..] => 1 + count_members(xs),
    }
}

/// The wildcard form, so the default-arm leg is covered beside the
/// unreachable-miss one.
pub fn head_or_zero(v: &[i32]) -> i32 {
    match *v {
        [] => 0,
        [_, _, ref rest @ ..] => 2 + rest.len() as i32,
        _ => 1,
    }
}

fn main() {
    assert_eq!(count_members(&[1, 2, 3, 4]), 4);
    assert_eq!(count_members(&[]), 0);
    assert_eq!(count_members(&[9]), 1);
    assert_eq!(head_or_zero(&[]), 0);
    assert_eq!(head_or_zero(&[7]), 1);
    assert_eq!(head_or_zero(&[7, 8, 9, 10]), 4);
}
