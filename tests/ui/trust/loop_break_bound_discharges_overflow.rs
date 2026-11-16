//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
//! A bottom-tested loop whose break test bounds its counter.
//!
//! This was a FALSE REFUTATION until 2026-09-18, which is the worst result this
//! compiler can produce: not an admitted gap but a positive claim that correct
//! code is wrong. `f` below ends with the counter at 6, and the compiler
//! reported `[overflow:add] FAILED` with a counterexample setting it to
//! `u32::MAX`, a state the loop cannot reach.
//!
//! The `while` and `for` spellings of the same program always proved, because
//! there the guard dominates the increment and an ordinary path condition
//! suffices. In this spelling the increment comes first and the bound has to
//! come from the previous iteration's non-break edge. Four things had to meet
//! for it to arrive: the branch is read back onto the values it compares rather
//! than onto the bool temp; that narrowing is intersected with the place's own
//! type range; every local is seeded with its type range; and the environment's
//! bound is found through a variable's SSA version token.
//!
//! `loop_break_unbounded_still_refutes.rs` is the other half.

pub fn f() -> u32 {
    let mut r = 0;
    loop {
        r += 1;
        if r > 5 {
            break;
        }
    }
    r
}

pub fn g() -> u32 {
    let mut r = 0u32;
    loop {
        r += 1;
        if r > 1000 {
            break;
        }
    }
    r
}
