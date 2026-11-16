//@ needs-trust-verify
//@ edition: 2021
//@ revisions: statics repeat_above_the_cap
//@[statics] check-pass
//@[repeat_above_the_cap] check-pass
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//! **A zero-sized array of `usize::MAX` elements compiles under verification
//! (Trust, 2026-09-29).**
//!
//! Valid Rust must compile identically with verification on. The THIR lowering
//! spells a non-scalar array as a tuple with one field per element, and asked for a
//! `usize::MAX`-field vector here: the whole compilation aborted with a capacity
//! overflow in `LowerCx::map_ty`, while the same file built with
//! `-Ztrust-verify=off` (the trip-count lane's precondition audit, `x02`). The tuple
//! spelling is now capped like every other per-element expansion
//! (`MAX_MATERIALIZED_ARRAY_LEN`), and a longer array records a gap and is left to
//! the MIR lane.

//!
//! * `repeat_above_the_cap`: a closure that is never called builds `[0u8; 1 << 59]`.
//!   The MIR-lane bridge spelled a constant repeat as one `Constant::Array` holding
//!   every element, asked for a `2^59`-element vector, and aborted the compiler (the
//!   round-2 precondition audit, `q17`). TrustIr has no repeat constant, so the bridge
//!   now refuses a repeat above its materialization cap as an unsupported operation:
//!   the closure's native lowering reports a gap, and the build fails with a
//!   verification error instead of a crash.
//!   RE-PINNED 2026-10-15 (the merge of 2026-10-14): main's `uniform_array` spelling
//!   lowers a repeat of ANY length as one instruction, which replaced that refusal at
//!   the merge, so the closure now lowers and verifies and the build succeeds
//!   (`check-pass`, measured on the merged stage 1). What this revision guards is
//!   unchanged: the compiler must not abort on the repeat.

#[cfg(statics)]
pub static HUGE: [(); usize::MAX] = [(); usize::MAX];

#[cfg(statics)]
pub fn huge_len() -> usize {
    let a = [(); usize::MAX];
    a.len()
}

#[cfg(repeat_above_the_cap)]
pub fn len_with_an_unused_buffer(s: &[u8]) -> usize {
    let _g = |_: &u8| [0u8; 1 << 59];
    s.len()
}
