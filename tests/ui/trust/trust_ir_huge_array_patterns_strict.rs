//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=on
//@ compile-flags: --crate-type=lib
//@ needs-trust-verify
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! Array PATTERNS over huge first-class arrays LOWER — under `strict`, where any producer
//! refusal is a compile error — and cost the pattern's text, not the array's length.
//!
//! Each body below was REFUSED by a length cap before every array was a first-class
//! `Ty::Array` (2026-09-23), in constant memory, so a check-pass without `strict` could not tell
//! the caps apart from their absence. Measured on the pre-change compiler (7bc480faf) under
//! `strict`: `classify_ref` refused `Match(array scrutinee)` (the `&[T; N]` match lane's
//! `ARRAY_REF_MATCH_LEN_CAP`, N > 256), `ends` refused `VarRef(unbound)` (the destructure's
//! `MAX_MATERIALIZED_ARRAY_LEN` element list), `classify` refused
//! `Array(length above materialization cap)` (the positional match's lane table). Re-adding any
//! of those caps turns this file red.
//!
//! `tail_past_u32` names a position past `u32::MAX` with a real literal test and a real binding,
//! so the positional match carries it as a `u64` slot position rather than a truncated field
//! index. `last_zst`/`last_zst_match` bind a position past `i64::MAX`: the element index is a
//! `Usize` constant (an `I64` one was an out-of-range constant that failed module validation —
//! `ConstTypeMismatch` — a hard error on a valid program). That failure is raised at final module
//! validation, which `-Ztrust-policy=advisory` demotes to a warning, so this file runs under the
//! default policy.
//!
//! Deliberately NOT here: a BINDING rest (`[a, rest @ .., z]`). Its middle used to be copied one
//! element at a time by both the producer and the MIR bridge's `Subslice` lowering. Since
//! trust-ir v50 (2026-09-28) it is a constant-size read — the uniform middle directly, or one
//! spill + `GEP` + `Load` — pinned under `strict` by trust_ir_uniform_array_strict.rs. It stays
//! out of THIS file because a regression back to the per-element copy at a length like these
//! would be a runaway compile in a suite that runs without a memory ceiling; that file pins it
//! at a length where a regression stays cheap.

#![allow(dead_code)]

// The `&[T; N]` match lane at N = 4e9 (it refused every N above 256).
pub fn classify_ref(v: &[u8; 4_000_000_000]) -> i32 {
    match v {
        [0, .., 255] => 1,
        _ => 2,
    }
}

// A destructure naming two positions of a 5e9-element array.
pub fn ends(v: [u8; 5_000_000_000]) -> u8 {
    let [a, .., b] = v;
    a ^ b
}

// The positional match classifying by the first and the last element.
pub fn classify(v: [u8; 4_000_000_000]) -> u8 {
    match v {
        [0, .., 255] => 1,
        [a, .., _] => a,
    }
}

// The last position, 4_999_999_999, does not fit a `u32`; it is tested AND bound.
pub fn tail_past_u32(v: [u8; 5_000_000_000]) -> u8 {
    match v {
        [0, .., 7] => 1,
        [_, .., x] => x,
    }
}

#[derive(Clone, Copy)]
pub struct Z;

// A zero-sized element at the largest length there is: the bound position is `usize::MAX - 1`,
// past `i64::MAX`.
pub fn last_zst(v: [Z; usize::MAX]) -> Z {
    let [.., z] = v;
    z
}

pub fn last_zst_match(v: [Z; usize::MAX]) -> Z {
    match v {
        [_, .., z] => z,
    }
}
