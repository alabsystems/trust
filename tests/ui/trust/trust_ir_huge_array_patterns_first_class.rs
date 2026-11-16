//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: --crate-type=lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
//! Array PATTERNS over huge first-class arrays cost the pattern's TEXT, not the array's length.
//!
//! The THIR producer's destructure (`let [a, .., b] = v`) and match (`match v { [0, .., x] =>
//! .. }`) lanes used to type each position from a `vec![elem; n]` of element types, behind a
//! `MAX_MATERIALIZED_ARRAY_LEN` (65536) refusal, and the `&[T; N]` match lane refused
//! `N > 256` outright because a long array was a module blow-up. Every array is a first-class
//! `Ty::Array` now: a lane reads its ONE element type and addresses a position with a `Usize`
//! index constant, so each pattern below names at most three positions whatever N is —
//! including `usize::MAX - 1`, which does not fit the `u32` field-index carrier the tuple and
//! struct shapes use (element positions are carried as `u64`).
//!
//! WHAT THIS FILE DISCRIMINATES, measured one function per file under a 4 GiB ceiling on the
//! pre-change compiler (7bc480faf): `tuple_ends` and `nested_ends` grew into the ceiling and
//! were killed (their element types were spelled as N-element tuples), and `zst_ends` ICEd with
//! `capacity overflow`. `ends`, `classify` and `classify_ref` were CONTROLS there — refused by a
//! length cap, in constant memory — so this file cannot tell those caps from their absence;
//! `trust_ir_huge_array_patterns_strict.rs` pins that they LOWER. (`classify_ref` here is also
//! refused by the new producer, `TupleMatch(by-ref subpattern)`: its second arm binds through
//! the reference.)
//!
//! Deliberately NOT here: a BINDING rest (`[a, rest @ .., z]`). Its middle used to be copied one
//! element at a time by both the producer and the MIR bridge's `Subslice` lowering. Since
//! trust-ir v50 (2026-09-28) it is a constant-size read — the uniform middle directly, or one
//! spill + `GEP` + `Load` — pinned under `strict` by trust_ir_uniform_array_strict.rs. It stays
//! out of THIS file because a regression back to the per-element copy at a length like these
//! would be a runaway compile in a suite that runs without a memory ceiling; that file pins it
//! at a length where a regression stays cheap.

#![allow(dead_code)]

// A destructure naming two positions of a 5e9-element array.
pub fn ends(v: [u8; 5_000_000_000]) -> u8 {
    let [a, .., b] = v;
    a ^ b
}

// The same over tuple elements (previously the tuple-spelled lane), through a dereference.
pub fn tuple_ends(v: &[(u8, u16); 4_000_000_000]) -> u16 {
    let [(_, a), .., (_, b)] = *v;
    a ^ b
}

// A nested element pattern at both ends of a 5e9-element array of arrays.
pub fn nested_ends(v: &[[u8; 3]; 5_000_000_000]) -> u8 {
    let [[a, _, _], .., [_, _, z]] = *v;
    a ^ z
}

// A match classifying by the first and the last element (the positional match lane).
pub fn classify(v: [u8; 4_000_000_000]) -> u8 {
    match v {
        [0, .., 255] => 1,
        [a, .., _] => a,
    }
}

// The `&[T; N]` match lane, which refused every N above 256. A memory CONTROL: the by-ref
// binding in its second arm is refused on its own terms (see the header).
pub fn classify_ref(v: &[u8; 4_000_000_000]) -> u8 {
    match v {
        [0, ..] => 1,
        [a, .., b] => *a ^ *b,
    }
}

// A zero-sized array at the largest length there is: the last position is `usize::MAX - 1`.
pub fn zst_ends(v: [(); usize::MAX]) -> bool {
    match v {
        [(), .., ()] => true,
    }
}
