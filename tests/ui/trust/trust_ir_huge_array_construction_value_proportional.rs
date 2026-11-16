//@ ignore-test (a HUGE-N memory probe: run it only under a memory ceiling, never in the suite; see below)
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: --crate-type=lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
//! CONSTRUCTING a tuple or struct that holds a huge array BY VALUE, under `-Ztrust-verify=on`.
//!
//! THE GAP THIS FILE KEPT VISIBLE IS CLOSED (2026-09-28). The THIR producer builds `(1, v)` as a
//! seed constant plus one `InsertField` per field, and the seed of an array lane was one
//! constant PER ELEMENT (`seed_lane_ty`'s array arm, `vec![one; n]`), as was the differential's
//! dead-seed zero for the MIR oracle's aggregate `Undef` (`zero_const_depth`). Both are now ONE
//! trust-ir v50 `Constant::Splat`, constant size in the length. Measured on 2026-09-23 before
//! the change with the producer alone, `tup` below at N = 1e6 / 4e6 / 16e6: 303 MB / 757 MB /
//! 2.58 GB, linear, and at N = 4e9 a 4 GiB ceiling killed it; after the change the whole file
//! compiles in the memory a small one takes (the pin-move commits record the measurements).
//!
//! It STAYS `ignore-test` on purpose. A regression here allocates per element at N = 4e9 — the
//! 2026-09-21 incident shape — and a parallel ui run has no memory ceiling, so this file is never
//! run by the suite. The shapes are pinned at a small N, under `strict`, by
//! `trust_ir_uniform_array_strict.rs`; run this one by hand only under a ceiling:
//! `taskpolicy -m 4096 <stage1 Mach-O rustc> -Ztrust-verify=on --crate-type=lib <this file>`.

#![allow(dead_code)]

// A tuple construction carrying a 4e9-byte array.
pub fn tup(v: [u8; 4_000_000_000]) -> (u8, [u8; 4_000_000_000]) {
    (1, v)
}

// A struct construction over a literal-length array field.
pub struct S {
    pub a: [u8; 67_108_864],
    pub b: u8,
}

pub fn wrap(a: [u8; 67_108_864]) -> S {
    S { a, b: 1 }
}

// A tuple construction whose length is a named const, evaluated in the signature.
const BUF: usize = 1 << 26;

pub fn pair(a: [u8; BUF]) -> (u8, [u8; BUF]) {
    (1, a)
}
