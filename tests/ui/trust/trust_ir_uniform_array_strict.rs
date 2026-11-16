//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=on
//@ compile-flags: --crate-type=lib
//@ needs-trust-verify
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! Uniform arrays — `[x; N]` with a constant or a runtime element, the seed of a struct literal
//! holding an array, the rest middle of an array pattern, `[(); N]` and `[Foo; N]` — LOWER under
//! `strict` (where any producer refusal is a compile error) past the length caps that used to
//! refuse them, because each is now ONE constant-size trust-ir value (v50 `Constant::Splat` /
//! `Inst::ArraySplat`) or a constant-size read through memory, never one value per element.
//!
//! Each length is chosen so that a REGRESSION here stays cheap while a re-added cap still turns
//! the file red:
//!   * `N` (2^17, just past `MAX_MATERIALIZED_ARRAY_LEN`, 65536) for the shapes whose old
//!     per-element spelling was a constant LIST — `zeros` and `wrap` (the compact repeat and the
//!     struct literal's seed, `seed_nonempty_array`, both refused above that cap), `units` and
//!     `promoted` (which lowered, but built one constant per element: the unit seed and the
//!     promotable-const eval's `vec![value; N]`). A regression back to a list costs 2^17
//!     constants, a few MB.
//!   * `M` (2049, just past the runtime element's `REPEAT_RUNTIME_ELEM_MAX`, 2048) for the shapes
//!     whose old spelling was a per-slot BUILD — `fill` and `foos` (refused by that budget) and
//!     the two rest middles `split` and `split_param` (copied one element at a time below the
//!     65536 cap). A per-slot build is super-linear in time in the current pipeline: MEASURED
//!     2026-09-28 on the commit-2 stage1 under `taskpolicy -m 4096`, `-Ztrust-ir-lower=strict
//!     -Ztrust-verify=on`, a `[v, v, ..]` literal of K runtime elements (the same per-slot build)
//!     took 5.9 s / 191 MB at K = 1024, 16.9 s / 215 MB at 2049 and 56 s / 259 MB at 4096.
//!     Extrapolated, that curve reaches hours at 2^17, so these shapes stay at `M`, where a
//!     regression costs ~17 s. (The rest middle's old 65536 cap is pinned by the unit test
//!     `rest_middle_is_constant_size` instead.)
//!
//! Today every shape is constant size: measured on the same stage1, this file with EVERY length
//! set to 2049 and with every length set to 2^17 both compile in 254 MB (1.0 s and 0.7 s).
//! Flatness in N itself is measured, not tested, under a memory ceiling (see the producer
//! commit's acceptance table).

#![allow(dead_code)]

const N: usize = 1 << 17;
const M: usize = 2049;

// A constant element: one `Const { Constant::Splat }`.
pub fn zeros() -> [u8; N] {
    [0; N]
}

// A runtime element: one `ArraySplat`.
pub fn fill(v: u32) -> [u32; M] {
    [v; M]
}

// A struct literal holding an array: its construction seed is one `Splat`.
pub struct S {
    pub a: [u8; N],
    pub b: u8,
}

pub fn wrap() -> S {
    S { a: [0; N], b: 1 }
}

// The rest middle of an array pattern over a uniform array: the uniform middle directly.
pub fn split() -> usize {
    let [a, rest @ ..] = [7u8; M];
    a as usize + rest.len()
}

// The rest middle of an array pattern over an arbitrary array: read back through memory.
pub fn split_param(v: [u16; M]) -> u16 {
    let [a, rest @ .., z] = v;
    a ^ z ^ rest[0]
}

// Unit and struct elements.
pub fn units() -> [(); N] {
    [(); N]
}

#[derive(Clone, Copy)]
pub struct Foo {
    pub x: u8,
}

pub fn foos(f: Foo) -> [Foo; M] {
    [f; M]
}

// A promoted borrow of a repeat: `&[0; N]` is `'static`.
pub fn promoted() -> &'static [u8; N] {
    &[0; N]
}
