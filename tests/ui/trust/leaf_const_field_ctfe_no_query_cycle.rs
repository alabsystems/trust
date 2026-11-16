//@ revisions: verify lower
//@ needs-trust-verify
//@ build-pass
//@ edition: 2021
//@[verify] compile-flags: --crate-type=lib -Ztrust-verify=on -Ztrust-policy=advisory
//@[lower] compile-flags: --crate-type=lib -Ztrust-verify=off -Ztrust-ir-lower=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE

//! **Regression (fix11, L2): CTFE of a constant reached through a local ADT's fields must not
//! close a query cycle from inside `mir_built`.**
//!
//! MEASURED on stage 1 of `425f2192be` with DEFAULT flags (and with `-Ztrust-ir-lower=on`):
//! `error[E0391]: cycle detected when evaluating type-level constant` on `Cyc` below, code
//! stock rustc accepts. wfcheck of `Cyc` evaluates `sized()`, which builds `sized`'s MIR; the
//! `mir_built` hook's MIR oracle (`trust_mir_extract::ty_convert`) converted `Option<&Cyc>`,
//! walked into `Cyc`'s fields and normalized `[u8; sized()]` — the evaluation already on the
//! stack. Inside `mir_built` a constant is now evaluated only when its whole CTFE closure is
//! leaf (`ctfe_reentrancy::ctfe_closure_is_leaf`): `sized()` is a call, so its length stays
//! unknown. The layout funnel takes the same rule (`evaluate_leaf_constants`), so the leaf
//! shapes below (`[u8; N]`, `[u8; Self::LEN]`, a trait constant over `u32`) are evaluated
//! there, and those must not cycle either. `build-pass` in both revisions is the assertion.

pub struct Cyc { a: [u8; sized()], b: u8 }
pub const fn sized() -> usize {
    let _r: Option<&Cyc> = None;
    4
}
pub fn cyc(x: Cyc) -> Cyc { x }

// The same shape one ADT further out, and through a by-value local in a non-const fn.
pub struct Outer { c: Option<Cyc>, n: u32 }
pub const fn outer_len() -> usize {
    let _o: Option<&Outer> = None;
    2
}
pub struct Back { a: [u16; outer_len()], b: u8 }
pub fn back(x: Back) -> Back { x }
pub fn outer(x: Outer) -> u32 { x.n }

// Leaf constants, which the funnel and the oracle now evaluate inside `mir_built`.
const N: usize = 3;
pub struct Leaf { a: [u8; N * 2], b: [u16; Self::LEN], c: [u8; <u32 as Bound>::MAX as usize] }
impl Leaf { pub const LEN: usize = 4; }
pub trait Bound { const MAX: Self; }
impl Bound for u32 { const MAX: u32 = 5; }
pub const fn leaf_user() -> usize {
    let _l: Option<&Leaf> = None;
    N
}
pub fn leaf(x: Leaf) -> Leaf { x }
pub fn leaf_len(x: &Leaf) -> usize { x.a.len() + x.b.len() + x.c.len() + leaf_user() }
