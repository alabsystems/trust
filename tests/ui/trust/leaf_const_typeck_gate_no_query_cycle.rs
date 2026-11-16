//@ revisions: verify lower
//@ needs-trust-verify
//@ build-pass
//@ edition: 2021
//@[verify] compile-flags: --crate-type=lib -Ztrust-verify=on -Ztrust-policy=advisory
//@[lower] compile-flags: --crate-type=lib -Ztrust-verify=off -Ztrust-ir-lower=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE

//! **Regression (fix11, L2): deciding whether a constant is leaf must not itself start a cycling
//! query from inside `mir_built`.**
//!
//! The L2 leaf test reads `typeck` of each leaf-SHAPED body. MEASURED on the stage 1 of the
//! fix11 WIP (`1b89b91f5d` plus its uncommitted L2 edits), both revisions' flags: each shape
//! below was `error[E0391]` on valid code that stock rustc (nightly-2026-04-20) accepts, because
//! that `typeck` selected or probed a candidate whose where-clause evaluates the const fn
//! currently having its MIR built (the pre-L2 tree failed the crate too, through the MIR
//! oracle's unconditional array-length evaluation) — `building MIR for g` -> `type-checking C` -> `evaluating
//! trait selection obligation u32: Bd` -> evaluating `g()` again. `typeck` of a leaf-shaped body
//! is now asked only after everything it can select or probe was checked inert from HIR
//! (`ctfe_reentrancy::leaf_shape`); these constants are declined, and `build-pass` in both
//! revisions is the assertion.

// A trait constant whose only impl carries a constant-evaluating where-clause.
pub mod trait_where {
    pub trait Bd { const MAX: usize; }
    impl Bd for u32 where [(); g()]: Sized { const MAX: usize = 1; }
    const C: usize = <u32 as Bd>::MAX;
    pub struct S { a: [u8; C], b: u8 }
    pub const fn g() -> usize { let _s: Option<&S> = None; 1 }
    pub fn s(x: S) -> S { x }
}

// A trait constant whose trait has a blanket impl with such a where-clause (selection over
// `u32` considers it even though `u32: Marker` fails).
pub mod blanket_where {
    pub trait Marker {}
    pub trait Bd { const MAX: usize; }
    impl Bd for u32 { const MAX: usize = 1; }
    impl<T> Bd for T where [(); g()]: Sized, T: Marker { const MAX: usize = 2; }
    const C: usize = <u32 as Bd>::MAX;
    pub struct S { a: [u8; C], b: u8 }
    pub const fn g() -> usize { let _s: Option<&S> = None; 1 }
    pub fn s(x: S) -> S { x }
}

// `Type::NAME` resolved by probing an inherent impl that carries such a where-clause.
pub mod inherent_where {
    pub struct D;
    impl D where [(); k()]: Sized { pub const LEN: usize = 3; }
    pub struct S { a: [u8; D::LEN], b: u8 }
    pub const fn k() -> usize { let _s: Option<&S> = None; 1 }
    pub fn s(x: S) -> S { x }
}

// A trait constant over a local type whose impl carries such a where-clause.
pub mod local_self_where {
    pub struct D;
    pub trait HasLen { const LEN: usize; }
    impl HasLen for D where [(); k()]: Sized { const LEN: usize = 3; }
    pub struct S { a: [u8; <D as HasLen>::LEN], b: u8 }
    pub const fn k() -> usize { let _s: Option<&S> = None; 1 }
    pub fn s(x: S) -> S { x }
}
