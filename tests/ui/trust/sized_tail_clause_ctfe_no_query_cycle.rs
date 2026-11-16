//@ revisions: verify lower
//@ needs-trust-verify
//@ build-pass
//@ edition: 2021
//@[verify] compile-flags: --crate-type=lib -Ztrust-verify=on -Ztrust-policy=advisory
//@[lower] compile-flags: --crate-type=lib -Ztrust-verify=off -Ztrust-ir-lower=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE

//! **Regression (fix11 L2 review): a `Sized` where-clause over a concrete type is not inert
//! when proving it reads a struct tail that names an alias.**
//!
//! `ctfe_reentrancy::clause_is_inert` admitted every alias-free `Sized`-family bound. Proving
//! `Tail: Sized` follows `Tail`'s struct-tail chain to `<u16 as P>::S` and normalizes it, which
//! selects `impl P for u16` and confirms its where-clause `[(); h()]: Sized`, evaluating `h()`:
//! the const fn whose MIR the hook is building when the layout funnel asks. MEASURED on the
//! stage 1 of `301d35d67d`, under the default lane and both revisions' flags: each module below
//! was `error[E0391]` ("building MIR for `h`" -> "type-checking `X`" -> "evaluating trait
//! selection obligation `Tail: Sized`" -> evaluating `h()` again), through the L2 leaf gate's
//! `typeck` of a constant (or explicit discriminant) whose path names an item carrying the
//! clause. Stock rustc (nightly-2026-04-20) accepts the crate. `clause_is_inert` now reads the
//! tail chain (`sizedness_proof_reads_no_alias`), so each constant is declined and left
//! unevaluated; `controls`' clauses name no alias on their tail chains and still admit.
//! `build-pass` in both revisions is the assertion.

// An inherent impl's constant, through `Type::NAME`.
pub mod inherent {
    pub trait P { type S; }
    impl P for u16 where [(); h()]: Sized { type S = u8; }
    pub struct Tail { pub s: <u16 as P>::S }
    pub struct Dw;
    impl Dw where Tail: Sized { pub const LEN: usize = 3; }
    const X: usize = Dw::LEN;
    pub struct S2 { a: [u8; X], b: u8 }
    pub const fn h() -> usize { let _w: Option<&S2> = None; 1 }
    pub fn s2(x: S2) -> S2 { x }
}

// The clause over a tuple whose last element is the tail struct.
pub mod tuple_tail {
    pub trait P { type S; }
    impl P for u16 where [(); h()]: Sized { type S = u8; }
    pub struct Tail { pub s: <u16 as P>::S }
    pub struct Dw;
    impl Dw where (u8, Tail): Sized { pub const LEN: usize = 3; }
    const X: usize = Dw::LEN;
    pub struct S2 { a: [u8; X], b: u8 }
    pub const fn h() -> usize { let _w: Option<&S2> = None; 1 }
    pub fn s2(x: S2) -> S2 { x }
}

// An explicit discriminant through the same inherent impl.
pub mod discriminant {
    pub trait P { type S; }
    impl P for u16 where [(); h()]: Sized { type S = u8; }
    pub struct Tail { pub s: <u16 as P>::S }
    pub struct Dw;
    impl Dw where Tail: Sized { pub const LEN: isize = 3; }
    pub enum E { A = Dw::LEN, B }
    pub const fn h() -> usize { let _w: Option<&E> = None; 1 }
    pub fn e(x: E) -> E { x }
}

// A trait constant whose trait carries the clause.
pub mod trait_where {
    pub trait P { type S; }
    impl P for u16 where [(); h()]: Sized { type S = u8; }
    pub struct Tail { pub s: <u16 as P>::S }
    pub trait Bd where Tail: Sized { const M: usize; }
    impl Bd for u32 { const M: usize = 2; }
    const X: usize = <u32 as Bd>::M;
    pub struct S2 { a: [u8; X], b: u8 }
    pub const fn h() -> usize { let _w: Option<&S2> = None; 1 }
    pub fn s2(x: S2) -> S2 { x }
}

// Controls: `Sized` clauses whose tail chains name no alias (`Plain`'s tail is a `u8`;
// `Gen<u8>`'s is its parameter, instantiated `u8`).
pub mod controls {
    pub struct Plain { pub a: u16, pub b: u8 }
    pub struct Gen<T> { pub t: T }
    pub struct Dw;
    impl Dw where Plain: Sized, Gen<u8>: Sized { pub const LEN: usize = 3; }
    const X: usize = Dw::LEN;
    pub struct S2 { a: [u8; X], b: u8 }
    pub const fn h() -> usize { let _w: Option<&S2> = None; 1 }
    pub fn s2(x: S2) -> S2 { x }
}
