//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
//! A RECURSIVE enum's uninhabited variant does not reach the `otherwise ->
//! Unreachable` arm rustc emits for it.
//!
//! `T<X>` mirrors trust-ir-conformance's `TyG<X>` (`subset.rs`, `ty_name`): one
//! variant is recursive and `Ext(X)` is instantiated at the empty `NoExt`. rustc
//! drops the dead arm from the `SwitchInt` (`[0, 1], otherwise -> Unreachable`), so
//! the code is correct; measured on a stage1 of main 7be75e9a80 it was reported
//!
//!     [unreach] FAILED (ay-in-process); counterexample: _2 = 2
//!
//! for `B(Box<T<X>>)` and `B(Vec<T<X>>)`, while `B(Box<u8>)`, `B(Box<X>)` and
//! `B(Option<X>)` proved. A recursive enum is spelled as a bare by-name datatype
//! marker at its use site, and the discriminant-domain fact read the marker (which
//! carries no variants) instead of the body's table definition, so no domain fact
//! was published at all.
//!
//! THE STRICT BUILD IS THE ASSERTION: a refuted row fails this file. The
//! fail-closed half — a LIVE sibling variant's reachable `unreachable!()` and an
//! INHABITED `Ext(u8)` both stay refuted at their live tags, and a marker the table
//! does not define (or defines for another instantiation) publishes nothing — is
//! pinned in trust-vcgen (`tests/uninhabited_recursive_arm_realmir.rs` and
//! `src/generate/uninhabited_variant_tests.rs`).
pub enum NoExt {}

impl NoExt {
    pub fn unreachable(&self) -> ! {
        match *self {}
    }
}

pub enum T<X> {
    A,
    B(Box<T<X>>),
    Ext(X),
}

pub fn name(t: &T<NoExt>) -> &'static str {
    match t {
        T::A => "A",
        T::B(_) => "B",
        T::Ext(e) => e.unreachable(),
    }
}

pub enum V<X> {
    A,
    B(Vec<V<X>>),
    Ext(X),
}

pub fn vname(t: &V<NoExt>) -> &'static str {
    match t {
        V::A => "A",
        V::B(_) => "B",
        V::Ext(e) => e.unreachable(),
    }
}
