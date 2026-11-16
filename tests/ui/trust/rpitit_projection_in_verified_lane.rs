//@ revisions: off adv strict
//@ needs-trust-verify
//@ edition: 2021
//@[off] compile-flags: -Ztrust-verify=off
//@[adv] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory
//@[strict] compile-flags: -Ztrust-verify=on -Ztrust-policy=strict
//@[off] check-pass
//@[adv] check-pass
//@[strict] check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ forbid-output: internal compiler error
//@ forbid-output: item_name: no name
//! A return-position `impl Trait` in a trait (RPITIT) whose synthetic associated type
//! reaches the trust-ir producer as a projection: `tests/ui/impl-trait/in-trait/reveal.rs`
//! (stable: an impl refining `fn f() -> Box<impl Sized>` to `Box<String>`, called through
//! the trait) and `tests/ui/delegation/impl-trait.rs` (`reuse <S as Trait>::bar` gives the
//! reused function a signature naming `<S as Trait>::{synthetic#0}`).
//!
//! Drop-in (release gate): stock rustc accepts both (`//@ check-pass` upstream). On
//! `origin/main` `93f05556da` and `d36c551fac` the verified lanes ICEd on each: the THIR
//! producer's `projection_reaches_opaque` looked the projection's associated item up by
//! NAME (`item_name`), and the synthetic item has none (`bug!: item_name: no name for ...
//! AnonAssocTy("f")` / `AnonAssocTy("bar")`). Such an item is an opaque in every impl by
//! construction, so the check now answers "reaches an opaque" for it without a name.

#![feature(fn_delegation)]

mod to_reuse {
    pub fn foo() -> impl Clone {
        0
    }
}

reuse to_reuse::foo;

trait Trait {
    fn bar() -> impl Clone {
        1
    }
}

struct S;
impl Trait for S {}

impl S {
    reuse to_reuse::foo;
    // ZERO-ROW-GATE (2026-10-10) refused `S::bar` here; R43-ZERO-ROW-PARITY (2026-10-13): accepted
    // again: the delegated call resolves to the trait default `Trait::bar` itself, whose body
    // (`1`) holds no panic-capable terminator, so the R43 parametric premises discharge it.
    reuse <S as Trait>::bar;
}

pub trait Foo {
    fn f() -> Box<impl Sized>;
}

impl Foo for () {
    #[expect(refining_impl_trait)]
    fn f() -> Box<String> {
        Box::new(String::new())
    }
}

fn main() {
    foo().clone();
    <S>::bar().clone();
    let _x: Box<String> = <() as Foo>::f();
}
