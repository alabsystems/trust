//@ needs-trust-verify
//@ edition: 2021
//@ revisions: default_leaf blanket_leaf default_oob override_panics two_selfs requires_violated assume_total_default specialization polymorphic_recursion name_collision fn_name_collision param_independent self_size_index self_const_index
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[default_leaf] check-pass
//@[default_leaf] forbid-output: concrete_default_and_blanket_calls::a_is_zero`
//@[blanket_leaf] check-pass
//@[blanket_leaf] forbid-output: concrete_default_and_blanket_calls::blanket`
//@[default_oob] check-fail
//@[override_panics] check-fail
//@[two_selfs] check-fail
//@[requires_violated] check-fail
//@[assume_total_default] check-fail
//@[specialization] check-fail
//@[polymorphic_recursion] check-fail
//@[name_collision] check-fail
//@[fn_name_collision] check-fail
//@[param_independent] check-pass
//@[self_size_index] check-fail
//@[self_const_index] check-fail
//! Lane T (2026-10-09): a CONCRETE call to a local trait method that resolves to the
//! trait's provided default (`a.w()` with `Self = Apple`) or to a generic/blanket
//! impl's method is bundled per instance (`local_trait_call_mono_target`). Before, no
//! lane bundled that instance and the call was an absent callee.
//! * `default_leaf` (the sweep's m13 shape): the CALLER `a_is_zero` verifies (pinned by
//!   `forbid-output`; with `TRUST_NO_BUNDLE_LOCAL_TRAIT_MONO=1` it is refused); the
//!   generic default `Score::is_zero` itself stays refused as its own root (D18).
//! * `blanket_leaf`: the CALLER `blanket` verifies (annotated as not erroring); the
//!   generic blanket body itself stays refused as its own root (DECISION_QUEUE D18),
//!   which is why the revision is check-fail.
//! RE-PINNED 2026-10-15 (the merge of 2026-10-14): both revisions now build. The
//! generic body is no longer refused as its own root: main's OD-1 instance hypothesis
//! publishes its open-trait dispatch as one `assumed (instance discharge)` row ("ASSUMED
//! per instance, not proved"; conditional evidence, never credit), which the default
//! policy reports as an advisory warning (measured on the merged stage 1:
//! `Score::is_zero` and `<T as Desc>::d` each `1 proved, 1 assumed`). That is not the
//! premise D18 (now D99) declined — no impl's verdict is charged as a proof — and the
//! callers' `forbid-output` pins still hold.
//! Every other revision is a caller that really panics and must stay refused:
//! an out-of-bounds default (its member Assert is charged exactly or refused), a
//! panicking generic-impl override chosen over a total default, one default at two
//! `Self` types where only one indexes out of bounds, a `requires` the call breaks,
//! an `assume_total` default (never bundled), a crate with `specialization`, and
//! polymorphic recursion (declined by the instantiation budget, no ICE).
//! `name_collision` and `fn_name_collision` (review round 91): a fn-scoped `S` inside
//! `fn host` and the module `host::S` render ONE member name, and the second call bound
//! to the first instance's total body while its own overflows (measured: the binary
//! panicked). The collector now keys on the instance and the drain poisons a name two
//! distinct instances share, so the caller keeps its refusal. `fn_name_collision` is
//! the same shape through a generic free fn, which had the hole before lane T.
//! `param_independent` (sweep m15): a default whose body uses nothing of `Self` (a
//! call and a guarded bounds assert) is decided by the R43 parametric registry from
//! its generic proof, now that the shape test admits parameter-free `Assert`/`Call`
//! terminators; lane T defers to it. `self_size_index` (`a[size_of::<Self>()]`) and
//! `self_const_index` (`a[Self::K]`) depend on `Self` and stay refused.
//! Accepted cost (review round 92): two closures expanded from ONE macro render one
//! `{closure@file:L:C}` member name, so a generic fn called with both is poisoned and its
//! caller refused, even when both closures are correct.
#![cfg_attr(specialization, feature(specialization))]
#![cfg_attr(specialization, allow(incomplete_features))]

#[cfg(default_leaf)]
pub trait Score {
    fn score(&self) -> u8;
    fn is_zero(&self) -> bool {
        self.score() == 0
    }
}
#[cfg(default_leaf)]
pub struct A(pub u8);
#[cfg(default_leaf)]
impl Score for A {
    fn score(&self) -> u8 {
        self.0
    }
}
#[cfg(default_leaf)]
pub fn a_is_zero(a: &A) -> bool {
    a.is_zero()
}

#[cfg(blanket_leaf)]
pub trait Tag {
    fn tag(&self) -> u8;
}
#[cfg(blanket_leaf)]
pub trait Desc {
    fn d(&self) -> u8;
}
#[cfg(blanket_leaf)]
impl<T: Tag> Desc for T {
    fn d(&self) -> u8 {
        self.tag()
    }
}
#[cfg(blanket_leaf)]
pub struct Item;
#[cfg(blanket_leaf)]
impl Tag for Item {
    fn tag(&self) -> u8 {
        3
    }
}
#[cfg(blanket_leaf)]
pub fn blanket(i: &Item) -> u8 {
    i.d()
}

#[cfg(default_oob)]
pub trait Tr {
    fn d(&self, a: &[u8; 4], i: usize) -> u8 {
        a[i]
    }
}
#[cfg(default_oob)]
pub struct A;
#[cfg(default_oob)]
impl Tr for A {}
#[cfg(default_oob)]
pub fn caller(x: &A, a: &[u8; 4]) -> u8 {
    //[default_oob]~^ ERROR Trust strict verification failed for `concrete_default_and_blanket_calls::caller`
    x.d(a, 9)
}

#[cfg(override_panics)]
pub trait G {
    fn g(&self) -> u8 {
        1
    }
}
#[cfg(override_panics)]
pub struct Wrap<T>(pub T);
#[cfg(override_panics)]
impl<T> G for Wrap<T> {
    fn g(&self) -> u8 {
        let a = [0u8; 2];
        a[5 % 7]
    }
}
#[cfg(override_panics)]
pub fn caller(w: &Wrap<u8>) -> u8 {
    //[override_panics]~^ ERROR Trust full verification failed for `concrete_default_and_blanket_calls::caller`
    w.g()
}

#[cfg(two_selfs)]
pub trait Sz: Sized {
    fn n(&self) -> usize {
        std::mem::size_of::<Self>()
    }
}
#[cfg(two_selfs)]
impl Sz for u8 {}
#[cfg(two_selfs)]
impl Sz for u64 {}
#[cfg(two_selfs)]
pub fn caller(a: &[u8; 4]) -> u8 {
    //[two_selfs]~^ ERROR Trust
    a[0u8.n()] + a[0u64.n()]
}

#[cfg(requires_violated)]
pub trait Rq {
    #[trust::requires(i < 4)]
    fn at(&self, a: &[u8; 4], i: usize) -> u8 {
        a[i]
    }
}
#[cfg(requires_violated)]
pub struct R;
#[cfg(requires_violated)]
impl Rq for R {}
#[cfg(requires_violated)]
pub fn caller(r: &R, a: &[u8; 4]) -> u8 {
    //[requires_violated]~^ ERROR Trust
    r.at(a, 9)
}

#[cfg(assume_total_default)]
pub trait At {
    #[trust::assume_total]
    fn v(&self) -> u8 {
        200
    }
}
#[cfg(assume_total_default)]
pub struct V;
#[cfg(assume_total_default)]
impl At for V {}
#[cfg(assume_total_default)]
pub fn caller(v: &V) -> u8 {
    //[assume_total_default]~^ ERROR Trust
    v.v() + 100
}

#[cfg(specialization)]
pub trait Sp {
    fn s(&self) -> u8;
}
#[cfg(specialization)]
impl<T> Sp for T {
    default fn s(&self) -> u8 {
        let a = [0u8; 1];
        a[3 % 5]
    }
}
#[cfg(specialization)]
pub fn caller(x: &u32) -> u8 {
    //[specialization]~^ ERROR Trust
    x.s()
}

#[cfg(polymorphic_recursion)]
pub struct Nest<T>(pub T);
#[cfg(polymorphic_recursion)]
pub trait Deep {
    fn depth(&self, n: u32) -> u32;
}
#[cfg(polymorphic_recursion)]
impl<T> Deep for Nest<T> {
    fn depth(&self, n: u32) -> u32 {
        if n == 0 { 0 } else { Nest(self).depth(n - 1) + 1 }
    }
}
#[cfg(polymorphic_recursion)]
pub fn caller(x: &Nest<u8>) -> u32 {
    //[polymorphic_recursion]~^ ERROR Trust
    x.depth(3)
}

#[cfg(name_collision)]
pub trait Tr2 {
    fn a(&self, x: usize) -> usize {
        self.b(x)
    }
    fn b(&self, x: usize) -> usize;
}
#[cfg(name_collision)]
pub mod host {
    pub struct S;
    impl super::Tr2 for S {
        fn b(&self, x: usize) -> usize {
            x / 3
        }
    }
}
#[cfg(name_collision)]
pub fn host(m: &crate::host::S, x: usize) -> usize {
    //[name_collision]~^ ERROR Trust
    struct S;
    impl Tr2 for S {
        fn b(&self, x: usize) -> usize {
            x + 1
        }
    }
    m.a(x) / 2 + S.a(x) / 2
}

#[cfg(fn_name_collision)]
pub trait Tr3 {
    fn b(&self, x: usize) -> usize;
}
#[cfg(fn_name_collision)]
pub fn a<T: Tr3>(t: &T, x: usize) -> usize {
    t.b(x)
}
#[cfg(fn_name_collision)]
pub mod host {
    pub struct S;
    impl super::Tr3 for S {
        fn b(&self, x: usize) -> usize {
            x / 3
        }
    }
}
#[cfg(fn_name_collision)]
pub fn host(m: &crate::host::S, x: usize) -> usize {
    //[fn_name_collision]~^ ERROR Trust
    struct S;
    impl Tr3 for S {
        fn b(&self, x: usize) -> usize {
            x + 1
        }
    }
    a(m, x) / 2 + a(&S, x) / 2
}

#[cfg(param_independent)]
pub trait Head {
    fn head(&self, a: &[u8]) -> u8 {
        if a.is_empty() { 0 } else { a[0] }
    }
}
#[cfg(param_independent)]
pub struct H;
#[cfg(param_independent)]
impl Head for H {}
#[cfg(param_independent)]
pub fn head_of(x: &H, a: &[u8]) -> u8 {
    x.head(a)
}

#[cfg(self_size_index)]
pub trait Sz2: Sized {
    fn at(&self, a: &[u8; 4]) -> u8 {
        a[std::mem::size_of::<Self>()]
    }
}
#[cfg(self_size_index)]
impl Sz2 for u64 {}
#[cfg(self_size_index)]
pub fn caller(x: &u64, a: &[u8; 4]) -> u8 {
    //[self_size_index]~^ ERROR Trust
    x.at(a)
}

#[cfg(self_const_index)]
pub trait Kc {
    const K: usize;
    fn get(&self, a: &[u8; 4]) -> u8 {
        a[Self::K]
    }
}
#[cfg(self_const_index)]
pub struct Big;
#[cfg(self_const_index)]
impl Kc for Big {
    const K: usize = 9;
}
#[cfg(self_const_index)]
pub fn caller(x: &Big, a: &[u8; 4]) -> u8 {
    //[self_const_index]~^ ERROR Trust
    x.get(a)
}
