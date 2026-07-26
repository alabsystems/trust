// Regression test for rust-lang#132991: unsizing coercion with deep trait
// hierarchies should not hang the compiler. The coercion queue previously
// grew without bound because nested obligations could generate predicates
// equivalent to ones already processed. The fix deduplicates obligations
// before enqueuing them.
//
// Trust: This test exercises the obligation deduplication in
// coerce_unsized_old_solver (compiler/rustc_hir_typeck/src/coercion.rs).

//@ check-pass

#![feature(unsize, coerce_unsized)]

use std::ops::CoerceUnsized;
use std::marker::Unsize;

// Build a deep trait hierarchy that generates repeated obligations
// during unsizing coercion.

trait Base {}
trait Level1: Base {}
trait Level2: Level1 {}
trait Level3: Level2 {}
trait Level4: Level3 {}
trait Level5: Level4 {}
trait Level6: Level5 {}
trait Level7: Level6 {}
trait Level8: Level7 {}

struct Wrapper<T: ?Sized> {
    inner: *const T,
}

impl<T: ?Sized + Unsize<U>, U: ?Sized> CoerceUnsized<Wrapper<U>> for Wrapper<T> {}

struct Concrete;
impl Base for Concrete {}
impl Level1 for Concrete {}
impl Level2 for Concrete {}
impl Level3 for Concrete {}
impl Level4 for Concrete {}
impl Level5 for Concrete {}
impl Level6 for Concrete {}
impl Level7 for Concrete {}
impl Level8 for Concrete {}

fn accept_dyn_base(_: Wrapper<dyn Base>) {}
fn accept_dyn_level4(_: Wrapper<dyn Level4>) {}
fn accept_dyn_level8(_: Wrapper<dyn Level8>) {}

fn main() {
    let c = Concrete;

    // These coercions traverse the trait hierarchy during unsizing.
    // Without deduplication, they could cause the coercion queue to
    // grow exponentially.
    let _: Wrapper<dyn Base> = Wrapper { inner: &c };
    let _: Wrapper<dyn Level4> = Wrapper { inner: &c };
    let _: Wrapper<dyn Level8> = Wrapper { inner: &c };

    accept_dyn_base(Wrapper { inner: &c });
    accept_dyn_level4(Wrapper { inner: &c });
    accept_dyn_level8(Wrapper { inner: &c });
}
