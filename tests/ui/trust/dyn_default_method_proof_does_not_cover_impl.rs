//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! Trust (2026-09-14): a trait DEFAULT method's panic-freedom proof must never be
//! read through a `dyn Trait` VIRTUAL call.
//!
//! `collect_proven_total_panic_free_callees` licenses a monomorphized call key
//! against the R43 parametric registry only when the call "resolves to the
//! registered body", pinned as `Instance::try_resolve(..).def_id() ==
//! callee_def_id`. For a `dyn` receiver `try_resolve` answers
//! `InstanceKind::Virtual(trait_method, slot)`, whose `def_id()` IS the trait
//! method's — so a virtual call passed the pin on the strength of the DEFAULT
//! body (`{ 0 }`, trivially panic-free and therefore parametric), the bridge's
//! no-obligation arm consumed it, and `use_widget` verified strict-clean while
//! the vtable it dispatches through holds `Bomb::rank`, which panics.
//!
//! The pin now also requires `InstanceKind::Item`. Both functions below must
//! fail strict: `Bomb::rank` on its own reachable panic, and `use_widget` on the
//! honest absent-callee obligation of a dynamic dispatch whose target Trust
//! declines to pick. Losing the `use_widget` error is the false proof coming back.

mod sealed {
    pub trait Widget {
        fn rank(&self) -> i32 {
            0
        }
    }
}

use sealed::Widget;

pub struct Bomb;
impl Widget for Bomb {
    fn rank(&self) -> i32 {
        //~^ ERROR Trust Level 0 safety verification incomplete for
        //~| ERROR Trust strict verification failed for
        panic!("the vtable holds THIS body, not the trait default")
    }
}

pub fn use_widget(w: &dyn Widget) -> i32 {
    //~^ ERROR Trust strict verification failed for `dyn_default_method_proof_does_not_cover_impl::use_widget`
    w.rank()
}

pub fn make() -> Box<dyn Widget> {
    Box::new(Bomb)
}
