// Regression test for rust-lang#153596: opaque types in binder positions
// must have their implied bounds properly applied.
//
// When an opaque type appears inside a `for<'a>` binder, its lifetime
// bounds must be verified. Previously, the WF checking infrastructure
// silently dropped these bounds because they contained escaping bound
// variables after the binder was skipped.

//@ known-bug: #153596

#![feature(type_alias_impl_trait)]

use std::fmt::Debug;

// Basic case: opaque type with lifetime parameter inside a higher-ranked bound.
mod basic {
    type Opaque<'a> = impl Sized + 'a;

    fn define<'a>(x: &'a ()) -> Opaque<'a> {
        x
    }

    // This function has a where clause with an opaque type inside a binder.
    // The WF check must verify that Opaque<'a>'s bounds hold for all 'a.
    fn use_in_binder<F>(_f: F)
    where
        F: for<'a> Fn(Opaque<'a>) -> Opaque<'a>,
    {
    }
}

// Case with trait bounds on the opaque type.
mod with_trait_bound {
    use std::fmt::Debug;

    type OpaqueDebug<'a> = impl Debug + 'a;

    fn define_debug<'a>(x: &'a str) -> OpaqueDebug<'a> {
        x
    }

    fn use_debug_in_binder<F>(_f: F)
    where
        F: for<'a> Fn(OpaqueDebug<'a>),
    {
    }
}

// Case where the opaque type appears as a trait argument inside a binder.
mod as_trait_arg {
    trait Process<T> {
        fn process(&self, val: T);
    }

    type Opaque<'a> = impl Sized + 'a;

    fn define<'a>(x: &'a i32) -> Opaque<'a> {
        x
    }

    fn use_as_arg<P>(_p: P)
    where
        P: for<'a> Process<Opaque<'a>>,
    {
    }
}

fn main() {}
