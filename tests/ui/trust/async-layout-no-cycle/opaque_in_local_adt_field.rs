//@ revisions: off by_value atpit enum_param returns_inner option_param tuple_param
//@ revisions: array_param ref_enum_match slice_match freeze_arg bounded_resolve
//@ revisions: projection_chain generic_call
//@ needs-trust-verify
//@ edition: 2024
//@ compile-flags: --crate-type lib
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory
//@[off] compile-flags: -Ztrust-verify=off
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ forbid-output: E0391
//@ forbid-output: cycle detected
//@ forbid-output: error[E
//! A type-alias- or associated-type-`impl Trait` that sits in a FIELD of a local ADT,
//! used inside the opaque's defining scope.
//!
//! Drop-in (release gate): stock rustc accepts this crate (`off` compiles every shape),
//! and so does the verified lane, one shape per revision. On `origin/main` `93f05556da`
//! every revision but `projection_chain` was E0391 under advisory and strict. The
//! trust-ir producer runs inside `mir_built`, which `type_of` of the opaque reaches
//! (borrowck of the defining body), and it asked `needs_drop(Inner)` in the codegen
//! typing mode: `struct Inner { a: u32, x: Option<X> }` carries no alias flag, so the
//! flag guard waved it through, and `needs_drop` normalized the field and revealed `X`
//! (`check_type_wf` -> `type_of(X)` -> `mir_borrowck(define)` -> `mir_built` -> the
//! producer -> `needs_drop(Inner)` -> `normalizing X`). The same hidden field reaches
//! `is_copy`, `layout_of` (also under a foreign ADT, a tuple or an array, which the deep
//! guard used to look past), a by-ref enum binding's offset, a slice pattern's element
//! size, `Freeze` of a call argument, and a selection whose impl bounds the field type.
//! Every type query the producer and its MIR oracle ask inside `mir_built` now goes
//! through the reveal funnel (`trust_mir_extract::ctfe_reentrancy`): the analysis
//! typing mode `rustc_mir_build` itself uses for `needs_drop`, `Copy`, `Sized` and
//! normalization, and the deep guard for `layout_of`, resolution and `Freeze`.
//! `projection_chain` (a projection whose impl writes another projection that ends at
//! the opaque, which the flag guards cannot see through) did not cycle on `93f05556da`;
//! it pins the chain that normalizing in the analysis mode inside `mir_built` closes by
//! construction.

#![cfg_attr(not(any(atpit, projection_chain)), feature(type_alias_impl_trait))]
#![cfg_attr(any(off, atpit, projection_chain), feature(impl_trait_in_assoc_type))]
#![allow(dead_code, unused)]

#[cfg(not(any(atpit, projection_chain)))]
mod tait {
    pub trait Tr {}
    impl Tr for u32 {}
    pub type X = impl Tr + Send;
    pub struct Inner {
        pub a: u32,
        pub x: Option<X>,
    }
    pub enum E {
        A(u32),
        B(Option<X>),
    }
    fn take(i: &Inner) -> u32 {
        i.a
    }
    fn id<T>(t: T) -> T {
        t
    }
    pub trait Bounded {
        fn m(&self) -> u32;
    }
    impl<T: Send> Bounded for Option<T> {
        fn m(&self) -> u32 {
            1
        }
    }

    #[define_opaque(X)]
    pub fn define() -> X {
        #[cfg(any(off, by_value))]
        {
            let c = |i: Inner| i.a;
            let _ = c(Inner { a: 1, x: None });
        }
        #[cfg(any(off, enum_param))]
        {
            let d = |e: E| match e {
                E::A(_) => 1u32,
                E::B(_) => 2,
            };
            let _ = d(E::A(1));
        }
        #[cfg(any(off, returns_inner))]
        {
            let r = |a: u32| Inner { a, x: None };
            let _ = r(1).a;
        }
        #[cfg(any(off, option_param))]
        {
            let o = |i: Option<Inner>| i.map(|i| i.a);
            let _ = o(None);
        }
        #[cfg(any(off, tuple_param))]
        {
            let t = |p: (Inner, u32)| p.1;
            let _ = t((Inner { a: 1, x: None }, 2));
        }
        #[cfg(any(off, array_param))]
        {
            let t = |p: [Inner; 1]| 3u32;
            let _ = t([Inner { a: 1, x: None }]);
        }
        #[cfg(any(off, ref_enum_match))]
        {
            let m = |e: &E| match e {
                E::A(n) => *n,
                E::B(_) => 2,
            };
            let _ = m(&E::A(1));
        }
        #[cfg(any(off, slice_match))]
        {
            let s = |v: &[Inner]| match v {
                [first, ..] => first.a,
                _ => 0,
            };
            let _ = s(&[]);
        }
        #[cfg(any(off, freeze_arg))]
        {
            let i = Inner { a: 1, x: None };
            let _ = take(&i);
            let f = |n: u32| {
                let i = Inner { a: n, x: None };
                take(&i)
            };
            let _ = f(1);
        }
        #[cfg(any(off, bounded_resolve))]
        {
            let c = |o: Option<Inner>| o.m();
            let _ = c(None);
        }
        #[cfg(any(off, generic_call))]
        {
            let c = |i: Inner| id(i).a;
            let _ = c(Inner { a: 1, x: None });
        }
        5u32
    }
}

#[cfg(any(off, atpit))]
mod atpit {
    pub trait P: Sized {
        type C;
        fn start(ctx: Ctx<Self>) -> Self::C;
    }
    pub struct Ctx<G: P> {
        pub a: u32,
        pub link: Option<G::C>,
    }
    impl P for () {
        type C = impl Sized;
        fn start(ctx: Ctx<Self>) -> Self::C {
            let f = |c: Ctx<()>| c.a;
            f(ctx)
        }
    }
}

#[cfg(any(off, projection_chain))]
mod projection_chain {
    pub trait Q {
        type D;
        fn d() -> Self::D;
    }
    pub trait P {
        type C;
    }
    impl P for () {
        type C = <() as Q>::D;
    }
    impl Q for () {
        type D = impl Sized;
        fn d() -> Self::D {
            let c = |x: Option<<() as P>::C>| 1u32;
            let _ = c(None);
            5u32
        }
    }
}
