//@ revisions: default certify
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@[default] check-pass
//@[certify] check-fail
//@ dont-check-compiler-stderr
//! DEP-SEAL-1, macros-2.0 residual, under compiletest: a def-site-hygienic macro
//! opens both LANGUAGE-VISIBILITY routes of `trait_impl_set_is_closed_world` (a trait
//! that is not exported; the sealed-trait idiom's private supertrait). The compiletest
//! twin of `tests/open-dispatch-ladder/w14_macro2_*`.
//!
//! A `pub macro` resolves its own paths at its definition site, with that site's
//! privacy, wherever it is invoked. So `pub macro seal($t:ty) { impl private::Sealed
//! for $t {} }` lets a downstream crate write `a::seal!(Bad); impl a::T for Bad { … }`,
//! and `pub macro imp(..) { impl private::T for $t { … } }` lets it implement a trait
//! no `use` exports. `effective_visibilities().is_exported` does not see that reach.
//! The fix (`crate_defines_def_site_macro`, DECISION_QUEUE SEAL-SUPERTRAIT-1) is
//! crate-wide: any macros-2.0 `macro`, or any macro with `#[rustc_macro_transparency]`,
//! drops both routes for every trait of the crate. That is why this file holds no
//! control: the classic idiom without such a macro is the `classic` and
//! `classic_macro_rules` modules of `private_supertrait_seal_needs_a_closed_impl_set.rs`.
//!
//! BEFORE (the stage 1 of `76a6ea45b2`, `scratchpad/stage1-w14`, measured
//! 2026-10-05 on this file under each revision's flags): `TRUST_RUNG2_PROBE=1`
//! printed `sealedness=Sealed` for `supertrait::T` and `not_exported::private::T`
//! (the Φ module prints no probe line), `f` carried no hypothesis row, and both
//! revisions built exit 0 with no diagnostic, so none of the annotations below fired.
//! A verify-off downstream that went through the macro and implemented the trait
//! with a panicking `m` panicked inside the certified `f` (exit 101; the same shapes
//! as the ladder rows, each built alone as crate `a`).
//!
//! AFTER (the stage 1 built from this change on `40d62538d9`, measured 2026-10-05,
//! `x.py test --stage 1`): every trait is `Open`; `f` carries one
//! `assumption:instance-hypothesis` row (the advisory warning under the default
//! policy, exit 0, hence `check-pass` there) and certify refuses it.
#![feature(decl_macro, register_tool)]
#![register_tool(trust)]
#![allow(private_bounds)]

pub mod supertrait {
    mod private {
        pub trait Sealed {}
        impl Sealed for super::Good {}
    }
    pub trait T: private::Sealed {
        fn m(&self) -> u32;
    }
    pub struct Good;
    impl T for Good {
        fn m(&self) -> u32 {
            7
        }
    }
    pub fn f<K: T>(x: &K) -> u32 {
        //[default]~^ WARN Trust verification advisory
        //[certify]~^^ ERROR Trust certify verification failed
        x.m()
    }
    pub macro seal($t:ty) {
        impl private::Sealed for $t {}
    }
}

pub mod supertrait_phi {
    mod private {
        pub trait Sealed {}
        impl Sealed for super::Good {}
    }
    pub trait T: private::Sealed {
        #[trust::panic_free]
        fn m(&self) -> u32;
    }
    pub struct Good;
    impl T for Good {
        fn m(&self) -> u32 {
            7
        }
    }
    pub fn f<K: T>(x: &K) -> u32 {
        //[default]~^ WARN Trust verification advisory
        //[certify]~^^ ERROR Trust certify verification failed
        x.m()
    }
    pub macro seal($t:ty) {
        impl private::Sealed for $t {}
    }
}

pub mod not_exported {
    mod private {
        pub trait T {
            fn m(&self) -> u32;
        }
    }
    pub struct Good;
    impl private::T for Good {
        fn m(&self) -> u32 {
            7
        }
    }
    pub fn f<K: private::T>(x: &K) -> u32 {
        //[default]~^ WARN Trust verification advisory
        //[certify]~^^ ERROR Trust certify verification failed
        x.m()
    }
    pub macro imp($t:ty, $v:expr) {
        impl private::T for $t {
            fn m(&self) -> u32 {
                $v
            }
        }
    }
}
