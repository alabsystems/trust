//@ revisions: default certify
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@[default] check-fail
//@[certify] check-fail
//@ dont-check-compiler-stderr
//! ZERO-ROW-GATE AMENDMENT (2026-10-10, docs/DECISION_QUEUE.md ZERO-ROW-GATE): the control modules `classic` and
//! `classic_macro_rules` keep their seal (no WARN, no instance-hypothesis row), but
//! each `f` now carries one ERROR from the zero-row gate: the sealed dispatch leaves no
//! obligation and no authenticated registry discharges the call, so the body publishes
//! an `unknown` row. The `default` revision is therefore check-fail, and "carries no
//! annotation" / "check-pass there" below are superseded for those two bodies. The
//! seal/open differential is still the exhaustive WARN set.
//!
//! DEP-SEAL-1 under compiletest: a PRIVATE supertrait seals an exported trait in a
//! library only when no downstream type can satisfy it (`private_supertrait_seals`,
//! DECISION_QUEUE SEAL-SUPERTRAIT-1). One module per shape of
//! `tests/open-dispatch-ladder/w14_*`, so this file is the compiletest twin of those
//! ladder rows, which the ladder script checks under its own flags only.
//!
//! Each lie module opens its seal for a downstream crate: a blanket impl of the
//! private `Sealed`, an impl for `Box<X>` or `&X` (fundamental wrappers, so
//! `impl a::T for Box<Local>` passes the orphan rule downstream), a generic `T<P>`
//! (`impl a::T<Local> for a::Good`), a private trait alias or a private auto trait.
//! `f<K: T>` calls `x.m()` through that trait, so once the seal is refused the call
//! is OPEN generic dispatch: OD-1 admits it as an `assumption:instance-hypothesis`
//! row (a CONDITIONAL result, a warning under the default policy) and certify
//! refuses it.
//!
//! BEFORE (the stage 1 of main `d5da8dc314`, which carries OD-1, measured
//! 2026-10-05; the wave-13 stage 1 of `4463aeeb6d`, without OD-1, the same): every
//! module's trait was `Sealed`, so `f` carried a whole-definition certificate with
//! no hypothesis row, and both revisions built exit 0 with no diagnostic: none of
//! the annotations below fired (the default revision's eight WARNs missing, the
//! certify revision compiling where it must fail). A verify-off downstream that
//! implemented `T` with a panicking `m` panicked inside the certified `f` (exit
//! 101; the ladder rows' measurement, repeated on that stage 1 with the wave-14
//! scout's probes).
//!
//! AFTER (the stage 1 of `76a6ea45b2`, wave 14, measured 2026-10-05): every lie
//! module's trait is `Open`; `f` carries one instance-hypothesis row (default: the
//! advisory warning, exit 0, hence `check-pass` there) and certify refuses it. The control module `classic` (`Sealed`
//! implemented for `Good` and `&'a Good` only, `T` without a type parameter) keeps
//! its seal in both revisions and carries no annotation. So does `classic_macro_rules`
//! (added 2026-10-05): the same idiom beside an exported `macro_rules!` that names the
//! private supertrait, which a downstream crate cannot use to open it (E0603); a
//! def-site-hygienic `pub macro` can, and is
//! `def_site_macro_opens_a_language_visibility_seal.rs`.
#![feature(register_tool, trait_alias, auto_traits)]
#![register_tool(trust)]

pub mod blanket {
    mod private {
        pub trait Sealed {}
        impl<X: ?Sized> Sealed for X {}
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
}

pub mod blanket_phi {
    mod private {
        pub trait Sealed {}
        impl<X: ?Sized> Sealed for X {}
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
}

pub mod boxed {
    mod private {
        pub trait Sealed {}
        impl Sealed for super::Good {}
        impl<X: ?Sized> Sealed for Box<X> {}
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
}

pub mod by_ref {
    mod private {
        pub trait Sealed {}
        impl Sealed for super::Good {}
        impl<X: ?Sized> Sealed for &X {}
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
}

pub mod generic {
    mod private {
        pub trait Sealed {}
        impl Sealed for super::Good {}
    }
    pub trait T<P>: private::Sealed {
        fn m(&self) -> u32;
    }
    pub struct Good;
    impl T<u8> for Good {
        fn m(&self) -> u32 {
            7
        }
    }
    pub fn f<P, K: T<P>>(x: &K) -> u32 {
        //[default]~^ WARN Trust verification advisory
        //[certify]~^^ ERROR Trust certify verification failed
        x.m()
    }
}

pub mod generic_phi {
    mod private {
        pub trait Sealed {}
        impl Sealed for super::Good {}
    }
    pub trait T<P>: private::Sealed {
        #[trust::panic_free]
        fn m(&self) -> u32;
    }
    pub struct Good;
    impl T<u8> for Good {
        fn m(&self) -> u32 {
            7
        }
    }
    pub fn f<P, K: T<P>>(x: &K) -> u32 {
        //[default]~^ WARN Trust verification advisory
        //[certify]~^^ ERROR Trust certify verification failed
        x.m()
    }
}

pub mod alias {
    mod private {
        pub trait Sealed = Clone;
    }
    pub trait T: private::Sealed {
        fn m(&self) -> u32;
    }
    #[derive(Clone)]
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
}

pub mod auto {
    mod private {
        pub auto trait Sealed {}
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
}

// Control: the classic idiom keeps its seal (no annotation in either revision).
pub mod classic {
    mod private {
        pub trait Sealed {}
        impl Sealed for super::Good {}
        impl<'a> Sealed for &'a super::Good {}
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
    // ZERO-ROW-GATE (2026-10-10): zero bridged obligations plus a call no authenticated registry discharges publish an `unknown` row; refused.
    //[certify,default]~v ERROR Trust strict verification failed for `private_supertrait_seal_needs_a_closed_impl_set::classic::f`
    pub fn f<K: T>(x: &K) -> u32 {
        x.m()
    }
}

// Control (2026-10-05, the macros-2.0 residual): the classic idiom beside an exported
// `macro_rules!` that names the private supertrait keeps its seal. A `macro_rules!`
// is semi-transparent: `$crate::classic_macro_rules::private::Sealed` in a downstream
// expansion resolves at the call site and is E0603 there, so it opens nothing, and
// `crate_defines_def_site_macro` does not count it. A `pub macro` in this file would
// drop the language-visibility routes for every module of the crate; that shape is
// `def_site_macro_opens_a_language_visibility_seal.rs`.
pub mod classic_macro_rules {
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
    // ZERO-ROW-GATE (2026-10-10): zero bridged obligations plus a call no authenticated registry discharges publish an `unknown` row; refused.
    //[certify,default]~v ERROR Trust strict verification failed for `private_supertrait_seal_needs_a_closed_impl_set::classic_macro_rules::f`
    pub fn f<K: T>(x: &K) -> u32 {
        x.m()
    }
    #[macro_export]
    macro_rules! classic_macro_rules_seal {
        ($t:ty) => {
            impl $crate::classic_macro_rules::private::Sealed for $t {}
        };
    }
}
