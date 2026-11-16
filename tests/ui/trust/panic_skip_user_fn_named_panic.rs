//@ revisions: default certify control
//@ needs-trust-verify
//@ edition: 2018
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! PANIC-SKIP-ANCHOR-1 (2026-10-05): a call's ARGUMENTS leave the fail-closed
//! `UnsupportedMir` collector only at the sysroot's own panic entry, never
//! because the callee's rendered name looks like one.
//!
//! trust-vcgen skipped the argument rows of every call whose rendering matched
//! `is_panic_intrinsic_call` (`contains("::panicking::")`,
//! `ends_with("::panic")`, …), so that a real `panic!`'s message constant does
//! not wedge the site at Unknown. A user `fn panic(x: u64) -> u64` that RETURNS
//! matched too, and so did any fn in a user module named `panicking`. `T::LIMIT`
//! in a generic body is an identity-less `ConstValue::OpaqueScalar`, which the
//! compiler must disclose with an `UnsupportedMir` row; passed to such a callee,
//! the row was dropped. The skip now needs what the bridge's diverging-site arm
//! needs: a call with no continuation (a tail call counts: the bridge lowers it
//! with `target: None`), the extractor's DIVERGE-ENTRY-1 stamp on the
//! `CalleeKey` (a real sysroot crate, not a trait item, the generic-free
//! definition path), and the name as a narrowing conjunct.
//!
//! Pinned to edition 2018 for `real_begin_panic`: there `panic!(T::LIMIT)`
//! lowers to `std::rt::begin_panic::<u64>(const <T as Lim>::LIMIT)`, a REAL
//! stamped panic entry handed the same identity-less operand.
//!
//! BEFORE (stage 1 of `76a6ea45b2`, each revision's own flags plus
//! `--cfg <revision> --emit=metadata`, measured 2026-10-05): `default` and
//! `certify` exit 0. `forged_suffix` and `forged_module` report one proved row
//! ("panic freedom: no assertion, `unreachable!`, or panic is reachable") and
//! `forged_tail` "function has no panic obligations (trivially panic-free)".
//! `control` exits 1: the same bodies under names the test does not match
//! (`sink2::accept`) are refused on `unsupported MIR ConstValue::OpaqueScalar:
//! bb0 call args[0]: identity-less opaque unsigned 64-bit scalar cannot be used
//! as proof input`.
//!
//! AFTER (predicted, not built): every `forged_*` keeps that row and is refused
//! in both policies, exactly as its `control` twin. `real_begin_panic` still
//! proves under both policies: its call is stamped and has no continuation, so
//! its argument stays unread, as every real `assert!`/`panic!` site's does. If a
//! `forged_*` function is accepted again, a name has started to decide the skip.
#![feature(explicit_tail_calls)]
#![expect(incomplete_features)]

pub trait Lim {
    const LIMIT: u64;
}

pub mod sink {
    // Returns normally and does nothing dangerous; only its NAME ends in `::panic`.
    #[inline(never)]
    pub fn panic(x: u64) -> u64 {
        x
    }
}

pub mod panicking {
    // No `panic` in the fn's own name: the module name supplies `::panicking::`.
    #[inline(never)]
    pub fn report(x: u64) -> u64 {
        x
    }
}

pub mod sink2 {
    #[inline(never)]
    pub fn accept(x: u64) -> u64 {
        x
    }
}

#[cfg(not(control))]
pub fn forged_suffix<T: Lim>() -> u64 {
    //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete
    //[default,certify]~| ERROR Trust strict verification failed
    sink::panic(T::LIMIT)
}

#[cfg(not(control))]
pub fn forged_module<T: Lim>() -> u64 {
    //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete
    //[default,certify]~| ERROR Trust strict verification failed
    panicking::report(T::LIMIT)
}

#[cfg(not(control))]
pub fn forged_tail<T: Lim>(_x: u64) -> u64 {
    //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete
    //[default,certify]~| ERROR Trust strict verification failed
    become sink::panic(T::LIMIT)
}

// A REAL panic site handed the same identity-less operand: proved before and
// after, in both policies (the path to it is infeasible).
pub fn real_begin_panic<T: Lim>(x: u64) -> u64 {
    if x > 5 && x < 3 {
        panic!(T::LIMIT)
    }
    x
}

// The honest twins: refused before and after. They are what every `forged_*`
// function reports once the name no longer decides.
#[cfg(control)]
pub fn control<T: Lim>() -> u64 {
    //[control]~^ ERROR Trust Level 0 safety verification incomplete
    //[control]~| ERROR Trust strict verification failed
    sink2::accept(T::LIMIT)
}

#[cfg(control)]
pub fn control_tail<T: Lim>(_x: u64) -> u64 {
    //[control]~^ ERROR Trust Level 0 safety verification incomplete
    //[control]~| ERROR Trust strict verification failed
    become sink2::accept(T::LIMIT)
}
