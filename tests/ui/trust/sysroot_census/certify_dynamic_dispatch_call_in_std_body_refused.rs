//@ needs-trust-verify
//@ revisions: formatter formatter_control callable_type_arg
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@[formatter] rustc-env:TRUST_SYSROOT_CENSUS_DEBUG=1
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[formatter] check-fail
//@[formatter_control] check-pass
//@[callable_type_arg] check-fail
//[formatter]~? RAW a dynamic-dispatch call to `core::fmt::Write::write_str` in `core::fmt::Formatter::<'_>::write_str`
//! Trust (2026-09-28, std-absent-callee; re-pinned 2026-10-08): a
//! DYNAMIC-DISPATCH call inside a std body (`InstanceKind::Virtual`) is a panic
//! site for the sysroot panic census: a vtable slot can hold any implementation.
//!
//! * `formatter` (the pin). `Formatter::write_str` and
//!   `<Formatter as fmt::Write>::write_char` forward to the formatter's
//!   `buf: &mut dyn fmt::Write`, which is whatever writer the formatting call was
//!   handed — a user `fmt::Write` whose `write_str` panics included. No argument or
//!   type argument of those calls names the writer, so the census's virtual-call
//!   arm is the only thing between these functions and a proof: with that arm
//!   treated as total, the census derived both forwarders total and `W::fmt`,
//!   `put` and `put_char` certified, while `write!(Boom, "{}", W)` with a
//!   panicking `Boom` panics at run time (`dyn writer`, exit 101). The `RAW` line
//!   pins the census's own reason. The NOTE is the refusal of the bundled
//!   forwarder's own absent callee, the virtual call itself.
//! * `formatter_control` (check-pass): `Formatter::width`, a `Formatter` method
//!   with no virtual call, certifies — so the refusals above come from the
//!   dispatch, not from `Formatter` as such.
//! * `callable_type_arg`: the fixture's first shape (2026-09-28),
//!   `Option::<u8>::map::<u8, &dyn Fn(u8) -> u8>` handed `&boom`. Since
//!   origin/main's callable-type-argument gate refuses a sysroot call instantiated
//!   at a `dyn Fn` type on its own, this revision no longer isolates the census
//!   arm; it stays as a refusal pin of the shape (a runtime build panics, `dyn`,
//!   exit 101).

#[cfg(formatter)]
pub mod formatter {
    use std::fmt;

    pub struct W;

    impl fmt::Display for W {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            //[formatter]~^ ERROR Trust strict verification failed for `<certify_dynamic_dispatch_call_in_std_body_refused::formatter::W as core::fmt::Display>::fmt`
            //[formatter]~| NOTE `<dyn core::fmt::Write as core::fmt::Write>::write_str` is a std/core/alloc function whose panic-freedom this compilation cannot derive: it is a call that does not resolve to a sysroot body with MIR
            f.write_str("w")
        }
    }

    pub fn put(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        //[formatter]~^ ERROR Trust strict verification failed for `certify_dynamic_dispatch_call_in_std_body_refused::formatter::put`
        f.write_str("x")
    }

    pub fn put_char(f: &mut fmt::Formatter<'_>) -> fmt::Result {
        //[formatter]~^ ERROR Trust strict verification failed for `certify_dynamic_dispatch_call_in_std_body_refused::formatter::put_char`
        fmt::Write::write_char(f, 'x')
    }
}

#[cfg(formatter_control)]
pub mod formatter_control {
    use std::fmt;

    pub fn width(f: &fmt::Formatter<'_>) -> Option<usize> {
        f.width()
    }
}

#[cfg(callable_type_arg)]
pub mod callable_type_arg {
    pub fn apply_dyn(x: Option<u8>, f: &dyn Fn(u8) -> u8) -> Option<u8> {
        //[callable_type_arg]~^ ERROR Trust strict verification failed for `certify_dynamic_dispatch_call_in_std_body_refused::callable_type_arg::apply_dyn`
        x.map(f)
    }

    fn boom(_: u8) -> u8 {
        panic!("dyn")
    }

    fn inc(x: u8) -> u8 {
        x.wrapping_add(1)
    }

    pub fn apply_dyn_boom() -> Option<u8> {
        //[callable_type_arg]~^ ERROR Trust strict verification failed for `certify_dynamic_dispatch_call_in_std_body_refused::callable_type_arg::apply_dyn_boom`
        apply_dyn(Some(1), &boom)
    }

    pub fn apply_dyn_inc() -> Option<u8> {
        //[callable_type_arg]~^ ERROR Trust strict verification failed for `certify_dynamic_dispatch_call_in_std_body_refused::callable_type_arg::apply_dyn_inc`
        apply_dyn(Some(1), &inc)
    }
}
