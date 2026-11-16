//@ revisions: certify_ovf certify_div default_open sound_t
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify_ovf] compile-flags: -Ztrust-policy=certify
//@[certify_div] compile-flags: -Ztrust-policy=certify
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! GENERIC-CALL-KEY-ALIAS-1 (2026-10-06): an open trait dispatch from a generic
//! body must not be named by a local blanket impl's DEFINITION key.
//!
//! Inside `fn f<T: Tr>(x: &T)`, the call `x.m()` prints `<T as k::Tr>::m`. The
//! blanket `impl<T: Marker> Tr for T` prints the same string as the key of its
//! own `m`, because a type parameter prints as its bare name with no owner.
//! Every by-name lane took the blanket body for the call
//! (`direct_call_def_path` residual 1). The return-summary lane lent it the
//! body's bound `m() == 1`, and `f`'s row was proved. `f::<Foo>` runs Foo's
//! own `m`, so it overflows (or divides by zero). The run witness is
//! `generic_call_key_alias_blanket_impl_run.rs`. Renaming `f`'s parameter to
//! `U` removes the alias, so the `U` twin is the proxy for the fixed compiler.
//!
//! Revisions, one shape each, selected by `--cfg <revision>`:
//! * `certify_ovf`: `x.m() + 1` with a private trait carrying Φ
//!   (`#[trust::panic_free]`) and `impl Tr for Foo { u32::MAX }`, under certify.
//! * `certify_div`: `100 / x.m()` with `impl Tr for Foo { 0 }`, under certify.
//! * `default_open`: `100 / x.m()` with a pub trait, no Φ and no `Foo`, under
//!   the default policy. A downstream `impl Tr for Foo { 0 }` divides by zero,
//!   and Foo's `m` is panic-free, so the instance-hypothesis row does not save
//!   the verdict.
//! * `sound_t`: `fn f<T: Marker>`, where the blanket IS every instantiation's
//!   target. It prints byte-identically and pins the fix's fail-closed cost: the
//!   `[divzero]` row moves from proved to failed. The function was already
//!   refused before (strict verification failed on a runtime-checked row), so
//!   its verdict does not change.
//!
//! BEFORE (stage 1 of `4ccd862830` at `scratchpad/stage1-w18b`, each revision's
//! flags plus `--cfg <revision> --emit=metadata`, measured 2026-10-06):
//! `certify_ovf` rc=0, `[overflow:add]` proved, Clean-kernel `Certified`, validation
//! `KernelRechecked`. `certify_div` rc=0, `[divzero]` proved and `Certified`.
//! `default_open` rc=0, `[divzero]` proved, plus the instance-hypothesis warning.
//! `sound_t` rc=1, but `[divzero]` proved, the Level 0 diagnostic only a warning,
//! and the error is strict verification failed.
//!
//! AFTER (PREDICTED, not built: the fix's stage 1 has not been built). The
//! prediction is the `U`-renamed twin of each revision, measured on the same
//! compiler with the same flags; it prints no definition key, so it is named
//! and refused as the tagged call will be. `certify_ovf` and `certify_div` rc=1,
//! with `[overflow:add]` / `[divzero]` FAILED (ay-in-process, counterexample
//! `_2 = 4294967295` / `_2 = 0`) and both errors below. `default_open` rc=1,
//! `[divzero]` FAILED, both errors, and the instance-hypothesis warning
//! unchanged. `sound_t` rc=1, `[divzero]` FAILED, and both errors.
#![allow(dead_code, private_bounds)]

#[cfg(any(certify_ovf, certify_div))]
trait Marker {}
#[cfg(any(certify_ovf, certify_div))]
trait Tr {
    #[trust::panic_free]
    fn m(&self) -> u32;
}
#[cfg(any(default_open, sound_t))]
pub trait Marker {}
#[cfg(any(default_open, sound_t))]
pub trait Tr {
    fn m(&self) -> u32;
}

// Definition key `<T as generic_call_key_alias_blanket_impl::Tr>::m`.
impl<T: Marker> Tr for T {
    fn m(&self) -> u32 {
        1
    }
}

#[cfg(any(certify_ovf, certify_div))]
pub struct Foo;
#[cfg(certify_ovf)]
impl Tr for Foo {
    fn m(&self) -> u32 {
        u32::MAX
    }
}
#[cfg(certify_div)]
impl Tr for Foo {
    fn m(&self) -> u32 {
        0
    }
}

// The call prints `<T as generic_call_key_alias_blanket_impl::Tr>::m`.
#[cfg(certify_ovf)]
pub fn f<T: Tr>(x: &T) -> u32 {
    //[certify_ovf]~^ NOTE [overflow:add] FAILED
    //[certify_ovf]~| ERROR Trust Level 0 safety verification incomplete
    //[certify_ovf]~| ERROR Trust strict verification failed
    x.m() + 1
}

#[cfg(any(certify_div, default_open))]
pub fn f<T: Tr>(x: &T) -> u32 {
    //[certify_div,default_open]~^ NOTE [divzero] FAILED
    //[certify_div,default_open]~| ERROR Trust Level 0 safety verification incomplete
    //[certify_div,default_open]~| ERROR Trust strict verification failed
    //[default_open]~| WARN 1 instance hypothesis row(s)
    100 / x.m()
}

#[cfg(sound_t)]
pub fn f<T: Marker>(x: &T) -> u32 {
    //[sound_t]~^ NOTE [divzero] FAILED
    //[sound_t]~| ERROR Trust Level 0 safety verification incomplete
    //[sound_t]~| ERROR Trust strict verification failed
    100 / x.m()
}
