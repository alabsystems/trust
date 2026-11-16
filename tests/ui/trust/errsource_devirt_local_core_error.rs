//@ revisions: default certify
//@ needs-trust-verify
//@ edition: 2021
//@ rustc-env:TRUST_ERRSOURCE_DEVIRT=1
//@ compile-flags: -Ztrust-verify=on -Coverflow-checks=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! A trait whose path PRINTS as `core::error::Error` is not core's `Error`
//! (ERRSOURCE-ANCHOR-1).
//!
//! With `TRUST_ERRSOURCE_DEVIRT` set, two lanes demote a virtual
//! `<dyn Error>::source` call whose receiver is pinned to a concrete type that keeps
//! the trait's default `source` (the `{ None }` body): the extractor's
//! `stamp_errsource_devirt_total_calls` rewrites the call to the obligation-free
//! total sentinel, and the compiler's `native_trust_ir_errsource_devirt_demotable_calls`
//! adds its key to the expected-absent set. Both recognized the trait by
//! `def_path_str(trait) == "core::error::Error" | "std::error::Error"`, and
//! `def_path_str` drops the LOCAL crate root, so this crate's own `mod core { mod
//! error { trait Error } }` prints exactly that. Its default `source` panics.
//!
//! BEFORE (stage 1 of main + wave 7, `scratchpad/stage1-w14`, each revision's own
//! flags plus `--cfg <revision> --emit=metadata`, with `TRUST_ERRSOURCE_DEVIRT=1`,
//! measured 2026-10-05): `TRUST_ERRSOURCE_DEVIRT_TRACE` prints `demotable=true` for
//! `go` in both lanes, `go` has no diagnostic in either revision, and the annotations
//! on it do not fire. The program panics (`..._run.rs`).
//!
//! AFTER (predicted): both lanes require the trait to be core's `Error` diagnostic
//! item, defined in a real sysroot crate, so `go`'s call keeps its
//! `[trust-absent-callee-assumption] ... dynamic dispatch` row. The annotations on
//! `go` are what the BEFORE compiler prints for this file with the variable UNSET,
//! line for line, which is the no-demotion path the fix leaves for this trait.
//!
//! Control: `go_std` makes the same call through std's real `Error` on a type that
//! keeps the default `source`. It is demoted before and after (measured BEFORE: no
//! diagnostic in either revision), so the anchor still admits the trait it exists
//! for.

pub mod core {
    pub mod error {
        pub trait Error {
            fn source(&self) -> Option<u32> {
                //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete for `errsource_devirt_local_core_error::core::error::Error::source`: 2 obligation(s) were not proved
                //[default,certify]~| ERROR Trust strict verification failed for `errsource_devirt_local_core_error::core::error::Error::source`: 2 obligation(s) were not fully verified
                panic!("user default source panicked")
            }
        }
    }
}

pub struct C(pub u8);

impl crate::core::error::Error for C {}

#[inline(never)]
pub fn go(c: &C) -> Option<u32> {
    //[default,certify]~^ ERROR Trust strict verification failed for `errsource_devirt_local_core_error::go`: 1 obligation(s) were not fully verified
    //[certify]~^^ ERROR Trust Level 0 safety verification incomplete for `errsource_devirt_local_core_error::go`: 1 obligation(s) were not proved
    let d: &dyn crate::core::error::Error = c;
    d.source()
}

pub struct R(pub u8);

impl std::fmt::Debug for R {
    fn fmt(&self, _f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Ok(())
    }
}

impl std::fmt::Display for R {
    fn fmt(&self, _f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Ok(())
    }
}

impl std::error::Error for R {}

#[inline(never)]
pub fn go_std(r: &R) -> bool {
    let d: &dyn std::error::Error = r;
    d.source().is_none()
}
