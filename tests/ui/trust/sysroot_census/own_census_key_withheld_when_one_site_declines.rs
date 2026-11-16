//@ needs-trust-verify
//@ revisions: alias alias_tdt no_alias
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[alias] check-fail
//@[alias_tdt] check-fail
//@[no_alias] check-pass
//@[alias] rustc-env:TRUST_SYSROOT_CENSUS_DEBUG=1
//@[alias_tdt] rustc-env:TRUST_SYSROOT_CENSUS_DEBUG=1
//[alias]~? RAW withheld key=`core::mem::drop::<own_census_key_withheld_when_one_site_declines::go::S::Inner>`
//[alias_tdt]~? RAW withheld key=`core::mem::drop::<own_census_key_withheld_when_one_site_declines::go::S::Inner>`
//! Trust (2026-09-28, std-absent-callee): the PER-CALLER census set
//! (`sysroot_panic_census::own_census_total_calls`) holds a call key only when
//! EVERY site of that key in the caller's own body was censused total. The
//! zero-obligation call gates read that set, so if one total site could carry
//! the key for a declining site of the same spelling, the caller would be
//! reported proved while one of its calls can panic.
//!
//! Two calls of one spelling reach different instances through
//! `direct_call_def_path` residual 7c: a type rendered INSIDE generic arguments
//! is not cross-namespace-tagged, so the module `S`'s `Inner` and the `Inner`
//! declared inside `fn S` both render `…::go::S::Inner`. Both calls below are
//! keyed `core::mem::drop::<…::go::S::Inner>`.
//!
//! * `alias`: `drop(a)` drops the module `Inner` (no drop glue, census total);
//!   `drop(Inner(7))` drops the fn-local `Inner`, whose `Drop` panics on 7 (the
//!   census reaches that user destructor and declines). The key is withheld from
//!   `go::S`'s own set as well as from its bundle, and `go::S` stays refused.
//!   A runtime build of this shape panics (`inner`, exit 101).
//! * `alias_tdt`: the `alias` shape with a THIRD call of the same key after the
//!   declining one — total, declining, total (`drop(b)` drops another module
//!   `Inner`). `alias` alone pins the rule only for its two-site order: a ledger
//!   that judged each key by ONE of its sites (say the sites collected into a map
//!   keyed by call key) keeps the declining site when the last entry wins, and
//!   `alias` still passes. Here the first site and the last site are both total,
//!   so a ledger that keeps the first, the last, or ignores the decline grants
//!   the key, and `go::S` certifies while a runtime build of the shape panics
//!   (`inner`, exit 101). Only judging EVERY site keeps it refused.
//! * `no_alias`: the same shape, but the fn-local `Inner` has no `Drop` impl.
//!   Both sites are censused total, the key is granted, and `go::S` certifies.
//!   This keeps the `alias` refusal from being vacuous: the only difference
//!   between the revisions is the panicking destructor behind the aliased key.
//!
//! If `alias` or `alias_tdt` ever certifies `go::S`, the per-caller set spent a
//! key one of the caller's own sites declined: a false proof, never progress.
//!
//! The `RAW` lines pin the aliasing itself (`TRUST_SYSROOT_CENSUS_DEBUG`'s
//! `withheld key=` line: one key judged total at one site and declined at another).
//! If residual 7c is ever fixed, the two `Inner`s render apart, those lines vanish
//! and the revisions fail loudly, instead of passing while no longer exercising
//! the per-caller rule.
#![allow(non_snake_case)]

pub mod go {
    pub mod S {
        pub struct Inner(pub u8);
    }

    #[cfg(any(alias, no_alias))]
    pub fn S(a: S::Inner) {
        //[alias]~^ ERROR Trust Level 0 safety verification incomplete for
        struct Inner(u8);
        #[cfg(alias)]
        impl Drop for Inner {
            fn drop(&mut self) {
                if self.0 == 7 {
                    panic!("inner")
                }
            }
        }
        core::mem::drop(a);
        core::mem::drop(Inner(7));
    }

    #[cfg(alias_tdt)]
    pub fn S(a: S::Inner, b: S::Inner) {
        //[alias_tdt]~^ ERROR Trust Level 0 safety verification incomplete for
        struct Inner(u8);
        impl Drop for Inner {
            fn drop(&mut self) {
                if self.0 == 7 {
                    panic!("inner")
                }
            }
        }
        core::mem::drop(a);
        core::mem::drop(Inner(7));
        core::mem::drop(b);
    }
}
