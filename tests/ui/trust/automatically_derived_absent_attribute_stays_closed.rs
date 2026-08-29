//@ needs-trust-verify
//@ aux-build:user_written_automatically_derived_dep.rs
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//~? RAW Trust
//! **ARM 3 — the baseline that must stay closed.** An unverified cross-crate
//! callee with NO `#[automatically_derived]` is refused, fail-closed, via
//!
//! ```text
//! [trust-absent-callee-assumption] call to absent callee
//! `<user_ad_dep::Plain as user_ad_dep::Idx>::get` (body not in the lowered
//! bundle) may panic
//! ```
//!
//! This is the arm that gives the other two their meaning. `Plain::get` and
//! `Marked::get` in `user_written_automatically_derived_dep.rs` are byte-identical
//! bodies with byte-identical signatures behind byte-identical `#[inline]`s; they
//! differ by exactly one token, `#[automatically_derived]`, on the impl. If this
//! test ever goes green while
//! `automatically_derived_user_written_not_admitted.rs` is still red, the
//! difference between "refused" and "silently trusted" has become one attribute
//! any dependency author can type — which is precisely the finding those two
//! files exist to pin.
//!
//! It is also the harness control: a run in which BOTH files pass has lost the
//! dependency (or the verifier never ran), not fixed the gate. `check-fail` here
//! cannot be satisfied vacuously, because a crate that fails to lower emits no
//! obligations at all and would report clean rather than refuse.

extern crate user_ad_dep;

use user_ad_dep::{Idx, Plain};

/// `xs` has 3 elements, the index is 5. The bounds check lives in the
/// dependency's body, where `i` is an opaque parameter, so no const-propagation
/// lint fires here — the call is simply an unverified foreign body that may
/// panic, and saying so is the whole job.
pub fn dep_plain() -> u32 {
    let xs: [u32; 3] = [10, 20, 30];
    <Plain as Idx>::get(&xs, 5)
}
