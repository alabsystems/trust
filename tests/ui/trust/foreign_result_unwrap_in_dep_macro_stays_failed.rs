//~ NOTE "line_start":56,"col_start":8,"line_end":56,"col_end":38},"outcome":"failed","solver":"level0-refutation-fail-closed-over-runtime_checked
//~| NOTE "line_start":53,"col_start":8,"line_end":53,"col_end":38},"outcome":"failed","solver":"level0-refutation-fail-closed-over-runtime_checked
//~| NOTE "total_proved":0,"total_failed":2,
//@ revisions: undeclared declared
//@ needs-trust-verify
//@ aux-build:json_shaped_dep.rs
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=both --crate-type=lib
//@ compile-flags: -Ztrust-policy=advisory
//@[declared] compile-flags: -Ztrust-bundle-foreign-crate=json_shaped_dep
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! DECISION_QUEUE "JSON-UNWRAP-1" (2026-10-06): an `unwrap` that a DEPENDENCY's
//! macro expands into the caller, over a dependency function's `Result`, is the
//! caller's own unwrap-family obligation, one row PER SITE, and stays `failed`
//! (UF-1's `unproved_fail_closed`) while nothing in this compilation proves the
//! callee returns `Ok`. This is the shape of `serde_json::json!({"k": v})`, whose
//! every interpolation is `serde_json::to_value(&v).unwrap()` (47 rows on the
//! 2026-10-05 gate preview: trust-vc-rustc 27, nn-optim 20).
//!
//! Line 1 pins, in both revisions, each site's own row by its span in the
//! auxiliary macro (line 56 is `u64_site`'s arm, line 53 `str_site`'s) as
//! `failed`, and the crate at exactly 0 proved and 2 failed, so no other row
//! may take an unwrap row's place.
//! * `undeclared`: the dependency is outside the bundling scope; its `to_value`
//!   is an absent callee (`runtime_checked`). MUST stay as pinned: no trusted
//!   list of "infallible" serializers or callee names may discharge these (OD-1
//!   rejected that class of trusted list; JSON-UNWRAP-1 rejects it again for
//!   `to_value`, whose real `Err` paths include map keys, `u128`, non-UTF-8
//!   paths, poisoned locks and every `S::Error::custom`).
//! * `declared`: the dependency is declared and `unsafe`-free, and its
//!   `to_value` IS infallible by construction, yet no lane delivers that fact
//!   to the caller (measured 2026-10-06, stage 1 of `875098bc9a`):
//!   - the return-discriminant summary that proves the same unwrap over a
//!     same-crate `Result` (`compute_return_disc_summaries`) reads only this
//!     crate's bodies;
//!   - the instance re-derivation of the dependency's generics ends `unknown`
//!     ("runs code not re-derived here: drop glue of `T`"), so it does not
//!     even establish the callee's panic-freedom;
//!   - the bundling flag does not put the `to_value::<&u64>`/`<&&str>`
//!     instances into the trust-ir bundle: both stay absent callees whose
//!     result is a fresh havoc, and trust-mc also rejects `str_site`'s input
//!     ("uses Alloca without an internally bound extent ...
//!     not_promotable.pointee_not_precise_scalar", the `&str` fat pointer).
//!   A fix to those GAPS (the dependency instance's body lowered into the
//!   bundle and accepted by trust-mc, or a same-crate summary lane extended to a
//!   re-derived declared body) may move THIS revision's unwrap rows to proved
//!   under authority that exists today; it is not ruled out by JSON-UNWRAP-1.
//!   It updates these pins in its own DECISION row. `undeclared` may move
//!   only through a proof of `to_value`'s own body, never a list or a name.
//! Advisory compiles (drop-in Rust).
extern crate json_shaped_dep;

use json_shaped_dep::{json_like, Value};

pub fn u64_site(a: u64) -> Value {
    json_like!(a)
}

pub fn str_site(b: &str) -> Value {
    json_like!([b])
}
