//@ needs-trust-verify
//@ aux-build:cross_crate_bundle_scope_dep.rs
//@ compile-flags: -Ztrust-verify=on --crate-type lib -Ztrust-bundle-foreign-crate=xcbundle_dep
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//~? RAW Trust
//! **ARM 3 — THE SOUNDNESS PIN. A foreign `ensures` is RE-DERIVED, never
//! ASSUMED. This test must fail, and if it ever passes the lane is unsound.**
//!
//! This is the arm that matters more than arm 2. Arm 2 shows the capability
//! arrived; this one shows it arrived without bringing a verdict with it.
//!
//! # The construction
//!
//! `xcbundle_dep::overclaims` declares `ensures result <= 3` and
//! its body returns `k` for every `k <= 31`, so `overclaims(10) == 10`. The
//! clause is FALSE of the code, and nothing has ever checked it: the aux crate is
//! compiled `-Ztrust-verify=off`, exactly as `targo` compiles a dependency.
//!
//! `need_three` below declares the same clause and its whole body is that call.
//! So:
//!
//! * if the caller ASSUMES the foreign clause read out of rmeta, `need_three`'s
//!   own postcondition follows immediately and this test PASSES — a proposition
//!   that is false of the program, proved, with a green verdict and nothing in
//!   the counts saying so;
//! * if the caller RE-DERIVES the callee's body, the returned value ranges up to
//!   31, `result <= 3` does not follow, and the postcondition row stays unproved
//!   under the fail-closed default.
//!
//! The bundling scope IS declared here — the flag is present and identical to
//! arm 2's — so this is not testing that the lane is off. It is testing what the
//! lane does when it is fully on.
//!
//! # Why this shape and not another
//!
//! Reading a foreign `ensures` from rmeta and assuming it at the call site is
//! the trap most likely to be walked into, because the metadata channel is real
//! and already works: `trust_contracts` genuinely is `separate_provide_extern`,
//! and a foreign `requires` genuinely is discharged at call sites today. But
//! DISCHARGING a foreign `requires` makes the caller prove MORE, while ASSUMING
//! a foreign `ensures` makes it prove LESS on someone else's say-so. That is
//! verdict import wearing a contract's clothes, and it is what this file
//! refuses.
//!
//! A sealed cross-compilation postcondition token was built once, in
//! `PostconditionAuthority`, and removed the same afternoon as a "forgeable
//! callee proof mint". `TrustProofResults` still derives
//! `TyEncodable`/`TyDecodable`/`StableHash`, so nothing in the type system stops
//! someone shipping it again in an afternoon. This test is the thing that would
//! notice.
extern crate xcbundle_dep;

pub fn need_three(k: u32) -> u32 ensures result <= 3 {
    xcbundle_dep::overclaims(k)
}
