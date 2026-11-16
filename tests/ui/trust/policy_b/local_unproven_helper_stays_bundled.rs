//@ needs-trust-verify
//@ revisions: i02 i02_certify i02_certify_census i02_defaults_certify_census
//@ revisions: unproven_certify discarded private_helper
//@ revisions: helper_div helper_wrapping_div cofolded generic_user_type recursive_pair
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[i02_certify] compile-flags: -Ztrust-policy=certify
//@[i02_certify] rustc-env:TRUST_NO_SYSROOT_CENSUS=1
//@[i02_certify_census] compile-flags: -Ztrust-policy=certify
//@[i02_defaults_certify_census] compile-flags: -Ztrust-policy=certify
//@[unproven_certify] compile-flags: -Ztrust-policy=certify
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[i02] check-pass
//@[discarded] check-pass
//@[private_helper] check-pass
//@[i02_certify] check-fail
//@[i02_certify_census] check-fail
//@[i02_defaults_certify_census] check-pass
//@[i02_defaults_certify_census] ignore-std-debug-assertions (measured with a release-like std only)
//@[unproven_certify] check-fail
//@[helper_div] check-fail
//@[helper_wrapping_div] check-fail
//@[cofolded] check-fail
//@[generic_user_type] check-fail
//@[recursive_pair] check-fail
//! CALLER POISONING by a local helper (measured 2026-09-23, stage-1 `96f2019566`).
//!
//! `tests/idiomatic-rust-sample/i02_vec_literal_of_defaults.rs`, verbatim:
//!
//!     pub fn defaults() -> Vec<u32> { vec![80, 443, 8080] }
//!     pub fn count() -> usize { defaults().len() }
//!
//! `defaults` alone builds under the default policy (its unproved rows keep
//! rustc's runtime checks: two warnings). `count` was REFUSED — `1 runtime-checked`,
//! "an unproved assumption-panic row — a generic absent callee — keeps the function
//! fail-closed". Diagnosed with the fix: the survivor cascade evicted the LOCAL
//! helper from `count`'s bundle, so the call became an absent callee no tolerance
//! covers. The caller was refused for calling a function that is itself accepted.
//!
//! THE FIX keeps a local, non-generic, unproven member bundled, and judges its
//! inner sites per site. That is only sound if a FATAL inner site still refuses
//! the caller, so most of this file is the other direction.
//!
//! Must BUILD (each was refused on the baseline — red before the fix):
//!
//!   * `i02` — the sample, verbatim.
//!   * `discarded` — the caller only binds the value (`let _v = defaults();`).
//!   * `private_helper` — the same helper without `pub`. NOT in the ruling's
//!     list of measured shapes; added because a private helper is the common
//!     form of this code and is equally local and non-generic. If the post-fix
//!     verdict differs, that is a finding about the fix's scope, not a typo here.
//!
//! Must stay REFUSED (each already refused on the baseline, for the eviction
//! reason, so none is red before the fix; they pin what the fix must NOT start
//! accepting). The pin is the annotation on the CALLER, because the helper alone
//! may already fail the crate:
//!
//!   * `unproven_certify` — a helper that lowers but keeps a tolerated absent-callee
//!     marker (`Vec::push`), under `-Ztrust-policy=certify`: kept bundled means
//!     REPORTED, never proved, so `count` stays refused. Added 2026-09-28 because
//!     the sample's own `defaults` now verifies (the `vec![..]` helper went on
//!     `EXACT_TOTAL`), so `i02_certify` no longer carries an unproven helper site.
//!   * `i02_certify` — the sample under `-Ztrust-policy=certify`, run with
//!     `TRUST_NO_SYSROOT_CENSUS=1` (2026-09-26). Originally the reported-only pin:
//!     the helper's only gap was the absent
//!     `box_assume_init_into_vec_unsafe::<u32, 3>` (the `vec!` expansion). Two
//!     independent changes since prove that helper — the sysroot panic census
//!     derives it total, and (2026-09-28) the `vec![..]` helper went on
//!     `EXACT_TOTAL` — so the helper no longer carries the refusal. The sample
//!     STILL fails `certify` because of main's P-GA-1 (DECISION_QUEUE,
//!     2026-10-02): a body that may reach the global allocator carries the
//!     DISCHARGED `contract:global-alloc-dealloc-panic-free` premise and is no
//!     longer counted verified, so `count`'s call to `defaults` keeps a
//!     runtime-checked row that `certify` refuses (on `count` only).
//!     `i02_defaults_certify_census` pins that `defaults` alone certifies with
//!     the census on; `i02_certify_census` (the whole sample, census on) is the
//!     same P-GA-1 refusal, re-pinned 2026-10-08.
//!   * `helper_div` / `helper_wrapping_div` — a helper whose inner site is fatal
//!     (`80 / d`; an absent `wrapping_div`) still refuses its caller.
//!   * `cofolded` — a tolerated helper call folded together with a FATAL site in
//!     the caller's own body (the fold hole's shape, one call level up). Since
//!     2026-09-28 its helper is the `Vec::push` one, because the `vec![..]` helper
//!     is now proved, not tolerated.
//!   * `generic_user_type` — a GENERIC local helper instantiated at a user type
//!     is not covered by the fix and still refuses its caller.
//!   * `recursive_pair` — still refused, at `pong`: a member stays bundled only
//!     once its OWN verification finished accepted, and in callee-first order
//!     `pong` is verified before `ping` has been, so `ping` is evicted from
//!     `pong`'s bundle exactly as before the fix. Deterministic (the demand
//!     order is fixed) and fail-closed; accepting the pair would need a
//!     cycle-aware acceptance rule, which is not in scope here. SINCE
//!     2026-09-25 (mutual-recursion termination, docs/KNOWN_HAZARDS.md) `ping`
//!     and `pong` are ALSO each refused on a `[termination]` row: they form a
//!     recursion cycle with no `decreases` measure, and `count` is refused for
//!     calling the unverified `ping`. The `pong` error pinned below is unchanged.

// ---- the sample, and the shapes that must now build ----

#[cfg(any(i02, i02_certify, i02_certify_census, i02_defaults_certify_census, discarded))]
pub fn defaults() -> Vec<u32> { vec![80, 443, 8080] }

#[cfg(any(i02, i02_certify, i02_certify_census))]
pub fn count() -> usize { defaults().len() }
//[i02_certify,i02_certify_census]~^ ERROR Trust strict verification failed for `local_unproven_helper_stays_bundled::count`

// ---- a helper kept bundled while UNPROVEN is reported, never proved ----

#[cfg(any(unproven_certify, cofolded))]
pub fn defaults() -> Vec<u32> {
    let mut v = Vec::new();
    v.push(80);
    v
}

#[cfg(unproven_certify)]
pub fn count() -> usize { defaults().len() }
//[unproven_certify]~^ ERROR Trust strict verification failed for `local_unproven_helper_stays_bundled::count`

#[cfg(discarded)]
pub fn load() { let _v = defaults(); }

#[cfg(private_helper)]
fn private_defaults() -> Vec<u32> { vec![80, 443, 8080] }

#[cfg(private_helper)]
pub fn count() -> usize { private_defaults().len() }

// ---- a fatal site anywhere in reach still refuses the caller ----

// The division is REFUTED in `defaults` itself (a counterexample, `d = 0`), so
// the crate fails there. `count`'s own row is only rustc's retained division
// check inside the bundled helper — reported, not failed — which is why the pin
// sits on the helper: the build cannot go green while the helper is refuted.
#[cfg(helper_div)]
pub fn defaults(d: u32) -> Vec<u32> { vec![80 / d] }
//[helper_div]~^ ERROR Trust strict verification failed for `local_unproven_helper_stays_bundled::defaults`

#[cfg(helper_div)]
pub fn count(d: u32) -> usize { defaults(d).len() }

#[cfg(helper_wrapping_div)]
pub fn defaults(d: u32) -> Vec<u32> { vec![80u32.wrapping_div(d)] }

#[cfg(helper_wrapping_div)]
pub fn count(d: u32) -> usize { defaults(d).len() }
//[helper_wrapping_div]~^ ERROR Trust strict verification failed for `local_unproven_helper_stays_bundled::count`

#[cfg(cofolded)]
pub fn count(a: u32, b: u32) -> usize {
    //[cofolded]~^ ERROR Trust strict verification failed for `local_unproven_helper_stays_bundled::count`
    let v = defaults();
    let q = a.wrapping_div(b);
    std::mem::forget(v);
    q as usize
}

// ---- a generic helper, and a mutually recursive pair ----

#[cfg(generic_user_type)]
pub struct Port(pub u32);

#[cfg(generic_user_type)]
pub fn defaults<T>(x: T) -> Vec<T> { vec![x] }

#[cfg(generic_user_type)]
pub fn count() -> usize { defaults(Port(80)).len() }
//[generic_user_type]~^ ERROR Trust strict verification failed for `local_unproven_helper_stays_bundled::count`

#[cfg(recursive_pair)]
pub fn ping(n: u32) -> Vec<u32> { if n == 0 { vec![80, 443] } else { pong(n - 1) } }

#[cfg(recursive_pair)]
pub fn pong(n: u32) -> Vec<u32> { ping(n) }
//[recursive_pair]~^ ERROR Trust strict verification failed for `local_unproven_helper_stays_bundled::pong`

#[cfg(recursive_pair)]
pub fn count(n: u32) -> usize { ping(n).len() }
