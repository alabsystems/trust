//@ needs-trust-verify
//@ aux-build:cross_crate_bundle_scope_dep.rs
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//~? RAW Trust
//! **ARM 1 — the DEFAULT. Without a build-declared bundling scope a foreign
//! callee is still an absent callee, and that is still fatal.**
//!
//! Read this file with `cross_crate_bundle_scope_declared.rs`, which is
//! byte-identical apart from one compile flag. The pair is the whole control:
//! if arm 2 ever passes for a reason other than the flag, this arm passes too
//! and the pair says so.
//!
//! # What the compiler does here, and why
//!
//! `passthru` calls a function whose body lives in another crate. The MIR for
//! that body IS available — the aux crate is compiled `-Zalways-encode-mir` —
//! and the callee's `ensures result <= 31` IS readable, because `trust_contracts`
//! crosses rmeta (`separate_provide_extern`). Neither of those facts admits it.
//! The foreign-bundling lane consults a scope this compilation was GIVEN, and
//! this compilation was given none, so the body is not offered to the bundler
//! and the call falls to the fail-closed arm:
//!
//! ```text
//! [trust-absent-callee-assumption] call to absent callee
//!   `xcbundle_dep::clamp_index` (body not in the lowered bundle) may panic
//! ```
//!
//! Under the fail-closed default an unproved assumption-panic row is a build
//! error, so a crate whose entire obligation content is that one row goes from
//! PASS to FAIL by adding one call. That is the cost this lane exists to remove,
//! and it is removed by DECLARING the scope, never by weakening the row.
//!
//! # Why this arm must keep failing
//!
//! The absent-callee mint is the fail-closed floor: it emits `Assert(false)`
//! plus a `NoPanic` annotation that keeps the panic path REACHABLE, havocs the
//! result, and mints one `PanicFreedom` obligation. Composition changes which
//! callees are in the bundle; it must never touch that arm. If this test starts
//! passing without its compile flags changing, something has made the floor
//! silently discharge, which is the shape of every false PROVE this tree has
//! recorded.
extern crate xcbundle_dep;

/// Deliberately NOT a bare passthrough. A body whose only content is the
/// foreign call has an empty obligation ledger once the call stops being an
/// absent callee, and "PASS with zero obligations" is a shape this tree has
/// been burned by. The capped increment gives the caller two obligations it
/// must genuinely discharge itself — an `Add` overflow and its hardened
/// boundary — so the passing arm is a pass WITH proofs, and the failing arm
/// differs from it by exactly one extra row.
pub fn bump_capped(a: u8) -> u8 {
    let _ = xcbundle_dep::clamp_index(3);
    if a > 200 {
        return 201;
    }
    a + 1
}
