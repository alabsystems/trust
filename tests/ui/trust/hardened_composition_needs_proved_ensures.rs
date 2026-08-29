//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-profile=unix_hardened --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//! Trust (B2 negative half (a)): threading the composed fact into the HARDENED
//! twin must not let a DECLARED-but-unproved `ensures` launder into it.
//!
//! This is `postcondition_composition_needs_proved_ensures.rs` under
//! `-Ztrust-verify-profile=unix_hardened`. The hardened panic-boundary lane now
//! receives the call-site postcondition assumption; if that channel were keyed
//! on the mere PRESENCE of an `ensures` rather than on its discharge, every
//! callee could write any proposition it liked and every caller would inherit
//! it — at the exact boundary the hardened profile exists to guard.
//!
//! `bad`'s `ensures` is false (`bad(0) == 0`, not `>= 1000`), so its own
//! postcondition rows come back unproved and the summary never acquires the
//! reuse bit. Both halves are pinned:
//!
//!  * `bad` itself must fail, and
//!  * `caller` must STILL fail — including its hardened `Overflow(Mul)` twin.
//!
//! The second is load-bearing. The body is shaped so that inheriting `y >= 1000`
//! would make the guard `y < 100` contradictory and the `y * 3` obligation prove
//! VACUOUSLY — a green row about an unreachable path, with no symptom anywhere.

pub fn bad(x: i32) -> i32
//~^ ERROR Trust
    ensures result >= 1000
{
    x
}

pub fn caller(x: i32) -> i32 {
//~^ ERROR Trust
    let y = bad(x);
    if y < 100 { y * 3 } else { 0 }
}
