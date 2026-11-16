//@ revisions: pub_callee private_callee
//@ needs-trust-verify
//@ edition: 2021
//@ aux-build:xcmreq_callee.rs
//@ aux-build:xcmreq_mid.rs
//@ compile-flags: -Ztrust-verify=off -Coverflow-checks=on
//@ run-fail
//@ error-pattern: attempt to add with overflow
//@ ignore-emscripten no processes
//! The WITNESS for `xcrate_declared_member_requires_callee.rs` (DEP-MEMBER-REQ-1,
//! docs/KNOWN_HAZARDS.md): what the call that fixture's `call` and `call_via`
//! revisions make COMPUTES. `xcmreq_callee` is built under `certify`; a verify-off
//! `xcmreq_mid` calls its `requires x < 100` functions with `u32::MAX`, outside the
//! clause, and nothing charges that call.
//!
//! * `pub_callee` — `xcmreq_mid::wrapper` calls the `pub` `inc`
//!   (`requires x < 100 { x + 1 }`). It WAS `run-pass` asserting the call RETURNED 0
//!   (measured through the stage 1 of `444376149e`, and in wave 15): the certify
//!   build of `xcmreq_callee` elided `inc`'s overflow check under its `requires`, so
//!   the wrong value escaped where vanilla Rust (every crate verify-off) panics. That
//!   pinned the hazard's premise, and its own note said a panic here would mean the
//!   dependency stopped eliding. It did, on purpose: ADVISORY-REQUIRES-CROSS-CRATE
//!   (`02e71e93b4`, landed by merge `d5debba1a8`; docs/DECISION_QUEUE.md) keeps every
//!   check a `requires` body's clause proved when another crate can call that body,
//!   and `inc` is a `pub fn` of a library. So this revision now behaves as vanilla
//!   Rust does: the call panics "attempt to add with overflow" (exit 101, measured on
//!   the stage 1 of `83ba8f1181`) and NO wrong value escapes. It pins exactly that
//!   protection for the `pub` callee: if the call ever returns, `main` prints the
//!   value and exits 0, and `run-fail` fails.
//! * `private_callee` — `xcmreq_mid::wrapper_via` calls the `pub` `inc_via`, whose
//!   private callee `bump` no other crate can call. ADVISORY-REQUIRES-CROSS-CRATE
//!   asked only whether the body that elides can be called from another crate, so
//!   `bump` still elided its check under the clause, which `inc_via`'s call charges
//!   under `inc_via`'s own clause. Measured 2026-10-05 on the stage 1
//!   `scratchpad/stage1-w16`: built rc=0, printed `xcmreq_mid::wrapper_via(4294967295)
//!   = 0` and exited 0. Since ADVISORY-REQUIRES-TRANSITIVE-1 a `requires` body named by
//!   a chain of `requires` bodies that starts at one another crate can call keeps
//!   every check its clause proved, so `bump` keeps its check and this PANICS too
//!   (run-fail; measured 2026-10-06 on the stage 1 of `0ac7a96d9f`: exit 101). Before
//!   the DEP-MEMBER-REQ-1 fix, a certify
//!   crate calling `wrapper_via` was accepted with its panic-freedom row proved
//!   (measured on the stage 1 of `76a6ea45b2`: `call_via` exit 0, "1 proved … out of
//!   1"); the declined-member rule still decides that verdict.
//!
//! These pin the dependency's half (which check is elided), not a verifier verdict.
//! The DEP-MEMBER-REQ-1 decline in the fixture stays a necessary refusal (the
//! consumer must not be credited with a proof through an uncharged call) whatever
//! either runtime outcome is. If either revision exits 0 again, the dependency
//! elided a check whose clause the caller here never established: fix the
//! compiler, not this file.

extern crate xcmreq_mid;

fn main() {
    let v = std::hint::black_box(u32::MAX);
    #[cfg(pub_callee)]
    {
        let got = xcmreq_mid::wrapper(v);
        // Reached only if the dependency's overflow check was removed again.
        println!("xcmreq_mid::wrapper({v}) = {got}: a wrong value escaped");
    }
    #[cfg(private_callee)]
    {
        let got = xcmreq_mid::wrapper_via(v);
        println!("xcmreq_mid::wrapper_via({v}) = {got}");
    }
}
