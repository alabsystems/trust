//@ needs-trust-verify
//@ edition: 2021
//@ revisions: rem certify div bitand guarded
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ rustc-env:TRUST_NO_SYSROOT_CENSUS=1
//@[certify] compile-flags: -Ztrust-policy=certify
//@[bitand] compile-flags: -Ztrust-policy=certify
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@[rem] check-pass
//@[certify] check-pass
//@[div] check-pass
//@[bitand] check-pass
//@[guarded] check-pass
//! TRUST_NO_SYSROOT_CENSUS (2026-09-26): this file pins the D5-C borrow-provenance
//! lane of a BUNDLED sysroot member, so it runs with the sysroot panic census off.
//! With it on, `<&u32 as BitAnd<u32>>::bitand` (no `Assert`, no panic site) is
//! discharged by the census before its bundled body's `Load` is ever asked about,
//! and the `bitand` revision's "1 proved" row would vanish — the lane this file
//! measures would no longer be observable. The knob only withholds census grants.
//!
//! **A reference-parameter load inside a bundled SYSROOT operator impl carries
//! `ValidBorrow`, so trust-mc can summarize the call (D5-C, 2026-09-24).**
//!
//! `x % 2` on a `&u32` calls `<&u32 as Rem<u32>>::rem`, which the monomorphic
//! foreign drain (the B-lane) bundles under its per-instance name. Its body loads
//! `*self` through the reference parameter.
//!
//! # Before (measured on stage-1 `trustc 0.10.0+g4e9fe36bf`, 2026-09-24)
//!
//! Every positive revision reported
//! `Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out,
//! 1 runtime-checked out of 2 obligation(s)`, with two warnings
//! ("Level 0 safety verification incomplete", "verification advisory"). `certify`
//! was rc=1. The runtime-checked row was the aggregate
//! `assertion:panic-freedom:0`, "fail-closed lowering reachable … (constructs:
//! UnsupportedDirectCallSummary)".
//!
//! The cause was measured, not inferred:
//! * `TRUST_BUNDLE_TRACE=1` showed the member admitted as `mono-candidate`, which
//!   means the B-lane. B-lane members are never put in `bundled_def_ids`, and
//!   that set was the only thing the borrow-provenance-clean set was built from.
//! * The `-Ztrust-dump=native-bundle` dump showed the member's
//!   `Load { ptr: 0 }` with `proofs: []`.
//! * `call-summary-census` on that dump: `declined unmodeled_instruction/Load`.
//!   With `ValidBorrow` added to that one `Load` in the JSON, the census reads
//!   `summarized`.
//!
//! # After
//!
//! The B-lane records its member's verdict at admission, keyed by the member's
//! exact `def_path` and computed on its instantiated body
//! (`trust_verify/bundled_borrow_provenance.rs`). The positive revisions must
//! show both rows proved and NO warning. WARN is deliberately not in
//! `dont-require-annotations`, so if a warning comes back the test fails.
//!
//! # The revisions
//!
//! * `rem`, `certify` — `x % 2` under the default policy and under `certify`.
//! * `div` — the `<&u32 as Div<u32>>::div` twin.
//! * `bitand` — `<&u32 as BitAnd<u32>>::bitand` under `certify`. This member has
//!   no `Assert` at all, so the `Load` is its only blocker. Before: rc=1,
//!   `0 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked out of 1`.
//!   This also corrects the 2026-09-20 table in `docs/DECISION_QUEUE.md` (D5).
//!   `x & 1` on a `&u32` hits the SAME `Load` decline. It only looked fine
//!   because the default policy tolerates the row, and its member has no
//!   `Assert` for the root's transitive-member gate to refuse. The
//!   discriminator was never "the callee branches".
//! * `guarded` — a divisor that is a parameter, guarded by the caller. The
//!   member's own `Assert` (`d != 0`) is still charged at the call. Only the
//!   memory-access obligation of the load is affected.
//! * `closure` — REMOVED 2026-09-25. It was sweep `s03`
//!   (`tests/ordinary-rust-sweep/s03.rs`): the CLOSURE's row proved, and the
//!   ROOT was refused by `ensure_bundled_member_asserts_exactly_charged`, which
//!   then admitted an Assert-bearing foreign member only at a direct root call.
//!   That refusal was pinned here so it could not change SILENTLY. It changed on
//!   purpose: a site owned by a local body verified as its own root is now
//!   credited to that run. Both halves — the closure's row, pinned with the same
//!   text, and the root — moved to
//!   `tests/ui/trust/bundled_member_assert_owned_by_own_root.rs` (`s03`, `i04`),
//!   beside the refusals the widening must not open.
//!
//! The negative twins (a real divide-by-zero, and a foreign member whose
//! reference is fabricated) are in `bundled_foreign_member_valid_borrow_refusals.rs`.

#[cfg(any(rem, certify))]
pub fn rem_ref(x: &u32) -> u32 {
    //[rem,certify]~^ NOTE Trust verification: 2 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 2 obligation(s)
    x % 2
}

#[cfg(div)]
pub fn div_ref(x: &u32) -> u32 {
    //[div]~^ NOTE Trust verification: 2 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 2 obligation(s)
    x / 3
}

#[cfg(bitand)]
pub fn and_ref(x: &u32) -> bool {
    //[bitand]~^ NOTE Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 1 obligation(s)
    x & 1 == 0
}

#[cfg(guarded)]
pub fn rem_ref_by(x: &u32, d: u32) -> u32 {
    //[guarded]~^ NOTE Trust verification: 2 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 2 obligation(s)
    if d == 0 { 0 } else { x % d }
}
