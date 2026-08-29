//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=strict -Ztrust-verify-profile=unix_hardened --crate-type lib
//@ check-pass
//! Trust (B2): postcondition composition must survive the HARDENED profile.
//!
//! This is `postcondition_composition_preconditioned_at_call_site.rs` run again
//! under `-Ztrust-verify-profile=unix_hardened` — the profile `targo trust
//! check` turns on BY DEFAULT. Before this file, NO ui test in the tree passed
//! any hardened profile at all (measured: `grep -rl trust-verify-profile
//! tests/ui/` returned nothing), so the whole composition suite was green while
//! the default production lane failed on the same source.
//!
//! What failed: `trust-vcgen`'s hardened panic-boundary twin is generated from
//! the same MIR asserts the per-statement arithmetic lane uses, but
//! `generate_hardened_vcs` took no `SummaryDatabase` — so a proved callee's
//! `ensures` could not reach it even in principle. Measured on this body before
//! the fix, via `RUSTC_LOG=rustc_mir_transform::trust_verify=debug`:
//!
//!   --no-hardened          2 obligations (1 trusted, 0 rt, 0 failed, 0 unknown)
//!   default unix_hardened  3 obligations (1 trusted, 0 rt, 1 failed, 0 unknown)
//!
//! and the extra row was `[hardened_panic_boundary] mir_assert::Overflow(Mul)
//! FAILED` with counterexample `x = 1, y = -715827883` — a witness that violates
//! `ensures result > 0`, i.e. the twin was refuting with a state the callee's
//! own discharged contract excludes. After the fix: 3 obligations, 2 trusted,
//! 0 failed, 0 unknown.
//!
//! SCOPE — why only the preconditioned shape is pinned here. The
//! precondition-FREE shape (`postcondition_composition_at_call_site.rs`'s
//! `clamp_low`/`triple`) is also fixed by the same change — its twin stops
//! refuting — but it still does not reach `check-pass` under this profile, for a
//! reason that has nothing to do with composition:
//!
//!   [hardened_panic_boundary] UNKNOWN (interval): Proved label lacked exact
//!   kernel/native proof authority
//!
//! i.e. the twin IS proved, by the `interval` engine, and the Proved label is
//! then downgraded for want of kernel/native evidence. That gate reproduces with
//! zero contracts in the program at all — a body that simply states the same
//! bound as an explicit `if y >= 0 && y <= 1000000` guard gets the identical
//! downgrade — so it is a separate, pre-existing hardened-lane authority
//! question, not a composition one. Pinning it here would pin someone else's
//! bug.
//!
//! The negative halves are `hardened_composition_needs_proved_ensures.rs` and
//! `hardened_composition_needs_discharge.rs`; both must keep FAILING under this
//! same profile, or the fix has bought its green by making the hardened lane
//! unable to refute.

pub fn positive_part(x: i32) -> i32
    requires x > 0
    ensures result > 0
{
    x
}

pub fn use_gppre(x: i32) -> i32 {
    if x > 0 {
        let y = positive_part(x);
        if y < 100 { y * 3 } else { 0 }
    } else {
        0
    }
}
