//@ battery-lane: A-rust
//@ battery-expect: frontier
//@ battery-flags: -Ztrust-verify=on --crate-type=lib
//! LANE A — FALSE LOOP INVARIANTS. Written as a negative control; MEASURED as
//! a frontier. The reclassification is the finding.
//!
//! ## Measured outcome (2026-07-25, toolchain c6be27eb88)
//!
//! Neither false invariant is REFUTED. Both land as unsupported rows:
//!
//!     [unknown] UNKNOWN ... unsupported MIR `UserLoopContractUnsupported`:
//!     loop invariant `i < xs.len()` is outside the exact single-path
//!     loop-transition fragment at bb1
//!
//! The report reads `2 proved, 0 failed, 2 unknown` — and to be exact about
//! what that means: the two PROVED obligations are bounds checks, not the
//! invariants. The invariants were never evaluated at all. **This is not a
//! false accept**: the build still fails, because strict policy treats an
//! unsupported row as an error. But it is not a refutation either, and the
//! difference matters — the battery has NO working negative control for the
//! E4 invariant surface until the single-path fragment grows to cover a
//! two-statement body. See `a12_FRONTIER_multipath_loop.rs` for the same
//! fragment limit hit from the positive side.
//!
//! Everything below this line is the original design intent, retained because
//! it states precisely what these programs SHOULD exercise once the fragment
//! covers them — at which point this file's verdict becomes `frontier-refuted`
//! and it should be restored to `battery-expect: reject`.
//!
//! ORIGINAL INTENT — FALSE LOOP INVARIANTS, one per failure mode.
//!
//! `a3` and `a5` cover a false `ensures` and a missing descent. Nothing in
//! this battery yet covers the E4 surface's own refutation: an authored loop
//! invariant that is simply not true. Authored loop facts must never be
//! accepted as documentation, or merely because they were written
//! (`tests/ui/trust/native_loop_clause_semantics.rs:9-13`).
//!
//! Both programs below are ORDINARY, well-typed Rust — they compile and run
//! under vanilla `rustc` semantics, and every name in every clause resolves.
//! The only thing wrong with them is the proof. A rejection here that carries
//! a parse error or an unresolved name would be a battery failure, not a
//! compiler success, and the runner classifies it as `reject-wrong-reason`.
//!
//! The two functions are aimed at the two halves of the loop rule, which
//! `crates/trust-vcgen/src/contracts.rs:1052-1063` builds as separate
//! verification conditions:
//!
//!   * INITIATION  — `preconditions && !invariant[entry]`. The loop guard is
//!     deliberately NOT assumed, so an invariant that is only true once the
//!     loop is running is refuted here (`parity_fold`).
//!   * CONSECUTION — `invariant && guard && !invariant[after]`. The body is
//!     symbolically executed through one full iteration, so an invariant the
//!     body breaks leaves a satisfiable violation (`backoff_delay`).
//!
//! Neither loop carries a `decreases` clause. That is deliberate: both loops
//! do terminate, and adding a measure would let the file fail for a second,
//! unrelated reason. The invariant-only shape is the one the pinned negative
//! revisions use (`native_loop_clause_semantics.rs:23-36`), and it makes the
//! refutation surgical.

/// Exponential retry backoff, capped by the caller.
///
/// FALSE INVARIANT — CONSECUTION. `delay <= 1000` is true on entry and is
/// broken by the body: doubling overshoots the cap rather than landing on it.
/// From the genuinely reachable state `delay == 512` with `limit == 1000`, the
/// guard holds, one iteration produces `1024`, and the invariant is false.
///
/// This is a real bug, not a synthetic one — "the cap bounds the loop
/// variable" is exactly what an engineer writes here, and it is wrong for
/// every doubling loop. The correct invariant is `delay <= 2 * 1000`, or the
/// body must clamp.
pub fn backoff_delay(limit: u32) -> u32
    requires limit <= 1000
{
    let mut delay = 1u32;
    while delay < limit
        invariant delay <= 1000
    {
        delay *= 2;
    }
    delay
}

/// XOR parity over a byte frame.
///
/// FALSE INVARIANT — INITIATION. The classic off-by-one: `i < xs.len()` is
/// the LOOP GUARD, not the loop invariant. It is not established at the loop
/// head, because an empty frame arrives there with `i == 0 == xs.len()`.
///
/// The distinction is invisible in testing — every non-empty input keeps the
/// clause true — and invisible to a verifier that assumes the guard when
/// checking entry. It is visible here only because the initiation condition is
/// built WITHOUT the guard. The author meant `i <= xs.len()`, which is what
/// `a9_bounds_safety.rs` writes and what makes `xs[i]` provably in bounds.
pub fn parity_fold(xs: &[u8]) -> u8 {
    let mut acc = 0u8;
    let mut i = 0usize;
    while i < xs.len()
        invariant i < xs.len()
    {
        acc ^= xs[i];
        i += 1;
    }
    acc
}
