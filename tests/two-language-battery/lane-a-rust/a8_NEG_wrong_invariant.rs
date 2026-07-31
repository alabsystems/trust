//@ battery-lane: A-rust
//@ battery-expect: reject
//@ battery-flags: -Ztrust-verify=on --crate-type=lib
//! LANE A NEGATIVE CONTROL — FALSE LOOP INVARIANTS, one per failure mode.
//!
//! ## Measured outcome (2026-07-26)
//!
//! The bounded multi-path and collection lanes now model both bodies. The
//! compiler genuinely refutes the bad consecution in `backoff_delay` and the
//! bad initiation in `parity_fold`; neither rejection depends on an
//! unsupported row. This file is therefore restored to an ordinary
//! `battery-expect: reject` canary.
//!
//! `a3` and `a5` cover a false `ensures` and a missing descent. Nothing in
//! those controls covers the E4 surface's own refutation: an authored loop
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
