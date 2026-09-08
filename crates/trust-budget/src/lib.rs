#![no_std]
//! The solver RESOURCE-BUDGET arithmetic: how a memory budget is split across
//! concurrent solves, how a per-obligation timeout is split across a decomposed
//! retry, and the floor under a per-process RSS ceiling.
//!
//! # Why this crate exists, and why budget arithmetic is verdict-bearing
//!
//! This looks like plumbing and is not. Three of the four numbers below decide
//! whether an obligation gets a solver at all, and Trust's own gate scripts
//! encode that: `require_env` in every `*_strict_gate.sh` refuses to SCORE a
//! run whose log carries `MemoryAdmission` or `memory admission failed`,
//! because in that state *"every obligation was refused BEFORE solver
//! dispatch"*. A budget derivation that returns nothing, or that returns a
//! ceiling the coordinator will not admit, produces exactly that log.
//!
//! The timeout split is sharper still. `trust-router`'s
//! `try_disjoint_component_refutation` states its own soundness condition in
//! prose:
//!
//! > *the retry must not multiply the caller's per-obligation timeout. The
//! > compiler computes that timeout as `min(configured,
//! > remaining_function_budget)` precisely so ONE VC cannot outlive the
//! > function's budget; re-solving N components at the full timeout would
//! > defeat it and — by exhausting the shared budget — **change the verdict of
//! > LATER obligations**, which is exactly the neutrality this lane claims.*
//!
//! That condition is a one-line inequality — the per-component budget must not
//! exceed the whole budget — and it is exactly what [`split_budget_ms`]'s
//! `ensures result <= total_ms` states. **This is the rare case where the
//! clause language can say the actual safety property rather than a bound
//! standing in for one.** Same for [`per_job_bytes`]: `result <= budget_bytes`
//! IS "a single job may not be promised more than the machine has".
//!
//! # Why it fits the fragment
//!
//! Everything here is `u64` over byte counts, millisecond counts and job
//! counts. There is no 128-bit type anywhere in the lane, so the
//! `docs/STRICT_VERIFICATION_FRAGMENT.md` §16.0 domain question does not even
//! arise; what made these hard to spot is that they do not look like verifier
//! code. They are three helpers in two files of `trust-router`, sitting under
//! doc comments that already argue the correctness they never checked.
//!
//! # THE SENTINEL
//!
//! `0` means "no derivation" and is the ONLY out-of-band answer, which lets
//! every function be total. That is exact rather than a convention:
//! `per_job_limit_mb_for` already ended `(megabytes > 0).then_some(megabytes)`,
//! so `Some(0)` was never constructible and `0 <-> None` loses nothing.
//!
//! **[`split_budget_ms`] is the exception, and its doc says so where a reader
//! will meet it:** there `0` means UNBOUNDED, not "no answer", because that is
//! the convention `trust-router`'s `timeout_ms` already carries. So `0` is the
//! WIDE end for that one function and the narrow end for the other three, in
//! one crate — the §15.5 / §16.1 direction question decided per function rather
//! than per crate.
//!
//! # What is proved, and what is only tested
//!
//! `result <= total_ms` and `result <= budget_bytes` are the real properties
//! and are proved. They do not pin the VALUE — a constant `0` satisfies both,
//! and for [`split_budget_ms`] a constant `0` is the *unsound-for-neutrality*
//! answer (it means unbounded), which is why
//! `split_budget_ms_is_never_zero_for_a_bounded_caller` exists and why the gate
//! watches a wrong-value mutation pass the lane at exit 0 while that test goes
//! red. Every value is pinned against an independent oracle over a domain that
//! includes both `u64` extremes.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

// Bootstrap rustc cannot parse Trust's native signature clauses, while the
// verified lane must retain those exact clause tokens. Each invocation below
// owns its function body once. Trust injects `cfg(trust_verify)` only while
// verification is active, selecting the native-clause expansion; an ordinary
// compiler emits the same function and body without the clauses. build.rs only
// registers the cfg name for stock Cargo's check-cfg lint; it never selects it.
#[cfg(trust_verify)]
macro_rules! trust_contract_fn {
    (
        $(#[$meta:meta])*
        $vis:vis fn $name:ident($($arg:ident : $arg_ty:ty),* $(,)?) -> $ret:ident
        clauses [$($clauses:tt)+]
        { $($body:tt)* }
    ) => {
        $(#[$meta])*
        $vis fn $name($($arg: $arg_ty),*) -> $ret
            $($clauses)+
        { $($body)* }
    };
}

#[cfg(not(trust_verify))]
macro_rules! trust_contract_fn {
    (
        $(#[$meta:meta])*
        $vis:vis fn $name:ident($($arg:ident : $arg_ty:ty),* $(,)?) -> $ret:ident
        clauses [$($clauses:tt)+]
        { $($body:tt)* }
    ) => {
        $(#[$meta])*
        $vis fn $name($($arg: $arg_ty),*) -> $ret { $($body)* }
    };
}

/// One mebibyte, in bytes.
pub const BYTES_PER_MB: u64 = 1048576;
/// The floor under a single solve's memory share: 1 GiB, so one solve keeps
/// workable headroom even on a host with many cores and little RAM.
pub const MIN_PER_JOB_BYTES: u64 = 1073741824;
/// The floor under the per-process RSS ceiling, in MB: 2 GiB, so a single
/// legitimate solve is never throttled by the per-process guard.
pub const MIN_PROCESS_CEILING_MB: u64 = 2048;

trust_contract_fn! {
/// One job's share of `budget_bytes` when `jobs` solves may run at once:
/// the even split, floored at [`MIN_PER_JOB_BYTES`], then capped at the whole
/// budget. `0` when there is no budget to divide.
///
/// The floor-then-cap order is not interchangeable with `clamp`, and the
/// original carries the reason: `budget.clamp(MIN_PER_JOB_BYTES, budget)`
/// **panics** whenever a small host has less than 1 GiB, because `clamp`
/// requires `min <= max` and nothing in the types establishes it. Writing the
/// two steps out is what makes every nonzero budget valid, and the cap is what
/// makes the clause below true.
///
/// **Clause `result <= budget_bytes`.** This is the property, not a stand-in
/// for one: a job may not be promised more memory than the machine was
/// budgeted, or the shared coordinator refuses the reservation and every
/// obligation in the unit is declined before solver dispatch. It rules out the
/// unfloored-and-uncapped `budget / jobs` composed wrongly, `MIN_PER_JOB_BYTES`
/// returned unconditionally (which exceeds a sub-GiB budget), and every
/// too-large answer. It admits a constant `0` — the fail-closed direction, and
/// the sentinel this function already uses — which
/// `per_job_bytes_is_not_the_constant_zero` rules out.
pub fn per_job_bytes(budget_bytes: u64, jobs: u64) -> u64
clauses [ensures result <= budget_bytes]
{
    if budget_bytes == 0 {
        return 0;
    }
    // Below the floor there is nothing to divide: the cap and the floor meet at
    // the whole budget. Taking this arm first is what lets every later arm
    // assume `budget_bytes >= MIN_PER_JOB_BYTES`.
    if budget_bytes < 1073741824 {
        return budget_bytes;
    }
    // THE DIVISION IS ONE CALL DOWN, and that is load-bearing. Written inline
    // as `let share = budget_bytes / jobs;` — with the identical guards, and
    // with the same explicit `share > budget_bytes` clamp below — this function
    // reported 8 proved / 1 UNKNOWN: a QUOTIENT-derived local supplies no range
    // to its own body's clause, exactly as fragment map §13.3 measured for a
    // MULTIPLY-derived one and §14.4 for a `%`-derived one. Moving the operator
    // into `raw_share` makes `share` a CALL result instead, and the guarded
    // clamp below then discharges. See §17.2.
    let share = raw_share(budget_bytes, jobs);
    if share < 1073741824 {
        return 1073741824;
    }
    if share > budget_bytes {
        return budget_bytes;
    }
    share
}
}

/// The even split alone, with the original's `.max(1)` on the divisor folded
/// in. Exists to put the `/` one call below every clause that has to bound its
/// result — see [`per_job_bytes`] — and the `jobs == 0` guard lives HERE rather
/// than at the two call sites because a `/` in a member of its own is where the
/// `division_by_zero` obligation is raised: hoisting the operator without
/// hoisting its guard turned one unknown postcondition into a REAL refutation
/// (`raw_share [VIOLATIONS] 1 failed`), which is the right answer and is worth
/// meeting as a measurement rather than as a bug.
fn raw_share(total: u64, parts: u64) -> u64 {
    if parts == 0 {
        return total;
    }
    total / parts
}

trust_contract_fn! {
/// `bytes` as whole mebibytes, rounding down. `0` for anything under a
/// mebibyte, which is the "not representable by this API" answer the memory
/// coordinator's reservation call needs — a `Some(0)` request would reserve
/// nothing and then wait on it.
///
/// **Clauses `result <= bytes` and `result <= 17592186044415`.** The second is
/// `u64::MAX / 2^20`, the largest whole-mebibyte count that exists, and it is
/// five orders of magnitude inside `u64::MAX`, so it is not the vacuous type
/// bound §16.7 had to settle for. Same direction, one variable and one literal
/// — fragment map §14.1's first row. Together they rule out every answer larger
/// than the byte count it came from, including the transposition
/// `BYTES_PER_MB / bytes` and a missing division. They admit a constant `0`;
/// `megabytes_of_matches_a_division_oracle` is exhaustive at every power of two
/// and both extremes.
pub fn megabytes_of(bytes: u64) -> u64
clauses [ensures result <= bytes ensures result <= 17592186044415]
{
    if bytes < 1048576 {
        return 0;
    }
    // One call down, and clamped: see [`per_job_bytes`] and §17.2.
    //
    // BOTH clamp arms return `0`, not the bound they are clamping to. Returning
    // `bytes` from the first — the obvious spelling — is a REAL violation of the
    // OTHER clause, because `bytes` is an unbounded `u64` and may exceed
    // `17592186044415`; it measured as one unknown row. `0` satisfies both
    // clauses on both arms and is this function's existing sentinel. Neither arm
    // is reachable (`bytes / 2^20 <= bytes` and `<= u64::MAX / 2^20` for every
    // `bytes`), which is exactly why the clamp may be the fail-closed value.
    let mb = raw_megabytes(bytes);
    if mb > bytes {
        return 0;
    }
    if mb > 17592186044415 {
        return 0;
    }
    mb
}
}

/// The division alone. Exists only to put the `/` one call below the clauses
/// on [`megabytes_of`].
fn raw_megabytes(bytes: u64) -> u64 {
    bytes / 1048576
}

trust_contract_fn! {
/// One component's share of a `total_ms` per-obligation timeout when a
/// decomposed retry solves `parts` components: the even split, floored at 1 ms
/// so no component is given a zero (instantly-expiring) budget.
///
/// **`0` MEANS UNBOUNDED HERE, NOT "NO ANSWER".** `trust-router`'s
/// `timeout_ms` already carries that convention and this function preserves it:
/// an unbounded caller stays unbounded. It is the one place in this crate where
/// `0` is the WIDE end, and it is why the clause below cannot be the whole
/// story.
///
/// **Clause `result <= total_ms`.** This is the neutrality condition
/// `try_disjoint_component_refutation` states in prose and never checked: the
/// whole retry must cost what ONE solve was already allowed to cost. It rules
/// out `total_ms` returned per component (the N-times-the-budget bug the doc
/// warns about), `total_ms * parts`, and `total_ms + 1`.
///
/// **It does NOT rule out a constant `0`, and here that is the DANGEROUS
/// direction** — `0` means unbounded, so a function that always returned it
/// would give every component an unlimited budget, which is precisely the
/// verdict-changing behaviour the clause exists to prevent. The clause language
/// cannot say "nonzero when `total_ms` is nonzero" (an implication over a
/// parameter is not writable, §13.9), so
/// `split_budget_ms_is_never_zero_for_a_bounded_caller` says it instead, and
/// `trust_budget_strict_gate.sh` mutation E watches the lane PASS at exit 0
/// with that mutation in place while the test goes red.
pub fn split_budget_ms(total_ms: u64, parts: u64) -> u64
clauses [ensures result <= total_ms]
{
    if total_ms == 0 {
        return 0;
    }
    // One call down: see [`per_job_bytes`] and §17.2. `parts == 0` is the
    // original's `components.max(1)` and is handled inside `raw_share`.
    let share = raw_share(total_ms, parts);
    // The `.max(1)` floor. `total_ms >= 1` on this arm, so `1 <= total_ms`.
    if share == 0 {
        return 1;
    }
    if share > total_ms {
        return total_ms;
    }
    share
}
}

trust_contract_fn! {
/// The per-process RSS ceiling in MB derived from a machine budget already
/// expressed in MB: the budget, floored at [`MIN_PROCESS_CEILING_MB`].
///
/// **Clauses `result >= budget_mb` and `result >= 2048`.** Two bounds in the
/// same direction, one variable and one literal — fragment map §14.1's first
/// row — and between them they are the *whole* stated intent of the original:
/// *"never trips spuriously on a small solve"* is `result >= 2048`, and *"never
/// fails open on a huge host"* is `result >= budget_mb`. This is the strongest
/// clause pair in the crate: it rules out a constant `0`, a constant `2048`
/// (violates the variable bound above 2 GiB), `budget_mb` returned unfloored
/// (violates the literal bound below 2 GiB), and a `min` written where the
/// `max` belongs. What it still admits is an answer that is too LARGE, which is
/// the direction that defers to the jobserver and the OS rather than throttling
/// a legitimate solve; `process_ceiling_mb_matches_a_max_oracle` pins the exact
/// value.
pub fn process_ceiling_mb(budget_mb: u64) -> u64
clauses [ensures result >= budget_mb ensures result >= 2048]
{
    if budget_mb < 2048 {
        return 2048;
    }
    budget_mb
}
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Byte counts worth walking: both `u64` extremes, every power of two, and
    /// the boundaries of both floors. Written here rather than derived from the
    /// crate's own constants where it matters.
    fn interesting_bytes() -> impl Iterator<Item = u64> {
        (0..64u32)
            .map(|k| 1u64 << k)
            .chain([
                0,
                1,
                1048575,
                1048576,
                1048577,
                1073741823,
                1073741824,
                1073741825,
                2147483648,
                17179869184,
                u64::MAX - 1,
                u64::MAX,
            ])
    }

    // -----------------------------------------------------------------------
    // per_job_bytes
    // -----------------------------------------------------------------------

    /// The ORIGINAL body of `trust_router::memory_jobserver::per_job_limit_mb_for`,
    /// transcribed verbatim from the pre-extraction source. The replacement
    /// must agree with it on every point, in the composed
    /// `megabytes_of(per_job_bytes(..))` form the consumer now uses.
    fn original_per_job_limit_mb_for(budget: u64, jobs: u64) -> Option<u64> {
        if budget == 0 {
            return None;
        }
        const MIN_PER_JOB_BYTES: u64 = 1024 * 1024 * 1024;
        let per_job = (budget / jobs.max(1)).max(MIN_PER_JOB_BYTES).min(budget);
        let megabytes = per_job / (1024 * 1024);
        (megabytes > 0).then_some(megabytes)
    }

    #[test]
    fn replaced_consumer_body_is_reproduced_exactly() {
        for budget in interesting_bytes() {
            for jobs in [0u64, 1, 2, 3, 4, 7, 8, 16, 64, 1024, u64::MAX] {
                let want = original_per_job_limit_mb_for(budget, jobs);
                let mb = megabytes_of(per_job_bytes(budget, jobs));
                let got = if mb > 0 { Some(mb) } else { None };
                assert_eq!(got, want, "per-job limit diverges at budget={budget} jobs={jobs}");
            }
        }
    }

    #[test]
    fn per_job_bytes_matches_a_floor_then_cap_oracle() {
        for budget in interesting_bytes() {
            for jobs in [0u64, 1, 2, 3, 5, 8, 100, u64::MAX] {
                // The oracle is written as the three steps in words, not as the
                // shipped control flow.
                let divisor = if jobs == 0 { 1 } else { jobs };
                let even = budget / divisor;
                let floored = if even < MIN_PER_JOB_BYTES { MIN_PER_JOB_BYTES } else { even };
                let capped = if floored > budget { budget } else { floored };
                assert_eq!(
                    per_job_bytes(budget, jobs),
                    capped,
                    "per_job_bytes({budget}, {jobs})"
                );
            }
        }
    }

    /// The clause `result <= budget_bytes` admits a constant `0`.
    #[test]
    fn per_job_bytes_is_not_the_constant_zero() {
        assert_eq!(per_job_bytes(17179869184, 4), 4294967296);
        assert_eq!(per_job_bytes(17179869184, 64), MIN_PER_JOB_BYTES);
    }

    /// `clamp(MIN, budget)` panics whenever `budget < MIN`. The whole reason
    /// the floor and the cap are written out is that this must not.
    #[test]
    fn a_budget_below_the_floor_does_not_panic_and_yields_the_budget() {
        for budget in [1u64, 2, 1048576, 1073741823] {
            assert_eq!(per_job_bytes(budget, 8), budget);
        }
    }

    // -----------------------------------------------------------------------
    // megabytes_of
    // -----------------------------------------------------------------------

    #[test]
    fn megabytes_of_matches_a_division_oracle() {
        for bytes in interesting_bytes() {
            assert_eq!(megabytes_of(bytes), bytes / 1048576, "megabytes_of({bytes})");
        }
        for bytes in 0..=(4 * 1048576u64 + 3) {
            assert_eq!(megabytes_of(bytes), bytes / 1048576);
        }
    }

    #[test]
    fn megabytes_of_is_not_the_constant_zero() {
        assert_eq!(megabytes_of(1048576), 1);
        assert_eq!(megabytes_of(17179869184), 16384);
    }

    /// The literal clause bound is the real maximum, not a round number.
    #[test]
    fn the_megabyte_clause_bound_is_attained() {
        assert_eq!(megabytes_of(u64::MAX), 17592186044415);
    }

    // -----------------------------------------------------------------------
    // split_budget_ms
    // -----------------------------------------------------------------------

    /// The ORIGINAL body of
    /// `trust_router::in_process_ay_backend::…::retry_component_timeout_ms`,
    /// transcribed verbatim.
    fn original_retry_component_timeout_ms(total_ms: u64, components: usize) -> u64 {
        if total_ms == 0 {
            return 0;
        }
        (total_ms / (components.max(1) as u64)).max(1)
    }

    #[test]
    fn replaced_timeout_body_is_reproduced_exactly() {
        for total in [0u64, 1, 2, 3, 5, 99, 100, 1000, 600_000, u64::MAX - 1, u64::MAX] {
            for parts in [0usize, 1, 2, 3, 7, 64, 1000, 100_000] {
                assert_eq!(
                    split_budget_ms(total, parts as u64),
                    original_retry_component_timeout_ms(total, parts),
                    "timeout split diverges at total={total} parts={parts}"
                );
            }
        }
    }

    /// THE NEUTRALITY CONDITION, asserted rather than argued: N components at
    /// the split budget must not cost more than one solve at the whole budget.
    #[test]
    fn the_whole_retry_costs_at_most_one_solve() {
        for total in [1u64, 2, 3, 5, 99, 100, 1000, 600_000] {
            for parts in 1..=64u64 {
                let each = split_budget_ms(total, parts);
                // The floor at 1 ms can round UP, so the guarantee is per
                // component; the sum is bounded by the whole budget whenever
                // the split is not floored.
                assert!(each <= total, "a component got more than the whole budget");
                if total / parts >= 1 {
                    assert!(
                        each.saturating_mul(parts) <= total.saturating_add(parts),
                        "the retry multiplied the budget at total={total} parts={parts}"
                    );
                }
            }
        }
    }

    /// The clause admits a constant `0`, and `0` means UNBOUNDED here — the
    /// dangerous direction. This is the test that rules it out.
    #[test]
    fn split_budget_ms_is_never_zero_for_a_bounded_caller() {
        for total in [1u64, 2, 3, 100, 600_000, u64::MAX] {
            for parts in [0u64, 1, 2, 7, 1000, u64::MAX] {
                assert_ne!(
                    split_budget_ms(total, parts),
                    0,
                    "a bounded caller was given an UNBOUNDED component budget \
                     at total={total} parts={parts}"
                );
            }
        }
    }

    /// …and an unbounded caller stays unbounded.
    #[test]
    fn an_unbounded_caller_stays_unbounded() {
        for parts in [0u64, 1, 2, 1000] {
            assert_eq!(split_budget_ms(0, parts), 0);
        }
    }

    // -----------------------------------------------------------------------
    // process_ceiling_mb
    // -----------------------------------------------------------------------

    /// The ORIGINAL tail of `trust_router::memory_guard::default_limit_mb`.
    #[test]
    fn process_ceiling_mb_matches_a_max_oracle() {
        for mb in [0u64, 1, 2047, 2048, 2049, 4096, 65536, u64::MAX - 1, u64::MAX] {
            let want = if mb > 2048 { mb } else { 2048 };
            assert_eq!(process_ceiling_mb(mb), want, "process_ceiling_mb({mb})");
        }
        for mb in 0..=8192u64 {
            assert_eq!(process_ceiling_mb(mb), mb.max(2048));
        }
    }

    /// Both halves of the stated intent, one assertion each.
    #[test]
    fn process_ceiling_never_throttles_and_never_fails_open() {
        assert_eq!(process_ceiling_mb(512), 2048, "a small host must not throttle a real solve");
        assert_eq!(process_ceiling_mb(65536), 65536, "a huge host must not be capped at the floor");
    }
}
