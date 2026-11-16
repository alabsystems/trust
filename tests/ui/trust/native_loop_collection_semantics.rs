//@ revisions: slice fixed_array slice_progress mutable_store mutation alias
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-timeout-ms=120000 -Cstrip=none
// The generous per-VC budget is NOT decoration, and NOT a relaxed assertion:
// this fixture asserts that the obligation is PROVABLE, never that it is
// provable within the 5s daily-driver default on a contended machine. Under
// parallel compiletest load the in-process solver's default budget
// intermittently lapses on one row, flipping it PROVED -> unknown, which the
// default policy then makes fatal. Measured 2026-09-21 as a controlled
// sweep of this one variable on an otherwise identical tree:
//     -Ztrust-verify-timeout-ms=200    -> rc=1, 3 proved / 1 unknown
//     -Ztrust-verify-timeout-ms=5000   -> rc=0, 4 proved / 0 unknown
//     -Ztrust-verify-timeout-ms=120000 -> rc=0, 4 proved / 0 unknown
// STRONGER WITNESS, measured 2026-09-21: the serial sweep above shows the axis,
// but this reproduces the actual red ON DEMAND. Running N copies of this very
// fixture concurrently against the same stage1 (self-contention, which is what
// parallel compiletest creates), concurrency 16 on an 18-core box, load ~34:
//     -Ztrust-verify-timeout-ms=5000   -> pass=0  fail=16
//     -Ztrust-verify-timeout-ms=120000 -> pass=16 fail=0
// Serially the row needs between 3000ms and 5000ms, so the 5s default carries
// under 1.7x margin and contention erases it. This also settles a standing
// question: the hardcoded 10s FULL_STARTUP_SMT_TIMEOUT in ay-chc's PDR startup
// discovery does NOT bind this path -- the cancellation is from ay_dpll's
// proof checker, a different module -- or 120000 could not have gone 16/16.
// SOUND, and in the direction that matters: a larger budget can only turn an
// unknown row into a definite verdict, never an unproved obligation into a
// proof (the same argument `verify_full_bundle_with_live_receipts` records
// for the flag itself). Same rationale and same spelling as
// `clean_origin_wrapping_verify_on.rs` and `wrapping_binop_opt_level.rs`.
// Only `slice_progress` was observed flaking, but the flag is crate-wide.
// Checked at the raised budget: `mutation` STILL refuses (rc=1, 2 unknown),
// so the extra budget does not rescue the revision that must fail.

//@[slice] build-pass
//@[fixed_array] build-pass
//@[slice_progress] build-pass
//@[mutable_store] build-pass
//@[mutation] check-fail
//@[alias] build-pass
//@ dont-check-compiler-stderr
//! End-to-end E4 coverage for the deliberately narrow collection model. The
//! immutable positive revisions bind source `xs.len()` and `xs[0]` to the same
//! slice/fixed-array terms used by the MIR transition. The exact mutable
//! revision pins a supported fixed-array Store/Select transition; the mutation
//! negative uses the same admitted shape with a genuinely false invariant. The
//! progress revision pins the exact `usize` domain shared by a slice length,
//! an index invariant, and an E5 distance measure. The alias revision retains
//! an exact immutable view across the loop and passes it to a safe Rust reader;
//! shared scalar collections are Freeze, so that call cannot mutate the modeled
//! sequence in a well-defined execution.

#[cfg(slice)]
pub fn read_slice(xs: &[u32], keep: bool) -> u32
    requires xs.len() > 0
{
    let _n = xs.len();
    let first = xs[0];
    let mut observed = 0;
    while keep invariant _n == xs.len() && first == xs[0] {
        observed = xs[0];
    }
    observed
}

#[cfg(fixed_array)]
pub fn read_fixed_array(xs: &[u32; 4], keep: bool) -> u32 {
    let _n = xs.len();
    let first = xs[0];
    let mut observed = 0;
    while keep invariant _n == xs.len() && first == xs[0] {
        observed = xs[0];
    }
    observed
}

#[cfg(slice_progress)]
pub fn walk_slice(xs: &[u32]) {
    let mut i = 0usize;
    while i < xs.len()
        invariant i <= xs.len()
        decreases xs.len() - i
    {
        i += 1;
    }
}

#[cfg(mutable_store)]
pub fn store_fixed_array(xs: &mut [u32; 4], keep: bool) {
    xs[0] = 7;
    while keep invariant xs[0] == 7 {
        xs[0] = 7;
    }
}

#[cfg(mutation)]
pub fn mutate_fixed_array(xs: &mut [u32; 4], keep: bool) { //[mutation]~ ERROR Trust Level 0 safety verification incomplete for
    //[mutation]~^ ERROR Trust strict verification failed for
    let _n = xs.len();
    let first = xs[0];
    while keep invariant _n == xs.len() && first == xs[0] {
        xs[0] = 1;
    }
}

#[cfg(alias)]
#[inline(never)]
fn observe_alias(xs: &[u32; 4]) -> u32 {
    xs[0]
}

#[cfg(alias)]
pub fn retain_alias(xs: &[u32; 4], keep: bool) -> u32 {
    let alias = xs;
    let _n = alias.len();
    let first = alias[0];
    let mut observed = 0;
    while keep invariant _n == alias.len() && first == alias[0] {
        observed = alias[0];
    }
    let after = observe_alias(alias);
    if observed == after { after } else { observed }
}

fn main() {}
