//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-timeout-ms=120000 -Cstrip=none
// The generous per-VC budget is NOT decoration, and NOT a relaxed assertion:
// this fixture asserts that the obligation is PROVABLE, never that it is
// provable within the 5s daily-driver default on a contended machine. Under
// parallel compiletest load the in-process solver's default budget
// intermittently lapses on one row, flipping it PROVED -> unknown, which the
// default policy then makes fatal. Measured 2026-09-21 as a controlled
// sweep of this one variable on an otherwise identical tree:
//     -Ztrust-verify-timeout-ms=200    -> rc=1, 5 proved / 1 unknown
//     -Ztrust-verify-timeout-ms=5000   -> rc=0, 6 proved / 0 unknown
//     -Ztrust-verify-timeout-ms=120000 -> rc=0, 6 proved / 0 unknown
// STRONGER WITNESS, measured 2026-09-21: the serial sweep above shows the axis,
// but this reproduces the actual red ON DEMAND. Running N copies of this very
// fixture concurrently against the same stage1 (self-contention, which is what
// parallel compiletest creates), concurrency 16 on an 18-core box, load ~34:
//     -Ztrust-verify-timeout-ms=5000   -> pass=0  fail=16
//     -Ztrust-verify-timeout-ms=120000 -> pass=16 fail=0
// Serially the row needs between 3000ms and 5000ms, so the 5s default carries
// under 1.7x margin and contention erases it. CORRECTED 2026-09-28: the lapse
// was in ay-chc, not ay_dpll's proof checker. The termination row is one
// nullary `error` fact; `try_acyclic_safety_proof` proved it in one SMT check
// but left the fact's locals free, so `verify_model` discarded every such
// model and the solve fell through to the full PDR search; and a found model
// was re-checked with a FIXED 2s per rule whatever the caller's budget
// (`CandidateNotAdmitted` under load). ay d2b0ce3e6 closes the fact exactly
// and 6ba257a28 makes the Safe-boundary check follow the caller's budget;
// measured with 72 CPU-spinning processes, 12 concurrent compiles: fixed
// 12/12 pass, before 0/12 (the pre-fix red was load, not the pin move).
// SOUND, and in the direction that matters: a larger budget can only turn an
// unknown row into a definite verdict, never an unproved obligation into a
// proof (the same argument `verify_full_bundle_with_live_receipts` records
// for the flag itself). Same rationale and same spelling as
// `clean_origin_wrapping_verify_on.rs` and `wrapping_binop_opt_level.rs`.

//@ build-pass
//@ dont-check-compiler-stderr
//! Projection-suffixed identifiers are ORDINARY user bindings on
//! contract-bearing functions. The modeled accessors mint their leaves inside
//! the reserved `__` family (`xs.len()` -> `xs__len`), so a parameter named
//! `max_len` — or even `xs_len` next to a slice `xs` that the clause projects
//! with `xs.len()` — never collides with a synthetic leaf and must compile AND
//! verify. Before the namespacing fix, every function below was a hard error:
//! "parameter `max_len` collides with the source-contract synthetic projection
//! namespace".
//!
//! Verification is live here: `-Ztrust-verify=on` under `build-pass` turns any
//! unproven obligation into a build error (see
//! `native_loop_collection_semantics.rs`, whose [mutation] revision fails with
//! "Trust strict verification failed" under these same flags). The loop shapes
//! below mirror that test's PROVEN [slice] / [slice_progress] revisions.

// The orca-alab regression shape: a contract-bearing fn whose parameter is
// legitimately named `max_len` and is used by the clauses.
pub fn count_up_to(max_len: usize) -> usize
    requires max_len > 0
    ensures 0 == 0
{
    let mut i = 0usize;
    while i < max_len
        invariant i <= max_len
        decreases max_len - i
    {
        i += 1;
    }
    i
}

// A parameter named EXACTLY like the old projection compatibility spelling,
// next to the slice it used to alias, with the clause projecting `xs.len()`:
// the minted `xs__len` leaf and the `xs_len` parameter stay distinct, so the
// requires is a real relation (not `x == x`) and the function still verifies.
pub fn slice_with_len_param(xs: &[u32], xs_len: usize) -> usize
    requires xs_len == xs.len()
    ensures 0 == 0
{
    let _ = xs;
    xs_len
}

// The PROVEN `[slice]` shape from `native_loop_collection_semantics.rs`, with
// the loop-local renamed to the once-colliding spelling `xs_len`.
pub fn read_slice_with_len_local(xs: &[u32], keep: bool) -> u32
    requires xs.len() > 0
{
    let xs_len = xs.len();
    let first = xs[0];
    let mut observed = 0;
    while keep invariant xs_len == xs.len() && first == xs[0] {
        observed = xs[0];
    }
    observed
}

// Chained/aliased suffix spellings (`x_value_sign` was rejected as a chained
// projection; `x_discr` and `max_value` as accessor leaves) are ordinary too.
pub fn chained_suffix_params(x_value_sign: i64, x_discr: u64, max_value: u64) -> u64
    ensures 0 == 0
{
    let _ = (x_value_sign, x_discr);
    max_value
}

fn main() {}
