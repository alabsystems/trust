//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Cstrip=none
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
