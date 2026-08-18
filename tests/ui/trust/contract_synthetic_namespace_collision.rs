//@ needs-trust-verify
//@ revisions: positional predicate prestate generated generated_param generated_local
//@ compile-flags: -Z trust-verify=off
//@ check-fail
//@ dont-check-compiler-stderr
//! Contract lowering must be injective. These names are legal Rust identifiers,
//! but they overlap the compatibility encoding for `old(x)`, positional MIR
//! places, the predicate vocabulary, or the reserved `__` metadata family.
//! Admitting them in a contracted scope can turn a deliberately false relation
//! into `x == x`.
//!
//! Modeled accessor projections (`xs.len()` and friends) are NOT in this test
//! any more: they are minted inside the reserved `__` family (`xs__len`), so
//! single-underscore spellings such as `xs_len`, `max_len`, or `x_value_sign`
//! are ordinary bindings. The positive coverage lives in
//! `contract_projection_named_params_verify.rs`.

#[cfg(positional)]
fn positional_alias(x: u64, _2: u64) -> u64
    //[positional]~^ ERROR parameter `_2` collides with the source-contract positional MIR-place namespace
    ensures 0 == 0
{
    x + _2
}

#[cfg(predicate)]
fn predicate_alias(priv_dropped: bool) -> bool
    //[predicate]~^ ERROR parameter `priv_dropped` collides with the source-contract predicate-symbol namespace
    requires priv_dropped() == priv_dropped
{
    priv_dropped
}

#[cfg(prestate)]
fn prestate_alias(x: u64, old_x: u64) -> u64
    //[prestate]~^ ERROR parameter `old_x` collides with the source-contract synthetic pre-state namespace
    ensures 0 == 0
{
    x + old_x
}

#[cfg(generated)]
fn generated_projection_alias(xs: &[u64], xs__len: usize) -> usize
    //[generated]~^ ERROR parameter `xs__len` collides with Trust's generated Formula metadata namespace
    ensures 0 == 0
{
    xs.len() + xs__len
}

#[cfg(generated_param)]
fn generated_metadata_alias(s: &[u64], s__slice_len: usize) -> usize
    //[generated_param]~^ ERROR parameter `s__slice_len` collides with Trust's generated Formula metadata namespace
    ensures 0 == 0
{
    s.len() + s__slice_len
}

#[cfg(generated_local)]
fn generated_metadata_loop_local(mut n: usize) {
    let __trust_constparam_0_N = 1usize;
    while n > 0
        invariant n <= __trust_constparam_0_N
        //[generated_local]~^ ERROR invalid `invariant` clause: visible binding `__trust_constparam_0_N` collides with the synthetic contract-variable namespace
    {
        n -= 1;
    }
}

fn main() {}
