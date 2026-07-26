//@ needs-trust-verify
//@ revisions: positional predicate prestate projection chain generated_param generated_local loop_alias binder_alias
//@ compile-flags: -Z trust-verify=off
//@ check-fail
//@ dont-check-compiler-stderr
//! Contract lowering must be injective. These names are legal Rust identifiers,
//! but they overlap the compatibility encoding for `old(x)`, collection/model
//! projections, or chained projections. Admitting them in a contracted scope
//! can turn a deliberately false relation into `x == x`.

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

#[cfg(projection)]
fn projection_alias(xs: &[u64], xs_len: usize) -> usize
    //[projection]~^ ERROR parameter `xs_len` collides with the source-contract synthetic projection namespace
    ensures 0 == 0
{
    xs.len() + xs_len
}

#[cfg(chain)]
fn chained_projection_alias(x: u64, x_value_sign: i64) -> i64
    //[chain]~^ ERROR parameter `x_value_sign` collides with the source-contract synthetic projection namespace
    ensures 0 == 0
{
    x as i64 + x_value_sign
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

#[cfg(loop_alias)]
fn false_loop_alias(xs: &[u64]) {
    let xs_len = 0usize;
    while xs_len < 1
        invariant xs.len() == xs_len
        //[loop_alias]~^ ERROR invalid `invariant` clause: visible binding `xs_len` collides with the synthetic contract-variable namespace
    {
        break;
    }
}

#[cfg(binder_alias)]
fn false_binder_alias(xs: &[u64]) {
    while !xs.is_empty()
        invariant forall xs_len: usize, xs.len() == xs_len
        //[binder_alias]~^ ERROR invalid `invariant` clause
    {
        break;
    }
}

fn main() {}
