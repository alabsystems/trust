//@ revisions: slice fixed_array mutation alias
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Cstrip=none
//@[slice] build-pass
//@[fixed_array] build-pass
//@[mutation] check-fail
//@[alias] check-fail
//@ dont-check-compiler-stderr
//! End-to-end E4 coverage for the deliberately narrow read-only collection
//! model. The positive revisions bind source `xs.len()` and `xs[0]` to the
//! same immutable slice/fixed-array terms used by the MIR transition. The
//! negative revisions keep the Rust operations feasible while demonstrating
//! that mutable collection state and retained collection aliases fail closed.

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
pub fn retain_alias(xs: &[u32; 4], keep: bool) -> u32 { //[alias]~ ERROR Trust Level 0 safety verification incomplete for
    //[alias]~^ ERROR Trust strict verification failed for
    let alias = xs;
    let _n = xs.len();
    let first = xs[0];
    while keep invariant _n == xs.len() && first == xs[0] {}
    observe_alias(alias)
}

fn main() {}
