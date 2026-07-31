//@ revisions: slice fixed_array slice_progress mutable_store mutation alias
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Cstrip=none
//@[slice] build-pass
//@[fixed_array] build-pass
//@[slice_progress] build-pass
//@[mutable_store] build-pass
//@[mutation] check-fail
//@[alias] check-fail
//@ dont-check-compiler-stderr
//! End-to-end E4 coverage for the deliberately narrow collection model. The
//! immutable positive revisions bind source `xs.len()` and `xs[0]` to the same
//! slice/fixed-array terms used by the MIR transition. The exact mutable
//! revision pins a supported fixed-array Store/Select transition; the mutation
//! negative uses the same admitted shape with a genuinely false invariant. The
//! progress revision pins the exact `usize` domain shared by a slice length,
//! an index invariant, and an E5 distance measure. The alias negative keeps
//! the Rust operation feasible while demonstrating that retained collection
//! aliases still fail closed.

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
pub fn retain_alias(xs: &[u32; 4], keep: bool) -> u32 { //[alias]~ ERROR Trust Level 0 safety verification incomplete for
    //[alias]~^ ERROR Trust strict verification failed for
    let alias = xs;
    let _n = xs.len();
    let first = xs[0];
    while keep invariant _n == xs.len() && first == xs[0] {}
    observe_alias(alias)
}

fn main() {}
