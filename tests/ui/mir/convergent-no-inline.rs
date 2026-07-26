// Regression test for rust-lang#137086
// Verifies that #[rustc_convergent] functions are not inlined.
// Trust: convergent operations must not be inlined because inlining
// changes the call-site context, breaking synchronization semantics.

//@ compile-flags: -Zmir-opt-level=3
//@ known-bug: #859
// The #[rustc_convergent] attribute surface is Trust roadmap work; until it
// exists, the honest expectation is the unknown-attribute error below.

#![feature(rustc_attrs)]

#[rustc_convergent]
#[inline(always)]
fn gpu_barrier() {
    // Simulates a GPU barrier/synchronization primitive.
    // In real code this would be an intrinsic or FFI call.
    core::hint::black_box(());
}

pub fn workgroup_operation() -> u32 {
    let a = core::hint::black_box(1u32);
    gpu_barrier();
    let b = core::hint::black_box(2u32);
    a + b
}

fn main() {
    workgroup_operation();
}
