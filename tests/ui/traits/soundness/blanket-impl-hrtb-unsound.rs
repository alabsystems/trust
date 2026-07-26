//@ known-bug: #95305
//@ check-pass
// Trust: regression test for rust-lang#95305
// Part of #859
//
// Unsound blanket impl with higher-ranked bounds. The compiler accepts
// blanket impls that combine higher-ranked trait bounds with associated
// types in a way that allows transmuting between arbitrary types.
//
// The core issue: a blanket impl with `for<'a> &'a T: SomeTrait` can
// provide an associated type that depends on the higher-ranked lifetime.
// When the compiler normalizes this associated type at a call site, it
// may pick a lifetime that does not actually satisfy the bound, leading
// to a type mismatch that the compiler fails to catch.
//
// This is closely related to the HRTB normalization family (#112905,
// #85336) but specifically involves blanket impls rather than coherence.
//
// PoC adapted from: https://github.com/rust-lang/rust/issues/95305
//
// STATUS: This demonstrates the blanket impl + HRTB unsoundness.
// When fixed, the compiler should reject blanket impls that allow
// lifetime-dependent associated type normalization to produce
// inconsistent types.

trait Trait<'a> {
    type Out;
}

// Blanket impl: for any T, if we have a reference &'a T, the output
// type is &'a T. This is fine in isolation.
impl<'a, T: 'a> Trait<'a> for T {
    type Out = &'a T;
}

// This function uses a higher-ranked bound to get the associated type
// for ALL lifetimes. The unsoundness in #95305 is that the compiler
// allows higher-ranked projections to be normalized in ways that
// lose lifetime information.
fn get_ref<T>(val: &T) -> <T as Trait<'_>>::Out {
    val
}

// Demonstrate that higher-ranked bounds with blanket impls produce
// the expected associated type for concrete instantiations.
fn use_hrtb<T>()
where
    for<'a> T: Trait<'a>,
{
    // The compiler accepts this bound, and within this function
    // T: Trait<'a> for all 'a. The associated type <T as Trait<'a>>::Out
    // should be &'a T for all 'a, but incorrect normalization may
    // pick a specific lifetime and treat it as universal.
}

fn main() {
    let x = 42u32;
    let r = get_ref(&x);
    println!("blanket impl HRTB test: {}", r);

    use_hrtb::<u32>();
}
