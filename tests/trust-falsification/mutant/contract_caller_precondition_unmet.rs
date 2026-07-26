#![crate_type = "lib"]
#![feature(contracts)]
#![allow(incomplete_features)]
// MUTANT (#5-PRE-A — caller-side precondition is a CHECKED obligation): `helper`
// is proved SAFE only under its `#[requires(i < 4)]` (its `a[i]` bounds check is
// discharged by ASSUMING i < 4). `caller` calls it with an UNCONSTRAINED index
// `i`, so it does NOT establish the precondition — the caller-side precondition
// VC `i >= 4` is a real, unmet obligation. Trust must FAIL CLOSED: an
// undischarged caller-side precondition whose violation entails a callee-side L0
// out-of-bounds panic is not a benign coverage gap. Before #5-PRE-A this built
// GREEN under the default strict policy (the caller-side Precondition VC was an
// L1 UNKNOWN bucketed non-fatally), then `caller([0;4], 4)` panicked at runtime.
#[core::contracts::requires(true)]
pub fn caller(a: [u8; 4], i: usize) -> u8 {
    helper(a, i)
}

#[core::contracts::requires(i < 4)]
pub fn helper(a: [u8; 4], i: usize) -> u8 {
    a[i]
}
