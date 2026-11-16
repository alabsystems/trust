//@ revisions: on off user_sum local_item_forge
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[off] compile-flags: -Ztrust-no-adapter-yield
//@[on] check-pass
//@[off] check-fail
//@[user_sum] check-fail
//@[local_item_forge] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//! Trust (2026-10-04): `ADAPTER_YIELD` through a lazy `map` whose consumer has
//! generic parameters of its own — `sum::<f64>`, `collect::<Vec<f64>>`, and
//! `fold(f64::INFINITY, f64::min)` (a3d_solve `cylindricity_cert::dot_min_over_box` and
//! its coverage folds). The consumer was refused outright; it is admitted when every
//! OWN generic argument and the adapter's item type name only primitives and
//! foundational-crate types and fn items, so its dispatch stays in core/alloc.
//!
//! BEFORE (measured on the stage 1 of `0d0ff693d6`): both closures refused, each
//! index row `[bounds] FAILED` with `i` unconstrained (= the `off` revision).
//!
//! `user_sum` is a DECLINE rail, not a panic witness: `sum::<Total>` names a local
//! type, so the consumer is refused and the closure's rows stay unproved.
//!
//! `local_item_forge` is the false premise the 2026-10-04 review found in the first
//! version of this relaxation (which checked only the consumer's own arguments):
//! `sum::<f64>` over a LOCAL item type `L` dispatches to the orphan-legal user
//! `impl Sum<L> for f64`, which receives the `Map<Range, C>` value as `I`, forges one
//! over `150..151` and calls the closure on `150`; `A[150]` panics. The adapter's item
//! type must be foundational too, so the closure keeps its refuted index row.

#[cfg(any(on, off))]
pub fn dot_min(bx: &[(f64, f64); 6], c: &[f64; 3]) -> f64 {
    (0..3).map(|i| bx[i].0 * c[i]).sum()
}

#[cfg(any(on, off))]
pub fn coverage(n0: &[f64; 3], root: &[(f64, f64); 3]) -> f64 {
    (0..3).map(|i| (n0[i] - root[i].0).min(root[i].1 - n0[i])).fold(f64::INFINITY, f64::min)
}

#[cfg(any(on, off))]
pub fn firsts(c: &[f64; 3]) -> Vec<f64> {
    (0..3).map(|i| c[i]).collect()
}

#[cfg(user_sum)]
pub struct Total(pub f64);

#[cfg(user_sum)]
impl core::iter::Sum<f64> for Total {
    fn sum<I: Iterator<Item = f64>>(iter: I) -> Self {
        Total(iter.fold(0.0, |a, b| a + b))
    }
}

#[cfg(user_sum)]
pub fn user_sum(c: &[f64; 3]) -> Total {
    (0..3).map(|i| c[i]).sum::<Total>()
}

#[cfg(local_item_forge)]
pub struct L(pub f64);

#[cfg(local_item_forge)]
static A: [f64; 3] = [1.0, 2.0, 3.0];

#[cfg(local_item_forge)]
impl core::iter::Sum<L> for f64 {
    fn sum<I: Iterator<Item = L>>(iter: I) -> f64 {
        assert!(core::mem::size_of::<I>() == core::mem::size_of::<core::ops::Range<usize>>());
        let mut forged: I = unsafe { core::mem::transmute_copy(&(150usize..151)) };
        forged.next().map(|l| l.0).unwrap_or(0.0)
    }
}

#[cfg(local_item_forge)]
pub fn local_item_forge() -> f64 {
    (0..3).map(|i| L(A[i])).sum::<f64>()
    //[local_item_forge]~^ ERROR Trust Level 0 safety verification incomplete for `generic_consumer::local_item_forge::{closure#0}`
}
