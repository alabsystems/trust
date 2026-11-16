//@ revisions: unopt opt opt3 explicit2
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=off
//@[opt] compile-flags: -O
//@[opt3] compile-flags: -Copt-level=3
//@[explicit2] compile-flags: -O -Zmir-opt-level=2
//@[unopt] check-fail
//@[opt] check-fail
//@[opt3] check-fail
//@[explicit2] build-pass
//@ dont-require-annotations: NOTE
//! TG16 (KERNEL-MIR-PARITY-1): a kernel obligation gets the same verdict in a
//! dev and a release build with verification off.
//!
//! The kernel-only lane E6-imports a function from `optimized_mir`. A verifying
//! session runs MIR opt level 1 at every `-Copt-level`; the vanilla `-O` session
//! ran upstream's level 2, whose inliner rewrites the body the lane imports. A
//! crate that carries a kernel obligation now runs level 1 for its bodies in
//! the vanilla lane too (`PassCtx::for_body`), so `unopt`, `opt` and `opt3`
//! give every citation one verdict.
//!
//! `add2` is level-independent: its `wrapping_add` call (level 1) and the raw
//! `Add` it inlines to (level 2) are both in the E6 fragment, so it discharges
//! in every revision. That shape split the levels until TG14's arithmetic
//! import admitted the raw `Add` (f563f55d64e).
//!
//! `add2_via` is the one that splits. At level 1 its body forwards to
//! `wadd_helper`, a callee with no island identity, and the forwarding gate
//! refuses it; at level 2 the inliner removes the call and the body discharges.
//! Unpinned, it was a hard error in a dev build and built under `--release`.
//!
//! `explicit2` is the control that the pin is what made the difference: an
//! explicit `-Zmir-opt-level=2` is the author's choice and is kept, the inliner
//! runs, and `add2_via` gets the level-2 verdict.

clean {
    def wadd (a b : UInt64) : UInt64 := a + b
    theorem wadd_self : forall (a b : UInt64), wadd a b = wadd a b := fun a b => rfl
}

pub fn add2(a: u64, b: u64) -> u64
    ensures result == wadd(a, b) by wadd_self
    //~^ NOTE kernel-discharges this postcondition statement
{
    a.wrapping_add(b)
}

#[inline]
fn wadd_helper(a: u64, b: u64) -> u64 {
    a.wrapping_add(b)
}

pub fn add2_via(a: u64, b: u64) -> u64
    ensures result == wadd(a, b) by wadd_self
    //[unopt,opt,opt3]~^ ERROR citation `wadd_self` failed the strict Clean statement/certification audit
    //[explicit2]~^^ NOTE kernel-discharges this postcondition statement
{
    wadd_helper(a, b)
}

fn main() {
    let _ = add2(1, 2);
    let _ = add2_via(1, 2);
}
