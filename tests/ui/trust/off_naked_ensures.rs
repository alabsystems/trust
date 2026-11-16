//@ revisions: unopt opt
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=off
//@[opt] compile-flags: -O
//@ rustc-env:TRUST_AY_SMT_TRACE=1
//@ build-pass
//@ dont-require-annotations: NOTE
//! TG3: the kernel-only lane is KERNEL work only. An `ensures` without `by` is
//! an SMT obligation (TG13 owns those in every build); with verification off
//! nothing reads it, so this lane makes no solver call.
//!
//! The witness is `naked`, which is FALSE (`x > x`): any engine that ran on it
//! would refute it and fail this build-pass test. Measured 2026-11-05 on the
//! TG3 stage-1 trustc: the same file under `-Ztrust-verify=on` reports `2
//! failed` for `naked` and fails. `TRUST_AY_SMT_TRACE=1` is a second, narrower
//! witness: it makes the in-process `ay` backend print every program it is
//! handed (`[aysmt] ---- program handed to ay ----`) and this test checks its
//! whole stderr. It is narrower because that verify-on run refuted `naked`
//! through another engine without printing an `[aysmt]` line, so its absence
//! alone would prove nothing. `cited` in the same crate keeps the kernel lane
//! busy, so the absence of a refutation is not because the lane did nothing.

clean {
    theorem refl_u64 : forall (x : UInt64), Eq x x := fun x => Eq.refl x
}

pub fn naked(x: u64) -> u64
    ensures result > x
{
    x
}

pub fn cited(x: u64) -> u64
    ensures result == x by refl_u64
    //~^ NOTE kernel-discharges this postcondition statement
{
    x
}

fn main() {
    let _ = naked(1);
    let _ = cited(2);
}
