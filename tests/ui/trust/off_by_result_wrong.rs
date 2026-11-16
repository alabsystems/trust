//@ revisions: unopt opt
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=off
//@[opt] compile-flags: -O
//@ check-fail
//@ dont-require-annotations: NOTE
//! TG3: an `ensures … by` whose clause mentions `result` is JUDGED with
//! verification off. Before TG3 this lane imported no body, so `result` had no
//! kernel denotation and the citation got a note saying it was NOT checked; a
//! wrong citation built. Now the kernel-only lane imports the function's body
//! and the cited theorem must prove the clause with `result` bound to it.
//!
//! `keep_ok` and `keep_bad` carry the same clause and the same citation; only
//! the body differs. `refl_u64` proves `x = x`, which is the goal for
//! `keep_ok` (its imported definition unfolds to `x`) and not for `keep_bad`
//! (it unfolds to `x + 1`). So the pair pins that the verdict reads the body.

clean {
    theorem refl_u64 : forall (x : UInt64), Eq x x := fun x => Eq.refl x
}

pub fn keep_ok(x: u64) -> u64
    ensures result == x by refl_u64
    //~^ NOTE kernel-discharges this postcondition statement
{
    x
}

pub fn keep_bad(x: u64) -> u64
    ensures result == x by refl_u64
    //~^ ERROR citation `refl_u64` failed the strict Clean statement/certification audit
{
    x.wrapping_add(1)
}

fn main() {
    let _ = keep_ok(1);
    let _ = keep_bad(2);
}
