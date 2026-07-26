//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! E9 domain safety: a `Nat` theorem cited for a `u64` clause must fail closed.
//! Exact per-clause filtering must reach the kernel's statement comparison,
//! not misclassify unrelated function bindings as an outside-fragment error.

clean {
    theorem nat_refl : forall (x : Nat), x = x := fun x => rfl
}

pub fn f_bad(x: u64) -> u64
    ensures result == result by nat_refl
    //~^ ERROR citation `nat_refl` failed the strict Clean statement/certification audit
{
    x
}

fn main() {
    let _ = f_bad(3);
}
