//@ compile-flags: -Z trust-verify=off
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! The pseudo-variable `result` is available only in an `ensures` clause.
//! Citation elaboration must fail closed rather than bind it from the return
//! type, even though the theorem would match a postcondition.

clean {
    theorem u64_refl : forall (x : UInt64), x = x := fun x => rfl
}

pub fn bad_precondition(x: u64) -> u64
    requires result == result by u64_refl
    //~^ ERROR citation `u64_refl` cannot be validated because this clause is outside the exact statement fragment: missing supported type for clause variable `result`
    //~| ERROR invalid `requires` clause: `result` is only allowed in an ensures clause
{
    x
}

fn main() {}
