//@ needs-trust-verify
//@ compile-flags: -Z trust-verify=off
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! Authored citations outside the exact typed-statement fragment are hard
//! errors. The compiler must not guess an unsupported `u128` carrier or
//! silently treat the citation as inert.

clean {
    theorem nat_zero : forall (x : Nat), x + 0 = x := fun x => rfl
}

fn f(x: u128) -> u128
    ensures x + 0 == x
        by nat_zero
        //~^ ERROR citation `nat_zero` cannot be validated because this clause is outside the exact statement fragment
{
    x
}

fn main() {}
