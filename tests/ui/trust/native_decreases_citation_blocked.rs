//@ needs-trust-verify
//@ compile-flags: -Z trust-verify=off
//@ check-fail
//! A cited `decreases` payload is not a closed predicate statement: authority
//! requires a typed before/after measure, strict descent, and well-founded
//! carrier. It remains hard-blocked until that TrustIR obligation exists.

clean {
    theorem zero_eq : 0 = 0 := rfl
    //~^ NOTE Clean island kernel-checked: 1 declaration(s) registered (zero_eq)
}

fn count(mut n: u32) -> u32 {
    while n > 0
        decreases 0 by zero_eq
        //~^ ERROR citation `zero_eq` on a `decreases` clause cannot be validated as a typed well-founded transition obligation
        //~| NOTE decreases citations remain blocked until the before/after measure, strict descent, and well-founded carrier are bound into TrustIR
    {
        n -= 1;
    }
    n
}

fn main() {}
