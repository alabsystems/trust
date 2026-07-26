//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! R4 §1 battery, the WRAP-vs-Int divergence vector (design note §1a): the
//! cited island body `(x * x)` reads over Int, while the citing clause sits
//! in a u64 contract whose body computes `x.wrapping_mul(x)`. At
//! `x = 2^33`, wrapping_mul yields 0 but the Int reading yields 2^66 — the
//! two readings DIVERGE, so when definitional expansion lands, this clause
//! must take the RATIFIED lane's reading and the verdict must come from
//! that reading alone (for the wrapping body, `result == sqr(x)` is FALSE
//! at the divergence point and must FAIL with a counterexample — never
//! silently prove under the other reading). TODAY the citation does not
//! lower at all and the strict build fails on the Unknowns; this pin holds
//! that fail-closed present. Flipping it to anything other than the
//! ratified-lane verdict is a soundness incident.

clean {
    def div_sqr (x : Int) : Int := (x * x)
}

fn wrapped_square(x: u64) -> u64
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    ensures result == div_sqr(x)
{
    x.wrapping_mul(x)
}

fn main() {
    let _ = wrapped_square(3);
}
