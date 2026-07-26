//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! R4 §1 by-citation battery (design note 2026-07-22): a contract clause
//! CALLING an island-only definition name. TODAY this fails closed as an
//! unsupported compiler-contract predicate: the clause parser retains the
//! call text, but no typed spec-position island-name resolution or
//! definition-pinned unfolding route exists. The §1 target flips this pin
//! ONLY when that full contract lands: PROOF-firewalled lookup against the
//! crate's kernel-checked environment, digest-pinned symbols, and
//! definitional-unfolding discharge (`island_definition_value`). Until then,
//! going green without that machinery is a soundness incident, not progress.

clean {
    def battery_sqr (x : Int) : Int := (x * x)
}

fn double_square(x: u64) -> u64
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    //~| NOTE unsupported contract predicate expression `result == battery_sqr(x)`
    //~| NOTE unsupported MIR `SpecEnsuresUnparseable`
    ensures result == battery_sqr(x)
{
    x
}

fn main() {
    let _ = double_square(3);
}
