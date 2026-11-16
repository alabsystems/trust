//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! E9-RESULT-CARRIER-4, the fail-closed twin of
//! `e9_island_alias_bool_result_discharge.rs`. Reading a result through an alias
//! must not prove a false clause, and must not pick a domain for a carrier with
//! several preimages: `Word := BitVec 64` carries `i64`, `u128`, `usize64` alike,
//! so a `Word`-valued call in proposition position stays refused.

clean {
    abbrev Flag := Bool
    abbrev Word := BitVec 64
    def never_flag (a : BitVec 64) : Flag := Bool.false
    def word_zero (a : BitVec 64) : Word := BitVec.ofNat 64 0
}

pub fn false_flag(a: i64) -> bool
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    ensures never_flag(a)
    //~^ ERROR `never_flag` was not discharged by definitional equality: the two sides are not
{
    true
}

pub fn word_valued(a: i64) -> bool
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    ensures word_zero(a)
    //~^ ERROR `word_zero` was not discharged by definitional equality: call to `word_zero` in a
{
    true
}

fn main() {}
