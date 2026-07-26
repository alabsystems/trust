//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ normalize-stderr: "elapsed_ms=\d+" -> "elapsed_ms=$$TIME"
//! Falsification pair of `e9_definitional_call_discharge`: (1) the same
//! call-bearing clause WITHOUT a citation stays a fail-closed build error;
//! (2) a citation whose theorem does not prove the clause fails closed.

pub fn ident(x: u64) -> u64 { x }

pub fn no_citation(x: u64) -> u64
    //~^ ERROR Trust Level 0 safety verification incomplete for
    //~| ERROR Trust strict verification failed for
    ensures ident(x) >= ident(x)
{ x }

clean {
    theorem triv : True := True.intro
}

pub fn wrong_theorem(x: u64) -> u64
    //~^ ERROR Trust Level 0 safety verification incomplete for
    //~| ERROR Trust strict verification failed for
    ensures ident(x) >= ident(x) by triv
    //~^ ERROR citation `triv`
{ x }

fn main() {}
