//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --test -Awarnings
//@ check-fail
//@ dont-check-compiler-stderr
#![expect(incomplete_features)]
#![feature(explicit_tail_calls)]

//! A `become` is a normal source-level return but remains a `TailCall` in
//! optimized MIR. Until certified monitor placement can preserve explicit
//! tail-call semantics, an executable ensures must fail closed instead of
//! silently missing that exit path.

fn identity(x: u8) -> u8 {
    x
}

fn tail_identity(x: u8) -> u8
    ensures result == x
    //~^ ERROR certified ensures monitors cannot instrument a function containing an explicit tail call
{
    become identity(x);
}

fn main() {}
