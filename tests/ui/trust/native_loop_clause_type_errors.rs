//@ check-fail
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr
//! E4/E5 loop clauses are verifier-language parser islands, but their syntax,
//! lexical bindings, and Bool/Int sorts are checked even when proof is off.

fn integer_invariant(mut n: u32) {
    while n > 0
        invariant n + 1 //~ ERROR invalid `invariant` clause: ill-typed source contract: invariant clause must have sort Bool
    {
        n -= 1;
    }
}

fn boolean_decrease(mut n: u32, flag: bool) {
    while n > 0
        decreases flag //~ ERROR invalid `decreases` clause: ill-typed source contract: decreases clause must have sort Int
    {
        n -= 1;
    }
}

fn unknown_binding(mut n: u32) {
    while n > 0
        invariant ghost > n //~ ERROR invalid `invariant` clause: source-contract variable `ghost` is not in scope
    {
        n -= 1;
    }
}

fn malformed_loop_measure(mut n: u32) {
    while n > 0
        decreases n + //~ ERROR invalid `decreases` clause:
    {
        n -= 1;
    }
}

fn bare_scalar_reference(mut n: u32, bound: &u32) {
    while n > 0
        invariant bound > 0 //~ ERROR invalid `invariant` clause: source-contract variable `bound` is not in scope
    {
        n -= 1;
    }
}

fn scalar_index(mut n: u32, flag: bool) {
    while n > 0
        invariant flag[0] == 0 //~ ERROR invalid `invariant` clause: ill-typed source contract: index requires an Array base
    {
        n -= 1;
    }
}

fn scalar_field(mut n: u32, flag: bool) {
    while n > 0
        invariant flag.nope == 0 //~ ERROR invalid `invariant` clause: ill-typed source contract: ordinary field projection `nope` is unsupported without exact field layout
    {
        n -= 1;
    }
}

fn unsupported_shadow_suppresses_outer_binding(mut n: u32, bound: u32) {
    let bound = || 0u32;
    while n > 0
        invariant bound > 0 //~ ERROR invalid `invariant` clause: source-contract variable `bound` is not in scope
    {
        n -= 1;
    }
    let _ = (bound(), n);
}

fn main() {}
