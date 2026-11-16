// Trust: KNOWN_HAZARDS "FIXED 2026-09-30 (residuals OPEN)", R-c (the by-value `ensures`
// false-proof class). An `ensures` names a parameter's ENTRY value. `setf` stores into a
// FIELD of its by-value parameter and returns it, so `result == p.a` is false (it returns
// the entry `p.a` plus 5, and `wrapping_add(5)` never returns its input). The mutated-
// parameter guard saw only whole-local writes, so the clause was checked against the
// return-time `p.a` and certify exited 0 with both postcondition rows `proved`. A
// parameter that is not single-static-assignment (modulo pointee borrows) is now treated
// as mutated, and the clause fails closed.
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ compile-flags: -Ztrust-verify-output=json --error-format=human
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//@ forbid-output: "line_start":28,"col_start":12,"line_end":28,"col_end":25},"outcome":"proved"
//@ forbid-output: "line_start":27,"col_start":0,"line_end":32,"col_end":1},"outcome":"proved"

pub struct Pair {
    pub a: u32,
    pub b: u32,
}

pub fn setf(mut p: Pair) -> u32
    ensures result == p.a
{
    p.a = p.a.wrapping_add(5);
    p.a
}
