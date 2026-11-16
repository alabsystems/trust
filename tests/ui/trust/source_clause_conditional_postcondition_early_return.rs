//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type=lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ forbid-output: was not discharged
//! THE REFERENCE BEHAVIOUR the per-path postcondition split imports — and the
//! fixture that REFUTES "a conditional `ensures` needs a body with at most two
//! return paths".
//!
//! This is the battery's a7 function, semantics for semantics, clause for
//! clause. The only difference from
//! `source_clause_conditional_postcondition_frontier.rs` is that the guards are
//! spelled as early `return`s instead of as one value-producing `if`
//! expression.
//!
//! MEASURED 2026-09-18 on the managed `trustc 1.99.0-dev (d75f13f97 2026-09-15)`
//! BEFORE the split existed, and re-measured identically on the stage1 built
//! from the tree that landed it (`4 proved / 4`, marker discharged — this body
//! has one guard path per `Return` predecessor, so the split does not fire on it
//! and its rows are byte-identical either way). On this exact source: exit 0,
//! "4 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 4
//! obligation(s)", `-Ztrust-verify-output=both` row by row —
//!
//! ```text
//! obligation:…:postcondition:0  proved  trust-exact-source-clause-discharge
//! vc:…:postcondition:0          proved  trust-full-verifier
//! vc:…:postcondition:1          proved  trust-full-verifier
//! vc:…:postcondition:2          proved  trust-full-verifier
//! ```
//!
//! THREE return paths, a non-atomic clause, and the source-clause marker
//! DISCHARGES. So the axis was never the path count and never the connective:
//! rustc gives each `return` its own `Return` block, so each path gets its own
//! FLAT postcondition row, and a flat row of this shape is admitted with a
//! trust-mc PDR receipt. The `if` expression spelling of the same program
//! merges two of its paths into one `goto`-only join, and vcgen emitted that
//! join as ONE row whose path-guard conjunct is `Or([path_1, path_2])` — the
//! only row of the clause that got no receipt.
//!
//! WHY THIS FILE IS NOT REDUNDANT with the frontier fixture. The frontier
//! asserts that the expression spelling now behaves like this one. THIS file
//! asserts the behaviour being imported, and it is measured rather than
//! predicted: if both go red the split regressed something general, and if only
//! the frontier goes red the split did not reach the expression shape. Two
//! fixtures, two different diagnoses.

pub fn pick_ret(a: u32, b: u32) -> u32
    ensures a <= 1000000 ==> result >= a
{
    if a >= 1000000 {
        return 1000000;
    }
    if b >= a {
        return b;
    }
    a
}
