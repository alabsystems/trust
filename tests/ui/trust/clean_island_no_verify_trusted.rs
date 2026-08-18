//@ needs-trust-verify
//@ compile-flags: -Z trust-verify=off
//@ check-fail
//! Both trusted automation escape hatches are forbidden in strict islands.
//! NB: the annotations live OUTSIDE the island — the strict Clean parser
//! fail-closes on `//` comment lines inside an island (Lean comments are `--`).

clean {
    theorem arith_debt : True := trustedArith
    theorem ay_debt : True := trustedAy
}
//~^^^ ERROR the publish audit refused this batch
// `ay_debt`/`trustedAy` is reported in the SAME diagnostic's issue list (the
// publish audit refuses the batch once and enumerates every debt), so it
// cannot carry its own annotation — one expectation per diagnostic.

fn main() {}
