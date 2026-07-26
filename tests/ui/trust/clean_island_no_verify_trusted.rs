//@ needs-trust-verify
//@ compile-flags: -Z trust-verify=off
//@ check-fail
//@ dont-check-compiler-stderr
//! Both trusted automation escape hatches are forbidden in strict islands.
//! NB: the annotations live OUTSIDE the island — the strict Clean parser
//! fail-closes on `//` comment lines inside an island (Lean comments are `--`).

clean {
    theorem arith_debt : True := trustedArith
    theorem ay_debt : True := trustedAy
}
//~^^^ ERROR Clean island declaration `arith_debt` uses `trustedArith`
//~^^^ ERROR Clean island declaration `ay_debt` uses `trustedAy`

fn main() {}
