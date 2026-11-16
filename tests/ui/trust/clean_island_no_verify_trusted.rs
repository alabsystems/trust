//@ needs-trust-verify
//@ compile-flags: -Z trust-verify=off
//@ check-fail
//! Both trusted automation escape hatches are forbidden in strict islands.
//! NB: the annotations live OUTSIDE the island — the strict Clean parser
//! fail-closes on `//` comment lines inside an island (Lean comments are `--`).
//! RE-PIN 2026-11-15: Clean (bcacce6e0, in the pin since e64e4b7901) ships the
//! admission markers (`sorry`, `trustedArith`, `trustedAy`) in an opt-in fragment,
//! not in the prelude the island registers into, so the island is refused when it
//! names one, before the publish audit that used to refuse it. Still a hard error
//! with nothing registered (docs/OPEN_ISSUES.md ISLAND-MARKER-DIAGNOSTIC-1).

clean {
    theorem arith_debt : True := trustedArith
    theorem ay_debt : True := trustedAy
}
//~^^^ ERROR `arith_debt` did not elaborate: Unknown identifier: trustedArith
//~^^^ ERROR `ay_debt` did not elaborate: Unknown identifier: trustedAy

fn main() {}
