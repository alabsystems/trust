//@ needs-trust-verify
//@ compile-flags: -Z trust-verify=off
//@ check-fail
//! `-Ztrust-verify=off` disables Rust VC routing, not Clean language integrity.
//! A strict parser island must reject explicit trust debt.
//! RE-PIN 2026-11-15: Clean (bcacce6e0, in the pin since e64e4b7901) ships the
//! admission markers (`sorry`, `trustedArith`, `trustedAy`) in an opt-in fragment,
//! not in the prelude the island registers into, so the island is refused when it
//! names one, before the publish audit that used to refuse it. Still a hard error
//! with nothing registered (docs/OPEN_ISSUES.md ISLAND-MARKER-DIAGNOSTIC-1).

clean {
    theorem hole : True := sorry
}
//~^^ ERROR `hole` did not elaborate

fn main() {}
