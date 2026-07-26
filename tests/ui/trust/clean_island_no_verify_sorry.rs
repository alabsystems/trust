//@ needs-trust-verify
//@ compile-flags: -Z trust-verify=off
//@ check-fail
//@ dont-check-compiler-stderr
//! `-Ztrust-verify=off` disables Rust VC routing, not Clean language integrity.
//! A strict parser island must reject explicit trust debt.

clean {
    theorem hole : True := sorry
    //~^ ERROR Clean island declaration `hole` uses explicit `sorry`
}

fn main() {}
