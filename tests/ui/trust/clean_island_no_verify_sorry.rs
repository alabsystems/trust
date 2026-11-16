//@ needs-trust-verify
//@ compile-flags: -Z trust-verify=off
//@ check-fail
//! `-Ztrust-verify=off` disables Rust VC routing, not Clean language integrity.
//! A strict parser island must reject explicit trust debt.

clean {
    theorem hole : True := sorry
}
//~^^ ERROR the publish audit refused this batch

fn main() {}
