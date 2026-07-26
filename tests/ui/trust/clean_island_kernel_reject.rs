//@ needs-trust-verify
//@ compile-flags: -Z trust-verify=off
//@ check-fail
//@ dont-check-compiler-stderr
//! E10 fail-closed even in Rust-compatibility/no-verification mode: an island
//! the Clean CIC kernel rejects FAILS THE BUILD, with the diagnostic
//! span-mapped into the island body.

clean {
    def bad : Nat := True
    //~^ ERROR Clean island declaration rejected
}

fn main() {}
