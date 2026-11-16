//@ needs-trust-verify
//@ compile-flags: -Z trust-verify=off
//@ check-fail
//@ dont-check-compiler-stderr
//! E10 fail-closed even in Rust-compatibility/no-verification mode: an island
//! the Clean CIC kernel rejects FAILS THE BUILD, with the diagnostic
//! span-mapped into the island body. (The annotation sits OUTSIDE the island:
//! its body is Clean text verbatim to the closing `}`, and a `//` line is
//! not a Lean comment.)

clean {
    def bad : Nat := True
}
//~^^ ERROR `bad` did not elaborate: Type mismatch: expected Nat, got Prop

fn main() {}
