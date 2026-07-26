//@ compile-flags: -Z trust-verify=off
//@ check-pass
//! The `clean { … }` PARSER ISLAND (two-language design E10): Clean (Lean)
//! declarations at item position — grammar vanilla Rust rejects, so no valid
//! program changes meaning. Verification is off, but island parsing,
//! elaboration, trust-debt rejection, and kernel checking remain mandatory;
//! only Rust VC routing is disabled. `clean!{}` macro invocations keep their
//! vanilla path.

clean {
    def Always (p : Nat -> Prop) : Prop := forall n, p n

    theorem always_unfolds (p : Nat -> Prop) : Always p = Always p := rfl
}

// A macro NAMED clean still works (the island arm requires a brace with no
// `!`, and is guarded by isnt_macro_invocation).
macro_rules! clean_macro {
    () => {
        fn from_macro() -> u32 {
            7
        }
    };
}
clean_macro!();

fn main() {
    let _ = from_macro();
}
