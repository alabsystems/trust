//@ needs-trust-verify
//@ check-fail
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr
//! **CLOSE NEGATIVE TWIN of `clean_island_standin_import_disclosed.rs`: the
//! stand-in disclosure is not an acceptance path.**
//!
//! A module no Clean-native prelude provider names verbatim is still REFUSED,
//! and the refused island discloses no stand-in: it reports no green for a
//! disclosure to qualify. Every NOTE below is annotated and
//! `dont-require-annotations` is deliberately absent, so a stand-in note
//! appearing on this island fails the test.

clean {
    import Mathlib.Data.Nat.Basic
    def six : UInt64 := 6
}
//~^^^ ERROR unresolved import `Mathlib.Data.Nat.Basic`
//~| NOTE the Clean island was rejected during resolver checking

fn main() {}
