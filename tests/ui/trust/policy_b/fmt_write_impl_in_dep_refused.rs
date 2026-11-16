//@ needs-trust-verify
//@ aux-build: policy_b_unverified_dep.rs
//@ compile-flags: -Ztrust-verify=on -Copt-level=0
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//! Refuted 2026-09-16 (fold-mask lens, resumed): the fold mask's "fmt machinery in
//! authentic core/alloc" exemption covered every item under a `fmt` module, TRAIT
//! METHODS included. A trait-method call is spelled with the trait item
//! (`core::fmt::Write::write_str`) and its target in `Self`, so this direct call
//! into the verify-off dependency's own `fmt::Write` impl was exempt from the
//! foreign-reach walk, co-folded under `println!`'s tolerated print row, and the
//! binary panicked in `dep` with every reported row "accounted for". The
//! exemption now excludes trait methods: `Self` is walked like any type argument,
//! `dep::Buf` reaches foreign user code, the tolerance is withheld, the build is
//! refused.
extern crate policy_b_unverified_dep as dep;
use std::fmt::Write as _;

fn main() {
    //~^ ERROR Trust full verification failed
    let k = std::env::args().count() as u8;
    let mut b = dep::Buf(k);
    println!("{k}");
    let _ = b.write_str(if k == 3 { "3" } else { "x" });
    println!("{}", b.0);
}
