//@ revisions: off adv
//@ needs-trust-verify
//@[off] compile-flags: -Ztrust-verify=off
//@[adv] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory
//@ run-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ forbid-output: E0391
//@ forbid-output: cycle detected
//! A Clean `def` that calls a Rust `const fn`, evaluated from inside type checking:
//! an array length in a signature (`sized`) and in a body (`counted`, through `N`).
//!
//! Drop-in (release gate): the verify-off lane builds and runs this, and so must
//! the verified lane. On `origin/main` `93f05556da` the verified lane rejected it
//! with E0391: const evaluation of the length demands `mir_for_ctfe(twice_inc)`,
//! whose faithfulness gate runs the purity guard over its Rust callee `inc`; the
//! guard read `optimized_mir(inc)`, which (with verification on) forces the crate
//! call-graph oracles — reading every fn's elaborated MIR, so `typeck` of the very
//! fn whose type or body is being checked. The guard now reads
//! `trust_rust_purity_fact(inc)`, a fact of `inc`'s pre-steal elaborated MIR, which
//! depends on `inc`'s own pipeline only.

#![allow(dead_code)]

const fn inc(x: u64) -> u64 {
    x.wrapping_add(1)
}

clean {
    def twice_inc (x : UInt64) : UInt64 := inc (inc x)
}

pub fn sized() -> [u8; twice_inc(1) as usize] {
    [0; 3]
}

const N: usize = twice_inc(1) as usize;

pub fn counted() -> usize {
    let a = [0u8; N];
    a.len()
}

fn main() {
    assert_eq!(sized().len(), 3);
    assert_eq!(counted(), 3);
}
