//@ needs-trust-verify
//@ compile-flags: --test -Ztrust-verify=on -Ztrust-verify-output=both
//@ build-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//~? RAW Trust: EXCLUDED [test-harness-synthesized] 6 body/bodies rustc's libtest harness synthesized (5 test runner closure(s), 1 harness main(s))
//~^^^^^^^ NOTE "kind":"excluded:test-harness-synthesized"
//~| NOTE "kind":"excluded:test-harness-synthesized"
//~| NOTE "kind":"excluded:test-harness-synthesized"
//~| NOTE "kind":"excluded:test-harness-synthesized"
//~| NOTE "kind":"excluded:test-harness-synthesized"
//~| NOTE "kind":"excluded:test-harness-synthesized"
//! Trust (CB4): under the DEFAULT strict policy a `--test` crate whose own
//! bodies verify builds — the code rustc's libtest harness synthesizes around
//! the tests is EXCLUDED from the proof inventory, with one disclosed
//! `excluded:test-harness-synthesized` row per excluded body and one human
//! summary line, never proof.
//!
//! Before CB4 every `#[test]` below raised `Trust strict verification failed for
//! `…::{closure#0}`` (`[trust-absent-callee-assumption] call to absent callee
//! `test::assert_test_result::<…>``) and the harness `main` raised `Trust full
//! verification failed for `…::main`` (`MissingObligationSourceSpan`: rustc
//! builds it at `DUMMY_SP`) — MEASURED on the same shapes (`unit`, `shapes`,
//! nested, `macro_rules!`), so this file failed with six unexpected errors.
//!
//! The shapes: a plain test calling a proved library fn, a `Result`-returning
//! test, a test in a module, a `macro_rules!`-generated test (the builtin
//! expander gives it `with_def_site_ctxt` spans, so provenance survives the
//! wrapper), and a test nested in a fn body (unnameable, so the harness never
//! runs it, but its descriptor and closure are still generated).
//!
//! The six `excluded:test-harness-synthesized` wire rows arrive as NOTE
//! diagnostics carrying the crate-root span (line 1), which is why their
//! annotations point at line 1 rather than being unspanned: MEASURED on
//! the Track B stage 1 (2026-09-28), 5 runner closures + 1 harness `main`.

pub fn add1(x: u8) -> u8 {
    if x < 255 { x + 1 } else { x }
}

#[test]
fn calls_add1() {
    let _ = add1(3);
}

#[test]
fn returns_result() -> Result<(), ()> {
    Ok(())
}

mod nested {
    #[test]
    fn in_module() {}
}

macro_rules! make_test {
    ($name:ident) => {
        #[test]
        fn $name() {}
    };
}

make_test!(from_macro);

pub fn outer() {
    #[test]
    fn inner_unnameable() {}
}
