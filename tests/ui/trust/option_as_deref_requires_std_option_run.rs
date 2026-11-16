//@ run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: option_as_deref_dep.rs
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -Coverflow-checks=on
//@ error-pattern: user Option::as_deref panics
//@ ignore-emscripten no processes
//@ dont-check-compiler-stderr
//! The runtime WITNESS for `option_as_deref_requires_std_option.rs`: the dependency's
//! `Option::as_deref` panics, so `victim` panics. Codegen never sees the sentinel
//! rewrite, so the program panics BEFORE and AFTER; what the fix changes is the
//! verdict on `victim`.
//!
//! BEFORE (stage 1 of `38e6c69b1c`, `scratchpad/stage1-w11fix`, this file's flags,
//! 2026-10-04): `victim` was "trivially panic-free", so the build printed one warning
//! (on `main`), the `victim` annotation below did not fire, and the program panicked
//! with the message above (exit 101).
//!
//! AFTER (predicted, then measured): `victim` keeps its absent-callee may-panic row, a
//! warning under advisory. Derived on the same stage 1 from a twin whose dependency
//! type is named `Opt`: it built with exactly the two warnings annotated here, and the
//! binary panicked with that message, exit 101.
//! Measured on the stage 1 of `4463aeeb6d` (2026-10-04): the build prints the annotated
//! warnings and the run panics `user Option::as_deref panics` (exit 101).

extern crate option_as_deref_dep as dep;

fn victim(o: &dep::Option) -> u8 {
    //~^ WARN Trust Level 0 safety verification incomplete for `option_as_deref_requires_std_option_run::victim`: 1 obligation(s) were not proved
    o.as_deref()
}

fn main() {
    //~^ WARN Trust Level 0 safety verification incomplete for `option_as_deref_requires_std_option_run::main`: 1 obligation(s) were not proved
    let o = dep::Option(Box::new(1u8));
    println!("{}", victim(std::hint::black_box(&o)));
}
