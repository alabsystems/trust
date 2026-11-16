//~ NOTE hardened boundary (process_semantics): std::process::Command::stdout::<hardened_stdio_conversion_dep::Loud>:
//~| NOTE hardened boundary (process_semantics): std::process::Command::stdout::<alloc::boxed::Box<hardened_stdio_conversion_dep::Loud>>:
//~| NOTE hardened boundary (process_semantics): std::process::Command::stdout::<&hardened_stdio_conversion_dep::Loud>:
//~| NOTE hardened boundary (process_semantics): std::process::Command::stdout::<hardened_stdio_conversion_dep::Direct>:
//~| NOTE hardened boundary (process_semantics): std::process::Command::stdout::<T>:
//~| NOTE hardened boundary (process_semantics): <hardened_command_stdio_exclusion_is_exact::Foo as hardened_command_stdio_exclusion_is_exact::T>::std::process::Command::stdout:
//~| NOTE hardened boundary (process_semantics): std::io::stdio::stdout:
// ignore-tidy-linelength
//@ needs-trust-verify
//@ aux-build: hardened_stdio_conversion_dep.rs
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-profile=unix_hardened -Ztrust-verify-output=both
//@ compile-flags: -Ztrust-policy=advisory -Copt-level=0 --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
//@ forbid-output: hardened boundary (process_semantics): std::process::Command::stdout::<std::process::Stdio>
//@ forbid-output: hardened boundary (process_semantics): std::process::Command::stdout::<std::fs::File>
//! Trust (2026-10-26, adversarial review of HARDENED-STDOUT-DEFPATH). The
//! `stdout` rule's exclusion of std's child-stdio configurer must name the call
//! WITH its generic argument and compare the whole callee, because
//! `Command::stdout<T: Into<Stdio>>` runs `cfg.into()`: for a dependency's type
//! that is the dependency's code, and the auxiliary crate's conversions print.
//! The first version compared def-path segments with generic arguments stripped
//! and dropped every `<…>`-prefixed segment, so it withheld each row required
//! below (measured on its stage 1: zero `process_semantics` rows for the five
//! `Command::stdout` calls and none for `Foo::std`'s call site).
//!
//! REQUIRED (each by callee): the four dependency conversions; a caller's type
//! parameter `T`, which can be any `Into<Stdio>`; the call site of a fn-local
//! `process::Command::stdout` inside a trait-impl method named `std` (whose
//! rendered callee ends in the std spelling behind a qualified prefix); and the
//! positive control `io::stdout()`. FORBIDDEN: the rows for std's own writeless
//! sources (`Stdio`, `File`), which the exclusion still covers. Rows are read
//! from the JSON transport (`TRUST_JSON` rows, filed as NOTEs on line 1), the
//! one output that names each row's callee; a library, so no signal policy
//! closes the mandate (`hardened_no_main_mandate_stays.rs`).

extern crate hardened_stdio_conversion_dep as dep;

use std::process::{Command, Stdio};

pub fn wire_dep(cmd: &mut Command) {
    cmd.stdout(dep::Loud);
}

pub fn wire_dep_box(cmd: &mut Command) {
    cmd.stdout(Box::new(dep::Loud));
}

pub fn wire_dep_ref(cmd: &mut Command, loud: &dep::Loud) {
    cmd.stdout(loud);
}

pub fn wire_dep_into(cmd: &mut Command) {
    cmd.stdout(dep::Direct);
}

pub fn wire_generic<T: Into<Stdio>>(cmd: &mut Command, cfg: T) {
    cmd.stdout(cfg);
}

pub fn wire_std(cmd: &mut Command, file: std::fs::File) {
    cmd.stdout(Stdio::piped());
    cmd.stdout(file);
}

pub struct Foo;

pub trait T {
    fn std(&self);
}

impl T for Foo {
    fn std(&self) {
        mod process {
            pub struct Command;
            impl Command {
                pub fn stdout(&mut self) {
                    use std::io::Write;
                    let _ = std::io::stdout().write_all(b"x");
                }
            }
        }
        process::Command.stdout();
    }
}
