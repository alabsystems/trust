//~ NOTE hardened boundary (process_semantics): std::io::stdio::stdout:
//~| NOTE hardened boundary (process_semantics): std::io::stdio::_print:
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-profile=unix_hardened -Ztrust-verify-output=both
//@ compile-flags: -Ztrust-policy=advisory -Copt-level=0 --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
//@ forbid-output: hardened boundary (process_semantics): std::process::Command::
//@ forbid-output: hardened boundary (process_semantics): std::io::stdio::stderr
//@ forbid-output: hardened boundary (process_semantics): std::io::stdio::_eprint
//! Trust (2026-10-25, hardened `stdout` false match). The hardened
//! `process_semantics` mandate is about THIS process's stdout, whose behaviour on
//! a closed pipe depends on the SIGPIPE disposition. Its rule matched the bare
//! token `stdout`, so it also minted on `std::process::Command::stdout`, which
//! only wires a CHILD's stdout and writes nothing here (claude-code-alab: two of
//! its three `process_semantics` rows). A library is used because no library
//! installs a signal policy, so the mandate stays open for every real writer
//! (`hardened_no_main_mandate_stays.rs`). The rows are read from the JSON
//! transport (`TRUST_JSON` rows, which compiletest files as NOTEs on line 1),
//! the one output that names each row's callee; `advisory` keeps every row and
//! lets the unrelated drop-glue gap in `wire_child` build.
//!
//! NEGATIVE: `wire_child`'s three `Command` configurers carry no
//! `process_semantics` row (`stderr`/`stdin` never matched; `stdout` did until
//! this change, measured on Trust 15698 at 20565c325). POSITIVE CONTROLS:
//! `io::stdout()` and `println!` keep theirs, named by callee. UNCHANGED:
//! `io::stderr()` and `eprintln!` had no `process_semantics` row before this
//! change and have none after; the rule has no stderr needle, and widening it is
//! a separate decision (docs/DECISION_QUEUE.md, HARDENED-STDOUT-DEFPATH).

use std::io::Write;
use std::process::{Command, Stdio};

pub fn wire_child(cmd: &mut Command) {
    cmd.stdout(Stdio::piped());
    cmd.stderr(Stdio::null());
    cmd.stdin(Stdio::null());
}

pub fn write_stdout() {
    let _ = std::io::stdout().write_all(b"x");
}

pub fn shout() {
    println!("hello");
}

pub fn write_stderr() {
    let _ = std::io::stderr().write_all(b"x");
}

pub fn whisper() {
    eprintln!("hello");
}
