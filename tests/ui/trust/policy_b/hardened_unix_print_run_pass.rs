//@ needs-trust-verify
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-profile=unix_hardened -Copt-level=0
//@ run-pass
//! The lane `targo trust build` selects by default. Under `unix_hardened` every
//! stdout write carries a `process_semantics` mandate — "model broken-pipe/SIGPIPE
//! compatibility instead of assuming Rust default process semantics" — which until
//! 2026-09-14 had NO discharge route at all, so hello-world was INCONCLUSIVE with
//! "1 mandated" and no fix (a v7/D3 defect). The Unix-tool profiles now DECLARE the
//! policy themselves: `main` installs SIGPIPE -> SIG_DFL (as `-Zon-broken-pipe=kill`),
//! a write to a closed pipe terminates the process quietly, as C tools do, and the
//! mandate is met by construction — reported, visible, discharged. The `_print`
//! absent-callee row rides policy B as before.
fn main() {
    println!("hello");
}
