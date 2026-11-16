//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Copt-level=0
//@ run-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! Policy B (owner ruling, 2026-07-25; docs/design/2026-07-25-completeness-gap-policy-ruling.md):
//! at a debug opt-level ordinary `println!` BUILDS AND RUNS under the DEFAULT policy.
//! `std::io::_print` is an absent callee whose only unproved obligation is a
//! panic-freedom row standing for std's own DEFINED write-failure / broken-pipe
//! `panic!` — a runtime-checked completeness gap with vanilla Rust semantics,
//! reported not failed. Green front door 7005b41c01 (2026-07-02); re-broken by
//! 42b923a273 (2026-08-09); restored here. `-Ztrust-policy=certify` twin:
//! `println_certify_rejects.rs`.
//!
//! SCOPE: pinned to `-Copt-level=0` deliberately, so this fixture isolates the
//! DEBUG-build behaviour the policy-B restoration delivers. The optimized lane has
//! its own pin, `println_release_opt_run_pass.rs`, and as of 2026-09-12 it passes
//! too — closing `-O` additionally required modelling the casts std's inlined
//! `format_args!` emits and narrowing the unsafe gate so inlined std stops counting
//! as the caller's own `unsafe`. Keep BOTH: they fail for different reasons and each
//! names its own mechanism.
fn main() {
    println!("hello from trust");
}
