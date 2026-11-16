//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Copt-level=0
//@ run-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! Policy B (owner ruling, 2026-07-25; docs/design/2026-07-25-completeness-gap-policy-ruling.md):
//! at a debug opt-level a `println!` of a RUNTIME value BUILDS AND RUNS under the
//! DEFAULT policy, exactly as a constant-argument `println!` already did.
//!
//! Twin of `println_default_run_pass.rs` (const string) and
//! `println_certify_rejects.rs`. This one isolates the RUNTIME-VALUE case fixed on
//! 2026-09-13: `format_args!` lowering wraps its call to the foundational-TCB
//! `core::fmt::Arguments::new` constructor in a COMPILER-GENERATED `unsafe` block,
//! which used to make `main`'s own HIR "use unsafe" and switch the
//! bundled-std-member tolerance off (only a runtime arg emits that packer; a const
//! arg folds to the safe `Arguments::from_str_nonconst`). The unsafe gate now
//! ignores that compiler-generated block, and a POSITIVE Display discriminator
//! keeps the tolerance to FOUNDATIONAL formatted types (`i32`, `str`, …); a USER
//! `Display` stays fatal — see `println_user_display_stays_closed.rs`.
//!
//! The only bundled obligation that cannot be discharged is still std's own
//! `ReentrantLock` accounting reached through `println!` — a foundational-TCB
//! completeness gap that policy B reports, not fails.
fn double(x: i32) -> i32 {
    x.wrapping_mul(2)
}
fn main() {
    let v = std::hint::black_box(21i32);
    println!("{}", double(v));
    println!("{}", v);
    println!("{} {}", v, v);
    let s = std::hint::black_box("hi");
    println!("{}", s);
}
