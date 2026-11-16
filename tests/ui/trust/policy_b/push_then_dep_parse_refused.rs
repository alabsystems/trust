//@ needs-trust-verify
//@ aux-build: policy_b_unverified_dep.rs
//@ compile-flags: -Ztrust-verify=on -Copt-level=0
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//~? RAW Trust
//! Refuted 2026-09-16 (type-walk lens, the fold mask's missing half). The
//! representative here is `Vec::<u8>::push` — a VANILLA sysroot callee — and the
//! co-folded source is `str::parse::<dep::P>`, a SYSROOT callee whose type
//! argument reaches a `FromStr` in a verify-off dependency. The crate rule cannot
//! see it (the callee is core's); `callee_instantiation_reaches_foreign_user_code`
//! walks the instantiation and masks it. Measured before the fix: exit 0, panic
//! in the dependency; `"3".parse::<dep::P>(); w.push(1)` was refused.
extern crate policy_b_unverified_dep as dep;
fn main() {
    let mut w: Vec<u8> = Vec::new();
    w.push(1);
    let _r: Result<dep::P, ()> = "3".parse();
}
