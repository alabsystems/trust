//@ needs-trust-verify
//@ aux-build: policy_b_unverified_dep.rs
//@ compile-flags: -Ztrust-verify=on -Copt-level=0
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//~? RAW Trust
//! Refuted 2026-09-16: the same fold mask through DROP GLUE — `Vec<dep::Bomb>`
//! drops values whose `Drop::drop` lives in a verify-off dependency, co-folded
//! under the vanilla `Vec::<u8>::push` representative. Both halves catch it: the
//! `Drop` terminator's glue walk and the foreign type argument of
//! `Vec::<dep::Bomb>::push`.
extern crate policy_b_unverified_dep as dep;
fn main() {
    let mut w: Vec<u8> = Vec::new();
    w.push(1);
    let mut v: Vec<dep::Bomb> = Vec::new();
    v.push(dep::Bomb(3));
}
