//@ needs-trust-verify
//@ aux-build: policy_b_unverified_dep.rs
//@ compile-flags: -Ztrust-verify=on -Copt-level=0
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//~? RAW Trust
//! 2026-09-16: a LOCAL wrapper must not stop the foreign-reach walk. `W` is this
//! crate's type (its own impls are verified bodies), but it carries `dep::Bomb`,
//! whose `Drop` lives in a verify-off dependency — and `Vec::<W>::clear` runs that
//! drop INSIDE the sysroot callee, with no `Drop` terminator in this body for the
//! glue walk to see. The walk therefore descends through local types (and local
//! closures' captures) and only exempts their OWN code. The vanilla `Vec::<u8>::
//! push` representative in front is what would otherwise have tolerated it.
extern crate policy_b_unverified_dep as dep;
struct W(#[allow(dead_code)] dep::Bomb);
fn main() {
    let mut w: Vec<u8> = Vec::new();
    w.push(1);
    let mut v: Vec<W> = Vec::new();
    v.push(W(dep::Bomb(3)));
    v.clear();
}
