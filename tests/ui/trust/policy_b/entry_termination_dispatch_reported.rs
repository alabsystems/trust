//@ needs-trust-verify
//@ aux-build: policy_b_unverified_dep.rs
//@ revisions: default certify
//@ compile-flags: -Ztrust-verify=on -Copt-level=0
//@[certify] compile-flags: -Ztrust-policy=certify
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[default] check-pass
//@[certify] check-fail
//! Refuted 2026-09-16 (fold-mask lens, resumed): `main`'s return VALUE is dispatched
//! by std — `lang_start` calls `<T as Termination>::report`, which runs the value's
//! `Debug` (on `Err`) and its `Drop` — through no terminator in any local body.
//! `fn main() -> Result<(), dep::Bomb>` built exit 0 with only the tolerated print
//! row ("can dispatch into no user code") and panicked in the verify-off
//! dependency's `Debug`, then its `Drop`.
//!
//! Policy B as ruled: the dispatch is a gap that keeps rustc's runtime check (a
//! panic there is a defined abort during error reporting), so the DEFAULT lane
//! publishes ONE honest runtime-checked row for it — its own row, never folded
//! under the print row — and the build succeeds; `certify` refuses it.
extern crate policy_b_unverified_dep as dep;

fn main() -> Result<(), dep::Bomb> {
    //[certify]~^ ERROR Trust certify verification failed
    let k = std::env::args().count() as u8;
    println!("{k}");
    if k == 3 { Err(dep::Bomb(k)) } else { Ok(()) }
}
