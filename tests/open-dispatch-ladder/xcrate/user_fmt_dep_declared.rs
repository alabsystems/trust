//@ trust-ladder-xcrate: verifies
//@ trust-ladder-xcrate-dep: libd
//@ trust-ladder-xcrate-declare: libd
//! D4-A (2026-09-24): `user_fmt_dep` with the dependency DECLARED
//! (`-Ztrust-bundle-foreign-crate=libd`). No verdict crosses rmeta; the impl is
//! RE-DERIVED here from its encoded MIR under this compilation's policy and
//! passes the same bar (and error transparency) a local impl does.
extern crate libd;
fn main() { println!("{:?}", libd::D); }
