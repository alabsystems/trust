//@ trust-ladder-xcrate: refuses
//@ trust-ladder-xcrate-dep: libd
//! GUARD RAIL, and the one that actually matters: the dependency's impl IS
//! provable where it lives, but the dependency is NOT DECLARED, so this
//! compilation re-derives nothing from it, and no verdict crosses rmeta —
//! `trust_proof_results` has no `separate_provide_extern`, and D4 (2026-09-23)
//! decided there will be no per-crate verdict bit either. This stays red
//! FOREVER as written; the declared twin is `user_fmt_dep_declared`.
extern crate libd;
fn main() { println!("{:?}", libd::D); }
