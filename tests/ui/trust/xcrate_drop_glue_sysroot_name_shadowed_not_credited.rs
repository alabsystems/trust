//@ needs-trust-verify
// `aux-crate`, not `aux-build`: the aux's crate name is `hashbrown`, so a bare
// `-L` search leaves `extern crate hashbrown` ambiguous against the sysroot's
// own `hashbrown` (E0464 "multiple candidates") before any Trust check runs.
//@ aux-crate: hashbrown=hashbrown.rs
//@ revisions: with_std_hashmap without_std_hashmap
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//@ check-fail
//! X1 adversarial review (2026-09-23) — A SYSROOT DESTRUCTOR'S CREDIT, INHERITED
//! BY A DEPENDENCY THAT SHARES THE SYSROOT CRATE'S NAME.
//!
//! BOTH REVISIONS MUST STAY REFUSED. Fix the compiler, never this file.
//!
//! # The defect
//!
//! The X1 fix admits a foreign destructor as drop-glue credit only when its
//! crate is in the sysroot. But the credit reaches the bridge as the ADT's
//! RENDERED PATH (`ADMITTED_DESTRUCTOR_ADTS` -> `bundled_destructor_adts`), and
//! that path spells the crate NAME. `drop(HashMap)` admits the sysroot's
//! `hashbrown::raw::RawTable`, so every other type in the same function that
//! renders `hashbrown::raw::RawTable` — here a verify-off dependency named
//! `hashbrown` (an ordinary crates.io name) — had its drop glue credited too,
//! and its panicking `Drop` was never charged.
//!
//! Measured on stage-1 `trustc` at `fa6661d85e`, as a binary, with the
//! dependency built WITHOUT MIR (so its own destructor is declined, which is what
//! the X1 rule makes of every dependency): with a `drop(HashMap)` beside it,
//! rc=0 and the program exited 101 ("boom"); without the `HashMap`
//! (`without_std_hashmap`), refused ("drop glue for `hashbrown::raw::RawTable`
//! has unproven panic-freedom").
//!
//! # The fix
//!
//! `foreign_destructor_admission.rs` credits a sysroot crate's destructor only
//! while no crate outside the sysroot (a dependency, or the local crate) shares
//! that crate's name. Here the dependency shadows `hashbrown`, so the sysroot
//! `RawTable` is not admitted either: `with_std_hashmap` is refused (on BOTH
//! drops — the `HashMap`'s credit is the cost of the namesake, fail-closed).
extern crate hashbrown;

#[cfg(with_std_hashmap)]
pub fn f(x: u32) -> u32 { //[with_std_hashmap]~ ERROR Trust strict verification failed
    let m: std::collections::HashMap<u8, u8> = std::collections::HashMap::new();
    drop(m);
    let g = hashbrown::raw::RawTable(x);
    let r = g.0;
    drop(g);
    r
}

#[cfg(without_std_hashmap)]
pub fn f(x: u32) -> u32 { //[without_std_hashmap]~ ERROR Trust strict verification failed
    let g = hashbrown::raw::RawTable(x);
    let r = g.0;
    drop(g);
    r
}
