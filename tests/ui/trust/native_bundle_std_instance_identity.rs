//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
//! Two DISTINCT instantiations of ONE generic std function in ONE crate must be
//! bundled as two DISTINCT bodies.
//!
//! This is the soundness property that lets std bodies be bundled at all. The
//! bridge resolves a call by the callee's RENDERED NAME, so if the foreign lane
//! keyed bundled bodies by bare `DefId` — the way the local lane does — a single
//! `core::cmp::max` entry would answer BOTH calls below, and whichever body was
//! registered last would discharge the other instantiation's obligation. That is
//! the mixed-case collision the R3 guard's probe T9 exists to prevent, and it is
//! exactly why the bundle assembler excludes std by crate name.
//!
//! The foreign lane is safe from it by construction: bundled bodies are named by
//! `exact_def_path_str_with_args`, so these two calls produce
//! `core::cmp::max::<i32>` and `core::cmp::max::<u8>` — two names, two bodies,
//! each proved against the code it actually reaches. `-Ztrust-dump=native-bundle`
//! shows one bundle per root, each carrying only its own instantiation.
//!
//! If a change ever made the two instantiations share a name,
//! `register_function_name`'s `insert_or_poison` REMOVES the colliding key
//! rather than letting one body answer for the other, so both calls fall back to
//! the fail-closed absent-callee arm and this test fails as a `check-pass`. The
//! failure mode is a lost proof, never a false one — and this fixture is what
//! notices.

pub fn probe_max_i32(a: i32, b: i32) -> i32 {
    std::cmp::max(a, b)
}

pub fn probe_max_u8(a: u8, b: u8) -> u8 {
    std::cmp::max(a, b)
}

pub fn probe_min_i32(a: i32, b: i32) -> i32 {
    std::cmp::min(a, b)
}

fn main() {}
