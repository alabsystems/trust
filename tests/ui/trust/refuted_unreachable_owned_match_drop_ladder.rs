//@ revisions: default certify
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify -Cpanic=abort
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! Class `v-refuted-unreachable` (2026-09-27 inventory), the RE-READ half: a by-value
//! `match` over a tuple whose payloads need drop glue — the shape of
//! `winnow::error::ErrMode::or` and of `fallible_iterator`'s `cmp` family.
//!
//! rustc re-reads each field's discriminant into fresh temps, the last switches each
//! covering only a SUBSET of tags with `otherwise -> Unreachable`:
//!
//! ```text
//! bb0: _3 = (_1, _2); _5 = discriminant(_3.0); switch _5 [0: bb9, 1: bb2, 2: bb1, _: bb5]
//! bb1: _6 = discriminant(_3.1); switch _6 [0: bb8, _: bb3]
//! bb3: _7 = discriminant(_3.0); switch _7 [2: bb7, _: bb4]
//! bb4: _8 = discriminant(_3.1); switch _8 [2: bb6, _: bb5]
//! bb5: unreachable
//! ```
//!
//! and, after the arms, a drop ladder that drops the payloads no arm moved out
//! (`drop(((_3.1 as Cut).0))`, `drop(_3.1)`). Those `Drop`s are partial writes of the
//! tuple, so the owned-aggregate tie of `build_discriminant_cse_facts` (arm (b)) refused
//! the WHOLE local, and the re-reads stayed untied: before (trust main `144f74baff`,
//! stage 1, both revisions)
//! `[unreach] FAILED (ay-in-process); counterexample: .. _5 = 1, _6 = 1, _7 = 0, _8 = 0 ..`
//! — `_3.0` read as tag 1 in bb0 and tag 0 in bb3 — a build error on correct Rust.
//!
//! Arm (c) licenses each read on its own: the tuple is never borrowed, so nothing but a
//! statement that names it can change it, and no path from an invalidating event (a
//! drop, a move out, a storage marker, entry) reaches bb0..bb4 without passing its one
//! construction. The re-reads are tied, the row proves, and under `certify` it is
//! kernel-certified (the guard is rendered through the tied read, so each path's
//! contradiction is syntactic). The second obligation of the body is the
//! `global-alloc-dealloc-panic-free` contract (P-GA-1), skipped as discharged vacuously,
//! so the report reads `1 proved, 0 failed, .. 1 skipped out of 2`.

pub enum Mode {
    Incomplete(u32),
    Backtrack(Vec<u8>),
    Cut(Vec<u8>),
}

pub fn or(a: Mode, b: Mode) -> Mode {
    //~^ NOTE Trust verification: 1 proved, 0 failed
    //~| NOTE of which 1 kernel-certified
    match (a, b) {
        (Mode::Backtrack(e), Mode::Backtrack(_)) => Mode::Backtrack(e),
        (Mode::Incomplete(n), _) | (_, Mode::Incomplete(n)) => Mode::Incomplete(n),
        (Mode::Cut(e), _) | (_, Mode::Cut(e)) => Mode::Cut(e),
    }
}
