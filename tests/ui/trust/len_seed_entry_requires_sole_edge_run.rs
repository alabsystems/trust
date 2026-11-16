//@ run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -Coverflow-checks=on
//@ error-pattern: attempt to subtract with overflow
//@ ignore-emscripten no processes
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! The run twin of `len_seed_entry_requires_sole_edge.rs` (LAST-SOME-ARM-SEED-1): the
//! program the `Some`-arm non-emptiness fact miscompiled. rustc -O0 spells `match
//! v.last() { Some(_) => {}, None => {} }` as `switchInt(d) -> [0: bbJ, 1: bbJ, ..]`, so
//! the `Some` target is the join `None` also enters, and `coll_len(v) >= 1` was seeded
//! there. Vanilla Rust panics at `v.len() - 1` for the empty `v` below.
//!
//! BEFORE: the `- 1` row was kernel-certified and its overflow check removed. Measured
//! 2026-10-12 on the stage 1 of `46e9afaf95` (`scratchpad/stage1-w25probe`): this
//! source built with these flags exits 0, and the binary prints
//! `18446744073709551615` and exits 0. Built without a policy flag (default) the
//! binary also returns `usize::MAX` (`std::process::exit(last_dup(&v) % 7)` exits 1).
//! Built `-Ztrust-verify=off`, it panics `attempt to subtract with overflow` (exit
//! 101).
//!
//! AFTER (predicted; not built in the lane): the fact is seeded only when the `Some`
//! edge is the arm's one entry, the row is not proved and the check stays, so the run
//! panics. The default policy refuses to BUILD a crate with an unproved row, so this
//! twin uses the advisory policy, which records the row and keeps the check.

#[inline(never)]
pub fn last_dup(v: &Vec<u8>) -> usize {
    match v.last() {
        Some(_) => {}
        None => {}
    }
    v.len() - 1
}

fn main() {
    let v: Vec<u8> = std::hint::black_box(Vec::new());
    println!("{}", last_dup(std::hint::black_box(&v)));
}
