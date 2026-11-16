//@ needs-trust-verify
//@ revisions: notes quiet
//@ compile-flags: -Ztrust-verify=on
//@[notes] compile-flags: -Ztrust-memory-notes
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@[quiet] forbid-output: trust: memory
//! The verifier's retained-memory notes are OPT-IN, and the per-body artifact
//! compaction they report on really runs.
//!
//! * `quiet` (no flag): not one `trust: memory` note. Both notes read the HOST's
//!   resident size, so on by default they made a compile's diagnostics depend on
//!   the machine (main's 5aa81ac168 measured
//!   tests/ui/borrowck/ever-init-many-locals.rs at 4858 MB max RSS, past the
//!   4 GiB checkpoint). The stderr is not snapshotted for the same reason: the
//!   census's GiB figures are the host's, only its counts are pinned.
//! * `notes` (`-Ztrust-memory-notes`): the census PINS `CompactArtifactsAfterPass`
//!   in `run_pass`. Each body the verify pass consumed has its slot compacted
//!   (the count reads 0 if the guard is deleted), while the pass still holds its
//!   own handle (the parenthesised count turns non-zero if the guard is declared
//!   before the `artifacts` binding), and no later pass had to recompute one.
//!   T3 L4 (C07): each compacted slot's VC context is released once its pass returns,
//!   because the compact projection holds none; the census counts them.
//!   T3 L4 (C07r, L4-E9-1): the only other holder is a pending import citation, which this
//!   crate has none of, so no context was held for one.
//!   T3 L4 (C09w): the counts are the coverage row's `memory` summary
//!   (`trust-memory-summary/v1`), printed from the same values; the pin holds
//!   `context_alive_after_compaction=0` and `compacted_rehits=0` under their wire names.

pub fn add_one(x: u32) -> u32 {
    x.wrapping_add(1)
}

pub fn pick(flag: bool, a: u8, b: u8) -> u8 {
    if flag { a } else { b }
}

fn main() {
    let _ = add_one(1);
    let _ = pick(true, 1, 2);
}

//[notes]~? NOTE trust: memory census: 3 artifact slots compacted after their verify pass (0 after the pass had dropped its own handle), 0 compacted slots recomputed by a later pass (compacted_rehits=0), 3 compacted contexts released (context_alive_after_compaction=0), 0 contexts held for a pending citation (contexts_held_for_citation=0, at most 0 at once)
