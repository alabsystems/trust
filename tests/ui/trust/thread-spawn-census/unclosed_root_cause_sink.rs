//@ needs-asm-support
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ forbid-output:(via inline assembly) [pools unclosed
//@ forbid-output:Remedy for an open principal
//! SC-8 (c), docs/DECISION_QUEUE.md (2026-10-11): disclosure only, the SINK case. No
//! `dyn` principal is open here; an UNKNOWN sink (inline assembly with an instruction,
//! as in `comment_only_asm_runs_nothing.rs`) sets the engine's `unenumerated` flag and
//! with it leaves every pool unclosed. `barrier`'s own row ends at that sink and
//! carries no back-reference (pinned by `forbid-output`), and with no open
//! principal the note names no remedy; `plain`'s row is decided by the unclosed pools, so it
//! names the sink and the node that first met it.

#![allow(dead_code)]

use std::arch::asm;

pub fn barrier(mut x: u64) -> u64 {
    //~^ NOTE not a spawn claim) (via inline assembly)
    unsafe {
        asm!("/*{0}*/ nop", inout(reg) x)
    };
    x
}

pub fn plain(n: u32) -> String { format!("{n}") }
//~^ NOTE an indirect call whose pool is not closed) [pools unclosed because: UNKNOWN sink inline assembly @ barrier; see the crate's SC-8 root-cause note]

//~? NOTE spawn census root cause (SC-8): pools unclosed because: UNKNOWN sink inline assembly @ barrier. Every indirect call's pool stays open while any of these holds (SC-5 (b))
