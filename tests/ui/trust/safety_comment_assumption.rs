//@ revisions: above above_strict above_certify above_json let_stmt closure inner
//@ revisions: none separated non_safety modeled
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[above] compile-flags: -Ztrust-policy=advisory
//@[above_certify] compile-flags: -Ztrust-policy=certify
//@[above_json] compile-flags: -Ztrust-policy=advisory
//@[above_json] compile-flags: -Ztrust-verify-output=json --error-format=human
//@[let_stmt] compile-flags: -Ztrust-policy=advisory
//@[closure] compile-flags: -Ztrust-policy=advisory
//@[inner] compile-flags: -Ztrust-policy=advisory
//@[above] check-pass
//@[above_strict] check-pass
//@[above_json] check-pass
//@[let_stmt] check-pass
//@[closure] check-pass
//@[inner] check-pass
//@[above_certify] check-fail
//@[none] check-fail
//@[separated] check-fail
//@[non_safety] check-fail
//@[modeled] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[above_certify] dont-require-annotations: ERROR
//@[none] dont-require-annotations: ERROR
//@[separated] dont-require-annotations: ERROR
//@[non_safety] dont-require-annotations: ERROR
//@[modeled] dont-require-annotations: ERROR
//@[above] forbid-output: [hardened_unsafe_operation] FAILED
//@[above] forbid-output: [unsafe:unmodeled-call]
//@[above_strict] forbid-output: [hardened_unsafe_operation] FAILED
//@[above_certify] forbid-output: [hardened_unsafe_operation] FAILED
//@[above_json] forbid-output: [unsafe:unmodeled-call]
//@[above_json] forbid-output: missing SAFETY comment
//@[above_json] forbid-output: is ASSUMED sound
//@[let_stmt] forbid-output: [hardened_unsafe_operation] FAILED
//@[closure] forbid-output: [hardened_unsafe_operation] FAILED
//@[inner] forbid-output: [hardened_unsafe_operation] FAILED
//@[none] forbid-output: is ASSUMED sound
//@[separated] forbid-output: is ASSUMED sound
//@[non_safety] forbid-output: is ASSUMED sound
//@[modeled] forbid-output: is ASSUMED sound
//! SAFETY-ASSUME-1 (ruled 2026-10-17; docs/DECISION_QUEUE.md "SAFETY-ASSUME-1"): a
//! user `unsafe { }` block whose `// SAFETY:` comment sits where clippy's
//! `undocumented_unsafe_blocks` accepts one is a DECLARED ASSUMPTION. The rows
//! Trust mints for the unsafe operations it has no model of become ONE
//! `assumption:safety-comment` row per block. That row is skipped, never proved and
//! never refuted, and names the comment's position. Advisory warns, the default
//! lane passes CONDITIONALLY, and `certify` refuses. The seam is
//! `compiler/rustc_mir_transform/src/trust_verify/safety_comment_assumption.rs`.
//!
//! BEFORE: every revision below built with the call's
//! `[unsafe:unmodeled-call]` row FAILED, comment or not. aterm's release
//! (`targo trust build --allow-l0-gaps -p aterm`) therefore failed on
//! `crates/aterm/src/main.rs`'s `dispatch_link` closure, whose two-line
//! `// SAFETY:` comment sits directly above its `let … = unsafe { … }?;`.
//!
//! Revisions:
//! * `above`, `above_strict`, `above_certify`, `above_json`: a comment directly
//!   above a block that calls an `unsafe fn`. Assumed under advisory, CONDITIONAL
//!   on the default lane, the refusal under certify, and the skipped row on the
//!   JSON wire (no human warning, no unmodeled-call row).
//! * `let_stmt`: the comment sits above the `let` whose initializer holds the
//!   block on a later line (clippy's `accept-comment-above-statement`).
//! * `closure`: aterm's shape. The block sits in a closure, and its `?`
//!   desugaring is compiler code that declares nothing.
//! * `inner`: `unsafe { // SAFETY: …`.
//! * `none`, `separated`, `non_safety`: no comment; a comment separated from the
//!   block by a statement; a plain comment without the marker. Each keeps today's
//!   FAILED row and the build fails.
//! * `modeled`: a declared block whose operation Trust DOES model (the
//!   `get_unchecked` bounds obligation) keeps that real obligation. An unguarded
//!   index still fails, comment or not, and nothing is charged.
//!
//! No annotation line of an undeclared revision may contain the marker with its
//! colon. The scan reads a run of `//` lines upward from the block, and these
//! annotations are such lines.
//!
//! NOT YET MEASURED: written from the implementation's message text, and not
//! compiled or run when it landed (the change was code-only). The first stage-1 run
//! of this file is the measurement.
#![allow(dead_code)]

/// # Safety
/// None needed: an `unsafe fn` only so that calling it is an unsafe-signature call.
pub unsafe fn danger(x: u32) -> u32 {
    x
}

/// # Safety
/// None needed, as `danger`.
pub unsafe fn pair(x: u32) -> Option<(u32, u32)> {
    Some((x, x))
}

// (a) A comment directly above the block.
#[cfg(any(above, above_strict, above_certify, above_json))]
pub fn above(x: u32) -> u32 {
    //[above]~^ WARN is ASSUMED sound on its
    //[above_strict]~^^ WARN is ASSUMED sound on its
    //[above_certify]~^^^ ERROR is sound only by its
    // SAFETY: `danger` has no precondition.
    unsafe { danger(x) }
}

// (b) A comment above the `let` that holds the block on a later line.
#[cfg(let_stmt)]
pub fn let_stmt(x: u32) -> u32 {
    //[let_stmt]~^ WARN is ASSUMED sound on its
    // SAFETY: `danger` has no precondition.
    let y = 1u32
        .wrapping_add(unsafe { danger(x) });
    y
}

// aterm's `dispatch_link` shape: a closure, a two-line comment, a `?`.
#[cfg(closure)]
pub fn dispatch(x: u32) -> Option<u32> {
    let run = || -> Option<u32> {
        //[closure]~^ WARN is ASSUMED sound on its
        // SAFETY: this early route takes the lanes once, before any thread
        // exists; `pair` has no precondition.
        let (a, b) = unsafe { pair(x) }?;
        Some(a.wrapping_add(b))
    };
    run()
}

// A comment inside the block, right after its brace.
#[cfg(inner)]
pub fn inner(x: u32) -> u32 {
    //[inner]~^ WARN is ASSUMED sound on its
    unsafe { // SAFETY: `danger` has no precondition.
        danger(x)
    }
}

// (c) No comment: today's FAILED row.
#[cfg(none)]
pub fn none(x: u32) -> u32 {
    //[none]~^ ERROR safety verification incomplete
    //[none]~| NOTE [hardened_unsafe_operation] FAILED (structural-unsafe-demand-finding)
    unsafe { danger(x) }
}

// (d) A comment separated from the block by a statement.
#[cfg(separated)]
pub fn separated(x: u32) -> u32 {
    //[separated]~^ ERROR safety verification incomplete
    //[separated]~| NOTE [hardened_unsafe_operation] FAILED (structural-unsafe-demand-finding)
    // SAFETY: `danger` has no precondition.
    let y = x.wrapping_add(1);
    unsafe { danger(y) }
}

// (d) A plain comment: no marker.
#[cfg(non_safety)]
pub fn non_safety(x: u32) -> u32 {
    //[non_safety]~^ ERROR safety verification incomplete
    //[non_safety]~| NOTE [hardened_unsafe_operation] FAILED (structural-unsafe-demand-finding)
    // This is fine: `danger` has no precondition.
    unsafe { danger(x) }
}

// (e) A modeled operation in a declared block keeps its real obligation.
#[cfg(modeled)]
pub fn modeled(s: &[u8], i: usize) -> u8 {
    //[modeled]~^ ERROR Trust strict verification failed
    // SAFETY: (deliberately wrong: `i` is not proven `< s.len()`).
    unsafe { *s.get_unchecked(i) }
}

// The charge row on the JSON wire. ONE annotation: compiletest lets one output line
// satisfy at most one expected annotation, and the whole `function_result` record is
// a single line. The solver label is minted only on the `assumption:safety-comment`
// row (`safety_comment_row`, whose shape the seam's unit tests pin).
//[above_json]~? RAW "outcome":"skipped","solver":"trust-safety-comment","time_ms":0,"reason":"declared assumption
