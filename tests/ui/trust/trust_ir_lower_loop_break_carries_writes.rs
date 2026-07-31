//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Trust (#183): a `break` carries the loop body's writes to the loop exit.
//!
//! The loop exit used to take NO block-params, and `lower_loop` re-bound each
//! carried local to its HEADER param after the loop — documented at the time as
//! "the exit reads carried locals at their header-param versions". A header
//! param holds the value at ITERATION ENTRY, not at the break point, so any
//! write the body made before breaking was silently dropped:
//!
//! ```text
//!   bb1(%1: i32):  condbr %0, bb3, bb4     ; header, z = %1
//!   bb2:           ret %1                  ; exit reads the HEADER param
//!   bb3:           %3 = const i32 1        ; z = 1
//!                  br bb2                  ; ...and drops it
//! ```
//!
//! `loop_assign(true)` returned 0 where Rust returns 1. Well-formed SSA, wrong
//! value — the same defect class as #182 (a join that merges control but not the
//! environment), here on the break edge rather than the short-circuit edge.
//!
//! The exit now takes the same param shape as the header and every `break`
//! passes its current values, exactly as the back-edge already did:
//!
//! ```text
//!   bb3:  %4 = const i32 1   br bb2(%4)    ; break carries z = 1
//!   bb4:  br bb2(%1)                       ; normal exit carries the header value
//!   bb2(%2: i32): ret %2                   ; reads the merged value
//! ```
//!
//! UNLIKE #182 THIS ONE WAS FENCED. The differential DID catch it — a lost write
//! changes a VALUE, and values are what the interpreter compares (`THIR returned
//! 0, MIR oracle returned 1`), so the body could never flip. That is exactly why
//! #182 was the more urgent of the two: a dominance violation changes no value,
//! so no differential can see it. Both are the same underlying mistake — a join
//! that merges control without merging the environment.
//!
//! Corpus-absent: the 2000-file ui_sample has zero real divergences, so this
//! shape was constructed rather than found, and fixing it moved no corpus
//! counter (clean/modelled/agreed/divergence all +0). A correctness fix, not a
//! number.

// The reproducer: the write before `break` must survive to the exit.
pub fn loop_assign(c: bool) -> i32 {
    let mut z = 0;
    while c {
        z = 1;
        break;
    }
    z
}

// The normal-exit edge must still carry the header value (the `break` path is
// not the only predecessor of the exit).
pub fn loop_noassign(c: bool) -> i32 {
    let mut z = 5;
    while c {
        break;
    }
    z
}

// No `break` at all — exit reached only by the condition failing.
pub fn loop_cond_exit(c: bool) -> i32 {
    let mut z = 0;
    while c {
        z = 2;
    }
    z
}

// Two carried locals, written in different orders, so the exit's param ORDER has
// to line up with the header's rather than merely having the right arity.
pub fn loop_two_carried(c: bool) -> i32 {
    let mut a = 1;
    let mut b = 2;
    while c {
        b = 20;
        a = 10;
        break;
    }
    a * 100 + b
}

// A write BEFORE a conditional break, so one exit edge carries the write and the
// other carries the header value.
pub fn loop_write_then_break(c: bool, d: bool) -> i32 {
    let mut z = 0;
    while c {
        z = 7;
        if d {
            break;
        }
    }
    z
}

fn main() {}
