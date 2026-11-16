//@ needs-trust-verify
//@ edition: 2021
//@ revisions: tpr tpr_certify gt gt_certify swap mut_le mut_late rel_dec2 rel_twice two_dec dowhile signed_rel ge_twice ge_twice_certify stale stale_certify conv_stale conv_stale_certify param_cursor
//@ revisions: merge_if_lt merge_if_lt_certify merge_if_gt merge_if_gt_certify merge_break_lt merge_break_lt_certify merge_break_gt merge_break_gt_certify merge_inside merge_inside_certify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[tpr_certify] compile-flags: -Ztrust-policy=certify
//@[gt_certify] compile-flags: -Ztrust-policy=certify
//@[ge_twice_certify] compile-flags: -Ztrust-policy=certify
//@[stale_certify] compile-flags: -Ztrust-policy=certify
//@[conv_stale_certify] compile-flags: -Ztrust-policy=certify
//@[merge_if_lt_certify] compile-flags: -Ztrust-policy=certify
//@[merge_if_gt_certify] compile-flags: -Ztrust-policy=certify
//@[merge_break_lt_certify] compile-flags: -Ztrust-policy=certify
//@[merge_break_gt_certify] compile-flags: -Ztrust-policy=certify
//@[merge_inside_certify] compile-flags: -Ztrust-policy=certify
//@[tpr] check-pass
//@[tpr_certify] check-pass
//@[gt] check-pass
//@[gt_certify] check-pass
//@[swap] check-pass
//@[mut_le] check-fail
//@[mut_late] check-fail
//@[rel_dec2] check-fail
//@[rel_twice] check-fail
//@[two_dec] check-fail
//@[dowhile] check-fail
//@[signed_rel] check-fail
//@[ge_twice] check-fail
//@[ge_twice_certify] check-fail
//@[stale] check-fail
//@[stale_certify] check-fail
//@[conv_stale] check-fail
//@[conv_stale_certify] check-fail
//@[param_cursor] check-fail
//@[merge_if_lt] check-fail
//@[merge_if_lt_certify] check-fail
//@[merge_if_gt] check-fail
//@[merge_if_gt_certify] check-fail
//@[merge_break_lt] check-fail
//@[merge_break_lt_certify] check-fail
//@[merge_break_gt] check-fail
//@[merge_break_gt_certify] check-fail
//@[merge_inside] check-pass
//@[merge_inside_certify] check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! The loop-guard underflow certificate of a downward-cursor decrement
//! (TWO-POINTER-FALSE-REFUTE, 2026-10-06; `crates/trust-vcgen/src/generate/induction.rs`
//! `downward_guards` / `TrueEdgeReach::certifies`, and `loop_bounds.rs`
//! `build_converging_pointer_facts`).
//!
//! `build_downward_induction_facts` bounds a decrement result `hi - c < s.len()` only
//! when a loop guard proves the decrement cannot underflow. Since 7180f666c3 only a
//! CONSTANT guard (`while i > 0`) counted, so the correct in-place two-pointer reverse
//! (`while lo < hi { hi -= 1; .. s[hi] .. }`, `lo: usize`, which gives `hi >= 1`) was
//! refuted with a counterexample it cannot reach (`hi = 2 > s.len() = 1` at the loop
//! head). The relational guard `x < hi` / `hi > x` over an UNSIGNED `x` now certifies
//! `K = 0` (`hi >= 1`). Hunting its edges found three ways the existing certificate
//! was granted to a cursor value the guard never tested — each a live false proof,
//! closed here:
//!
//! * `ge_twice` (DOWNWARD-GUARD-SECOND-DEC-1) — a SECOND decrement inherited the
//!   guard's lower bound;
//! * `stale` (DOWNWARD-GUARD-STALE-1) — a boolean computed before the first decrement
//!   was read as a guard on the cursor;
//! * `conv_stale` (CONVERGING-GUARD-STALE-1) — the converging fact `lo < s.len()` was
//!   emitted of an `lo` incremented between the comparison and the switch;
//!
//! plus `param_cursor` (DOWNWARD-PARAM-CURSOR-1): a `mut` parameter cursor's entry
//! value was not counted, and its bounds row was proved.
//!
//! # BEFORE
//!
//! Measured 2026-10-06, and again 2026-10-09 with the same results, with
//! `scratchpad/stage1-w21before` (the stage 1 of 46e9afaf95, main + waves 18-19), each
//! revision's own flags plus `--cfg <rev> --emit=metadata`:
//!
//! | revision | rc | before |
//! |---|---|---|
//! | `tpr`, `tpr_certify` | 1, 1 | `two_pointer_reverse` 4 proved, 2 failed (`[bounds]`, `[slice]` on `s[hi]`); `zero_down_to` 1 proved, 1 failed (`[bounds]`) |
//! | `gt`, `gt_certify` | 1, 1 | 3 proved, 3 failed (`s[hi]` and both `s[lo]`) |
//! | `swap` | 1 | 2 proved, 1 failed (`[slice]`), 1 runtime-checked (`swap`'s panic-freedom) |
//! | `mut_le`, `mut_late`, `rel_dec2`, `rel_twice`, `two_dec`, `dowhile`, `signed_rel` | 1 each | refuted, with the `FAILED` row annotated below |
//! | `ge_twice`, `ge_twice_certify` | **0, 0** | 4 proved, 0 failed (3 kernel-certified) |
//! | `stale`, `stale_certify` | **0, 0** | 4 proved, 0 failed |
//! | `conv_stale`, `conv_stale_certify` | **0, 0** | 3 proved, 0 failed (3 kernel-certified) |
//! | `param_cursor` | 1 | 2 proved (the `s[i]` `[bounds]` row among them), 1 unknown (`[termination]`): only the strict-verification error, and no `[bounds] FAILED` |
//!
//! Runtime oracle (`-Ztrust-verify=off -Coverflow-checks=on`): `ge_twice(&mut [0, 0])`
//! and `stale(&mut [0, 0])` panic "attempt to subtract with overflow",
//! `conv_stale3(&mut [0])` "index out of bounds: the len is 1 but the index is 1",
//! `param_cursor(&mut [0; 4], 9, false)` "the len is 4 but the index is 8". The
//! correct functions never panic for every length 0..63 (and every `lo` for
//! `zero_down_to`). Built WITH verification, the false `ge_twice` / `stale` proofs
//! ELIDE the `i - 1` overflow check: see `two_pointer_relational_guard_run.rs`.
//!
//! # AFTER (predicted, not built)
//!
//! Derived from the unit tests in `crates/trust-vcgen/src/generate/downward_guard_tests.rs`,
//! which run the two builders on the MIR of these exact functions: the win revisions
//! gain `_8.0 < s.len()` (`_7.0` for `zero_down_to`; `tpr_gt` also gains its
//! converging `lo` facts) — the fact the `while lo < hi && hi > 0` twin already had
//! when it proved 6/6 on the same stage 1 — and each lie loses its false fact, so the
//! annotated row refutes. The twins' facts are unchanged except `rel_twice` (its
//! FIRST decrement gains a true bound; the second, the annotated one, does not) and
//! `mut_late` (its decrement gains a true bound; its failing rows read the loop-head
//! `hi`). `swap` is a default-policy revision only: certify still refuses its
//! runtime-checked `swap` panic-freedom row.
//!
//! AFTER-state twins, measured 2026-10-09 on the same stage 1 (default and certify):
//! each is a line-for-line copy rewritten so the BEFORE compiler already emits exactly
//! the facts the fix leaves. `param_cursor` with the cursor a LOCAL of two inits (`let
//! mut i = j; if c { i = s.len() }`, so no downward var): rc=1, `1 proved, 1 failed`,
//! `[bounds] FAILED`. `conv_stale3` with `hi = hi | 0` after its init (no downward
//! var, so no converging fact): rc=1, `2 proved, 1 failed`, `[bounds] FAILED`.
//! `two_pointer_reverse_swap` with a redundant `&& hi > 0`: default rc=0 (`3 proved,
//! 0 failed, 1 runtime-checked`), certify rc=1. The `tpr` twin is
//! `two_pointer_reverse_g` below (6/6 before).

// ------------------------------------------------------------------ WINS

#[cfg(any(tpr, tpr_certify))]
pub fn two_pointer_reverse(s: &mut [u8]) {
    //[tpr,tpr_certify]~^ NOTE Trust verification: 6 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 6 obligation(s)
    let mut lo = 0;
    let mut hi = s.len();
    while lo < hi {
        hi -= 1;
        let t = s[lo];
        s[lo] = s[hi];
        s[hi] = t;
        lo += 1;
    }
}

#[cfg(any(tpr, tpr_certify))]
pub fn zero_down_to(s: &mut [u8], lo: usize) {
    let mut hi = s.len();
    while lo < hi {
        hi -= 1;
        s[hi] = 0;
    }
}

// The control: a redundant constant guard. It proved 6/6 before and must still.
#[cfg(any(tpr, tpr_certify))]
pub fn two_pointer_reverse_g(s: &mut [u8]) {
    let mut lo = 0;
    let mut hi = s.len();
    while lo < hi && hi > 0 {
        hi -= 1;
        let t = s[lo];
        s[lo] = s[hi];
        s[hi] = t;
        lo += 1;
    }
}

#[cfg(any(gt, gt_certify))]
pub fn tpr_gt(s: &mut [u8]) {
    let mut lo = 0;
    let mut hi = s.len();
    while hi > lo {
        hi -= 1;
        let t = s[lo];
        s[lo] = s[hi];
        s[hi] = t;
        lo += 1;
    }
}

#[cfg(swap)]
pub fn two_pointer_reverse_swap(s: &mut [u8]) {
    let mut lo = 0;
    let mut hi = s.len();
    while lo < hi {
        hi -= 1;
        s.swap(lo, hi);
        lo += 1;
    }
}

// --------------------------------------------- TWINS (refuted before and after)

// `<=` is not a guard: at `lo == hi == 0` the decrement underflows.
#[cfg(mut_le)]
pub fn tpr_le(s: &mut [u8]) {
    //[mut_le]~^ ERROR Trust Level 0 safety verification incomplete
    //[mut_le]~^^ ERROR Trust strict verification failed
    //[mut_le]~^^^ NOTE [overflow:sub] FAILED
    let mut lo = 0;
    let mut hi = s.len();
    while lo <= hi {
        hi -= 1;
        let t = s[lo];
        s[lo] = s[hi];
        s[hi] = t;
        lo += 1;
    }
}

// The accesses run BEFORE the decrement: `s[hi]` at `hi == s.len()`.
#[cfg(mut_late)]
pub fn tpr_late(s: &mut [u8]) {
    //[mut_late]~^ ERROR Trust Level 0 safety verification incomplete
    //[mut_late]~^^ ERROR Trust strict verification failed
    //[mut_late]~^^^ NOTE [bounds] FAILED
    let mut lo = 0;
    let mut hi = s.len();
    while lo < hi {
        let t = s[lo];
        s[lo] = s[hi];
        s[hi] = t;
        hi -= 1;
        lo += 1;
    }
}

// Stride 2 under `lo < hi`: `hi >= 1` does not give `hi >= 2` (`lo = 0, hi = 1`).
#[cfg(rel_dec2)]
pub fn rel_dec2(s: &mut [u8], lo: usize) {
    //[rel_dec2]~^ ERROR Trust Level 0 safety verification incomplete
    //[rel_dec2]~^^ ERROR Trust strict verification failed
    //[rel_dec2]~^^^ NOTE [overflow:sub] FAILED
    let mut hi = s.len();
    while lo < hi {
        hi -= 2;
        s[hi] = 0;
    }
}

// Two decrements under one `lo < hi`: the second underflows at `hi == 1`.
#[cfg(rel_twice)]
pub fn rel_twice(s: &mut [u8], lo: usize) {
    //[rel_twice]~^ ERROR Trust Level 0 safety verification incomplete
    //[rel_twice]~^^ ERROR Trust strict verification failed
    //[rel_twice]~^^^ NOTE [overflow:sub] FAILED
    let mut hi = s.len();
    while lo < hi {
        hi -= 1;
        hi -= 1;
        s[hi] = 0;
    }
}

// Two decrements under one `i > 0`: the second underflows at `i == 1`.
#[cfg(two_dec)]
pub fn two_dec(a: &mut [u8]) {
    //[two_dec]~^ ERROR Trust Level 0 safety verification incomplete
    //[two_dec]~^^ ERROR Trust strict verification failed
    //[two_dec]~^^^ NOTE [overflow:sub] FAILED
    let mut i = a.len();
    while i > 0 {
        i -= 1;
        i -= 1;
        a[i] = 0;
    }
}

// The decrement runs before the first test: it underflows at `a.len() == 0`.
#[cfg(dowhile)]
pub fn dowhile(a: &mut [u8]) {
    //[dowhile]~^ ERROR Trust Level 0 safety verification incomplete
    //[dowhile]~^^ ERROR Trust strict verification failed
    //[dowhile]~^^^ NOTE [overflow:sub] FAILED
    let mut i = a.len();
    loop {
        i -= 1;
        a[i] = 0;
        if i > 0 {
            continue;
        } else {
            break;
        }
    }
}

// A SIGNED floor can be negative: `lo = -1` drives `hi` to -1, `a[usize::MAX]`.
#[cfg(signed_rel)]
pub fn signed_rel(a: &mut [u8; 8], lo: i64) {
    //[signed_rel]~^ ERROR Trust Level 0 safety verification incomplete
    //[signed_rel]~^^ ERROR Trust strict verification failed
    //[signed_rel]~^^^ NOTE [bounds] FAILED
    let mut hi: i64 = 8;
    while lo < hi {
        hi -= 1;
        a[hi as usize] = 0;
    }
}

// ------------------------------------------------ LIES (accepted before)

// DOWNWARD-GUARD-SECOND-DEC-1: at `a.len() == 2` the two decrements leave `i == 0`
// and `a[i - 1]` underflows; the second decrement inherited `i > 1`'s `_t.0 >= 1`.
#[cfg(any(ge_twice, ge_twice_certify))]
pub fn ge_twice(a: &mut [u8]) {
    //[ge_twice,ge_twice_certify]~^ ERROR Trust Level 0 safety verification incomplete
    //[ge_twice,ge_twice_certify]~^^ ERROR Trust strict verification failed
    //[ge_twice,ge_twice_certify]~^^^ NOTE [overflow:sub] FAILED
    let mut i = a.len();
    while i > 1 {
        i -= 1;
        i -= 1;
        a[i - 1] = 0;
    }
}

// DOWNWARD-GUARD-STALE-1: `c` tested `i` BEFORE the first decrement; at
// `a.len() == 2` the body sees `i == 1`, and `a[i - 1]` underflows after the second.
#[cfg(any(stale, stale_certify))]
pub fn stale(a: &mut [u8]) {
    //[stale,stale_certify]~^ ERROR Trust Level 0 safety verification incomplete
    //[stale,stale_certify]~^^ ERROR Trust strict verification failed
    //[stale,stale_certify]~^^^ NOTE [overflow:sub] FAILED
    let mut i = a.len();
    if i != 0 {
        let c = i > 1;
        i -= 1;
        if c {
            i -= 1;
            a[i - 1] = 0;
        }
    }
}

#[cfg(any(conv_stale, conv_stale_certify))]
#[inline(never)]
fn tick() {}

// CONVERGING-GUARD-STALE-1: `c` compared `lo` BEFORE `lo += 1`; the call puts the
// increment in a block of its own, before the switch. `conv_stale3(&mut [0])`
// indexes `s[1]`.
#[cfg(any(conv_stale, conv_stale_certify))]
pub fn conv_stale3(s: &mut [u8]) {
    //[conv_stale,conv_stale_certify]~^ ERROR Trust Level 0 safety verification incomplete
    //[conv_stale,conv_stale_certify]~^^ ERROR Trust strict verification failed
    //[conv_stale,conv_stale_certify]~^^^ NOTE [bounds] FAILED
    let mut lo = 0;
    let mut hi = s.len();
    loop {
        if lo > 1000 {
            break;
        }
        let c = lo < hi;
        lo += 1;
        tick();
        if c {
            hi -= 1;
            s[lo] = 0;
        } else {
            break;
        }
    }
}

// DOWNWARD-PARAM-CURSOR-1: with `c == false` the cursor keeps its caller value,
// which `s.len()` does not bound.
#[cfg(param_cursor)]
pub fn param_cursor(s: &mut [u8], mut i: usize, c: bool) {
    //[param_cursor]~^ ERROR Trust Level 0 safety verification incomplete
    //[param_cursor]~^^ ERROR Trust strict verification failed
    //[param_cursor]~^^^ NOTE [bounds] FAILED
    if c {
        i = s.len();
    }
    while i > 0 {
        i -= 1;
        s[i] = 0;
    }
}

// ------------------------------------- CONVERGING-MERGE-1 (2026-10-10, check-fail)
//
// `build_converging_pointer_facts` gave `lo < s.len()` to every block reachable from
// the guard's TRUE target, including a block the FALSE edge also reaches. Each
// function below indexes `s[lo]` at such a block. BEFORE, measured 2026-10-10 with
// each revision's flags plus `--cfg <rev> --emit=metadata` (the falsification gate's
// flags, `-Cpanic=abort`, give the same verdicts on both, and on integ7's stage 1 of
// `5ccf66a518` before this fix):
//
// | revision (default, `_certify`) | origin/main `32b6ef82d6` (`stage1-w21base`) | `d58bad8195` (`stage1-w21`, `integ/wave21`'s compiler) |
// |---|---|---|
// | `merge_if_lt` | **0, 0**: 3 proved, 0 failed, 2 kernel-certified (the false `s[lo]` row among them) | **0, 0**: 3/0, 3 kernel-certified |
// | `merge_if_gt` | 1, 1: `[bounds] FAILED` (`s[lo]`) | **0, 0**: 3/0, 3 kernel-certified |
// | `merge_break_lt` | 1, 1: `[slice] FAILED` (`s[hi]`) masked the false `s[lo]` row | **0, 0**: 4/0, 4 kernel-certified |
// | `merge_break_gt` | 1, 1: `[bounds]` (`s[lo]`) and `[slice]` (`s[hi]`) FAILED | **0, 0**: 4/0, 4 kernel-certified |
// | `merge_inside` | 0, 0: 3/0 | 0, 0: 3/0 |
//
// Runtime oracle (`-Ztrust-verify=off -Coverflow-checks=on`): `c3(&mut [0], 5)` and
// `c4(&mut [0], 5)` panic "index out of bounds: the len is 1 but the index is 5",
// `c1(&mut [7])` and `c2(&mut [7])` "the len is 1 but the index is 1", `c1(&mut [])`
// "the len is 0 but the index is 0". Built with verification (advisory) by the
// stage 1 of `d58bad8195` (`5ccf66a518`'s compiler sources), the binary panics the
// same way: the bounds check was kept, so the lie was the certified verdict, not an
// elided check. AFTER (the stage 1 of this fix, measured 2026-10-10, both policies and
// the gate's flags): the fact speaks only for blocks `TrueEdgeReach::certifies`
// admits, and each `s[lo]` row refutes — c1 and c2 exit 1 with `3 proved, 1 failed`,
// c3 and c4 with `2 proved, 1 failed`, each `[bounds] FAILED` on a reachable state
// (c1: `lo = 1, s.len() = 1`; c4: `lo = 0, s.len() = 0`); `inside` stays 3/0.

// The `if` merge; a false proof on origin/main.
#[cfg(any(merge_if_lt, merge_if_lt_certify))]
pub fn c3(s: &mut [u8], lo: usize) {
    //[merge_if_lt,merge_if_lt_certify]~^ ERROR Trust Level 0 safety verification incomplete
    //[merge_if_lt,merge_if_lt_certify]~^^ ERROR Trust strict verification failed
    //[merge_if_lt,merge_if_lt_certify]~^^^ NOTE [bounds] FAILED
    let mut hi = s.len();
    if lo < hi {
        hi -= 1;
        s[hi] = 0;
    }
    s[lo] = 1;
}

// The same, spelled `hi > lo` (the spelling TWO-POINTER-FALSE-REFUTE taught the
// converging builder to read).
#[cfg(any(merge_if_gt, merge_if_gt_certify))]
pub fn c4(s: &mut [u8], lo: usize) {
    //[merge_if_gt,merge_if_gt_certify]~^ ERROR Trust Level 0 safety verification incomplete
    //[merge_if_gt,merge_if_gt_certify]~^^ ERROR Trust strict verification failed
    //[merge_if_gt,merge_if_gt_certify]~^^^ NOTE [bounds] FAILED
    let mut hi = s.len();
    if hi > lo {
        hi -= 1;
        s[hi] = 0;
    }
    s[lo] = 1;
}

// The loop exit, which the `break` and the guard's false edge share.
#[cfg(any(merge_break_lt, merge_break_lt_certify))]
pub fn c1(s: &mut [u8]) {
    //[merge_break_lt,merge_break_lt_certify]~^ ERROR Trust Level 0 safety verification incomplete
    //[merge_break_lt,merge_break_lt_certify]~^^ ERROR Trust strict verification failed
    //[merge_break_lt,merge_break_lt_certify]~^^^ NOTE [bounds] FAILED
    let mut lo = 0;
    let mut hi = s.len();
    while lo < hi {
        hi -= 1;
        if s[hi] == 0 {
            break;
        }
        lo += 1;
    }
    s[lo] = 1;
}

#[cfg(any(merge_break_gt, merge_break_gt_certify))]
pub fn c2(s: &mut [u8]) {
    //[merge_break_gt,merge_break_gt_certify]~^ ERROR Trust Level 0 safety verification incomplete
    //[merge_break_gt,merge_break_gt_certify]~^^ ERROR Trust strict verification failed
    //[merge_break_gt,merge_break_gt_certify]~^^^ NOTE [bounds] FAILED
    let mut lo = 0;
    let mut hi = s.len();
    while hi > lo {
        hi -= 1;
        if s[hi] == 0 {
            break;
        }
        lo += 1;
    }
    s[lo] = 1;
}

// The control (check-pass): `s[lo]` inside the TRUE arm keeps its fact.
#[cfg(any(merge_inside, merge_inside_certify))]
pub fn inside(s: &mut [u8], lo: usize) {
    //[merge_inside,merge_inside_certify]~^ NOTE Trust verification: 3 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 3 obligation(s)
    let mut hi = s.len();
    if hi > lo {
        hi -= 1;
        s[hi] = 0;
        s[lo] = 1;
    }
}
