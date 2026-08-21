// LANE LR — LOOPS AND RECURSION, EACH BLOCKER ISOLATED FROM THE OTHERS.
//
// The two smallest populations in `clean_kernel`, and the two nothing had attacked directly. The
// crate's whole LOOP population is one body — `env::native_reducers_bool_ext::nat_gcd` — and its
// whole RECURSION population is seven, of which two (`level::Level::is_zero` / `is_nonzero`) are
// `derived_mir: agreed`. Every recorded blocker for those bodies is a CONJUNCTION of several
// refusals landing on one body at once, so "the loop is what refuses it" was never measured. This
// file separates them.
//
// Each body below removes exactly one thing from the corpus shape it is derived from, so the
// verdict delta between two neighbours names ONE clause. Nothing here is a new plan or a new
// admission: the file is a measurement instrument, and every body in it is expected to be refused
// today. What it pins is WHICH clause refuses, and — for group A — a distinction in BUILT that no
// probe had recorded.
//
// THE RESULT GROUP A EXISTS TO PIN (measured on rustc's own `mir_built` output, see the group's
// comment): the `while` desugaring emits a STATICALLY UNREACHABLE block holding a storage marker,
// and `mir_differential::canon_markers` fail-closes on exactly that. The `loop { if c { break } }`
// spelling does not emit it. That is a property of `rustc_mir_build`, not of the producer, so no
// shim-side or producer-side change can reach it — the distinction is recorded here so a later
// lane does not spend a driver build rediscovering it.
//
// No body name in this file appears in any other probe file.
//
// ============================================================================================
// MEASURED, whole file, both opt levels, one sealed driver at `6bb5fa64ef`
// (`-Ztrust-ir-lower=on -Ztrust-verify=off -Coverflow-checks=on`):
//
//   body                         derived_mir   markers_exact   flip -O3   flip -O0
//   a01_while_param_only         agreed        false           -          FLIP
//   a02_loop_break_param_only    unsupported   -               -          -
//   a03_while_param_rem          agreed        false           -          FLIP
//   a04_loop_break_param_rem     unsupported   -               -          -
//   b01_gcd_no_let               agreed        false           -          FLIP
//   b02_gcd_no_assert            agreed        false           -          FLIP
//   b03_gcd_neither              agreed        false           -          FLIP
//   b04_gcd_loop_break           unsupported   -               -          -
//   c01_self_if                  agreed        false           -          FLIP
//   c02_self_match               agreed        false           -          FLIP
//   c03_mutual_a / _b            agreed        false           -          FLIP
//   c04_self_via_closure         unsupported   -               -          -
//   c04_self_via_closure::{c#0}  agreed        false           -          FLIP
//   d01_loop_then_self           agreed        false           -          FLIP
//   d02_self_inside_loop         unsupported   -               -          -
//   e01_loop_match_break_const   unsupported   -               -          -
//   e02_loop_match_break_param   unsupported   -               -          -
//   e03_self_const_arg           agreed        TRUE            FLIP       FLIP
//   e04_self_no_arg              agreed        TRUE            FLIP       FLIP
//   e05_mutual_const_arg_a / _b  agreed        TRUE            FLIP       FLIP
//   e06_self_bool_const_arg      agreed        TRUE            FLIP       FLIP
//   e07_loop_and_self_const_arg  unsupported   -               -          -
//
// THREE THINGS THAT WERE NOT KNOWN BEFORE THIS FILE RAN:
//
//   1. RECURSION IS NOT A WALL. Five recursion-carrying bodies — including a genuine MUTUAL pair
//      (`e05_*`, one two-member call-graph SCC, both members) — reach `markers_exact` and FLIP at
//      `-O3`. Nothing about the self-call or the call-graph cycle is refused anywhere. What was
//      being measured as "the recursion wall" is the SHAPES the corpus's seven recursive bodies
//      happen to carry (whole-aggregate `Load`, `FatPtr(Slice)` params, a `&LevelArc` temp).
//
//   2. `nat_gcd`'S THIRD BLOCKER IS INDEPENDENT AND SUFFICIENT. `a01_while_param_only` carries a
//      `mut` parameter instead of a `let` and `&` instead of `%`, so neither the `func.scopes`
//      firewall nor the `Inst::Assert` clause applies — and it is still refused, at exactly
//      `marker channel(built): storage marker in unwalked block 7 (cleanup/dead code)`. Six
//      independent `while` bodies here (a01, a03, b01, b02, b03, d01) are refused at that one
//      line. Removing either of the other two blockers changes nothing.
//
//   3. THE LOOP LANE'S REACHABLE ROUTE IS IN THE PRODUCER, NOT THE ORACLE. `e01`/`e02` are
//      loop-carrying and MARKER-FREE in built — they would reach `markers_exact` trivially, the
//      way 1,058 of the 1,096 exact bodies already do. They never get there because the producer
//      fails closed on `break <value>` (`lib.rs`, `lower_break`), which every marker-free loop
//      spelling needs. That is a build item in a non-frozen file, not an oracle question.
// ============================================================================================

#![allow(clippy::eq_op, clippy::identity_op, dead_code, unused_variables)]
#![allow(clippy::let_and_return, clippy::needless_return, clippy::bool_comparison)]
#![allow(clippy::needless_range_loop, clippy::while_immutable_condition)]
#![allow(clippy::never_loop, clippy::mut_range_bound, clippy::only_used_in_recursion)]
#![allow(unconditional_recursion, clippy::match_single_binding, clippy::unit_arg)]

// --- A: THE LOOP, WITH THE `func.scopes` FIREWALL AND THE `Assert` REMOVED. -------------------
//
// `nat_gcd` is refused by `plan_branch_markers` three times over: `func.scopes.is_some()`
// (to_mir.rs, the wave-MF firewall — it carries `let t = b`), `operands_of` on `Inst::Assert` (the
// `%` div-by-zero guard), and the back-edge clause. These four bodies carry a `mut` PARAMETER
// instead of a `let` and a `&`/`>>` instead of a `%`, so the back edge is the only clause left.
//
// a01 vs a02 is the `while` / `loop`-`break` distinction described above; a03 vs a04 re-adds the
// `Assert` on each side of it.

#[inline(never)]
pub fn a01_while_param_only(mut n: u32) -> u32 {
    while n > 3 {
        n = n & 5;
    }
    n
}

#[inline(never)]
pub fn a02_loop_break_param_only(mut n: u32) -> u32 {
    loop {
        if n <= 3 {
            break n;
        }
        n = n & 5;
    }
}

#[inline(never)]
pub fn a03_while_param_rem(mut a: u64, b: u64) -> u64 {
    while a > b {
        a = a % b;
    }
    a
}

#[inline(never)]
pub fn a04_loop_break_param_rem(mut a: u64, b: u64) -> u64 {
    loop {
        if a <= b {
            break a;
        }
        a = a % b;
    }
}

// --- B: `nat_gcd` ITSELF, WITH ONE THING REMOVED AT A TIME. ------------------------------------
//
// b01 is `nat_gcd` verbatim minus the source `let` (the swap is spelled with `^=`, which mints no
// binding and no scope). b02 is `nat_gcd` minus the `Assert` (`&` for `%`). b03 is minus both.
// b04 keeps both but spells the loop as `loop`/`break`.

#[inline(never)]
pub fn b01_gcd_no_let(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        a = a % b;
        a ^= b;
        b ^= a;
        a ^= b;
    }
    a
}

#[inline(never)]
pub fn b02_gcd_no_assert(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let t = b;
        b = a & b;
        a = t;
    }
    a
}

#[inline(never)]
pub fn b03_gcd_neither(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        a = a & b;
        a ^= b;
        b ^= a;
        a ^= b;
    }
    a
}

#[inline(never)]
pub fn b04_gcd_loop_break(mut a: u64, mut b: u64) -> u64 {
    loop {
        if b == 0 {
            break a;
        }
        let t = b;
        b = a % b;
        a = t;
    }
}

// --- C: RECURSION, WITH NOTHING ELSE IN THE BODY. ---------------------------------------------
//
// Every one of the crate's seven recursion-carrying bodies also carries something the shim or the
// oracle refuses for a reason that has nothing to do with the self-call: a whole-aggregate `Load`,
// a `FatPtr(Slice)` parameter, an untracked reborrow, or a `&LevelArc` temp. These carry a scalar
// parameter and nothing else, so a refusal here is about the CALL and the CFG it forces.
//
// c01/c02 are the `if` and `match` spellings; c03 is a mutual pair (two SCC members rather than
// one self-edge); c04 is the sub-case a self-call makes reachable in principle — recursion through
// a BODYFUL CLOSURE, where the callee is a LOCAL body, so the cross-crate callee problem that
// defers most call-bearing bodies to the seam does not apply.

#[inline(never)]
pub fn c01_self_if(n: u32) -> u32 {
    if n == 0 { 0 } else { c01_self_if(n & 3) }
}

#[inline(never)]
pub fn c02_self_match(n: u32) -> u32 {
    match n {
        0 => 0,
        _ => c02_self_match(n & 3),
    }
}

#[inline(never)]
pub fn c03_mutual_a(n: u32) -> u32 {
    if n == 0 { 0 } else { c03_mutual_b(n & 3) }
}

#[inline(never)]
pub fn c03_mutual_b(n: u32) -> u32 {
    if n == 0 { 1 } else { c03_mutual_a(n & 3) }
}

#[inline(never)]
pub fn c04_self_via_closure(n: u32) -> u32 {
    if n == 0 { 0 } else { (|m: u32| c04_self_via_closure(m))(n & 3) }
}

// --- D: LOOP AND RECURSION IN ONE BODY. -------------------------------------------------------
//
// Neither population contains a body that carries both. These two say what happens when one does,
// so the two lanes' walls can be observed as independent rather than assumed to be.

#[inline(never)]
pub fn d01_loop_then_self(mut n: u32) -> u32 {
    while n > 8 {
        n = n & 7;
    }
    if n == 0 { 0 } else { d01_loop_then_self(n & 3) }
}

#[inline(never)]
pub fn d02_self_inside_loop(mut n: u32) -> u32 {
    loop {
        if n <= 1 {
            break n;
        }
        n = d02_self_inside_loop(n & 3);
    }
}

// --- E: THE MARKER-FREE SPELLINGS — the point of the file. ------------------------------------
//
// `markers_exact` is reached today by 1,096 `clean_kernel` bodies, and 1,058 of those reach it the
// TRIVIAL way: built emits no storage marker at all, the shim emits none, and the channel reports
// `0 marker line(s) identical`. Only 38 bodies reach it with a NON-EMPTY sequence, the largest
// being `expr::bvar_in_range` at 21 lines. So the reachable question for both of this file's
// populations is not "can a plan reproduce built's markers" but "is there a loop / recursion
// spelling for which built emits NONE".
//
// Measured on `mir_built` output before any of these were written (`while` vs `loop`, `if` vs
// `match`, temp-forced vs bare-place vs constant call argument):
//
//   * `while` ALWAYS emits `StorageLive(_k)` on a `()` statement-value local in the entry block,
//     and ALWAYS emits a statically unreachable block holding `StorageDead` of the loop's break
//     local — the shape `canon_markers` fail-closes on. Both are properties of the desugaring, so
//     every `while` body in the corpus is outside `markers_exact` no matter what the shim emits.
//   * `loop { match .. { .. => break v, .. => () } }` emits ZERO markers.
//   * a self-call whose argument needs an operand temp emits a live/dead pair for that temp; a
//     self-call with a CONSTANT argument, or with no argument, emits ZERO markers.
//
// e01/e02 are loop-carrying and marker-free. e03..e06 are recursion-carrying and marker-free,
// including a mutual pair. e07 is both. Their neighbours one token away are in groups A-D above,
// so the boundary is a diff and not an assertion.

#[inline(never)]
pub fn e01_loop_match_break_const(c: bool) -> u32 {
    loop {
        match c {
            true => break 1,
            false => (),
        }
    }
}

#[inline(never)]
pub fn e02_loop_match_break_param(n: u32) -> u32 {
    loop {
        match n {
            0 => (),
            _ => break n,
        }
    }
}

#[inline(never)]
pub fn e03_self_const_arg(n: u32) -> u32 {
    match n {
        0 => 0,
        _ => e03_self_const_arg(1),
    }
}

#[inline(never)]
pub fn e04_self_no_arg() -> u32 {
    e04_self_no_arg()
}

#[inline(never)]
pub fn e05_mutual_const_arg_a(n: u32) -> u32 {
    match n {
        0 => 0,
        _ => e05_mutual_const_arg_b(1),
    }
}

#[inline(never)]
pub fn e05_mutual_const_arg_b(n: u32) -> u32 {
    match n {
        0 => 1,
        _ => e05_mutual_const_arg_a(1),
    }
}

#[inline(never)]
pub fn e06_self_bool_const_arg(c: bool) -> u32 {
    match c {
        true => 0,
        false => e06_self_bool_const_arg(true),
    }
}

#[inline(never)]
pub fn e07_loop_and_self_const_arg(n: u32) -> u32 {
    loop {
        match n {
            0 => break e07_loop_and_self_const_arg(1),
            _ => (),
        }
    }
}
