// LANE L9 — THE LOOP MARKER PLAN'S PROBE CORPUS.
//
// Every body here is a `loop { if COND { break; } BODY }` in the shape `plan_loop_markers`
// admits, or a NEAR MISS that must be refused. It is compiled with `-Ztrust-ir-lower=on` and read
// through the oracle; the built marker sequences quoted below were measured with
//   build/host/stage1/bin/rustc --crate-type=lib --edition 2021 \
//     -Zdump-mir=all -Zmir-include-spans=no -Ztrust-ir-lower=off
// on the 1.99.0-dev (94147b34f) fork driver and replayed through
// `reports/loop-block8-2026-08-19/walk.py`, which is `mir_differential::canon_markers`' own walk.
//
// ==========================================================================================
// WHY THIS ORIENTATION AND NOT `while`. Lane L8 established that a `while` body's BUILT MIR
// carries a `StorageDead` of the desugaring's `()` break local in a STATICALLY DEAD block, which
// `mir_differential.rs`'s unwalked-block sweep refuses on the BUILT side — before a derived line
// is read. That refusal is in a FROZEN file and no producer change can reach it.
//
// It is not a property of loops. Measured, all seven `loop { if c { break; } .. }` probes:
// `(no unwalked block carries a marker)`. The dead block is minted for the `while` desugaring's
// break-VALUE local; an explicit `loop` with a UNIT `break` has none. So for this orientation the
// built side does NOT err, and the only remaining wall is the derived side's — the shim's, in an
// unfrozen file, which is what `plan_loop_markers` removes.
//
// ==========================================================================================
// THE BUILT SEQUENCE FOR `l1`, VERBATIM (13 marker lines, 8 walked blocks of 11):
//
//   bb0.0:live _2    <- the LOOP's own `()` value          | region 1: across the back edge
//   bb2.0:live _4    <- the `if`-STATEMENT's `()` value    | region 2: one iteration
//   bb2.0:live _5    <- the condition's own temp           | region 2: one iteration
//   bb2.0:live _6    <- the condition's operand temp       | region 3: one expression
//   bb7.0:dead _6    <- ELSE arm entry
//   bb8.0:dead _5    <- the `if`-JOIN == the loop BODY == the LATCH
//   bb8.0:dead _4
//   bb8.0:live _8    <- the body statement's operand temp
//   bb8.2:dead _8
//   bb3.0:dead _6    <- BREAK arm entry
//   bb9.0:dead _5    <- the loop EXIT
//   bb9.0:dead _4
//   bb9.0:dead _2
//
// One rule generates all thirteen: storage spans are LIFO-nested by REGION, and every edge that
// LEAVES a region retires that region's live locals on it in reverse `StorageLive` order. A local
// live across the back edge is retired only on the loop-exit edge; a local live within one
// iteration is retired TWICE, once on each edge out of its region; a local live within one
// expression is retired at the entry of both arms.

#![allow(dead_code, unused_variables)]
#![allow(clippy::all)]

// ------------------------------------------------------- ADMITTED, AND EXPECTED TO BE EXACT ---
// `l1` / `l2` / `l6` / `m6`: the ONLY marked result is the condition, which is what the plan
// requires, so the derived sequence should equal built's line for line.

/// The canonical shape. 13 built marker lines.
#[inline(never)]
pub fn l1_loop_break_head(mut n: u32) -> u32 {
    loop {
        if n <= 3 {
            break;
        }
        n = n & 5;
    }
    n
}

/// The same, with the condition TRUE-on-break. Byte-identical built structure; 13 lines.
#[inline(never)]
pub fn l2_break_on_true(mut n: u32) -> u32 {
    loop {
        if n > 3 {
            break;
        }
        n = n & 5;
    }
    n
}

/// A labelled break. Built is byte-identical to `l1`; 13 lines.
#[inline(never)]
pub fn l6_labelled(mut n: u32) -> u32 {
    'outer: loop {
        if n <= 3 {
            break 'outer;
        }
        n = n & 5;
    }
    n
}

/// The EXIT block carries straight-line work of its own after the region deads: 15 lines, the
/// last two being `bb9.0:live _9` / `bb9.2:dead _9` AFTER `dead _5; dead _4; dead _2`.
#[inline(never)]
pub fn m6_exit_work(mut n: u32) -> u32 {
    loop {
        if n <= 3 {
            break;
        }
        n = n & 5;
    }
    n | 7
}

// ---------------------------------------------------------------------------- REFUSED ---------

/// REFUSED — and this is the clause that stands in for `source_form_admits` rule 2. Two successive
/// statements over the same variable (`a = a & 5; a = a | 3;`) lower to `%6 = and %2, %5;
/// %8 = or %6, %7`, which is the trust-ir of the single nested expression `a = (a & 5) | 3`
/// INSTRUCTION FOR INSTRUCTION. Built distinguishes them — two statements get one operand temp
/// each and no result temp, one expression gets a result temp for the inner `&` — and no plan
/// reading the instruction stream can. `needs` would therefore mark `%6`, exactly as lane K's
/// identical clause does for the acyclic class, and the derived sequence would not be built's.
/// `plan_loop_markers` requires `needs` to be the CONDITION AND NOTHING ELSE, which refuses it.
/// (18 built marker lines; the two-operand condition's second temp lands at assign 1, not 0.)
#[inline(never)]
pub fn m1_two_ops_two_stmts(mut a: u32, b: u32) -> u32 {
    loop {
        if a <= b {
            break;
        }
        a = a & 5;
        a = a | 3;
    }
    a
}

/// REFUSED — the same statement chain as `m1`, three statements deep, but the clause that fires
/// first is lane K's ORDERING RULE (1): `%7 = or %5, %6` is a marked result taking a marked
/// operand. 24 built marker lines. (`planwalk.py`, the offline replay of the plan's decision,
/// reports the acting clause for each refusal; it is not always the one you would guess.)
#[inline(never)]
pub fn m7_three_stmts(mut a: u32, b: u32) -> u32 {
    loop {
        if a <= b {
            break;
        }
        a = a & b;
        a = a | 3;
        a = a ^ b;
    }
    a
}

/// REFUSED — the `while` orientation. Its arms are the other way round (then = BODY, else = the
/// exit trampoline) and its built body carries `StorageDead(_8)` in a statically dead block, so
/// the ORACLE refuses it on the built side whatever this shim emits. `plan_loop_markers` refuses
/// it structurally: the then-arm is not a bare `Br` to the `Return` block.
#[inline(never)]
pub fn r1_while(mut n: u32) -> u32 {
    while n > 3 {
        n = n & 5;
    }
    n
}

/// REFUSED — the `if` is the loop body's TRAILING expression, so built mints NO `()` value local
/// for it (measured: 10 marker lines, no `_4`). The plan refuses it because the body block carries
/// no instruction of its own.
#[inline(never)]
pub fn r2_break_tail(mut n: u32) -> u32 {
    loop {
        n = n & 5;
        if n <= 3 {
            break;
        }
    }
    n
}

/// REFUSED — a nested condition `(n & m) <= 3`. Built opens the OUTER temp first and this shim's
/// linear SSA walk would open the inner one first, so ordering rule (1) refuses it — exactly as
/// it does for the acyclic class.
#[inline(never)]
pub fn r3_nested_cond(mut n: u32, m: u32) -> u32 {
    loop {
        if (n & m) <= 3 {
            break;
        }
        n = n & 5;
    }
    n
}

/// REFUSED — two `if`/`break`s make a 9-block producer body; the plan admits exactly six.
#[inline(never)]
pub fn r4_two_ifs(mut n: u32, m: u32) -> u32 {
    loop {
        if n <= 3 {
            break;
        }
        if n == m {
            break;
        }
        n = n & 5;
    }
    n
}

/// REFUSED — a source `let` in the loop body opens a lexical scope, and wave-MF's firewall
/// (`func.scopes.is_none()`) is consulted before anything else.
#[inline(never)]
pub fn r5_let_in_body(mut a: u32, b: u32) -> u32 {
    loop {
        if a <= b {
            break;
        }
        let t = a & b;
        a = t | 1;
    }
    a
}

/// REFUSED — `return` instead of `break`. The producer emits a SECOND `Return`, and the built body
/// carries a marker in a statically dead block again (measured: refused at bb10).
#[inline(never)]
pub fn r6_loop_return(mut n: u32) -> u32 {
    loop {
        if n <= 3 {
            return n;
        }
        n = n & 5;
    }
}

/// REFUSED — a shift. Under `-Coverflow-checks=on` (which is `clean-kernel`'s release profile) the
/// idiom carries an `Inst::Assert`, and the instruction-set clause refuses it first — measured.
/// With checks OFF it reaches the SHIFT clause, which exists because `shift_value_cast_pair` reads
/// its operands through `cx.operand`, not `mf_operand`, so a marked temp feeding one would never
/// be retired and the body would fail CLOSED at the `mf_live` check, LOSING an `agreed` verdict it
/// holds today.
#[inline(never)]
pub fn r7_shift(mut n: u32) -> u32 {
    loop {
        if n <= 3 {
            break;
        }
        n = n >> 1;
    }
    n
}
