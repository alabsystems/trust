//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
// wave-LB (wave-full-0901b coverage tier): `Break(outside loop)` — 21
// sole-tag bodies — was never a loop break at all. Every one of them is a
// LABELED BLOCK break (`'p: { .. break 'p v .. }`), the shape `pin!`
// expands to; only loops carried a break target, so the forward edge died
// with a tag naming the wrong construct. A labeled block is a loop that
// never loops, so the loop machinery applies with the back edge deleted:
// allocate an exit, push a BlockCtx, and have every `break 'p` plus the
// fall-through tail Br into it carrying the value.
//
// FENCES (each keeps a shape falling through to the pre-wave path with
// nothing emitted, so no existing verdict moves): a block nested inside a
// LOOP is refused outright (a break there could name either construct);
// and a block that ASSIGNS a local outliving it is refused, which is what
// keeps the exit's params exactly [result?] — a carried set would need the
// loop's pre-pass seeding, and a block has no header to bind pre-block
// versions in. `break 'p` is matched by NAME and only against the
// INNERMOST open block, so it can never steal a loop's unlabeled break.
#![allow(unused_labels)]

// The measured shape: a labeled block whose value comes from a break.
pub fn block_break_value(c: bool) -> i64 {
    'p: {
        if c {
            break 'p 7;
        }
        11
    }
}

// Both edges reach the exit: the break AND the fall-through tail.
pub fn block_two_edges(x: i64) -> i64 {
    'p: {
        if x > 0 {
            break 'p x;
        }
        -x
    }
}

// A UNIT labeled block that assigns no outer local: no result param, and
// the fall-through edge still joins.
pub fn block_unit(c: bool) -> i64 {
    'p: {
        if c {
            break 'p;
        }
    }
    5
}

// Negative control 1 (the assignment fence): this block assigns `n`,
// which outlives it, so the lane declines before emitting anything and
// the break keeps `Break(outside loop)` — the pre-wave verdict verbatim.
// The fence is what keeps the exit's params exactly [result?].
pub fn block_assigns_outer(c: bool) -> i64 {
    let mut n = 0;
    'p: {
        if c {
            break 'p;
        }
        n = 5;
    }
    n
}

// Negative control 2 (the loop fence): a labeled block INSIDE a loop is
// refused outright — a break there could name either construct — and the
// break then resolves against the LOOP lane, which reports
// `Break(non-innermost label)`.
pub fn block_in_loop(n: i64) -> i64 {
    let mut acc = 0;
    loop {
        'p: {
            if acc > n {
                break 'p;
            }
            acc += 1;
        }
        if acc > n {
            break;
        }
    }
    acc
}

fn main() {
    assert_eq!(block_break_value(true), 7);
    assert_eq!(block_break_value(false), 11);
    assert_eq!(block_two_edges(-3), 3);
    assert_eq!(block_unit(false), 5);
    assert_eq!(block_assigns_outer(false), 5);
    assert_eq!(block_in_loop(2), 3);
}
