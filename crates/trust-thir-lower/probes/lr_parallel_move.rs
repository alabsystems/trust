// LANE LOOP2 — THE PARALLEL-MOVE PROBE CORPUS (a `Br` edge is a phi row).
//
// Every body here exercises the emitter's lowering of `Br` edge arguments onto the target
// block's param locals. The measured defect this corpus pins: the pre-LOOP2 emitter assigned
// edge args SEQUENTIALLY in param order, so an argument that READS a target param the same edge
// had already WRITTEN got the new value — `r1_rot_let_and`'s back edge is
// `br header(%and, %b)` with `%b` the header's first param, and the old lowering emitted
// `p0 = BitAnd(..); p1 = copy p0;`, i.e. `a = a & b` instead of `a = t`. The oracle refused it
// (fail closed, no flip ever shipped):
//
//   built   `loop@b0 h0: seed=a1 back=h1`
//   derived `loop@b0 h0: seed=a1 back=bin(BitAnd,u64,h0,h1)`     <- the clobbered read
//
// Only a loop BACK EDGE can hazard: an acyclic edge's args cannot mention the target's own
// params (SSA dominance), and the pre-header/break-arm edges write locals disjoint from the ones
// they read. The repair (`parallel_move_snapshots` + the snapshot emission in the `Inst::Br`
// arm) reads all clobbered sources into fresh temps before the first destination write.
//
// EXPECTED VERDICTS with the repair, measured through the oracle at -O3:
//   r1_rot_let_and      agreed   (was: mismatch)   — the gcd rotation shape, BitAnd body
//   r2_rot_let_rem      agreed   (was: mismatch)   — Euclid's gcd itself (urem + div assert)
//   r3_rot_while        agreed   (was: agreed)     — the `while` spelling: latch params make the
//                                                    edge hazard-free; byte-identical emission
//   r4_no_hazard        agreed + markers_exact + FLIP (was: same) — the admitted loop-plan class
//                                                    must not move by a single statement
//
// The marker channel stays refused for r1/r2 (the rotation class has no marker plan yet — the
// scope firewall and the assert cluster stand); this corpus pins the SEMANTIC repair only.
#![allow(dead_code)]

// r1: the minimal rotation — the g8 shape. Two loop-carried values, a `let`-mediated swap.
pub fn r1_rot_let_and(mut a: u64, mut b: u64) -> u64 {
    loop {
        if b == 0 {
            break;
        }
        let t = b;
        b = a & b;
        a = t;
    }
    a
}

// r2: Euclid's gcd, loop-orientation — the clean-kernel `nat_gcd` body's rotation with the
// div-guard assert cluster in the loop body.
pub fn r2_rot_let_rem(mut a: u64, mut b: u64) -> u64 {
    loop {
        if b == 0 {
            break;
        }
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

// r3: the `while` spelling of r1. Its back edge routes through a latch block whose OWN params
// feed the header, so no edge reads a place it writes — the schedule is empty and emission is
// byte-identical to pre-LOOP2. (Its markers stay refused on the BUILT side: the `while`
// desugaring's dead break-value block, lane L8.)
pub fn r3_rot_while(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let t = b;
        b = a & b;
        a = t;
    }
    a
}

// r4: the loop-plan admitted class (single carried value, no hazard) — the regression control.
// This body is `markers_exact` and FLIPS at -O3 today; the repair must not move it.
pub fn r4_no_hazard(mut a: u64, b: u64) -> u64 {
    loop {
        if a == 0 {
            break;
        }
        a = a & b;
    }
    a
}
