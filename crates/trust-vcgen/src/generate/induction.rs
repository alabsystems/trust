// Downward induction variables and countdown loops: a local that strictly
// decreases toward a constant floor under a dominating guard. Recovering the
// trip count is what bounds the accumulated value in the loop's arithmetic
// obligations.

use super::*;

/// Locals that are DOWNWARD induction variables: initialized EXACTLY ONCE to a
/// stable parameter slice length `B` and updated ONLY by self-decrements
/// (`i = CheckedSub(i, c).0`, `c >= 1`). Such `i` satisfies the loop invariant
/// `i <= B`. See [`build_downward_induction_facts`] for the soundness argument.
pub(super) fn downward_induction_vars(func: &VerifiableFunction) -> Vec<DownwardVar> {
    const FUEL: u32 = 16;
    let mut out = Vec::new();
    for cand in 0..func.body.locals.len() {
        let mut inits: Vec<Formula> = Vec::new();
        let mut decrements: Vec<(usize, i128)> = Vec::new();
        let mut disqualified = false;

        for block in &func.body.blocks {
            for stmt in &block.stmts {
                let Statement::Assign { place, rvalue, .. } = stmt else { continue };
                if place.local != cand {
                    continue;
                }
                if !place.projections.is_empty() {
                    disqualified = true;
                    break;
                }
                if let Rvalue::Use(Operand::Copy(p) | Operand::Move(p)) = rvalue
                    && matches!(p.projections.as_slice(), [trust_types::Projection::Field(0)])
                    && let Some(c) = checked_self_decrement_const(func, cand, p.local)
                {
                    decrements.push((p.local, c));
                    continue;
                }
                if let Some(b) = init_rvalue_stable_len(func, rvalue, FUEL) {
                    inits.push(b);
                    continue;
                }
                disqualified = true;
                break;
            }
            if let Terminator::Call { dest, .. } = &block.terminator
                && dest.local == cand
            {
                disqualified = true;
            }
            if disqualified {
                break;
            }
        }

        // Trust (countdown-loop piece, P0 root-cause fix): a mut-borrow /
        // raw-address of the candidate is a write channel the def scan above
        // cannot see — a callee receiving `&mut i` reseats `i` arbitrarily,
        // voiding the downward invariant. Fail closed (see `local_mut_escapes`).
        if disqualified || decrements.is_empty() || local_mut_escapes(func, cand) {
            continue;
        }
        // Trust (countdown-loop piece): multi-init support. A SINGLE init keeps
        // its exact bound (constant or stable symbolic length). MULTIPLE inits
        // qualify only when ALL are integer constants — every init then sets
        // `i <= max(inits)` and self-decrements only shrink, so `i <= max` is an
        // invariant (`u128::fmt`'s offset has inits {39, 23, 7}). Mixed or
        // symbolic multi-inits stay disqualified (two different `len()` symbols
        // admit no single sound bound).
        let (bound, single_const_init) = match inits.as_slice() {
            [] => continue,
            [one] => {
                let const_init = match one {
                    Formula::Int(n) => Some(*n),
                    _ => None,
                };
                (one.clone(), const_init)
            }
            many => {
                let mut max: Option<i128> = None;
                for f in many {
                    let Formula::Int(n) = f else {
                        max = None;
                        break;
                    };
                    max = Some(max.map_or(*n, |m: i128| m.max(*n)));
                }
                match max {
                    Some(m) => (Formula::Int(m), None),
                    None => continue,
                }
            }
        };
        out.push(DownwardVar { local: cand, bound, decrements, single_const_init });
    }
    out
}

/// The constant `K` of a loop guard `j > K` for the downward var `local` — a
/// `SwitchInt` on `_g = Gt(j, K)` or `_g = Lt(K, j)` whose TRUE edge enters the
/// loop body. Returns `K` and the guard's true-target block. With the guard the
/// decrement result `j - c >= (K + 1) - c`, discharging a SECONDARY index
/// subtraction like `s[j - 1]` (needs `j >= 1`, i.e. `K = 1`).
pub(super) fn downward_guard_lower_k(
    func: &VerifiableFunction,
    local: usize,
) -> Option<(i128, usize, BlockId)> {
    const FUEL: u32 = 16;
    for block in &func.body.blocks {
        let Terminator::SwitchInt { discr, targets, otherwise, .. } = &block.terminator else {
            continue;
        };
        let Some(g) = operand_root_local(func, discr, FUEL) else { continue };
        let (op, a, b) = match crate::unique_whole_local_def(func, g) {
            Some(Rvalue::BinaryOp(
                op @ (trust_types::BinOp::Gt | trust_types::BinOp::Lt),
                a,
                b,
            )) => (op, a, b),
            _ => continue,
        };
        // `Gt(j, K)` → (j is `a`, K is `b`); `Lt(K, j)` → (K is `a`, j is `b`).
        let (j_op, k_op) = match op {
            trust_types::BinOp::Gt => (a, b),
            _ => (b, a),
        };
        if operand_root_local(func, j_op, FUEL) != Some(local) {
            continue;
        }
        let k = match k_op {
            Operand::Constant(trust_types::ConstValue::Int(v)) => *v,
            Operand::Constant(trust_types::ConstValue::Uint(v, _)) => i128::try_from(*v).ok()?,
            _ => continue,
        };
        if let Some(t) = bool_switch_true_target(targets, *otherwise) {
            return Some((k, block.id.0, t));
        }
    }
    None
}

/// The block whose statements assign `_t = CheckedBinaryOp(Sub, …)` (a decrement
/// of the downward var). Used to verify the decrement is guard-dominated.
pub(super) fn checked_sub_block(func: &VerifiableFunction, t: usize) -> Option<usize> {
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign {
                place,
                rvalue: Rvalue::CheckedBinaryOp(trust_types::BinOp::Sub, ..),
                ..
            } = stmt
                && place.local == t
                && place.projections.is_empty()
            {
                return Some(block.id.0);
            }
        }
    }
    None
}

pub(super) fn build_downward_induction_facts(func: &VerifiableFunction) -> Vec<Formula> {
    // Trust (sr_countdown/wrong_divisor false-accept fix): the UPPER bound
    // `result <= B - c` emitted below is SOUND only when the decrement provably
    // does NOT underflow. If the loop can drive the cursor below `c` (so
    // `offset - c` wraps to ~2^W as an unsigned index), the bound is FALSE for the
    // wrapped result and, conjoined onto the `buf[result]` bounds VC, EXCLUDES the
    // real out-of-bounds write — a false PROVE (`countdown_wrong_divisor` verified
    // `2 proved,0 failed` while it OOB-writes for large `n`). Two independent
    // certificates of underflow-freedom are accepted: (a) a dominating cursor
    // guard `offset > k` with `k + 1 >= c` (the general reverse loop
    // `while i > 0 { i -= 1; a[i] }`), or (b) the countdown trip analysis
    // lower-bounding this exact result by a NON-NEGATIVE `LEN - c*T` (the itoa
    // family, whose guard is on the companion, not the cursor). The trip analysis
    // emits that `Ge` ONLY when `loop_lower >= 0`, so its presence for this result
    // IS the underflow-free certificate. `wrong_divisor` has neither (its guard is
    // on `remain`; `LEN - c*T < 0`), so it gets no upper bound and its bounds VC
    // correctly refutes; the itoa PROVED family keeps the bound and still proves.
    let underflow_free: FxHashSet<String> = countdown_trip_analysis(func)
        .global
        .iter()
        .filter_map(|f| match f {
            Formula::Ge(lhs, rhs) if matches!(rhs.as_ref(), Formula::Int(k) if *k >= 0) => {
                match lhs.as_ref() {
                    Formula::Var(name, _) => Some(name.clone()),
                    _ => None,
                }
            }
            _ => None,
        })
        .collect();
    let mut facts = Vec::new();
    for dv in downward_induction_vars(func) {
        // A `j > K` loop guard gives the decrement result `j - c >= (K + 1) - c`
        // (sound only where the decrement is GUARD-DOMINATED), which discharges a
        // SECONDARY index subtraction like `s[j - 1]` (needs `_t.0 >= 1`, i.e. K=1).
        let guard = downward_guard_lower_k(func, dv.local);
        let dominated = guard.map(|(_, gblock, ttarget)| {
            let mut avoid = FxHashSet::default();
            avoid.insert(gblock);
            let from_true = reachable_avoiding(func, ttarget.0, &avoid);
            // Blocks reachable from the guard's OTHER successors (the `j <= K` edges).
            let mut from_other: FxHashSet<usize> = FxHashSet::default();
            if let Terminator::SwitchInt { targets, otherwise, .. } =
                &func.body.blocks[gblock].terminator
            {
                for succ in targets.iter().map(|(_, t)| *t).chain(std::iter::once(*otherwise)) {
                    if succ != ttarget {
                        from_other.extend(reachable_avoiding(func, succ.0, &avoid));
                    }
                }
            }
            (from_true, from_other)
        });

        for (t, c) in dv.decrements {
            let result_place =
                Place { local: t, projections: vec![trust_types::Projection::Field(0)] };
            let result_name = crate::place_to_var_name(func, &result_place);
            let result_var = Formula::Var(result_name.clone(), Sort::Int);
            // Underflow-free certificate for THIS decrement (see the function
            // header): (a) a dominating cursor guard `offset > k` with `k + 1 >= c`
            // (offset >= k+1 >= c at the CheckedSub, so `offset - c` never wraps),
            // OR (b) the trip analysis's non-negative lower bound on this result.
            let guard_protects =
                if let (Some((k, _, _)), Some((from_true, from_other))) = (guard, &dominated) {
                    k + 1 >= c
                        && checked_sub_block(func, t)
                            .is_some_and(|cs| from_true.contains(&cs) && !from_other.contains(&cs))
                } else {
                    false
                };
            let underflow_free_here = guard_protects || underflow_free.contains(&result_name);
            // Trust (countdown-loop piece, B1): STRENGTHENED from `result < B` to
            // `result <= B - c` for a CONSTANT bound — equally a theorem of the
            // downward invariant (`i <= B` and `result = i - c` give
            // `result <= B - c`), and one unit is exactly what the countdown write
            // pattern needs: after `offset -= 4`, the accesses `buf[offset + 1..3]`
            // require `result + 3 < B`, i.e. `result <= B - 4`.
            //
            // SOUNDNESS (fuzzer-caught FALSE PROOF, sr_countdown[u16;N=3;short]):
            // a NEGATIVE constant bound is a math-int-only claim — the VC lane also
            // conjoins the RUST type range `0 <= result` onto overflow VCs, and
            // `result <= -1 AND result >= 0` is UNSAT: every premise set containing
            // both is vacuously "proved", including the decrement's own underflow
            // row (u16 buffer 3, stride 4 was PROVED yet panics at u16::MAX). When
            // `B - c < 0`, emit NOTHING (the loop body underflows on entry; fail
            // closed). A SYMBOLIC bound keeps the original `Lt(result, B)` shape:
            // `B - c` could be negative at runtime (`s.len() < c`), which would
            // smuggle the same inconsistency in as a phantom `len >= c` premise —
            // `Lt(result, B)`'s worst case (`len >= 1`) is exactly the
            // pre-strengthening behavior.
            match &dv.bound {
                Formula::Int(n) => {
                    let bound = n - c;
                    if bound >= 0 && underflow_free_here {
                        facts.push(Formula::Le(
                            Box::new(result_var.clone()),
                            Box::new(Formula::Int(bound)),
                        ));
                    }
                }
                b => {
                    if underflow_free_here {
                        facts.push(Formula::Lt(Box::new(result_var.clone()), Box::new(b.clone())));
                    }
                }
            }
            // Lower bound, only when the decrement block is reachable ONLY via the
            // guard's `j > K` edge (so `j > K` holds at the CheckedSub) and the
            // bound `(K+1)-c` is non-trivial (`> 0`; for unsigned, `>= 0` is free).
            if let (Some((k, _, _)), Some((from_true, from_other))) = (guard, &dominated)
                && let Some(cs_block) = checked_sub_block(func, t)
                && from_true.contains(&cs_block)
                && !from_other.contains(&cs_block)
            {
                let lower = k + 1 - c;
                if lower >= 1 {
                    facts.push(Formula::Ge(Box::new(result_var), Box::new(Formula::Int(lower))));
                }
            }
        }
    }
    facts
}

// ======================================================================
// Trust (countdown-loop piece): bounded-countdown-loop trip facts — the itoa
// `Unsigned::fmt` family.
//
//   let mut offset = buf.len();            // downward var, single CONST init LEN
//   let mut remain = n;                    // companion x: unsigned, defs = init + x/=D
//   while remain > C { offset -= c; ...; remain /= D; ... buf[offset + k] ... }
//   if remain > 9 { offset -= 2; ... }     // post-loop sites: per-path K(v) coupling
//
// THE THEOREM (division-countdown trip bound). Let x be UNSIGNED of width N, so
// x <= M := 2^N - 1 ALWAYS — the TYPE bound, never lattice information (the
// i128-TOP rule: an abstract value at TOP is "unknown", the type max is a
// theorem). If (a) the loop-site decrement of the cursor is dominated by a
// guard `x > C` (const C >= 0) and shares no guard-free cycle, and (b) every
// guard-true -> guard path executes `x /= D_j` (const D_j >= 2, D := min), and
// (c) x's defs are one init + const self-divisions (+ defs that cannot reach
// the guard), then before the k-th decrement at least k-1 divisions have run,
// so the k-th guard-true passage sees x <= floor(M / D^(k-1)); `x > C` forces
// floor(M / D^(k-1)) > C. Hence the decrement executes at most
//   T := |{ j >= 0 : floor(M / D^j) > C }|
// times — computed by DIRECT SIMULATION (terminates: D >= 2 forces <= N + 1
// steps; D < 2 is rejected BEFORE simulating, which is also the soundness gate:
// D = 1 never shrinks x). The cursor is MONOTONE (init once to LEN, only
// self-decrements), so every loop-site decrement RESULT satisfies
//   _t.0 >= LEN - c * T                                   (emitted iff >= 0)
// EXACTLY TIGHT: u64 / D=10^4 / C=999 gives T = 5 and LEN = 20 consumes the
// buffer to exactly offset 0 — a T = 4 derivation would false-prove a 16-byte
// buffer, and a 19-byte buffer must (and does) get NO fact. T == 0 (u8: M=255
// <= C=999) emits NOTHING — "vacuously true because unreachable" is not this
// builder's theorem to assert.
//
// POST-LOOP sites (`offset -= 2` after exit): per acyclic exit path,
//   K(v) := max{ k : floor(M / (D^k * R)) >= v }
// bounds the loop-site decrement count whenever a path guard establishes
// `x >= v` (v >= 1) at a point where x's value is still init+division-pure —
// R is the product of the path's own off-cycle division constants executed
// BEFORE the guard read (a reseat `remain /= 100` between exit and the guard
// TIGHTENS the exit bound; an opaque reseat, e.g. through a call payload,
// makes later guards UNUSABLE, never wrong). Each path also always carries the
// T-candidate (n_loop <= T unconditionally), and an `Eq(param, k0)`-true edge
// with `x`'s init = that UNWRITTEN param and k0 <= C is the ZERO-TRIP
// candidate (x0 = k0 <= C means the loop body never ran). The site fact is
//   _t_s.0 >= min over paths of max over that path's candidates    (iff >= 0)
// with S_path (the other off-cycle decrements on the path) subtracted; an
// UNSATISFIABLE path guard (v > floor(M / R)) marks the path infeasible (it
// never executes; it contributes no minimum). All facts are conjunction-free
// linear inequalities over Int keyed to the FRESH per-decrement result temps
// (`_t.0`), riding the same versioned-SSA staleness discipline as the
// downward-induction facts; `&mut`/`&raw` escapes of cursor or companion
// disqualify everything (`local_mut_escapes`).
// ======================================================================
/// `T` (max loop-site decrements) and `K(v)` share one simulation:
/// `countdown_k_max(m, d, r, v)` = `max{ k >= 0 : floor(m / (d^k * r)) >= v }`,
/// or `None` when even `k = 0` fails (an infeasible `x >= v` guard). Nested
/// floor-division composes exactly: `floor(floor(m/r)/d) = floor(m/(r*d))`.
/// CALLER CONTRACT: `d >= 2`, `v >= 1`, `r >= 1` (checked by every caller; the
/// loop then strictly shrinks and terminates in <= 128 steps).
pub(super) fn countdown_k_max(m: u128, d: u128, r: u128, v: u128) -> Option<u32> {
    debug_assert!(d >= 2 && v >= 1 && r >= 1);
    let mut cur = m / r;
    if cur < v {
        return None;
    }
    let mut k = 0u32;
    loop {
        cur /= d;
        if cur < v {
            return Some(k);
        }
        k += 1;
    }
}

/// The trip count `T = |{ j >= 0 : floor(m / d^j) > c }|` for the loop guard
/// `x > c` — `K(c + 1) + 1`, or `0` when the guard can never be true (u8's
/// `remain > 999`: emit nothing).
pub(super) fn countdown_trip_count(m: u128, d: u128, c: u128) -> u32 {
    match c.checked_add(1).and_then(|v| countdown_k_max(m, d, 1, v)) {
        Some(k) => k + 1,
        None => 0,
    }
}

/// `from` can reach `to` in the CFG (reflexive: `from == to` is `true`).
pub(super) fn countdown_can_reach(func: &VerifiableFunction, from: usize, to: usize) -> bool {
    let empty = FxHashSet::default();
    reachable_avoiding(func, from, &empty).contains(&to)
}

/// Structural constant resolution for the countdown gates: a literal, a
/// single-static-assignment `Use` copy chain ending in one, or a B0-modeled
/// `try_into(CONST).expect(..)` destination (`expect_consts`,
/// [`expect_infallible_const_map`] — how the itoa macro fns spell `999` and
/// `10_000`). Fail-closed `None` on anything else.
pub(super) fn countdown_resolve_const(
    func: &VerifiableFunction,
    op: &Operand,
    expect_consts: &FxHashMap<usize, i128>,
    fuel: u32,
) -> Option<i128> {
    if fuel == 0 {
        return None;
    }
    if let Some(c) = operand_const_int(op) {
        return Some(c);
    }
    let (Operand::Copy(p) | Operand::Move(p)) = op else { return None };
    if !p.projections.is_empty() || !is_single_static_assignment(func, p.local) {
        return None;
    }
    if let Some(v) = expect_consts.get(&p.local) {
        return Some(*v);
    }
    match crate::unique_whole_local_def(func, p.local) {
        Some(Rvalue::Use(inner)) => countdown_resolve_const(func, inner, expect_consts, fuel - 1),
        _ => None,
    }
}

/// The boolean `SwitchInt` edge pair of `block`: `(true_target, false_target)`,
/// `None` when the switch is not the two-armed boolean shape or the two edges
/// coincide (an ambiguous edge carries no branch information).
pub(super) fn countdown_bool_edges(block: &trust_types::BasicBlock) -> Option<(usize, usize)> {
    let Terminator::SwitchInt { targets, otherwise, .. } = &block.terminator else {
        return None;
    };
    let (t_true, t_false) = match targets.as_slice() {
        [(0, f)] => (otherwise.0, f.0),
        [(1, t)] => (t.0, otherwise.0),
        _ => return None,
    };
    (t_true != t_false).then_some((t_true, t_false))
}

/// The `x >= v` bound a boolean `SwitchInt` block's TRUE edge establishes about
/// companion `x`, read LOCALLY: the comparison def must live in the switch
/// block itself, its `x`-side operand must be `x` directly or a same-block
/// single-def copy of `x`, and the block must contain NO def of `x` at all —
/// so the value compared is exactly `x` at block entry (no stale temp carried
/// across a division, no mid-block reseat; the staleness that would otherwise
/// under-count divisions and over-credit the bound). The constant side resolves
/// through [`countdown_resolve_const`] (B0). Returns `v >= 1`.
pub(super) fn countdown_guard_true_edge_lower_bound(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    x: usize,
    expect_consts: &FxHashMap<usize, i128>,
) -> Option<i128> {
    let Terminator::SwitchInt { discr, .. } = &block.terminator else { return None };
    let (Operand::Copy(gp) | Operand::Move(gp)) = discr else { return None };
    if !gp.projections.is_empty() || !is_single_static_assignment(func, gp.local) {
        return None;
    }
    // No def of `x` anywhere in this block — the compared value is x at entry.
    let x_def_in_block = block
        .stmts
        .iter()
        .any(|s| matches!(s, Statement::Assign { place, .. } if place.local == x));
    if x_def_in_block {
        return None;
    }
    // The comparison def, in THIS block.
    let cmp = block.stmts.iter().find_map(|s| match s {
        Statement::Assign { place, rvalue: Rvalue::BinaryOp(op, a, b), .. }
            if place.local == gp.local && place.projections.is_empty() =>
        {
            Some((op, a, b))
        }
        _ => None,
    });
    let (op, a, b) = cmp?;
    // An operand "reads x FRESHLY": directly, via a same-block single-def copy,
    // or via a cross-block single-def copy whose copy-block -> switch-block
    // region is x-def-free (the while-loop desugar puts `_t = Copy x` in the
    // loop HEADER and the comparison after interleaved calls — `while remain >
    // 999.try_into().expect(..)`). SOUND: with no x-def on any copy -> switch
    // path that avoids re-entering the copy block, the value compared and the
    // division count at the switch are IDENTICAL to those at the copy — a stale
    // temp carried across a division (which would under-count divisions and
    // over-credit the bound) is exactly what the region check rejects.
    let reads_x_locally = |o: &Operand| -> bool {
        let (Operand::Copy(p) | Operand::Move(p)) = o else { return false };
        if !p.projections.is_empty() {
            return false;
        }
        if p.local == x {
            return true;
        }
        if !is_single_static_assignment(func, p.local) {
            return false;
        }
        if !matches!(
            crate::unique_whole_local_def(func, p.local),
            Some(Rvalue::Use(Operand::Copy(q) | Operand::Move(q)))
                if q.local == x && q.projections.is_empty()
        ) {
            return false;
        }
        // Same-block copy: fresh by the block's own x-def-freedom (checked above).
        if block.stmts.iter().any(|s| {
            matches!(s, Statement::Assign { place, .. }
                if place.local == p.local && place.projections.is_empty())
        }) {
            return true;
        }
        // Cross-block copy: locate the copy block D (the temp is SSA, so D is
        // its unique def site and dominates every read); require D itself
        // x-def-free, and NO x-def block on a D -> switch path avoiding D.
        let Some(d_block) = func.body.blocks.iter().find(|b| {
            b.stmts.iter().any(|s| {
                matches!(s, Statement::Assign { place, .. }
                    if place.local == p.local && place.projections.is_empty())
            })
        }) else {
            return false;
        };
        let d_defines_x = d_block
            .stmts
            .iter()
            .any(|s| matches!(s, Statement::Assign { place, .. } if place.local == x));
        if d_defines_x {
            return false;
        }
        let mut avoid_d = FxHashSet::default();
        avoid_d.insert(d_block.id.0);
        let region: FxHashSet<usize> = terminator_succs(&d_block.terminator)
            .into_iter()
            .flat_map(|s| reachable_avoiding(func, s, &avoid_d))
            .collect();
        for w in &func.body.blocks {
            let w_defines_x = w
                .stmts
                .iter()
                .any(|s| matches!(s, Statement::Assign { place, .. } if place.local == x))
                || matches!(&w.terminator, Terminator::Call { dest, .. } if dest.local == x);
            if w_defines_x
                && region.contains(&w.id.0)
                && reachable_avoiding(func, w.id.0, &avoid_d).contains(&block.id.0)
            {
                return false; // a division/reseat can sit between the read and the compare
            }
        }
        true
    };
    let resolve = |o: &Operand| countdown_resolve_const(func, o, expect_consts, 8);
    let v = match op {
        // `x > C` (x on the left) / `C < x` (x on the right): x >= C + 1.
        trust_types::BinOp::Gt if reads_x_locally(a) => resolve(b)?.checked_add(1)?,
        trust_types::BinOp::Lt if reads_x_locally(b) => resolve(a)?.checked_add(1)?,
        // `x >= C` / `C <= x`: x >= C.
        trust_types::BinOp::Ge if reads_x_locally(a) => resolve(b)?,
        trust_types::BinOp::Le if reads_x_locally(b) => resolve(a)?,
        // `x != 0`: x >= 1 (unsigned). Only the 0 constant carries a bound.
        trust_types::BinOp::Ne if reads_x_locally(a) && resolve(b) == Some(0) => 1,
        trust_types::BinOp::Ne if reads_x_locally(b) && resolve(a) == Some(0) => 1,
        _ => return None,
    };
    (v >= 1).then_some(v)
}

/// The ZERO-TRIP witness on a boolean TRUE edge: `Eq(p, k0)` where `p` is an
/// UNWRITTEN parameter and `k0` a constant. If the companion's single init is
/// `x = p` and `k0 <= C` (the loop-guard constant), the loop body ran ZERO
/// times on any trace taking this edge (`x0 = k0 <= C`: the guard is false at
/// its first evaluation and divisions only shrink). Returns `(p, k0)`.
pub(super) fn countdown_zero_trip_eq(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    expect_consts: &FxHashMap<usize, i128>,
) -> Option<(usize, i128)> {
    let Terminator::SwitchInt { discr, .. } = &block.terminator else { return None };
    let (Operand::Copy(gp) | Operand::Move(gp)) = discr else { return None };
    if !gp.projections.is_empty() || !is_single_static_assignment(func, gp.local) {
        return None;
    }
    let Some(Rvalue::BinaryOp(trust_types::BinOp::Eq, a, b)) =
        crate::unique_whole_local_def(func, gp.local)
    else {
        return None;
    };
    // A parameter read: direct, or a single-def whole copy (stability of `p`
    // makes read position irrelevant — its value IS the entry value).
    let param_of = |o: &Operand| -> Option<usize> {
        let (Operand::Copy(p) | Operand::Move(p)) = o else { return None };
        if !p.projections.is_empty() {
            return None;
        }
        let root = if (1..=func.body.arg_count).contains(&p.local) {
            p.local
        } else if is_single_static_assignment(func, p.local)
            && let Some(Rvalue::Use(Operand::Copy(q) | Operand::Move(q))) =
                crate::unique_whole_local_def(func, p.local)
            && q.projections.is_empty()
            && (1..=func.body.arg_count).contains(&q.local)
        {
            q.local
        } else {
            return None;
        };
        local_value_is_stable(func, root).then_some(root)
    };
    let resolve = |o: &Operand| countdown_resolve_const(func, o, expect_consts, 8);
    if let (Some(p), Some(k0)) = (param_of(a), resolve(b)) {
        return Some((p, k0));
    }
    if let (Some(p), Some(k0)) = (param_of(b), resolve(a)) {
        return Some((p, k0));
    }
    None
}

pub(super) fn build_countdown_trip_facts(func: &VerifiableFunction) -> Vec<Formula> {
    countdown_trip_analysis(func).global
}

/// The per-block pre-value companion of [`build_countdown_trip_facts`] —
/// conjoined onto the decrement blocks' VCs exactly like the converging
/// two-pointer facts (bare names, versioned at the consuming block).
pub(super) fn build_countdown_preval_facts(func: &VerifiableFunction) -> FxHashMap<BlockId, Vec<Formula>> {
    countdown_trip_analysis(func).per_block
}

/// Gates 4-7 of the countdown analysis for ONE candidate (guard, companion):
/// GATE-UINT + the whole-function companion def scan + division unavoidability
/// + the trip simulation. `None` rejects the CANDIDATE (never the family).
pub(super) fn countdown_companion_qual(
    func: &VerifiableFunction,
    expect_consts: &FxHashMap<usize, i128>,
    gb: usize,
    t_true: usize,
    t_false: usize,
    x: usize,
    v_loop: i128,
) -> Option<CountdownCompanionQual> {
    let empty: FxHashSet<usize> = FxHashSet::default();
    // Gate 4 (GATE-UINT): companion strictly UNSIGNED with a concrete width;
    // M is the TYPE maximum — never an interval-analysis value (i128-TOP rule).
    let Some(Ty::Int { width, signed: false }) = func.body.locals.get(x).map(|d| d.ty.clone())
    else {
        return None;
    };
    let m: u128 = crate::range::unsigned_max(width);

    // Gate 5: companion defs — one init + `x = x / D` (const D >= 2) self-
    // divisions; any OTHER def only in blocks that cannot reach the guard
    // (itoa's post-loop reseat). No `&mut`/`&raw` escape, no call dest.
    if local_mut_escapes(func, x) {
        return None;
    }
    let guard_reach = reachable_avoiding(func, gb, &empty);
    let is_param_x = (1..=func.body.arg_count).contains(&x);
    let mut init: Option<(usize, &Rvalue)> = None;
    let mut div_sites: Vec<(usize, u128)> = Vec::new(); // (block, D)
    let mut opaque_def_blocks: FxHashSet<usize> = FxHashSet::default();
    for block in &func.body.blocks {
        if matches!(&block.terminator, Terminator::Call { dest, .. } if dest.local == x) {
            return None;
        }
        for stmt in &block.stmts {
            let Statement::Assign { place, rvalue, .. } = stmt else { continue };
            if place.local != x {
                continue;
            }
            if !place.projections.is_empty() {
                return None;
            }
            let self_div = match rvalue {
                Rvalue::BinaryOp(trust_types::BinOp::Div, lhs, rhs)
                    if matches!(lhs, Operand::Copy(p) | Operand::Move(p)
                        if p.local == x && p.projections.is_empty()) =>
                {
                    countdown_resolve_const(func, rhs, expect_consts, 8)
                }
                _ => None,
            };
            if let Some(d) = self_div {
                if d < 2 {
                    return None; // D=1 never shrinks; D<=0 is not a shrink either.
                }
                div_sites.push((block.id.0, d as u128));
            } else if countdown_can_reach(func, block.id.0, gb) {
                // A non-division def that can precede loop iterations: the init,
                // at most once, and never re-executable (not reachable FROM the
                // guard — an in-loop re-init re-inflates x: unbounded trips).
                if is_param_x || init.is_some() || guard_reach.contains(&block.id.0) {
                    return None;
                }
                init = Some((block.id.0, rvalue));
            } else {
                // Strictly post-loop non-division def (opaque reseat): sound for
                // the trip count; makes later PATH guards unusable (B3 tracking).
                opaque_def_blocks.insert(block.id.0);
            }
        }
    }
    if !is_param_x && init.is_none() {
        return None;
    }
    // In-loop divisions: on the guard's cycle. D := the minimum (worst case).
    let in_loop_divs: Vec<(usize, u128)> = div_sites
        .iter()
        .copied()
        .filter(|&(b, _)| guard_reach.contains(&b) && countdown_can_reach(func, b, gb))
        .collect();
    let d_loop = in_loop_divs.iter().map(|&(_, d)| d).min()?;
    // Gate 6: the division is UNAVOIDABLE per iteration — from the guard's
    // true edge, the guard is unreachable when avoiding the in-loop division
    // blocks (kills `if f { x /= D }`: an unbounded-trip false proof).
    let div_blocks: FxHashSet<usize> = in_loop_divs.iter().map(|&(b, _)| b).collect();
    if reachable_avoiding(func, t_true, &div_blocks).contains(&gb) {
        return None;
    }

    // Gate 7: T by simulation (the T == 0 emit-nothing decision is the caller's).
    let c_guard = v_loop - 1; // v_loop >= 1 so C >= 0.
    let trips = countdown_trip_count(m, d_loop, c_guard as u128);

    // The zero-trip source: the companion's init is an UNWRITTEN parameter.
    let zero_trip_src: Option<usize> = match init {
        Some((_, Rvalue::Use(Operand::Copy(q) | Operand::Move(q))))
            if q.projections.is_empty()
                && (1..=func.body.arg_count).contains(&q.local)
                && q.local != x
                && local_value_is_stable(func, q.local) =>
        {
            Some(q.local)
        }
        _ => None,
    };

    Some(CountdownCompanionQual {
        gb,
        t_false,
        x,
        m,
        d_loop,
        c_guard,
        trips,
        div_sites,
        opaque_def_blocks,
        zero_trip_src,
    })
}

pub(super) fn countdown_trip_analysis(func: &VerifiableFunction) -> CountdownFacts {
    const MAX_PATHS: usize = 8;
    const MAX_PATH_LEN: usize = 64;
    let mut facts = CountdownFacts::default();
    if func.body.blocks.is_empty() {
        return facts;
    }
    let expect_consts = expect_infallible_const_map(func);
    let entry = func.body.blocks[0].id.0;

    'dv: for dv in downward_induction_vars(func) {
        // Gate 1: single CONSTANT init — a symbolic LEN cannot justify
        // `LEN - c*T >= 0`, and a multi-init cursor has no single position count.
        let Some(len) = dv.single_const_init else { continue };
        // Gate 2: exactly ONE decrement site on a cycle (a second on-cycle site
        // under-counts the stride; duplicate temps are ambiguous — bail).
        let mut on_cycle: Vec<(usize, i128, usize)> = Vec::new();
        let mut off_cycle: Vec<(usize, i128, usize)> = Vec::new();
        {
            let mut seen_temps: FxHashSet<usize> = FxHashSet::default();
            for &(t, c) in &dv.decrements {
                if !seen_temps.insert(t) {
                    continue 'dv;
                }
                let Some(csb) = checked_sub_block(func, t) else { continue 'dv };
                if block_is_on_cycle(func, csb) {
                    on_cycle.push((t, c, csb));
                } else {
                    off_cycle.push((t, c, csb));
                }
            }
        }
        let [(t_loop, c_loop, cs_block)] = on_cycle.as_slice() else { continue };
        let (t_loop, c_loop, cs_block) = (*t_loop, *c_loop, *cs_block);
        if c_loop < 1 {
            continue;
        }
        // Every OFF-cycle decrement must be strictly post-loop (a pre-loop
        // decrement executes before in-loop ones and breaks position counting).
        for &(_, _, sb) in &off_cycle {
            if countdown_can_reach(func, sb, cs_block) {
                continue 'dv;
            }
        }

        // Gate 3: the loop guard — a boolean SwitchInt whose TRUE edge is the
        // ONLY way to the decrement (true-edge reachable, false-edge and
        // entry-avoiding-guard NOT), read locally from a companion `x != cursor`.
        // EVERY dominating candidate is tried, and a candidate whose companion
        // fails the gates 4-7 moves on to the NEXT candidate rather than
        // bailing the family — the real itoa loop condition is
        // `mem::size_of::<Self>() > 1 && remain > limit`, TWO chained boolean
        // switches that BOTH dominate the decrement: the size_of switch comes
        // first in block order and its "companion" is a call dest (gate 5
        // rejects it); the `remain` switch right behind it is the countdown
        // guard. Trying candidates in sequence is sound: each fully-qualified
        // (guard, companion) pair independently proves its own T bound.
        let mut qual: Option<CountdownCompanionQual> = None;
        'guard: for gblock in &func.body.blocks {
            let Some((t_true, t_false)) = countdown_bool_edges(gblock) else { continue };
            let gb = gblock.id.0;
            let mut avoid = FxHashSet::default();
            avoid.insert(gb);
            if !reachable_avoiding(func, t_true, &avoid).contains(&cs_block)
                || reachable_avoiding(func, t_false, &avoid).contains(&cs_block)
                || reachable_avoiding(func, entry, &avoid).contains(&cs_block)
            {
                continue;
            }
            // No guard-free cycle through the decrement: between two decrement
            // executions there is always a guard passage.
            let cs_cycle_free = terminator_succs(&func.body.blocks[cs_block].terminator)
                .into_iter()
                .all(|s| !reachable_avoiding(func, s, &avoid).contains(&cs_block));
            if !cs_cycle_free {
                continue;
            }
            // The companion read: try every local as x is overkill — extract the
            // compared local from the switch block's own comparison def by probing
            // the guard shape for each candidate side. The comparison operands are
            // in the block; test both sides' root locals.
            let Terminator::SwitchInt { discr, .. } = &gblock.terminator else { continue };
            let (Operand::Copy(gp) | Operand::Move(gp)) = discr else { continue };
            if !gp.projections.is_empty() {
                continue;
            }
            let sides = gblock.stmts.iter().find_map(|s| match s {
                Statement::Assign { place, rvalue: Rvalue::BinaryOp(_, a, b), .. }
                    if place.local == gp.local && place.projections.is_empty() =>
                {
                    Some((operand_root_local(func, a, 8), operand_root_local(func, b, 8)))
                }
                _ => None,
            });
            let Some((ra, rb)) = sides else { continue };
            for x in [ra, rb].into_iter().flatten() {
                if x == dv.local {
                    continue;
                }
                if let Some(v) =
                    countdown_guard_true_edge_lower_bound(func, gblock, x, &expect_consts)
                    && let Some(q) =
                        countdown_companion_qual(func, &expect_consts, gb, t_true, t_false, x, v)
                {
                    qual = Some(q);
                    break 'guard;
                }
            }
        }
        let Some(q) = qual else { continue };
        let CountdownCompanionQual {
            gb,
            t_false,
            x,
            m,
            d_loop,
            c_guard,
            trips,
            div_sites,
            opaque_def_blocks,
            zero_trip_src,
        } = q;
        // Gate 7 tail: T == 0 emits NOTHING (u8 — "vacuously true because
        // unreachable" is not this builder's theorem to assert).
        if trips == 0 {
            continue;
        }

        // B2: the loop-site decrement result bound (emit only when >= 0 — a
        // negative bound is exactly the one-smaller-buffer refutation case).
        // Saturating arithmetic throughout the bound computations: saturation
        // only ever DRIVES THE BOUND DOWN (toward "emit nothing"), never up.
        let loop_lower = len.saturating_sub(c_loop.saturating_mul(i128::from(trips)));
        let cursor_var =
            || Formula::Var(crate::place_to_var_name(func, &Place::local(dv.local)), Sort::Int);
        let block_stores_cursor = |b: usize| {
            func.body.blocks[b]
                .stmts
                .iter()
                .any(|s| matches!(s, Statement::Assign { place, .. } if place.local == dv.local))
        };
        if loop_lower >= 0 {
            let result_place =
                Place { local: t_loop, projections: vec![trust_types::Projection::Field(0)] };
            facts.global.push(Formula::Ge(
                Box::new(Formula::Var(crate::place_to_var_name(func, &result_place), Sort::Int)),
                Box::new(Formula::Int(loop_lower)),
            ));
            // Pre-value form at the decrement block: the m-th execution reads
            // `i = LEN - c*(m-1) >= LEN - c*(T-1)` (see the struct doc for the
            // no-same-block-store gate).
            if !block_stores_cursor(cs_block) {
                facts.per_block.entry(BlockId(cs_block)).or_default().push(Formula::Ge(
                    Box::new(cursor_var()),
                    Box::new(Formula::Int(loop_lower.saturating_add(c_loop))),
                ));
            }
        }

        // ---------------- B3: post-loop coupling, per site ----------------
        if off_cycle.is_empty() {
            continue;
        }
        // Cursor store blocks per decrement temp (`i = _t.0`), for S_path.
        let store_blocks_of = |t: usize| -> FxHashSet<usize> {
            let mut out = FxHashSet::default();
            for block in &func.body.blocks {
                for stmt in &block.stmts {
                    if let Statement::Assign {
                        place,
                        rvalue: Rvalue::Use(Operand::Copy(p) | Operand::Move(p)),
                        ..
                    } = stmt
                        && place.local == dv.local
                        && place.projections.is_empty()
                        && p.local == t
                        && matches!(p.projections.as_slice(), [trust_types::Projection::Field(0)])
                    {
                        out.insert(block.id.0);
                    }
                }
            }
            out
        };
        let entry_avoiding_guard = {
            let mut avoid = FxHashSet::default();
            avoid.insert(gb);
            reachable_avoiding(func, entry, &avoid)
        };
        'site: for &(t_s, c_s, site_block) in &off_cycle {
            // The site executes only after the loop (never guard-free from entry).
            if entry_avoiding_guard.contains(&site_block) {
                continue;
            }
            // Enumerate the acyclic exit paths t_false -> site (avoiding the
            // guard: the tail after the LAST guard passage). A revisit means a
            // cyclic post-loop region — bail the site (S_path would under-count).
            let mut paths: Vec<Vec<usize>> = Vec::new();
            let mut stack: Vec<Vec<usize>> = vec![vec![t_false]];
            let mut steps = 0usize;
            while let Some(path) = stack.pop() {
                steps += 1;
                if steps > 4096 || path.len() > MAX_PATH_LEN {
                    continue 'site;
                }
                let last = *path.last().expect("non-empty path");
                if last == site_block {
                    paths.push(path);
                    if paths.len() > MAX_PATHS {
                        continue 'site;
                    }
                    continue;
                }
                if last >= func.body.blocks.len() {
                    continue;
                }
                for succ in terminator_succs(&func.body.blocks[last].terminator) {
                    if succ == gb {
                        continue; // re-entering the loop is not a tail path
                    }
                    if path.contains(&succ) {
                        continue 'site; // cyclic exit region: bail the site
                    }
                    let mut next = path.clone();
                    next.push(succ);
                    stack.push(next);
                }
            }
            if paths.is_empty() {
                continue; // site unreachable from the exit edge: no fact
            }
            // The loop-site decrement must never sit on an exit tail.
            if paths.iter().any(|p| p.contains(&cs_block)) {
                continue;
            }
            let mut site_min: Option<i128> = None;
            for path in &paths {
                // S_path: other off-cycle decrements executed on this tail
                // (counted once per site — off-cycle blocks are cycle-free).
                let mut s_path: i128 = 0;
                for &(t_o, c_o, sb_o) in &off_cycle {
                    if t_o == t_s {
                        continue;
                    }
                    let stores = store_blocks_of(t_o);
                    if path.iter().any(|b| *b == sb_o || stores.contains(b)) {
                        s_path = s_path.saturating_add(c_o);
                    }
                }
                // Walk the path: accumulate R (path division constants) and the
                // opaque flag; collect guard candidates at each taken edge.
                let mut r: u128 = 1;
                let mut x_opaque = false;
                let mut best: i128 = len
                    .saturating_sub(c_loop.saturating_mul(i128::from(trips)))
                    .saturating_sub(s_path)
                    .saturating_sub(c_s);
                let mut infeasible = false;
                for (i, &b) in path.iter().enumerate() {
                    if i + 1 < path.len() {
                        let next = path[i + 1];
                        let block = &func.body.blocks[b];
                        if let Some((tt_b, tf_b)) = countdown_bool_edges(block) {
                            // Guard candidate on the TRUE edge, x still pure.
                            if next == tt_b
                                && tf_b != next
                                && !x_opaque
                                && let Some(v) = countdown_guard_true_edge_lower_bound(
                                    func,
                                    block,
                                    x,
                                    &expect_consts,
                                )
                            {
                                match countdown_k_max(m, d_loop, r, v as u128) {
                                    None => {
                                        infeasible = true;
                                        break;
                                    }
                                    Some(k) => {
                                        let k = k.min(trips);
                                        let cand = len
                                            .saturating_sub(c_loop.saturating_mul(i128::from(k)))
                                            .saturating_sub(s_path)
                                            .saturating_sub(c_s);
                                        best = best.max(cand);
                                    }
                                }
                            }
                            // Zero-trip candidate on the TRUE edge.
                            if next == tt_b
                                && tf_b != next
                                && let Some(src) = zero_trip_src
                                && let Some((p, k0)) =
                                    countdown_zero_trip_eq(func, block, &expect_consts)
                                && p == src
                                && (0..=c_guard).contains(&k0)
                            {
                                best = best.max(len.saturating_sub(s_path).saturating_sub(c_s));
                            }
                        }
                    }
                    // The block's own companion defs apply to LATER guards (guard
                    // blocks themselves are x-def-free by construction).
                    if opaque_def_blocks.contains(&b) {
                        x_opaque = true;
                    }
                    for &(db, d) in &div_sites {
                        if db == b {
                            r = r.saturating_mul(d);
                        }
                    }
                }
                if infeasible {
                    continue; // this path can never execute: no minimum from it
                }
                site_min = Some(site_min.map_or(best, |sm: i128| sm.min(best)));
            }
            if let Some(bound) = site_min
                && bound >= 0
            {
                let result_place =
                    Place { local: t_s, projections: vec![trust_types::Projection::Field(0)] };
                facts.global.push(Formula::Ge(
                    Box::new(Formula::Var(
                        crate::place_to_var_name(func, &result_place),
                        Sort::Int,
                    )),
                    Box::new(Formula::Int(bound)),
                ));
                // Pre-value form at the site block (result + c_s), same
                // no-same-block-store gate as the loop site.
                if !block_stores_cursor(site_block) {
                    facts.per_block.entry(BlockId(site_block)).or_default().push(Formula::Ge(
                        Box::new(cursor_var()),
                        Box::new(Formula::Int(bound.saturating_add(c_s))),
                    ));
                }
            }
        }
    }
    facts
}
