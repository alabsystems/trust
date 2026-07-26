// Loop iteration and accumulation bounds: back-edge counting, fixed-array and
// reduction trip counts, per-iteration addend ranges, flattened multi-dimension
// indices, and pointers that converge on a common target. The result is an
// upper bound on what an accumulator can reach, which is what an overflow
// obligation over a loop-carried value needs.

use super::*;

/// CFG successors of a terminator (block ids).
pub(super) fn terminator_succs(t: &Terminator) -> Vec<usize> {
    match t {
        Terminator::Goto(b) => vec![b.0],
        Terminator::SwitchInt { targets, otherwise, .. } => {
            targets.iter().map(|(_, b)| b.0).chain(std::iter::once(otherwise.0)).collect()
        }
        Terminator::Assert { target, .. } | Terminator::Drop { target, .. } => vec![target.0],
        Terminator::Call { target, .. } => target.iter().map(|b| b.0).collect(),
        Terminator::Opaque { targets, .. } => targets.iter().map(|b| b.0).collect(),
        _ => Vec::new(),
    }
}

/// Count distinct LOOP HEADERS — the distinct TARGETS of true CFG BACK EDGES, found by DFS
/// from the entry block: an edge `u -> v` is a back edge iff `v` is GRAY (on the recursion
/// stack) when traversed, i.e. `v` is an ancestor of `u` (so `v` is a loop header). Counting
/// distinct back-edge targets measures the number of loops EXACTLY for any CFG: multiple back
/// edges to the SAME header (an intra-loop `if`/`continue`) are one loop, while each NESTED
/// loop has a distinct header. Unlike the prior `succ <= src` heuristic, a forward/cross edge
/// to an earlier-numbered block is NOT a back edge (its target is not on the stack), so it is
/// not miscounted — which is what lets a nested matrix loop be recognized as exactly 2 loops.
/// Iterative DFS to avoid recursion-depth limits on large generated bodies.
pub(super) fn count_back_edges(func: &VerifiableFunction) -> usize {
    let blocks = &func.body.blocks;
    if blocks.is_empty() {
        return 0;
    }
    let succ: FxHashMap<usize, Vec<usize>> =
        blocks.iter().map(|b| (b.id.0, terminator_succs(&b.terminator))).collect();
    // 0 = white (unseen), 1 = gray (on stack), 2 = black (finished).
    let mut color: FxHashMap<usize, u8> = blocks.iter().map(|b| (b.id.0, 0u8)).collect();
    let mut headers: FxHashSet<usize> = FxHashSet::default();
    let entry = blocks[0].id.0;
    color.insert(entry, 1);
    let mut stack: Vec<(usize, usize)> = vec![(entry, 0)];
    while let Some(&(u, i)) = stack.last() {
        let edges = succ.get(&u).map(Vec::as_slice).unwrap_or(&[]);
        if i < edges.len() {
            stack.last_mut().unwrap().1 += 1;
            let v = edges[i];
            match color.get(&v).copied().unwrap_or(2) {
                0 => {
                    color.insert(v, 1);
                    stack.push((v, 0));
                }
                1 => {
                    headers.insert(v); // back edge: v is on the recursion stack
                }
                _ => {} // forward / cross edge
            }
        } else {
            color.insert(u, 2);
            stack.pop();
        }
    }
    headers.len()
}

/// Trace an iterator local back to the operand passed to its `into_iter` constructor
/// (`iter = into_iter(arr)`), walking whole-local Ref/Use copies. Returns the
/// `into_iter` ARGUMENT — for `for &x in &[ELEM;N]` this is the array.
pub(super) fn trace_iter_to_into_iter_arg(
    func: &VerifiableFunction,
    local: usize,
    fuel: u32,
) -> Option<Operand> {
    if fuel == 0 {
        return None;
    }
    if let Some(rvalue) = crate::unique_whole_local_def(func, local) {
        return match rvalue {
            Rvalue::Ref { place, .. } if place.projections.is_empty() => {
                trace_iter_to_into_iter_arg(func, place.local, fuel - 1)
            }
            Rvalue::Use(Operand::Copy(p) | Operand::Move(p)) if p.projections.is_empty() => {
                trace_iter_to_into_iter_arg(func, p.local, fuel - 1)
            }
            _ => None,
        };
    }
    for block in &func.body.blocks {
        if let Terminator::Call { func: callee, args, dest, .. } = &block.terminator
            && dest.local == local
            && dest.projections.is_empty()
            && args.len() == 1
            && callee_is_into_iter(callee)
        {
            return Some(args[0].clone());
        }
    }
    None
}

/// Find the `Iterator::next` call whose dest is `next_result_local` and trace its
/// receiver to the `into_iter` argument (the iterated collection).
pub(super) fn next_call_to_array_operand(
    func: &VerifiableFunction,
    next_result_local: usize,
    fuel: u32,
) -> Option<Operand> {
    for block in &func.body.blocks {
        if let Terminator::Call { func: callee, args, dest, .. } = &block.terminator
            && dest.local == next_result_local
            && dest.projections.is_empty()
            && callee_is_iterator_next(callee)
            && args.len() == 1
            && let Operand::Copy(p) | Operand::Move(p) = &args[0]
            && p.projections.is_empty()
        {
            return trace_iter_to_into_iter_arg(func, p.local, fuel);
        }
    }
    None
}

/// `(N, MAX(ELEM))` for a fixed array `[ELEM; N]` with unsigned integer `ELEM`.
pub(super) fn fixed_array_elem_bound(elem: &Ty, len: u64) -> Option<(i128, i128)> {
    let width = elem.int_width()?;
    if elem.is_signed() || !elem.is_integer() || width >= 127 {
        return None;
    }
    Some((len as i128, (1i128 << width) - 1))
}

/// For a loop-element local `x` (the `&x`/`x` bound by `for &x in C`), if `C` is a
/// FIXED-SIZE array `[ELEM; N]` with unsigned `ELEM`, return `(N, MAX(ELEM))`. The
/// for-each desugar binds `x = *(next(&mut iter) as Some).0`, `iter = into_iter(C)`.
/// Only a fixed-size array yields a STATIC trip count `N`; a slice (symbolic length)
/// or any other shape returns None.
pub(super) fn for_each_element_fixed_array_bound(
    func: &VerifiableFunction,
    x_local: usize,
) -> Option<(i128, i128)> {
    let (elem, len) = for_each_array_elem_ty(func, x_local)?;
    fixed_array_elem_bound(&elem, len)
}

/// The `(ELEM, LEN)` of the FIXED-SIZE array a for-each loop-element local `x` (the
/// `&x`/`x` bound by `for &x in C`) iterates, by tracing the for-each desugar
/// `x = *(next(&mut iter) as Some).0`, `iter = into_iter(C)` back to `C`. Returns the
/// element type and length WITHOUT any signedness/width judgement — callers apply their
/// own (unsigned `fixed_array_elem_bound`, or the signed-aware reduction range). Only a
/// fixed-size array (static `LEN`) qualifies; a slice or other shape yields None.
pub(super) fn for_each_array_elem_ty(func: &VerifiableFunction, x_local: usize) -> Option<(Ty, u64)> {
    const FUEL: u32 = 16;
    // x = *deref_src
    let deref_src = match crate::unique_whole_local_def(func, x_local)? {
        Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
            if matches!(p.projections.as_slice(), [trust_types::Projection::Deref]) =>
        {
            p.local
        }
        _ => return None,
    };
    // deref_src = some_local.Downcast(_).Field(0)  (the Option Some payload `&ELEM`)
    let some_local = match crate::unique_whole_local_def(func, deref_src)? {
        Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
            if matches!(
                p.projections.as_slice(),
                [trust_types::Projection::Downcast(_), trust_types::Projection::Field(0)]
            ) =>
        {
            p.local
        }
        _ => return None,
    };
    // some_local = next() result; trace its receiver to the iterated array operand.
    let array_op = next_call_to_array_operand(func, some_local, FUEL)?;
    match crate::operand_ty(func, &array_op)? {
        Ty::Array { elem, len } => Some((*elem, len)),
        Ty::Ref { inner, .. } => match *inner {
            Ty::Array { elem, len } => Some((*elem, len)),
            _ => None,
        },
        _ => None,
    }
}

/// Read an operand as a known integer constant.
pub(super) fn operand_const_int(op: &Operand) -> Option<i128> {
    match op {
        Operand::Constant(ConstValue::Int(c)) => Some(*c),
        Operand::Constant(ConstValue::Uint(c, _)) if *c <= i128::MAX as u128 => Some(*c as i128),
        _ => None,
    }
}

/// The index LOCAL of the last `Index(_)` projection in `place` (`a[i]` -> `i`'s local).
pub(super) fn index_local_of_place(place: &Place) -> Option<usize> {
    place.projections.iter().rev().find_map(|p| match p {
        trust_types::Projection::Index(i) => Some(*i),
        _ => None,
    })
}

/// `(K, MAX(ELEM))` for a manual-INDEX reduction addend `x = a[i]`, where the loaded
/// element `x` has UNSIGNED integer type (so `0 <= x <= MAX(type)` for whatever value is
/// read) and the index `i` is the value yielded by the exclusive `Range` `[start, end)`
/// driving the (single) loop, so the self-add runs EXACTLY `K = end - start` times. Both
/// range bounds must be known non-negative constants with `end >= start`. Unlike a
/// for-each over a fixed array, the trip count here comes from the RANGE, not an array
/// length — and that is precisely what keeps `t <= C + K*MAX(ELEM)` a SOUND invariant: a
/// `Range` yields each value once and then stops, so (under the single-loop guard in the
/// caller) the self-add cannot run more than `K` times. A manually-incremented or
/// non-monotonic counter is NOT a `Range::next` payload and yields None — it could revisit
/// an in-bounds index unboundedly, which would make the bound false. A slice/dynamic end,
/// a signed/non-integer element, or a non-constant bound also yield None.
pub(super) fn index_range_reduction_bound(func: &VerifiableFunction, x_local: usize) -> Option<(i128, i128)> {
    const FUEL: u32 = 16;
    // x = a[i] : a load of an Index place (possibly behind a Deref for `&[ELEM; N]`).
    let idx_local = match crate::unique_whole_local_def(func, x_local)? {
        Rvalue::Use(Operand::Copy(p) | Operand::Move(p)) => index_local_of_place(p)?,
        _ => return None,
    };
    // The loaded element's OWN type bounds the addend: unsigned integer => `<= MAX(type)`.
    // verifier-perf: borrow the declared type — only scalar predicates are read.
    let elem_ty = crate::local_ty_ref(func, x_local)?;
    let width = elem_ty.int_width()?;
    if elem_ty.is_signed() || !elem_ty.is_integer() || width >= 127 {
        return None;
    }
    let elem_max = (1i128 << width) - 1;
    // i = (next() as Some).0 — the value yielded by the loop's exclusive Range.
    let opt_local = match crate::unique_whole_local_def(func, idx_local)? {
        Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
            if is_some_payload_projection(&p.projections) =>
        {
            p.local
        }
        _ => return None,
    };
    let (start_op, end_op) = next_call_range_operands(func, opt_local, FUEL)?;
    let k = operand_const_int(end_op)?.checked_sub(operand_const_int(start_op)?)?;
    if k < 0 {
        return None;
    }
    Some((k, elem_max))
}

/// The constant init `C` of a self-accumulator `acc`, IFF `acc`'s ONLY two whole-local
/// definitions are (a) `acc = const C` (`C >= 0`) and (b) `acc = Copy/Move(ck_dest).0`
/// (the self-add result). Any other definition returns None — so the bound
/// `acc <= C + N*M` cannot be invalidated by a value the accumulation doesn't account
/// for. Two writes the statement scan below CANNOT see would each invalidate the bound,
/// so both fail-closed: (1) a `Call` terminator whose dest is `acc` (`acc = f()` sets it
/// to an unconstrained return value); (2) a mutable borrow `&mut acc`, or a RAW pointer of
/// `acc` of EITHER mutability `&raw const/mut acc` (`AddressOf(_, ..)`), through which an
/// unsafe write can flow — a `*const` raw pointer is a valid root for a `*const -> *mut`
/// cast + write, so withholding only the mutable-raw form left a stale-bound leak that was
/// merely obligation-contained (hunt-4 defense-in-depth). A shared borrow `&acc` cannot
/// mutate and its cast to `*mut` is rejected by the `invalid_reference_casting` deny, so it
/// need not be withheld (keeps the bound for legitimate read-only borrows of `acc`).
pub(super) fn accumulator_init_const(func: &VerifiableFunction, acc: usize, ck_dest: usize) -> Option<i128> {
    let mut init: Option<i128> = None;
    let mut saw_self_add = false;
    let mut def_count = 0usize;
    for block in &func.body.blocks {
        if let Terminator::Call { dest, .. } = &block.terminator
            && dest.local == acc
            && dest.projections.is_empty()
        {
            return None;
        }
        for stmt in &block.stmts {
            let Statement::Assign { place, rvalue, .. } = stmt else { continue };
            if let Rvalue::Ref { mutable: true, place: aliased } | Rvalue::AddressOf(_, aliased) =
                rvalue
                && aliased.local == acc
            {
                return None;
            }
            if place.local != acc || !place.projections.is_empty() {
                continue;
            }
            def_count += 1;
            match rvalue {
                Rvalue::Use(Operand::Constant(ConstValue::Int(c))) if *c >= 0 => init = Some(*c),
                Rvalue::Use(Operand::Constant(ConstValue::Uint(c, _)))
                    if *c <= i128::MAX as u128 =>
                {
                    init = Some(*c as i128)
                }
                Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
                    if p.local == ck_dest
                        && matches!(
                            p.projections.as_slice(),
                            [trust_types::Projection::Field(0)]
                        ) =>
                {
                    saw_self_add = true
                }
                _ => return None,
            }
        }
    }
    if def_count == 2 && saw_self_add { init } else { None }
}

/// The trip count `K` of the single loop, traced from a reduction ELEMENT local (the
/// for-each element or the manual-index loaded element) — `N` for a fixed array, or
/// `end - start` for a Range-driven loop. Discards the element's own max (the caller
/// supplies a possibly-different per-addend max, e.g. a product).
pub(super) fn reduction_trip_count(func: &VerifiableFunction, elem_local: usize) -> Option<i128> {
    for_each_element_fixed_array_bound(func, elem_local)
        .or_else(|| index_range_reduction_bound(func, elem_local))
        .map(|(k, _)| k)
}

/// An upper bound on how many times the loop body (and so any self-add inside it) executes:
/// the PRODUCT of every loop's trip count. Each loop must be a const-bounded iterator — an
/// exclusive `Range::next` `[start, end)` (K = end - start) or a for-each `into_iter` over a
/// fixed array `[ELEM; N]` (K = N) — found by tracing its `Iterator::next` call. Handles a
/// SINGLE loop (product over one factor), NESTED loops (`for i { for j { t += a[i][j] } }`
/// — K = N*M), and a CONSTANT-addend reduction where there is no addend element to trace K
/// from.
///
/// SOUNDNESS — never UNDER-counts (which would make `t <= init + K*M` a false bound): there
/// is exactly one `Iterator::next` call per `Range`/for-each loop, so this requires the
/// number of `next()` calls to EQUAL the number of loops (distinct back-edge headers,
/// `count_back_edges`). A while-loop or a non-const range has no/uncountable trip count and
/// no matching `next()` call, so it makes the counts differ ⇒ None ⇒ no bound. For SEQUENTIAL
/// (non-nested) loops the product OVER-counts (sound, looser); a self-add appearing in more
/// than one loop is independently excluded by `accumulator_init_const`'s single-self-add gate.
/// True if block `start` lies on a CYCLE — its own successors can reach it again
/// (`start -> … -> start`). A loop DRIVER (`Iterator::next` called every iteration)
/// sits on its loop's cycle; a STRAY `next()` consumed once before/after a loop does
/// not. Forward reachability over `terminator_succs` (the same successor relation
/// `count_back_edges` walks), bounded by the visited set.
pub(super) fn block_is_on_cycle(func: &VerifiableFunction, start: usize) -> bool {
    let succ: FxHashMap<usize, Vec<usize>> =
        func.body.blocks.iter().map(|b| (b.id.0, terminator_succs(&b.terminator))).collect();
    let mut stack: Vec<usize> = succ.get(&start).cloned().unwrap_or_default();
    let mut seen: FxHashSet<usize> = FxHashSet::default();
    while let Some(b) = stack.pop() {
        if b == start {
            return true;
        }
        if seen.insert(b)
            && let Some(s) = succ.get(&b)
        {
            stack.extend(s.iter().copied());
        }
    }
    false
}

pub(super) fn total_loop_iterations(func: &VerifiableFunction) -> Option<i128> {
    const FUEL: u32 = 16;
    // Count ONLY the `Iterator::next` calls that actually DRIVE a loop — i.e. whose
    // call block lies on a CYCLE (the loop body branches back through it every
    // iteration). A STRAY `next()` consumed once OUTSIDE any loop (`let _ = it.next();`
    // before a `while`) is NOT on a cycle, so excluding it stops it from balancing a
    // manual while-loop's back-edge count: otherwise `#next == #back_edges` held
    // (1 == 1) and the stray range's trip count `K` became the while-loop's
    // accumulator bound, falsely discharging an out-of-bounds index (SOUNDNESS,
    // hunt-11). Excluding (vs failing) is the looser sound choice — a real for-each
    // loop alongside a stray next still proves via the genuine on-cycle driver.
    let next_dests: Vec<usize> = func
        .body
        .blocks
        .iter()
        .filter_map(|b| match &b.terminator {
            Terminator::Call { func: callee, dest, .. }
                if callee_is_iterator_next(callee)
                    && dest.projections.is_empty()
                    && block_is_on_cycle(func, b.id.0) =>
            {
                Some(dest.local)
            }
            _ => None,
        })
        .collect();
    if next_dests.is_empty() || next_dests.len() != count_back_edges(func) {
        return None;
    }
    let mut k: i128 = 1;
    for dest in next_dests {
        let tc = if let Some((start, end)) = next_call_range_operands(func, dest, FUEL) {
            operand_const_int(end)?.checked_sub(operand_const_int(start)?)?
        } else if let Some(arr) = next_call_to_array_operand(func, dest, FUEL) {
            match crate::operand_ty(func, &arr)? {
                Ty::Array { len, .. } => len as i128,
                Ty::Ref { inner, .. } => match *inner {
                    Ty::Array { len, .. } => len as i128,
                    _ => return None,
                },
                _ => return None,
            }
        } else {
            return None;
        };
        if tc < 0 {
            return None;
        }
        k = k.checked_mul(tc)?;
    }
    Some(k)
}

/// The two operands of a multiply that produces the reduction addend — either a direct
/// `Mul(l, r)` rvalue or the `Field(0)` of a `CheckedMul(l, r)` (the overflow-checked
/// product the `+=` reads). None for any other shape.
pub(super) fn reduction_mul_operands(
    func: &VerifiableFunction,
    addend_local: usize,
) -> Option<(Operand, Operand)> {
    match crate::unique_whole_local_def(func, addend_local)? {
        Rvalue::CheckedBinaryOp(BinOp::Mul, l, r) | Rvalue::BinaryOp(BinOp::Mul, l, r) => {
            Some((l.clone(), r.clone()))
        }
        Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
            if matches!(p.projections.as_slice(), [trust_types::Projection::Field(0)]) =>
        {
            match crate::unique_whole_local_def(func, p.local)? {
                Rvalue::CheckedBinaryOp(BinOp::Mul, l, r) => Some((l.clone(), r.clone())),
                _ => None,
            }
        }
        _ => None,
    }
}

/// The `(base, shift-amount)` operands of a LEFT-SHIFT producing the reduction addend —
/// either a direct `Shl` or the `.0` field of an overflow-checked `Shl` (mirrors
/// `reduction_mul_operands`). Used to recognize a shift-scaled addend `t += (x as ACC) << k`.
pub(super) fn reduction_shl_operands(
    func: &VerifiableFunction,
    addend_local: usize,
) -> Option<(Operand, Operand)> {
    match crate::unique_whole_local_def(func, addend_local)? {
        Rvalue::CheckedBinaryOp(BinOp::Shl, l, r) | Rvalue::BinaryOp(BinOp::Shl, l, r) => {
            Some((l.clone(), r.clone()))
        }
        Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
            if matches!(p.projections.as_slice(), [trust_types::Projection::Field(0)]) =>
        {
            match crate::unique_whole_local_def(func, p.local)? {
                Rvalue::CheckedBinaryOp(BinOp::Shl, l, r) => Some((l.clone(), r.clone())),
                _ => None,
            }
        }
        _ => None,
    }
}

/// An upper bound on a multiply FACTOR's value. A non-negative integer constant bounds
/// itself. A `Cast(src, _)` of an UNSIGNED integer source is bounded by `MAX(src type)`:
/// `src` is a typed value in `[0, MAX(src)]` (even a wrapped intermediate is a valid value
/// of its type), and a widening cast preserves it while a narrowing cast can only shrink it
/// — so `MAX(src)` bounds the cast result either way. None otherwise (so an unbounded
/// factor declines the whole product, never over-claims).
pub(super) fn factor_max(func: &VerifiableFunction, op: &Operand) -> Option<i128> {
    match op {
        Operand::Constant(ConstValue::Int(c)) if *c >= 0 => Some(*c),
        Operand::Constant(ConstValue::Uint(c, _)) if *c <= i128::MAX as u128 => Some(*c as i128),
        Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => {
            let Rvalue::Cast(src, _) = crate::unique_whole_local_def(func, p.local)? else {
                return None;
            };
            let ty = crate::operand_ty_cow(func, src)?;
            let w = ty.int_width()?;
            if ty.is_signed() || !ty.is_integer() || w >= 127 {
                return None;
            }
            Some((1i128 << w) - 1)
        }
        _ => None,
    }
}

/// The reduction ELEMENT local underlying a multiply factor `x as A` (the cast source), so
/// the caller can trace it to the loop trip count. None for a constant factor.
pub(super) fn factor_elem_local(func: &VerifiableFunction, op: &Operand) -> Option<usize> {
    let (Operand::Copy(p) | Operand::Move(p)) = op else { return None };
    if !p.projections.is_empty() {
        return None;
    }
    let Rvalue::Cast(Operand::Copy(xp) | Operand::Move(xp), _) =
        crate::unique_whole_local_def(func, p.local)?
    else {
        return None;
    };
    if !xp.projections.is_empty() {
        return None;
    }
    Some(xp.local)
}

/// `(trip count K, per-iteration addend max M)` for a recognized reduction addend, so the
/// accumulator bound is `init + K*M`. Three shapes, all with a structurally-bounded K:
/// (a) a widened element `x as ACC` — `M = MAX(ELEM)`; (b) a PRODUCT
/// `(a[i] as ACC) * (b[i] as ACC)` (or with a constant factor) — `M = factor1_max *
/// factor2_max`; (c) a LEFT-SHIFT `(x as ACC) << k` for a constant `k` — `M = MAX(ELEM) *
/// 2^k`. SOUNDNESS of the product bound: each factor `fi <= mi`, so the true
/// product `<= m1*m2`; and the addend is the overflow-checked product's value, which is an
/// ACC-typed value — if `m1*m2 < 2^ACCwidth` no wrap occurs and the addend equals the true
/// product `<= m1*m2`, while if `m1*m2 >= 2^ACCwidth` any wrapped value is `< 2^ACCwidth
/// <= m1*m2` — so `addend <= m1*m2` holds unconditionally (self-limiting: a product that
/// can overflow leaves `init + K*M >= 2^ACCwidth`, so the accumulator bound does not
/// discharge and the obligation still fails).
pub(super) fn addend_per_iteration_bound(
    func: &VerifiableFunction,
    addend_local: usize,
) -> Option<(i128, i128)> {
    // (a) bare widened element: `t += x as ACC`.
    if let Some(Rvalue::Cast(Operand::Copy(xp) | Operand::Move(xp), _)) =
        crate::unique_whole_local_def(func, addend_local)
        && xp.projections.is_empty()
        && let Some(kb) = for_each_element_fixed_array_bound(func, xp.local)
            .or_else(|| index_range_reduction_bound(func, xp.local))
    {
        return Some(kb);
    }
    // (c) left-shift-scaled element: `t += (x as ACC) << k` (k a non-negative constant). The
    // element is bounded EXACTLY as in case (a) (`MAX(ELEM)` over a fixed array or range), then
    // scaled to `M = MAX(ELEM) * 2^k`. SOUNDNESS: the addend is the ACC-typed value
    // `(x << k) mod 2^ACCwidth`; if `x*2^k < 2^ACCwidth` it equals `x*2^k <= MAX(ELEM)*2^k = M`,
    // and otherwise the wrapped value is `< 2^ACCwidth <= M` — so `addend <= M` unconditionally
    // (self-limiting, exactly the product-addend argument: a shift that can overflow ACC leaves
    // `init + K*M >= 2^ACCwidth`, so the bound does not discharge and the obligation still fails).
    if let Some((base, shift)) = reduction_shl_operands(func, addend_local) {
        let k = operand_const_int(&shift)?;
        if !(0..64).contains(&k) {
            return None;
        }
        let elem = factor_elem_local(func, &base)?;
        let (trip, elem_max) = for_each_element_fixed_array_bound(func, elem)
            .or_else(|| index_range_reduction_bound(func, elem))?;
        let per = elem_max.checked_mul(1i128.checked_shl(k as u32)?)?;
        return Some((trip, per));
    }
    // (b) product addend: `t += f1 * f2`.
    let (f1, f2) = reduction_mul_operands(func, addend_local)?;
    let per = factor_max(func, &f1)?.checked_mul(factor_max(func, &f2)?)?;
    let elem = factor_elem_local(func, &f1).or_else(|| factor_elem_local(func, &f2))?;
    let k = reduction_trip_count(func, elem)?;
    Some((k, per))
}

/// `(MIN(ELEM), MAX(ELEM))` for a bare-widened SIGNED reduction addend `t += x as ACC`,
/// where `x` is a SIGNED narrow integer element (`iN`, `N < 64`) iterated by a for-each over a
/// FIXED-SIZE array `[iN; LEN]`. The signed-only sibling of [`addend_per_iteration_bound`] (which
/// is UNSIGNED-only by construction — `fixed_array_elem_bound`/`index_range_reduction_bound` both
/// reject signed elements because the unsigned path emits only an UPPER bound `acc <= C + K*MAX`,
/// which is unsound when the addend can be negative).
///
/// Returns only the per-ELEMENT range; the TRIP COUNT is supplied by the caller's `K =
/// total_loop_iterations` (the PRODUCT of every loop's trip count — exactly as the unsigned path
/// does), NOT this array's length, so a NESTED loop `for _ in 0..M { for &x in a { acc += x as ACC
/// } }` correctly multiplies by `M*LEN` rather than under-counting at `LEN`. A signed element
/// ranges over the FULL two's-complement interval `[-2^(N-1), 2^(N-1)-1]`, so the accumulator (sum
/// of at most `K` elements, plus the const init) ranges over `[C + K*MIN, C + K*MAX]`. The caller
/// emits BOTH endpoints as linear facts, which ay discharges DIRECTLY (no structural folding): the
/// per-add overflow check `i32::MIN <= acc_old + addend <= i32::MAX` follows by Farkas from the
/// symmetric post-add bounds whenever `C + K*MIN >= i32::MIN` and `C + K*MAX <= i32::MAX` — and is
/// SELF-LIMITING, since a genuinely-overflowing reduction has an endpoint outside the ACC type and
/// the bound then fails to discharge. The for-each-over-fixed-array trace is required only to
/// CONFIRM `x` is a bounded array element (not to source the trip count); the bare widened-element
/// form is the only addend recognized (no product/shift) to keep the symmetric argument simple;
/// `N < 64` keeps `K*range` inside `i128`.
pub(super) fn signed_addend_per_iteration_range(
    func: &VerifiableFunction,
    addend_local: usize,
) -> Option<(i128, i128)> {
    let Rvalue::Cast(Operand::Copy(xp) | Operand::Move(xp), _) =
        crate::unique_whole_local_def(func, addend_local)?
    else {
        return None;
    };
    if !xp.projections.is_empty() {
        return None;
    }
    // verifier-perf: borrow the declared type — only scalar predicates are read.
    let elem_ty = crate::local_ty_ref(func, xp.local)?;
    let width = elem_ty.int_width()?;
    if !elem_ty.is_signed() || !elem_ty.is_integer() || width >= 64 {
        return None;
    }
    // CONFIRM `x` is a for-each element of a fixed-size array (so it is a bounded element); the
    // length is discarded — the trip count comes from the caller's whole-nest `K`.
    let _ = for_each_array_elem_ty(func, xp.local)?;
    let elem_min = -(1i128 << (width - 1));
    let elem_max = (1i128 << (width - 1)) - 1;
    Some((elem_min, elem_max))
}

/// `(start, end)` of the exclusive `Range` a for-loop variable iterates, when both are constants.
/// The loop var `v` is the Some-payload of `Range::next` (`v = (next() as Some).0`); trace it to
/// the originating range aggregate and read its constant bounds. None for a non-range / non-const.
pub(super) fn loop_var_const_range(func: &VerifiableFunction, local: usize) -> Option<(i128, i128)> {
    const FUEL: u32 = 16;
    let opt_local = match crate::unique_whole_local_def(func, local)? {
        Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
            if is_some_payload_projection(&p.projections) =>
        {
            p.local
        }
        _ => return None,
    };
    let (start_op, end_op) = next_call_range_operands(func, opt_local, FUEL)?;
    Some((operand_const_int(start_op)?, operand_const_int(end_op)?))
}

/// The local of a `dst = Use(Copy(tuple.0))` extraction of `tuple_local`'s field 0 — the index
/// `_20` in `_20 = _23.0` for a checked-op result `_23`. None if no such single extraction.
pub(super) fn checked_result_field0_consumer(func: &VerifiableFunction, tuple_local: usize) -> Option<usize> {
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign {
                place,
                rvalue: Rvalue::Use(Operand::Copy(p) | Operand::Move(p)),
                ..
            } = stmt
                && place.projections.is_empty()
                && p.local == tuple_local
                && p.projections.as_slice() == [trust_types::Projection::Field(0)]
            {
                return Some(place.local);
            }
        }
    }
    None
}

/// Global facts for a FLATTENED 2D index `g[y*W + x]` over nested const-range loops
/// (`for y in 0..H { for x in 0..W' { g[y*W + x] } }`). The MIR is a checked-op chain:
/// `_22 = CheckedMul(y, W); _21 = _22.0; _23 = CheckedAdd(_21, x); _20 = _23.0; g[_20]`. With
/// `y ∈ [0, H)` and `x ∈ [0, W')`, `y*W ≤ (H-1)*W` and `y*W + x ≤ (H-1)*W + (W'-1)`. Emit those two
/// upper bounds on the mul result `_21` and the index `_20`: the index bound discharges `g[_20]`
/// (the incompatible-const-bounds discharge: `_20 ≤ (H-1)*W+(W'-1) < g.len()` vs `_20 ≥ len`), and
/// the mul-result bound discharges the Int-form `[overflow:add]` on `_21 + x`. (The BV-encoded
/// `[overflow:mul]` on `y*W` is handled separately by the BV operand-bound render.)
///
/// SOUNDNESS: both bounds are TRUE — `W` is a const, `H`/`W'` are the const range ends, and the
/// loop-var trace (`loop_var_const_range`) yields the EXACT exclusive-range bounds. SELF-LIMITING:
/// an out-of-range grid (`(H-1)*W+(W'-1) ≥ g.len()`) leaves compatible bounds and stays
/// runtime-checked; a non-const dimension / non-loop-var operand yields no fact.
pub(super) fn build_flattened_index_facts(func: &VerifiableFunction) -> Vec<Formula> {
    let mut facts = Vec::new();
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            let Statement::Assign {
                place: add_tuple,
                rvalue: Rvalue::CheckedBinaryOp(BinOp::Add, mul_op, x_op),
                ..
            } = stmt
            else {
                continue;
            };
            if !add_tuple.projections.is_empty() {
                continue;
            }
            let (Operand::Copy(mul_p) | Operand::Move(mul_p)) = mul_op else { continue };
            let (Operand::Copy(x_p) | Operand::Move(x_p)) = x_op else { continue };
            if !mul_p.projections.is_empty() || !x_p.projections.is_empty() {
                continue;
            }
            // mul_p = Use(Copy(mul_tuple.0)); mul_tuple = CheckedMul(y, W_const).
            let Some(Rvalue::Use(Operand::Copy(mt) | Operand::Move(mt))) =
                crate::unique_whole_local_def(func, mul_p.local)
            else {
                continue;
            };
            if mt.projections.as_slice() != [trust_types::Projection::Field(0)] {
                continue;
            }
            let Some(Rvalue::CheckedBinaryOp(BinOp::Mul, y_op, w_op)) =
                crate::unique_whole_local_def(func, mt.local)
            else {
                continue;
            };
            let (Operand::Copy(y_p) | Operand::Move(y_p)) = y_op else { continue };
            if !y_p.projections.is_empty() {
                continue;
            }
            let Some(w) = operand_const_int(w_op).filter(|w| *w > 0) else { continue };
            let (Some((_, y_end)), Some((_, x_end))) =
                (loop_var_const_range(func, y_p.local), loop_var_const_range(func, x_p.local))
            else {
                continue;
            };
            let (Some(mul_bound), Some(idx_bound)) = (
                (y_end - 1).checked_mul(w),
                (y_end - 1).checked_mul(w).and_then(|m| m.checked_add(x_end - 1)),
            ) else {
                continue;
            };
            let Some(idx_local) = checked_result_field0_consumer(func, add_tuple.local) else {
                continue;
            };
            let mul_name =
                crate::place_to_var_name(func, &Place { local: mul_p.local, projections: vec![] });
            let idx_name =
                crate::place_to_var_name(func, &Place { local: idx_local, projections: vec![] });
            facts.push(Formula::Le(
                Box::new(Formula::Var(mul_name, Sort::Int)),
                Box::new(Formula::Int(mul_bound)),
            ));
            facts.push(Formula::Le(
                Box::new(Formula::Var(idx_name, Sort::Int)),
                Box::new(Formula::Int(idx_bound)),
            ));
        }
    }
    facts
}

/// Bounded fixed-array REDUCTION accumulator bound (#50). For
/// `let mut acc = C; for &x in &[ELEM; N] { acc = acc + (x as ACC); }` the loop
/// abstraction otherwise leaves `acc` unbounded, so the per-iteration overflow check
/// `acc + (x as ACC) <= MAX(ACC)` cannot discharge even when it provably cannot
/// overflow. Emit the GLOBAL fact `acc <= C + N * MAX(ELEM)`: at any program point
/// `acc` is `C` plus the sum of at most `N` elements each `<= MAX(ELEM)`, so it holds
/// everywhere (sound to conjoin onto every VC) and is SELF-LIMITING — a
/// genuinely-overflowing reduction (large `N`, or a non-narrowing addend) leaves the
/// obligation SAT and still fails. CONSERVATIVE recognition (each guards soundness):
/// (1) the self-add runs at most `K = total_loop_iterations` times — the PRODUCT of every
/// loop's const trip count, defined only when every loop is a const-bounded `Range`/for-each
/// (so a single loop, a nested matrix loop `K=N*M`, and a counter all qualify, while an
/// unbounded while-loop does not); (2) the addend is `x as ACC` where `x` is bounded by a
/// structurally-bounded per-element max — EITHER the element of a for-each over a FIXED-SIZE
/// array `[ELEM; N]`
/// (`for_each_element_fixed_array_bound`, trip count = the array length), OR a loaded
/// unsigned element `a[i]` whose index `i` is the payload of an exclusive `Range`
/// `[start, end)` driving the loop (`index_range_reduction_bound`, trip count =
/// `end - start`); (3) `acc`'s only definitions are a const init and the self-add (and it
/// is neither call-clobbered nor mutably aliased — see `accumulator_init_const`).
pub(super) fn build_accumulator_bound_facts(func: &VerifiableFunction) -> Vec<Formula> {
    let mut facts = Vec::new();
    // `K` = an upper bound on how many times any self-add executes = the PRODUCT of every
    // loop's trip count (`total_loop_iterations`). None — so no bound — unless EVERY loop is
    // a const-bounded `Range`/for-each iterator, which guarantees `K` cannot under-count the
    // self-add's executions (an unbounded while-loop would, and is excluded). This single gate
    // replaces the former `count_back_edges == 1` check and uniformly handles a single loop, a
    // nested matrix loop (`K = N*M`), and a constant-addend counter.
    let Some(k) = total_loop_iterations(func) else {
        return facts;
    };
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            let Statement::Assign {
                place: ck_dest,
                rvalue: Rvalue::CheckedBinaryOp(BinOp::Add, lhs, rhs),
                ..
            } = stmt
            else {
                continue;
            };
            if !ck_dest.projections.is_empty() {
                continue;
            }
            let (Operand::Copy(acc_p) | Operand::Move(acc_p)) = lhs else { continue };
            if !acc_p.projections.is_empty() {
                continue;
            }
            let acc = acc_p.local;
            // SIGNED reduction `t += x as ACC` over a fixed array of signed `iN` elements: the
            // addend ranges over `[MIN, MAX]` (negative possible), so the unsigned single-upper
            // bound below would be unsound. Emit the SYMMETRIC pair `[init + K*MIN, init + K*MAX]`
            // for both the accumulator and the post-add sum; ay discharges the i-typed add's
            // overflow check (both directions) by Farkas from these linear facts (self-limiting:
            // an endpoint outside ACC leaves the obligation SAT). Handled here so the unsigned
            // match below — which only emits an upper bound — never sees a signed element.
            if let Operand::Copy(rp) | Operand::Move(rp) = rhs
                && rp.projections.is_empty()
                && let Some((smin, smax)) = signed_addend_per_iteration_range(func, rp.local)
                && let Some(init_c) = accumulator_init_const(func, acc, ck_dest.local)
                && let (Some(lo), Some(hi)) = (
                    k.checked_mul(smin).and_then(|nm| init_c.checked_add(nm)),
                    k.checked_mul(smax).and_then(|nm| init_c.checked_add(nm)),
                )
            {
                let acc_name =
                    crate::place_to_var_name(func, &Place { local: acc, projections: vec![] });
                let addend_name =
                    crate::place_to_var_name(func, &Place { local: rp.local, projections: vec![] });
                let acc_var = || Formula::Var(acc_name.clone(), Sort::Int);
                let addend_var = || Formula::Var(addend_name.clone(), Sort::Int);
                // Accumulator range `lo <= acc <= hi`.
                facts.push(Formula::Le(Box::new(acc_var()), Box::new(Formula::Int(hi))));
                facts.push(Formula::Ge(Box::new(acc_var()), Box::new(Formula::Int(lo))));
                // Addend's own element range `smin <= addend <= smax`.
                facts.push(Formula::Le(Box::new(addend_var()), Box::new(Formula::Int(smax))));
                facts.push(Formula::Ge(Box::new(addend_var()), Box::new(Formula::Int(smin))));
                // TIGHT post-add (sum) range `lo <= acc_old + addend <= hi` — exactly the i-typed
                // overflow operand, the sum of at most `K` signed elements plus init.
                let sum = || Formula::Add(Box::new(acc_var()), Box::new(addend_var()));
                facts.push(Formula::Le(Box::new(sum()), Box::new(Formula::Int(hi))));
                facts.push(Formula::Ge(Box::new(sum()), Box::new(Formula::Int(lo))));
                continue;
            }
            // Per-iteration addend max `M`: a NON-NEGATIVE CONSTANT (`t += c`, a counter /
            // conditional count `if cond { t += 1 }`), OR a widened element `x as A` /
            // product `(a[i] as A)*(b[i] as A)` (`addend_per_iteration_bound`'s per-addend
            // max; its own trip count is discarded in favour of the whole-nest `K`).
            let (per_max, addend_local) = match rhs {
                Operand::Constant(ConstValue::Int(c)) if *c >= 0 => (*c, None),
                Operand::Constant(ConstValue::Uint(c, _)) if *c <= i128::MAX as u128 => {
                    (*c as i128, None)
                }
                Operand::Copy(rp) | Operand::Move(rp) if rp.projections.is_empty() => {
                    match addend_per_iteration_bound(func, rp.local) {
                        Some((_, per)) => (per, Some(rp.local)),
                        None => continue,
                    }
                }
                _ => continue,
            };
            let Some(init_c) = accumulator_init_const(func, acc, ck_dest.local) else { continue };
            let Some(bound) = k.checked_mul(per_max).and_then(|nm| init_c.checked_add(nm)) else {
                continue;
            };
            let acc_name =
                crate::place_to_var_name(func, &Place { local: acc, projections: vec![] });
            if std::env::var("TRUST_ACC_DEBUG").is_ok() {
                eprintln!(
                    "TRUST_ACC[{}] acc={} K={} per_max={} init={} -> bound {} <= {}",
                    func.name, acc, k, per_max, init_c, acc_name, bound
                );
            }
            facts.push(Formula::Le(
                Box::new(Formula::Var(acc_name.clone(), Sort::Int)),
                Box::new(Formula::Int(bound)),
            ));
            // Also bound the per-iteration ADDEND itself (`addend <= per_max`). The
            // per-add overflow check is `acc_old + addend <= MAX(ACC)`; the
            // accumulator bound gives `acc_old <= bound` but the check ALSO needs the
            // addend's own bound. The shift lane (`t += (x as ACC) << k`) already
            // supplies it via the shift facts, so it discharged; the bare widened
            // element (`t += x as ACC`) did not, leaving a provably-safe accumulator
            // runtime-checked. `per_max` is exactly that addend's max
            // (`addend_per_iteration_bound`), so emitting it is sound (a true fact)
            // and closes the bare-cast reduction. The constant-addend arm needs no
            // bound (the constant is its own).
            if let Some(addend) = addend_local {
                let addend_name =
                    crate::place_to_var_name(func, &Place { local: addend, projections: vec![] });
                facts.push(Formula::Le(
                    Box::new(Formula::Var(addend_name.clone(), Sort::Int)),
                    Box::new(Formula::Int(per_max)),
                ));
                // TIGHT POST-ADD (sum) bound `acc_old + addend <= bound`. The per-add
                // overflow check is `acc_old + addend <= MAX(ACC)`; `acc <= bound` alone
                // over-approximates `acc_old` by one iteration's worth (so `acc_old +
                // addend <= bound + per_max`), which overshoots MAX by `per_max` when the
                // per-iteration addend is large relative to MAX — e.g. `t += (x as u16)
                // << 4` over `[u8;16]` (`bound=65280`, `per_max=4080` → `<= 69360 >
                // 65535`), leaving the safe shift reduction runtime-checked. But `acc_old
                // + addend` IS the POST-add accumulator value = the sum of at most `K`
                // elements, bounded by the SAME `bound = init + K*per_max <= MAX`. This
                // fact discharges the check directly (and is the only form the structural
                // arithmetic discharge `conjuncts_carry_arith_contradiction` can use,
                // since ay leaves the `<<k` addend's Int/BV round-trip Unknown).
                // SELF-LIMITING: a genuinely-overflowing reduction has `bound > MAX`, so
                // this fact does not prove it.
                facts.push(Formula::Le(
                    Box::new(Formula::Add(
                        Box::new(Formula::Var(acc_name, Sort::Int)),
                        Box::new(Formula::Var(addend_name, Sort::Int)),
                    )),
                    Box::new(Formula::Int(bound)),
                ));
            }
        }
    }
    facts
}

/// Trace an operand to its root whole-local through `Copy`/`Move` and `Use` copies.
pub(super) fn operand_root_local(func: &VerifiableFunction, op: &Operand, fuel: u32) -> Option<usize> {
    if fuel == 0 {
        return None;
    }
    let (Operand::Copy(p) | Operand::Move(p)) = op else { return None };
    if !p.projections.is_empty() {
        return None;
    }
    if let Some(Rvalue::Use(inner)) = crate::unique_whole_local_def(func, p.local) {
        if let Some(root) = operand_root_local(func, inner, fuel - 1) {
            return Some(root);
        }
    }
    Some(p.local)
}

/// The successor a boolean `SwitchInt` takes when the discriminant is TRUE (value
/// 1) — for `_g = Lt(lo, hi)` this is the `lo < hi` (loop-body) edge.
pub(super) fn bool_switch_true_target(targets: &[(u128, BlockId)], otherwise: BlockId) -> Option<BlockId> {
    if let Some((_, t)) = targets.iter().find(|(v, _)| *v == 1) {
        return Some(*t);
    }
    // Only value 0 (false) is listed ⇒ true falls through to `otherwise`.
    if targets.iter().any(|(v, _)| *v == 0) {
        return Some(otherwise);
    }
    None
}

/// Blocks that WRITE `local` (whole-value, field/index store, or call dest).
pub(super) fn local_write_blocks(func: &VerifiableFunction, local: usize) -> FxHashSet<usize> {
    let mut out = FxHashSet::default();
    for block in &func.body.blocks {
        let writes = block
            .stmts
            .iter()
            .any(|s| matches!(s, Statement::Assign { place, .. } if place.local == local))
            || matches!(&block.terminator, Terminator::Call { dest, .. } if dest.local == local);
        if writes {
            out.insert(block.id.0);
        }
    }
    out
}

/// Blocks reachable from `start` without ENTERING any block in `avoid` (those
/// blocks are neither visited nor expanded).
pub(super) fn reachable_avoiding(
    func: &VerifiableFunction,
    start: usize,
    avoid: &FxHashSet<usize>,
) -> FxHashSet<usize> {
    let mut seen = FxHashSet::default();
    let mut stack = vec![start];
    while let Some(b) = stack.pop() {
        if avoid.contains(&b) || b >= func.body.blocks.len() || !seen.insert(b) {
            continue;
        }
        for succ in v2_terminator_targets(&func.body.blocks[b].terminator) {
            stack.push(succ.0);
        }
    }
    seen
}

/// Per-block facts for the CONVERGING two-pointer idiom
///   `let lo = 0; let hi = s.len(); while lo < hi { hi -= 1; … s[lo] …; lo += 1; }`.
///
/// `s[hi]` is already discharged by [`build_downward_induction_facts`] (`hi` is a
/// downward var, so each decrement result `< s.len()`). For `s[lo]`: on the
/// loop-body path the guard gives `lo < hi`, and `hi <= s.len()` (downward
/// invariant), so `lo < s.len()`. This holds for `lo`'s value AT THE GUARD; it stops
/// holding once `lo` is incremented (`lo + 1` may equal `s.len()`). So the fact
/// `lo < s.len()` is emitted ONLY at "lo-stable" blocks — those reachable from the
/// guard's true-edge WITHOUT passing through any block that writes `lo` and WITHOUT
/// re-entering the loop header, AND not reachable at all from a `lo`-write block's
/// successors (so no path delivers a post-increment `lo`). At such blocks `lo`
/// equals its guard value on every path, so `lo < s.len()` is SOUND.
pub(super) fn build_converging_pointer_facts(func: &VerifiableFunction) -> FxHashMap<BlockId, Vec<Formula>> {
    const FUEL: u32 = 16;
    let mut map: FxHashMap<BlockId, Vec<Formula>> = FxHashMap::default();
    let downward = downward_induction_vars(func);
    if downward.is_empty() {
        return map;
    }

    for block in &func.body.blocks {
        let Terminator::SwitchInt { discr, targets, otherwise, .. } = &block.terminator else {
            continue;
        };
        // The guard discriminant must be `_g = Lt(lo, hi)`.
        let Some(g_local) = operand_root_local(func, discr, FUEL) else { continue };
        let Some(Rvalue::BinaryOp(trust_types::BinOp::Lt, a, b)) =
            crate::unique_whole_local_def(func, g_local)
        else {
            continue;
        };
        let (Some(lo), Some(hi)) =
            (operand_root_local(func, a, FUEL), operand_root_local(func, b, FUEL))
        else {
            continue;
        };
        // `hi` (the guard's upper operand) must be a downward induction var.
        let Some(dv) = downward.iter().find(|d| d.local == hi) else { continue };
        let Some(true_target) = bool_switch_true_target(targets, *otherwise) else { continue };
        // Trust (countdown-loop piece, P0 root-cause fix): `local_write_blocks`
        // sees only visible defs — a `bump(&mut lo)` reseat writes `lo` through
        // the borrow WITHOUT a write block, so the "lo-stable blocks" analysis
        // would emit `lo < s.len()` at blocks where the reseated `lo` is
        // arbitrary (confirmed false PROOF: `while lo < hi { hi -= 1;
        // bump(&mut lo); s[lo]; lo += 1; }` proved, panics rc=101). `hi` is
        // covered by the same check inside `downward_induction_vars`.
        if local_mut_escapes(func, lo) {
            continue;
        }

        let header = block.id.0;
        let mut reassign = local_write_blocks(func, lo);
        // The header re-reads `lo` for the next iteration — stop BFS there so the
        // analysis stays within ONE loop body.
        let mut avoid_body = reassign.clone();
        avoid_body.insert(header);
        let stable = reachable_avoiding(func, true_target.0, &avoid_body);

        // Blocks reachable from any lo-write block's successors (within the body,
        // avoiding the header) carry a POST-write `lo` on some path — exclude them.
        let mut tainted: FxHashSet<usize> = FxHashSet::default();
        let mut avoid_header: FxHashSet<usize> = FxHashSet::default();
        avoid_header.insert(header);
        for &w in &reassign {
            if w >= func.body.blocks.len() {
                continue;
            }
            for succ in v2_terminator_targets(&func.body.blocks[w].terminator) {
                tainted.extend(reachable_avoiding(func, succ.0, &avoid_header));
            }
        }
        reassign.insert(header);

        let lo_var = Formula::Var(crate::place_to_var_name(func, &Place::local(lo)), Sort::Int);
        // `lo` is the loop's lower pointer; when it is an UNSIGNED integer it is
        // `>= 0`, which (with the guard `lo < hi`) gives `hi >= 1` and discharges
        // the `hi -= 1` underflow check. A non-param local's usize non-negativity is
        // otherwise not asserted in the Int model.
        let lo_unsigned =
            func.body.locals.get(lo).is_some_and(|d| d.ty.is_integer() && !d.ty.is_signed());
        for b in stable {
            if tainted.contains(&b) || reassign.contains(&b) {
                continue;
            }
            let entry = map.entry(BlockId(b)).or_default();
            entry.push(Formula::Lt(Box::new(lo_var.clone()), Box::new(dv.bound.clone())));
            if lo_unsigned {
                entry.push(Formula::Ge(Box::new(lo_var.clone()), Box::new(Formula::Int(0))));
            }
        }
    }
    map
}

// ======================================================================
// Push-guarded nested-container element-length facts
//   `let mut m: Vec<Vec<T>> = Vec::new();
//    for .. { let row = ..; if row.len() <= n { return }; m.push(row); }
//    for col in 0..n { for r in 0..n { .. m[r][col] .. } }`
// ======================================================================
//
// The inner access `m[r][col]` lowers to `<Vec<T> as Index>::index(m[r], col)`;
// its bounds obligation is `col < len(m[r])`, where `len(m[r])` is recovered by
// `collection_abstract_len_with_base` as the abstract length var of the OUTER
// element read `_e = <Vec<Vec<T>> as Index>::index(&m, r)` — i.e.
// `coll_len(_e)`. That var is
// FREE (no model-level tie between `_e` and m's contents), so the solver refutes
// the bound with `len(m[r]) == 0`. This is the dominant nested-matrix/vector
// FALSE-REFUTE class (ny `exact::solve_system` and friends).
//
// The missing fact is the loop invariant `∀ pushed row: len(row) > n`, which
// holds because m starts EMPTY and every element is a `m.push(row)` DOMINATED by
// a guard `row.len() <= n → return` (so the reached push has `row.len() > n`).
// Since m is push-only, EVERY element of m has length > n, hence any valid
// `m[k]` has `coll_len(m[k]) > n`. We emit exactly that fact — in the SAME
// `coll_len_var` vocabulary the inner bound reads — keyed to the element read's
// dest, so `col < n < coll_len(m[k])` discharges (the `col < n` disjunct is the
// range-yield machinery's job; this only supplies the missing upper term).
//
// SOUNDNESS (a false slice-bounds PROVE is a memory-safety false-proof):
//  * m must be an owned `Vec`, created EMPTY (`Vec::new`/`with_capacity`) with
//    exactly ONE whole-local def, never written through a projection
//    (`m[i]=..`/SetDiscriminant/Deinit), and every `&mut m`/raw-mut borrow must
//    feed ONLY `Vec::push` as receiver — so pop/truncate/clear/remove/insert/
//    extend/swap and any `&mut m` escape FAIL CLOSED (the whole invariant is void
//    if m can shrink or an element be overwritten).
//  * every `Vec::push(&mut m, row)` must be DOMINATED by a guard that proves
//    `len(row) > n` on the push edge (structural decode of the SwitchInt
//    comparison + reachability dominance), the guard's `n` must be STABLE
//    (`place_source_is_stable`), and `row` must NOT be resized between the length
//    snapshot and the push (reachability-scoped to one iteration). If any push is
//    unguarded, or the bounds differ across pushes, emit NOTHING.
//  * the fact is emitted only for an element whose type is itself a `Vec` (the
//    nested case the inner `coll_len` bound reads), keyed to that element's dest,
//    so it never over-claims about a non-element `k` (the separate `k < m.len()`
//    obligation scopes validity) nor about a scalar element.
/// A single-element usize set (reachability `avoid` argument).
pub(super) fn one_block_set(b: usize) -> FxHashSet<usize> {
    let mut s = FxHashSet::default();
    s.insert(b);
    s
}
