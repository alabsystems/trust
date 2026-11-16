// Loop iteration and accumulation bounds: back-edge counting, fixed-array and
// reduction trip counts, per-iteration addend ranges, flattened multi-dimension
// indices, and pointers that converge on a common target. The result is an
// upper bound on what an accumulator can reach, which is what an overflow
// obligation over a loop-carried value needs.

use trust_types::loop_nest::{LoopDriver, LoopNest, NaturalLoop};

use super::*;

/// CFG successors of a terminator (block ids).
pub(super) fn terminator_succs(t: &Terminator) -> Vec<usize> {
    let mut succs = Vec::new();
    for_each_terminator_succ(t, |id| succs.push(id));
    succs
}

/// True if `target` is a CFG successor of `t`.
fn terminator_has_succ(t: &Terminator, target: usize) -> bool {
    let mut found = false;
    for_each_terminator_succ(t, |id| {
        if id == target {
            found = true;
        }
    });
    found
}

/// The sole CFG successor of `t`, or `None` if `t` has zero or more than one successor.
fn terminator_sole_succ(t: &Terminator) -> Option<usize> {
    let mut sole = None;
    let mut multiple = false;
    for_each_terminator_succ(t, |id| {
        if sole.is_some() {
            multiple = true;
        } else {
            sole = Some(id);
        }
    });
    if multiple { None } else { sole }
}

/// Visit each CFG successor of a terminator without allocating a `Vec`.
pub(super) fn for_each_terminator_succ(t: &Terminator, mut f: impl FnMut(usize)) {
    match t {
        Terminator::Goto(b) => f(b.0),
        Terminator::SwitchInt { targets, otherwise, .. } => {
            for (_, b) in targets {
                f(b.0);
            }
            f(otherwise.0);
        }
        Terminator::Assert { target, .. } | Terminator::Drop { target, .. } => f(target.0),
        Terminator::Call { target: Some(b), .. } => f(b.0),
        Terminator::Opaque { targets, .. } => {
            for b in targets {
                f(b.0);
            }
        }
        _ => {}
    }
}

/// The `idx`-th CFG successor of `t` in [`for_each_terminator_succ`] order, or `None`
/// once `idx` is past the last successor. Avoids allocating a `Vec<usize>` per block
/// during iterative DFS walks.
#[inline]
pub(super) fn nth_terminator_succ(t: &Terminator, idx: usize) -> Option<usize> {
    match t {
        Terminator::Goto(b)
        | Terminator::Assert { target: b, .. }
        | Terminator::Drop { target: b, .. }
        | Terminator::Call { target: Some(b), .. } => (idx == 0).then_some(b.0),
        Terminator::SwitchInt { targets, otherwise, .. } => {
            if let Some((_, b)) = targets.get(idx) {
                Some(b.0)
            } else if idx == targets.len() {
                Some(otherwise.0)
            } else {
                None
            }
        }
        Terminator::Opaque { targets, .. } => targets.get(idx).map(|b| b.0),
        _ => None,
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
    super::back_edge_count_for(func)
}

pub(super) fn count_back_edges_uncached(func: &VerifiableFunction) -> usize {
    let blocks = &func.body.blocks;
    if blocks.is_empty()
        || super::cached_terminator_presence_for_body(&func.body)
            .is_some_and(|tp| !tp.has_back_edge)
    {
        return 0;
    }
    if blocks.iter().enumerate().all(|(i, b)| b.id.0 == i) {
        let n = blocks.len();
        // Low 2 bits: 0 = white (unseen), 1 = gray (on stack), 2 = black (finished).
        // Bit 2 (4): already counted as a distinct back-edge header.
        let mut color = vec![0u8; n];
        let mut headers = 0usize;
        let entry = 0usize;
        color[entry] = 1;
        let mut stack: Vec<(usize, usize)> = vec![(entry, 0)];
        while let Some(top) = stack.last_mut() {
            let (u, i) = *top;
            if let Some(v) = nth_terminator_succ(&blocks[u].terminator, i) {
                top.1 += 1;
                let state = color.get(v).copied().unwrap_or(2);
                match state & 3 {
                    0 => {
                        color[v] = 1;
                        stack.push((v, 0));
                    }
                    1 => {
                        if (state & 4) == 0 {
                            color[v] = state | 4;
                            headers += 1;
                        }
                    }
                    _ => {}
                }
            } else {
                color[u] = (color[u] & 4) | 2;
                stack.pop();
            }
        }
        return headers;
    }
    back_edge_latches(func).len()
}

/// The DFS behind [`count_back_edges`], keeping each loop header's back-edge SOURCES
/// (its latches): `header -> [u, …]` for every back edge `u -> header`.
/// [`driver_heads_its_loop`] needs the latches to rebuild the header's natural loop.
fn back_edge_latches(func: &VerifiableFunction) -> FxHashMap<usize, Vec<usize>> {
    let blocks = &func.body.blocks;
    let mut latches: FxHashMap<usize, Vec<usize>> = FxHashMap::default();
    if blocks.is_empty()
        || super::cached_terminator_presence_for_body(&func.body)
            .is_some_and(|tp| !tp.has_back_edge)
    {
        return latches;
    }
    if blocks.iter().enumerate().all(|(i, b)| b.id.0 == i) {
        let n = blocks.len();
        // 0 = white (unseen), 1 = gray (on stack), 2 = black (finished).
        let mut color = vec![0u8; n];
        let entry = 0usize;
        color[entry] = 1;
        let mut stack: Vec<(usize, usize)> = vec![(entry, 0)];
        while let Some(top) = stack.last_mut() {
            let (u, i) = *top;
            if let Some(v) = nth_terminator_succ(&blocks[u].terminator, i) {
                top.1 += 1;
                match color.get(v).copied().unwrap_or(2) {
                    0 => {
                        color[v] = 1;
                        stack.push((v, 0));
                    }
                    1 => {
                        // back edge: v is on the recursion stack
                        latches.entry(v).or_default().push(u);
                    }
                    _ => {} // forward / cross edge
                }
            } else {
                color[u] = 2;
                stack.pop();
            }
        }
        return latches;
    }
    let succ: FxHashMap<usize, Vec<usize>> =
        blocks.iter().map(|b| (b.id.0, terminator_succs(&b.terminator))).collect();
    // 0 = white (unseen), 1 = gray (on stack), 2 = black (finished).
    let mut color: FxHashMap<usize, u8> = blocks.iter().map(|b| (b.id.0, 0u8)).collect();
    let entry = blocks[0].id.0;
    color.insert(entry, 1);
    let mut stack: Vec<(usize, usize)> = vec![(entry, 0)];
    while let Some(top) = stack.last_mut() {
        let (u, i) = *top;
        let edges = succ.get(&u).map(Vec::as_slice).unwrap_or(&[]);
        if i < edges.len() {
            top.1 += 1;
            let v = edges[i];
            match color.get(&v).copied().unwrap_or(2) {
                0 => {
                    color.insert(v, 1);
                    stack.push((v, 0));
                }
                1 => {
                    // back edge: v is on the recursion stack
                    latches.entry(v).or_default().push(u);
                }
                _ => {} // forward / cross edge
            }
        } else {
            color.insert(u, 2);
            stack.pop();
        }
    }
    latches
}

/// Trace an iterator local back to the operand passed to its `into_iter` constructor
/// (`iter = into_iter(arr)`), walking whole-local Ref/Use copies. Returns the
/// `into_iter` ARGUMENT — for `for &x in &[ELEM;N]` this is the array.
pub(super) fn trace_iter_to_into_iter_arg(
    func: &VerifiableFunction,
    local: usize,
    fuel: u32,
) -> Option<Operand> {
    if fuel == 0 || crate::local_defs::is_parameter(func, local) {
        return None;
    }
    // The seam's VALUE resolver first; when it declines, the ORIGIN hop
    // (`iterator_origin_def`), licensed here because the result is the COLLECTION the
    // iterator was built from, read for its element type and static length:
    // `slice::Iter::next` consumes and never reseats, so every element it yields is
    // an element of that collection and it yields at most `len` of them. `len` is
    // therefore an UPPER bound on the trip count through this hop, exact only under
    // the BMC lane's own single-`next`-site fence.
    let def = crate::local_defs::unique_value_def(func, local)
        .or_else(|| iterator_origin_def(func, local));
    if let Some(rvalue) = def {
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
    // The call-destination hop, GATED on the call being the local's only write channel
    // (`iterator_yield::call_dest_hop`). At `-Copt-level=0` the `for`-loop desugar's
    // `into_iter` destination is a compiler temp with one write, so no source program
    // reaches a reseated one here — but the gate is a property of the HOP, not of one
    // opt level: with the identity `into_iter` folded away the loop's receiver copy
    // lands on the user's iterator local directly, and `it = a.into_iter(); it =
    // b.into_iter()` is then exactly the shape the range tracer's witnesses take.
    // The synthetic pin is `call_dest_hop_gate_tests::the_into_iter_arg_hop_is_gated`.
    let (callee, args) = super::iterator_yield::call_dest_hop(func, local)?;
    if args.len() == 1 && callee_is_into_iter(callee) {
        // Trust (2026-09-19): hop THROUGH `v.iter()` when the `into_iter`
        // argument is itself a `<[T]>::iter` result, so `for _ in v.iter()`
        // reaches the same slice `for _ in v` does.
        //
        // `slice::Iter` yields exactly `v.len()` items — the same count
        // `into_iter(v)` gives — so the hop preserves the trip count exactly.
        // That is the property this function's own header already relies on for
        // `slice::Iter::next`: it "consumes and never reseats, so every element
        // it yields is an element of that collection and it yields at most `len`
        // of them".
        //
        // Gated by the same `call_dest_hop` as every other hop here, so a
        // reseated iterator local is refused rather than traced to the first
        // constructor — the `windows_reseat` hazard its sibling in
        // `container_len.rs` records.
        if let Operand::Copy(p) | Operand::Move(p) = &args[0]
            && p.projections.is_empty()
            && let Some((inner_callee, inner_args, inner_key)) =
                super::iterator_yield::call_dest_hop_keyed(func, p.local)
            && inner_args.len() == 1
            // Keyed (SLICE-INHERENT-1): a user `W::<[T], &[T; N]>::iter(a)` is not
            // std's and may yield more than `N` items.
            && super::container_len::callee_is_slice_iter(inner_callee, inner_key)
        {
            return Some(inner_args[0].clone());
        }
        return Some(args[0].clone());
    }
    None
}

/// Find the `Iterator::next` call whose dest is `next_result_local` and trace its
/// receiver to the `into_iter` argument (the iterated collection). The entrance is
/// gated by `iterator_yield::next_call_receiver` — the `next` call must be the Option
/// local's ONLY write channel, so a payload written by two `next` calls in two
/// branches is attributed to neither collection's trip count.
pub(super) fn next_call_to_array_operand(
    func: &VerifiableFunction,
    next_result_local: usize,
    fuel: u32,
) -> Option<Operand> {
    let receiver = super::iterator_yield::next_call_receiver(func, next_result_local)?;
    trace_iter_to_into_iter_arg(func, receiver, fuel)
}

/// The `(ELEM, LEN)` of the FIXED-SIZE array a for-each loop-element local `x` (the
/// `&x`/`x` bound by `for &x in C`) iterates, by tracing the for-each desugar
/// `x = *(next(&mut iter) as Some).0`, `iter = into_iter(C)` back to `C`. Returns the
/// element type and length WITHOUT any signedness/width judgement — callers apply their
/// own (unsigned `fixed_array_elem_bound`, or the signed-aware reduction range). Only a
/// fixed-size array (static `LEN`) qualifies; a slice or other shape yields None.
pub(super) fn for_each_array_elem_ty(
    func: &VerifiableFunction,
    x_local: usize,
) -> Option<(Ty, u64)> {
    for_each_array_source(func, x_local).map(|(elem, len, _)| (elem, len))
}

/// [`for_each_array_elem_ty`] plus the ITERATED OPERAND itself (`C` in
/// `for &x in C`). The BMC refutation lane (`bmc_reduction`) needs it to check
/// that the array is an unconstrained function INPUT — without that check its
/// per-iteration free variables would misdescribe a literal/const array, which
/// would be a FALSE refutation. The bound-fact lane never needs it, so
/// `for_each_array_elem_ty` keeps its two-value shape.
pub(super) fn for_each_array_source(
    func: &VerifiableFunction,
    x_local: usize,
) -> Option<(Ty, u64, Operand)> {
    if crate::local_defs::is_parameter(func, x_local) || !body_has_iterator_next(func) {
        return None;
    }
    const FUEL: u32 = 16;
    // x = *deref_src
    let deref_src = match crate::local_defs::unique_value_def(func, x_local)? {
        Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
            if matches!(p.projections.as_slice(), [trust_types::Projection::Deref])
                && !crate::local_defs::is_parameter(func, p.local) =>
        {
            p.local
        }
        _ => return None,
    };
    // deref_src = some_local.Downcast(_).Field(0)  (the Option Some payload `&ELEM`)
    let some_local = match crate::local_defs::unique_value_def(func, deref_src)? {
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
    match crate::operand_ty_cow(func, &array_op)?.as_ref() {
        Ty::Array { elem, len } => Some(((**elem).clone(), *len, array_op)),
        Ty::Ref { inner, .. } => match inner.as_ref() {
            Ty::Array { elem, len } => Some(((**elem).clone(), *len, array_op)),
            _ => None,
        },
        _ => None,
    }
}

/// Read an operand as a known integer constant.
pub(crate) fn operand_const_int(op: &Operand) -> Option<i128> {
    match op {
        Operand::Constant(ConstValue::Int(c)) => Some(*c),
        Operand::Constant(ConstValue::Uint(c, _)) if *c <= i128::MAX as u128 => Some(*c as i128),
        _ => None,
    }
}

/// An UPPER bound on how many values a traced exclusive `Range` can yield, from
/// constant bounds. `end - start` when both operands are constants — the cardinality
/// of the yield set `[start, end)`, which a `next` before the loop can only shrink
/// (see `iterator_yield::RangeOrigin`). When `start` is not a constant the bound is
/// `end` alone, licensed ONLY for an UNSIGNED element type: `Range<T>` yields
/// strictly monotone, pairwise distinct values, every one `< end` and — for unsigned
/// `T` — `>= 0`, so at most `end` of them exist whatever `start` was. A signed range
/// with a non-constant `start` has no bound this function can state and declines.
///
/// Every consumer needs an UPPER bound (`acc <= init + K * max` is monotone in `K`);
/// the one lane that needs EXACTNESS, `bmc_reduction`, fences that itself with its
/// single-`next`-site requirement and traces the array, not the range.
pub(super) fn range_trip_count_upper_bound(
    func: &VerifiableFunction,
    origin: RangeOrigin<'_>,
) -> Option<i128> {
    // Trust (2026-09-19): a `min`-BOUNDED end, not just a literal one.
    // `for _ in 0..k.min(10) { n += 1 }` left the accumulator lane with no trip
    // count at all — measured, `TRUST_ACC_DEBUG=1` prints nothing — while the
    // literal `0..10` twin proves. `bound_operand_upper_bound` is the same
    // `min(a, c) <= c` recogniser the manual-counter path already uses; reuse it
    // rather than mint a second one.
    //
    // SOUND BY THIS FUNCTION'S OWN CONTRACT. It returns an UPPER bound on the
    // iteration count, and `min(a, c) <= c` makes `c` one. Its consumer,
    // `build_accumulator_bound_facts`, emits `acc <= init + K * per_max`, so a
    // LARGER K yields a LARGER — weaker — bound. Over-approximating K can
    // therefore only lose completeness, never license a value the accumulation
    // does not reach. (`max` is deliberately absent from that recogniser for the
    // mirror-image reason: it is a LOWER bound.)
    //
    // The bound stays SELF-LIMITING, which the guard rail
    // `loop_accumulator_correct_refusal_bounded_addend_really_overflows.rs`
    // exists to hold: `while i < 100 { c += 3 }` on `u8` still emits `c <= 300`
    // and is still correctly refused. Nothing here clamps to the type range.
    let end = operand_const_int(origin.end)
        .or_else(|| bound_operand_upper_bound(func, origin.end))
        .or_else(|| slice_len_end_upper_bound(func, origin.end, 4))?;
    match operand_const_int(origin.start) {
        Some(start) => end.checked_sub(start),
        None => {
            let ty = crate::operand_ty_cow(func, origin.end)?;
            (ty.is_integer() && !ty.is_signed()).then_some(end)
        }
    }
}

/// Trust (2026-09-30): an upper bound on a range END whose one value is the LENGTH of
/// a slice (or `str`) with a provably non-zero-sized element: `isize::MAX`, the same
/// bound and the same predicate the slice-iterator arm of the trip count uses
/// (`ty_is_definitely_nonzero_sized`; a ZST slice can reach `usize::MAX` and returns
/// None). Only a VALUE bound is claimed, never a name, so a later reseat of the slice
/// is irrelevant; `unique_value_def` guarantees the end has no other value. Sweep
/// `q18`: `for i in (0..v.len()).step_by(2) { if v[i] == 0 { c += 1 } }` over
/// `v: &[u8]` had no trip count, and `c += 1` was refuted at `usize::MAX`.
fn slice_len_end_upper_bound(func: &VerifiableFunction, end: &Operand, fuel: u32) -> Option<i128> {
    if fuel == 0 {
        return None;
    }
    let (Operand::Copy(p) | Operand::Move(p)) = end else { return None };
    if !p.projections.is_empty() || crate::local_defs::is_parameter(func, p.local) {
        return None;
    }
    // Only a REFERENCE: a raw `*const [T]`'s length is unconstrained metadata
    // (`ptr::slice_from_raw_parts(p, usize::MAX)` is safe), and a bare `[T]` place
    // says nothing about which pointer it was read through.
    let nonzst_slice = |ty: &Ty| -> bool {
        let Ty::Ref { inner, .. } = ty else { return false };
        match inner.as_ref() {
            Ty::Slice { elem } => trust_types::alloc_model::ty_is_definitely_nonzero_sized(elem),
            Ty::Str => true,
            _ => false,
        }
    };
    match crate::local_defs::unique_value_def(func, p.local)? {
        Rvalue::UnaryOp(trust_types::UnOp::PtrMetadata, inner)
            if matches!(
                crate::ptr_metadata_model(func, inner),
                crate::PtrMetadataModel::Length(_)
            ) && crate::operand_ty_cow(func, inner).is_some_and(|ty| nonzst_slice(&ty)) =>
        {
            Some(i64::MAX as i128)
        }
        Rvalue::Use(inner) => slice_len_end_upper_bound(func, inner, fuel - 1),
        _ => None,
    }
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
///
/// This is the RAW recognizer: it counts only definitions `body.blocks` carries, so a
/// PARAMETER accumulator's implicit entry definition is NOT charged here. Every lane that
/// ASSERTS the derived bound must call [`accumulator_bound_init_const`] instead; this one
/// is for the BMC refutation lane, which only needs a value `acc` can hold at loop entry.
/// True when `rvalue` reads the RESULT field of the checked-arithmetic temp
/// `ck_dest` back into a local — the statement that makes an `Add` a SELF-add.
///
/// Accepts the direct `x = ck.0` AND the ONE-HOP `x = t` where `t`'s only value
/// is `ck.0`. The hop is not cosmetic: measured 2026-09-18, `-Ztrust-dump=mir`
/// on `while i < 3 { c += 1; i += 1; }` emits
/// `bb5: _3 = _6.0; _4 = _7.0; _1 = _3; _2 = _4;` — every read-back goes through
/// a temp, so the direct-only matcher recognized NEITHER the accumulator nor the
/// counter and the whole bound mechanism was silent on that program.
///
/// SOUNDNESS rests entirely on [`crate::local_defs::unique_value_def`], which is
/// the audited resolver for "this local's value IS that rvalue": it answers
/// `None` for a `Call` destination, a `SetDiscriminant`/`Deinit`/`Drop`, a
/// projected store, an unlocatable pointer write and a mutable-or-raw alias,
/// with no exception — the three channels its doc records as live kernel-
/// certified false proofs. With a unique value definition there is no other
/// value `t` could hold, so `x = t` and `x = ck.0` denote the same value.
pub(super) fn reads_back_checked_result(
    func: &VerifiableFunction,
    rvalue: &Rvalue,
    ck_dest: usize,
) -> bool {
    let Rvalue::Use(Operand::Copy(p) | Operand::Move(p)) = rvalue else { return false };
    let is_field0 = |q: &Place| {
        q.local == ck_dest
            && matches!(q.projections.as_slice(), [trust_types::Projection::Field(0)])
    };
    if is_field0(p) {
        return true;
    }
    if !p.projections.is_empty() || crate::local_defs::is_parameter(func, p.local) {
        return false;
    }
    matches!(
        crate::local_defs::unique_value_def(func, p.local),
        Some(Rvalue::Use(Operand::Copy(q) | Operand::Move(q))) if is_field0(q)
    )
}

pub(super) fn accumulator_init_const(
    func: &VerifiableFunction,
    acc: usize,
    ck_dest: usize,
) -> Option<i128> {
    let mut init: Option<i128> = None;
    let mut saw_self_add = false;
    let mut def_count = 0usize;
    let invalid =
        crate::any_local_write_candidate(func, &func.body.blocks, acc, |block, item| match item {
            Some(stmt) => {
                let Statement::Assign { place, rvalue, .. } = stmt else { return false };
                if let Rvalue::Ref { mutable: true, place: aliased } | Rvalue::AddressOf(_, aliased) =
                    rvalue
                    && aliased.local == acc
                {
                    return true;
                }
                if place.local != acc || !place.projections.is_empty() {
                    return false;
                }
                def_count += 1;
                if def_count > 2 {
                    return true;
                }
                match rvalue {
                    Rvalue::Use(Operand::Constant(ConstValue::Int(c))) if *c >= 0 => {
                        init = Some(*c);
                        false
                    }
                    Rvalue::Use(Operand::Constant(ConstValue::Uint(c, _)))
                        if *c <= i128::MAX as u128 =>
                    {
                        init = Some(*c as i128);
                        false
                    }
                    _ if reads_back_checked_result(func, rvalue, ck_dest) => {
                        saw_self_add = true;
                        false
                    }
                    _ => true,
                }
            }
            None => {
                matches!(
                    &block.terminator,
                    Terminator::Call { dest, .. }
                        if dest.local == acc && dest.projections.is_empty()
                )
            }
        });
    if !invalid && def_count == 2 && saw_self_add { init } else { None }
}

/// [`accumulator_init_const`] for the BOUND lanes — the same recognition PLUS the
/// accumulator's implicit ENTRY definition when `acc` is a PARAMETER.
///
/// A parameter is defined at entry, implicitly, and `body.blocks` never carries that
/// definition, so the statement scan in `accumulator_init_const` cannot see it. A by-value
/// `mut t: u64` parameter with a CONDITIONAL const init and a self-add therefore scores
/// `def_count == 2` and is admitted, while `t` actually holds THREE values: the caller's
/// argument, the `t = 0` store, and the self-add result. On the path that skips the store
/// the caller's value survives into the loop, so the emitted fact `acc <= C + K*M` is FALSE
/// — its path condition goes UNSAT and every obligation on it discharges AND kernel-certifies.
///
/// MEASURED on the toolchain built from `1d457f875e` (whose `loop_bounds.rs` is
/// byte-identical to `442cb527e7`'s), `-Ztrust-policy=certify`:
///
/// ```text
/// pub fn u64_acc_param(mut t: u64, a: &[u8;64], c: bool) -> u64 {
///     if c { t = 0; } for &x in a { t += x as u64; } t }
///
/// note: Trust verification: 2 proved, 0 failed, 0 unknown, 0 timed out,
///       0 runtime-checked out of 2 obligation(s)
///     = note: of which 2 kernel-certified by the clean CIC kernel
///
/// TRUST_ACC[u64_acc_param] acc=1 K=64 per_max=255 init=0 -> bound t <= 16320
/// TRUST_ACC[u64_acc]       acc=2 K=64 per_max=255 init=0 -> bound t <= 16320
/// ```
///
/// `u64_acc_param` has `arg_count == 3`, so its accumulator `_1` IS a parameter and
/// `t <= 16320` is false — a stock-rustc oracle (`-C overflow-checks=on`, at `-O` and
/// without) panics on 5 of 48 inputs sweeping `t` x array-fill x `c`. The control `u64_acc`
/// has `arg_count == 1`, so its `_2` is an ordinary local, the same bound is TRUE, and it
/// still proves. That difference is the whole discriminator.
///
/// WHY A WRAPPER rather than a tightening of `accumulator_init_const` itself: the two
/// consumers need opposite things. A BOUND lane ASSERTS `acc <= C + K*M` on every reaching
/// path, so an unaccounted entry value makes it unsound. The BMC lane
/// (`bmc_reduction::recognize_bounded_reduction`) REFUTES — it exhibits one input on which
/// the obligation fails — and `init` there is a value the accumulator demonstrably CAN hold
/// at loop entry, which stays true for a parameter. Tightening the shared recognizer would
/// have cost that lane refutations it is entitled to; the raw recognizer is therefore left
/// exactly as it was, and only the three bound sites move to this wrapper.
pub(super) fn accumulator_bound_init_const(
    func: &VerifiableFunction,
    acc: usize,
    ck_dest: usize,
) -> Option<i128> {
    // Locals `1..=arg_count` are the parameters (local 0 is the return place).
    if acc > 0 && acc <= func.body.arg_count {
        return None;
    }
    accumulator_init_const(func, acc, ck_dest)
}

fn for_each_block_succ(blocks: &[trust_types::BasicBlock], id: usize, f: impl FnMut(usize)) {
    if let Some(blk) = blocks
        .get(id)
        .filter(|b| b.id.0 == id)
        .or_else(|| blocks.iter().find(|b| b.id.0 == id))
    {
        for_each_terminator_succ(&blk.terminator, f);
    }
}

/// True if block `start` lies on a CYCLE — its own successors can reach it again
/// (`start -> … -> start`). A loop DRIVER (`Iterator::next` called every iteration)
/// sits on its loop's cycle; a STRAY `next()` consumed once before/after a loop does
/// not. Forward reachability over `terminator_succs` (the same successor relation
/// `count_back_edges` walks), bounded by the visited set.
pub(super) fn block_is_on_cycle(func: &VerifiableFunction, start: usize) -> bool {
    let blocks = &func.body.blocks;
    if blocks.is_empty()
        || super::cached_terminator_presence_for_body(&func.body)
            .is_some_and(|tp| !tp.has_back_edge)
    {
        return false;
    }
    if blocks.iter().enumerate().all(|(i, b)| b.id.0 == i) {
        let n = blocks.len();
        if start >= n {
            return false;
        }
        let mut seen = vec![false; n];
        let mut stack: Vec<usize> = Vec::new();
        let mut direct_self = false;
        for_each_terminator_succ(&blocks[start].terminator, |s| {
            if s == start {
                direct_self = true;
            } else if s < n && !seen[s] {
                seen[s] = true;
                stack.push(s);
            }
        });
        if direct_self {
            return true;
        }
        while let Some(b) = stack.pop() {
            let mut hit = false;
            for_each_terminator_succ(&blocks[b].terminator, |s| {
                if s == start {
                    hit = true;
                } else if s < n && !seen[s] {
                    seen[s] = true;
                    stack.push(s);
                }
            });
            if hit {
                return true;
            }
        }
        return false;
    }
    let mut stack: Vec<usize> = Vec::new();
    for_each_block_succ(blocks, start, |s| stack.push(s));
    let mut seen: FxHashSet<usize> = FxHashSet::default();
    while let Some(b) = stack.pop() {
        if b == start {
            return true;
        }
        if seen.insert(b) {
            for_each_block_succ(blocks, b, |s| stack.push(s));
        }
    }
    false
}

/// The PRODUCT of the trip counts of every `next`-driven loop in the function, when
/// every loop is one — the bounded-reduction REFUTATION lane's trip count
/// (`bmc_reduction`), which fences it to exactly one loop over a fixed array itself.
///
/// NOT A BOUND ON ANY BLOCK. Until 2026-09-29 the accumulator lanes read this as the
/// number of times a self-add can run, and five ordinary programs that overflow were
/// proved: an iterator rebuilt inside its own loop, a cycle that skips `next`, an add on
/// the `None` arm, an empty SIBLING loop making the product 0, and an add before a
/// counter test. The proving side now asks [`block_execution_bound`], and
/// `trust_types::loop_nest` states the argument.
///
/// Trust (merge 2026-10-14): upstream hardened this product independently
/// (TRIP-DRIVER-1, TRIP-ZERO-PRODUCT-1, TRIP-MID-TEST-1, and the manual-counter
/// fallback); that code is kept, so the refutation lane reads the stricter count:
///
/// An upper bound `K` on how many times any one self-add of the function executes, the
/// number every consumer multiplies by a per-iteration addend bound (`acc <= init +
/// K*M`). It is the PRODUCT, over every loop, of `max(1, tc)`, where `tc` is that loop's
/// trip count. Each loop must be a const-bounded iterator — an exclusive `Range::next`
/// `[start, end)` (`tc = end - start`) or a for-each `into_iter` over a fixed array
/// `[ELEM; N]` (`tc = N`) — found by tracing its `Iterator::next` call. Handles a SINGLE
/// loop (product over one factor), NESTED loops (`for i { for j { t += a[i][j] } }` —
/// `K = N*M`), and a CONSTANT-addend reduction where there is no addend element to trace
/// `K` from. With no `next`-driven loop at all, [`manual_counter_trip_count`] answers.
///
/// SOUNDNESS — never UNDER-counts (which would make `t <= init + K*M` a false bound):
///
///   * EVERY loop (every distinct back-edge header, `count_back_edges`) has a DRIVER
///     whose trip count is known, and a loop's factor is the smallest among its own
///     drivers (TRIP-DRIVER-1). A `next()` call drives the natural loop `L` it sits in
///     only when `L` EXITS on its `None` and CONTINUES on its `Some` — the switch on
///     its result's discriminant decides it — and its iterator is BUILT outside `L`
///     ([`loop_driven_by`]). Then every pass of `L` consumes one item of an iterator
///     that only `next` advances (the tracers' own `iter_mut_borrows_only_feed_next`
///     gate), so `L` passes at most `tc` times per entry. A while-loop or a non-const
///     range has no driver with a known count ⇒ None ⇒ no bound. The former rule
///     (#on-cycle-`next` == #loops) counted a `let _ = r.next();` that never exits
///     its loop, and balanced a manual `while` with a second `next` in another loop.
///   * Every FACTOR is at least 1 (TRIP-ZERO-PRODUCT-1). A self-add sits in one loop
///     nest (`accumulator_init_const`'s single-self-add gate), and it runs at most the
///     product of the trip counts of the loops that CONTAIN it — or once, outside every
///     loop. The product over ALL loops bounds that only when no factor is smaller than
///     1: a zero-trip loop (`for _ in 0..WARMUP {}` with `WARMUP == 0`, `for _ in e` over
///     a `&[T; 0]`, an empty inner loop) made the whole product 0 while the other loop
///     still added 300 times, and the kernel certified overflow and bounds rows under
///     the false fact `c <= init`. A loop that runs zero times contributes the factor 1,
///     which is what the manual-counter lane's `k.max(1)` already did.
///   * A driver that is not its loop's header runs AFTER part of each pass
///     (TRIP-MID-TEST-1). In `loop { c += 1; if it.next().is_none() { break; } }` the
///     add runs once more than `next()` returns `Some`, so `tc` under-counts it. A
///     driver whose natural loop is entered only through it (a `for`/`while let`
///     header, [`driver_heads_its_loop`]) is exempt; any other driver is refused when
///     an on-cycle checked add is reachable before it ([`driver_follows_a_loop_add`]).
///     The driver's own call block and the block its call returns to run on the
///     `None` pass as well, header or not, so a checked add in either refuses the
///     driver too (2026-10-05).
pub(super) fn total_loop_iterations(func: &VerifiableFunction) -> Option<i128> {
    if !super::terminator_presence_for(func).has_iterator_next_call {
        return manual_counter_trip_count(func);
    }
    // The CANDIDATE drivers are the `Iterator::next` calls whose call block lies on a
    // CYCLE (the loop body branches back through it every iteration). A STRAY `next()`
    // consumed once OUTSIDE any loop (`let _ = it.next();` before a `while`) is NOT on
    // a cycle, so excluding it stops it from balancing a manual while-loop's back-edge
    // count: otherwise `#next == #back_edges` held (1 == 1) and the stray range's trip
    // count `K` became the while-loop's accumulator bound, falsely discharging an
    // out-of-bounds index (SOUNDNESS, hunt-11). Excluding (vs failing) is the looser
    // sound choice — a real for-each loop alongside a stray next still proves via the
    // genuine on-cycle driver. An on-cycle candidate is a driver only under
    // [`loop_driven_by`] (TRIP-DRIVER-1, below).
    let candidates: Vec<usize> = func
        .body
        .blocks
        .iter()
        .filter_map(|b| match &b.terminator {
            Terminator::Call { func: callee, dest, .. }
                if dest.projections.is_empty()
                    && callee_is_iterator_next(callee)
                    && block_is_on_cycle(func, b.id.0) =>
            {
                Some(b.id.0)
            }
            _ => None,
        })
        .collect();
    if candidates.is_empty() {
        // No `Iterator::next` drives ANY loop here. A hand-written counter loop
        // still has a recoverable trip count, and without this the whole
        // accumulator-bound mechanism is silent on every `while` loop — see
        // [`manual_counter_trip_count`] for the measurement and the gates.
        return manual_counter_trip_count(func);
    }
    // Trust (2026-10-04, TRIP-DRIVER-1): a `next()` call on a cycle is not, by being
    // there, the loop's DRIVER. It drives the loop `L` only when `L` exits on its
    // `None` and continues on its `Some`, and when its iterator is built outside `L`
    // ([`loop_driven_by`]). Each loop takes the smallest trip count among its own
    // drivers, and a loop with none — `let _ = r.next();` inside a `loop` that exits on
    // something else, a manual `while` balanced by a second `next` in ANOTHER loop —
    // gives no bound at all. The former identity (#on-cycle-`next` == #loops) let both
    // shapes through.
    let loops = natural_loops(func);
    let mut factors: FxHashMap<usize, i128> = FxHashMap::default();
    for call_block in candidates {
        let Some((header, dest)) = loop_driven_by(func, call_block, &loops) else { continue };
        // Trust (2026-10-04, TRIP-MID-TEST-1): a driver with an on-cycle add before it
        // lets that add run once more than the driver yields — refuse rather than add
        // a `+1` per such loop, which no consumer has asked for.
        if driver_follows_a_loop_add(func, call_block, &loops) {
            return None;
        }
        let Some(tc) = driver_trip_count(func, dest) else { continue };
        factors.entry(header).and_modify(|f| *f = (*f).min(tc)).or_insert(tc);
    }
    if loops.is_empty() || loops.iter().any(|l| !factors.contains_key(&l.header)) {
        return None;
    }
    let mut k: i128 = 1;
    for tc in factors.into_values() {
        // Trust (2026-10-04, TRIP-ZERO-PRODUCT-1): a zero-trip loop is the factor 1,
        // never 0 — see the doc above.
        k = k.checked_mul(tc.max(1))?;
    }
    Some(k)
}

/// The trip count of the loop `next`-driver whose result is `dest`: the range length
/// (`range_trip_count_upper_bound`) or the iterated array's length, `isize::MAX` for a
/// slice of a provably non-ZST element; `None` when neither traces, or when the count
/// is negative.
fn driver_trip_count(func: &VerifiableFunction, dest: usize) -> Option<i128> {
    const FUEL: u32 = 16;
    let tc = if let Some(origin) = next_call_range_operands(func, dest, FUEL) {
        range_trip_count_upper_bound(func, origin)?
    } else {
        let arr = next_call_to_array_operand(func, dest, FUEL)?;
        // Trust (2026-09-19): a SLICE source yields `isize::MAX`, not None.
        //
        // `for _ in v.iter() { n += 1 }` had no trip count, so a `usize`
        // counter over a slice was refuted as an unbounded overflow. A
        // slice's length is symbolic, but it has a CONSTANT upper bound
        // whenever its element is provably non-ZST, and both that bound and
        // its ZST exception are ALREADY in this crate's model — see
        // `conjoin_slice_len_bounds`/`nonzst_slice_len_vars`
        // (`type_ranges.rs:915`), whose comment states the rule: "`size_of::<T>()
        // >= 1` forces `len <= isize::MAX`; a ZST container can reach
        // `usize::MAX`, so unknown/ZST elements keep only the lower bound."
        //
        // So this introduces NO new premise and NO new gate. It reuses that
        // lane's own predicate (`ty_is_definitely_non_zst`) and its own
        // constant, rather than minting a second pair that could drift.
        //
        // SOUND, and fail-closed on the exception. The iteration count of a
        // slice iterator IS its length, so `isize::MAX` is a valid UPPER
        // bound; the consumer emits `acc <= init + K * per_max`, where a
        // larger K gives a larger — weaker — bound. A ZST element returns
        // None and keeps its refusal, which is CORRECT rather than
        // incomplete: `[(); usize::MAX]` is a valid slice and a `usize`
        // counter over it genuinely DOES overflow on the last increment.
        match crate::operand_ty_cow(func, &arr)?.as_ref() {
            Ty::Array { len, .. } => *len as i128,
            Ty::Slice { elem }
                if super::type_ranges::slice_elem_is_definitely_non_zst(func, elem) =>
            {
                i64::MAX as i128
            }
            Ty::Ref { inner, .. } => match inner.as_ref() {
                Ty::Array { len, .. } => *len as i128,
                Ty::Slice { elem }
                    if super::type_ranges::slice_elem_is_definitely_non_zst(func, elem) =>
                {
                    i64::MAX as i128
                }
                _ => return None,
            },
            _ => return None,
        }
    };
    (tc >= 0).then_some(tc)
}

/// The two operands of a multiply that produces the reduction addend — either a direct
/// `Mul(l, r)` rvalue or the `Field(0)` of a `CheckedMul(l, r)` (the overflow-checked
/// product the `+=` reads). None for any other shape.
pub(super) fn reduction_mul_operands(
    func: &VerifiableFunction,
    addend_local: usize,
) -> Option<(Operand, Operand)> {
    if crate::local_defs::is_parameter(func, addend_local) {
        return None;
    }
    match crate::local_defs::unique_value_def(func, addend_local)? {
        Rvalue::CheckedBinaryOp(BinOp::Mul, l, r) | Rvalue::BinaryOp(BinOp::Mul, l, r) => {
            Some((l.clone(), r.clone()))
        }
        Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
            if matches!(p.projections.as_slice(), [trust_types::Projection::Field(0)])
                && !crate::local_defs::is_parameter(func, p.local) =>
        {
            match crate::local_defs::unique_value_def(func, p.local)? {
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
    if crate::local_defs::is_parameter(func, addend_local) {
        return None;
    }
    match crate::local_defs::unique_value_def(func, addend_local)? {
        Rvalue::CheckedBinaryOp(BinOp::Shl, l, r) | Rvalue::BinaryOp(BinOp::Shl, l, r) => {
            Some((l.clone(), r.clone()))
        }
        Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
            if matches!(p.projections.as_slice(), [trust_types::Projection::Field(0)])
                && !crate::local_defs::is_parameter(func, p.local) =>
        {
            match crate::local_defs::unique_value_def(func, p.local)? {
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
        Operand::Copy(p) | Operand::Move(p)
            if p.projections.is_empty() && !crate::local_defs::is_parameter(func, p.local) =>
        {
            let Rvalue::Cast(src, _) = crate::local_defs::unique_value_def(func, p.local)? else {
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

/// The per-iteration max `M` of a recognized reduction addend, so the accumulator bound
/// is `init + K*M` for the `K` the caller takes from `block_execution_bound`. Three
/// shapes: (a) a widened element `x as ACC` — `M = MAX(ELEM)`; (b) a PRODUCT
/// `(a[i] as ACC) * (b[i] as ACC)` (or with a constant factor) — `M = factor1_max *
/// factor2_max`; (c) a LEFT-SHIFT `(x as ACC) << k` for a constant `k` — `M = MAX(ELEM) *
/// 2^k`. Every `MAX(ELEM)` is [`factor_max`]'s: the cast SOURCE's own unsigned type
/// bounds it, whatever the source is. SOUNDNESS of the product bound: each factor
/// `fi <= mi`, so the true product `<= m1*m2`; and the addend is the overflow-checked
/// product's value, which is an ACC-typed value — if `m1*m2 < 2^ACCwidth` no wrap occurs
/// and the addend equals the true product `<= m1*m2`, while if `m1*m2 >= 2^ACCwidth` any
/// wrapped value is `< 2^ACCwidth <= m1*m2` — so `addend <= m1*m2` holds unconditionally
/// (self-limiting: a product that can overflow leaves `init + K*M >= 2^ACCwidth`, so the
/// accumulator bound does not discharge and the obligation still fails).
///
/// Trust (2026-09-29): this used to return `(K, M)` and to require the ELEMENT to be
/// traced to a for-each over a fixed-size array or to a load indexed by a constant
/// `Range`'s yield, only to compute a `K` both callers discarded for
/// `block_execution_bound`'s. The trace gated nothing `M` needs — it returned the same
/// `MAX(ELEM)` the type does — and it refused every other element source: `for &b in
/// a.iter()` over a `&[u8; 4]` (the element is reached through an unsize cast and
/// `slice::iter`), `for b in a` over a `[u8; 4]` by value (no `Deref` in the binding),
/// and `for &x in v.iter().take(3)`, all measured refuted with `s = u32::MAX` on the
/// 659-program ordinary-Rust sweep while `K` was already bounded.
pub(super) fn addend_per_iteration_bound(
    func: &VerifiableFunction,
    addend_local: usize,
) -> Option<i128> {
    let addend = Operand::Copy(Place::local(addend_local));
    // (d) a remainder by a positive constant, possibly through an integer cast:
    // `t += (n % c) as ACC` (ordsweep2 numeric/c03 digit_sum). For an UNSIGNED `n`
    // and a constant `c >= 1`, `n % c` is in `[0, c - 1]` on every execution, and a
    // cast to an integer type that holds `c - 1` keeps that value. Asked BEFORE (a):
    // (a) also matches the cast and answers the source type's maximum, true but no
    // bound at all for `(n % 10) as u8` over a `u64`.
    if let Some(per) = unsigned_const_rem_max(func, addend_local) {
        return Some(per);
    }
    // (a) bare widened element: `t += x as ACC`.
    if let Some(per) = factor_max(func, &addend) {
        return Some(per);
    }
    // (c) left-shift-scaled element: `t += (x as ACC) << k` (k a non-negative constant). The
    // element is bounded EXACTLY as in case (a), then scaled to `M = MAX(ELEM) * 2^k`.
    // SOUNDNESS: the addend is the ACC-typed value `(x << k) mod 2^ACCwidth`; if
    // `x*2^k < 2^ACCwidth` it equals `x*2^k <= MAX(ELEM)*2^k = M`, and otherwise the wrapped
    // value is `< 2^ACCwidth <= M` — so `addend <= M` unconditionally (self-limiting, exactly
    // the product-addend argument: a shift that can overflow ACC leaves `init + K*M >=
    // 2^ACCwidth`, so the bound does not discharge and the obligation still fails).
    if let Some((base, shift)) = reduction_shl_operands(func, addend_local) {
        let k = operand_const_int(&shift)?;
        if !(0..64).contains(&k) {
            return None;
        }
        return factor_max(func, &base)?.checked_mul(1i128.checked_shl(k as u32)?);
    }
    // (b) product addend: `t += f1 * f2`.
    let (f1, f2) = reduction_mul_operands(func, addend_local)?;
    factor_max(func, &f1)?.checked_mul(factor_max(func, &f2)?)
}

/// `c - 1` when `local`'s single definition is `n % c`, or an integer cast of a
/// single-assignment `n % c`, with `n` an unsigned integer and `c` a constant
/// `>= 1` that the cast's target holds (see [`addend_per_iteration_bound`] (d)).
fn unsigned_const_rem_max(func: &VerifiableFunction, local: usize) -> Option<i128> {
    if crate::local_defs::is_parameter(func, local) {
        return None;
    }
    let rem_local = match crate::local_defs::unique_value_def(func, local)? {
        Rvalue::Cast(Operand::Copy(src) | Operand::Move(src), target)
            if src.projections.is_empty() && !crate::local_defs::is_parameter(func, src.local) =>
        {
            let width = target.int_width()?;
            if !target.is_integer() {
                return None;
            }
            Some((src.local, Some((width, target.is_signed()))))
        }
        Rvalue::BinaryOp(BinOp::Rem, ..) => Some((local, None)),
        _ => None,
    }?;
    let (rem_local, cast) = rem_local;
    let Rvalue::BinaryOp(BinOp::Rem, Operand::Copy(n) | Operand::Move(n), divisor) =
        crate::local_defs::unique_value_def(func, rem_local)?
    else {
        return None;
    };
    let n_ty = crate::local_ty_ref(func, n.local)?;
    if !n.projections.is_empty() || !n_ty.is_integer() || n_ty.is_signed() {
        return None;
    }
    let c = operand_const_int(divisor).filter(|c| *c >= 1)?;
    let max = c - 1;
    if let Some((width, signed)) = cast {
        let holds = if signed {
            width >= 2 && max <= (1i128 << (width.min(127) - 1)) - 1
        } else {
            width >= 1 && (width >= 127 || max <= (1i128 << width) - 1)
        };
        if !holds {
            return None;
        }
    }
    Some(max)
}

/// `(MIN(ELEM), MAX(ELEM))` for a bare-widened SIGNED reduction addend `t += x as ACC`,
/// where `x` is a SIGNED narrow integer element (`iN`, `N < 64`) iterated by a for-each over a
/// FIXED-SIZE array `[iN; LEN]`, and `ACC` is a SIGNED integer type that holds every `iN` value
/// (`is_modeled_identity_cast(iN, ACC)`: `iN` itself or a wider `iM`), so the addend EQUALS the
/// element and `[MIN(ELEM), MAX(ELEM)]` is its range.
///
/// The cast TARGET is load-bearing (CAST-SIGNED-REDUCTION-TARGET-1). An UNSIGNED target maps a
/// negative element to a huge addend (`-1i8 as u32 == 4294967295`), so `[MIN, MAX]` of the
/// element is FALSE for the addend, and the caller's symmetric facts `acc <= init + K*MAX` and
/// `acc + addend <= init + K*MAX` then discharged a real overflow: `t: u32 += *x as u32` over
/// `[i8; 4]` was kernel-certified and panics on `[-1, -1, 0, 0]`. A narrowing signed target
/// (`i16 as i8`) keeps the value inside the element's range but wraps it; it is declined too,
/// at no cost: the element's range is wider than `ACC`'s, so every fact the lane could emit
/// for it is weaker than `ACC`'s own type range. On `None` the caller's unsigned lane declines
/// the signed element as well, so the row stays unproved.
///
/// The signed-only sibling of [`addend_per_iteration_bound`] (which is UNSIGNED-only by
/// construction — `fixed_array_elem_bound`/`index_range_reduction_bound` both reject signed
/// elements because the unsigned path emits only an UPPER bound `acc <= C + K*MAX`, which is
/// unsound when the addend can be negative).
///
/// Returns only the per-ELEMENT range; the TRIP COUNT is supplied by the caller's `K =
/// block_execution_bound` (the product over the loops containing the add — exactly as the
/// unsigned path does), NOT this array's length, so a NESTED loop `for _ in 0..M { for &x in a {
/// acc += x as ACC } }` correctly multiplies by `M*LEN` rather than under-counting at `LEN`. A signed element
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
    if crate::local_defs::is_parameter(func, addend_local) || !body_has_iterator_next(func) {
        return None;
    }
    let Rvalue::Cast(Operand::Copy(xp) | Operand::Move(xp), to_ty) =
        crate::local_defs::unique_value_def(func, addend_local)?
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
    // The element's signed range is the ADDEND's range only when the cast keeps the
    // value: a signed target at least as wide. `x as u64` of `-1i8` is `u64::MAX`, and
    // `t += x as u64` over `&[i8; 16]` was proved with the addend bounded by
    // `[-128, 127]`, then panicked at runtime (trip-count lane audit, 2026-09-29).
    // CAST-SIGNED-REDUCTION-TARGET-1 (upstream, same defect): the addend is `x as ACC`,
    // not `x`. Its range is the element's only when the cast is a value-preserving
    // signed widening (or the no-op); an unsigned `ACC` wraps every negative element to
    // near `2^ACCwidth`. Both tests must admit.
    if !to_ty.is_integer()
        || !to_ty.is_signed()
        || to_ty.int_width()? < width
        || !matches!(to_ty, Ty::Int { signed: true, .. })
        || !crate::is_modeled_identity_cast(elem_ty, to_ty)
    {
        return None;
    }
    // CONFIRM `x` is a for-each element of a fixed-size array (so it is a bounded element); the
    // length is discarded — the trip count comes from the caller's whole-nest `K`.
    let _ = for_each_array_elem_ty(func, xp.local)?;
    let elem_min = -(1i128 << (width - 1));
    let elem_max = (1i128 << (width - 1)) - 1;
    Some((elem_min, elem_max))
}

/// `(start, end)` of the exclusive `Range` a for-loop variable iterates, when constant. The
/// loop var `v` is the Some-payload of `Range::next` (`v = (next() as Some).0`); trace it to
/// the originating range aggregate and read its constant bounds. None for a non-range or a
/// non-const `end`. `start` is `None` when it is not a constant; every consumer of this
/// function reads `end` for its bound and treats `start` as optional. Both are YIELD-SET
/// bounds of the loop variable (`start <= v < end`), not the iterator's position — see
/// `iterator_yield::RangeOrigin`.
pub(super) fn loop_var_const_range(
    func: &VerifiableFunction,
    local: usize,
) -> Option<(Option<i128>, i128)> {
    if crate::local_defs::is_parameter(func, local) || !body_has_iterator_next(func) {
        return None;
    }
    const FUEL: u32 = 16;
    let opt_local = match crate::local_defs::unique_value_def(func, local)? {
        Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
            if is_some_payload_projection(&p.projections) =>
        {
            p.local
        }
        _ => return None,
    };
    let RangeOrigin { start, end } = next_call_range_operands(func, opt_local, FUEL)?;
    Some((operand_const_int(start), operand_const_int(end)?))
}

/// The local of a `dst = Use(Copy(tuple.0))` extraction of `tuple_local`'s field 0 — the index
/// `_20` in `_20 = _23.0` for a checked-op result `_23`.
///
/// `None` unless there is EXACTLY ONE such extraction. It previously returned the
/// first match with no uniqueness gate, so with two consumers the caller learned
/// about one of them and silently ignored the other — a caller that reads this as
/// "the consumer" would be wrong. `checked_result_field0_consumer_declines_when_not_unique`
/// (in `merged_local_vacuity_tests`) is the row that fails when the second-distinct-consumer
/// bail is deleted — this comment previously named a row that does not exist.
pub(super) fn checked_result_field0_consumer(
    func: &VerifiableFunction,
    tuple_local: usize,
) -> Option<usize> {
    let mut found: Option<usize> = None;
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
                if found.is_some_and(|f| f != place.local) {
                    return None;
                }
                found = Some(place.local);
            }
        }
    }
    found
}

/// The field-0 consumer of a checked result, but only when its bare symbol has
/// one stable meaning throughout the body.
///
/// `build_flattened_index_facts` emits a GLOBAL fact over that bare symbol. A
/// mere extraction site is not enough to license such a fact: a merged local
/// can also be assigned an unconstrained value, and a parameter has an implicit
/// entry value in addition to its visible body writes. In either case, applying
/// the checked-result bound to the bare name constrains the other value and can
/// false-prove a bounds check. The shared, parameter-aware SSA-collapse gate is
/// the exact authority boundary for this use.
pub(super) fn stable_checked_result_field0_consumer(
    func: &VerifiableFunction,
    tuple_local: usize,
) -> Option<usize> {
    let local = checked_result_field0_consumer(func, tuple_local)?;
    local_versions_collapse_to_bare(func, local).then_some(local)
}

pub(super) fn append_stable_flattened_index_bound(
    func: &VerifiableFunction,
    tuple_local: usize,
    bound: i128,
    facts: &mut Vec<Formula>,
) {
    let Some(idx_local) = stable_checked_result_field0_consumer(func, tuple_local) else {
        return;
    };
    let idx_name = crate::place_to_var_name(func, &Place::local(idx_local));
    facts.push(Formula::Le(
        Box::new(Formula::Var(idx_name, Sort::Int)),
        Box::new(Formula::Int(bound)),
    ));
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
/// loop-var trace (`loop_var_const_range`) yields the EXACT exclusive-range bounds, and the index
/// consumer passes `local_versions_collapse_to_bare`, so the global bare-name fact cannot leak onto
/// a merged definition or a parameter's distinct entry value. SELF-LIMITING:
/// an out-of-range grid (`(H-1)*W+(W'-1) ≥ g.len()`) leaves compatible bounds and stays
/// runtime-checked; a non-const dimension / non-loop-var operand or unstable consumer yields no
/// index fact.
pub(super) fn build_flattened_index_facts(func: &VerifiableFunction) -> Vec<Formula> {
    if !body_has_iterator_next(func) {
        return Vec::new();
    }
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
            if !mul_p.projections.is_empty()
                || !x_p.projections.is_empty()
                || crate::local_defs::is_parameter(func, mul_p.local)
                || crate::local_defs::is_parameter(func, x_p.local)
            {
                continue;
            }
            // mul_p = Use(Copy(mul_tuple.0)); mul_tuple = CheckedMul(y, W_const).
            let Some(Rvalue::Use(Operand::Copy(mt) | Operand::Move(mt))) =
                crate::local_defs::unique_value_def(func, mul_p.local)
            else {
                continue;
            };
            if mt.projections.as_slice() != [trust_types::Projection::Field(0)]
                || crate::local_defs::is_parameter(func, mt.local)
            {
                continue;
            }
            let Some(Rvalue::CheckedBinaryOp(BinOp::Mul, y_op, w_op)) =
                crate::local_defs::unique_value_def(func, mt.local)
            else {
                continue;
            };
            let (Operand::Copy(y_p) | Operand::Move(y_p)) = y_op else { continue };
            if !y_p.projections.is_empty() {
                continue;
            }
            let Some(w) = operand_const_int(w_op).filter(|w| *w > 0) else { continue };
            let Some((_, y_end)) = loop_var_const_range(func, y_p.local) else {
                continue;
            };
            let Some((_, x_end)) = loop_var_const_range(func, x_p.local) else {
                continue;
            };
            let Some(mul_bound) = (y_end - 1).checked_mul(w) else {
                continue;
            };
            let Some(idx_bound) = mul_bound.checked_add(x_end - 1) else {
                continue;
            };
            let mul_name = crate::place_to_var_name(func, &Place::local(mul_p.local));
            facts.push(Formula::Le(
                Box::new(Formula::Var(mul_name, Sort::Int)),
                Box::new(Formula::Int(mul_bound)),
            ));
            // The mul result remains independently bounded even when the final
            // checked-add consumer is merged. Only the INDEX fact requires the
            // consumer's global bare-name license.
            append_stable_flattened_index_bound(func, add_tuple.local, idx_bound, &mut facts);
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
/// (1) the self-add's block runs at most `K = block_execution_bound` times — the product,
/// over the loops CONTAINING it, of each loop's trip count (plus one where the add is not
/// behind that loop's driver edge); see `trust_types::loop_nest` for why no other product
/// is a bound (a single loop, a nested matrix loop `K=N*M`, and a counter loop all
/// qualify, while an undriven while-loop does not); (2) the addend is `x as ACC` where `x` is bounded by a
/// structurally-bounded per-element max — EITHER the element of a for-each over a FIXED-SIZE
/// array `[ELEM; N]`
/// (`for_each_element_fixed_array_bound`, trip count = the array length), OR a loaded
/// unsigned element `a[i]` whose index `i` is the payload of an exclusive `Range`
/// `[start, end)` driving the loop (`index_range_reduction_bound`, trip count =
/// `end - start`); (3) `acc`'s only definitions are a const init and the self-add (and it
/// is neither call-clobbered nor mutably aliased — see `accumulator_init_const`).
pub(super) fn build_accumulator_bound_facts(func: &VerifiableFunction) -> Vec<Formula> {
    let mut facts = Vec::new();
    // `K` = an upper bound on how many times THIS self-add's block runs
    // (`block_execution_bound`). `None` — so no bound — unless every loop containing it
    // has a driver: a `next` call or a counter test that every iteration crosses.
    // `block_execution_bound` short-circuits when `back_edge_count_for(func) == 0` and
    // otherwise shares the per-function memoized `LoopNest` (`super::loop_nest_for`).
    for block in &func.body.blocks {
        let mut block_k: Option<Option<i128>> = None;
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
            if matches!(block_k, Some(None)) {
                break;
            }
            let acc = acc_p.local;
            let Some(init_c) = accumulator_bound_init_const(func, acc, ck_dest.local) else {
                continue;
            };
            let Some(k) = *block_k
                .get_or_insert_with(|| block_execution_bound(func, block.id.0))
            else {
                break;
            };
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
                && let (Some(lo), Some(hi)) = (
                    k.checked_mul(smin).and_then(|nm| init_c.checked_add(nm)),
                    k.checked_mul(smax).and_then(|nm| init_c.checked_add(nm)),
                )
            {
                let acc_name = crate::place_to_var_name(func, &Place::local(acc));
                let addend_name = crate::place_to_var_name(func, &Place::local(rp.local));
                let acc_var = Formula::Var(acc_name, Sort::Int);
                let addend_var = Formula::Var(addend_name, Sort::Int);
                // Accumulator range `lo <= acc <= hi`.
                facts.push(Formula::Le(Box::new(acc_var.clone()), Box::new(Formula::Int(hi))));
                facts.push(Formula::Ge(Box::new(acc_var.clone()), Box::new(Formula::Int(lo))));
                // Addend's own element range `smin <= addend <= smax`.
                facts.push(Formula::Le(Box::new(addend_var.clone()), Box::new(Formula::Int(smax))));
                facts.push(Formula::Ge(Box::new(addend_var.clone()), Box::new(Formula::Int(smin))));
                // TIGHT post-add (sum) range `lo <= acc_old + addend <= hi` — exactly the i-typed
                // overflow operand, the sum of at most `K` signed elements plus init.
                let sum = Formula::Add(Box::new(acc_var), Box::new(addend_var));
                facts.push(Formula::Le(Box::new(sum.clone()), Box::new(Formula::Int(hi))));
                facts.push(Formula::Ge(Box::new(sum), Box::new(Formula::Int(lo))));
                continue;
            }
            // Per-iteration addend max `M`: a NON-NEGATIVE CONSTANT (`t += c`, a counter /
            // conditional count `if cond { t += 1 }`), OR a widened element `x as A` /
            // product `(a[i] as A)*(b[i] as A)` (`addend_per_iteration_bound`'s per-addend
            // max; the trip count is always the whole-nest `K`).
            let (per_max, addend_local) = match rhs {
                Operand::Constant(ConstValue::Int(c)) if *c >= 0 => (*c, None),
                Operand::Constant(ConstValue::Uint(c, _)) if *c <= i128::MAX as u128 => {
                    (*c as i128, None)
                }
                Operand::Copy(rp) | Operand::Move(rp) if rp.projections.is_empty() => {
                    match addend_per_iteration_bound(func, rp.local) {
                        Some(per) => (per, Some(rp.local)),
                        None => continue,
                    }
                }
                _ => continue,
            };
            let Some(bound) = k.checked_mul(per_max).and_then(|nm| init_c.checked_add(nm)) else {
                continue;
            };
            let acc_name = crate::place_to_var_name(func, &Place::local(acc));
            static ACC_DEBUG: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
            if *ACC_DEBUG.get_or_init(|| crate::trust_vcgen_env_var_present("TRUST_ACC_DEBUG")) {
                eprintln!(
                    "TRUST_ACC[{}] acc={} K={} per_max={} init={} -> bound {} <= {}",
                    func.name, acc, k, per_max, init_c, acc_name, bound
                );
            }
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
                facts.push(Formula::Le(
                    Box::new(Formula::Var(acc_name.clone(), Sort::Int)),
                    Box::new(Formula::Int(bound)),
                ));
                let addend_name = crate::place_to_var_name(func, &Place::local(addend));
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
            } else {
                facts.push(Formula::Le(
                    Box::new(Formula::Var(acc_name, Sort::Int)),
                    Box::new(Formula::Int(bound)),
                ));
            }
        }
    }
    facts
}

/// Trace an operand to its root whole-local through `Copy`/`Move` and `Use` copies.
pub(super) fn operand_root_local(
    func: &VerifiableFunction,
    op: &Operand,
    fuel: u32,
) -> Option<usize> {
    if fuel == 0 {
        return None;
    }
    let (Operand::Copy(p) | Operand::Move(p)) = op else { return None };
    if !p.projections.is_empty() {
        return None;
    }
    if let Some(Rvalue::Use(inner)) = crate::local_defs::unique_value_def(func, p.local) {
        if let Some(root) = operand_root_local(func, inner, fuel - 1) {
            return Some(root);
        }
    }
    Some(p.local)
}

/// Does the boolean `SwitchInt` ending `guard` test the CURRENT value of `root` through
/// the comparison operand `op` of `g = cmp(..)`?
///
/// Trust (2026-10-10, review round 103): [`operand_root_local`] follows `x = copy root`
/// to a MUTABLE root, so a guard on a stale copy was credited to the root's current
/// value. `let l0 = lo; while l0 < hi { hi -= 1; s[lo]; lo += 2 }` got `lo < len`, and
/// `let k = j; while k > 1 { j -= 1; a[j - 1] }` got `j - 1 >= 1`, both kernel-certified
/// and both panic; a bool `g = lo < hi` computed before `lo` is rewritten is the same
/// channel. Here the comparison must be computed in `guard` itself, `op` must reach
/// `root` through whole copies made in `guard` before it, and no statement after the
/// read of `root` may write `root`.
pub(super) fn guard_operand_reads_current(
    func: &VerifiableFunction,
    guard: BlockId,
    g: usize,
    op: &Operand,
    root: usize,
) -> bool {
    let Some(block) = func
        .body
        .blocks
        .get(guard.0)
        .filter(|b| b.id == guard)
        .or_else(|| func.body.blocks.iter().find(|b| b.id == guard))
    else {
        return false;
    };
    let Some(cmp_at) = block.stmts.iter().rposition(|stmt| {
        matches!(stmt, Statement::Assign { place, rvalue: Rvalue::BinaryOp(..), .. }
            if place.local == g && place.projections.is_empty())
    }) else {
        return false;
    };
    let (Operand::Copy(p) | Operand::Move(p)) = op else { return false };
    if !p.projections.is_empty() {
        return false;
    }
    let (mut cur, mut pos) = (p.local, cmp_at);
    while cur != root {
        let Some((k, next)) =
            block.stmts[..pos].iter().enumerate().rev().find_map(|(k, stmt)| match stmt {
                Statement::Assign { place, rvalue, .. } if place.local == cur => match rvalue {
                    Rvalue::Use(Operand::Copy(q) | Operand::Move(q))
                        if place.projections.is_empty() && q.projections.is_empty() =>
                    {
                        Some((k, Some(q.local)))
                    }
                    _ => Some((k, None)),
                },
                _ => None,
            })
        else {
            return false;
        };
        let Some(next) = next else { return false };
        (cur, pos) = (next, k);
    }
    !block.stmts[pos + 1..]
        .iter()
        .any(|stmt| matches!(stmt, Statement::Assign { place, .. } if place.local == root))
}

/// The successor a boolean `SwitchInt` takes when the discriminant is TRUE (value
/// 1) — for `_g = Lt(lo, hi)` this is the `lo < hi` (loop-body) edge.
pub(super) fn bool_switch_true_target(
    targets: &[(u128, BlockId)],
    otherwise: BlockId,
) -> Option<BlockId> {
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
    crate::visit_local_write_candidates(func, &func.body.blocks, local, |block, item| match item {
        Some(s) => {
            if matches!(s, Statement::Assign { place, .. } if place.local == local) {
                out.insert(block.id.0);
            }
        }
        None => {
            if matches!(&block.terminator, Terminator::Call { dest, .. } if dest.local == local) {
                out.insert(block.id.0);
            }
        }
    });
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
    let n = func.body.blocks.len();
    if start >= n || avoid.contains(&start) {
        return seen;
    }
    seen.insert(start);
    let mut stack = vec![start];
    while let Some(b) = stack.pop() {
        for_each_v2_terminator_target(&func.body.blocks[b].terminator, |succ| {
            let s = succ.0;
            if s < n && !avoid.contains(&s) && seen.insert(s) {
                stack.push(s);
            }
        });
    }
    seen
}

/// True iff `target` is in [`reachable_avoiding`]`(func, start, avoid)`, using a
/// flat `Vec<bool>` visited table and short-circuiting as soon as `target` is reached.
pub(super) fn reachable_avoiding_contains(
    func: &VerifiableFunction,
    start: usize,
    avoid: &FxHashSet<usize>,
    target: usize,
) -> bool {
    let n = func.body.blocks.len();
    if start >= n || target >= n || avoid.contains(&start) || avoid.contains(&target) {
        return false;
    }
    if start == target {
        return true;
    }
    let mut seen = vec![false; n];
    seen[start] = true;
    let mut stack = vec![start];
    while let Some(b) = stack.pop() {
        let mut hit = false;
        for_each_v2_terminator_target(&func.body.blocks[b].terminator, |succ| {
            let s = succ.0;
            if s == target {
                hit = true;
            } else if s < n && !seen[s] && !avoid.contains(&s) {
                seen[s] = true;
                stack.push(s);
            }
        });
        if hit {
            return true;
        }
    }
    false
}

/// True iff `target` is reachable from `start` without entering `avoid_block` (when
/// `Some`), equivalent to `reachable_avoiding(func, start, &avoid).contains(&target)`
/// without allocating an `FxHashSet<usize>`.
pub(super) fn reachable_avoiding_one_contains(
    func: &VerifiableFunction,
    start: usize,
    avoid_block: Option<usize>,
    target: usize,
) -> bool {
    let n = func.body.blocks.len();
    if start >= n
        || target >= n
        || avoid_block == Some(start)
        || avoid_block == Some(target)
    {
        return false;
    }
    if start == target {
        return true;
    }
    let mut seen = vec![false; n];
    seen[start] = true;
    let mut stack = vec![start];
    while let Some(b) = stack.pop() {
        let mut hit = false;
        for_each_v2_terminator_target(&func.body.blocks[b].terminator, |succ| {
            let s = succ.0;
            if s == target {
                hit = true;
            } else if s < n && !seen[s] && avoid_block != Some(s) {
                seen[s] = true;
                stack.push(s);
            }
        });
        if hit {
            return true;
        }
    }
    false
}

/// Per-block facts for the CONVERGING two-pointer idiom
///   `let lo = 0; let hi = s.len(); while lo < hi { hi -= 1; … s[lo] …; lo += 1; }`
/// (or the same guard spelled `hi > lo`).
///
/// `s[hi]` is discharged by [`build_downward_induction_facts`]: `hi` is a downward
/// var, and the relational guard `lo < hi` over an UNSIGNED `lo` certifies the
/// decrement underflow-free (`hi >= 1`), so its result gets `hi - 1 < s.len()`
/// (TWO-POINTER-FALSE-REFUTE: from 7180f666c3 until 2026-10-06 only a constant
/// guard certified it, and this sentence was false). For `s[lo]`: on the
/// loop-body path the guard gives `lo < hi`, and `hi <= s.len()` (downward
/// invariant), so `lo < s.len()`. This holds for `lo`'s value AT THE GUARD, and only
/// on paths that took the guard's TRUE edge; it stops holding once `lo` is
/// incremented (`lo + 1` may equal `s.len()`). So the fact `lo < s.len()` is emitted
/// ONLY at "lo-stable" blocks — those reachable from the guard's true-edge WITHOUT
/// passing through any block that writes `lo` and WITHOUT re-entering the loop header,
/// AND not reachable at all from a `lo`-write block's successors (so no path delivers
/// a post-increment `lo`), AND certified by the true edge
/// ([`TrueEdgeReach::certifies`]): reached neither from the guard's OTHER successors
/// nor from the function entry without passing the guard, on a non-degenerate switch.
/// At such blocks every path last took the true edge and `lo` equals its guard value,
/// so `lo < s.len()` is SOUND.
///
/// The true-edge clause is CONVERGING-MERGE-1 (2026-10-10). Without it, a block that
/// the FALSE edge also reaches got the fact: the merge after `if lo < hi { hi -= 1;
/// s[hi] = 0 } s[lo] = 1` (`lo` a parameter; `c3(&mut [0], 5)` indexes `s[5]`), and
/// the loop exit a `break` shares with the guard's false edge (`while lo < hi { hi -=
/// 1; if s[hi] == 0 { break } lo += 1 } s[lo] = 1`; `c1(&mut [7])` indexes `s[1]`).
/// certify kernel-certified each `s[lo]` `[bounds]` row. The `if` shape was a false
/// proof on main (`32b6ef82d6`); the `Gt(hi, lo)` spelling and the relational
/// decrement certificate of TWO-POINTER-FALSE-REFUTE made the others reachable.
///
/// "Its guard value" presumes the guard READ the current `lo`. A boolean computed
/// before a `lo` write does not (CONVERGING-GUARD-STALE-1, 2026-10-06): in
/// `loop { if lo > 1000 { break } let c = lo < hi; lo += 1; tick(); if c { hi -= 1;
/// s[lo] = 0 } else { break } }` the increment sits in a block BEFORE the switch, so
/// neither the lo-stable walk nor the taint walk (both start at the switch) sees it,
/// `lo < s.len()` was emitted of the incremented `lo`, and certify kernel-certified
/// all three rows of a function that indexes `s[1]` on a one-byte slice. The
/// comparison and the read of `lo` must now sit in the switch block with no `lo`
/// write after the read (`guard_comparison_in_block`, `cursor_read_in_block`). The
/// read of `hi` needs no such check: `hi <= s.len()` holds at every point.
pub(super) fn build_converging_pointer_facts(
    func: &VerifiableFunction,
) -> FxHashMap<BlockId, Vec<Formula>> {
    const FUEL: u32 = 16;
    let mut map: FxHashMap<BlockId, Vec<Formula>> = FxHashMap::default();
    if !super::terminator_presence_for(func).has_switch_int {
        return map;
    }
    let downward = super::downward_induction_vars_for(func);
    if downward.is_empty() {
        return map;
    }

    for block in &func.body.blocks {
        let Terminator::SwitchInt { discr, targets, otherwise, .. } = &block.terminator else {
            continue;
        };
        let Some(true_target) = bool_switch_true_target(targets, *otherwise) else { continue };
        if true_target.0 == 0
            || std::iter::once(otherwise)
                .chain(targets.iter().map(|(_, t)| t))
                .filter(|&&t| t == true_target)
                .count()
                != 1
        {
            continue;
        }
        // The guard discriminant must be `_g = Lt(lo, hi)` (or `Gt(hi, lo)`, the same
        // predicate), computed in this block.
        let Some((cmp_idx, cmp)) = guard_comparison_in_block(func, block, discr, FUEL) else {
            continue;
        };
        let (lo_op, hi_op) = match cmp {
            Rvalue::BinaryOp(trust_types::BinOp::Lt, a, b) => (a, b),
            Rvalue::BinaryOp(trust_types::BinOp::Gt, a, b) => (b, a),
            _ => continue,
        };
        let Some(hi) = operand_root_local(func, hi_op, FUEL) else {
            continue;
        };
        // A PARAMETER `hi` qualifies as a downward var when its entry value reaches no
        // DECREMENT (DOWNWARD-PARAM-CURSOR-1), which says nothing about THIS guard's
        // read: an init between the guard and the decrement (`while lo < hi { hi =
        // s.len(); hi -= 1; .. }`) leaves the guard comparing the caller's `hi`, which
        // `s.len()` does not bound. Fail closed.
        if crate::local_defs::is_parameter(func, hi) {
            continue;
        }
        // `hi` (the guard's upper operand) must be a downward induction var.
        let Some(dv) = downward.iter().find(|d| d.local == hi) else { continue };
        let Some(lo) = operand_root_local(func, lo_op, FUEL) else {
            continue;
        };
        // The guard must have compared the CURRENT `lo` (CONVERGING-GUARD-STALE-1).
        let Some(lo_read) = cursor_read_in_block(func, block, lo_op, cmp_idx, lo, FUEL) else {
            continue;
        };
        if block.stmts[lo_read + 1..].iter().any(|s| writes_local(s.local_write(lo))) {
            continue;
        }
        // Trust (2026-10-10, review round 103; composed with upstream's
        // CONVERGING-GUARD-STALE-1 read check above): `g_local` is the comparison's
        // own destination.
        let Some(Statement::Assign { place: g_place, .. }) = block.stmts.get(cmp_idx) else {
            continue;
        };
        let g_local = g_place.local;
        if !guard_operand_reads_current(func, block.id, g_local, lo_op, lo) {
            continue;
        }
        // Trust (2026-10-10, review round 102): "reachable from the true edge" is not
        // dominance. `while lo < hi { hi -= 1; if c { break; } lo += 1; } s[lo]` reaches
        // the exit from the true edge (the `break`) AND from the false edge, where `lo >=
        // hi`: `s[lo]` was kernel-certified and panics on an empty `s`. A block gets the
        // fact only if it cannot be reached from entry around the true target, and the
        // true target is entered only through the guard's true edge.
        if !crate::guards::block_has_sole_predecessor(func, true_target, block.id) {
            continue;
        }
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

        // Blocks reachable from any lo-write block's successors (within the body,
        // avoiding the header) carry a POST-write `lo` on some path — exclude them.
        let mut tainted: FxHashSet<usize> = FxHashSet::default();
        let avoid_header = one_block_set(header);
        for &w in &reassign {
            if w >= func.body.blocks.len() {
                continue;
            }
            for_each_v2_terminator_target(&func.body.blocks[w].terminator, |succ| {
                tainted.extend(reachable_avoiding(func, succ.0, &avoid_header));
            });
        }
        // The header re-reads `lo` for the next iteration — stop BFS there so the
        // analysis stays within ONE loop body.
        reassign.insert(header);
        let stable = reachable_avoiding(func, true_target.0, &reassign);
        let around_guard = reachable_avoiding(func, 0, &one_block_set(true_target.0));

        let lo_var = Formula::Var(crate::place_to_var_name(func, &Place::local(lo)), Sort::Int);
        // `lo` is the loop's lower pointer; when it is an UNSIGNED integer it is
        // `>= 0`, which (with the guard `lo < hi`) gives `hi >= 1` and discharges
        // the `hi -= 1` underflow check. A non-param local's usize non-negativity is
        // otherwise not asserted in the Int model.
        let lo_unsigned =
            crate::local_ty_ref(func, lo).is_some_and(|ty| ty.is_integer() && !ty.is_signed());
        // CONVERGING-MERGE-1: the fact speaks only for blocks every path reaches
        // through the TRUE edge, `lo` unwritten since (see the function doc).
        let reach = true_edge_reach(func, lo, header, true_target);
        for b in stable {
            if tainted.contains(&b) || reassign.contains(&b) || around_guard.contains(&b) {
                continue;
            }
            let whole_block = func.body.blocks.get(b).map_or(0, |blk| blk.stmts.len());
            if !reach.certifies(func, lo, b, whole_block) {
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

// ── WHAT RUNS BEFORE A LOOP'S TEST (TRIP-MID-TEST-1) ───────────────────────
//
// A trip count counts how often a loop's TEST (a counter comparison, an
// `Iterator::next` driver) lets the loop continue. A block that runs BEFORE the test
// in each pass runs once more than that, and a cycle that AVOIDS the test is not
// bounded by it at all. The helpers below answer both questions on block ids, over
// `terminator_succs` — the successor relation `block_is_on_cycle` and
// `count_back_edges` walk — so they need no positional block layout.

/// `terminator_succs` for every block, keyed by block id.
fn block_successors(func: &VerifiableFunction) -> FxHashMap<usize, Vec<usize>> {
    func.body.blocks.iter().map(|b| (b.id.0, terminator_succs(&b.terminator))).collect()
}

/// Blocks reachable from the entry block without ENTERING `avoid` (`avoid` itself is
/// never in the result). For a loop test `T` this is everything that can run before
/// `T` is first reached — the pre-loop code, and the part of each pass between the
/// loop header and `T`.
fn reachable_from_entry_avoiding(func: &VerifiableFunction, avoid: usize) -> FxHashSet<usize> {
    let mut seen: FxHashSet<usize> = FxHashSet::default();
    let Some(entry) = func.body.blocks.first().map(|b| b.id.0) else { return seen };
    let mut stack = vec![entry];
    while let Some(b) = stack.pop() {
        if b == avoid || !seen.insert(b) {
            continue;
        }
        for_each_block_succ(&func.body.blocks, b, |s| stack.push(s));
    }
    seen
}

/// True when the CFG with `excluded` deleted still has a cycle — some way to loop
/// that never passes through `excluded`. `false` means every cycle of the function
/// runs through `excluded`. Iterative three-colour DFS from every block.
fn has_cycle_avoiding(func: &VerifiableFunction, excluded: usize) -> bool {
    let blocks = &func.body.blocks;
    if blocks.is_empty()
        || super::cached_terminator_presence_for_body(&func.body)
            .is_some_and(|tp| !tp.has_back_edge)
    {
        return false;
    }
    if blocks.iter().enumerate().all(|(i, b)| b.id.0 == i) {
        let n = blocks.len();
        // 0 = white (unseen), 1 = gray (on stack), 2 = black (finished).
        let mut color = vec![0u8; n];
        let mut stack: Vec<(usize, usize)> = Vec::new();
        for root in 0..n {
            if root == excluded || color[root] != 0 {
                continue;
            }
            color[root] = 1;
            stack.clear();
            stack.push((root, 0));
            while let Some(top) = stack.last_mut() {
                let (u, i) = *top;
                if let Some(v) = nth_terminator_succ(&blocks[u].terminator, i) {
                    top.1 += 1;
                    if v == excluded {
                        continue;
                    }
                    match color.get(v).copied().unwrap_or(2) {
                        0 => {
                            color[v] = 1;
                            stack.push((v, 0));
                        }
                        1 => return true,
                        _ => {}
                    }
                } else {
                    color[u] = 2;
                    stack.pop();
                }
            }
        }
        return false;
    }
    let succ = block_successors(func);
    // 0 = white (unseen), 1 = gray (on stack), 2 = black (finished).
    let mut color: FxHashMap<usize, u8> = FxHashMap::default();
    for root in func.body.blocks.iter().map(|b| b.id.0) {
        if root == excluded || color.contains_key(&root) {
            continue;
        }
        color.insert(root, 1);
        let mut stack: Vec<(usize, usize)> = vec![(root, 0)];
        while let Some(top) = stack.last_mut() {
            let (u, i) = *top;
            let edges = succ.get(&u).map(Vec::as_slice).unwrap_or(&[]);
            if i < edges.len() {
                top.1 += 1;
                let v = edges[i];
                if v == excluded {
                    continue;
                }
                match color.get(&v).copied().unwrap_or(0) {
                    0 => {
                        color.insert(v, 1);
                        stack.push((v, 0));
                    }
                    1 => return true,
                    _ => {}
                }
            } else {
                color.insert(u, 2);
                stack.pop();
            }
        }
    }
    false
}

/// True when `block` holds a checked add whose left operand is a whole local — every
/// add a trip-count consumer can bound (`build_accumulator_bound_facts`, the BV
/// accumulator lane and the BMC reduction all start from `CheckedBinaryOp(Add, acc, _)`
/// with `acc` a whole local). Deliberately wider than "a self-add": counting an add the
/// consumers then decline only loosens or drops a bound.
fn block_holds_checked_add(block: &trust_types::BasicBlock) -> bool {
    block.stmts.iter().any(|stmt| {
        matches!(
            stmt,
            Statement::Assign {
                rvalue: Rvalue::CheckedBinaryOp(BinOp::Add, Operand::Copy(p) | Operand::Move(p), _),
                ..
            } if p.projections.is_empty()
        )
    })
}

/// True when some block of `region` lies on a cycle and holds a checked add — an add
/// that can run once per pass of a loop.
fn region_has_on_cycle_add(func: &VerifiableFunction, region: &FxHashSet<usize>) -> bool {
    if region.is_empty() {
        return false;
    }
    func.body
        .blocks
        .iter()
        .filter(|b| region.contains(&b.id.0) && block_holds_checked_add(b))
        .any(|b| block_is_on_cycle(func, b.id.0))
}

/// True when `driver` is a loop header (a back-edge target) whose natural loop is
/// entered ONLY through it: no block of that loop is reachable from the entry without
/// passing `driver` (`pre` is [`reachable_from_entry_avoiding`]`(driver)`). Then each
/// pass of the loop starts at `driver`, nothing in the loop runs before it, and its
/// trip count bounds every block of the loop except the driver's own call block and
/// the block its call returns to, which also run on the `None` pass
/// ([`driver_follows_a_loop_add`] asks about those two first) — the shape of every
/// `for` and `while let` loop, whose `next()` call heads the loop.
///
/// The natural loop is rebuilt from the header's own latches: `driver` plus every
/// block that reaches a latch without passing `driver`. An outer loop's body is NOT
/// part of it, so an add in an outer body (`for i { c += 1; for j { … } }`) does not
/// disqualify the inner driver; the outer driver's own factor bounds that add.
fn driver_heads_its_loop(driver: usize, pre: &FxHashSet<usize>, loops: &[TripLoop]) -> bool {
    loops
        .iter()
        .find(|l| l.header == driver)
        .is_some_and(|l| l.body.iter().all(|b| !pre.contains(b)))
}

/// TRIP-MID-TEST-1, iterator lane: true when `driver` (an on-cycle `Iterator::next`
/// call block) does NOT head its loop and an on-cycle checked add can run before it.
/// Such an add runs once more per loop entry than the driver returns `Some`
/// (`loop { c += 1; if it.next().is_none() { break; } }`: 255 adds for 254 items), so
/// the driver's trip count under-counts it.
///
/// The pre-region is everything reachable from the entry without passing `driver`.
/// That over-approximates "before the driver within its own pass" (it also holds the
/// pre-loop code, whose off-cycle adds run once and are covered by `K >= 1`, and any
/// earlier loop), so a non-header driver is refused more often than strictly needed:
/// the fail-closed direction.
///
/// Trust (2026-10-05, TRIP-MID-TEST-1 residual): the driver's OWN two blocks run on
/// the `None` pass too, header or not — the call block's statements before the call,
/// and the block the call returns to, whose statements run before the switch on the
/// result's discriminant ([`loop_driven_by`] makes that block the call's only
/// successor and the call its only predecessor). A checked add in either runs once
/// per `next()` call, `tc + 1` times. `while let Some(_) = { c = add_with_overflow(c,
/// 1).0; it.next() } {}` puts the add in the call block of a driver that HEADS its
/// loop, so the header exemption below let `tc` stand, and `let x = it.next(); c =
/// add_with_overflow(c, 1).0; let Some(_) = x else { break };` puts it above the
/// switch; both read `K = 255` for 256 adds at `-Zmir-opt-level=2 -Zinline-mir=no`
/// (a trapping `c += 1` ends its block with an `Assert`, so only a NON-trapping
/// checked add — the intrinsic, or an inlined `overflowing_add` — can sit there).
fn driver_follows_a_loop_add(
    func: &VerifiableFunction,
    driver: usize,
    loops: &[TripLoop],
) -> bool {
    if driver_blocks_hold_checked_add(func, driver) {
        return true;
    }
    if !func.body.blocks.iter().any(block_holds_checked_add) {
        return false;
    }
    let pre = reachable_from_entry_avoiding(func, driver);
    if driver_heads_its_loop(driver, &pre, loops) {
        return false;
    }
    region_has_on_cycle_add(func, &pre)
}

/// True when the `next()` call block `driver`, or the block its call returns to,
/// holds a checked add — an add that runs on every call, the `None` one included.
/// An unreadable call block, or a call with no return block, answers `true`: the
/// fail-closed answer for the refusal it feeds.
fn driver_blocks_hold_checked_add(func: &VerifiableFunction, driver: usize) -> bool {
    let block_of = |id: usize| {
        func.body
            .blocks
            .get(id)
            .filter(|b| b.id.0 == id)
            .or_else(|| func.body.blocks.iter().find(|b| b.id.0 == id))
    };
    let Some(call_block) = block_of(driver) else { return true };
    let Terminator::Call { target: Some(target), .. } = &call_block.terminator else {
        return true;
    };
    let Some(return_block) = block_of(target.0) else { return true };
    block_holds_checked_add(call_block) || block_holds_checked_add(return_block)
}

/// A natural loop: a back-edge target (`header`) and every block that reaches one of
/// its latches without passing it, the header included.
///
/// Trust (merge 2026-10-14): named `TripLoop`, not `NaturalLoop`, so it does not
/// collide with the imported `trust_types::loop_nest::NaturalLoop` the per-block
/// execution bound uses.
struct TripLoop {
    header: usize,
    body: FxHashSet<usize>,
}

/// Every natural loop of the function, one per loop header (the headers
/// [`count_back_edges`] counts). In the reducible CFG rustc's MIR is, two natural
/// loops are nested or disjoint, so the innermost loop holding a block is the smallest
/// one that holds it.
fn natural_loops(func: &VerifiableFunction) -> Vec<TripLoop> {
    let latches_by_header = back_edge_latches(func);
    if latches_by_header.is_empty() {
        return Vec::new();
    }
    let mut preds: FxHashMap<usize, Vec<usize>> = FxHashMap::default();
    for b in &func.body.blocks {
        for_each_terminator_succ(&b.terminator, |t| {
            preds.entry(t).or_default().push(b.id.0);
        });
    }
    latches_by_header
        .into_iter()
        .map(|(header, latches)| {
            let mut body: FxHashSet<usize> = FxHashSet::default();
            body.insert(header);
            let mut stack = latches;
            while let Some(b) = stack.pop() {
                if body.insert(b)
                    && let Some(p) = preds.get(&b)
                {
                    stack.extend(p.iter().copied());
                }
            }
            TripLoop { header, body }
        })
        .collect()
}

/// TRIP-DRIVER-1: the loop header and the result local of the `Iterator::next` call
/// that terminates block `call_block`, when that call DRIVES its innermost natural loop
/// `L`; `None` when it does not. All three must hold:
///
///   1. The call's only successor switches on the DISCRIMINANT of the call's result
///      (`d = discriminant(r); switchInt(d)`), and nothing else reaches that switch, so
///      the branch is decided by this call's value. `let _ = r.next();` has no such
///      switch, and `if r.next().is_none()` switches on a `bool` a call computed.
///   2. `Option`'s `None` arm (discriminant 0) LEAVES `L` and its `Some` arm (1) STAYS
///      in it; any other target of the switch is unreachable or outside `L`. A `None`
///      that continues (`match r.next() { None => continue, … }`) bounds nothing.
///   3. The iterator — the place the call's `&mut` receiver borrows — is written by no
///      block of `L`: it is built outside the loop it drives. `loop { let mut r =
///      0..2; let Some(_) = r.next() else { break }; … }` rebuilds it every pass, so
///      it never runs out.
///
/// What the call's iterator yields, and that only `next` advances it, is the trip-count
/// tracers' question (`iterator_origin_def`'s `iter_mut_borrows_only_feed_next` gate),
/// asked by [`driver_trip_count`]; this function decides only WHICH loop the call
/// bounds.
fn loop_driven_by(
    func: &VerifiableFunction,
    call_block: usize,
    loops: &[TripLoop],
) -> Option<(usize, usize)> {
    let block_of = |id: usize| {
        func.body
            .blocks
            .get(id)
            .filter(|b| b.id.0 == id)
            .or_else(|| func.body.blocks.iter().find(|b| b.id.0 == id))
    };
    let block = block_of(call_block)?;
    let Terminator::Call { dest, args, target: Some(target), .. } = &block.terminator else {
        return None;
    };
    if !dest.projections.is_empty() {
        return None;
    }
    let result = dest.local;
    // 1. The successor's switch reads the result's discriminant, taken there.
    let switch = block_of(target.0)?;
    let Terminator::SwitchInt {
        discr: Operand::Copy(d) | Operand::Move(d),
        targets,
        otherwise,
        ..
    } = &switch.terminator
    else {
        return None;
    };
    if !d.projections.is_empty() || crate::local_defs::is_parameter(func, d.local) {
        return None;
    }
    let Some(Rvalue::Discriminant(read)) = crate::local_defs::unique_value_def(func, d.local)
    else {
        return None;
    };
    if read.local != result || !read.projections.is_empty() {
        return None;
    }
    let [Operand::Copy(receiver) | Operand::Move(receiver)] = args.as_slice() else {
        return None;
    };
    if !receiver.projections.is_empty() {
        return None;
    }
    // 2. `None` (0) leaves the innermost loop, `Some` (1) stays in it.
    let lp = loops.iter().filter(|l| l.body.contains(&call_block)).min_by_key(|l| l.body.len())?;
    let arm =
        |value: u128| targets.iter().find(|(v, _)| *v == value).map_or(otherwise.0, |(_, b)| b.0);
    let (none_arm, some_arm) = (arm(0), arm(1));
    if lp.body.contains(&none_arm) || !lp.body.contains(&some_arm) {
        return None;
    }
    let both_listed = [0u128, 1].iter().all(|v| targets.iter().any(|(t, _)| t == v));
    let other_arms = targets
        .iter()
        .filter(|(v, _)| *v > 1)
        .map(|(_, b)| b.0)
        .chain(both_listed.then_some(otherwise.0));
    for other in other_arms {
        let dead = block_of(other)
            .is_some_and(|b| matches!(b.terminator, Terminator::Unreachable));
        if lp.body.contains(&other) && !dead {
            return None;
        }
    }
    let taken_at = crate::local_defs::unique_defining_block(func, d.local)?;
    if func.body.blocks.get(taken_at)?.id.0 != switch.id.0 {
        return None;
    }
    // 3. The iterator the receiver borrows is built outside the loop.
    let iterator = borrowed_iterator(func, receiver.local)?;
    if crate::fn_memo::sole_predecessors(func)
        .and_then(|sp| sp.no_other_exit_predecessor(*target, block.id))
        != Some(true)
    {
        let mut entries = 0usize;
        for b in &func.body.blocks {
            if terminator_has_succ(&b.terminator, target.0) {
                entries += 1;
                if entries > 1 {
                    return None;
                }
            }
        }
        if entries != 1 {
            return None;
        }
    }
    if local_write_blocks(func, iterator).iter().any(|b| lp.body.contains(b)) {
        return None;
    }
    Some((lp.header, result))
}

/// The local a `next` receiver borrows: `r = &mut it` gives `it`, and the reborrow
/// `r = &mut (*q)` with `q = &mut it` gives `it` too (the spelling pre-optimization MIR
/// uses). Anything else is `None`.
fn borrowed_iterator(func: &VerifiableFunction, receiver: usize) -> Option<usize> {
    if crate::local_defs::is_parameter(func, receiver) {
        return None;
    }
    let Some(Rvalue::Ref { mutable: true, place }) =
        crate::local_defs::unique_value_def(func, receiver)
    else {
        return None;
    };
    match place.projections.as_slice() {
        [] => Some(place.local),
        [trust_types::Projection::Deref] if !crate::local_defs::is_parameter(func, place.local) => {
            let Some(Rvalue::Ref { mutable: true, place: inner }) =
                crate::local_defs::unique_value_def(func, place.local)
            else {
                return None;
            };
            inner.projections.is_empty().then_some(inner.local)
        }
        _ => None,
    }
}

// ── MANUAL COUNTER LOOPS ────────────────────────────────────────────────────

/// True when `start` lies on a cycle that AVOIDS `excluded` — the same forward
/// reachability [`block_is_on_cycle`] walks, with one block deleted from the
/// graph. `false` therefore means EVERY cycle through `start` passes through
/// `excluded`, which is how the gates below establish "this statement runs on
/// every iteration".
fn block_is_on_cycle_excluding(func: &VerifiableFunction, start: usize, excluded: usize) -> bool {
    if start == excluded {
        return false;
    }
    let blocks = &func.body.blocks;
    if blocks.is_empty()
        || super::cached_terminator_presence_for_body(&func.body)
            .is_some_and(|tp| !tp.has_back_edge)
    {
        return false;
    }
    if blocks.iter().enumerate().all(|(i, b)| b.id.0 == i) {
        let n = blocks.len();
        if start >= n {
            return false;
        }
        let mut seen = vec![false; n];
        let mut stack: Vec<usize> = Vec::new();
        let mut direct_self = false;
        for_each_terminator_succ(&blocks[start].terminator, |b| {
            if b == start {
                direct_self = true;
            } else if b != excluded && b < n && !seen[b] {
                seen[b] = true;
                stack.push(b);
            }
        });
        if direct_self {
            return true;
        }
        while let Some(b) = stack.pop() {
            let mut hit = false;
            for_each_terminator_succ(&blocks[b].terminator, |t| {
                if t == start {
                    hit = true;
                } else if t != excluded && t < n && !seen[t] {
                    seen[t] = true;
                    stack.push(t);
                }
            });
            if hit {
                return true;
            }
        }
        return false;
    }
    let mut stack: Vec<usize> = Vec::new();
    for_each_block_succ(blocks, start, |b| {
        if b != excluded {
            stack.push(b);
        }
    });
    let mut seen: FxHashSet<usize> = FxHashSet::default();
    while let Some(b) = stack.pop() {
        if b == start {
            return true;
        }
        if b != excluded && seen.insert(b) {
            for_each_block_succ(blocks, b, |t| {
                if t != excluded {
                    stack.push(t);
                }
            });
        }
    }
    false
}

/// Which BRANCH of the loop test leaves the loop: `Some(true)` when the TRUE
/// edge exits (`loop { …; if r > N { break } }`), `Some(false)` when the FALSE
/// edge exits (`while i < N { … }`), `None` when the test does not gate the back
/// edge at all.
///
/// WHY IT MUST BE ASKED. The comparison alone does not say what continuing
/// requires. Bottom-tested loops exit on TRUE, so their continuation condition is
/// the comparison's NEGATION, and reading it without this gets the bound exactly
/// backwards. Measured on the daily-driver bench's `ctrl/c5`,
/// `loop { r += 1; if r > x.min(5) { break; } }`, whose `SwitchInt` sends the
/// FALSE arm back to the loop head and the TRUE arm out.
///
/// FAIL-CLOSED: exactly one edge must leave the cycle and the other must stay in
/// it. Both edges inside means the comparison gates nothing (a plain `if` in the
/// body); both outside means it is not a loop test. Either answers `None`.
fn loop_exit_branch_polarity(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    discr: &Operand,
    targets: &[(u128, BlockId)],
    otherwise: BlockId,
) -> Option<bool> {
    let test_block = block.id.0;
    let mut exit_on: Option<bool> = None;
    let mut stays = 0usize;
    for (value, target) in targets.iter().map(|(v, b)| (Some(*v), *b)).chain([(None, otherwise)]) {
        let truth = crate::abstract_interp::transfer::branch_truth(func, discr, value, targets)?;
        let in_loop = target.0 == test_block || block_is_on_cycle(func, target.0);
        if in_loop {
            stays += 1;
        } else {
            if exit_on.is_some() {
                return None;
            }
            exit_on = Some(truth);
        }
    }
    (stays == 1).then_some(exit_on?)
}

/// A non-negative integer constant operand, else `None`.
fn const_operand_nonneg(op: &Operand) -> Option<i128> {
    match op {
        Operand::Constant(ConstValue::Int(c)) if *c >= 0 => Some(*c),
        Operand::Constant(ConstValue::Uint(c, _)) if *c <= i128::MAX as u128 => Some(*c as i128),
        _ => None,
    }
}

/// A manual loop counter as [`counter_init_stride_block`] recognizes it.
struct ManualCounter {
    /// The constant the counter starts from.
    init: i128,
    /// Block id of that constant init definition.
    init_block: usize,
    /// The positive constant its one self-add adds.
    stride: i128,
    /// Block id of that `CheckedBinaryOp(Add, ctr, stride)`.
    add_block: usize,
    /// Where the incremented value lands in the counter (`ctr = ck.0`, or `ctr = t`
    /// with `t = ck.0`): block id and statement index. Which side of the loop test
    /// this write is on decides what value the test sees (TRIP-MID-TEST-1).
    write_at: (usize, usize),
}

/// The index in `block.stmts` of the `Assign` whose rvalue IS `rvalue` (the same
/// reference, not an equal value) — where a definition the seam returned sits.
fn assign_position(block: &trust_types::BasicBlock, rvalue: &Rvalue) -> Option<usize> {
    block.stmts.iter().position(
        |stmt| matches!(stmt, Statement::Assign { rvalue: held, .. } if std::ptr::eq(held, rvalue)),
    )
}

/// The counter's init, stride, add block and write position ([`ManualCounter`]) for
/// a local whose ONLY definitions are a non-negative constant init OFF every cycle and
/// ONE self-add of a positive constant — the same recognition
/// [`accumulator_init_const`] performs, plus the stride and the positions, which the
/// trip count needs and the accumulator does not.
///
/// Refuses, on EVERY channel `trust_types::LocalWrite` names rather than on the three
/// this function used to enumerate by hand, a counter that anything else can write: a
/// write this recognition cannot see lets the counter be reset or advanced by less
/// than `stride` per iteration, and that makes the trip count UNDER-count — the
/// false-bound direction. The channel set is `local_defs::value_defs`'s.
///
/// Refuses a constant init that sits ON a cycle (TRIP-INIT-CYCLE-1). Such an init is
/// not an init: it RESETS the counter on every pass (`loop { i = 0; …; i += 1; if i >=
/// 10 { break; } }`, or `let mut i = 0;` declared inside the loop body), so the test
/// never sees the counter advance and the loop runs until some other exit, however
/// long that takes. An init on no cycle runs at most once, and borrowck puts it before
/// every read of the counter, so it runs before the loop. This is the gate
/// `bmc_reduction::const_init_is_outside_loop` and the countdown lane's companion
/// qualifier already applied; this lane had none.
fn counter_init_stride_block(func: &VerifiableFunction, ctr: usize) -> Option<ManualCounter> {
    // Pass 1: EVERY value the counter can hold, from the seam. `value_defs` is the
    // complete channel set — it refuses a PARAMETER (whose entry definition is not in
    // `body.blocks`, so no list built by a block scan can contain it), a `Call`/
    // `TailCall` destination, a projected or discriminant store, a `Deinit`/`Drop`, a
    // mutable-or-raw alias, and an unlocatable write. The hand-rolled scan this
    // replaces enumerated three of those by hand and was blind to `Partial` and to
    // `TailCall`; a counter RESET or advanced through a channel this function does not
    // see runs the loop longer than `K` says, and an UNDER-counted `K` is the
    // false-bound direction.
    let defs = crate::local_defs::value_defs(func, ctr)?;
    // Exactly two definitions — a non-negative constant init and ONE read-back of a
    // checked add — so nothing else can reset it or advance it by a different amount.
    let [(first_at, first), (second_at, second)] = defs.as_slice() else { return None };
    let mut init: Option<(i128, usize)> = None;
    let mut write: Option<(usize, usize, &Rvalue)> = None;
    for (at, rvalue) in [(*first_at, *first), (*second_at, *second)] {
        match rvalue {
            Rvalue::Use(Operand::Constant(ConstValue::Int(c))) if *c >= 0 => init = Some((*c, at)),
            Rvalue::Use(Operand::Constant(ConstValue::Uint(c, _))) if *c <= i128::MAX as u128 => {
                init = Some((*c as i128, at))
            }
            // The self-add read-back, direct or through one temp.
            _ => write = Some((checked_result_read_back_temp(func, rvalue)?, at, rvalue)),
        }
    }
    let ((init, init_at), (ck, write_index, write_rvalue)) = (init?, write?);
    let init_block = func.body.blocks.get(init_at)?.id.0;
    // Trust (2026-10-04, TRIP-INIT-CYCLE-1): the init must run once, before the loop
    // — never on a cycle, where it resets the counter every pass. See the doc above.
    if block_is_on_cycle(func, init_block) {
        return None;
    }
    // Pass 2: the checked add that feeds the read-back must add a POSITIVE CONSTANT to
    // the counter itself, and its overflow flag must TRAP. WHICH rvalue is the temp's
    // value, and WHICH block holds it, are seam questions too: `unique_value_def` and
    // `unique_defining_block` both refuse every second-write channel, so the add
    // recognized here is the only one that can have produced the value read back — the
    // scan they replace took the FIRST matching `Assign` and asked nothing about the
    // temp's other writes.
    let Some(Rvalue::CheckedBinaryOp(BinOp::Add, lhs, rhs)) =
        crate::local_defs::unique_value_def(func, ck)
    else {
        return None;
    };
    let add_block = func.body.blocks.get(crate::local_defs::unique_defining_block(func, ck)?)?;
    let (Operand::Copy(lp) | Operand::Move(lp)) = lhs else { return None };
    if lp.local != ctr || !lp.projections.is_empty() {
        return None;
    }
    let stride = const_operand_nonneg(rhs)?;
    if stride < 1 {
        return None;
    }
    // The overflow flag must TRAP. `i = i.overflowing_add(s).0` has the same shape but
    // CONTINUES with the wrapped value, so the counter would not be monotone and
    // `i = i0 + m*s` — the whole trip-count argument — would be false. Requiring the
    // `Assert` is what makes "overflow implies no continuation" true rather than
    // assumed.
    if !overflow_flag_traps(&add_block.terminator, ck) {
        return None;
    }
    // Where the read-back sits: the seam's own definition, located by identity.
    let write_block = func.body.blocks.get(write_index)?;
    let write_stmt = assign_position(write_block, write_rvalue)?;
    Some(ManualCounter {
        init,
        init_block,
        stride,
        add_block: add_block.id.0,
        write_at: (write_block.id.0, write_stmt),
    })
}

/// The checked-arithmetic temp whose RESULT field `rvalue` reads back — the inverse of
/// [`reads_back_checked_result`], which answers the same question about a temp the
/// caller already has. Accepts the direct `x = ck.0` and the ONE-HOP `x = t` where
/// `t`'s only value is `ck.0`, on the same argument: the hop is
/// [`crate::local_defs::unique_value_def`], so there is no other value `t` could hold.
///
/// It replaces a scan over every `Assign` in the body looking for a `CheckedBinaryOp`
/// whose destination the rvalue reads back; the temp is named by the rvalue itself, so
/// no definition scan is needed to find it.
fn checked_result_read_back_temp(func: &VerifiableFunction, rvalue: &Rvalue) -> Option<usize> {
    let field0 = |q: &Place| match q.projections.as_slice() {
        [trust_types::Projection::Field(0)] => Some(q.local),
        _ => None,
    };
    let Rvalue::Use(Operand::Copy(p) | Operand::Move(p)) = rvalue else { return None };
    if let Some(ck) = field0(p) {
        return Some(ck);
    }
    if !p.projections.is_empty() {
        return None;
    }
    match crate::local_defs::unique_value_def(func, p.local) {
        Some(Rvalue::Use(Operand::Copy(q) | Operand::Move(q))) => field0(q),
        _ => None,
    }
}

/// True when `terminator` is the `Assert` that TRAPS the overflow flag of the
/// checked-arithmetic temp `ck` — `assert(!move (ck.1))`. rustc emits it as the
/// terminator of the very block holding the `CheckedBinaryOp`, so this is a
/// local check, not a dataflow one.
fn overflow_flag_traps(terminator: &Terminator, ck: usize) -> bool {
    let Terminator::Assert { cond, expected: false, .. } = terminator else { return false };
    let (Operand::Copy(p) | Operand::Move(p)) = cond else { return false };
    p.local == ck && matches!(p.projections.as_slice(), [trust_types::Projection::Field(1)])
}

/// True when any statement or terminator in the function writes through a
/// channel this pass cannot see — inline asm (`Opaque`), a custom `Drop`,
/// `CopyNonOverlapping`, `Deinit`, an `Intrinsic`, or an `Unsupported`
/// statement. Each can set the counter or the accumulator without an `Assign`
/// this scan would find, and a counter advanced or RESET behind our back makes
/// the trip count UNDER-count.
///
/// [`WriteEffect`] is the right oracle rather than a hand-written variant list
/// because its classifiers are EXHAUSTIVE: a new MIR write channel fails to
/// compile until it is classified, so it cannot silently bypass this gate.
fn has_unmodelable_write(func: &VerifiableFunction) -> bool {
    super::has_unmodelable_write_for(func)
}

pub(super) fn has_unmodelable_write_uncached(func: &VerifiableFunction) -> bool {
    use trust_types::WriteEffect;
    func.body.blocks.iter().any(|block| {
        block.terminator.write_effect() == WriteEffect::FailClosedOrBackstopped
            || block
                .stmts
                .iter()
                .any(|stmt| stmt.write_effect() == WriteEffect::FailClosedOrBackstopped)
    })
}

/// The counter local a loop test actually compares, resolving ONE copy.
///
/// rustc does not compare the counter; it compares a fresh copy of it. `ctrl/c5`
/// lowers `if r > x.min(5)` to `_5 = copy _2; … _4 = Gt(_5, _6)`, so requiring
/// the compared operand to BE the counter recognizes nothing.
///
/// SOUNDNESS — a copy taken before the increment is a STALE value, and a trip
/// count read off it UNDER-counts, which is the false-bound direction. Both
/// clauses below exist for that:
///
///   * `local` is either the counter itself, or a local whose UNIQUE value
///     definition is `Use(Copy/Move(counter))` — `unique_value_def` refuses a
///     `Call` destination, a projected store, an unlocatable pointer write and
///     any mutable-or-raw alias, so nothing else can have written it;
///   * that definition sits in the test block itself, or in a block whose ONLY
///     successor is the test block and which is the test block's ONLY
///     predecessor — a straight line with no room for another write, and no
///     other path into the test that could arrive with a different value.
///
/// A copy hoisted ABOVE the loop, or into a block the test is also reachable
/// from some other way, fails the second clause and is refused.
///
/// Returns the counter and WHERE its value is read for the test — block id and
/// statement index: the copy's own statement, or, when the test compares the counter
/// itself, the comparison, which `discriminant_defining_comparison` requires to be the
/// test block's LAST statement. A write of the counter in that same block lands before
/// or after the read by statement order (TRIP-MID-TEST-1).
fn counter_local_compared_at(
    func: &VerifiableFunction,
    test_block: &trust_types::BasicBlock,
    local: usize,
) -> Option<(usize, (usize, usize))> {
    let Some(copy @ Rvalue::Use(Operand::Copy(p) | Operand::Move(p))) =
        crate::local_defs::unique_value_def(func, local)
    else {
        // Not a copy at all: it may be the counter itself, read by the comparison.
        return Some((local, (test_block.id.0, test_block.stmts.len().checked_sub(1)?)));
    };
    if !p.projections.is_empty() {
        return None;
    }
    let counter = p.local;
    // Where is that copy defined? The seam answers with the ONE block that writes
    // `local`: `unique_defining_block` grants an answer only when the local holds one
    // value on EVERY channel and is not a parameter, so no other block can write it and
    // the positional argument below is about the only definition there is. The scan
    // this replaces took the first block holding an `Assign` to `local` and was blind
    // to every other channel.
    let defining = func.body.blocks.get(crate::local_defs::unique_defining_block(func, local)?)?;
    let read_at = (defining.id.0, assign_position(defining, copy)?);
    if defining.id.0 == test_block.id.0 {
        return Some((counter, read_at));
    }
    if terminator_sole_succ(&defining.terminator) != Some(test_block.id.0) {
        return None;
    }
    if crate::fn_memo::sole_predecessors(func)
        .and_then(|sp| sp.no_other_exit_predecessor(test_block.id, defining.id))
        == Some(true)
    {
        return Some((counter, read_at));
    }
    let mut sole_pred = None;
    for b in &func.body.blocks {
        if terminator_has_succ(&b.terminator, test_block.id.0) {
            if sole_pred.is_some() || b.id.0 != defining.id.0 {
                return None;
            }
            sole_pred = Some(b.id.0);
        }
    }
    (sole_pred == Some(defining.id.0)).then_some((counter, read_at))
}

/// An upper bound the PROGRAM has already established for a loop-bound operand
/// that is not a literal — today only `Ord::min(_, c)`, which is `<= c` for any
/// other argument, by definition of `min`. core's `min` only (`call_facts::
/// primitive_int_ord_method`, NAME-ANCHOR-1/-2): a user function NAMED `min`, or a
/// user `Ord` impl that overrides `min`, bounds nothing.
///
/// WHY THIS IS NOT A VALUE RESOLUTION. It never claims to know what the operand
/// IS, only that it cannot exceed `c`. That is all a trip count needs, and it is
/// what keeps this away from the resolver channel whose doc records three live
/// kernel-certified false proofs.
///
/// Trust: 2026-09-19 — it is [`local_min_upper_bound`] on the operand's local, and
/// it used to be a SECOND COPY of that scan which differed in one place: it had no
/// PARAMETER arm. A `mut m: u32` written once by `m = x.min(5)` on some path reaches
/// the loop test with its unbounded ENTRY value on every other path, and reading
/// `m <= 5` there UNDER-counts the trip count — the false-bound direction, and the
/// exact hole `build_min_upper_bound_facts` had already written a parameter skip for.
/// The seam answers it once now, for both callers;
/// `a_min_bounded_parameter_limit_is_refused` is the row.
///
/// `max` is deliberately absent: `max(a, c) >= c` is a LOWER bound and says
/// nothing about how far the counter can run.
fn bound_operand_upper_bound(func: &VerifiableFunction, bound_op: &Operand) -> Option<i128> {
    let (Operand::Copy(p) | Operand::Move(p)) = bound_op else { return None };
    if !p.projections.is_empty() {
        return None;
    }
    local_min_upper_bound(func, p.local)
}

/// Global facts `m <= c` for every local whose ONLY definition is an
/// `Ord::min(_, c)` call with a constant argument — std's `Ord::min`/`cmp::min` on
/// a primitive integer `Self` (`call_facts::primitive_int_ord_method`), never by
/// the name `min` alone and never by std's trait path alone (see
/// [`local_min_upper_bound`]).
///
/// WHY THIS IS GLOBAL AND NOT A LOOP FACT. `min(a, c) <= c` holds at every
/// program point, for signed and unsigned alike, so it is sound to conjoin onto
/// any obligation over `m`. It was written for the trip-count lane, but the same
/// value shows up wherever a program clamps a size:
///
///     pub fn build(n: usize) -> Vec<u32> { (0..n.min(8) as u32).collect() }
///
/// was `[unbounded_allocation] FAILED` with a counterexample of 33554432 — the
/// allocation lane reconstructs the element count from the range end, that end is
/// a `min` CALL DESTINATION, and nothing bounded it. The range really is bounded
/// by 8. Measured 2026-09-19.
///
/// THE `pmod` LESSON, again. That false proof came from an `Assign`-only scan
/// resolving a local whose OTHER definition was a `Call` destination, so the
/// question is asked on EVERY channel and refuses on any surprise — exactly one
/// defining `Call` which must be a `min` with one constant argument, no `Assign`
/// beside it, no projected or discriminant write, no mutable-or-raw alias, no
/// unlocatable write, and never a PARAMETER, whose implicit entry definition no block
/// scan can see. All of that is `local_defs::unique_value_call`; this lane states the
/// requirement and the seam decides it.
///
/// Trust: 2026-09-19 — the loop below used to carry its own `1..=arg_count` skip. The
/// skip was correct for the local it tested and did not cover the CAST HOP, which
/// re-asks the question about the cast's SOURCE: `if c { n = n.min(8); } let k = n as
/// u64;` has a parameter source, and `k <= 8` is false on the path that skips the
/// call. The parameter arm is now the seam's, once, for the local and for every hop.
/// `a_parameter_gets_no_min_bound` and `a_cast_from_a_parameter_min_gets_no_bound` are
/// the rows.
///
/// `max` is deliberately absent — `max(a, c) >= c` is a LOWER bound.
pub(super) fn build_min_upper_bound_facts(func: &VerifiableFunction) -> Vec<Formula> {
    if !super::terminator_presence_for(func).has_bare_dest_call {
        return Vec::new();
    }
    let mut direct_bounds: Vec<(usize, i128)> = Vec::new();
    for b in &func.body.blocks {
        if let Terminator::Call { func: callee, args, dest, .. } = &b.terminator
            && dest.projections.is_empty()
            && args.len() == 2
            && method_tail(callee) == "min"
            && !direct_bounds.iter().any(|(l, _)| *l == dest.local)
            && let Some(bound) = local_min_upper_bound(func, dest.local)
        {
            direct_bounds.push((dest.local, bound));
        }
    }
    if direct_bounds.is_empty() {
        return Vec::new();
    }
    let lookup_direct = |local: usize| -> Option<i128> {
        direct_bounds.iter().find_map(|&(l, b)| (l == local).then_some(b))
    };
    let mut facts = Vec::new();
    for local in 0..func.body.locals.len() {
        let bound = lookup_direct(local).or_else(|| {
            let Rvalue::Cast(Operand::Copy(p) | Operand::Move(p), target_ty) =
                crate::local_defs::unique_value_def(func, local)?
            else {
                return None;
            };
            if !p.projections.is_empty() {
                return None;
            }
            let bound = lookup_direct(p.local)?;
            let source_ty = crate::local_ty_ref(func, p.local)?;
            if !matches!(source_ty, Ty::Int { signed: false, .. }) {
                return None;
            }
            (int_ty_max(target_ty)? >= bound).then_some(bound)
        });
        let Some(bound) = bound else { continue };
        let name = crate::place_to_var_name(func, &Place::local(local));
        facts.push(Formula::Le(
            Box::new(Formula::Var(name, Sort::Int)),
            Box::new(Formula::Int(bound)),
        ));
    }
    facts
}

/// The inclusive maximum of an integer type, or `None` for anything else.
fn int_ty_max(ty: &Ty) -> Option<i128> {
    match ty {
        Ty::Int { width, signed } => {
            let width = *width as u32;
            if *signed {
                (width >= 1 && width <= 127).then(|| (1i128 << (width - 1)) - 1)
            } else {
                (width <= 127).then(|| (1i128 << width) - 1)
            }
        }
        _ => None,
    }
}

/// The constant `c` of the single `Ord::min(_, c)` call that is `local`'s only
/// definition — see [`build_min_upper_bound_facts`] for every refusal.
fn local_min_upper_bound(func: &VerifiableFunction, local: usize) -> Option<i128> {
    // The seam's `WholeOpaque` resolver: `unique_value_call` answers only when ONE
    // `Call` destination is the local's ONLY value on EVERY channel — not a PARAMETER
    // (whose entry definition reaches every use on a path that skips the call), no
    // second call, no `Assign` beside it, no projected/discriminant write, no mutable
    // alias, no unlocatable write. The scan this replaces enumerated the `Assign` and
    // `Call`-dest channels and the alias by hand and answered for a parameter, whose
    // unbounded entry value the fact `local <= c` would have been false of.
    let Terminator::Call { func: callee, args, dest, .. } =
        crate::local_defs::unique_value_call(func, local)?
    else {
        return None;
    };
    let [arg0, arg1] = args.as_slice() else {
        return None;
    };
    // Exactly one constant argument, the other being the unbounded operand.
    let c = match (const_operand_nonneg(arg0), const_operand_nonneg(arg1)) {
        (Some(c), None) | (None, Some(c)) => c,
        _ => return None,
    };
    // The std `Ord::min` / `cmp::min`, AUTHENTICATED: a user `mod lim { pub fn min(a:
    // u32, _cap: u32) -> u32 { a } }` also ends in `::min`, and `0..lim::min(n, 10)` was
    // proved to run at most 10 times, then overflowed (trip-count lane audit, 2026-09-29).
    // Trust (2026-10-03, NAME-ANCHOR-1): std's `min`, not a function NAMED `min`.
    // This was `callee.ends_with("::min") && !callee.ends_with("::max")`, which
    // any user function satisfies: `util::min(x, 10)` returning `x` got the
    // GLOBAL fact `dest <= 10`, the Clean kernel certified the `+ 1` overflow row
    // under it, and the elision deleted the check — `util::min(u32::MAX, 10) + 1`
    // returned 0 (`tests/ui/trust/min_upper_bound_requires_std_min{,_run}.rs`).
    // `ord_method` admits only a `core::cmp::`/`std::cmp::`-rooted path or a
    // qualified `<T as core::cmp::Ord>::min`; it anchors the trait, not `T`.
    // Trust (2026-10-04, NAME-ANCHOR-2): `primitive_int_ord_method` — the ONE gate
    // every `min`/`max`/`clamp` fact asks — adds that the destination, and so
    // `T` (`Ord::min` returns `Self`), is a primitive integer whose `Ord` only
    // `core` implements, with every argument of that type. This lane already
    // required an integer destination; the call-dest, global min/max, return-pin
    // and const-summary lanes did not, and a user `impl Ord for E` overriding
    // `min` was certified through them. One predicate covers both consumers here:
    // the global fact (`build_min_upper_bound_facts`) and the trip count
    // (`bound_operand_upper_bound`).
    // (Merge 2026-10-14: local main's `call_facts::is_ord_min_call` gate is gone
    // upstream; `primitive_int_ord_method` asks the same, now position-anchored,
    // `ord_method`, so it subsumes it.)
    if dest.local != local || primitive_int_ord_method(func, callee, args, dest) != Some("min") {
        return None;
    }
    Some(c)
}

/// The driver of a MANUAL counter loop — `while i < N { … i += s; }` — for
/// [`block_execution_bound`]: the test's continue edge, and how many times one
/// entry of `lp` can cross it.
///
/// WHY THIS EXISTS. A hand-written `while` has no `Iterator::next` to read a trip
/// count from. Measured 2026-09-18: `for &x in a { t += x as u64 }` over `&[u8; 64]`
/// proves (the mechanism emits `t <= 0 + 64*255`), while the same reduction written
/// `while i < 3 { c += 1; i += 1; }` was refuted `[overflow:add] FAILED` — not because
/// anything about `c` is harder, but because nothing supplied a trip count.
///
/// SOUNDNESS. The one requirement is that `trip` never UNDER-counts how many times
/// the continue edge is crossed in one entry of `lp`; each clause closes one way to
/// under-count:
///
///   * The test is in `lp`'s OWN blocks, and exactly one of its edges leaves `lp`.
///     A test whose edges both stay gates nothing (`loop { if i < 3 {} … }`); which
///     edge LEAVES decides what continuing means (`loop { …; if r > N { break } }`
///     continues on the comparison's NEGATION).
///   * The counter has a constant init, ONE self-add of a constant stride `s >= 1`
///     whose overflow flag TRAPS, and is neither call-clobbered nor mutably aliased
///     (`counter_init_stride_block`). A counter that can be reset, or advanced by
///     less than `s`, runs the loop longer.
///   * The init is OUTSIDE `lp`, so an iteration cannot reset the counter, and
///     EVERY iteration passes the block where the counter takes its advanced value.
///     Otherwise `if cond { i += 1 }` advances it on only some iterations.
///   * The limit `N` is a constant, or a value the program bounded above by a
///     constant (`min(_, c)`).
///
/// With those, the counter only grows, and between two crossings of the continue
/// edge an iteration advanced it, so the `m`-th crossing in one entry reads
/// `i >= i0 + (m-1)*s` and continuing needs that `< N`. Hence
/// `m <= ceil((N - i0) / s)` (one more span unit for `<=`), which is `trip`.
/// That every iteration crosses the edge at all, and whether a given block sits
/// behind it, [`block_execution_bound`] checks for every driver alike: before
/// 2026-09-29 this was a separate trip count read as a bound on every self-add, and
/// `loop { if flag { c += 1; continue } if i >= 10 { break } i += 1 }` (a cycle
/// through neither the test nor the advance) and `loop { c += 1; if i >= 10 {
/// break } i += 1 }` (an add that runs once more than the loop continues) were both
/// proved and overflowed.
pub(super) fn counter_loop_driver(
    func: &VerifiableFunction,
    nest: &LoopNest,
    lp: &NaturalLoop,
) -> Option<LoopDriver> {
    if !super::terminator_presence_for(func).has_switch_int {
        return None;
    }
    for block in &func.body.blocks {
        let Terminator::SwitchInt { discr, targets, otherwise, .. } = &block.terminator else {
            continue;
        };
        if !nest.owns(lp, block.id.0) {
            continue;
        }
        let Some((op, lhs, rhs)) =
            crate::abstract_interp::transfer::discriminant_defining_comparison(block, discr)
        else {
            continue;
        };
        if !matches!(op, BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge) {
            continue;
        }
        // Exactly one edge leaves `lp`; its truth value says what continuing means.
        let mut exit_on: Option<bool> = None;
        let mut stay: Option<usize> = None;
        let mut well_formed = true;
        let arms = targets.iter().map(|(v, b)| (Some(*v), *b)).chain([(None, *otherwise)]);
        for (value, target) in arms {
            let Some(truth) =
                crate::abstract_interp::transfer::branch_truth(func, discr, value, targets)
            else {
                well_formed = false;
                break;
            };
            if lp.contains(target.0) {
                well_formed &= stay.replace(target.0).is_none();
            } else {
                well_formed &= exit_on.replace(truth).is_none();
            }
        }
        let (true, Some(exit_on), Some(stay)) = (well_formed, exit_on, stay) else { continue };
        let op = if exit_on {
            crate::abstract_interp::transfer::negate_order_comparison(op)
        } else {
            op
        };
        // Normalise `>`/`>=` by swapping, so only `<`/`<=` are reasoned about.
        let (op, counter_op, bound_op) = match op {
            BinOp::Lt | BinOp::Le => (op, lhs, rhs),
            BinOp::Gt => (BinOp::Lt, rhs, lhs),
            BinOp::Ge => (BinOp::Le, rhs, lhs),
            _ => continue,
        };
        let (Operand::Copy(cp) | Operand::Move(cp)) = counter_op else { continue };
        if !cp.projections.is_empty() {
            continue;
        }
        let Some(limit) =
            const_operand_nonneg(bound_op).or_else(|| bound_operand_upper_bound(func, bound_op))
        else {
            continue;
        };
        if has_unmodelable_write(func) {
            return None;
        }
        // rustc compares a COPY of the counter, not the counter: c5's test is
        // `Gt(_5, _6)` with `_5 = copy _2` (`-Ztrust-dump=mir-only`). Resolve one
        // such copy, and ONLY under the positional rule in
        // `counter_local_compared_at`.
        // (Upstream's `counter_local_compared_at` also returns where the copy is read;
        // this driver does not need it.)
        let Some((counter, _)) = counter_local_compared_at(func, block, cp.local) else {
            continue;
        };
        let Some(ManualCounter { init, init_block, stride, write_at: (advance, _), .. }) =
            counter_init_stride_block(func, counter)
        else {
            continue;
        };
        if lp.contains(init_block) || !nest.every_iteration_passes(lp, advance) {
            continue;
        }
        // `m <= ceil((limit - init) / stride)` for `<`, and one more for `<=`. One
        // stride loose when every iteration advances BEFORE its test (`loop { i += 1;
        // if i > N { break } }`, whose `m`-th test reads `i0 + m*s`): tightening it
        // needs the compared copy to postdate the advance, a statement-order
        // question `counter_local_compared_at` does not answer.
        let span = match op {
            BinOp::Le => limit.checked_sub(init)?.checked_add(1)?,
            _ => limit.checked_sub(init)?,
        };
        let trip = if span <= 0 { 0 } else { span.checked_add(stride - 1)? / stride };
        return Some(LoopDriver { edge: (block.id.0, stay), trip });
    }
    None
}

/// Trip count of a MANUAL counter loop — `while i < N { … i += s; }`.
///
/// Trust (merge 2026-10-14): upstream's whole-function count, kept for
/// [`total_loop_iterations`] (the bounded-reduction REFUTATION lane) and its tests.
/// The PROVING lanes read the per-block [`block_execution_bound`], whose counter
/// driver is [`counter_loop_driver`] above.
///
/// WHY THIS EXISTS. [`total_loop_iterations`] recovers `K` only from an
/// `Iterator::next` call that drives the loop, so a hand-written `while` gets no
/// `K` at all and [`build_accumulator_bound_facts`] returns EMPTY. Measured
/// 2026-09-18: `for &x in a { t += x as u64 }` over `&[u8; 64]` proves (the
/// mechanism emits `t <= 0 + 64*255`), while the same reduction written
/// `while i < 3 { c += 1; i += 1; }` is refuted `[overflow:add] FAILED` — not
/// because anything about `c` is harder, but because no `Iterator::next` exists
/// to read a trip count from.
///
/// SOUNDNESS. The one requirement is that `K` never UNDER-counts how many times
/// a self-add runs; an under-count makes `t <= init + K*M` a FALSE bound, which
/// is the false-proof direction. Each clause below closes one way to under-count:
///
///   * ONE loop (`count_back_edges == 1`). A self-add inside an INNER loop runs
///     the inner trip count times per outer iteration, which this single `K`
///     would not cover.
///   * The counter has a constant init, ONE self-add of a constant stride
///     `s >= 1`, and is neither call-clobbered nor mutably aliased
///     (`counter_init_stride_block`). A counter that can be reset, or advanced by
///     less than `s`, runs the loop longer than `K` says.
///   * The const init is on NO cycle (TRIP-INIT-CYCLE-1,
///     `counter_init_stride_block`). An init inside the loop RESETS the counter on
///     every pass, so its test bounds nothing.
///   * EVERY cycle through the test passes through the self-add's block AND through
///     the block whose statement writes the incremented value back into the
///     counter. Otherwise `if cond { i += 1 }` advances the counter on only some
///     iterations and the loop runs MORE than `K` times. (The ACCUMULATOR needs no
///     such clause: an accumulator skipped on some paths is added FEWER times,
///     which `K` over-counts — the safe direction, and the `if cond { t += 1 }`
///     shape the existing doc already admits.)
///   * EVERY cycle of the function passes through the test (TRIP-MID-TEST-1), and
///     the test's exit edge LEAVES the loop while its other edge stays in it. A
///     test that does not gate the back edge bounds nothing:
///     `loop { if i < 3 {} c += 1; i += 1; … }` would take `K = 3` from a
///     comparison the loop does not obey. And a cycle that AVOIDS the test — a
///     `continue` above it, as in
///     `loop { c += 1; …; if flag { continue; } i += 1; if i >= 10 { break; } }` —
///     loops without testing or advancing the counter at all.
///   * The bound `N` is a CONSTANT. A variable bound has no value here — the
///     entry-state interval that could bound it is the abstract interpreter's,
///     not this pass's — so it is refused rather than guessed.
///
/// THE COUNT. Let `K0 = ceil((N - i0) / s)` (0 when `N <= i0`). Every pass of the
/// loop runs the test once, and the counter's write once, either BEFORE the test
/// (the c5 shape, `loop { r += 1; if r > 5 { break; } }`) or AFTER it (`while i <
/// N { …; i += 1; }`, and the mid-tested `loop { c += 1; if i >= N { break; } i +=
/// 1; }`). A wrapping `i += s` is itself a checked add that panics, so it has no
/// continuation.
///
///   * Write after the test: the `j`-th test sees `i0 + (j-1)*s` and continues
///     iff that is `< N`, so the test continues `C = K0` times.
///   * Write before the test: the `j`-th test sees `i0 + j*s`, so it continues
///     `C = K0 - 1` times (0 when `K0 == 0`).
///
/// A block that runs AFTER the test in a pass runs at most `C` times; code that
/// runs BEFORE the test's branch in a pass — a block reachable from the entry
/// without passing the test, AND the test block's own statements, which precede its
/// `SwitchInt` — runs at most `C + 1` times (TRIP-MID-TEST-1: the mid-tested shape's
/// `c += 1` runs `K0 + 1` times, and the old `K0` was a false bound on it). So this
/// returns `C + 1` when an on-cycle checked add precedes the test's branch and `C`
/// otherwise,
/// clamped to at least 1 so a self-add placed OUTSIDE the loop (which runs once)
/// is still covered. The c5 shape stays exact: its own add precedes the test and
/// its write lands before it, so `C + 1 = K0`.
///
/// "Before the test" is read on block ids by reachability, which names the region
/// between the loop header and the test exactly when every cycle passes the test
/// and the single loop is entered only through its header — the reducible CFG
/// rustc's MIR is.
pub(super) fn manual_counter_trip_count(func: &VerifiableFunction) -> Option<i128> {
    if !super::terminator_presence_for(func).has_switch_int {
        return None;
    }
    if count_back_edges(func) != 1 {
        return None;
    }
    for block in &func.body.blocks {
        let Terminator::SwitchInt { discr, targets, otherwise, .. } = &block.terminator else {
            continue;
        };
        let test_block = block.id.0;
        if !block_is_on_cycle(func, test_block) {
            continue;
        }
        let Some((op, lhs, rhs)) =
            crate::abstract_interp::transfer::discriminant_defining_comparison(block, discr)
        else {
            continue;
        };
        if has_unmodelable_write(func) {
            return None;
        }
        // WHICH EDGE LEAVES THE LOOP decides what the comparison means. A
        // `while i < N` exits on FALSE, so continuing IS the comparison; a
        // `loop { …; if r > N { break } }` exits on TRUE, so continuing is its
        // NEGATION. Reading the comparison without asking which edge exits gets
        // the bottom-tested form exactly backwards.
        let Some(exit_on) = loop_exit_branch_polarity(func, block, discr, targets, *otherwise)
        else {
            continue;
        };
        let op = if exit_on {
            crate::abstract_interp::transfer::negate_order_comparison(op)
        } else {
            op
        };
        // Normalise `>`/`>=` by swapping, so only `<`/`<=` are reasoned about.
        let (op, counter_op, bound_op) = match op {
            BinOp::Lt | BinOp::Le => (op, lhs, rhs),
            BinOp::Gt => (BinOp::Lt, rhs, lhs),
            BinOp::Ge => (BinOp::Le, rhs, lhs),
            _ => continue,
        };
        let (Operand::Copy(cp) | Operand::Move(cp)) = counter_op else { continue };
        if !cp.projections.is_empty() {
            continue;
        }
        // rustc compares a COPY of the counter, not the counter: c5's test is
        // `Gt(_5, _6)` with `_5 = copy _2` (`-Ztrust-dump=mir-only`). Resolve one
        // such copy, and ONLY under the positional rule in
        // `counter_local_compared_at`, because a copy taken BEFORE the increment
        // is a stale value and the trip count read off it would UNDER-count.
        let Some((counter, read_at)) = counter_local_compared_at(func, block, cp.local) else {
            continue;
        };
        // The limit is a literal constant, or a value the program has already
        // bounded above — today `Ord::min(_, c)`, which is `<= c` by definition.
        let Some(limit) =
            const_operand_nonneg(bound_op).or_else(|| bound_operand_upper_bound(func, bound_op))
        else {
            continue;
        };
        let Some(ctr) = counter_init_stride_block(func, counter) else { continue };
        // The self-add, and the write that lands it, must run on EVERY iteration.
        if block_is_on_cycle_excluding(func, test_block, ctr.add_block)
            || block_is_on_cycle_excluding(func, test_block, ctr.write_at.0)
        {
            continue;
        }
        // Trust (2026-10-04, TRIP-MID-TEST-1): every cycle passes through the test.
        // `loop_exit_branch_polarity` established that exactly one edge leaves the
        // cycle and the other stays in it; this establishes that no pass of the loop
        // can skip the test.
        if has_cycle_avoiding(func, test_block) {
            continue;
        }
        // `K0 = ceil((limit - init) / stride)` for `<`, with one more for `<=`.
        let span = match op {
            BinOp::Le => limit.checked_sub(ctr.init)?.checked_add(1)?,
            _ => limit.checked_sub(ctr.init)?,
        };
        let k0 = if span <= 0 { 0 } else { span.checked_add(ctr.stride - 1)? / ctr.stride };
        // Which value the test reads. The write lands BEFORE the read when it sits
        // in the reading block at an earlier statement, or in another block that
        // runs before the test (reachable from the entry without passing it).
        let pre_test = reachable_from_entry_avoiding(func, test_block);
        let (write_block, write_stmt) = ctr.write_at;
        let read_sees_write = if write_block == read_at.0 {
            write_stmt < read_at.1
        } else {
            pre_test.contains(&write_block)
        };
        let continuations = if read_sees_write { (k0 - 1).max(0) } else { k0 };
        // A checked add that runs before the test in a pass runs once more: one in a
        // block reachable from the entry without passing the test, or one in the TEST
        // BLOCK itself, whose statements all run before its `SwitchInt` on every pass,
        // the exiting one included. Trust (2026-10-05, TRIP-MID-TEST-1 residual): the
        // test block was missed — `reachable_from_entry_avoiding` never holds the block
        // it avoids. A trapping `c += 1` cannot sit there (its `Assert` ends the
        // block), but a NON-trapping `CheckedBinaryOp(Add, c, 1)` can, and
        // `build_accumulator_bound_facts` bounds it: `c = c.overflowing_add(1).0` above
        // `if i >= 254 { break; }` lands in the test block once `-Zmir-opt-level=2`
        // inlines it, and read `K = 254` for 255 adds (a Certified row, the check
        // elided, `ovf_wrap()` returned 0). The test block is on a cycle (checked
        // above), so its add is an on-cycle add.
        let extra =
            i128::from(block_holds_checked_add(block) || region_has_on_cycle_add(func, &pre_test));
        return Some(continuations.checked_add(extra)?.max(1));
    }
    None
}

/// Trust (2026-10-01, ordsweep2 numeric/c03, c15): the driver of a SHRINKING loop —
/// `while n > 0 { …; n /= 10 }` / `while n != 0 { …; n >>= 1 }` — for
/// [`block_execution_bound`]: the test's continue edge, and the number of times one
/// entry of `lp` can cross it.
///
/// SOUNDNESS. Continuing requires `n >= 1` (the test is `n > 0`, `n != 0`, `n >= c`
/// with `c >= 1`, or the mirrored spellings), and `n` is an UNSIGNED integer of width
/// `w`, so it is at most `MAX = 2^w - 1` whatever its initial value (a parameter
/// included). Inside `lp` its ONLY write is `n = n / d` (constant `d >= 2`) or
/// `n = n >> k` (constant `k >= 1`), in a block every iteration passes, and nothing
/// writes it through an alias anywhere (no escape, no unlocatable write). So between
/// two crossings of the continue edge `n` was divided by at least `d` (or `2^k`), and
/// the `m`-th crossing reads `n <= MAX / d^(m-1)`, which is `>= 1` only while
/// `m <= digits_d(MAX)`. That is `trip`: the number of base-`d` digits of `MAX`.
/// A guard inside the loop that skips the division on some iteration fails
/// `every_iteration_passes`; a second write (a reset) fails the one-write clause.
fn shrinking_loop_driver(
    func: &VerifiableFunction,
    nest: &LoopNest,
    lp: &NaturalLoop,
) -> Option<LoopDriver> {
    if !super::terminator_presence_for(func).has_switch_int {
        return None;
    }
    for block in &func.body.blocks {
        let Terminator::SwitchInt { discr, targets, otherwise, .. } = &block.terminator else {
            continue;
        };
        if !nest.owns(lp, block.id.0) {
            continue;
        };
        // The order comparisons through the shared reader, and `n != 0` / `n == 0`
        // (which that reader leaves out) by the same shape: the block's last
        // statement defines the discriminant.
        let Some((op, lhs, rhs)) =
            crate::abstract_interp::transfer::discriminant_defining_comparison(block, discr)
                .or_else(|| {
                    let (Operand::Copy(place) | Operand::Move(place)) = discr else { return None };
                    match block.stmts.last()? {
                        Statement::Assign {
                            place: dest,
                            rvalue: Rvalue::BinaryOp(op @ (BinOp::Eq | BinOp::Ne), lhs, rhs),
                            ..
                        } if place.projections.is_empty()
                            && dest.projections.is_empty()
                            && dest.local == place.local =>
                        {
                            Some((*op, lhs, rhs))
                        }
                        _ => None,
                    }
                })
        else {
            continue;
        };
        if !matches!(op, BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge | BinOp::Eq | BinOp::Ne) {
            continue;
        }
        let mut exit_on: Option<bool> = None;
        let mut stay: Option<usize> = None;
        let mut well_formed = true;
        let arms = targets.iter().map(|(v, b)| (Some(*v), *b)).chain([(None, *otherwise)]);
        for (value, target) in arms {
            let Some(truth) =
                crate::abstract_interp::transfer::branch_truth(func, discr, value, targets)
            else {
                well_formed = false;
                break;
            };
            if lp.contains(target.0) {
                well_formed &= stay.replace(target.0).is_none();
            } else {
                well_formed &= exit_on.replace(truth).is_none();
            }
        }
        let (true, Some(exit_on), Some(stay)) = (well_formed, exit_on, stay) else { continue };
        // The comparison that holds when the loop CONTINUES.
        let op = match (exit_on, op) {
            (true, BinOp::Eq) => BinOp::Ne,
            (true, BinOp::Ne) => BinOp::Eq,
            (true, other) => crate::abstract_interp::transfer::negate_order_comparison(other),
            (false, other) => other,
        };
        let konst = |o: &Operand| const_operand_nonneg(o);
        // Which operand is `n`, given that continuing implies `n >= 1`.
        let counter_op = match op {
            BinOp::Gt if konst(rhs).is_some() => lhs,
            BinOp::Ge if konst(rhs).is_some_and(|c| c >= 1) => lhs,
            BinOp::Lt if konst(lhs).is_some() => rhs,
            BinOp::Le if konst(lhs).is_some_and(|c| c >= 1) => rhs,
            BinOp::Ne if konst(rhs) == Some(0) => lhs,
            BinOp::Ne if konst(lhs) == Some(0) => rhs,
            _ => continue,
        };
        let (Operand::Copy(cp) | Operand::Move(cp)) = counter_op else { continue };
        if !cp.projections.is_empty() {
            continue;
        }
        if has_unmodelable_write(func) {
            return None;
        }
        let Some((n, _)) = counter_local_compared_at(func, block, cp.local) else { continue };
        let Some(Ty::Int { width, signed: false }) = crate::local_ty_ref(func, n) else {
            continue;
        };
        let Some(trip) = shrinking_trip(func, nest, lp, n, *width) else { continue };
        return Some(LoopDriver { edge: (block.id.0, stay), trip });
    }
    None
}

/// The trip bound for [`shrinking_loop_driver`]'s counter `n`, or `None` when its
/// writes are not exactly one self-division inside `lp` (see there).
fn shrinking_trip(
    func: &VerifiableFunction,
    nest: &LoopNest,
    lp: &NaturalLoop,
    n: usize,
    width: u32,
) -> Option<i128> {
    let mut shrink: Option<(usize, i128)> = None;
    let poisoned =
        crate::any_local_write_candidate(func, &func.body.blocks, n, |block, item| match item {
            Some(stmt) => {
                // Review round 35: `local_write` never reports an `&mut n` (escapes are
                // asked separately), and `grow(&mut n)` inside the loop regrew `n` and
                // overflowed a counter this bound had CERTIFIED. Any escape refuses.
                if crate::stmt_escapes_local(func, stmt, n) {
                    return true;
                }
                match stmt.local_write(n) {
                    trust_types::LocalWrite::Untouched => false,
                    trust_types::LocalWrite::WholeNamed(rvalue) if lp.contains(block.id.0) => {
                        // The division may go through a single-assignment temp (`_7 = _2 /
                        // 10; …; _2 = copy _7`, the verification MIR's shape). `n` has no
                        // other write in `lp` (this scan refuses one), so the temp holds
                        // this iteration's `n`, divided.
                        //
                        // The temp must be DEFINED inside `lp` (review round 35): `let h = n
                        // / 2; while n > 0 { n = h; … }` copies a value computed once, so
                        // `n` stops shrinking and the loop need not end.
                        let rvalue = match rvalue {
                            Rvalue::Use(Operand::Copy(t) | Operand::Move(t))
                                if t.projections.is_empty()
                                    && crate::local_defs::is_single_static_assignment(
                                        func, t.local,
                                    )
                                    && crate::local_defs::unique_defining_block(func, t.local)
                                        .and_then(|b| func.body.blocks.get(b))
                                        .is_some_and(|b| lp.contains(b.id.0)) =>
                            {
                                let Some(rv) = crate::local_defs::unique_value_def(func, t.local)
                                else {
                                    return true;
                                };
                                rv
                            }
                            Rvalue::Use(_) => {
                                return true;
                            }
                            other => other,
                        };
                        let is_n = |o: &Operand| {
                            matches!(o, Operand::Copy(p) | Operand::Move(p)
                                if p.local == n && p.projections.is_empty())
                        };
                        let trip = match rvalue {
                            // The m-th crossing reads n <= MAX / d^(m-1): the base-d digits.
                            Rvalue::BinaryOp(BinOp::Div, p, d) if is_n(p) => {
                                let Some(d) = const_operand_nonneg(d).filter(|d| *d >= 2) else {
                                    return true;
                                };
                                let Ok(d) = u128::try_from(d) else {
                                    return true;
                                };
                                let mut v: u128 =
                                    if width >= 128 { u128::MAX } else { (1u128 << width) - 1 };
                                let mut digits = 0i128;
                                while v > 0 {
                                    v /= d;
                                    digits += 1;
                                }
                                digits
                            }
                            // The m-th crossing reads n < 2^(width - k(m-1)).
                            Rvalue::BinaryOp(BinOp::Shr, p, k) if is_n(p) => {
                                let Some(k) = const_operand_nonneg(k)
                                    .filter(|k| (1..i128::from(width)).contains(k))
                                else {
                                    return true;
                                };
                                (i128::from(width) + k - 1) / k
                            }
                            // `n &= n - 1` clears the lowest set bit of a NONZERO n, so
                            // between two crossings (each reading n >= 1) the popcount
                            // falls by one: at most `width` crossings.
                            Rvalue::BinaryOp(BinOp::BitAnd, a, b)
                                if (is_n(a) && is_n_minus_one(func, lp, b, n))
                                    || (is_n(b) && is_n_minus_one(func, lp, a, n)) =>
                            {
                                i128::from(width)
                            }
                            _ => {
                                return true;
                            }
                        };
                        shrink.replace((block.id.0, trip)).is_some()
                    }
                    // A whole write OUTSIDE the loop only sets the entry value, which the
                    // bound does not use (it relies on `n <= MAX` alone).
                    trust_types::LocalWrite::WholeNamed(_) | trust_types::LocalWrite::WholeOpaque
                        if !lp.contains(block.id.0) =>
                    {
                        false
                    }
                    _ => true,
                }
            }
            None => match block.terminator.local_write(n) {
                trust_types::LocalWrite::Untouched => false,
                trust_types::LocalWrite::WholeOpaque if !lp.contains(block.id.0) => false,
                _ => true,
            },
        });
    if poisoned {
        return None;
    }
    let (at, trip) = shrink?;
    if !nest.every_iteration_passes(lp, at) {
        return None;
    }
    Some(trip)
}

/// Whether `operand` is `n - 1` computed in THIS iteration of `lp`: a projection-free
/// single-assignment temp `t = n - 1`, or field 0 of `t = CheckedSub(n, 1)`, `t`
/// defined inside `lp`. [`shrinking_trip`] has refused every other write of `n` in
/// `lp`, and a temp used before its in-loop definition would be read uninitialized
/// on the first iteration, so `t` holds the current `n`, minus one.
fn is_n_minus_one(
    func: &VerifiableFunction,
    lp: &NaturalLoop,
    operand: &Operand,
    n: usize,
) -> bool {
    let (Operand::Copy(t) | Operand::Move(t)) = operand else { return false };
    let checked = match t.projections.as_slice() {
        [] => false,
        [trust_types::Projection::Field(0)] => true,
        _ => return false,
    };
    if !crate::local_defs::is_single_static_assignment(func, t.local)
        || !crate::local_defs::unique_defining_block(func, t.local)
            .and_then(|b| func.body.blocks.get(b))
            .is_some_and(|b| lp.contains(b.id.0))
    {
        return false;
    }
    let (lhs, rhs) = match crate::local_defs::unique_value_def(func, t.local) {
        Some(Rvalue::BinaryOp(BinOp::Sub, l, r)) if !checked => (l, r),
        Some(Rvalue::CheckedBinaryOp(BinOp::Sub, l, r)) if checked => (l, r),
        _ => return false,
    };
    matches!(lhs, Operand::Copy(p) | Operand::Move(p) if p.local == n && p.projections.is_empty())
        && const_operand_nonneg(rhs) == Some(1)
}

/// The driver of a loop an `Iterator::next` call drives, for
/// [`block_execution_bound`]: the call's `Some` edge, and what ONE instance of its
/// iterator can yield — a range's trip count, an array's length, or `isize::MAX` for a
/// slice of a non-ZST element. The instance must be fixed for a whole entry of the
/// loop (`trust_types::loop_nest::iterator_instance_is_fixed`): the receiver is
/// `&mut it` of a whole local nothing inside the loop writes, and nothing else aliases
/// it. `loop { let mut r = 0..10; match r.next() … }` used to take 10 from the range
/// and was proved; it never ends.
fn next_loop_driver(
    func: &VerifiableFunction,
    nest: &LoopNest,
    lp: &NaturalLoop,
) -> Option<LoopDriver> {
    if !super::terminator_presence_for(func).has_iterator_next_call {
        return None;
    }
    const FUEL: u32 = 16;
    let (dest, edge) =
        trust_types::loop_nest::next_call_driving(&func.body, nest, lp, callee_is_iterator_next)?;
    let receiver = super::iterator_yield::next_call_receiver(func, dest)?;
    let Some(Rvalue::Ref { mutable: true, place: instance }) =
        crate::local_defs::unique_value_def(func, receiver)
    else {
        return None;
    };
    if !instance.projections.is_empty()
        || !trust_types::loop_nest::iterator_instance_is_fixed(
            &func.body,
            lp,
            dest,
            receiver,
            instance.local,
        )
    {
        return None;
    }
    let trip = if let Some(origin) = next_call_range_operands(func, dest, FUEL) {
        range_trip_count_upper_bound(func, origin)?
    } else {
        let source = match loop_instance_initializer(func, lp, instance.local) {
            Some(Rvalue::Use(Operand::Copy(p) | Operand::Move(p))) if p.projections.is_empty() => {
                Operand::Copy(Place::local(p.local))
            }
            _ => Operand::Copy(Place::local(instance.local)),
        };
        iterated_source_yield_bound(func, &source, FUEL)?
    };
    Some(LoopDriver { edge, trip })
}

/// The one initializer of the iterator INSTANCE a loop's `next` advances, when its
/// only other writes are `Drop`s of it OUTSIDE the loop.
///
/// The general origin question (`iterator_origin_def`) refuses a `Drop`, and an
/// iterator that owns its items is dropped after its loop: `for x in v` over a
/// `Vec<u32>` moves `v` into an `IntoIter` whose drop glue runs at the loop exit, so
/// the trip count was never traced and a counter over it was refuted with
/// `n = usize::MAX` (ordinary-Rust completeness sweep, 2026-09-29).
///
/// THE CALLER'S ARGUMENT (`local_defs::body_unique_initializing_def` asks each caller
/// to state its own). `trust_types::loop_nest::iterator_instance_is_fixed` has
/// already established that nothing inside `lp` writes the instance and that its
/// only alias is the `next` receiver, read by that call alone. Here it has exactly
/// one whole write in the body, it is not a parameter, and its only other writes
/// are whole-place `Drop`s in blocks outside `lp`. So through every entry of `lp`
/// the instance holds the value that initializer produced, advanced only by `next`,
/// which consumes and never reseats; a drop outside the loop ends its life and is
/// not observed by any iteration. The initializer's yield bound therefore bounds
/// the `Some`s of the entry.
fn loop_instance_initializer<'f>(
    func: &'f VerifiableFunction,
    lp: &NaturalLoop,
    instance: usize,
) -> Option<&'f Rvalue> {
    if crate::local_defs::is_parameter(func, instance) {
        return None;
    }
    let mut found: Option<&Rvalue> = None;
    let poisoned = crate::any_local_write_candidate(
        func,
        &func.body.blocks,
        instance,
        |block, item| match item {
            Some(stmt) => match stmt.local_write(instance) {
                trust_types::LocalWrite::Untouched | trust_types::LocalWrite::Escape => false,
                trust_types::LocalWrite::WholeNamed(rvalue) if found.is_none() => {
                    found = Some(rvalue);
                    false
                }
                _ => true,
            },
            None => match (&block.terminator, block.terminator.local_write(instance)) {
                (_, trust_types::LocalWrite::Untouched) => false,
                (Terminator::Drop { place, .. }, trust_types::LocalWrite::Partial)
                    if place.local == instance
                        && place.projections.is_empty()
                        && !lp.contains(block.id.0) =>
                {
                    false
                }
                _ => true,
            },
        },
    );
    if poisoned {
        return None;
    }
    found
}

/// `Iterator` adapters whose iterator yields at most as many items as the one they
/// wrap — the `self` receiver, `args[0]`. `chain`, `flat_map`, `flatten`, `cycle` and
/// `by_ref` are absent on purpose: the first three yield more, `cycle` without end,
/// and `by_ref` shares its iterator with whoever else holds it.
const LENGTH_NON_INCREASING_ADAPTERS: &[&str] = &[
    "cloned",
    "copied",
    "enumerate",
    "filter",
    "filter_map",
    "fuse",
    "inspect",
    "map",
    "map_while",
    "peekable",
    "rev",
    "scan",
    "skip",
    "skip_while",
    "step_by",
    "take",
    "take_while",
    "zip",
];

/// Slice iterator constructors yielding at most `len` items (a chunk or window
/// holds at least one element) — or, for `split`, one more than that.
const SLICE_ITERATORS: &[&str] = &[
    "chunks",
    "chunks_exact",
    "chunks_exact_mut",
    "chunks_mut",
    "iter",
    "iter_mut",
    "rchunks",
    "rchunks_exact",
    "rchunks_exact_mut",
    "rchunks_mut",
    "windows",
];

/// An upper bound on how many items the iterator built from `source` can yield:
/// the length of the array, slice, `Vec` or `str` at its root, through the
/// `into_iter`, slice-iterator, `str`-view and length-non-increasing adapter calls
/// that build it (`v.iter().rev().skip(1)`, `s.bytes()`, `a.windows(2).enumerate()`).
///
/// A slice, `Vec` or `str` has a symbolic length, but at most `isize::MAX` for a
/// non-ZST element — `conjoin_slice_len_bounds`/`nonzst_slice_len_vars`
/// (`type_ranges.rs`) state the rule, and this reuses their predicate. A ZST element
/// keeps its refusal, correctly: `[(); usize::MAX]` is a valid slice and a `usize`
/// counter over it DOES overflow on the last increment. `str` is `u8` bytes, and its
/// views yield at most `len + 2` items (`is_str_view_iter_producer` states why).
///
/// Every hop is a whole-local copy or a call that is the local's only write channel
/// (`call_dest_hop`), and every intermediate `Self` type is a std adapter over a std
/// slice iterator, so each `Iterator` method is std's: a user type can override a
/// provided method only in its own `impl`, and none of its values reach here.
pub(super) fn iterated_source_yield_bound(
    func: &VerifiableFunction,
    source: &Operand,
    fuel: u32,
) -> Option<i128> {
    const ISIZE_MAX: i128 = i64::MAX as i128;
    if fuel == 0 {
        return None;
    }
    let non_zst = |elem: &Ty| trust_types::alloc_model::ty_is_definitely_nonzero_sized(elem);
    let by_type = |ty: &Ty| match ty {
        Ty::Array { len, .. } => Some(*len as i128),
        Ty::Slice { elem } | Ty::Seq { elem, .. } if non_zst(elem) => Some(ISIZE_MAX),
        Ty::Str => Some(ISIZE_MAX),
        _ => None,
    };
    let ty = crate::operand_ty_cow(func, source)?;
    let ty = match ty.as_ref() {
        Ty::Ref { inner, .. } => inner.as_ref(),
        other => other,
    };
    // A slice made by UNSIZING a fixed-size array has that array's length, which is
    // tighter than the slice's `isize::MAX` (`for &b in a.iter()` over `a: &[u8; 4]`
    // iterates `a as &[u8]`).
    if matches!(ty, Ty::Slice { .. })
        && let Some(len) = unsized_array_len(func, source)
    {
        return Some(len);
    }
    if let Some(bound) = by_type(ty) {
        return Some(bound);
    }
    let (Operand::Copy(p) | Operand::Move(p)) = source else { return None };
    if !p.projections.is_empty() {
        return None;
    }
    if let Some(rvalue) = crate::local_defs::unique_value_def(func, p.local)
        .or_else(|| iterator_origin_def(func, p.local))
    {
        return match rvalue {
            Rvalue::Ref { place, .. }
            | Rvalue::Use(Operand::Copy(place) | Operand::Move(place))
                if place.projections.is_empty() =>
            {
                iterated_source_yield_bound(func, &Operand::Copy(Place::local(place.local)), fuel - 1)
            }
            _ => None,
        };
    }
    // SLICE-INHERENT-1: the `<[T]>` recognizers below take the call's key.
    let (callee, args, callee_key) = super::iterator_yield::call_dest_hop_keyed(func, p.local)?;
    let receiver = args.first()?;
    let tail = super::alloc_bounds::method_tail(callee);
    let through =
        |extra: i128| iterated_source_yield_bound(func, receiver, fuel - 1)?.checked_add(extra);
    // Trust (2026-09-29): three std shapes whose count is known although the length-
    // non-increasing walk below cannot state it. Each callee is std's, authenticated
    // exactly as the adapters below are.
    //  * `it.take(n)` yields at most `n` items (and at most what `it` yields), so an
    //    unbounded `it` is still bounded here: `for &x in v.iter().take(3)`.
    //  * `a.chain(b)` yields `a`'s items and then `b`'s, so the SUM bounds it.
    //  * `Option::iter` yields at most one item.
    if tail == "take" && vc_callee_is_std_iter_trait_method(callee, "Iterator", "take") {
        let n = args
            .get(1)
            .and_then(|n| operand_const_int(n).or_else(|| bound_operand_upper_bound(func, n)))?;
        if n < 0 {
            return None;
        }
        return Some(match iterated_source_yield_bound(func, receiver, fuel - 1) {
            Some(inner) => inner.min(n),
            None => n,
        });
    }
    if tail == "chain" && vc_callee_is_std_iter_trait_method(callee, "Iterator", "chain") {
        let other = args.get(1)?;
        return through(0)?.checked_add(iterated_source_yield_bound(func, other, fuel - 1)?);
    }
    if matches!(tail, "iter" | "iter_mut") && callee_is_std_option_iter(callee) {
        return Some(1);
    }
    // Trust (2026-10-01): `v.iter().flatten()` (or `iter_mut`) over a slice of std
    // `Option`s or `Result`s: each `&Option<T>` / `&Result<T, E>` item yields at
    // most one value, so the flattened iterator yields at most `v.len()`. The
    // receiver must be the slice iterator ITSELF: any adapter in between could
    // change the item type to something that yields many (sweep c45).
    if tail == "flatten"
        && vc_callee_is_std_iter_trait_method(callee, "Iterator", "flatten")
        && flatten_receiver_is_slice_of_option_or_result(func, receiver)
    {
        return through(0);
    }
    if (tail == "into_iter" && callee_is_into_iter(callee))
        || (LENGTH_NON_INCREASING_ADAPTERS.contains(&tail)
            && vc_callee_is_std_iter_trait_method(callee, "Iterator", tail))
        || (SLICE_ITERATORS.contains(&tail)
            && vc_callee_is_slice_inherent(callee, callee_key, tail))
    {
        return through(0);
    }
    if tail == "split" && vc_callee_is_slice_inherent(callee, callee_key, "split") {
        return through(1);
    }
    if super::alloc_vcs::is_str_view_iter_producer(callee, tail)
        && super::alloc_vcs::producer_receiver_value_is_authenticated_sysroot(func, args)
    {
        return through(2);
    }
    None
}

/// `N` when `source` is a whole local whose one value is an UNSIZE cast of a
/// `&[T; N]`/`&mut [T; N]` (or raw) pointer to a slice pointer of the SAME element
/// type — the coercion sets the slice's length metadata to exactly `N`. The
/// element-type check is what keeps a `PtrToPtr` cast that reinterprets the unit
/// (`*const [u32; 4] as *const [u8]`) out, as in `guards::push_unsize_slice_len`.
pub(super) fn unsized_array_len(func: &VerifiableFunction, source: &Operand) -> Option<i128> {
    let (Operand::Copy(p) | Operand::Move(p)) = source else { return None };
    if !p.projections.is_empty() {
        return None;
    }
    let Rvalue::Cast(from, to_ty) = crate::local_defs::unique_value_def(func, p.local)? else {
        return None;
    };
    fn pointee(ty: &Ty) -> Option<&Ty> {
        match ty {
            Ty::Ref { inner, .. } => Some(inner.as_ref()),
            Ty::RawPtr { pointee, .. } => Some(pointee.as_ref()),
            _ => None,
        }
    }
    let Ty::Slice { elem: slice_elem } = pointee(to_ty)? else { return None };
    let from_ty = crate::operand_ty_cow(func, from)?;
    let Ty::Array { elem: array_elem, len } = pointee(from_ty.as_ref())? else {
        return None;
    };
    (slice_elem == array_elem).then_some(*len as i128)
}

/// `core::option::Option::<T>::iter` (or `iter_mut`), which yields at most one item.
/// `receiver` is the whole-local result of std `<[T]>::iter`/`iter_mut` on a
/// slice reference whose element is exactly the sysroot `Option` or `Result` ADT,
/// so each item is `&Option<_>`/`&Result<_, _>` (or `&mut`), whose std
/// `IntoIterator` yields at most one value.
fn flatten_receiver_is_slice_of_option_or_result(
    func: &VerifiableFunction,
    receiver: &Operand,
) -> bool {
    let (Operand::Copy(p) | Operand::Move(p)) = receiver else { return false };
    if !p.projections.is_empty() {
        return false;
    }
    let Some((callee, args, callee_key)) =
        super::iterator_yield::call_dest_hop_keyed(func, p.local)
    else {
        return false;
    };
    if !super::iterator_yield::vc_callee_is_slice_inherent_any(
        callee,
        callee_key,
        &["iter", "iter_mut"],
    ) {
        return false;
    }
    let Some(slice) = args.first() else { return false };
    let Some(ty) = crate::operand_ty_cow(func, slice) else { return false };
    let Ty::Ref { inner, .. } = ty.as_ref() else { return false };
    let Ty::Slice { elem } = inner.as_ref() else { return false };
    matches!(elem.as_ref(), Ty::Adt { name, .. }
        if super::witness_grounding::is_std_option_name(name)
            || super::witness_grounding::is_std_result_name(name))
}

fn callee_is_std_option_iter(callee: &str) -> bool {
    if !(callee.starts_with("core::option::") || callee.starts_with("std::option::"))
        || !callee.contains("iter")
        || callee.contains(" as ")
        || trust_types::path_has_unauthenticated_crate_stamp(callee)
    {
        return false;
    }
    matches!(
        super::iterator_yield::vc_strip_generics_cow(callee).as_ref(),
        "core::option::Option::iter"
            | "core::option::Option::iter_mut"
            | "std::option::Option::iter"
            | "std::option::Option::iter_mut"
    )
}

/// The slice whose length bounds how many items the iterator built from `source`
/// yields: [`iterated_source_yield_bound`]'s walk, through `into_iter`, the
/// length-non-increasing adapters and the slice-iterator constructors, returning the
/// slice operand at its root instead of a number. Authenticated `str::bytes` has
/// the same bound: it yields exactly one item per byte. Other `str` views and
/// `split` (which may yield `len + 2` items) are not followed.
pub(super) fn iterated_slice_of<'a>(
    func: &'a VerifiableFunction,
    source: &'a Operand,
    fuel: u32,
) -> Option<&'a Operand> {
    if fuel == 0 {
        return None;
    }
    let (Operand::Copy(p) | Operand::Move(p)) = source else { return None };
    if !p.projections.is_empty() {
        return None;
    }
    if let Some(rvalue) = crate::local_defs::unique_value_def(func, p.local)
        .or_else(|| iterator_origin_def(func, p.local))
    {
        return match rvalue {
            Rvalue::Ref { place, .. } if place.projections.is_empty() => {
                iterated_slice_of_local(func, place.local, fuel - 1)
            }
            Rvalue::Use(inner) => iterated_slice_of(func, inner, fuel - 1),
            _ => None,
        };
    }
    iterated_slice_of_local(func, p.local, fuel - 1)
}

fn iterated_slice_of_local(func: &VerifiableFunction, local: usize, fuel: u32) -> Option<&Operand> {
    if fuel == 0 {
        return None;
    }
    if let Some(Rvalue::Use(inner)) = crate::local_defs::unique_value_def(func, local) {
        return iterated_slice_of(func, inner, fuel - 1);
    }
    let (callee, args, callee_key) = super::iterator_yield::call_dest_hop_keyed(func, local)?;
    let receiver = args.first()?;
    if super::iterator_yield::vc_callee_is_slice_inherent_any(callee, callee_key, SLICE_ITERATORS) {
        return Some(receiver);
    }
    // The inherent core item pins `Self` to str; neither a same-named user
    // producer nor a rendered std path can supply this key. Keep the existing
    // licensed-length and count-destination guards at the consumer.
    if trust_types::CalleeKey::opt_is_real_sysroot(callee_key)
        && trust_types::CalleeKey::opt_is_one_of(callee_key, &[trust_types::SysrootItem::StrBytes])
        && args.len() == 1
        && super::alloc_vcs::producer_receiver_value_is_authenticated_sysroot(func, args)
    {
        return Some(receiver);
    }
    (callee_is_into_iter(callee)
        || super::iterator_yield::vc_callee_is_std_iter_trait_method_any(
            callee,
            "Iterator",
            LENGTH_NON_INCREASING_ADAPTERS,
        ))
    .then(|| iterated_slice_of(func, receiver, fuel - 1))
    .flatten()
}

/// An upper bound on how many times `block` runs in one call of `func`: the
/// product, over the natural loops containing it, of each loop's trip count, plus
/// one where the block (or the nested loop holding it) is not behind that loop's
/// driver edge. `trust_types::loop_nest` states the argument; a loop is bounded by
/// its `next` call ([`next_loop_driver`]) or, failing that, its counter test
/// ([`counter_loop_driver`]). `None` when a containing loop has neither.
pub(super) fn block_execution_bound(func: &VerifiableFunction, block: usize) -> Option<i128> {
    if super::back_edge_count_for(func) == 0 {
        return Some(1);
    }
    block_execution_bound_in(func, super::loop_nest_for(func)?.as_ref(), block)
}

/// [`block_execution_bound`] over a nest the caller already computed.
pub(super) fn block_execution_bound_in(
    func: &VerifiableFunction,
    nest: &LoopNest,
    block: usize,
) -> Option<i128> {
    nest.block_execution_bound(block, |nest, lp| {
        let accepts = |d: &LoopDriver| d.trip >= 0 && nest.crosses_every_iteration(lp, d.edge);
        if let Some(d) = next_loop_driver(func, nest, lp).filter(accepts) {
            return vec![d];
        }
        if let Some(d) = counter_loop_driver(func, nest, lp).filter(accepts) {
            return vec![d];
        }
        if let Some(d) = shrinking_loop_driver(func, nest, lp).filter(accepts) {
            return vec![d];
        }
        Vec::new()
    })
}

#[cfg(test)]
#[path = "str_bytes_count_bound_tests.rs"]
mod str_bytes_count_bound_tests;
