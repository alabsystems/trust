// Per-block definitional facts and the versioning that keeps them sound. A
// fact established in one block is only usable at a program point where the
// subject has not been redefined, so every fact is rebound to the SSA version
// live at its use site.

use super::*;

pub(super) fn v2_block_span(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
) -> SourceSpan {
    block
        .stmts
        .iter()
        .find_map(|stmt| match stmt {
            Statement::Assign { span, .. } => Some(span.clone()),
            _ => None,
        })
        .unwrap_or_else(|| func.span.clone())
}

pub(super) fn v2_is_float_operand(func: &VerifiableFunction, operand: &Operand) -> bool {
    matches!(crate::operand_ty_cow(func, operand).as_deref(), Some(trust_types::Ty::Float { .. }))
}

/// Is `divisor` a literal constant guaranteed to be nonzero? If so, we can
/// skip emitting the divzero VC entirely — it's trivially proved-safe.
pub(super) fn v2_divisor_is_nonzero_constant(divisor: &Operand) -> bool {
    match divisor {
        Operand::Constant(ConstValue::Int(v)) => *v != 0,
        Operand::Constant(ConstValue::Uint(v, _)) => *v != 0,
        Operand::Constant(ConstValue::Float(v)) => *v != 0.0,
        Operand::Constant(ConstValue::FloatBits { bits, width }) => {
            !crate::float_bits_magnitude_is_zero(*bits, *width)
        }
        _ => false,
    }
}

/// The set of `BoundsCheck` `Assert` blocks whose checked index is PROVABLY in
/// range via a loop-yield bound — a `for i in 0..s.len()` exclusive-range yield
/// ([`build_range_yield_guard_map`]) or a `for (i, _) in s.iter().enumerate()`
/// index yield ([`build_enumerate_yield_guard_map`]) that establishes
/// `index < len` for the SAME length the assert checks. The hardened
/// panic-boundary lane SKIPS emitting its `BoundsCheck` twin for these blocks,
/// the per-statement bounds VC already PROVES the access via the SAME yield fact
/// — a fact the per-statement
/// lane conjoins onto the bounds VC but the hardened twin does NOT — so without
/// the skip the twin over-refutes a provably-safe guarded index (per-statement
/// PROVED while the hardened twin FAILS).
///
/// Computed once per function (both yield maps are built a single time) and empty
/// when the function has no range/enumerate yield payloads, so this is a no-op for
/// non-looping code.
///
/// SOUND under-approximation: a block is included ONLY when a yield fact of the
/// exact form `Lt(index, len)` — `index` naming the asserted index local and `len`
/// STRUCTURALLY equal to the canonicalized asserted length — is present. An
/// unguarded / constant / derived / projected index, or a loop over a DIFFERENT
/// bound (`for i in 0..K { v[i] }`, `K != v.len()`), is NOT included and keeps its
/// refutable twin; skipping only a genuinely-in-range index can never mask a real
/// out-of-bounds panic.
pub(crate) fn v2_boundscheck_index_in_range_skip_set(
    func: &VerifiableFunction,
) -> std::collections::HashSet<BlockId> {
    let mut skip = std::collections::HashSet::new();
    let range_map = build_range_yield_guard_map(func);
    let enumerate_map = build_enumerate_yield_guard_map(func);
    if range_map.is_empty() && enumerate_map.is_empty() {
        return skip;
    }
    for block in &func.body.blocks {
        if v2_boundscheck_index_provably_in_range(func, block, &range_map, &enumerate_map) {
            skip.insert(block.id);
        }
    }
    skip
}

/// True iff the `BoundsCheck` `Assert` at `assert_block` checks an index that a
/// loop-yield fact (range or enumerate) proves is `< len` for the SAME length the
/// assert checks. See [`v2_boundscheck_index_in_range_skip_set`] for the soundness
/// argument. Returns `false` (fail-closed) for any non-`BoundsCheck` assert, a
/// non-`Lt`/`expected == false` condition, a non-plain-local index, or a length
/// that does not structurally match a yield fact's upper bound.
pub(super) fn v2_boundscheck_index_provably_in_range(
    func: &VerifiableFunction,
    assert_block: &trust_types::BasicBlock,
    range_map: &FxHashMap<BlockId, Vec<Formula>>,
    enumerate_map: &FxHashMap<BlockId, Vec<Formula>>,
) -> bool {
    const TRACE_FUEL: u32 = 16;
    let Terminator::Assert { cond, expected: true, msg: AssertMessage::BoundsCheck, .. } =
        &assert_block.terminator
    else {
        return false;
    };
    // The bounds assert is `assert(Lt(index, len))`; recover the index/len operands
    // from the `_c = Lt(index, len)` definition in this block.
    let Some((_, BinOp::Lt, index_op, len_op)) =
        v2_find_condition_binary_operands(func, assert_block, cond)
    else {
        return false;
    };
    // The index must be a plain (projection-free) local to be a loop-yield payload;
    // a constant or projected index carries no yield bound and stays refutable.
    let index_name = match index_op {
        Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => {
            place_to_var_name(func, p)
        }
        _ => return false,
    };
    // Canonicalize the checked length the SAME way the yield-fact END is
    // canonicalized (a `Len`/`PtrMetadata` temp -> `slice_len_formula(s)`), so the
    // two compare structurally exactly when they name the same slice's length.
    let checked_len = resolve_range_bound_formula(func, len_op, TRACE_FUEL);

    let yields_index_lt_checked_len = |facts: &[Formula]| -> bool {
        facts.iter().any(|fact| match fact {
            Formula::Lt(lo, hi) => {
                matches!(lo.as_ref(), Formula::Var(name, _) if *name == index_name)
                    && hi.as_ref() == &checked_len
            }
            _ => false,
        })
    };

    range_map.get(&assert_block.id).is_some_and(|facts| yields_index_lt_checked_len(facts))
        || enumerate_map
            .get(&assert_block.id)
            .is_some_and(|facts| yields_index_lt_checked_len(facts))
}

/// Build a divisor-is-zero formula for `BinaryOp(Div|Rem, _, divisor)`.
///
/// For constant divisors this reduces to `Bool(divisor == 0)` (always UNSAT
/// for nonzero constants, always SAT for literal zero). For variable divisors
/// it emits `var == 0`, which is satisfiable iff the divisor can be zero —
/// the solver finds a witness assignment and the VC is reported as Failed.
pub(super) fn v2_divisor_is_zero_formula(func: &VerifiableFunction, divisor: &Operand) -> Formula {
    match divisor {
        Operand::Constant(ConstValue::Int(v)) => Formula::Bool(*v == 0),
        Operand::Constant(ConstValue::Uint(v, _)) => Formula::Bool(*v == 0),
        Operand::Constant(ConstValue::Float(v)) => Formula::Bool(*v == 0.0),
        Operand::Constant(ConstValue::FloatBits { bits, width }) => {
            Formula::Bool(crate::float_bits_magnitude_is_zero(*bits, *width))
        }
        // A typed opaque integer constant divisor (const-generic `N`, associated
        // const, `size_of::<T>()` in a generic body) carries NO decidable value, so
        // it MIGHT be zero. Emit the satisfiable `opaque_symbol == 0` — NOT the
        // `Bool(false)` "provably nonzero" below — so the div/rem-by-zero obligation
        // stays Failed/Unknown (never falsely Proved). Reusing `operand_to_formula`'s
        // by-name opaque symbol also lets a dominating `if N != 0 { … }` guard on the
        // same operand legitimately discharge it. THIS ARM MUST PRECEDE the
        // `Operand::Constant(_) => Bool(false)` catch-all below.
        Operand::Constant(ConstValue::OpaqueScalar { .. }) => Formula::Eq(
            Box::new(operand_to_formula(func, divisor)),
            Box::new(v2_zero_formula_for_operand(func, divisor)),
        ),
        // Trust: piece #7a — a const-generic PARAM divisor (`x / N`) carries NO
        // decidable value, so it MIGHT be zero. Emit the satisfiable
        // `constparam_symbol == 0` — NOT the `Bool(false)` "provably nonzero"
        // catch-all below — so `x / N` stays Failed/Unknown, never falsely Proved.
        // Reusing `operand_to_formula`'s per-param symbol also lets a dominating
        // `if N != 0 { … }` guard legitimately discharge it. THIS ARM MUST PRECEDE
        // the `Operand::Constant(_) => Bool(false)` catch-all, exactly like the
        // `OpaqueScalar` arm above. Without it, `x / N` would false-prove.
        Operand::Constant(ConstValue::ConstParam { .. }) => Formula::Eq(
            Box::new(operand_to_formula(func, divisor)),
            Box::new(v2_zero_formula_for_operand(func, divisor)),
        ),
        // Reachability invariant for the catch-all below. `Bool(false)` means
        // "divisor provably nonzero", which discharges the div/rem-by-zero
        // obligation as Proved — so this arm must NEVER see a constant of
        // unknown value, or it would be a false PROVE. It cannot: the
        // non-numeric/unknown-valued constants are `ConstValue::OpaqueConst`
        // — minted solely for (a) f16/f128 scalars (float-typed divisions route
        // to `FloatDivisionByZero` via the `is_float` lhs-gate, never reaching an
        // integer div-by-zero fold) and (b) aggregates, which cannot be a divisor —
        // and `ConstValue::OpaqueScalar` / `ConstValue::ConstParam`, both handled
        // by the explicit arms ABOVE. Divisors with a known value lower to
        // Int/Uint/Float/FloatBits, handled above. So every constant reaching this
        // arm is nonzero by construction.
        Operand::Constant(_) => Formula::Bool(false),
        Operand::Copy(_) | Operand::Move(_) | Operand::Symbolic(_) => {
            let value = match divisor {
                Operand::Copy(_) | Operand::Move(_) => operand_to_formula(func, divisor),
                Operand::Symbolic(formula) => formula.clone(),
                _ => unreachable!(),
            };
            if let Some(Ty::Float { width }) = crate::operand_ty_cow(func, divisor).as_deref() {
                v2_float_is_zero_formula(value, *width)
            } else {
                Formula::Eq(Box::new(value), Box::new(v2_zero_formula_for_operand(func, divisor)))
            }
        }
        _ => Formula::Bool(false),
    }
}

pub(super) fn v2_float_is_zero_formula(value: Formula, width: u32) -> Formula {
    Formula::Eq(
        Box::new(v2_float_magnitude_bits(value, width)),
        Box::new(Formula::BitVec { value: 0, width: width - 1 }),
    )
}

pub(super) fn v2_float_magnitude_bits(value: Formula, width: u32) -> Formula {
    Formula::BvExtract { inner: Box::new(value), high: width - 2, low: 0 }
}

pub(super) fn v2_zero_formula_for_operand(func: &VerifiableFunction, operand: &Operand) -> Formula {
    if v2_is_float_operand(func, operand) {
        Formula::BitVec { value: 0, width: 64 }
    } else if let Some(Sort::BitVec(width)) = crate::operand_sort(func, operand) {
        Formula::BitVec { value: 0, width }
    } else {
        match operand {
            Operand::Symbolic(formula) => v2_zero_formula_for_formula(formula),
            _ => Formula::Int(0),
        }
    }
}

pub(super) fn v2_zero_formula_for_formula(formula: &Formula) -> Formula {
    if let Some(width) = crate::formula_bit_width(formula) {
        Formula::BitVec { value: 0, width }
    } else {
        Formula::Int(0)
    }
}

#[cfg(test)]
pub(super) fn v2_guard_targets_matching(
    func: &VerifiableFunction,
    pred: impl Fn(&AssertMessage) -> bool,
) -> std::collections::HashSet<BlockId> {
    func.body
        .blocks
        .iter()
        .filter_map(|bb| match &bb.terminator {
            Terminator::Assert { msg, target, .. } if pred(msg) => Some(*target),
            _ => None,
        })
        .collect()
}

#[cfg(test)]
pub(crate) fn v2_overflow_guard_targets(
    func: &VerifiableFunction,
) -> std::collections::HashSet<BlockId> {
    v2_guard_targets_matching(func, |msg| {
        matches!(msg, AssertMessage::Overflow(BinOp::Div | BinOp::Rem | BinOp::Shl | BinOp::Shr))
    })
}

/// The sole `BoundsCheck` assert per normal-success target, as an index into
/// `func.body.blocks`. A target with TWO OR MORE candidate `BoundsCheck`
/// asserts is ABSENT: among multiple candidates, target identity cannot say
/// which (if either) guarded a given row, and ambiguity is never suppression
/// authority — the rows emit, and a dominating path guard may still discharge
/// them downstream (over-report is the fail-closed direction).
pub(super) fn v2_sole_bounds_assert_by_target(
    func: &VerifiableFunction,
) -> FxHashMap<BlockId, usize> {
    let mut candidates: FxHashMap<BlockId, Option<usize>> = FxHashMap::default();
    for (block_index, bb) in func.body.blocks.iter().enumerate() {
        if let Terminator::Assert { msg: AssertMessage::BoundsCheck, target, .. } = &bb.terminator {
            candidates.entry(*target).and_modify(|slot| *slot = None).or_insert(Some(block_index));
        }
    }
    candidates.into_iter().filter_map(|(target, slot)| slot.map(|i| (target, i))).collect()
}

/// Whether the `BoundsCheck` assert at `assert_block` is EXACTLY BOUND to every
/// index-bounds row the rvalue lane would emit for `place` at
/// `use_block.stmts[use_stmt_index]` — the only condition under which that lane
/// may suppress those rows.
///
/// This replaces the deleted `v2_bounds_guard_targets` bare-target set. Target
/// identity alone ("some `BoundsCheck` assert jumps here") never proved that
/// the assert guarded THIS operation and THESE operands: a `Lt(_i, len_A)`
/// assert whose success edge enters a block that also indexes a DIFFERENT
/// collection `B` (with index `_j`, or even the same `_i` against a different
/// length) suppressed B's rows on A's authority — the same identity weakness
/// the Overflow/OverflowNeg and Div/Rem lanes already had removed (see
/// `v2_divrem_overflow_assert_exactly_bound` and the plain-arm comment in
/// `safety.rs`). The binding demanded here, per row:
///
///  * SOLE ENTRY: the assert's normal success edge is the only way into
///    `use_block` — no other predecessor edge (cleanup edges included), not the
///    assert's own unwind edge, and not the entry block. A row reachable around
///    the assert is a row the assert does not cover on some execution;
///  * the assert cond's live definition, in the assert's OWN block, is the
///    canonical `Lt(index, bound)` with `expected: true` and both operands
///    projection-free, alias-stable, and un-rewritten through the terminator
///    (`v2_find_condition_binary_operands`);
///  * the compared index IS the row's index local — an UNSIGNED one (a signed
///    row carries an `index < 0` disjunct the assert never checked) — and
///    reaches the indexed statement un-rewritten;
///  * the compared bound IS the row's collection length
///    ([`v2_assert_len_binding_holds`]).
///
/// `ConstantIndex`/`Subslice` rows are never suppressible here: a runtime
/// `Lt(index, len)` check is not authority over a constant-offset obligation.
/// Any other shape — ambiguity, rewrite, aliasing, non-canonical polarity,
/// multiple candidate asserts ([`v2_sole_bounds_assert_by_target`]) — keeps the
/// row.
pub(super) fn v2_bounds_assert_exactly_covers_place(
    func: &VerifiableFunction,
    assert_block: &trust_types::BasicBlock,
    use_block: &trust_types::BasicBlock,
    use_stmt_index: usize,
    place: &Place,
) -> bool {
    use std::borrow::Cow;
    // The entry block also executes with NO predecessor edge at all; the assert
    // cannot cover that execution's rows.
    if use_block.id.0 == 0 {
        return false;
    }
    // The assert's FAILURE/cleanup edge runs exactly when the index is out of
    // bounds — it must not re-enter the block whose rows it would suppress.
    if assert_block.terminator.unwind_cleanup_target() == Some(use_block.id) {
        return false;
    }
    // Sole-entry: no OTHER block's terminator may reach `use_block`
    // (`exit_targets` lists cleanup edges too).
    let bypassed = func.body.blocks.iter().any(|b| {
        b.id != assert_block.id
            && b.terminator.exit_targets().iter().any(
                |t| matches!(t, trust_types::ClauseTarget::Block(succ) if *succ == use_block.id),
            )
    });
    if bypassed {
        return false;
    }

    // Walk the projections exactly as `check_direct_projection_load` does, so
    // "every row" here is byte-for-byte the set of rows the builder would emit.
    let Some(mut ty) = crate::local_ty_ref(func, place.local).map(Cow::Borrowed) else {
        return false;
    };
    let mut prefix = Place::local(place.local);
    let mut any_row_bound = false;
    for projection in &place.projections {
        match projection {
            Projection::Index(index_local) => {
                if rvalue_safety::collection_len_formula(func, &prefix, ty.as_ref()).is_some() {
                    if !v2_bounds_assert_binds_index_row(
                        func,
                        assert_block,
                        use_block,
                        use_stmt_index,
                        *index_local,
                        &prefix,
                        ty.as_ref(),
                    ) {
                        return false;
                    }
                    any_row_bound = true;
                }
            }
            Projection::ConstantIndex { .. } | Projection::Subslice { .. } => {
                if rvalue_safety::collection_len_formula(func, &prefix, ty.as_ref()).is_some() {
                    return false;
                }
            }
            _ => {}
        }
        let Some(next_ty) = crate::step_place_ty_cow(ty, projection) else {
            // The row builder stops at an unresolvable step too: no further rows.
            break;
        };
        prefix.projections.push(projection.clone());
        ty = next_ty;
    }
    any_row_bound
}

/// One index-bounds row's exact binding to the assert: canonical `Lt` cond,
/// index identity, and length correspondence. See
/// [`v2_bounds_assert_exactly_covers_place`].
fn v2_bounds_assert_binds_index_row(
    func: &VerifiableFunction,
    assert_block: &trust_types::BasicBlock,
    use_block: &trust_types::BasicBlock,
    use_stmt_index: usize,
    index_local: usize,
    collection: &Place,
    collection_ty: &Ty,
) -> bool {
    // Canonical polarity ONLY. An `expected: false` BoundsCheck succeeds when
    // its condition is FALSE — its success edge carries no `index < len`
    // evidence whatsoever.
    let Terminator::Assert {
        cond, expected: true, msg: AssertMessage::BoundsCheck, target, ..
    } = &assert_block.terminator
    else {
        return false;
    };
    if *target != use_block.id {
        return false;
    }
    let Some((cmp_index, BinOp::Lt, index_op, bound_op)) =
        v2_find_condition_binary_operands(func, assert_block, cond)
    else {
        return false;
    };
    // Index identity: the compared operand IS the row's index local...
    let (Operand::Copy(index_place) | Operand::Move(index_place)) = index_op else {
        return false;
    };
    if !index_place.projections.is_empty() || index_place.local != index_local {
        return false;
    }
    // ...an UNSIGNED one (`Lt(i, len)` says nothing about a signed row's
    // `i < 0` disjunct)...
    if crate::operand_ty_cow(func, index_op).as_deref().is_some_and(Ty::is_signed) {
        return false;
    }
    // ...that reaches the indexed statement un-rewritten. The success edge
    // enters `use_block` directly (sole-entry, checked by the caller), so the
    // only statements between the comparison and the read are the assert
    // block's tail (`v2_find_condition_binary_operands` refuses rewrites
    // there) and the use block's prefix, scanned here.
    let index_name = place_to_var_name(func, index_place);
    if (0..use_stmt_index.min(use_block.stmts.len()))
        .any(|k| stmt_writes_name(func, use_block, k, &index_name))
    {
        return false;
    }
    v2_assert_len_binding_holds(func, assert_block, cmp_index, bound_op, collection, collection_ty)
}

/// Whether the assert cond's BOUND operand is exactly this row's collection
/// length. Three canonical shapes, all resolved in the assert's OWN block:
///
///  * `bound = Len(<collection>)` — the length of the EXACT place the row
///    indexes;
///  * `bound = PtrMetadata(p)` where `p` is the fat pointer whose pointee the
///    row indexes — read directly (`PtrMetadata(copy s)` for a `(*s)[i]` row;
///    `slice_metadata_place` pops the deref) or through the canonical rustc
///    reborrow chain `_p = &raw (*s); bound = PtrMetadata(_p)` (the reborrow's
///    metadata IS the metadata of the exact place it reborrows);
///  * a constant (bare, or a constant-defined temp) equal to the TYPE-derived
///    array length (`Formula::Int(N)` / the const-generic param symbol).
///
/// A type-carried length (`[T; N]` / `[T; const N]`) cannot change with the
/// collection's value. A slice/str length is VALUE metadata, so the binding
/// additionally demands the fat-pointer root REBIND-FREE
/// ([`v2_slice_metadata_root_can_rebind`]) — element stores through the
/// pointer never move its length, but a rebind of the pointer itself would
/// decouple the checked length from the indexed access. Everything else — a
/// chained copy, a foreign local, a bound defined in another block — is NOT a
/// length binding: fail closed.
fn v2_assert_len_binding_holds(
    func: &VerifiableFunction,
    assert_block: &trust_types::BasicBlock,
    cmp_index: usize,
    bound_op: &Operand,
    collection: &Place,
    collection_ty: &Ty,
) -> bool {
    let Some(row_len) = rvalue_safety::collection_len_formula(func, collection, collection_ty)
    else {
        return false;
    };
    let bound_place = match bound_op {
        // A literal bound is exact only against a type-derived length.
        Operand::Constant(_) => return v2_const_matches_len(func, bound_op, &row_len),
        Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => p,
        _ => return false,
    };
    let bound_name = place_to_var_name(func, bound_place);
    for k in (0..cmp_index.min(assert_block.stmts.len())).rev() {
        if !stmt_writes_name(func, assert_block, k, &bound_name) {
            continue;
        }
        let Statement::Assign { place, rvalue, .. } = &assert_block.stmts[k] else {
            return false;
        };
        if place != bound_place {
            return false;
        }
        match rvalue {
            Rvalue::Len(p) if p == collection => {}
            Rvalue::UnaryOp(
                trust_types::UnOp::PtrMetadata,
                Operand::Copy(p) | Operand::Move(p),
            ) if *p == rvalue_safety::slice_metadata_place(func, collection)
                || v2_is_reborrow_of(func, assert_block, k, p, collection) => {}
            Rvalue::Use(op @ Operand::Constant(_)) => {
                return v2_const_matches_len(func, op, &row_len);
            }
            _ => return false,
        }
        if matches!(collection_ty, Ty::Array { .. } | Ty::SymArray { .. }) {
            return true;
        }
        // VALUE metadata: the length read and the indexed access must see the
        // same fat pointer.
        return !v2_slice_metadata_root_can_rebind(func, collection.local);
    }
    false
}

/// Whether `pointer`'s live definition before `assert_block.stmts[before]` is
/// exactly the canonical reborrow `pointer = &<collection>` /
/// `&raw <collection>` of the EXACT place the row indexes — the shape rustc
/// emits for slice indexing (`_p = &raw const (*s); _len = PtrMetadata(_p)`).
/// The reborrow's fat-pointer metadata is by construction the metadata of the
/// place it reborrows, so `PtrMetadata(pointer)` reads the collection's length.
/// The reverse scan finds the LATEST write, so an interposed rewrite of the
/// temp is itself the found statement and fails the shape check; a mut-borrowed
/// or multi-written temp is refused outright (`value_local_is_unstable`).
fn v2_is_reborrow_of(
    func: &VerifiableFunction,
    assert_block: &trust_types::BasicBlock,
    before: usize,
    pointer: &Place,
    collection: &Place,
) -> bool {
    if !pointer.projections.is_empty() || guards::value_local_is_unstable(func, pointer.local) {
        return false;
    }
    let pointer_name = place_to_var_name(func, pointer);
    for k in (0..before.min(assert_block.stmts.len())).rev() {
        if !stmt_writes_name(func, assert_block, k, &pointer_name) {
            continue;
        }
        let Statement::Assign { place, rvalue, .. } = &assert_block.stmts[k] else {
            return false;
        };
        if place != pointer {
            return false;
        }
        return matches!(
            rvalue,
            Rvalue::Ref { place: reborrowed, .. } | Rvalue::AddressOf(_, reborrowed)
                if reborrowed == collection
        );
    }
    false
}

/// Whether the fat-pointer/slice METADATA of root `local` can be rebound
/// anywhere in the function. Pointee writes — any place whose projections start
/// with `Deref` (`(*s)[i] = v`, `*s = ..`) — copy element data through the
/// pointer and can NEVER move its length metadata; likewise a reborrow of the
/// pointee (`&mut (*s)`, `&raw (*s)`) hands out element access only. What CAN
/// rebind the metadata is a write to the pointer local itself: a non-`Deref`
/// `Assign`/`SetDiscriminant`/`Deinit` dest, a `Call` destination, or a
/// mutable/raw borrow OF THE POINTER LOCAL (a channel through which `s = other`
/// can happen invisibly). This is deliberately narrower than
/// `value_local_is_unstable`, whose whole-VALUE staleness question also counts
/// element stores — correct for value facts, needlessly fail-closed for a
/// length that element stores cannot touch.
fn v2_slice_metadata_root_can_rebind(func: &VerifiableFunction, local: usize) -> bool {
    let names_pointer_itself = |place: &Place| {
        place.local == local && place.projections.first() != Some(&Projection::Deref)
    };
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            match stmt {
                Statement::Assign { place, rvalue, .. } => {
                    if names_pointer_itself(place) {
                        return true;
                    }
                    match rvalue {
                        Rvalue::Ref { mutable: true, place: bp } | Rvalue::AddressOf(_, bp)
                            if names_pointer_itself(bp) =>
                        {
                            return true;
                        }
                        _ => {}
                    }
                }
                Statement::SetDiscriminant { place, .. } | Statement::Deinit { place }
                    if names_pointer_itself(place) =>
                {
                    return true;
                }
                _ => {}
            }
        }
        if let Terminator::Call { dest, .. } = &block.terminator
            && names_pointer_itself(dest)
        {
            return true;
        }
    }
    false
}

/// A constant bound equals the row's length only when it renders to the EXACT
/// length term — the concrete `Int(N)` of a `[T; N]` or the per-param symbol of
/// a `[T; const N]`. Value metadata (a slice length) has no constant identity.
fn v2_const_matches_len(func: &VerifiableFunction, bound: &Operand, row_len: &Formula) -> bool {
    const_int_value(bound).map(Formula::Int).as_ref() == Some(row_len)
        || &operand_to_formula(func, bound) == row_len
}

pub(super) fn v2_formula_with_block_defs(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    formula: Formula,
) -> Formula {
    v2_formula_with_block_defs_at_point(func, block, block.stmts.len(), formula)
}

/// Conjoin same-block definition facts onto a VC `formula`, with both sides
/// versioned at the staleness-class S2c granularity:
///
///   * the VC body (`formula`, the bare obligation goal) is renamed at the
///     USE-POINT `end` (the program point the obligation is taken at);
///   * each block-def is renamed at ITS OWN establish point
///     (`version_block_def_at_establish`).
///
/// A LIVE def carries the same `#token` as the body's reference (nothing rewrote
/// the place between its establish point and `end`), so they unify. A def whose
/// subject is HAVOCED or reassigned before `end` carries a stale `#token` that
/// the body's `#end` reference does not match — the kill's drop, by
/// name-disjointness, at statement granularity. `combine_relevant_block_defs`
/// then prunes the disconnected (stale) def as irrelevant.
pub(super) fn v2_formula_with_block_defs_at_point(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    end: usize,
    formula: Formula,
) -> Formula {
    v2_formula_with_block_defs_at_point_recorded(func, block, end, formula).0
}

/// As [`v2_formula_with_block_defs_at_point`], but also returns the pieces the
/// authenticated-obligation recorder needs: the terminal-versioned `body` (the raw
/// violation as it appears INSIDE the returned formula) and the block-defs KEPT (in
/// conjoin order). Trust: seeding `ObligationRecord.body = renamed_body` and
/// `wrappers = [ConjoinFactsLast { facts: kept }]` (omitted when `kept` is empty)
/// reconstructs the returned formula bit-for-bit — the body is recorded at the
/// point the emitter builds it, NOT re-parsed from the finished formula.
pub(super) fn v2_formula_with_block_defs_at_point_recorded(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    end: usize,
    formula: Formula,
) -> (Formula, Formula, Vec<Formula>) {
    let sv = StmtVersionCtx::build(func);
    let body = version_rename_at(&formula, &sv, func, block.id, end);
    // Trust (ARM-B): the VERSIONED extract keeps pure place-read defs across a
    // later same-block clobber — sound HERE ONLY because every def below is
    // stamped at its establish point (`version_block_def_at_establish`), so the
    // kept def pins the PRE-write value by name. This is what ties a closure's
    // `&mut`-upvar guard read to its use read (`_2 == _1.0*`, `_4 == _1.0*`
    // with no write between) — the last unified read-tie instance.
    let mut defs = guards::extract_block_definitions_until_versioned(func, block, end);
    defs.extend(extract_set_discriminant_definitions_until(func, block, end));
    // The same-block deref-store-havoc kill (`drop_havoced_block_defs`) is DELETED
    // here: the establish-point versioning below subsumes it — a def whose subject
    // is havoced by an opaque deref-store carries a `#establish` token that the
    // terminal-versioned `body` does not match, so it cannot constrain the
    // post-havoc obligation (the drop, by name-disjointness). Proven 0-residual by
    // `block_def_establish_subsumes_kill` across the corpus + battery, and the
    // falsification gate's 65 mutants stay refuted with the kill gone. (The
    // guard-THREADING lane in `build_semantic_guard_map` still uses the kill — that
    // is a separate staleness mechanism, not subsumed by this same-block versioning.)
    let defs: Vec<Formula> = defs
        .into_iter()
        .map(|d| version_block_def_at_establish(&sv, func, block, end, d))
        .collect();
    let (combined, kept) = combine_relevant_block_defs_recorded(defs, body.clone());
    (combined, body, kept)
}

/// The place name a block-definition fact DEFINES: the top-level lhs of an `Eq`
/// or a range comparison (`Lt`/`Le`/`Gt`/`Ge`), with any `#token` stripped.
/// `None` for shapes with no single defined subject.
pub(super) fn block_def_subject(def: &Formula) -> Option<String> {
    let lhs = match def {
        Formula::Eq(l, _)
        | Formula::Lt(l, _)
        | Formula::Le(l, _)
        | Formula::Gt(l, _)
        | Formula::Ge(l, _) => l,
        _ => return None,
    };
    match &**lhs {
        Formula::Var(name, _) => Some(name.split('#').next().unwrap_or(name).to_string()),
        // Float value-definitions wrap the destination var in `FpFromBits` to
        // lift its bit pattern into FP space (lhs = FpFromBits { bits: Var(dest) }).
        // The subject is the inner var — peek through so the staleness /
        // clobber-dedup / versioning machinery recognizes a def of `dest`.
        // (Without this a stale FP def could survive a reassignment of `dest`
        // and discharge a goal about the new value — a false-PROVE.)
        Formula::FpFromBits { bits, .. } => match &**bits {
            Formula::Var(name, _) => Some(name.split('#').next().unwrap_or(name).to_string()),
            _ => None,
        },
        _ => None,
    }
}

/// The statement index in `block` that ESTABLISHES `base`: the latest real
/// Assign/SetDiscriminant in `stmts[..end]` whose destination IS `base`. An
/// opaque deref-store is EXCLUDED — it HAVOCS `base` (the version oracle counts
/// it as a write, via `stmt_writes_name`) but does not textually DEFINE it, so it
/// is not an establish point. `None` when no in-block statement defines `base`.
pub(super) fn block_def_establish_stmt(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    base: &str,
    end: usize,
) -> Option<usize> {
    // `dest` establishes `base` iff it IS `base` or an ANCESTOR of it: a whole-local
    // aggregate write `agg = (..)` establishes the field def `agg.0`. A DESCENDANT
    // write (`agg.0.1 = w`) is deliberately NOT an establish point — it is a later
    // partial update that makes the `agg.0` def stale, which the terminal token
    // already reflects.
    let establishes = |dest: &str| -> bool {
        dest == base
            || (base.len() > dest.len()
                && base.starts_with(dest)
                && matches!(base.as_bytes()[dest.len()], b'.' | b'[' | b'*'))
            // Trust (P0 false-refutation, 2026-07-02): a borrow/raw-pointer write
            // `_6 = &raw const *dst` ESTABLISHES the synthetic metadata def
            // `_6__slice_len == dst__slice_len` that the block-def extraction
            // emits for it. Without this the tie fact has no establish point,
            // stays BARE under establish-versioning, and is name-disjoint from
            // the `#token`-versioned `PtrMetadata` read it must discharge — the
            // guarded `&mut [T]` index false-refutation. Must stay consistent
            // with `stmt_writes_name` (`write_covers_derived_slice_len`), which
            // mints the read token this def must match.
            || write_covers_derived_slice_len(dest, base)
    };
    (0..end.min(block.stmts.len())).rev().find(|&k| match &block.stmts[k] {
        Statement::Assign { place, .. } => {
            let is_opaque_deref =
                matches!(place.projections.first(), Some(trust_types::Projection::Deref))
                    && crate::deref_pointer_is_opaque(func, place.local);
            !is_opaque_deref && establishes(&crate::place_to_var_name(func, place))
        }
        Statement::SetDiscriminant { place, .. } => {
            establishes(&crate::place_to_var_name(func, place))
        }
        _ => false,
    })
}

/// Version a block-definition fact at ITS OWN establish point: every operand READ
/// is renamed to its value just BEFORE the defining statement `k` (read-point
/// `k`), and the DEFINED subject (top-level lhs) is renamed to its value just
/// AFTER `k` (point `k+1`). This pins the fact to the program point that produced
/// it, so the whole-VC terminal rename SKIPS it (already `#`-versioned) and a fact
/// about a subsequently-HAVOCED/reassigned place names a DIFFERENT variable than
/// the terminal-versioned body.
///
/// A self-referential rhs (`x = x + 1`) is handled correctly: the rhs `x` stays
/// at the old value (read-point `k`) while the lhs `x` advances to the new value
/// (`k+1`), so the fact is `x_new = x_old + 1`, never the unsatisfiable `x = x+1`.
///
/// Defs with no recoverable subject, or already-versioned array term defs
/// (`arr$L$vN`, their own version scheme), pass through unchanged.
pub(super) fn version_block_def_at_establish(
    sv: &StmtVersionCtx,
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    end: usize,
    def: Formula,
) -> Formula {
    let Some(subj) = block_def_subject(&def) else { return def };
    if subj.starts_with("arr$") {
        return def;
    }
    // A deref subject `x*` is established by the borrow `x = &..` of its base `x`.
    let base = subj.strip_suffix('*').unwrap_or(&subj).to_string();
    let Some(k) = block_def_establish_stmt(func, block, &base, end) else { return def };
    // 1. all reads at the read-point k (values BEFORE the defining write).
    let read_versioned = version_rename_at(&def, sv, func, block.id, k);
    // 2. re-version the DEFINED subject (top-level lhs) to k+1 (value AFTER it).
    let new_tok = sv.version_token_at(func, block.id, k + 1, &subj);
    rebind_block_def_subject(read_versioned, &subj, new_tok)
}

/// Replace the top-level lhs subject Var of a block-def fact with `subj` carrying
/// `tok` (`subj#tok`, or bare `subj` when `tok` is None). Only the DEFINED
/// position (operand 0 of the top-level Eq/range comparison) is touched; reads in
/// the rhs keep their read-point versions.
pub(super) fn rebind_block_def_subject(def: Formula, subj: &str, tok: Option<String>) -> Formula {
    // Rewrite the subject var to `subj` (optionally version-tokened `subj#tok`),
    // preserving an `FpFromBits` wrapper if the lhs is a float value-definition
    // (`FpFromBits { bits: Var(subj) }`). Rewriting the INNER var (not the
    // wrapper) is required so re-versioning of a reassigned float dest applies to
    // the FP def too — see `block_def_subject`.
    fn rewrite_lhs(l: &Formula, subj: &str, tok: &Option<String>) -> Formula {
        match l {
            Formula::Var(_, s) => match tok {
                Some(t) => Formula::Var(format!("{subj}#{t}"), s.clone()),
                None => Formula::Var(subj.to_string(), s.clone()),
            },
            Formula::FpFromBits { bits, eb, sb } => Formula::FpFromBits {
                bits: Box::new(rewrite_lhs(bits, subj, tok)),
                eb: *eb,
                sb: *sb,
            },
            other => other.clone(),
        }
    }
    match def {
        Formula::Eq(l, r) => Formula::Eq(Box::new(rewrite_lhs(&l, subj, &tok)), r),
        Formula::Lt(l, r) => Formula::Lt(Box::new(rewrite_lhs(&l, subj, &tok)), r),
        Formula::Le(l, r) => Formula::Le(Box::new(rewrite_lhs(&l, subj, &tok)), r),
        Formula::Gt(l, r) => Formula::Gt(Box::new(rewrite_lhs(&l, subj, &tok)), r),
        Formula::Ge(l, r) => Formula::Ge(Box::new(rewrite_lhs(&l, subj, &tok)), r),
        other => other,
    }
}

/// The statement that ESTABLISHES a block's assert-passed semantics: the
/// `CheckedBinaryOp` whose `.1` overflow flag the block's `Assert` terminator
/// tests. Its no-overflow facts are about the operand values READ there.
pub(super) fn assert_passed_establish_stmt(
    _func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
) -> Option<usize> {
    let Terminator::Assert { cond, expected: false, .. } = &block.terminator else {
        return None;
    };
    let p = match cond {
        Operand::Copy(p) | Operand::Move(p) => p,
        _ => return None,
    };
    if !matches!(p.projections.as_slice(), [trust_types::Projection::Field(1)]) {
        return None;
    }
    let tuple_local = p.local;
    block.stmts.iter().position(|s| {
        matches!(s, Statement::Assign { place, rvalue: Rvalue::CheckedBinaryOp(..), .. }
            if place.local == tuple_local && place.projections.is_empty())
    })
}

/// Version a THREADED assert-passed fact at its establish point. A definitional
/// fact (`_N.0 == result`) is pinned via `version_block_def_at_establish`; a purely
/// RELATIONAL fact (`min <= result`, operand ranges) has every operand versioned at
/// the `CheckedBinaryOp` read-point `k`. Entry params stay BARE (and ride the
/// exemption); an operand reassigned afterward names a different variable.
pub(super) fn version_assert_passed_fact(
    sv: &StmtVersionCtx,
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    k: usize,
    fact: Formula,
) -> Formula {
    if block_def_subject(&fact).is_some() {
        version_block_def_at_establish(sv, func, block, block.stmts.len(), fact)
    } else {
        version_rename_at(&fact, sv, func, block.id, k)
    }
}

/// Version a THREADED fact established by the block's TERMINATOR (a modeled
/// total-call / min / max / clamp bound on a `Call` dest). The terminator runs
/// after every statement, so the dest is pinned to the terminator marker `s{b}_t`
/// (matching the terminator-aware OUT in the inter-block oracle); other operands are
/// read at the block terminal. A successor that REASSIGNS the dest reads a distinct
/// token, disconnecting the stale bound.
pub(super) fn version_terminator_dest_fact(
    sv: &StmtVersionCtx,
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    dest_name: &str,
    fact: Formula,
) -> Formula {
    let read_versioned = version_rename_at(&fact, sv, func, block.id, block.stmts.len());
    let term_tok = format!("s{}_t", block.id.0);
    read_versioned.map(&mut |node| match node {
        Formula::Var(name, sort) if name.split('#').next() == Some(dest_name) => {
            Formula::Var(format!("{dest_name}#{term_tok}"), sort)
        }
        other => other,
    })
}

/// SOUNDNESS WITNESS for deleting `drop_havoced_block_defs`. The kill drops every
/// block-def whose free variables overlap a deref-store-havoc name. The
/// establish-point versioning makes that drop redundant for the DANGEROUS case (a
/// def whose SUBJECT is havoced: a stale value that could false-prove a post-havoc
/// obligation) — such a def is name-disjoint from the terminal-versioned body
/// exactly when it is stale (`est ≠ term`), and correctly CONNECTS when it is a
/// fresh post-havoc def (`est == term`). The non-dangerous case (only an RHS read
/// is havoced) is kept by the versioning at the read's pre-havoc value — sound,
/// and strictly more precise than the kill's conservative drop.
///
/// This returns the count of defs the kill drops that the versioning CANNOT pin
/// to an establish point yet whose SUBJECT is havoced — i.e. the residual for
/// which the kill would still be load-bearing. `0` across the corpus + battery ⟹
/// the versioning subsumes the kill and it can be deleted.
#[cfg(test)]
pub(crate) fn block_def_establish_subsumes_kill(func: &VerifiableFunction) -> usize {
    let mut residual = 0usize;
    for block in &func.body.blocks {
        let end = block.stmts.len();
        let havoc: FxHashSet<String> = deref_store_havoc_names(func, block).into_iter().collect();
        if havoc.is_empty() {
            continue;
        }
        let mut defs = guards::extract_block_definitions_until(func, block, end);
        defs.extend(extract_set_discriminant_definitions_until(func, block, end));
        for d in &defs {
            if formula_survives_redefs(d, &havoc) {
                continue; // the kill KEEPS this def — nothing to subsume.
            }
            let Some(subj) = block_def_subject(d) else {
                residual += 1; // kill drops a subject-less def; versioning can't pin it.
                continue;
            };
            let subj_havoced = havoc.iter().any(|h| place_names_overlap(&subj, h));
            if !subj_havoced {
                continue; // RHS-only havoc: versioning keeps the def soundly.
            }
            let base = subj.strip_suffix('*').unwrap_or(&subj).to_string();
            let pinned = !subj.starts_with("arr$")
                && block_def_establish_stmt(func, block, &base, end).is_some();
            if !pinned {
                residual += 1; // havoced subject the versioning could not establish-pin.
            }
        }
    }
    residual
}

// `drop_havoced_block_defs` (the deref-store-havoc staleness kill) was DELETED:
// both the same-block conjoin lane (`v2_formula_with_block_defs_at_point`) and the
// inter-block threading lane (`build_semantic_guard_map`) now establish-version
// their defs (`version_block_def_at_establish`) so a havoced subject is name-
// disjoint from the post-havoc read — the drop, achieved by the statement-granular
// version oracle. Subsumption is proven 0-residual by
// `block_def_establish_subsumes_kill`.
pub(super) fn v2_formula_with_block_defs_before_stmt(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    stmt_index: usize,
    formula: Formula,
) -> Formula {
    // Mid-block obligation: the use-point IS `stmt_index` (defs and body both
    // versioned up to there).
    v2_formula_with_block_defs_at_point(func, block, stmt_index, formula)
}

/// Attach only the block-definition conjuncts whose left-hand-side variables are
/// transitively referenced by the VC formula.
///
/// Block definitions capture the dataflow of an entire basic block, so a typical
/// VC formula sees defs for many locals (including ones it doesn't care about).
/// Irrelevant defs hurt the solver in two ways:
///
///   1. They expand the search space — more variables to reason about.
///   2. When the irrelevant def crosses theories (e.g., a bitwise-AND lowered as
///      `bv2nat(bvand(int2bv(x), int2bv(y)))`), it injects a hard mixed-Int/BV
///      subterm into a formula that would otherwise live in a single theory.
///      ay-incremental returns `unknown` on those mixed formulas (#leb128-shift),
///      so dropping irrelevant defs is the difference between Proved/Failed
///      results and Unknown.
///
/// This is a sound optimization: dropping conjuncts that share no variables with
/// the rest of the formula cannot change satisfiability.
/// Attach the relevant block-defs AND return the ones KEPT, in the exact order they
/// are conjoined (before `formula`). Trust: the
/// authenticated-obligation recorder seeds a `ConjoinFactsLast { facts: kept }`
/// wrapper from this so `reconstruct(body, [wrapper]) == And([kept.., body])`
/// reproduces the combined formula bit-for-bit. An empty `kept` means the combined
/// formula IS `formula` unchanged (no wrapper is recorded).
pub(super) fn combine_relevant_block_defs_recorded(
    defs: Vec<Formula>,
    formula: Formula,
) -> (Formula, Vec<Formula>) {
    if defs.is_empty() {
        return (formula, Vec::new());
    }

    let mut needed: FxHashSet<String> = FxHashSet::default();
    collect_formula_var_names(&formula, &mut needed);

    // Walk defs in reverse so a def of `_4 = _3` pulls in `_3`'s def too.
    let mut keep_rev: Vec<Formula> = Vec::new();
    for def in defs.into_iter().rev() {
        let mut def_vars: FxHashSet<String> = FxHashSet::default();
        collect_formula_var_names(&def, &mut def_vars);
        // Heuristic: a def is relevant iff its destination (the lhs of the top-level Eq, if any)
        // is in `needed`, OR any of its free variables intersects `needed`. Either way we add
        // every free variable of the def to `needed` so deeper dependencies are picked up next.
        let intersects = def_vars.iter().any(|name| needed.contains(name));
        if intersects {
            for name in def_vars {
                needed.insert(name);
            }
            keep_rev.push(def);
        }
    }

    if keep_rev.is_empty() {
        return (formula, Vec::new());
    }

    let kept: Vec<Formula> = keep_rev.into_iter().rev().collect();
    let mut conjuncts: Vec<Formula> = kept.clone();
    conjuncts.push(formula);
    (Formula::And(conjuncts), kept)
}

pub(super) fn collect_formula_var_names(formula: &Formula, out: &mut FxHashSet<String>) {
    match formula {
        Formula::Var(name, _) => {
            out.insert(name.as_str().to_string());
        }
        Formula::Bool(_) | Formula::Int(_) | Formula::UInt(_) | Formula::BitVec { .. } => {}
        Formula::Not(inner) | Formula::Neg(inner) => collect_formula_var_names(inner, out),
        Formula::BvNot(inner, _)
        | Formula::BvToInt(inner, _, _)
        | Formula::IntToBv(inner, _)
        | Formula::BvZeroExt(inner, _)
        | Formula::BvSignExt(inner, _) => collect_formula_var_names(inner, out),
        Formula::BvExtract { inner, .. } => collect_formula_var_names(inner, out),
        Formula::And(children) | Formula::Or(children) => {
            for child in children {
                collect_formula_var_names(child, out);
            }
        }
        Formula::Implies(a, b)
        | Formula::Eq(a, b)
        | Formula::Lt(a, b)
        | Formula::Le(a, b)
        | Formula::Gt(a, b)
        | Formula::Ge(a, b)
        | Formula::Add(a, b)
        | Formula::Sub(a, b)
        | Formula::Mul(a, b)
        | Formula::Div(a, b)
        | Formula::Rem(a, b)
        | Formula::Select(a, b)
        | Formula::BvConcat(a, b)
        | Formula::BvAdd(a, b, _)
        | Formula::BvSub(a, b, _)
        | Formula::BvMul(a, b, _)
        | Formula::BvUDiv(a, b, _)
        | Formula::BvSDiv(a, b, _)
        | Formula::BvURem(a, b, _)
        | Formula::BvSRem(a, b, _)
        | Formula::BvAnd(a, b, _)
        | Formula::BvOr(a, b, _)
        | Formula::BvXor(a, b, _)
        | Formula::BvShl(a, b, _)
        | Formula::BvLShr(a, b, _)
        | Formula::BvAShr(a, b, _)
        | Formula::BvULt(a, b, _)
        | Formula::BvULe(a, b, _)
        | Formula::BvSLt(a, b, _)
        | Formula::BvSLe(a, b, _) => {
            collect_formula_var_names(a, out);
            collect_formula_var_names(b, out);
        }
        Formula::Ite(c, t, e) | Formula::Store(c, t, e) => {
            collect_formula_var_names(c, out);
            collect_formula_var_names(t, out);
            collect_formula_var_names(e, out);
        }
        Formula::Forall(bindings, body) | Formula::Exists(bindings, body) => {
            // Skip names introduced by the quantifier; they're locally bound.
            let mut child = FxHashSet::default();
            collect_formula_var_names(body, &mut child);
            for (name, _) in bindings {
                child.remove(name.as_str());
            }
            for name in child {
                out.insert(name);
            }
        }
        // IEEE-754 floating-point nodes: recurse into operands so the inner
        // var names (incl. the dest/operand vars inside `FpFromBits`) are
        // collected. Without this, float value-definitions would collect no
        // vars and be pruned as irrelevant (sound but inert); collecting them
        // lets the relevance filter and clobber-dedup track them correctly.
        Formula::FpNeg(a)
        | Formula::FpAbs(a)
        | Formula::FpIsNaN(a)
        | Formula::FpIsInfinite(a)
        | Formula::FpIsZero(a)
        | Formula::FpIsNormal(a)
        | Formula::FpIsSubnormal(a)
        | Formula::FpIsNegative(a)
        | Formula::FpIsPositive(a) => collect_formula_var_names(a, out),
        Formula::FpFromBits { bits, .. } => collect_formula_var_names(bits, out),
        Formula::FpRem(a, b)
        | Formula::FpMin(a, b)
        | Formula::FpMax(a, b)
        | Formula::FpEq(a, b)
        | Formula::FpLt(a, b)
        | Formula::FpLe(a, b)
        | Formula::FpGt(a, b)
        | Formula::FpGe(a, b)
        | Formula::FpSqrt(a, b) => {
            collect_formula_var_names(a, out);
            collect_formula_var_names(b, out);
        }
        Formula::FpAdd(a, b, c)
        | Formula::FpSub(a, b, c)
        | Formula::FpMul(a, b, c)
        | Formula::FpDiv(a, b, c) => {
            collect_formula_var_names(a, out);
            collect_formula_var_names(b, out);
            collect_formula_var_names(c, out);
        }
        Formula::FpFma(a, b, c, d) => {
            collect_formula_var_names(a, out);
            collect_formula_var_names(b, out);
            collect_formula_var_names(c, out);
            collect_formula_var_names(d, out);
        }
        // FP literals / rounding-mode carry no variables.
        Formula::FpConst { .. }
        | Formula::FpNaN { .. }
        | Formula::FpInf { .. }
        | Formula::FpZero { .. }
        | Formula::FpRoundingMode(_) => {}
        _ => {}
    }
}

pub(super) fn v2_formula_with_block_defs_at(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    stmt_index: Option<usize>,
    formula: Formula,
) -> Formula {
    match stmt_index {
        Some(index) => v2_formula_with_block_defs_before_stmt(func, block, index, formula),
        None => v2_formula_with_block_defs(func, block, formula),
    }
}

pub(super) fn v2_find_target_binary_operands<'a>(
    func: &'a VerifiableFunction,
    target: BlockId,
    op: BinOp,
) -> Option<(&'a trust_types::BasicBlock, usize, &'a Operand, &'a Operand)> {
    let block = func.body.blocks.get(target.0)?;
    v2_find_block_binary_operands(block, op)
        .map(|(stmt_index, lhs, rhs)| (block, stmt_index, lhs, rhs))
}

pub(crate) fn v2_find_block_binary_operands(
    block: &trust_types::BasicBlock,
    op: BinOp,
) -> Option<(usize, &Operand, &Operand)> {
    let mut found = None;
    for (stmt_index, stmt) in block.stmts.iter().enumerate() {
        let Statement::Assign { rvalue, .. } = stmt else {
            continue;
        };
        let candidate = match rvalue {
            Rvalue::BinaryOp(stmt_op, lhs, rhs) | Rvalue::CheckedBinaryOp(stmt_op, lhs, rhs)
                if *stmt_op == op =>
            {
                Some((stmt_index, lhs, rhs))
            }
            _ => None,
        };
        if let Some(candidate) = candidate {
            if found.is_some() {
                // A block id plus operation is not enough identity to select
                // among multiple candidates. The assert caller converts this
                // ambiguity into an explicit proof-gap row.
                return None;
            }
            found = Some(candidate);
        }
    }
    found
}

/// `cond`'s live definition in `block` as a comparison `(stmt_index, op, lhs,
/// rhs)` — the SHIPPED rule, which admits only PROJECTION-FREE comparison
/// inputs. [`v2_find_projected_condition_binary_operands`] is the sibling that
/// admits a field-projected input; see it for why the two are separate rather
/// than one loosened rule.
pub(super) fn v2_find_condition_binary_operands<'a>(
    func: &VerifiableFunction,
    block: &'a trust_types::BasicBlock,
    cond: &Operand,
) -> Option<(usize, BinOp, &'a Operand, &'a Operand)> {
    v2_condition_binary_operands(func, block, cond, false)
}

/// As [`v2_find_condition_binary_operands`], but a comparison INPUT may carry
/// FIELD projections (`_3 = Lt(_2.0, const 32)`). Everything else — the
/// projection-free stable flag place, the live whole-local definition, const
/// identity, and the no-later-rewrite scan — is the same rule.
///
/// THE PROJECTION IS THE REAL LOWERING, not a hypothetical. `1u32 << t` with
/// `let t = (x | 64) + 1` extracts (`-Ztrust-dump=mir`, stage2 @ 17abbefc3) as
///
/// ```text
/// bb0: _3 = CheckedBinaryOp(Add, _2, const 1u32); assert(!_3.1, Overflow(Add)) -> bb1
/// bb1: _4 = BinaryOp(Lt, Copy _3.0, const 32u32); assert(_4, Overflow(Shl))    -> bb2
/// bb2: _0 = BinaryOp(Shl, const 1u32, Copy _3.0)
/// ```
///
/// so the comparison input is `_3.0`, the value field of the `CheckedAdd` tuple
/// — exactly the shape that already forced [`v2_eq_def_binds_projected_operand`]
/// to exist for the zero-divisor chain. The shipped rule's comment ("faithful
/// rustc MIR materializes comparison inputs in projection-free temporaries") is
/// a false premise, and it cost a real obligation: with the finder returning
/// `None`, `v2_shift_assert_binds_statement` refuses, so the assert lane drops
/// to a generic `VcKind::ArithmeticOverflow` row while the per-statement
/// `ShiftOverflow` row — the VACUOUS one, sitting under the assert's own
/// `AssertHolds` guard — survives as the ONLY `shift:left` row at the span, and
/// reads `proved` on a genuinely-UB shift. (Pretty-printed `--emit=mir` renders
/// `_3.0` as a plain local and hides this; the extracted verification input does
/// not.)
///
/// A SIBLING, NOT A LOOSENING, for the reason c67021cd0d gave for the shift
/// suppression itself: this finder is shared by the bounds, div/rem and
/// arithmetic lanes, each of which uses it to decide an EXACT binding that can
/// delete an obligation. Relaxing it in place would move all of them at once on
/// one unmeasured edit. Callers opt in by name, so the projection dimension
/// stays visible at the call site.
///
/// ITS CALLER is `checked_vcs::v2_shift_assert_binds_statement`, the ONE
/// predicate `c67021cd0d` made serve both shift lanes so they cannot drift
/// apart. Until that call site selects this rule the projected shape stays
/// broken in exactly the way described above.
///
/// FAIL-CLOSED ON EVERYTHING THE PROJECTION ADDS:
///  * FIELD projections only — the one shape rustc emits here. `Deref` is a read
///    through a pointer whose stores are opaque to a def scan; `Index` reads a
///    SEPARATE index local that nothing in this rule covers; the rest are
///    refused because they were not measured, not because they were judged
///    unsafe. This is deliberately STRICTER than `checked_vcs`'s sibling concept
///    `v2_place_is_statically_addressed` (which also admits
///    `Downcast`/`ConstantIndex`/`Subslice`/`OpaqueCast`/`UnwrapUnsafeBinder`).
///    If the two are ever unified, THIS is the one to widen — and
///    `tests/projected_shift_canary_real_mir.rs`'s
///    `a_downcast_projected_amount_does_not_suppress` is the arm that must then
///    be re-pointed at a projection the widened rule still refuses.
///  * Stability is enforced the way [`guards::value_local_is_unstable`]'s own
///    contract prescribes for a projected value: on the BASE local, which counts
///    field stores AND mutable borrows of the aggregate, so a single-assigned
///    base is stable function-wide — strictly stronger than a same-block scan.
///    (That call is already keyed on `input.local`; for `_3.0` it asks about
///    `_3`.)
///  * The comparison must not read the flag it defines. The shipped rule spells
///    that `input == cond_place`, which a projected input can never equal;
///    `place_names_overlap` is the projection-aware form of the same test and
///    also catches a forged `_4 = Lt(_4.0, ..)`.
pub(super) fn v2_find_projected_condition_binary_operands<'a>(
    func: &VerifiableFunction,
    block: &'a trust_types::BasicBlock,
    cond: &Operand,
) -> Option<(usize, BinOp, &'a Operand, &'a Operand)> {
    v2_condition_binary_operands(func, block, cond, true)
}

/// The body of both condition finders. `projected_inputs` is the ONLY dimension
/// they differ in: with it `false` the behavior is the shipped rule, byte for
/// byte.
fn v2_condition_binary_operands<'a>(
    func: &VerifiableFunction,
    block: &'a trust_types::BasicBlock,
    cond: &Operand,
    projected_inputs: bool,
) -> Option<(usize, BinOp, &'a Operand, &'a Operand)> {
    let cond_place = match cond {
        Operand::Copy(place) | Operand::Move(place) if place.projections.is_empty() => place,
        _ => return None,
    };
    if guards::value_local_is_unstable(func, cond_place.local) {
        return None;
    }
    let cond_name = place_to_var_name(func, cond_place);

    // Public TrustIR is not SSA, and a write through an alias can redefine the
    // condition just as surely as a direct assignment.  Reverse-scan the same
    // canonical write relation used by the statement-version oracle; the first
    // live write must itself be the exact whole-local comparison definition.
    for (stmt_index, stmt) in block.stmts.iter().enumerate().rev() {
        if !stmt_writes_name(func, block, stmt_index, &cond_name) {
            continue;
        }
        let Statement::Assign { place, rvalue, .. } = stmt else {
            return None;
        };
        if place != cond_place {
            return None;
        }
        let Rvalue::BinaryOp(op, lhs, rhs) = rvalue else {
            return None;
        };

        // Public TrustIR is not SSA.  The terminator reads the boolean produced
        // here, so substituting the *later* value of either comparison operand
        // would prove a different assertion.  Reject a carrier whose input is
        // rewritten afterwards, and — unless the caller asked for the
        // projection-tolerant rule — keep the projection-free-temporary boundary
        // the shipped callers were measured against.
        let mut operand_names = Vec::new();
        for operand in [lhs, rhs] {
            if let Operand::Copy(input) | Operand::Move(input) = operand {
                let projection_admissible = if projected_inputs {
                    input.projections.iter().all(|p| matches!(p, trust_types::Projection::Field(_)))
                } else {
                    input.projections.is_empty()
                };
                if !projection_admissible || guards::value_local_is_unstable(func, input.local) {
                    return None;
                }
                let name = place_to_var_name(func, input);
                // The comparison must not read the flag it defines.
                let reads_its_own_flag = if projected_inputs {
                    place_names_overlap(&name, &cond_name)
                } else {
                    input == cond_place
                };
                if reads_its_own_flag {
                    return None;
                }
                if !operand_names.contains(&name) {
                    operand_names.push(name);
                }
            }
        }
        let writes_comparison_input = (stmt_index + 1..block.stmts.len()).any(|later_index| {
            operand_names.iter().any(|name| stmt_writes_name(func, block, later_index, name))
        });
        if writes_comparison_input {
            return None;
        }
        return Some((stmt_index, *op, lhs, rhs));
    }
    None
}

/// The UNIQUE `Neg` operand of `target`, or `None` when `target` holds no `Neg`,
/// holds more than one, or negates a value that is projected, reassigned
/// elsewhere in the function, or rewritten earlier in `target` itself.
///
/// UNIQUENESS IS AN IDENTITY GUARANTEE, and the per-statement suppression
/// (`v2_negation_assert_exactly_bound`) leans on it: `Some` means `target` has
/// exactly one Neg statement, so a caller holding a Neg statement OF `target`
/// knows the assert bound to that very statement — not merely to the block.
pub(crate) fn v2_find_target_neg_operand(
    func: &VerifiableFunction,
    target: BlockId,
) -> Option<&Operand> {
    let block = func.body.blocks.get(target.0)?;
    let mut found: Option<(usize, &Operand)> = None;
    for (stmt_index, stmt) in block.stmts.iter().enumerate() {
        let Statement::Assign { rvalue, .. } = stmt else {
            continue;
        };
        if let Rvalue::UnaryOp(trust_types::UnOp::Neg, operand) = rvalue {
            if found.is_some() {
                return None;
            }
            found = Some((stmt_index, operand));
        }
    }
    let (stmt_index, operand) = found?;
    // The source-block overflow condition compares the value that reaches the
    // normal target. If that target rewrites the negated local first, the
    // condition no longer authenticates this operation.
    if let Operand::Copy(place) | Operand::Move(place) = operand {
        if !place.projections.is_empty() || guards::value_local_is_unstable(func, place.local) {
            return None;
        }
        let name = crate::place_to_var_name(func, place);
        if (0..stmt_index).any(|index| stmt_writes_name(func, block, index, &name)) {
            return None;
        }
    }
    Some(operand)
}
