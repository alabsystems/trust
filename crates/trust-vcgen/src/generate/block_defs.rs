// Per-block definitional facts and the versioning that keeps them sound. A
// fact established in one block is only usable at a program point where the
// subject has not been redefined, so every fact is rebound to the SSA version
// live at its use site.

use super::*;

// Trust (W4/spine-derives-unreachable): moved to
// `trust_types::terminator_obligations::block_span` — one definition, two
// callers (this producer and the trust-ir spine), on the static_truth
// precedent. This wrapper keeps every in-crate spelling.
pub(super) fn v2_block_span(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
) -> SourceSpan {
    trust_types::terminator_obligations::block_span(func, block)
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

/// Trust (2026-10-15, TRUST-KI-1015-1): the per-block LOOP-YIELD facts of one
/// function — the exclusive-range payload map ([`build_range_yield_guard_map`],
/// `start <= i < end`) and the enumerate-index map
/// ([`build_enumerate_yield_guard_map`], `0 <= i < len`). The per-statement
/// safety lane conjoins both onto every row of a block (`safety.rs`). The hardened
/// panic-boundary lane builds them once per function and conjoins the same facts onto
/// the twin of the block's `Assert` (`hardened::append_assert_panic_vcs`). (Until
/// 2026-10-17 it also read them for a `BoundsCheck` skip set; the twin is now always
/// emitted, see there.)
///
/// The facts are the maps' own, unchanged: each is keyed to the blocks that read the
/// payload or a single-assignment local computed from it (`attach_payload_facts`),
/// so a block that runs only after the payload was assigned. See the soundness
/// gates in `iterator_yield`'s banner.
pub(crate) struct LoopYieldGuards {
    range: std::rc::Rc<FxHashMap<BlockId, Vec<Formula>>>,
    enumerate: std::rc::Rc<FxHashMap<BlockId, Vec<Formula>>>,
}

impl LoopYieldGuards {
    pub(crate) fn build(func: &VerifiableFunction) -> Self {
        Self {
            range: super::range_yield_guards_for(func),
            enumerate: super::enumerate_yield_guards_for(func),
        }
    }

    /// Every loop-yield fact attached to `block`: the range facts, then the
    /// enumerate facts, the order the per-statement lane conjoins them in. Empty
    /// for a block that reads no yielded payload.
    pub(crate) fn facts_at(&self, block: BlockId) -> Vec<Formula> {
        let r = self.range.get(&block);
        let e = self.enumerate.get(&block);
        let cap = r.map_or(0, Vec::len) + e.map_or(0, Vec::len);
        if cap == 0 {
            return Vec::new();
        }
        let mut facts = Vec::with_capacity(cap);
        if let Some(at) = r {
            facts.extend(at.iter().cloned());
        }
        if let Some(at) = e {
            facts.extend(at.iter().cloned());
        }
        facts
    }
}

/// Build a divisor-is-zero formula for `BinaryOp(Div|Rem, _, divisor)`.
///
/// For constant divisors this reduces to `Bool(divisor == 0)` (always UNSAT
/// for nonzero constants, always SAT for literal zero). For variable divisors
/// it emits `var == 0`, which is satisfiable iff the divisor can be zero —
/// the solver finds a witness assignment and the VC is reported as Failed.
pub(super) fn v2_divisor_is_zero_formula(func: &VerifiableFunction, divisor: &Operand) -> Formula {
    match divisor {
        // A memory image is diagnostic, not a numeric value. The public body
        // preflight/operand collector emits UnsupportedMir; this independent
        // conservative fallback must never claim that its divisor is nonzero.
        Operand::Constant(value) if value.contains_memory_image() => Formula::Bool(true),
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
        // An opaque REFERENCE carrier (OPAQUE-REF-ID-1) has no decidable value
        // either. A well-typed integer division never divides by one, but this
        // fold does not get to assume that: name it by its occurrence identity and
        // leave `== 0` satisfiable, exactly like `OpaqueScalar` above. THIS ARM
        // MUST PRECEDE the catch-all.
        Operand::Constant(
            ConstValue::OpaqueConst(_)
            | ConstValue::UnitVariantRef { .. }
            | ConstValue::EmptyClosureRef { .. }
            | ConstValue::StructScalarFieldsRef { .. },
        ) => Formula::Eq(
            Box::new(operand_to_formula(func, divisor)),
            Box::new(v2_zero_formula_for_operand(func, divisor)),
        ),
        // Reachability invariant for the catch-all below. `Bool(false)` means
        // "divisor provably nonzero", which discharges the div/rem-by-zero
        // obligation as Proved — so this arm must NEVER see a constant of
        // unknown value, or it would be a false PROVE. It cannot: every
        // unknown-valued constant (`OpaqueScalar`, `ConstParam` and the
        // opaque-reference carriers) has an explicit arm ABOVE, and divisors with
        // a known value lower to Int/Uint/Float/FloatBits, handled above. What
        // remains (`Unit`, `Str`, `CallableItem`) cannot be an integer divisor.
        Operand::Constant(_) => Formula::Bool(false),
        Operand::Copy(_) | Operand::Move(_) => {
            let value = operand_to_formula(func, divisor);
            if let Some(Ty::Float { width }) = crate::operand_ty_cow(func, divisor).as_deref() {
                v2_float_is_zero_formula(value, *width)
            } else {
                Formula::Eq(Box::new(value), Box::new(v2_zero_formula_for_operand(func, divisor)))
            }
        }
        Operand::Symbolic(formula) => {
            let value = formula.clone();
            if let Some(Ty::Float { width }) = crate::operand_ty_cow(func, divisor).as_deref() {
                v2_float_is_zero_formula(value, *width)
            } else {
                Formula::Eq(Box::new(value), Box::new(v2_zero_formula_for_operand(func, divisor)))
            }
        }
        // A refused divisor (it also yields an `UnsupportedMir` row) MIGHT be zero:
        // name it by its occurrence identity and leave `== 0` satisfiable — never
        // the `Bool(false)` "provably nonzero" (OPAQUE-REF-ID-1).
        Operand::Unsupported { .. } => Formula::Eq(
            Box::new(operand_to_formula(func, divisor)),
            Box::new(v2_zero_formula_for_operand(func, divisor)),
        ),
        // A future operand variant: unknown value, so it MIGHT be zero.
        _ => Formula::Bool(true),
    }
}

/// OPAQUE-REF-ID-1: a divisor with no modeled value is never "provably nonzero". Before,
/// the opaque-reference carriers fell to the `Operand::Constant(_) => Bool(false)`
/// catch-all and an `Operand::Unsupported` divisor to the `_ => Bool(false)` arm, either of
/// which discharges a DivisionByZero row as Proved without looking at the value.
#[cfg(test)]
mod unmodeled_divisor_tests {
    use super::*;

    #[test]
    fn unmodeled_divisors_stay_possibly_zero_and_are_named_by_site() {
        let func = crate::memory_image_tests::function(Rvalue::Use(Operand::Constant(
            ConstValue::Uint(7, 8),
        )));
        let site = trust_types::OpaqueOrigin::Site { block: 0, stmt: 0, slot: 1 };
        for divisor in [
            Operand::Constant(ConstValue::OpaqueConst(site.clone())),
            Operand::Constant(ConstValue::UnitVariantRef {
                enum_name: "E".into(),
                variant: 0,
                origin: site.clone(),
            }),
            Operand::Constant(ConstValue::StructScalarFieldsRef {
                adt_name: "S".into(),
                fields: vec![ConstValue::Uint(1, 8)],
                origin: site.clone(),
            }),
            Operand::Unsupported { kind: "Const".into(), detail: "x".into(), origin: site.clone() },
        ] {
            let formula = v2_divisor_is_zero_formula(&func, &divisor);
            let Formula::Eq(lhs, rhs) = &formula else {
                panic!("{divisor:?}: a satisfiable `symbol == 0`, got {formula:?}")
            };
            assert_eq!(**rhs, Formula::Int(0), "{divisor:?}");
            let name = lhs.var_name().expect("the divisor's own symbol");
            assert!(name.ends_with("b0_s0_o1") || name.contains("_b0_s0_o1_"), "{name}");
            assert!(!v2_divisor_is_nonzero_constant(&divisor), "{divisor:?}");
        }
    }
}

#[cfg(test)]
mod memory_image_refusal_tests {
    use super::*;

    #[test]
    fn memory_image_divisor_and_operand_collector_refuse_independently() {
        use crate::memory_image_tests::{assert_refusal, function, image, nested_image};
        let func = function(Rvalue::Use(Operand::Constant(ConstValue::Uint(7, 8))));
        for value in [image(0), image(8), nested_image(8)] {
            let operand = Operand::Constant(value);
            assert_eq!(v2_divisor_is_zero_formula(&func, &operand), Formula::Bool(true));
            assert!(!v2_divisor_is_nonzero_constant(&operand));
            let mut vcs = Vec::new();
            crate::generate::slice_conversion::collect_operand_unsupported(
                &func,
                &"isolated operand",
                &func.span,
                &operand,
                &mut vcs,
            );
            assert_refusal(&vcs);
        }
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
    if !super::terminator_presence_for(func).has_bounds_check_assert {
        return FxHashMap::default();
    }
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
    if !matches!(
        &assert_block.terminator,
        Terminator::Assert { expected: true, msg: AssertMessage::BoundsCheck, target, .. }
            if *target == use_block.id
    ) {
        return false;
    }
    // The assert's FAILURE/cleanup edge runs exactly when the index is out of
    // bounds — it must not re-enter the block whose rows it would suppress.
    if assert_block.terminator.unwind_cleanup_target() == Some(use_block.id) {
        return false;
    }
    // Sole-entry: no OTHER block's terminator may reach `use_block`
    // (`exit_targets` lists cleanup edges too).
    let bypassed = if let Some(no_other) = crate::fn_memo::sole_predecessors(func)
        .and_then(|sp| sp.no_other_exit_predecessor(use_block.id, assert_block.id))
    {
        !no_other
    } else {
        func.body
            .blocks
            .iter()
            .any(|b| b.id != assert_block.id && b.terminator.has_exit_block_target(use_block.id))
    };
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
                if let Some(row_len) =
                    rvalue_safety::collection_len_formula(func, &prefix, ty.as_ref())
                {
                    if !v2_bounds_assert_binds_index_row(
                        func,
                        assert_block,
                        use_block,
                        use_stmt_index,
                        *index_local,
                        &prefix,
                        ty.as_ref(),
                        &row_len,
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
    row_len: &Formula,
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
    let use_prefix_end = use_stmt_index.min(use_block.stmts.len());
    if use_prefix_end > 0 {
        let index_name = place_to_var_name(func, index_place);
        if (0..use_prefix_end).any(|k| stmt_writes_name(func, use_block, k, &index_name)) {
            return false;
        }
    }
    v2_assert_len_binding_holds(
        func,
        assert_block,
        cmp_index,
        use_block,
        use_stmt_index,
        bound_op,
        collection,
        collection_ty,
        row_len,
    )
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
    // Trust (2026-09-20): the USE side, threaded in so the slice-metadata
    // stability question can be asked over the interval between the length read
    // and the access instead of over the whole function. See
    // `v2_slice_metadata_root_rebinds_between`.
    use_block: &trust_types::BasicBlock,
    use_stmt_index: usize,
    bound_op: &Operand,
    collection: &Place,
    collection_ty: &Ty,
    row_len: &Formula,
) -> bool {
    let bound_place = match bound_op {
        // A literal bound is exact only against a type-derived length.
        Operand::Constant(_) => return v2_const_matches_len(func, bound_op, row_len),
        Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => p,
        _ => return false,
    };
    let prefix_end = cmp_index.min(assert_block.stmts.len());
    let Some(k) = (0..prefix_end).rev().find(|&k| {
        matches!(
            &assert_block.stmts[k],
            Statement::Assign { place, .. } if place == bound_place
        )
    }) else {
        return false;
    };
    let Statement::Assign { rvalue, .. } = &assert_block.stmts[k] else {
        return false;
    };
    match rvalue {
        Rvalue::Len(p) if p == collection => {}
        Rvalue::UnaryOp(
            trust_types::UnOp::PtrMetadata,
            Operand::Copy(_) | Operand::Move(_),
        )
        | Rvalue::Use(Operand::Constant(_)) => {}
        _ => return false,
    }
    if k + 1 < prefix_end {
        let bound_name = place_to_var_name(func, bound_place);
        if (k + 1..prefix_end).any(|j| stmt_writes_name(func, assert_block, j, &bound_name)) {
            return false;
        }
    }
    match rvalue {
        Rvalue::Len(p) if p == collection => {}
        Rvalue::UnaryOp(
            trust_types::UnOp::PtrMetadata,
            Operand::Copy(p) | Operand::Move(p),
        ) if *p == rvalue_safety::slice_metadata_place(func, collection)
            || v2_is_reborrow_of(func, assert_block, k, p, collection) => {}
        Rvalue::Use(op @ Operand::Constant(_)) => {
            return v2_const_matches_len(func, op, row_len);
        }
        _ => return false,
    }
    if matches!(collection_ty, Ty::Array { .. } | Ty::SymArray { .. }) {
        return true;
    }
    // VALUE metadata: the length read and the indexed access must see the
    // same fat pointer.
    //
    // Trust (2026-09-20): asked over the INTERVAL between the two, not over
    // the whole function. `v2_slice_metadata_root_can_rebind` answers "is
    // this pointer rebound ANYWHERE", and for every slice a loop yields the
    // answer is yes — the loop rebinds it once per iteration, which is a
    // DIFFERENT execution of both the length read and the access.
    //
    // MEASURED on `for w in v.windows(2) { if w[0] > w[1] { .. } }`: the
    // `PtrMetadata` shape matched at the length statement and the binding
    // was refused for that reason alone, so every such row was emitted and
    // then refuted on a model the program cannot produce (`_11` free).
    //
    // The ALIAS half stays whole-function on purpose — a `&mut s`/`&raw s`
    // anywhere is a channel through which a write can land inside the
    // interval invisibly, so it is not an interval question at all. Only
    // the DIRECT-write half becomes path-local, over exactly the statements
    // that can run between the two points: the assert block's tail after the
    // length statement, and the use block's prefix before the access. The
    // caller has already established SOLE ENTRY, so nothing else runs.
    !v2_slice_metadata_root_rebinds_between(
        func,
        assert_block,
        k,
        use_block,
        use_stmt_index,
        collection.local,
    )
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
pub(super) fn v2_is_reborrow_of(
    func: &VerifiableFunction,
    assert_block: &trust_types::BasicBlock,
    before: usize,
    pointer: &Place,
    collection: &Place,
) -> bool {
    let prefix_end = before.min(assert_block.stmts.len());
    if prefix_end == 0 || !pointer.projections.is_empty() {
        return false;
    }
    let Some(k) = (0..prefix_end).rev().find(|&k| {
        matches!(&assert_block.stmts[k], Statement::Assign { place, .. } if place == pointer)
    }) else {
        return false;
    };
    let Statement::Assign { rvalue, .. } = &assert_block.stmts[k] else {
        return false;
    };
    if !matches!(
        rvalue,
        Rvalue::Ref { place: reborrowed, .. } | Rvalue::AddressOf(_, reborrowed)
            if reborrowed == collection
    ) || guards::value_local_is_unstable(func, pointer.local)
    {
        return false;
    }
    if k + 1 < prefix_end {
        let pointer_name = place_to_var_name(func, pointer);
        return !(k + 1..prefix_end).any(|j| stmt_writes_name(func, assert_block, j, &pointer_name));
    }
    true
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
/// Whether the fat-pointer metadata of root `local` can be rebound ON THE PATH
/// between a length read and an indexed access that the caller has already shown
/// to be joined by a sole-entry `BoundsCheck` success edge.
///
/// This is [`v2_slice_metadata_root_can_rebind`] split in two, because its two
/// halves answer different questions:
///
///  * the ALIAS half — a mutable/raw borrow OF THE POINTER LOCAL — stays
///    WHOLE-FUNCTION. Such a borrow is a channel through which `s = other` can
///    happen invisibly, including from inside the interval, so restricting it to
///    the interval would be unsound;
///  * the DIRECT-WRITE half becomes path-local: only a write to the pointer
///    local that can actually RUN between the length statement and the access
///    decouples them. The statements that can are exactly the assert block's
///    tail after `len_stmt` and the use block's prefix before `use_stmt_index`;
///    the assert terminator itself writes nothing (a `Call` dest would not be a
///    `BoundsCheck` assert), and sole entry — established by
///    [`v2_bounds_assert_exactly_covers_place`] before this is reached — means
///    no other block runs in between.
///
/// WHY THE WHOLE-FUNCTION FORM WAS WRONG HERE, and why this is not a widening of
/// what may be suppressed. A loop rebinds its yielded slice once per iteration
/// (`_8 = ((_5 as Some).0)` at the top of the body). That write is in a
/// DIFFERENT execution of both endpoints, so it cannot decouple the pair this
/// row is about — but the whole-function scan sees it and refuses every
/// loop-carried slice, which is every `for w in v.windows(2)` row there is.
fn v2_slice_metadata_root_rebinds_between(
    func: &VerifiableFunction,
    assert_block: &trust_types::BasicBlock,
    len_stmt: usize,
    use_block: &trust_types::BasicBlock,
    use_stmt_index: usize,
    local: usize,
) -> bool {
    let names_pointer_itself = |place: &Place| {
        place.local == local && place.projections.first() != Some(&Projection::Deref)
    };
    // ALIAS half: whole-function, unchanged in strength.
    if crate::any_local_write_stmt(func, &func.body.blocks, local, |_b, stmt| {
        matches!(
            stmt,
            Statement::Assign {
                rvalue: Rvalue::Ref { mutable: true, place: bp } | Rvalue::AddressOf(_, bp),
                ..
            } if names_pointer_itself(bp)
        )
    }) {
        return true;
    }
    // DIRECT-WRITE half: only the statements that can run between the two.
    let writes_root = |block: &trust_types::BasicBlock, range: std::ops::Range<usize>| {
        range.filter_map(|k| block.stmts.get(k)).any(|stmt| match stmt {
            Statement::Assign { place, .. }
            | Statement::SetDiscriminant { place, .. }
            | Statement::Deinit { place } => names_pointer_itself(place),
            _ => false,
        })
    };
    if writes_root(assert_block, len_stmt.saturating_add(1)..assert_block.stmts.len()) {
        return true;
    }
    if writes_root(use_block, 0..use_stmt_index.min(use_block.stmts.len())) {
        return true;
    }
    false
}

pub(super) fn v2_slice_metadata_root_can_rebind(func: &VerifiableFunction, local: usize) -> bool {
    let names_pointer_itself = |place: &Place| {
        place.local == local && place.projections.first() != Some(&Projection::Deref)
    };
    crate::any_local_write_candidate(func, &func.body.blocks, local, |block, item| match item {
        Some(stmt) => match stmt {
            Statement::Assign { place, rvalue, .. } => {
                names_pointer_itself(place)
                    || matches!(
                        rvalue,
                        Rvalue::Ref { mutable: true, place: bp } | Rvalue::AddressOf(_, bp)
                            if names_pointer_itself(bp)
                    )
            }
            Statement::SetDiscriminant { place, .. } | Statement::Deinit { place } => {
                names_pointer_itself(place)
            }
            _ => false,
        },
        None => {
            matches!(&block.terminator, Terminator::Call { dest, .. } if names_pointer_itself(dest))
        }
    })
}

/// A constant bound equals the row's length only when it renders to the EXACT
/// length term — the concrete `Int(N)` of a `[T; N]` or the per-param symbol of
/// a `[T; const N]`. Value metadata (a slice length) has no constant identity.
fn v2_const_matches_len(func: &VerifiableFunction, bound: &Operand, row_len: &Formula) -> bool {
    const_int_value(bound).is_some_and(|n| matches!(row_len, Formula::Int(m) if *m == n))
        || &operand_to_formula(func, bound) == row_len
}

pub(super) fn v2_formula_with_block_defs(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    formula: Formula,
) -> Formula {
    v2_formula_with_block_defs_at_point(func, block, block.stmts.len(), formula)
}

/// As [`v2_formula_with_block_defs`], but also returning the pieces an
/// `ObligationRecord` needs: the RENAMED body (the violation as it appears
/// inside the returned formula) and the block-defs KEPT, so that
/// `body = renamed_body`, `wrappers = [ConjoinFactsLast { facts: kept }]`
/// reconstructs the returned formula bit-for-bit.
///
/// Trust: 2026-09-21 — the whole-block twin of
/// [`v2_formula_with_block_defs_at_point_recorded`], which already existed. Its
/// absence is why `generate/safety.rs`'s slice-method panic arm pushes
/// `obligation: None`: block defs VERSION-RENAME the body, so a record seeded
/// with the ORIGINAL violation cannot replay, and `ob_record_conjoin_wrap` is
/// fail-closed against that shape. A row with an unreplayable record is worse
/// than one with none, so the lane correctly recorded nothing rather than
/// recording wrongly — and this is the missing piece, not a new mechanism.
pub(super) fn v2_formula_with_block_defs_recorded(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    formula: Formula,
) -> (Formula, Formula, Vec<Formula>) {
    v2_formula_with_block_defs_at_point_recorded(func, block, block.stmts.len(), formula)
}

/// Trust: 2026-09-16 (round A8) — [`v2_formula_with_block_defs`] restricted to the
/// same-block LENGTH TIES: the defs whose subject is a `{place}__slice_len` name
/// (`guards::push_copy_slice_len` / `push_borrow_slice_len` / `push_unsize_slice_len`),
/// each versioned at its own establish point exactly as the full builder versions
/// every def. For the slice RANGE-INDEX call obligation, which deliberately skips the
/// full block-defs (the `Range { .. }` aggregate's field equalities were measured to
/// push the default-mode solver to Unknown on a trivial contradiction — see the
/// `1e` arm of `generate_v2_safety_vcs_impl_with_origins_checked`): once the obligation's
/// length is the argument temp's OWN name (`_8 = copy _1; index(move _8, ..)` at
/// `-Copt-level=0`, with the root `s` unlicensed for the canonical name because it
/// is reseated elsewhere), the tie `_8__slice_len#s1_0 == s__slice_len#s0_0` is the
/// only thing that connects it to the length the `min` fact bounds. Conjoining a
/// versioned true equality is drop-only-in-reverse (monotone): it can discharge a
/// spurious refutation, never hide a real one.
pub(super) fn v2_formula_with_slice_len_ties(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    formula: Formula,
) -> Formula {
    let end = block.stmts.len();
    let sv = super::stmt_versions_for(func);
    let body = version_rename_owned_at(formula, &sv, func, block.id, end);
    let defs: Vec<Formula> = slice_len_ties_versioned_until(func, block, end, &sv)
        .into_iter()
        .filter_map(|d| pin_bare_reads_rewritten_before(&sv, func, block, end, d))
        .collect();
    combine_block_defs_as_recipe_only(func, defs, body)
}

/// As [`v2_formula_with_slice_len_ties`], but also returning the renamed body
/// and the ties KEPT, for the same `ObligationRecord` reconstruction.
///
/// Trust: 2026-09-21 — the plain form already computed both and threw them
/// away (`combine_relevant_block_defs_recorded(..).0`); this returns the whole
/// tuple. The RANGE-INDEX arm of the slice-method panic lane takes this path,
/// so it is the second of the two pieces that lane needs before it can record.
pub(super) fn v2_formula_with_slice_len_ties_recorded(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    formula: Formula,
) -> (Formula, Formula, Vec<Formula>) {
    let end = block.stmts.len();
    let sv = super::stmt_versions_for(func);
    let body = version_rename_owned_at(formula, &sv, func, block.id, end);
    // Trust: 2026-10-10 (local; kept on merge 2026-10-14) — and a tie whose bare reads
    // the block rewrites before `end` is pinned there or withheld
    // (`pin_bare_reads_rewritten_before`).
    let defs: Vec<Formula> = slice_len_ties_versioned_until(func, block, end, &sv)
        .into_iter()
        .filter_map(|d| pin_bare_reads_rewritten_before(&sv, func, block, end, d))
        .collect();
    // MERGE, 2026-09-18 — `func` is threaded through the relevance closure
    // deliberately: `collect_relevance_var_names` compares names in their
    // POST-COLLAPSE spelling (`relevance_var_name` folds every version of the return
    // slot onto `_0`, and a versioned whole local onto its bare name where the
    // versions provably denote one value). These ties are versioned per establish
    // point just above, so a tie minted as `_12__slice_len#s1_0` is relevant to a
    // body that spells the same value under a different token; matched on raw names
    // it would be dropped as irrelevant and the row would lose its length fact.
    let (combined, kept) = combine_block_defs_as_recipe(func, defs, body.clone());
    (combined, body, kept)
}

fn block_has_slice_len_tie_candidate_until(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    end: usize,
) -> bool {
    let end = end.min(block.stmts.len());
    block.stmts[..end].iter().any(|stmt| match stmt {
        Statement::Assign {
            rvalue:
                Rvalue::Use(_) | Rvalue::Cast(..) | Rvalue::Ref { .. } | Rvalue::AddressOf(..),
            ..
        } => true,
        Statement::Assign { place, .. } if place.projections.is_empty() => func
            .body
            .locals
            .get(place.local)
            .and_then(|d| d.name.as_deref())
            .is_some_and(|n| n.ends_with(SLICE_LEN_SUFFIX)),
        _ => false,
    })
}

/// The same-block LENGTH TIES of `block` in `stmts[..end]` — the defs whose subject
/// is a `{place}__slice_len` name (`guards::push_copy_slice_len` /
/// `push_borrow_slice_len` / `push_unsize_slice_len`) — each versioned at ITS OWN
/// establish point. Shared by [`v2_formula_with_slice_len_ties_recorded`] (the
/// block-terminal consumer) and [`v2_live_slice_len_ties_at_point`] (the
/// use-point consumer).
fn slice_len_ties_versioned_until(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    end: usize,
    sv: &StmtVersionCtx,
) -> Vec<Formula> {
    if !block_has_slice_len_tie_candidate_until(func, block, end) {
        return Vec::new();
    }
    guards::extract_block_definitions_until_versioned_indexed(func, block, end)
        .into_iter()
        .filter(|(_, d)| block_def_subject(d).is_some_and(|s| s.ends_with(SLICE_LEN_SUFFIX)))
        // Trust: 2026-09-16 (round A9) — a tie whose source is spelled through an
        // `Index(l)` segment with a multi-valued `l` (`s*[_3]__slice_len`) is a fact
        // about whichever slot `l` selects; the emitters withhold it
        // (`guards::push_copy_slice_len` and siblings) and this consumer refuses it
        // again, so the two copy ties of `index_local_min_bug` (`_12__slice_len ==
        // s*[_3]__slice_len` at `j = 0`, `_13__slice_len == s*[_3]__slice_len` at
        // `j = k`) can never be conjoined onto one obligation whichever producer
        // minted them.
        .filter(|(_, d)| !formula_mentions_non_ssa_index_segment(func, d))
        // Each tie is pinned at ITS OWN statement (`k + 1` bounds the establish
        // search), never at a later reseat of its subject's base (round A11).
        //
        // Trust: 2026-09-25 — RESTORED. 4b2f78a544 rebuilt this chain as the
        // `_recorded` twin and dropped this step (`.map(|(_, d)| d)`). The ties then
        // reached `combine_relevant_block_defs_recorded` UNVERSIONED
        // (`_8__slice_len == s__slice_len`), and the body spells the same values
        // `_8__slice_len#s1_0` / `s__slice_len#s0_0`. So the relevance closure
        // dropped the one tie this builder exists for. `a8_ctl_min_after_reseat_o0`
        // (`s = b; let n = s.len().min(100); s[..n]`, oracle: never panics) went
        // from proved to REFUTED on the untied `_8__slice_len#s1_0 = 0`. The record
        // is unaffected: `kept` is whatever combine kept, versioned or not, so
        // `{body, [ConjoinFactsLast { kept }]}` still replays to `combined`.
        .map(|(k, d)| version_block_def_at_establish(sv, func, block, (k + 1).min(end), d))
        .collect()
}

/// Trust: 2026-10-02 (slices matched through a tuple) — the same-block LENGTH
/// TIES that hold at the use point `point` of a row in `block`, for a consumer
/// that conjoins them BEFORE its own whole-row version rename at that same point
/// (the load/store index lane, `generate_v2_rvalue_safety_vcs_impl`).
///
/// THE DEFECT THIS CLOSES (false refutation of valid Rust). `match (a, b) {
/// ([x], [y]) => .. }` tests each field's length through one fresh copy
/// (`_15 = copy (_3.0)`, `_8 = PtrMetadata(&raw (*_15))`, `switchInt(_8 == 1)`)
/// and reads the arm's `ConstantIndex` through ANOTHER fresh copy in the arm
/// block (`_17 = copy (_3.0)`, `_10 = &(*_17)[0 of 1]`). The row's length is
/// `_17__slice_len`; the only fact that names it is the arm block's own copy tie
/// `_17__slice_len == _3.0__slice_len`, and the index lane conjoined the
/// DOMINATING blocks' definitions but never its own block's, so the row was
/// refuted at `_17__slice_len = 0` beside `_3.0__slice_len = 1`.
///
/// SOUNDNESS. Each tie is a true equation pinned at its own statement
/// (`version_block_def_at_establish`): a source reseated between the tie and
/// `point` is named by its pre-reseat token (`a__slice_len#e`), a subject
/// reseated there carries a token the row's read does not, and the relevance
/// closure drops it. The caller renames the whole row at `point` afterwards; a
/// tie that rename would still change (a name left bare at its establish point
/// that the block writes before `point`) is withheld rather than re-stamped onto
/// the post-write value. Conjoining a true fact only deletes infeasible models:
/// it can discharge a spurious refutation, never hide a real one. Pinned by
/// `slice_len_ties_at_point_tests` and `tests/slice_tuple_pattern_len_realmir.rs`.
pub(super) fn v2_live_slice_len_ties_at_point(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    point: usize,
    formula: &Formula,
) -> Vec<Formula> {
    let end = point.min(block.stmts.len());
    if !block_has_slice_len_tie_candidate_until(func, block, end) {
        return Vec::new();
    }
    let sv = super::stmt_versions_for(func);
    let ties: Vec<Formula> = slice_len_ties_versioned_until(func, block, end, &sv)
        .into_iter()
        .filter(|tie| {
            !trust_types::any_formula_node(tie, &mut |node| match node {
                Formula::Var(name, _) => {
                    !name.contains('#') && sv.version_token_at(func, block.id, end, name).is_some()
                }
                _ => false,
            })
        })
        .collect();
    if ties.is_empty() {
        return Vec::new();
    }
    let body = version_rename_at(formula, &sv, func, block.id, end);
    let kept = relevant_block_def_indices(func, &ties, &body);
    if kept.is_empty() {
        return Vec::new();
    }
    let mut ties = ties;
    kept.into_iter()
        .filter_map(|index| {
            ties.get_mut(index).map(|slot| std::mem::replace(slot, Formula::Bool(false)))
        })
        .collect()
}

/// Trust: 2026-09-16 (round A9) — true iff some variable of `f` embeds, by number, an
/// index local that is not `local_defs::is_single_static_assignment`: a name carrying
/// a segment `[_<l>]` (the spelling `place_to_var_name` gives `Projection::Index(l)`)
/// whose `l` has more than one value. Such a name denotes a different slot at
/// different program points, and a fact keyed on it is a claim about all of them.
pub(super) fn formula_mentions_non_ssa_index_segment(
    func: &VerifiableFunction,
    f: &Formula,
) -> bool {
    fn name_has_non_ssa_index_segment(func: &VerifiableFunction, name: &str) -> bool {
        let base = name.split('#').next().unwrap_or(name);
        let mut rest = base;
        while let Some(pos) = rest.find("[_") {
            let after = &rest[pos + 2..];
            let digits: &str = after.split(|c: char| !c.is_ascii_digit()).next().unwrap_or("");
            if !digits.is_empty()
                && after.as_bytes().get(digits.len()) == Some(&b']')
                && let Ok(local) = digits.parse::<usize>()
                && !crate::local_defs::is_single_static_assignment(func, local)
            {
                return true;
            }
            rest = after;
        }
        false
    }
    trust_types::any_formula_node(f, &mut |node| match node {
        Formula::Var(name, _) => name_has_non_ssa_index_segment(func, name),
        Formula::SymVar(sym, _) => name_has_non_ssa_index_segment(func, sym.as_str()),
        _ => false,
    })
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
pub(crate) struct VersionedBlockDefs {
    defs: Vec<Formula>,
    rel_vars: std::cell::OnceCell<Vec<Vec<String>>>,
}

impl VersionedBlockDefs {
    pub(crate) fn compute(
        sv: &StmtVersionCtx,
        func: &VerifiableFunction,
        block: &trust_types::BasicBlock,
        end: usize,
    ) -> Self {
        let end = end.min(block.stmts.len());
        if end == 0 {
            return Self { defs: Vec::new(), rel_vars: std::cell::OnceCell::new() };
        }
        // Trust (ARM-B): the VERSIONED extract keeps pure place-read defs across a
        // later same-block clobber — sound HERE ONLY because every def below is
        // stamped at its establish point (`version_block_def_at_establish`), so the
        // kept def pins the PRE-write value by name. This is what ties a closure's
        // `&mut`-upvar guard read to its use read (`_2 == _1.0*`, `_4 == _1.0*`
        // with no write between) — the last unified read-tie instance.
        // Trust: 2026-09-16 (round A11) — each def is pinned at ITS OWN statement: the
        // establish search is bounded by `k + 1`, the index the extraction tags it
        // with. Searching from `end` took the LATEST ancestor write of the subject,
        // which is a later reseat whenever one exists: `p.0 = 3; p = q; t[p.0]` at
        // `-O0` (one block) stamped the field def onto `p.0#s0_2` — the token of
        // `p = q`, which the post-reseat read carries — and PROVED kernel-certified a
        // program that panics (`field_store_reseat_bug`; `a[0] = 3; a = q; t[a[0]]`
        // likewise). The extraction's subject-pin exemption (a def kept across a later
        // rebinding of its subject on THIS extraction only) rests on exactly this bound.
        // Set-discriminant defs carry no index and keep the `end` search: their subject
        // is the `discr_` namespace, which no place write rebinds.
        let mut defs: Vec<(usize, Formula)> =
            guards::extract_block_definitions_until_versioned_indexed(func, block, end);
        defs.extend(
            extract_set_discriminant_definitions_until(func, block, end)
                .into_iter()
                .map(|d| (end, d)),
        );
        if defs.is_empty() {
            return Self { defs: Vec::new(), rel_vars: std::cell::OnceCell::new() };
        }
        // The same-block deref-store-havoc kill (`drop_havoced_block_defs`) is DELETED
        // here: the establish-point versioning below subsumes it — a def whose subject
        // is havoced by an opaque deref-store carries a `#establish` token that the
        // terminal-versioned `body` does not match, so it cannot constrain the
        // post-havoc obligation (the drop, by name-disjointness). Proven 0-residual by
        // `block_def_establish_subsumes_kill` across the corpus + battery, and the
        // falsification gate's 65-mutant suite stays refuted with the kill gone. (The
        // guard-THREADING lane in `build_semantic_guard_map` still uses the kill — that
        // is a separate staleness mechanism, not subsumed by this same-block versioning.)
        let defs: Vec<Formula> = defs
            .into_iter()
            .map(|(k, d)| version_block_def_at_establish(sv, func, block, (k + 1).min(end), d))
            .filter_map(|d| pin_bare_reads_rewritten_before(sv, func, block, end, d))
            .collect();
        Self { defs, rel_vars: std::cell::OnceCell::new() }
    }

    fn relevant_indices<'a>(&'a self, func: &VerifiableFunction, formula: &'a Formula) -> Vec<usize> {
        if self.defs.is_empty() {
            return Vec::new();
        }
        let mut needed: FxHashSet<&'a str> = FxHashSet::default();
        let mut bound: Vec<&'a str> = Vec::new();
        visit_formula_var_names(formula, &mut bound, &mut |raw| {
            needed.insert(relevance_var_name_str(func, raw));
        });
        if needed.is_empty() {
            return Vec::new();
        }
        let rel_vars = self.rel_vars.get_or_init(|| {
            let mut bound = Vec::new();
            self.defs
                .iter()
                .map(|def| {
                    let mut vars: Vec<String> = Vec::new();
                    bound.clear();
                    visit_formula_var_names(def, &mut bound, &mut |raw| {
                        let rel = relevance_var_name_str(func, raw);
                        if !vars.iter().any(|v| v == rel) {
                            vars.push(rel.to_string());
                        }
                    });
                    vars
                })
                .collect()
        });
        let mut keep_rev: Vec<usize> = Vec::new();
        for (index, def_vars) in rel_vars.iter().enumerate().rev() {
            if def_vars.iter().any(|rel| needed.contains(rel.as_str())) {
                for rel in def_vars {
                    needed.insert(rel.as_str());
                }
                keep_rev.push(index);
            }
        }
        keep_rev.reverse();
        keep_rev
    }

    fn combine_as_recipe(
        &self,
        func: &VerifiableFunction,
        formula: Formula,
    ) -> (Formula, Vec<Formula>) {
        if self.defs.is_empty() {
            return (formula, Vec::new());
        }
        let kept = self.relevant_indices(func, &formula);
        if kept.is_empty() {
            if super::recipes::recording() {
                super::recipes::record_slice(&self.defs, 0, &formula);
            }
            return (formula, Vec::new());
        }
        let facts: Vec<Formula> = kept.iter().map(|&index| self.defs[index].clone()).collect();
        let mut conjuncts = Vec::with_capacity(facts.len() + 1);
        conjuncts.extend_from_slice(&facts);
        conjuncts.push(formula);
        let combined = Formula::And(conjuncts);
        if super::recipes::recording() {
            super::recipes::record_slice(&self.defs, facts.len(), &combined);
        }
        (combined, facts)
    }

    fn combine_as_recipe_only(&self, func: &VerifiableFunction, formula: Formula) -> Formula {
        if self.defs.is_empty() {
            return formula;
        }
        let kept = self.relevant_indices(func, &formula);
        let kept_len = kept.len();
        let combined = if kept.is_empty() {
            formula
        } else {
            let mut conjuncts: Vec<Formula> = Vec::with_capacity(kept_len + 1);
            for &index in &kept {
                conjuncts.push(self.defs[index].clone());
            }
            conjuncts.push(formula);
            Formula::And(conjuncts)
        };
        if super::recipes::recording() {
            super::recipes::record_slice(&self.defs, kept_len, &combined);
        }
        combined
    }
}

pub(super) fn v2_formula_with_block_defs_at_point(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    end: usize,
    formula: Formula,
) -> Formula {
    let sv = super::stmt_versions_for(func);
    let body = version_rename_owned_at(formula, &sv, func, block.id, end);
    let vdefs = sv.versioned_block_defs_at_point(func, block, end);
    vdefs.combine_as_recipe_only(func, body)
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
    let sv = super::stmt_versions_for(func);
    let body = version_rename_owned_at(formula, &sv, func, block.id, end);
    let vdefs = sv.versioned_block_defs_at_point(func, block, end);
    let (combined, kept) = vdefs.combine_as_recipe(func, body.clone());
    (combined, body, kept)
}

/// Trust: 2026-09-18 (g7 false refutation) —
/// [`v2_formula_with_block_defs_at_point_recorded`] restricted to the same-block
/// COPY TIES: the defs emitted by a statement whose rvalue is a pure
/// `Rvalue::Use` of a PLACE (`_6 = copy _2`, `_2 = move _7.0`). Such a statement
/// RENAMES a value; it does not compute one, so the fact it contributes is an
/// equality between two reads and nothing else.
///
/// WHY A RESTRICTION EXISTS AT ALL. The unsigned `var * var` overflow row in
/// `overflow_vc` is a MIXED query: a QF_BV rendering of the machine multiply
/// conjoined with an Int out-of-range core over the same operands, which
/// `trust-router`'s DISJOINT-COMPONENT lane refutes component-wise. Conjoining
/// the FULL same-block defs onto it drags whatever else the block computes into
/// the Int core — `c == x ^ y`, `d == c | 7` for the collapse fixture's
/// `(x ^ y | 7) * x` — which is neither linear nor disjoint from the BV half, and
/// ay has no combined decision procedure for the result: it answers
/// `incomplete`, phase `theory-combination`, with its executor refusal as the
/// detail (`internal-error` before ay's AD1 fix). A genuine overflow then
/// degrades from `Failed` WITH a counterexample to `Unknown`: a real bug that
/// ships.
/// (Measured: `path_guard_collapse_cost_real_mir::
/// a_genuine_overflow_in_a_collapsed_block_is_still_refuted` fails under the
/// unrestricted conjoin, and the same file's size pin moves off 77.) A copy tie
/// introduces one `Eq` over two reads, so it cannot move a row out of the
/// fragment its core already lives in, and it adds nothing at all to a block
/// that computes its operands rather than copying them.
///
/// SOUNDNESS is `v2_formula_with_slice_len_ties`': conjoining a versioned true
/// equality is drop-only-in-reverse (monotone) — it can discharge a spurious
/// refutation, never hide a real one. Each tie is versioned at ITS OWN establish
/// point while the body is versioned at `end`, so a tie whose source is
/// overwritten between the copy and the use point (`b = c; t = copy b; a * t`)
/// carries a token the use-point read does not, is name-disjoint, and is pruned
/// as irrelevant — which is exactly why the write-before-the-multiply twin stays
/// refuted.
fn stmt_is_copy_tie_candidate(stmt: &Statement) -> bool {
    match stmt {
        Statement::Assign {
            rvalue: Rvalue::Use(Operand::Copy(_) | Operand::Move(_)),
            ..
        } => true,
        // Trust (2026-10-08): a cast to a slice/str FAT pointer defines only
        // its length ties (`guards::push_cast_slice_len`), the same kind of
        // pinned true equality as a copy's: the elaborated `Box<[T]>` deref
        // `_10 = copy (_1.0.0) as *const [T]; _0 = (*_10)[_2]` reads `_10`'s
        // length in the block that defines it.
        Statement::Assign {
            rvalue: Rvalue::Cast(Operand::Copy(_) | Operand::Move(_), to_ty),
            ..
        } => matches!(
            to_ty,
            Ty::RawPtr { pointee, .. } | Ty::Ref { inner: pointee, .. }
                if matches!(pointee.as_ref(), Ty::Slice { .. } | Ty::Str)
        ),
        _ => false,
    }
}

pub(super) fn block_has_copy_tie_candidate_until(
    block: &trust_types::BasicBlock,
    end: usize,
) -> bool {
    let end = end.min(block.stmts.len());
    block.stmts[..end].iter().any(stmt_is_copy_tie_candidate)
}

pub(super) fn v2_formula_with_copy_ties_at_point_recorded(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    end: usize,
    formula: Formula,
) -> (Formula, Formula, Vec<Formula>) {
    let sv = super::stmt_versions_for(func);
    let body = version_rename_owned_at(formula, &sv, func, block.id, end);
    if !block_has_copy_tie_candidate_until(block, end) {
        return (body.clone(), body, Vec::new());
    }
    let defs: Vec<Formula> =
        guards::extract_block_definitions_until_versioned_indexed(func, block, end)
            .into_iter()
            .filter(|(k, _)| block.stmts.get(*k).is_some_and(stmt_is_copy_tie_candidate))
            // Same refusal as the slice-length ties: a name spelled through an
            // `Index(l)` segment with a multi-valued `l` denotes a different slot at
            // different points, so a fact keyed on it is a claim about all of them.
            .filter(|(_, d)| !formula_mentions_non_ssa_index_segment(func, d))
            // Each tie is pinned at ITS OWN statement (round A11), never at a later
            // reseat of its subject.
            .map(|(k, d)| version_block_def_at_establish(&sv, func, block, (k + 1).min(end), d))
            .filter_map(|d| pin_bare_reads_rewritten_before(&sv, func, block, end, d))
            .collect();
    let (combined, kept) = combine_block_defs_as_recipe(func, defs, body.clone());
    (combined, body, kept)
}

/// The place name a block-definition fact DEFINES: the top-level lhs of an `Eq`
/// or a range comparison (`Lt`/`Le`/`Gt`/`Ge`), with any `#token` stripped.
/// `None` for shapes with no single defined subject.
pub(super) fn block_def_subject(def: &Formula) -> Option<&str> {
    let lhs = match def {
        Formula::Eq(l, _)
        | Formula::Lt(l, _)
        | Formula::Le(l, _)
        | Formula::Gt(l, _)
        | Formula::Ge(l, _) => l,
        _ => return None,
    };
    match &**lhs {
        Formula::Var(name, _) => Some(name.split('#').next().unwrap_or(name)),
        // Float value-definitions wrap the destination var in `FpFromBits` to
        // lift its bit pattern into FP space (lhs = FpFromBits { bits: Var(dest) }).
        // The subject is the inner var — peek through so the staleness /
        // clobber-dedup / versioning machinery recognizes a def of `dest`.
        // (Without this a stale FP def could survive a reassignment of `dest`
        // and discharge a goal about the new value — a false-PROVE.)
        Formula::FpFromBits { bits, .. } => match &**bits {
            Formula::Var(name, _) => Some(name.split('#').next().unwrap_or(name)),
            _ => None,
        },
        _ => None,
    }
}

/// The statement index in `block` that ESTABLISHES `base`: the latest real
/// Assign/SetDiscriminant in `stmts[..end]` whose destination IS `base` or an
/// ancestor of it, or whose derived length `base` is. An opaque deref-store
/// establishes the names in its own textual tree, and nothing else: the other
/// places it may havoc (the version oracle counts those writes via
/// `stmt_writes_name`) are not DEFINED by it. `None` when no in-block statement
/// defines `base`.
///
/// Trust: 2026-09-16 (round A11) — `end` is the establish search's exclusive
/// bound and MUST be the def's own statement index + 1 whenever the caller has it
/// (`guards::extract_block_definitions_indexed` and its versioned twin tag every
/// def). With `end = stmts.len()` the search returns the LATEST ancestor write in
/// the block, which is a later reseat of the subject whenever one exists (`p.0 =
/// 3; p = q` — the field def re-stamped onto `p = q`'s token, the post-reseat
/// read's own; a certified false PROVE). Bounded by the def's own statement, the
/// result is that statement itself (its destination IS the subject, or the
/// subject's base for `x*` / `x__slice_len`) or an ancestor write that PRECEDES
/// it — never one that follows.
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
                && crate::is_projection_segment_lead(base.as_bytes()[dest.len()]))
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
            // An opaque pointer can havoc aliases without defining their values,
            // but an explicit store DEFINES every name in its own textual tree:
            // the destination, its fields (`*p = S { .. }` defines `p*.0`) and its
            // derived length (`*s = t` defines `s*__slice_len`). That tree is
            // exactly what `establishes` accepts, and an alias is never in it. In
            // particular, `self.field = n` must advance the field's subject token
            // even though `self` is a parameter with no local referent.
            //
            // Trust (2026-09-29): the gate admitted the exact destination only, so
            // the derived length `s*__slice_len == t__slice_len` of a whole-pointee
            // store `*s = t` shipped BARE — the function-entry spelling — and an
            // earlier `let b = s.as_bytes()` took the new string's length (audit
            // round 2). Opacity (`deref_store_is_opaque`, asked on the written
            // place since 2026-09-18) still decides what a store HAVOCS; it no
            // longer narrows what the store defines.
            let dest = crate::place_to_var_name(func, place);
            establishes(&dest)
        }
        Statement::SetDiscriminant { place, .. } => {
            establishes(&crate::place_to_var_name(func, place))
        }
        _ => false,
    })
}

/// Re-spell every read of the establish-versioned `def` that is still BARE — the
/// value it read was the ENTRY one — when a statement of `block` rewrites that name
/// before the use point `end`: as `name#pre_s{b}_{w}`, the value just before the
/// first such statement `w`, the symbol `pin_in_place_update_reads` mints for the
/// same value. `None` (the caller drops the def, a weakening) when the def's own
/// subject is bare and rewritten, when no rewriting statement can be located, or
/// when a minted symbol would collide with a local's name. A def with no subject
/// passes through unchanged.
///
/// Trust (2026-09-29): the same-block lanes conjoin these defs onto a body renamed
/// at `end`, and the obligation's use-point rename then stamps every `#`-free name
/// with its version AT `end`. A bare read is the entry value only until the first
/// in-block write, so a def taken before that write and used after it became a
/// claim about the NEW value: `let old = x; x = 0; a[old | x]` (a `mut` parameter;
/// the 2026-09-17 pack proves it) and `let old = p.0; p.0 = 0; ..` were PROVED on a
/// `[u8; 4]` and index out of bounds for `x = 7`. `60888aafec1` widened it to every
/// whole-pointee store (`*p = 0` now establishes its def at the token the stamped
/// read also got), which an audit measured in the bounds, overflow and div/rem
/// lanes (`tests/ui/trust/read_before_a_same_block_write_keeps_the_old_value_refused.rs`).
pub(super) fn pin_bare_reads_rewritten_before(
    sv: &StmtVersionCtx,
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    end: usize,
    def: Formula,
) -> Option<Formula> {
    // Only a def with a subject was versioned at an establish point, which is what
    // makes a bare read there the ENTRY value (no write reaches it). A def with no
    // recoverable subject (a range fact over several names) comes back from
    // `version_block_def_at_establish` unchanged, bare everywhere, and a bare name in
    // it may be a read taken AFTER a write: pinning that to the pre-write value would
    // be a false fact. Such a def keeps its old handling (an audit, 2026-09-30).
    let Some(subject) = block_def_subject(&def) else { return Some(def) };
    let mut bare_names: Vec<&str> = Vec::new();
    let mut subject_rewritten = false;
    trust_types::for_each_free_variable_name(&def, &mut |name| {
        if !subject_rewritten
            && !name.contains('#')
            && !bare_names.contains(&name)
            && sv.version_token_at(func, block.id, end, name).is_some()
        {
            if subject == name {
                subject_rewritten = true;
            } else {
                bare_names.push(name);
            }
        }
    });
    // A bare SUBJECT was never established; a def about a rewritten place with
    // no establish point says nothing this lane can pin.
    if subject_rewritten {
        return None;
    }
    if bare_names.is_empty() {
        return Some(def);
    }
    if bare_names.len() > 1 {
        bare_names.sort_unstable();
    }
    let mut renames: Vec<(String, String)> = Vec::with_capacity(bare_names.len());
    for name in bare_names {
        let w = sv.first_writer_before(func, block, end, name)?;
        let minted = format!("{name}#{PRE_WRITE_SENTINEL_PREFIX}_s{}_{w}", block.id.0);
        if sv.has_hash_local_named(&minted) {
            return None;
        }
        renames.push((name.to_string(), minted));
    }
    if renames.is_empty() {
        return Some(def);
    }
    Some(def.map(&mut |node| match node {
        Formula::Var(name, sort) => match renames.iter().find(|(from, _)| *from == name) {
            Some((_, to)) => Formula::Var(to.clone(), sort),
            None => Formula::Var(name, sort),
        },
        other => other,
    }))
}

/// The statement in `block[..end]` that ESTABLISHES a block def about `subj` — the
/// one rule the establish-point consumers ask ([`version_block_def_at_establish`],
/// `assert_refutation`'s range pinning, the test-only subsumption check). The one
/// exception is `path_defs::pin_in_place_update_reads`, which keeps the narrower
/// base-keyed search on purpose (its doc says why: widening it needs its own recorded decision).
///
/// The search is keyed on the SUBJECT itself, `x*` included. A deref subject has two
/// establishing writes, and [`block_def_establish_stmt`] matches both against it: the
/// borrow `x = &..` of its base (an ANCESTOR write of `x*`, since `*` is a projection
/// lead) for the referent def `x* == y`, and a store THROUGH `x` (`*x = v`, whose
/// destination IS `x*`) for the stored-value def `x* == v`.
///
/// Trust (2026-09-30, the r8c union review's F2 closure controls). Every site
/// searched the BASE `x` instead (`subj.strip_suffix('*')`), which finds only the
/// borrow: a store's def `x* == v` had no establish point and was threaded BARE into
/// every successor, where it shared its symbol with the bare read of `x*` BEFORE the
/// store. `let i = *m; if i < s.len() { *m = usize::MAX; s[*m] }` then carried
/// `i == m*` and `m* == usize::MAX` together, so the guard read `usize::MAX <
/// s.len()` and the `[slice]` row was kernel-certified PROVED on a body that
/// panics — for a raw-pointer parameter, a raw pointer behind `&` or `&mut`, and a
/// closure's captured pointer, with or without a `&raw mut` reborrow
/// (tests/data/shared_reach_pointer_havoc.rs).
pub(crate) fn def_subject_establish_stmt(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    subj: &str,
    end: usize,
) -> Option<usize> {
    block_def_establish_stmt(func, block, subj, end)
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
///
/// `end` bounds the establish search (`block_def_establish_stmt`): pass the def's
/// OWN statement index + 1 (round A11) — see that function's doc for why the block
/// end is the wrong bound.
pub(super) fn version_block_def_at_establish(
    sv: &StmtVersionCtx,
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    end: usize,
    def: Formula,
) -> Formula {
    // Trust (2026-09-30, stale-read seal): a def this function cannot pin at an
    // establish statement used to be returned UNSTAMPED, and every later
    // whole-formula rename then stamped it at the CONSUMER's point — a fact about
    // the value at `end` read against whatever the place held there. Pin it at
    // `end` (just after the emitting statement, for every indexed caller) and seal
    // what stays bare; a seal collision drops the fact (fail closed).
    let pin_at_end = |def: Formula| -> Formula {
        let point = end.min(block.stmts.len());
        let renamed = version_rename_owned_at(def, sv, func, block.id, point);
        super::path_defs::seal_bare_reads(sv, func, block.id, point, renamed)
            .unwrap_or(Formula::Bool(true))
    };
    // Subjectless facts (a cast's `Implies`, ...) are pinned at `end` too.
    let Some(subj) = block_def_subject(&def) else { return pin_at_end(def) };
    if subj.starts_with("arr$") {
        return def;
    }
    // GEN-KEY == SUBJECT, the refusal `pin_in_place_update_reads` already
    // carries (path_defs.rs), replicated at this second rebind site. A def
    // whose raw lhs is a plain `Var` containing '#' — a caller-built local
    // literally named `n#x` — has gen-key `n#x` but recovered subject `n`;
    // rebinding it onto the BASE local's establish token would ship a
    // hypothesis about a place this def never wrote (reachable since the
    // gen-sets widened to raw destinations, which gives the base an establish
    // point). Refuse. The `FpFromBits` peek-through keeps working:
    // `formula_def_name` is `None` there, and the split subject IS the write's
    // real destination.
    if let Formula::Eq(l, _)
    | Formula::Lt(l, _)
    | Formula::Le(l, _)
    | Formula::Gt(l, _)
    | Formula::Ge(l, _) = &def
        && let Formula::Var(raw, _) = &**l
        && raw != subj
    {
        // Trust (2026-09-30, stale-read seal): refuse by DROPPING the fact — the
        // unstamped def returned here before would be re-stamped by the
        // consumer's rename at a point this def never described.
        return Formula::Bool(true);
    }
    // Trust (2026-09-30, P3 of the `vac` root cause, and the r8c union review's F2
    // closure controls, which found it independently): search with the FULL subject.
    // Stripping `*` searched for the base `x`, so a whole-deref store `(*x) = v`
    // (which writes `x*`, not `x`) had NO establish statement and the def was
    // returned bare — then relabelled with whatever token the consumer's rename
    // gave `x*` (`*x = a; ext(); *x = c` proved `a == c`). A deref subject `x*` is
    // established by the borrow `x = &..` of its base OR by a store through it;
    // `def_subject_establish_stmt` is the one statement of that rule.
    let Some(k) = def_subject_establish_stmt(func, block, subj, end) else {
        return pin_at_end(def);
    };
    let subj = subj.to_owned();
    // 1. all reads at the read-point k (values BEFORE the defining write).
    let read_versioned = version_rename_owned_at(def, sv, func, block.id, k);
    // Trust (2026-09-30, P1 of the `vac` root cause): SEAL the reads still bare
    // at `k` so no later rename re-stamps them with a post-write token (the
    // `s.f#s0_0 == !s.f#s0_0` recurrence). A collision drops the fact.
    let Some(read_versioned) =
        super::path_defs::seal_bare_reads(sv, func, block.id, k, read_versioned)
    else {
        return Formula::Bool(true);
    };
    // 2. re-version the DEFINED subject (top-level lhs) to k+1 (value AFTER it).
    let new_tok = sv.version_token_at(func, block.id, k + 1, &subj);
    // Trust (2026-09-30, stale-read seal): a subject some point versions but that
    // has NO token just after its own establishing write is an inconsistency; a
    // bare subject would be re-stamped by the consumer. Drop the fact.
    if new_tok.is_none() && sv.ever_versioned(func, &subj) {
        return Formula::Bool(true);
    }
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
    fn rewrite_lhs(l: Formula, subj: &str, tok: &Option<String>) -> Formula {
        match l {
            Formula::Var(mut name, s) => match tok {
                Some(t) => {
                    name.clear();
                    name.reserve(subj.len() + 1 + t.len());
                    name.push_str(subj);
                    name.push('#');
                    name.push_str(t);
                    Formula::Var(name, s)
                }
                None => {
                    if name != subj {
                        name.clear();
                        name.push_str(subj);
                    }
                    Formula::Var(name, s)
                }
            },
            Formula::FpFromBits { bits, eb, sb } => Formula::FpFromBits {
                bits: Box::new(rewrite_lhs(*bits, subj, tok)),
                eb,
                sb,
            },
            other => other,
        }
    }
    match def {
        Formula::Eq(l, r) => Formula::Eq(Box::new(rewrite_lhs(*l, subj, &tok)), r),
        Formula::Lt(l, r) => Formula::Lt(Box::new(rewrite_lhs(*l, subj, &tok)), r),
        Formula::Le(l, r) => Formula::Le(Box::new(rewrite_lhs(*l, subj, &tok)), r),
        Formula::Gt(l, r) => Formula::Gt(Box::new(rewrite_lhs(*l, subj, &tok)), r),
        Formula::Ge(l, r) => Formula::Ge(Box::new(rewrite_lhs(*l, subj, &tok)), r),
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
        // The definitional fact is about the `CheckedBinaryOp` at `k`: bound the
        // establish search there (round A11), not at the block end.
        version_block_def_at_establish(sv, func, block, (k + 1).min(block.stmts.len()), fact)
    } else {
        version_rename_owned_at(fact, sv, func, block.id, k)
    }
}

/// Trust (THE TIME AXIS of the terminator-fact channel): does any ARGUMENT of
/// this call render to a variable whose BASE name is `name`?
///
/// [`version_terminator_dest_fact`] rewrites EVERY occurrence of its subject's
/// base name to the POST-call token. That is a PIN when every such occurrence
/// denotes the value the terminator just defined, and a SILENT TIME SHIFT when
/// one of them is a PRE-call read — an argument's own entry value, re-read
/// against the post-state.
///
/// The shift is not "one imprecise fact". Every producer on this channel emits
/// either an equality pinning the dest to a function of the arguments
/// (`wrapping_neg`, `saturating_*`, the modeled intrinsics, `from_bits`) or a
/// relation between the dest and an argument (min/max/clamp, and a rebound
/// callee `ensures`). Collapse the two symbols and `dest == f(arg)` becomes the
/// fixpoint equation `d == f(d)` and `result > n` becomes `n > n` — one
/// STRENGTHENS the hypothesis, the other is outright UNSATISFIABLE. These facts
/// are CONJOINED into the successors' guard set under the "SAT iff violation"
/// convention, so a false hypothesis discharges every obligation in that scope,
/// including obligations about locals the callee's contract never mentions.
///
/// The predicate is EXACT for the argument channel: the rewrite keys on the base
/// name, so an argument matters here precisely when it renders to one. A
/// PROJECTED read of the dest local (`n.0` where the dest is `n`) renders to a
/// different base name, is not rewritten, and is correctly admitted.
///
/// RESIDUAL, stated rather than implied: a producer that traces BACKWARD from an
/// argument can reach a local that is not itself an argument —
/// `int_try_from_unwrap_or_facts`'s `_r = try_from(_x)` conduit is the one in
/// tree. If that `_x` were the dest local this predicate would not see it. The
/// durable repair for the whole channel is to build the dest occurrence ALREADY
/// versioned: `version_rename_at` passes `#`-bearing names through untouched, so
/// the blanket rewrite would not be needed at all. That is a change across eight
/// fact producers with pinned SMT-LIB in each; this guard is not it.
pub(super) fn terminator_args_read_name(
    func: &VerifiableFunction,
    args: &[Operand],
    name: &str,
) -> bool {
    args.iter().any(|arg| {
        if matches!(
            arg,
            Operand::Constant(
                ConstValue::Int(_) | ConstValue::Uint(..) | ConstValue::Bool(_) | ConstValue::Unit
            )
        ) {
            return false;
        }
        trust_types::any_free_variable_name(
            &crate::operand_to_formula(func, arg),
            &mut |v| v.split('#').next() == Some(name),
        )
    })
}

/// Version a THREADED fact established by the block's TERMINATOR (a modeled
/// total-call / min / max / clamp bound on a `Call` dest). The terminator runs
/// after every statement, so the dest is pinned to the terminator marker `s{b}_t`
/// (matching the terminator-aware OUT in the inter-block oracle); other operands are
/// read at the block terminal. A successor that REASSIGNS the dest reads a distinct
/// token, disconnecting the stale bound.
///
/// PRECONDITION, NOW ENFORCED: every occurrence of `dest_name` in `fact` must
/// denote the value this terminator DEFINES. `None` — no fact at all — when one
/// of them provably does not, i.e. when an argument of this same call renders to
/// `dest_name` (see [`terminator_args_read_name`] for what the shift does and
/// what it costs). Until 2026-08-31 this was an UNSTATED property of the MIR
/// that reaches `TrustVerify` (rustc evaluates call arguments into fresh
/// temporaries, and neither `CopyProp` nor `DestinationPropagation` merges a
/// local read by a call terminator with that terminator's destination): no gate
/// on the injection path refused the shape, and the only thing preventing it was
/// emergent. Refusing costs a fact; retiming an argument read costs the
/// soundness argument for every fact this channel carries.
pub(super) fn version_terminator_dest_fact(
    sv: &StmtVersionCtx,
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    dest_name: &str,
    fact: Formula,
) -> Option<Formula> {
    if let Terminator::Call { args, .. } = &block.terminator
        && terminator_args_read_name(func, args, dest_name)
    {
        return None;
    }
    let read_versioned = version_rename_owned_at(fact, sv, func, block.id, block.stmts.len());
    if !trust_types::any_free_variable_name(&read_versioned, &mut |name| {
        name.split('#').next() == Some(dest_name)
    }) {
        return Some(read_versioned);
    }
    use std::fmt::Write as _;
    Some(read_versioned.map(&mut |node| match node {
        Formula::Var(mut name, sort) if name.split('#').next() == Some(dest_name) => {
            name.truncate(dest_name.len());
            let _ = write!(name, "#s{}_t", block.id.0);
            Formula::Var(name, sort)
        }
        other => other,
    }))
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
        let havoc: FxHashSet<String> =
            deref_store_havoc_names(func, block).iter().cloned().collect();
        if havoc.is_empty() {
            continue;
        }
        let mut defs = guards::extract_block_definitions_indexed(func, block);
        defs.extend(
            extract_set_discriminant_definitions_until(func, block, end)
                .into_iter()
                .map(|d| (end, d)),
        );
        for (k, d) in &defs {
            if formula_survives_redefs(d, &havoc) {
                continue; // the kill KEEPS this def — nothing to subsume.
            }
            let Some(subj) = block_def_subject(d) else {
                residual += 1; // kill drops a subject-less def; versioning can't pin it.
                continue;
            };
            let subj_havoced = havoc.iter().any(|h| write_rebinds(h, subj));
            if !subj_havoced {
                continue; // RHS-only havoc: versioning keeps the def soundly.
            }
            let pinned = !subj.starts_with("arr$")
                && def_subject_establish_stmt(func, block, subj, (k + 1).min(end)).is_some();
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
    func: &VerifiableFunction,
    defs: Vec<Formula>,
    formula: Formula,
) -> (Formula, Vec<Formula>) {
    let kept = relevant_block_def_indices(func, &defs, &formula);
    conjoin_kept_block_defs(defs, &kept, formula)
}

/// [`combine_relevant_block_defs_recorded`], the combination recorded as a recipe (its
/// candidates, and how many the rule kept) while the generation writes into a context
/// (T3 C08, `super::recipes`), so the row sink can join the row as a Spine row. The
/// returned formula and kept list are exactly the eager ones, which stay authoritative
/// (L4-ORACLE-1); without an open recipe log nothing is recorded or copied.
pub(super) fn combine_block_defs_as_recipe(
    func: &VerifiableFunction,
    defs: Vec<Formula>,
    formula: Formula,
) -> (Formula, Vec<Formula>) {
    if defs.is_empty() {
        return (formula, Vec::new());
    }
    let kept = relevant_block_def_indices(func, &defs, &formula);
    if !super::recipes::recording() {
        return conjoin_kept_block_defs(defs, &kept, formula);
    }
    let facts: Vec<Formula> = kept.iter().map(|&index| defs[index].clone()).collect();
    let combined = if facts.is_empty() {
        formula
    } else {
        let mut conjuncts = Vec::with_capacity(facts.len() + 1);
        conjuncts.extend(facts.iter().cloned());
        conjuncts.push(formula);
        Formula::And(conjuncts)
    };
    super::recipes::record(defs, facts.len(), &combined);
    (combined, facts)
}

fn combine_block_defs_as_recipe_only(
    func: &VerifiableFunction,
    defs: Vec<Formula>,
    formula: Formula,
) -> Formula {
    if defs.is_empty() {
        return formula;
    }
    let kept = relevant_block_def_indices(func, &defs, &formula);
    if !super::recipes::recording() {
        if kept.is_empty() {
            return formula;
        }
        let mut defs = defs;
        let mut conjuncts: Vec<Formula> = Vec::with_capacity(kept.len() + 1);
        for &index in &kept {
            if let Some(slot) = defs.get_mut(index) {
                conjuncts.push(std::mem::replace(slot, Formula::Bool(false)));
            }
        }
        conjuncts.push(formula);
        return Formula::And(conjuncts);
    }
    let kept_len = kept.len();
    let combined = if kept.is_empty() {
        formula
    } else {
        let mut conjuncts: Vec<Formula> = Vec::with_capacity(kept_len + 1);
        for &index in &kept {
            conjuncts.push(defs[index].clone());
        }
        conjuncts.push(formula);
        Formula::And(conjuncts)
    };
    super::recipes::record(defs, kept_len, &combined);
    combined
}

/// The positions in `defs` of the facts the block-def relevance rule keeps for
/// `formula`, in order (the rule [`combine_relevant_block_defs_recorded`] documents).
fn relevant_block_def_indices<'a>(
    func: &VerifiableFunction,
    defs: &'a [Formula],
    formula: &'a Formula,
) -> Vec<usize> {
    if defs.is_empty() {
        return Vec::new();
    }

    let mut needed: FxHashSet<&'a str> = FxHashSet::default();
    let mut bound: Vec<&'a str> = Vec::new();
    visit_formula_var_names(formula, &mut bound, &mut |raw| {
        needed.insert(relevance_var_name_str(func, raw));
    });
    if needed.is_empty() {
        return Vec::new();
    }

    // Walk defs in reverse so a def of `_4 = _3` pulls in `_3`'s def too.
    let mut keep_rev: Vec<usize> = Vec::new();
    let mut def_vars: Vec<&'a str> = Vec::new();
    for (index, def) in defs.iter().enumerate().rev() {
        def_vars.clear();
        bound.clear();
        let mut intersects = false;
        visit_formula_var_names(def, &mut bound, &mut |raw| {
            let rel = relevance_var_name_str(func, raw);
            if !intersects && needed.contains(rel) {
                intersects = true;
            }
            if !def_vars.contains(&rel) {
                def_vars.push(rel);
            }
        });
        // Heuristic: a def is relevant iff its destination (the lhs of the top-level Eq, if any)
        // is in `needed`, OR any of its free variables intersects `needed`. Either way we add
        // every free variable of the def to `needed` so deeper dependencies are picked up next.
        if intersects {
            needed.extend(def_vars.drain(..));
            keep_rev.push(index);
        }
    }
    keep_rev.reverse();
    keep_rev
}

/// `And([kept.., formula])` and the kept facts, moved out of `defs` (`kept` lists their
/// positions in order); `formula` itself when nothing is kept.
fn conjoin_kept_block_defs(
    mut defs: Vec<Formula>,
    kept: &[usize],
    formula: Formula,
) -> (Formula, Vec<Formula>) {
    if kept.is_empty() {
        return (formula, Vec::new());
    }
    let kept: Vec<Formula> = kept
        .iter()
        .filter_map(|&index| {
            defs.get_mut(index).map(|slot| std::mem::replace(slot, Formula::Bool(false)))
        })
        .collect();
    let mut conjuncts: Vec<Formula> = Vec::with_capacity(kept.len() + 1);
    conjuncts.extend(kept.iter().cloned());
    conjuncts.push(formula);
    (Formula::And(conjuncts), kept)
}

/// Collect a formula's variable names in the spelling the FINAL
/// `normalize_ssa_version_tokens` pass will hand the solver: a `base#tok` whose
/// `base` is a local all of whose versions provably denote ONE value is collected
/// as the bare `base`.
///
/// This exists so the relevance filter's notion of "same name" matches the
/// emitter's. Two lanes legitimately stamp the same SSA local differently — a
/// block definition carries its ESTABLISH token (`_8#s5_0`) while a formula
/// renamed at a successor block carries the ENTRY token naming the same reaching
/// def (`_8#e_s5_0`) — and both collapse to `_8` before the solver ever sees
/// them. Comparing the raw spellings made the filter believe the def and the use
/// were unrelated and drop the def, which is how `if x < 0 { 0 } else { x / 2 }`
/// reached the solver with `x / 2` unstated and its true postcondition
/// `result >= 0` refutable.
///
/// This is a RELEVANCE-ONLY normalization: kept defs are conjoined verbatim, with
/// their own tokens, and nothing in the emitted formula is renamed here.
///
/// SOUNDNESS, against the one hazard this file exists to protect. The staleness
/// kill works by name-disjointness — a def whose subject was rewritten carries a
/// token the use-point read does not — so the question is whether this can
/// resurrect a stale def into a position where it constrains a live read. It
/// cannot, for two independent reasons:
///
///   * A local is collapsed here only when `local_versions_collapse_to_bare`
///     holds, which means it is assigned once (or is a never-written parameter).
///     Such a local has no second value, so it has no stale version to
///     resurrect.
///   * A stale def of a REASSIGNED local keeps its token, because that local
///     does not collapse. The most this change can do is KEEP such a def when
///     its right-hand side happens to mention a collapsed local — and that def
///     still says something about a subject spelling nothing else in the query
///     reads. It constrains a variable with no other occurrence, which is noise,
///     not a proof.
///
/// The decision is the same one `normalize_ssa_version_tokens` makes on the same
/// predicate, so this only aligns the filter with what the solver will actually
/// be handed.
pub(super) fn collect_relevance_var_names(
    func: &VerifiableFunction,
    formula: &Formula,
    out: &mut FxHashSet<String>,
) {
    let mut bound = Vec::new();
    visit_formula_var_names(formula, &mut bound, &mut |raw| {
        let rel = relevance_var_name_str(func, raw);
        if !out.contains(rel) {
            out.insert(rel.to_string());
        }
    });
}

/// Borrowed form of [`relevance_var_name`]: returns the post-collapse spelling as a
/// `&str` without heap allocation.
pub(super) fn relevance_var_name_str<'a>(func: &VerifiableFunction, name: &'a str) -> &'a str {
    if super::contract_vcs::is_return_slot_name(name) {
        return "_0";
    }
    let Some((base, _tok)) = name.split_once('#') else {
        return name;
    };
    // A loop-transition HAVOC is not a second spelling of the bare local —
    // `normalize_ssa_version_tokens` refuses to collapse it, and so must this.
    // Nor is a guard-local path-guard spelling (`GUARD_VALUE_TOKEN_PREFIX`).
    if crate::version_token_is_loop_transition_havoc(name)
        || crate::version_token_is_guard_value(name)
    {
        return name;
    }
    let base_local = crate::fn_memo::whole_local_index_by_base(func, base, |l| {
        crate::place_to_var_name(func, &Place::local(l))
    });
    match base_local {
        Some(local) if super::discharge::local_versions_collapse_to_bare(func, local) => base,
        _ => name,
    }
}

/// One name, in the post-collapse spelling. Identity unless the name is a
/// versioned whole local whose versions provably denote a single value. The row sink
/// lists these as the context's relevance names (T3 C08, `super::recipes`).
#[cfg_attr(not(test), allow(dead_code))]
pub(super) fn relevance_var_name(func: &VerifiableFunction, name: &str) -> String {
    // Return-slot versions share a relevance bucket so a result clause can
    // retain the definitions needed along its path. This is only a fact-selection
    // heuristic: retained facts keep their distinct statement-version names.
    // In particular, historical return values must not be renamed to the final one.
    //
    // Without this, a return assignment the block-def lane CAN lower but the CHC
    // encoder cannot — `_0 = x >> 1`, written straight into the return slot — is
    // dropped here on a token mismatch (`_0#s3_0` against the body's merged
    // `_0#s1_0_s3_0`), the row then has no pin at all, and the silent-weakening
    // tripwire fails it closed to a visible unsupported row. Measured: the `i64`
    // spelling proves and the `i32` one did not, for no reason except that rustc
    // routed one through a temporary and the other straight into `_0`.
    //
    // This cannot launder a stale definition into a live read. The unifier that
    // licenses it requires EXACTLY ONE return-slot pin version and declines
    // otherwise, so a second definition makes it do nothing rather than choose;
    // and outside the postcondition lane no unification runs at all, leaving a
    // kept definition constraining a name nothing else reads.
    relevance_var_name_str(func, name).to_string()
}

pub(super) fn collect_formula_var_names(formula: &Formula, out: &mut FxHashSet<String>) {
    let mut bound = Vec::new();
    visit_formula_var_names(formula, &mut bound, &mut |name| {
        if !out.contains(name) {
            out.insert(name.to_string());
        }
    });
}

fn visit_formula_var_names<'a>(
    formula: &'a Formula,
    bound: &mut Vec<&'a str>,
    on_var: &mut impl FnMut(&'a str),
) {
    match formula {
        Formula::Var(name, _) => {
            if !bound.contains(&name.as_str()) {
                on_var(name.as_str());
            }
        }
        Formula::Bool(_) | Formula::Int(_) | Formula::UInt(_) | Formula::BitVec { .. } => {}
        Formula::Not(inner) | Formula::Neg(inner) => visit_formula_var_names(inner, bound, on_var),
        Formula::BvNot(inner, _)
        | Formula::BvToInt(inner, _, _)
        | Formula::IntToBv(inner, _)
        | Formula::BvZeroExt(inner, _)
        | Formula::BvSignExt(inner, _) => visit_formula_var_names(inner, bound, on_var),
        Formula::BvExtract { inner, .. } => visit_formula_var_names(inner, bound, on_var),
        Formula::And(children) | Formula::Or(children) => {
            for child in children {
                visit_formula_var_names(child, bound, on_var);
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
            visit_formula_var_names(a, bound, on_var);
            visit_formula_var_names(b, bound, on_var);
        }
        Formula::Ite(c, t, e) | Formula::Store(c, t, e) => {
            visit_formula_var_names(c, bound, on_var);
            visit_formula_var_names(t, bound, on_var);
            visit_formula_var_names(e, bound, on_var);
        }
        Formula::Forall(bindings, body) | Formula::Exists(bindings, body) => {
            // Skip names introduced by the quantifier; they're locally bound.
            let prev_len = bound.len();
            for (name, _) in bindings {
                bound.push(name.as_str());
            }
            visit_formula_var_names(body, bound, on_var);
            bound.truncate(prev_len);
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
        | Formula::FpIsPositive(a) => visit_formula_var_names(a, bound, on_var),
        Formula::FpFromBits { bits, .. } => visit_formula_var_names(bits, bound, on_var),
        Formula::FpRem(a, b)
        | Formula::FpMin(a, b)
        | Formula::FpMax(a, b)
        | Formula::FpEq(a, b)
        | Formula::FpLt(a, b)
        | Formula::FpLe(a, b)
        | Formula::FpGt(a, b)
        | Formula::FpGe(a, b)
        | Formula::FpSqrt(a, b) => {
            visit_formula_var_names(a, bound, on_var);
            visit_formula_var_names(b, bound, on_var);
        }
        Formula::FpAdd(a, b, c)
        | Formula::FpSub(a, b, c)
        | Formula::FpMul(a, b, c)
        | Formula::FpDiv(a, b, c) => {
            visit_formula_var_names(a, bound, on_var);
            visit_formula_var_names(b, bound, on_var);
            visit_formula_var_names(c, bound, on_var);
        }
        Formula::FpFma(a, b, c, d) => {
            visit_formula_var_names(a, bound, on_var);
            visit_formula_var_names(b, bound, on_var);
            visit_formula_var_names(c, bound, on_var);
            visit_formula_var_names(d, bound, on_var);
        }
        // FP literals / rounding-mode carry no variables.
        Formula::FpConst { .. }
        | Formula::FpNaN { .. }
        | Formula::FpInf { .. }
        | Formula::FpZero { .. }
        | Formula::FpRoundingMode(_) => {}
        // `[v; N]` as a constant array: the value's vars are the only ones.
        Formula::ConstArray { value, .. } => visit_formula_var_names(value, bound, on_var),
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
    // Public TrustIR is not SSA, and a write through an alias can redefine the
    // condition just as surely as a direct assignment. Because `cond_place` is
    // projection-free, every direct `Assign` to `cond_place` writes `cond_name`:
    // find the last direct assignment first, verify its `BinaryOp` shape, and
    // only check `(stmt_index + 1..block.stmts.len())` for an intervening alias
    // write when statements follow the comparison.
    let stmt_index = (0..block.stmts.len()).rev().find(|&k| {
        matches!(&block.stmts[k], Statement::Assign { place, .. } if place == cond_place)
    })?;
    let Statement::Assign { rvalue: Rvalue::BinaryOp(op, lhs, rhs), .. } =
        &block.stmts[stmt_index]
    else {
        return None;
    };
    if guards::value_local_is_unstable(func, cond_place.local) {
        return None;
    }
    let has_later_stmts = stmt_index + 1 < block.stmts.len();
    let cond_name = if has_later_stmts || projected_inputs {
        let name = place_to_var_name(func, cond_place);
        if has_later_stmts
            && (stmt_index + 1..block.stmts.len())
                .any(|later_index| stmt_writes_name(func, block, later_index, &name))
        {
            return None;
        }
        Some(name)
    } else {
        None
    };

    // Public TrustIR is not SSA.  The terminator reads the boolean produced
    // here, so substituting the *later* value of either comparison operand
    // would prove a different assertion.  Reject a carrier whose input is
    // rewritten afterwards, and — unless the caller asked for the
    // projection-tolerant rule — keep the projection-free-temporary boundary
    // the shipped callers were measured against.
    let mut first_operand_name: Option<String> = None;
    let mut second_operand_name: Option<String> = None;
    for operand in [lhs, rhs] {
        if let Operand::Copy(input) | Operand::Move(input) = operand {
            let projection_admissible = if projected_inputs {
                input.projections.iter().all(|p| matches!(p, trust_types::Projection::Field(_)))
            } else {
                input.projections.is_empty()
            };
            if !projection_admissible
                || (!projected_inputs && input == cond_place)
                || guards::value_local_is_unstable(func, input.local)
            {
                return None;
            }
            if !projected_inputs {
                if has_later_stmts {
                    let name = place_to_var_name(func, input);
                    if first_operand_name.is_none() {
                        first_operand_name = Some(name);
                    } else if first_operand_name.as_ref() != Some(&name) {
                        second_operand_name = Some(name);
                    }
                }
            } else {
                let name = place_to_var_name(func, input);
                // The comparison must not read the flag it defines.
                if cond_name.as_deref().is_some_and(|cn| place_names_overlap(&name, cn)) {
                    return None;
                }
                if has_later_stmts {
                    if first_operand_name.is_none() {
                        first_operand_name = Some(name);
                    } else if first_operand_name.as_ref() != Some(&name) {
                        second_operand_name = Some(name);
                    }
                }
            }
        }
    }
    let writes_comparison_input = first_operand_name.is_some()
        && (stmt_index + 1..block.stmts.len()).any(|later_index| {
            first_operand_name
                .as_deref()
                .is_some_and(|name| stmt_writes_name(func, block, later_index, name))
                || second_operand_name
                    .as_deref()
                    .is_some_and(|name| stmt_writes_name(func, block, later_index, name))
        });
    if writes_comparison_input {
        return None;
    }
    Some((stmt_index, *op, lhs, rhs))
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
    v2_find_target_neg_statement(func, target).map(|(_, operand)| operand)
}

/// [`v2_find_target_neg_operand`], together with the unique `Neg`'s DESTINATION
/// place — the same statement under the same refusals, so `Some` here is `Some`
/// there and names the same operand.
///
/// Trust (SELF-GUARDED-LITERAL-OPERAND-1, 2026-10-12): the destination is what
/// types a WIDTH-LESS literal operand. A MIR `Neg`'s result type is its operand
/// type, but `crate::operand_ty` of a `ConstValue::Int` is derived from the
/// constant's VALUE (`i64` for `i32::MIN`), so both negation lanes read the width
/// of a literal from here through [`guards::bare_neg_machine_shape`].
pub(crate) fn v2_find_target_neg_statement(
    func: &VerifiableFunction,
    target: BlockId,
) -> Option<(&trust_types::Place, &Operand)> {
    let block = func.body.blocks.get(target.0)?;
    let mut found: Option<(usize, &trust_types::Place, &Operand)> = None;
    for (stmt_index, stmt) in block.stmts.iter().enumerate() {
        let Statement::Assign { place: dest, rvalue, .. } = stmt else {
            continue;
        };
        if let Rvalue::UnaryOp(trust_types::UnOp::Neg, operand) = rvalue {
            if found.is_some() {
                return None;
            }
            found = Some((stmt_index, dest, operand));
        }
    }
    let (stmt_index, dest, operand) = found?;
    // The source-block overflow condition compares the value that reaches the
    // normal target. If that target rewrites the negated local first, the
    // condition no longer authenticates this operation.
    if let Operand::Copy(place) | Operand::Move(place) = operand {
        if !place.projections.is_empty() || guards::value_local_is_unstable(func, place.local) {
            return None;
        }
        if stmt_index > 0 {
            let name = crate::place_to_var_name(func, place);
            if (0..stmt_index).any(|index| stmt_writes_name(func, block, index, &name)) {
                return None;
            }
        }
    }
    Some((dest, operand))
}
