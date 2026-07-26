// Lifting MIR operands and rvalues into MirSem. This is where the fragment
// boundary lives: a construct with no faithful MirSem image must fail to lift
// rather than lift approximately, because everything downstream treats a
// successful lift as exact. Casts, guards and comparisons each need their own
// resolution because MIR spells them through temporaries.

use super::*;

/// Trust: GAP-DEREF-SELF soundness — whether ANYTHING in `body` WRITES THROUGH
/// a deref of `local`: a STATEMENT write (`(*local) := …`,
/// `SetDiscriminant((*local), …)`, `Deinit(*local)`, `Retag(*local)`), a mutable
/// borrow/address of the dereferenced place, or a terminator destination/drop
/// rooted there. An immutable Rust reference can never be written through in
/// SAFE code, but this defends [`sem_operand_of_mir`]'s deref-self arm against a
/// malformed/adversarial body that nonetheless contains one.
///
/// Trust MIR is a public schema, so checking only places rooted at `local` is not
/// enough: a hand-built body can first copy the shared reference into another
/// local and then write through that alias. Build a whole-body MAY-alias closure
/// over type-preserving, unprojected shared-reference `Copy`/`Move` assignments
/// before scanning effects. The worklist is bounded by `body.locals.len()` and a
/// visited set makes malformed alias cycles terminate. This is deliberately
/// conservative across control flow and reassignments: once a local may have
/// held the reference, a write through it invalidates the entry-value model.
pub(crate) fn deref_write_exists(body: &trust_types::VerifiableBody, local: usize) -> bool {
    use std::collections::{HashSet, VecDeque};

    use trust_types::{Operand, Projection, Rvalue, Statement, Terminator, Ty};

    let shared_ref_types_match = |source: usize, destination: usize| {
        let Some(source_ty) = body.locals.get(source).map(|decl| &decl.ty) else {
            return false;
        };
        let Some(destination_ty) = body.locals.get(destination).map(|decl| &decl.ty) else {
            return false;
        };
        matches!(source_ty, Ty::Ref { mutable: false, .. })
            && matches!(destination_ty, Ty::Ref { mutable: false, .. })
            && source_ty.eq_ignoring_disc_index_safe(destination_ty)
    };

    let mut aliases = HashSet::from([local]);
    let mut pending = VecDeque::from([local]);
    let mut processed = 0usize;
    while let Some(source) = pending.pop_front() {
        processed += 1;
        if processed > body.locals.len().saturating_add(1) {
            // Impossible with the visited set for a well-indexed body. Treat an
            // internally inconsistent alias graph as a write, i.e. fail closed.
            return true;
        }
        for statement in body.blocks.iter().flat_map(|block| &block.stmts) {
            let Statement::Assign { place: destination, rvalue, .. } = statement else {
                continue;
            };
            let Rvalue::Use(Operand::Copy(source_place) | Operand::Move(source_place)) = rvalue
            else {
                continue;
            };
            if !destination.projections.is_empty()
                || !source_place.projections.is_empty()
                || source_place.local != source
                || !shared_ref_types_match(source, destination.local)
            {
                continue;
            }
            if aliases.insert(destination.local) {
                pending.push_back(destination.local);
            }
        }
    }

    let place_derefs_local = |place: &trust_types::Place| {
        aliases.contains(&place.local)
            && matches!(place.projections.first(), Some(Projection::Deref))
    };
    body.blocks.iter().flat_map(|b| &b.stmts).any(|s| match s {
        Statement::Assign { place, rvalue, .. } => {
            place_derefs_local(place)
                || matches!(rvalue,
                        Rvalue::Ref { mutable: true, place }
                            | Rvalue::AddressOf(true, place)
                            if place_derefs_local(place))
        }
        Statement::SetDiscriminant { place, .. }
        | Statement::Deinit { place }
        | Statement::Retag { place } => place_derefs_local(place),
        _ => false,
    }) || body.blocks.iter().any(|b| match &b.terminator {
        Terminator::Call { dest, atomic, .. } => {
            place_derefs_local(dest)
                || atomic.as_ref().is_some_and(|atomic| {
                    place_derefs_local(&atomic.place)
                        || atomic.dest.as_ref().is_some_and(place_derefs_local)
                })
        }
        Terminator::Drop { place, .. } => place_derefs_local(place),
        _ => false,
    })
}

/// Trust: W19 mutators inc-1 (2026-07-24) — [`deref_write_exists`] scoped to EXCLUDE a
/// single already-recognized write place (the field-setter's sole `(*self).fld` store).
/// Reuses the SAME shared-ref alias BFS + deref-write/`&mut`-of-deref detection, but the
/// recognized write is not itself counted — so a `true` means the receiver (or a
/// shared-ref alias of it) is written through / mutably reborrowed at SOME OTHER place,
/// which the field-setter recognizer's G2 declines fail-closed. Whole-body (live +
/// dead), so a dead-code alias write also declines (over-strict but sound). A `Place`
/// that is not `[Deref, ..]`-rooted can never equal a deref-write place, so passing a
/// non-deref `exclude` degrades to the base [`deref_write_exists`].
pub(crate) fn deref_write_exists_excluding(
    body: &trust_types::VerifiableBody,
    local: usize,
    exclude: &trust_types::Place,
) -> bool {
    use std::collections::{HashSet, VecDeque};

    use trust_types::{Operand, Projection, Rvalue, Statement, Terminator, Ty};

    let shared_ref_types_match = |source: usize, destination: usize| {
        let Some(source_ty) = body.locals.get(source).map(|decl| &decl.ty) else {
            return false;
        };
        let Some(destination_ty) = body.locals.get(destination).map(|decl| &decl.ty) else {
            return false;
        };
        matches!(source_ty, Ty::Ref { mutable: false, .. })
            && matches!(destination_ty, Ty::Ref { mutable: false, .. })
            && source_ty.eq_ignoring_disc_index_safe(destination_ty)
    };

    // Shared-ref alias closure — BYTE-IDENTICAL to `deref_write_exists`'s BFS.
    let mut aliases = HashSet::from([local]);
    let mut pending = VecDeque::from([local]);
    let mut processed = 0usize;
    while let Some(source) = pending.pop_front() {
        processed += 1;
        if processed > body.locals.len().saturating_add(1) {
            return true; // inconsistent alias graph → fail closed.
        }
        for statement in body.blocks.iter().flat_map(|block| &block.stmts) {
            let Statement::Assign { place: destination, rvalue, .. } = statement else {
                continue;
            };
            let Rvalue::Use(Operand::Copy(source_place) | Operand::Move(source_place)) = rvalue
            else {
                continue;
            };
            if !destination.projections.is_empty()
                || !source_place.projections.is_empty()
                || source_place.local != source
                || !shared_ref_types_match(source, destination.local)
            {
                continue;
            }
            if aliases.insert(destination.local) {
                pending.push_back(destination.local);
            }
        }
    }

    let place_derefs_local = |place: &trust_types::Place| {
        aliases.contains(&place.local)
            && matches!(place.projections.first(), Some(Projection::Deref))
    };
    // Same write-detection as `deref_write_exists`, but the single recognized write
    // place is excluded from the Assign arm (it is the setter's OWN sanctioned store).
    body.blocks.iter().flat_map(|b| &b.stmts).any(|s| match s {
        Statement::Assign { place, rvalue, .. } => {
            (place_derefs_local(place) && place != exclude)
                || matches!(rvalue,
                        Rvalue::Ref { mutable: true, place }
                            | Rvalue::AddressOf(true, place)
                            if place_derefs_local(place))
        }
        Statement::SetDiscriminant { place, .. }
        | Statement::Deinit { place }
        | Statement::Retag { place } => place_derefs_local(place),
        _ => false,
    }) || body.blocks.iter().any(|b| match &b.terminator {
        Terminator::Call { dest, atomic, .. } => {
            place_derefs_local(dest)
                || atomic.as_ref().is_some_and(|atomic| {
                    place_derefs_local(&atomic.place)
                        || atomic.dest.as_ref().is_some_and(place_derefs_local)
                })
        }
        Terminator::Drop { place, .. } => place_derefs_local(place),
        _ => false,
    })
}

/// Map a Trust MIR `Operand` (the exact struct `operand_to_formula` consumes) into
/// the MirSem `SemOperand` fragment, when it is a scalar operand the anchor models.
/// `None` (fail-closed) for any operand outside the modeled fragment — so a
/// faithfulness certificate is minted ONLY for operands MirSem actually pins.
///
/// `param_index` resolves a parameter place's local to its 0-based binding index
/// (the de-Bruijn position the reflection grounds it to); a place that is not a
/// parameter is outside the modeled fragment.
///
/// Trust: REASSIGNED-PARAM soundness — `body` is threaded so the SINGLE entry-
/// time resolution chokepoint fails closed on a parameter that is REASSIGNED
/// before use ([`param_reassigned_by_stmt`]). `Var(idx)` denotes the parameter's
/// ENTRY value; a reassigned parameter's real value differs, so resolving it here
/// would mint a certificate about the wrong value. This is the ONLY place a bare
/// parameter place becomes a `Var`, so guarding it closes the blind spot for
/// EVERY entry-time consumer at once (return leaf, call arguments, the
/// CallThenPureOp `other` operand, guarded arms, checked-field/cast sources) while
/// leaving every `param_index`-based MEMBERSHIP check (never routed through this
/// function) intact. The LOOP path uses `sem_operand_for_loop`, not this
/// function, so a reassigned loop counter is unaffected.
#[must_use]
pub fn sem_operand_of_mir(
    body: &trust_types::VerifiableBody,
    op: &trust_types::Operand,
    param_index: &dyn Fn(usize) -> Option<u64>,
) -> Option<SemOperand> {
    use trust_types::{ConstValue, Operand, Projection, Ty};
    match op {
        Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => {
            // Trust: REASSIGNED-PARAM soundness — an entry-time read of a
            // parameter reassigned before use is UNSOUND; fail closed.
            if param_reassigned_by_stmt(body, p.local) {
                return None;
            }
            if !matches!(
                body.locals.get(p.local).map(|local| &local.ty),
                Some(Ty::Int { .. }) | Some(Ty::Bool)
            ) {
                return None;
            }
            let idx = param_index(p.local)?;
            let var = SemOperand::Var(idx);
            // `Operand::Move` of a parameter place is the move-out form; model it as
            // `Move (Var idx)` to exercise the transparent-move adequacy case.
            Some(if matches!(op, Operand::Move(_)) { SemOperand::Move(Box::new(var)) } else { var })
        }
        // Trust: GAP-DEREF-SELF — a bare DEREF of an immutable reference-to-SCALAR
        // parameter (`Copy(*_1)`/`Move(*_1)`, `_1 : &{int}` — the `u8::is_ascii`-class
        // `_t = *self` shape). This is `sem_field_read_operand`'s SIMPLER SIBLING
        // (`[Deref, Field(fld)]` minus the `Field`): the referent IS the scalar, so
        // there is no field to project — modeled DIRECTLY as `Var(idx)`, reusing the
        // SAME env-slot convention `sem_field_read_operand`/`sem_discriminant_base_of_mir`
        // already establish for a Deref'd reference parameter (the grounding
        // environment is address-free: it carries the referent's own logical value at
        // the parameter's slot, so `Copy`ing a bare `{int}` parameter and `Copy`ing
        // through a `&{int}` parameter's Deref denote the SAME `Var(idx)` — the two
        // shapes never collide on the SAME local because MIR's own type system routes
        // a reference-typed local through a `Deref` projection and a scalar-typed
        // local through the empty-projection arm above, never both).
        //
        // Fail-closed for:
        //   * a `&mut self` receiver (a mutable alias could reassign the referent
        //     between the read and its use — no different in kind from
        //     `sem_field_read_operand`'s identical `&mut` decline);
        //   * a non-reference base, or a reference to a non-scalar (`Ty::Int` only —
        //     a struct/enum/slice referent is the field/discriminant/index leaves'
        //     territory, out of THIS fragment);
        //   * a parameter REASSIGNED before this read (the SAME entry-time-value
        //     soundness gate the base arm applies, applied here too);
        //   * a malformed/adversarial body that nonetheless WRITES THROUGH the
        //     reference (`deref_write_exists` — belt-and-suspenders: an immutable
        //     Rust reference can never be written through in SAFE code, but this
        //     defends the recognizer even if some upstream extraction bug ever
        //     produced such a body, mirroring `param_reassigned_by_stmt`'s
        //     mutable-alias/call-dest defense-in-depth checks).
        Operand::Copy(p) | Operand::Move(p)
            if matches!(p.projections.as_slice(), [Projection::Deref]) =>
        {
            if param_reassigned_by_stmt(body, p.local) {
                return None;
            }
            match body.locals.get(p.local).map(|l| &l.ty) {
                Some(Ty::Ref { mutable: false, inner }) if matches!(**inner, Ty::Int { .. }) => {}
                _ => return None, // `&mut self`, a non-reference base, or a non-scalar referent.
            }
            if deref_write_exists(body, p.local) {
                return None;
            }
            let idx = param_index(p.local)?;
            let var = SemOperand::Var(idx);
            Some(if matches!(op, Operand::Move(_)) { SemOperand::Move(Box::new(var)) } else { var })
        }
        Operand::Constant(ConstValue::Int(k)) => Some(SemOperand::Const(*k)),
        Operand::Constant(ConstValue::Uint(k, _)) => i128::try_from(*k).ok().map(SemOperand::Const),
        // Trust: discriminant-guard leaf — a `bool` LITERAL (`Either::is_left`-class
        // arm values: `_0 := true` / `_0 := false`). Modeled as the 0/1 `Int` encoding
        // ALREADY established in this file for a Bool-typed CALL result (see
        // `bool_as_int`'s doc: "a Rust `bool` is modeled by the opaque Int carrier,
        // 0/1 by convention" — the SAME idiom `sem_call_return_of_mir`'s
        // `local_is_int_or_bool` widening already relies on). A literal `bool` is the
        // SAME convention applied to a CONSTANT rather than an opaque call result.
        Operand::Constant(ConstValue::Bool(b)) => Some(SemOperand::Const(i128::from(*b))),
        _ => None,
    }
}

/// Recover a local's sole complete definition relative to an optional concrete
/// use site. Production recognizers pass the exact use site, which upgrades the
/// ordinary single-definition gate to entry reachability, block dominance, and
/// strict same-block statement order. Site-less callers retain the historical
/// whole-body behavior for standalone probes, but still require the complete
/// single-write/no-mutable-alias invariant.
pub(super) fn local_definition_for_optional_use(
    body: &trust_types::VerifiableBody,
    local: usize,
    use_site: Option<(trust_types::BlockId, Option<usize>)>,
) -> Option<(trust_types::BlockId, usize, &trust_types::Rvalue)> {
    if let Some((use_block, use_statement)) = use_site {
        return unique_local_definition_dominating(body, local, use_block, use_statement);
    }
    if !crate::prove::local_soundly_resolvable(body, local) {
        return None;
    }
    let mut definition = None;
    for block in &body.blocks {
        for (statement_index, statement) in block.stmts.iter().enumerate() {
            if let Some(rvalue) =
                crate::assignment_types::assigned_local_rvalue(body, statement, local)
            {
                if definition.is_some() {
                    return None;
                }
                definition = Some((block.id, statement_index, rvalue));
            }
        }
    }
    definition
}

/// Return the mathematical value of an integer constant cast only when the
/// machine cast preserves that value. The MirSem constant carrier is an
/// unbounded `i128`; declining value-changing casts avoids falsely identifying
/// a wrapped/truncated result with its source.
pub(super) fn value_preserving_integer_constant_cast(
    value: &trust_types::ConstValue,
    destination: &trust_types::Ty,
) -> Option<i128> {
    use trust_types::{ConstValue, Ty};

    let value = match value {
        // Widthless signed cast literals use the compatibility schema's i64
        // source type (the same rule as assignment_types::cast_operand_matches).
        ConstValue::Int(value) => i64::try_from(*value).ok().map(i128::from)?,
        ConstValue::Uint(value, width) => {
            if *width == 0 || *width > 128 || (*width < 128 && *value >= (1u128 << *width)) {
                return None;
            }
            i128::try_from(*value).ok()?
        }
        _ => return None,
    };
    let Ty::Int { width, signed } = destination else { return None };
    if *width == 0 || *width > 128 {
        return None;
    }
    if *signed {
        if *width == 128 {
            return Some(value);
        }
        let bound = 1i128 << (*width - 1);
        (-bound..bound).contains(&value).then_some(value)
    } else {
        let unsigned = u128::try_from(value).ok()?;
        (*width == 128 || unsigned < (1u128 << *width)).then_some(value)
    }
}

/// Map a GUARD comparison operand into the `SemOperand` fragment — a superset of
/// [`sem_operand_of_mir`] that ALSO resolves a SLICE-LENGTH temp: a `Copy/Move(local
/// k)` where `_k := UnaryOp(PtrMetadata, slice)` or `_k := Len(slice)` reflects to
/// `Len (Var slice_param)` (the `b` operand of an index guard `i < s.len()`). Falls
/// back to the scalar `sem_operand_of_mir` for everything else. `None` (fail-closed)
/// for a length over a non-parameter slice, or any other unmodeled operand.
pub(super) fn sem_guard_operand_of_mir(
    body: &trust_types::VerifiableBody,
    op: &trust_types::Operand,
    param_index: &dyn Fn(usize) -> Option<u64>,
    use_site: Option<(trust_types::BlockId, Option<usize>)>,
) -> Option<SemOperand> {
    use trust_types::{Operand, Place, Rvalue, Ty, UnOp};
    // Resolve `slice` operand (a `Copy/Move` of a parameter place) to its `Var`.
    let slice_var = |place: &Place| -> Option<SemOperand> {
        if !place.projections.is_empty() {
            return None;
        }
        if param_reassigned_by_stmt(body, place.local) {
            return None;
        }
        match body.locals.get(place.local).map(|local| &local.ty) {
            Some(Ty::Ref { mutable: false, inner })
                if matches!(inner.as_ref(), Ty::Slice { .. } | Ty::Array { .. }) => {}
            _ => return None,
        }
        if deref_write_exists(body, place.local) {
            return None;
        }
        Some(SemOperand::Var(param_index(place.local)?))
    };
    if let Operand::Copy(p) | Operand::Move(p) = op {
        if p.projections.is_empty() && param_index(p.local).is_none() {
            // Trust: block-order-first SOUNDNESS (recognizer well-formedness campaign,
            // 2026-07-05, closure pass) — `find_map` below returns the FIRST assignment to
            // the length temp `p.local` in block order; a MULTIPLY-assigned length temp would
            // resolve to a decoy earlier write instead of the real `PtrMetadata`/`Len` rvalue.
            // A length temp is a plain SSA-shaped leaf (not a loop counter), so
            // single-assignment is the right invariant here. Fail-closed.
            if !crate::prove::local_soundly_resolvable(body, p.local) {
                return None;
            }
            // A non-parameter temp: trace its single assignment, recognizing the
            // slice-length rvalues `PtrMetadata(slice)` / `Len(slice)`.
            let rv = if let Some((use_block, use_statement)) = use_site {
                Some(unique_local_definition_dominating(body, p.local, use_block, use_statement)?.2)
            } else {
                body.blocks
                    .iter()
                    .flat_map(|b| &b.stmts)
                    .find_map(|s| crate::assignment_types::assigned_local_rvalue(body, s, p.local))
            };
            match rv {
                Some(Rvalue::UnaryOp(UnOp::PtrMetadata, Operand::Copy(sp) | Operand::Move(sp))) => {
                    return Some(SemOperand::Len(Box::new(slice_var(sp)?)));
                }
                Some(Rvalue::Len(sp)) => {
                    return Some(SemOperand::Len(Box::new(slice_var(sp)?)));
                }
                _ => {}
            }
            // Trust: CAST-TEMP GUARD READ (2026-07-08) — the length-temp resolution
            // above declined (`rv` was neither `PtrMetadata`/`Len`, or fell through
            // the match); try a CAST-temp resolution. `local_soundly_resolvable` is
            // the SAME uniqueness gate (single static assignment, no call-dest
            // write, no mutable alias) `resolve_cast_source_operand` applies —
            // STRICTLY stronger than the bare `len_assign_count == 1` check above
            // (which already declined a multiply-assigned temp before reaching
            // here), so this is belt-and-suspenders, not a new soundness surface.
            if crate::prove::local_soundly_resolvable(body, p.local) {
                if let Some(cast_op) =
                    sem_guard_cast_temp_operand(body, p.local, param_index, use_site)
                {
                    return Some(cast_op);
                }
                // Trust: DEREF-MATERIALIZATION GUARD TEMP (WALL-JOINTEMP, 2026-07-16)
                // — the cast-temp resolution above declined; try a
                // deref-materialization resolution. The SINGLE-RANGE u8 ascii
                // predicates (`u8::is_ascii_{digit,octdigit,uppercase,lowercase,
                // graphic}`) materialize `*self` into a temp `_t := Use(Copy(*_p))`
                // ONCE and then compare `_t` against BOTH range bounds, whereas the
                // char equivalents read `*self` directly in each compare (and so were
                // already FULLY_FAITHFUL). `_t` holds the IDENTICAL value as `*_p`
                // (a pure SSA copy), so it resolves to the SAME `Var(param)` the
                // direct-deref GAP-DEREF-SELF read produces — no new carrier, the
                // branch refinement closes reflexively at the same term. This is the
                // guard-OPERAND-side SSA normalization that (together with the already
                // admitted join-via-temp `_0 := Use(_t)` return move) closes the
                // WALL-JOINTEMP single-range-predicate gap.
                if let Some(deref_op) =
                    sem_deref_materialization_temp_operand(body, p.local, param_index, use_site)
                {
                    return Some(deref_op);
                }
            }
        }
    }
    sem_operand_of_mir(body, op, param_index)
}

/// Trust: CAST-TEMP GUARD READ (2026-07-08) — resolve a single-assigned,
/// call-dest-free, non-mutably-aliased non-parameter local `target`
/// (uniqueness gated by the CALLER via
/// [`crate::prove::local_soundly_resolvable`]) whose SOLE static assignment is
/// an integer `Rvalue::Cast(src, dest_ty)`. `src`'s DECLARED type and
/// `dest_ty` must BOTH be `Ty::Int` — a `char` operand is ALREADY
/// `Ty::Int{width:32,signed:false}` in this IR (see the fixture dumps under
/// `fixtures/census-rung2-2026-07-07/ascii_utils`), so this ONE arm covers
/// int↔int AND char↔int uniformly; a float/pointer/enum cast declines
/// fail-closed.
///
/// Two denotations, composed from EXISTING machinery (see
/// [`SemOperand::Cast`]'s doc for why the second tier is honest, not exact):
///   * VALUE-PRESERVING widening (same-signedness equal/widening, or strict
///     unsigned-to-signed widening): delegates to
///     [`resolve_widening_cast_rvalue`]'s exact-identity reasoning (unwrapped
///     from its `SemRvalue::Use` wrapper to the bare `SemOperand`).
///   * TRUNCATING or any remaining signedness-changing reinterpret: the opaque
///     [`SemOperand::Cast`] carrier — honest (asserts no numeric relationship
///     between the cast value and its source), never a false claim.
///
/// `None` (fail-closed) when the assignment is not a `Cast`, either type is
/// non-`Int`, the cast source is projected, or the source itself does not
/// resolve (through [`resolve_cast_source_operand`]'s existing at-most-one-
/// level temp inlining).
pub(super) fn sem_guard_cast_temp_operand(
    body: &trust_types::VerifiableBody,
    target: usize,
    param_index: &dyn Fn(usize) -> Option<u64>,
    use_site: Option<(trust_types::BlockId, Option<usize>)>,
) -> Option<SemOperand> {
    use trust_types::{Operand, Rvalue, Ty};
    let (definition_block, definition_statement, rvalue) =
        local_definition_for_optional_use(body, target, use_site)?;
    let source_use_site = Some((definition_block, Some(definition_statement)));
    let Rvalue::Cast(src, dest_ty) = rvalue else { return None };
    let Ty::Int { width: dw, signed: ds } = dest_ty else { return None };
    // WIDENING / equal-width same-signedness — the EXACT identity path.
    if let Some(SemRvalue::Use(op)) =
        resolve_widening_cast_rvalue(body, src, dest_ty, param_index, source_use_site)
    {
        return Some(op);
    }
    // TRUNCATING / reinterpret — the source's DECLARED type must still be
    // `Ty::Int` (an int↔int/char↔int cast only; a float/pointer source
    // declines fail-closed).
    let (Operand::Copy(p) | Operand::Move(p)) = src else { return None };
    if !p.projections.is_empty() {
        return None;
    }
    if !matches!(body.locals.get(p.local).map(|l| &l.ty), Some(Ty::Int { .. })) {
        return None;
    }
    let resolved_src = resolve_cast_source_operand(body, src, param_index, source_use_site)?;
    Some(SemOperand::Cast(Box::new(resolved_src), u64::from(*dw), *ds))
}

/// Trust: DEREF-MATERIALIZATION GUARD TEMP (WALL-JOINTEMP, 2026-07-16) — resolve
/// a non-parameter temp `target` (uniqueness gated by the CALLER via
/// [`crate::prove::local_soundly_resolvable`]: single static assignment, not a
/// call dest, not mutably aliased) whose SOLE static assignment is a bare
/// deref-materialization `target := Use(Copy(*_p) | Move(*_p))` — a copy of the
/// referent of an immutable-reference parameter `_p : &{int}`.
///
/// This is the guard-operand SSA normalization the single-range u8 ascii
/// predicates need. `u8::is_ascii_digit`'s body reads `*self` ONCE into a temp
/// (`_3 := Use(Copy(*_1))`) and then compares `_3` against BOTH range bounds
/// (`48 <= _3 && _3 <= 57`); the corresponding `char::is_ascii_digit` reads
/// `*self` DIRECTLY in each compare and was already FULLY_FAITHFUL. The temp
/// holds the IDENTICAL value as `*_p` (a pure value-identity copy, unchanged),
/// so it must denote the SAME thing.
///
/// SOUNDNESS: we do NOT invent a denotation — we DELEGATE the resolved inner
/// operand `Copy(*_p)`/`Move(*_p)` to [`sem_operand_of_mir`], whose GAP-DEREF-SELF
/// arm is the SINGLE authority for a deref-of-`&{int}`-parameter read. That arm
/// applies every gate uniformly: `_p` must be a parameter (`param_index(_p)`),
/// its type must be `Ty::Ref { mutable: false, inner: Ty::Int }` (a `&mut`, a
/// non-reference, or a non-scalar referent declines), `_p` must not be reassigned
/// (`param_reassigned_by_stmt`), and nothing may write THROUGH it
/// (`deref_write_exists`). The result is the EXACT `Var(param)` (or
/// `Move(Var(param))`) the direct-deref read produces — the modeled Bool/Int
/// carrier is unchanged, so the kernel adequacy witness is byte-identical to the
/// char predicate's, never a shape-only promotion.
///
/// FAIL-CLOSED (`None`) for: an assignment that is not a `Use` (e.g. a `BinaryOp`,
/// a `Cast`, a call result); a `Use` of a place that is NOT exactly `[Deref]`-
/// projected (a copy of a plain local, a field/index projection, or a deeper
/// projection); or a deref whose base is not an immutable-`&{int}` parameter (all
/// declined by the delegated GAP-DEREF-SELF arm). A copy of a DIFFERENT local, of
/// an UNMODELED value, or of a value produced AFTER a mutation therefore never
/// resolves through this path.
pub(super) fn sem_deref_materialization_temp_operand(
    body: &trust_types::VerifiableBody,
    target: usize,
    param_index: &dyn Fn(usize) -> Option<u64>,
    use_site: Option<(trust_types::BlockId, Option<usize>)>,
) -> Option<SemOperand> {
    use trust_types::{Operand, Projection, Rvalue};
    // `target`'s SOLE static assignment (single-assignment already guaranteed by
    // the caller's `local_soundly_resolvable` gate).
    let (_, _, rvalue) = local_definition_for_optional_use(body, target, use_site)?;
    // It must be a bare `Use` of a `[Deref]`-projected place — a value-identity
    // move of a dereferenced operand, nothing else.
    let Rvalue::Use(inner @ (Operand::Copy(p) | Operand::Move(p))) = rvalue else { return None };
    if !matches!(p.projections.as_slice(), [Projection::Deref]) {
        return None;
    }
    // Delegate to `sem_operand_of_mir`'s GAP-DEREF-SELF arm — the single authority
    // for a deref-of-`&{int}`-parameter read (it applies the `&{immutable int}` /
    // not-reassigned / no-deref-write gates and yields the SAME `Var(param)` the
    // direct-deref read produces). A deref of a non-parameter / `&mut` / non-scalar
    // base declines there, fail-closed.
    sem_operand_of_mir(body, inner, param_index)
}

/// Trust: ADT-return leaf — resolve a GUARD comparison operand for
/// [`sem_adt_return_shape_of`]'s OWN `switch_leaf`: a superset of
/// [`sem_guard_operand_of_mir`] that ALSO resolves a same-block CONSTANT-FOLDABLE
/// cast temp `_k := Cast(Constant(c), ty)` — the `$dst::MAX as $src`/`$dst::MIN as
/// $src` shape `cast` 0.3.0's `from_unsigned!`/`from_signed!` macros compile the
/// guard's bound to (rustc does not constant-fold this cast in the dumped MIR; e.g.
/// `u8::MAX as u16` lowers to `_3 := Cast(Uint(255,8), u16)`). Gated by
/// [`crate::prove::local_soundly_resolvable`] (single-assignment, not a call dest,
/// not mutably-aliased), so a multiply-assigned/aliased guard-bound temp fails
/// closed rather than resolving to a decoy value. The cast is returned as the
/// source constant ONLY when that mathematical value is representable unchanged
/// in the destination type; truncating/wrapping/signedness-changing constants
/// decline rather than being misidentified with their source. Falls back to
/// [`sem_guard_operand_of_mir`] for everything else — a SCOPED ADDITION used ONLY by
/// the ADT-return recognizer, never by the pre-existing scalar-return guard path.
pub(super) fn sem_adt_guard_operand_of_mir(
    body: &trust_types::VerifiableBody,
    op: &trust_types::Operand,
    param_index: &dyn Fn(usize) -> Option<u64>,
    use_site: Option<(trust_types::BlockId, Option<usize>)>,
) -> Option<SemOperand> {
    use trust_types::{ConstValue, Operand, Rvalue};
    if let Some(direct) = sem_guard_operand_of_mir(body, op, param_index, use_site) {
        return Some(direct);
    }
    let (Operand::Copy(p) | Operand::Move(p)) = op else { return None };
    if !p.projections.is_empty() || param_index(p.local).is_some() {
        return None;
    }
    if !crate::prove::local_soundly_resolvable(body, p.local) {
        return None;
    }
    let (_, _, rvalue) = local_definition_for_optional_use(body, p.local, use_site)?;
    match rvalue {
        Rvalue::Cast(
            Operand::Constant(value @ (ConstValue::Int(_) | ConstValue::Uint(_, _))),
            dest,
        ) => value_preserving_integer_constant_cast(value, dest).map(SemOperand::Const),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Trust: field-read leaf — the "field-read of `&self` + integer width-cast,
// scalar return" shape (`arrayvec::ArrayVec::len`'s body: `_2 = (*_1).0; _0 =
// _2 as u64; return`). Two new fail-closed recognizers:
//   * `sem_field_read_operand` — a struct-FIELD READ `(*p).fld` on an
//     IMMUTABLE reference PARAMETER, modeled via `SemOperand::Field` (which
//     desugars to the EXISTING `Index`/`idx_elem` opaque carrier — see the
//     variant doc).
//   * `resolve_widening_cast_rvalue` — a SOUND WIDENING integer `Cast`,
//     modeled as the IDENTITY on the unbounded `Int` carrier (zero-/sign-
//     extension changes representation, not value): the cast's own rvalue is
//     modeled as `Use` of its (possibly one-level-inlined) source operand.
// ---------------------------------------------------------------------------
/// Trust: field-read leaf — recognize a struct-FIELD READ operand: `Copy`/
/// `Move` of a place `[Deref, Field(fld)]` on an IMMUTABLE reference PARAMETER
/// (`&self`-shaped: `Ty::Ref { mutable: false, .. }`). Modeled as
/// `SemOperand::Field(Var(param_idx), fld)`. `None` (fail-closed) for a field
/// read through a MUTABLE reference (`&mut self`), a non-parameter base, a
/// deeper/different projection shape (nested fields, an index-then-field, a
/// bare `Field` with no `Deref`), or any other unmodeled operand — so a
/// negative-control shape never gets a false certificate.
pub(super) fn sem_field_read_operand(
    body: &trust_types::VerifiableBody,
    op: &trust_types::Operand,
    param_index: &dyn Fn(usize) -> Option<u64>,
) -> Option<SemOperand> {
    use trust_types::{ClosureCallKind, Operand, Projection, Ty};
    let (Operand::Copy(p) | Operand::Move(p)) = op else { return None };
    match p.projections.as_slice() {
        [Projection::Deref, Projection::Field(fld)] => {
            let idx = param_index(p.local)?;
            match body.locals.get(p.local).map(|l| &l.ty) {
                Some(Ty::Ref { mutable: false, inner }) => match inner.as_ref() {
                    Ty::Adt { fields, .. }
                        if fields
                            .get(*fld)
                            .is_some_and(|(_, ty)| matches!(ty, Ty::Int { .. } | Ty::Bool)) => {}
                    _ => return None,
                },
                _ => return None, // `&mut self` (or a non-reference base) — declines.
            }
            if param_reassigned_by_stmt(body, p.local) || deref_write_exists(body, p.local) {
                return None;
            }
            Some(SemOperand::Field(Box::new(SemOperand::Var(idx)), u64::try_from(*fld).ok()?))
        }
        // Trust: M6 rung 6 — BY-VALUE param field read (`self.0` where
        // `self: ExprMeta` is a BY-VALUE ADT parameter — the `ExprMeta::
        // loose_bvar_range`-class leaf shape; the `[Deref, Field]` arm above is
        // the `&self`-shaped sibling). ENTRY-TIME-VALUE soundness gates,
        // stricter than the sibling arm (a by-value param's field can be
        // written directly, which the `&self` immutable-ref arm structurally
        // cannot):
        //   * the param itself must not be REASSIGNED (`param_reassigned_by_stmt`
        //     — the same entry-time gate `sem_operand_of_mir` applies);
        //   * NO statement may write ANY projection of the param (a direct
        //     field write `self.0 = ..` would make the entry-time read stale);
        //   * the shared `local_soundly_resolvable` gate declines a call-dest /
        //     mutable-alias write reaching the param.
        // Fail-closed on every clause.
        [Projection::Field(fld)] => {
            let idx = param_index(p.local)?;
            match body.locals.get(p.local).map(|l| &l.ty) {
                Some(Ty::Adt { fields, .. })
                    if fields
                        .get(*fld)
                        .is_some_and(|(_, ty)| matches!(ty, Ty::Int { .. } | Ty::Bool)) => {}
                // Trust: W6 increment-3 (CAPTURING closures, 2026-07-18) — a
                // single-level upvar field read `_1.i` on the BY-VALUE Closure-typed
                // ENV parameter of a closure body (`map_cap::{closure#0}`'s sole shape
                // blocker: `_3 = copy _1.0`). The env is the closure's first parameter
                // (`param_index` is `Some` above and only the env has `Ty::Closure`);
                // upvar `i` is modeled as the SAME MODEL-ONLY `SemOperand::Field(Var
                // env_idx, i)` opaque total selector the `&self`/by-value-ADT arms use
                // (the captured value is a total function of the env value — no new
                // axiom, no new carrier). CAPTURE-SPECIFIC gates, fail-closed:
                //   * `i < upvars.len()` — an out-of-range upvar index declines (a
                //     forged `.k` past the last capture never resolves to a live field);
                //   * IMMUTABLE call kinds ONLY (`Fn`/`FnOnce`); `FnMut` DECLINES — a
                //     mutable-env closure can rebind its captures BETWEEN calls, so the
                //     entry-time upvar value is not a stable denotation (the same reason
                //     the `&self` arm declines `&mut self`). A missing call signature
                //     (`call == None`) also declines (kind unverifiable).
                // The single-level `[Field]` match already rejects `_1.0.1` (a nested
                // upvar-of-upvar projection), and the shared entry-time-value gates
                // below (`param_reassigned_by_stmt`, projected-write, call-dest-write,
                // mutable-alias) apply UNIFORMLY — a reassigned/mutated env declines.
                Some(Ty::Closure { upvars, call, .. }) => {
                    if *fld >= upvars.len() {
                        return None; // out-of-range upvar index.
                    }
                    match call.as_deref() {
                        Some(sig)
                            if matches!(
                                sig.kind,
                                ClosureCallKind::Fn | ClosureCallKind::FnOnce
                            ) => {}
                        _ => return None, // FnMut (mutable env) or unknown kind — declines.
                    }
                }
                _ => return None, // not a by-value ADT / closure-env param — outside this arm.
            }
            if param_reassigned_by_stmt(body, p.local) {
                return None;
            }
            // Any PROJECTED write to the param (a direct field write) — fail closed.
            let field_written = body.blocks.iter().flat_map(|b| &b.stmts).any(|s| {
                matches!(s, trust_types::Statement::Assign { place, .. }
                    if place.local == p.local && !place.projections.is_empty())
            });
            if field_written {
                return None;
            }
            // A call-dest write or a mutable alias of the param — fail closed
            // (the same two write-set blind spots `local_soundly_resolvable`
            // guards for temps; a param has ZERO statement writes, so that
            // helper's `write_count == 1` gate does not fit here — these are
            // its remaining two clauses, applied directly).
            let call_dest_written = body.blocks.iter().any(|b| {
                matches!(&b.terminator,
                    trust_types::Terminator::Call { dest, .. } if dest.local == p.local)
            });
            if call_dest_written {
                return None;
            }
            let mutably_aliased = body.blocks.iter().flat_map(|b| &b.stmts).any(|s| {
                matches!(s,
                    trust_types::Statement::Assign {
                        rvalue: trust_types::Rvalue::Ref { mutable: true, place }, ..
                    } | trust_types::Statement::Assign {
                        rvalue: trust_types::Rvalue::AddressOf(true, place), ..
                    }
                    if place.local == p.local)
            });
            if mutably_aliased {
                return None;
            }
            Some(SemOperand::Field(Box::new(SemOperand::Var(idx)), u64::try_from(*fld).ok()?))
        }
        _ => None,
    }
}

/// Trust: discriminant-guard leaf — resolve the `place` inside an
/// `Rvalue::Discriminant(place)` to the `SemOperand` BASE naming the enum value
/// whose tag is read: a bare parameter place (`self: Either<L, R>` BY VALUE) or a
/// `[Deref]` projection on an IMMUTABLE reference parameter (`self: &Either<L,
/// R>` — the `Either::is_left`-class shape). `None` (fail-closed) for:
///   * a `&mut self` receiver (a mutable alias could reassign the referent
///     BETWEEN the discriminant read and the switch — no different in kind from
///     `sem_field_read_operand`'s identical `&mut` decline, and this shape has no
///     mechanism to verify no intervening write occurred);
///   * a parameter REASSIGNED before this read (`param_reassigned_by_stmt` — the
///     SAME entry-time-value soundness gate `sem_operand_of_mir` applies to every
///     other parameter read, applied here too so a `_1 = other_ref; discriminant
///     (*_1)` body cannot certify the WRONG (post-reassignment) value);
///   * a non-parameter base, or any deeper/different projection (nested derefs,
///     a field-then-discriminant, …) — outside the modeled fragment.
///   * a base whose declared type is not an enum with either first-class
///     variant metadata or the exact validated historical flattened layout;
///     the opaque tag carrier still denotes an actual MIR discriminant read,
///     never an invented tag for a scalar/struct;
///   * any write through a direct reference base, even if malformed input marks
///     that reference immutable.
///
/// Trust: DISCRIMINANT-AS-VALUE (M5 slice B, 2026-07-08) — a SECOND base shape,
/// tried when `place.local` is NOT itself a parameter: a same-body TEMP whose
/// SOLE assignment is an IMMUTABLE address-of a BY-VALUE parameter (`_2 := &_1
/// (self: Ordering); _0 := Discriminant((*_2))` — the `Ordering::as_raw` shape,
/// the sibling of the `Either::is_left`-class direct-`&self`-receiver shape
/// above: `as_raw` takes `self` BY VALUE and re-borrows it INLINE to call the
/// `discriminant_value` intrinsic, rather than receiving `&self` directly).
/// `*(&_1)` is the identity, so the discriminant read is exactly `_1`'s own tag —
/// resolved to `Var(idx)` at the REFERENT's parameter index, reusing the deref-
/// self identity reasoning [`sem_operand_of_mir`]'s GAP-DEREF-SELF arm
/// established (`b42adf3079`), generalized from "deref a reference PARAMETER" to
/// "deref a locally-taken reference TO a parameter". Gated FAIL-CLOSED,
/// belt-and-suspenders like every sibling temp-chase in this file:
///   * `_2` (the reference temp) must be [`crate::prove::local_soundly_resolvable`]
///     — exactly ONE static assignment, never a `Call` dest, never itself
///     mutably aliased — so a multiply-assigned or aliased `_2` cannot resolve to
///     a decoy write;
///   * the address-of must be IMMUTABLE (`Rvalue::Ref { mutable: false, .. }`) —
///     a `&mut` re-borrow could be written through, same reasoning as the direct
///     `&mut self` decline above;
///   * the referent place must be a BARE (unprojected) local;
///   * the referent parameter must not be [`param_reassigned_by_stmt`] (the same
///     entry-time-value gate, applied to the REAL underlying parameter);
///   * [`deref_write_exists`] over `_2` must be empty — no statement or call-dest
///     write reaches through `_2` between the borrow and the read (an immutable
///     Rust reference can never be written through in SAFE code, but this
///     defends against a malformed/adversarial body, mirroring
///     `sem_operand_of_mir`'s identical defense).
/// A projected referent, a mutable re-borrow, a multiply-assigned/aliased `_2`,
/// a write-through, or a reassigned referent all decline — never a false
/// certificate.
pub(super) fn sem_discriminant_base_of_mir(
    body: &trust_types::VerifiableBody,
    place: &trust_types::Place,
    param_index: &dyn Fn(usize) -> Option<u64>,
    use_site: Option<(trust_types::BlockId, Option<usize>)>,
) -> Option<SemOperand> {
    use trust_types::{Projection, Rvalue, Ty};
    if param_reassigned_by_stmt(body, place.local) {
        return None;
    }
    if let Some(idx) = param_index(place.local) {
        return match place.projections.as_slice() {
            [] if crate::assignment_types::modeled_enum_variant_count(
                &body.locals.get(place.local)?.ty,
            )
            .is_some() =>
            {
                Some(SemOperand::Var(idx))
            }
            [Projection::Deref] => match body.locals.get(place.local).map(|l| &l.ty) {
                Some(Ty::Ref { mutable: false, inner })
                    if crate::assignment_types::modeled_enum_variant_count(inner).is_some()
                        && !deref_write_exists(body, place.local) =>
                {
                    Some(SemOperand::Var(idx))
                }
                _ => None, // `&mut self` (or a non-reference base) — declines.
            },
            _ => None,
        };
    }
    // Trust: DISCRIMINANT-AS-VALUE — `place.local` is a non-parameter TEMP. Only
    // the `[Deref]`-projected shape (`*_2`) is in scope here (a bare non-parameter
    // local, with no projection, names a temp `Ordering` value directly — never
    // produced by a `Discriminant` guard/return in real MIR, and outside this
    // fragment either way).
    if place.projections.as_slice() != [Projection::Deref] {
        return None;
    }
    if !crate::prove::local_soundly_resolvable(body, place.local) {
        return None; // `_2` multiply-assigned, call-dest-written, or mutably aliased.
    }
    if deref_write_exists(body, place.local) {
        return None; // a write reaches through `_2` — the deref-self defense.
    }
    match body.locals.get(place.local).map(|l| &l.ty) {
        Some(Ty::Ref { mutable: false, inner })
            if crate::assignment_types::modeled_enum_variant_count(inner).is_some() => {}
        _ => return None, // the reference temp must itself point to an enum.
    }
    let definition = if let Some((use_block, use_statement)) = use_site {
        unique_local_definition_dominating(body, place.local, use_block, use_statement)?.2
    } else {
        body.blocks
            .iter()
            .flat_map(|b| &b.stmts)
            .find_map(|s| crate::assignment_types::assigned_local_rvalue(body, s, place.local))?
    };
    let Rvalue::Ref { mutable: false, place: referent } = definition else { return None };
    if !referent.projections.is_empty() {
        return None; // `&(self.field)` or deeper — outside the modeled fragment.
    }
    if param_reassigned_by_stmt(body, referent.local) {
        return None;
    }
    if crate::assignment_types::modeled_enum_variant_count(&body.locals.get(referent.local)?.ty)
        .is_none()
    {
        return None; // a scalar/struct referent has no modeled discriminant.
    }
    let ridx = param_index(referent.local)?;
    Some(SemOperand::Var(ridx))
}

/// Trust: field-read leaf — trace a CAST's source operand to a `SemOperand`,
/// resolving through AT MOST one level of temp indirection: a bare parameter/
/// constant operand resolves directly (`sem_operand_of_mir`) or as a direct
/// field read (`sem_field_read_operand`); a NON-parameter temp `_t` resolves
/// through its SOLE static assignment `_t := Use(op')`, where `op'` is itself
/// one of those two modeled shapes. This mirrors `resolve_checked_field_rvalue`'s
/// INLINING discipline: the intermediate temp's value is substituted DIRECTLY
/// (never left as a further `Var` cross-reference to a non-parameter local), so
/// the composed value stays CLOSED over parameters/constants/field-reads —
/// required by the existing single-assignment `exec`/Lemma-1C machinery, which
/// reasons about the LAST assignment to the RETURNED index only (untouched).
/// When `use_site` is present, every chased temp definition must dominate that
/// use and precede it strictly in the same block. The definition site becomes
/// the use site for the inlined rvalue's own operands.
/// `None` (fail-closed) for a deeper chain, a multiply-assigned temp, or an
/// operand outside this fragment.
pub(super) fn resolve_cast_source_operand(
    body: &trust_types::VerifiableBody,
    op: &trust_types::Operand,
    param_index: &dyn Fn(usize) -> Option<u64>,
    use_site: Option<(trust_types::BlockId, Option<usize>)>,
) -> Option<SemOperand> {
    use trust_types::{Operand, Rvalue};
    if let Some(direct) = sem_operand_of_mir(body, op, param_index) {
        return Some(direct);
    }
    if let Some(field) = sem_field_read_operand(body, op, param_index) {
        return Some(field);
    }
    // A NON-parameter temp: trace its SOLE static assignment one level deep.
    let (Operand::Copy(p) | Operand::Move(p)) = op else { return None };
    if !p.projections.is_empty() || param_index(p.local).is_some() {
        return None;
    }
    // Trust: Call-dest/mutable-alias SOUNDNESS (recognizer well-formedness campaign,
    // 2026-07-05, closure pass) — the loop below already declines a MULTIPLY-assigned temp
    // (`found.is_some()`), but that scan only sees `Statement::Assign`; it is BLIND to a
    // `Terminator::Call` dest write or a `&mut`/`&raw mut` alias write to the SAME temp
    // elsewhere in the body, either of which makes the one `Statement::Assign` found here NOT
    // the temp's complete definition (mirrors `prove::ir_resolve_cast_source_operand`'s twin
    // fix). Fail-closed.
    if !crate::prove::local_soundly_resolvable(body, p.local) {
        return None;
    }
    let (_, _, definition) = local_definition_for_optional_use(body, p.local, use_site)?;
    match definition {
        Rvalue::Use(inner) => sem_operand_of_mir(body, inner, param_index)
            .or_else(|| sem_field_read_operand(body, inner, param_index)),
        _ => None,
    }
}

/// Trust: field-read leaf — recognize a SOUND WIDENING integer CAST `Cast(op,
/// dest_ty)` as the IDENTITY on the unbounded `Int` carrier: a zero-/sign-
/// extending cast changes REPRESENTATION, not VALUE, so it contributes no
/// arithmetic content beyond its (resolved) source operand — modeled as
/// `SemRvalue::Use(<resolved source>)`.
///
/// Admitted ONLY when the source's DECLARED type (`op`'s place local's type in
/// `body.locals`) and `dest_ty` are both `Ty::Int` and either (a) they have the
/// SAME signedness with `dest_width >= src_width`, or (b) the source is unsigned,
/// the destination signed, and `dest_width > src_width`. Case (b) is still
/// value-preserving because every source value fits below the destination sign
/// bit. `None` (fail-closed) for anything else: a non-integer cast, truncation,
/// same-width/other-direction signedness change, projected/constant source, or
/// an unresolvable source.
pub(super) fn resolve_widening_cast_rvalue(
    body: &trust_types::VerifiableBody,
    op: &trust_types::Operand,
    dest_ty: &trust_types::Ty,
    param_index: &dyn Fn(usize) -> Option<u64>,
    use_site: Option<(trust_types::BlockId, Option<usize>)>,
) -> Option<SemRvalue> {
    use trust_types::{Operand, Ty};
    let (Operand::Copy(p) | Operand::Move(p)) = op else { return None };
    if !p.projections.is_empty() {
        return None; // a projected cast source is a different (unmodeled) shape.
    }
    let src_ty = &body.locals.get(p.local)?.ty;
    let (Ty::Int { width: sw, signed: ss }, Ty::Int { width: dw, signed: ds }) = (src_ty, dest_ty)
    else {
        // Trust: W11-FLOAT-EXACT-WIDENING (BLOCKED, 2026-07-16) — the MirSem-lane
        // twin of `prove::ir_resolve_widening_cast_rvalue`'s matching gate. A float
        // DESTINATION (`int -> f32/f64`, `f32 -> f64`) or float SOURCE declines
        // HERE, fail-closed. Eleven destination rows are exact for genuinely typed
        // source values, but the vendored carrier loses the source width and both
        // FPExt/FPTrunc are identity; even the f32-source invariant is unstatable.
        // See the TrustIR twin for the required structured IEEE lane: width-tagged
        // values, rounding in int->float and FPTrunc, exact FPExt, and explicit
        // NaN/infinity/signed-zero/subnormal behavior. Until then every float cast
        // fails closed; the tests are representative recognizer probes, not a
        // corpus-wide or kernel-forgery claim.
        return None;
    };
    // Trust: GAP-CROSS-SIGN-WIDEN (2026-07-16) — a SIGN-CROSSING WIDENING cast
    // `u_w -> i_W` with `W > w` is VALUE-PRESERVING, hence the IDENTITY on the
    // unbounded `Int` carrier. An unsigned source value lies in `[0, 2^w)`, and a
    // STRICT widening `W > w` gives `2^w <= 2^(W-1)`, so every source value is
    // `< 2^(W-1) = i_W::MAX + 1` and embeds EXACTLY into `i_W` with its sign bit
    // clear: the zero-extended bit pattern reinterpreted as signed equals the
    // original value (`u8::MAX = 255 < 32767 = i16::MAX`, etc.). Kernel-anchored
    // against the vendored trust-ir `semCast` semantics by
    // `bridge_cast_zext_signcross_widening_identity` (trustir_bridge.rs):
    // `toSigned (truncateUnsigned v W) W = v` for `0 <= v < 2^(W-1)` — the ZExt
    // raw-encode is the identity (`v < 2^W`) and the signed reinterpret is the
    // identity (`v < 2^(W-1)`), so the composed cast is the identity.
    //
    // FAIL-CLOSED gate — STRICT widening ONLY (`dw > sw`):
    //   * a SAME-WIDTH sign cross (`u_w -> i_w`, `dw == sw`) is a value-CHANGING
    //     reinterpret (`u8 255 -> i8 == -1`) — NOT admitted (falls to the
    //     `ss != ds` decline below);
    //   * a NARROWING sign cross (`u_W -> i_w`, `dw < sw`) truncates — NOT admitted;
    //   * an `i -> u` crossing (`!ds`) is a NON-value-preserving reinterpret on
    //     negatives (`i8 -1 -> u16 == 65535`) — NOT admitted (guarded by `*ds`);
    //   * same-signedness casts (`ss == ds`) never enter here — this clause fires
    //     only when `ss != ds` (specifically `!ss && ds`), leaving the existing
    //     same-signedness widening/no-op/shift-narrowing paths byte-for-byte intact.
    if !*ss && *ds && dw > sw {
        let resolved = resolve_cast_source_operand(body, op, param_index, use_site)?;
        return Some(SemRvalue::Use(resolved));
    }
    if ss != ds {
        return None; // signedness reinterpret — NOT identity.
    }
    if dw < sw {
        // Trust: M6 rung 6 — the SHIFT-NARROWED EXACT cast (a TYPE-WIDTH fact,
        // not a general narrowing admission): `Cast(Shr(x: uW, k), uV)` with
        // `W − k ≤ V` is VALUE-PRESERVING — `x: uW ⇒ x >> k < 2^(W−k) ≤ 2^V`,
        // so the "truncating" cast provably loses no value and is the IDENTITY
        // on the unbounded `Int` carrier (the `ExprMeta::loose_bvar_range`
        // leaf shape: `(self.0 >> 44) as u32`, where `64 − 44 = 20 ≤ 32`).
        // Gates, all fail-closed:
        //   * BOTH types unsigned (`ss == ds` above + `!ss` here — the width
        //     argument is a nonnegative value-range argument, unsigned only);
        //   * the cast source is a SINGLE-write temp (`local_soundly_resolvable`)
        //     whose sole assignment is a `Shr` by a LITERAL `Uint` amount `k`
        //     with `k ≤ W` and `W − k ≤ V`;
        //   * the `Shr` rvalue itself must resolve through the NORMAL
        //     `sem_rvalue_of_mir` dispatch — re-applying the UNSIGNED-ONLY
        //     `Shr` admission gate to the shifted operand.
        // Any other narrowing cast stays declined exactly as before.
        if *ss {
            return None; // signed narrowing — no width fact, fail closed.
        }
        if p.projections.is_empty()
            && param_index(p.local).is_none()
            && crate::prove::local_soundly_resolvable(body, p.local)
        {
            let (definition_block, definition_statement, shr_rv) =
                local_definition_for_optional_use(body, p.local, use_site)?;
            if let trust_types::Rvalue::BinaryOp(trust_types::BinOp::Shr, _, amount) = shr_rv {
                if let trust_types::Operand::Constant(trust_types::ConstValue::Uint(k, _)) = amount
                {
                    let (w, v, k) = (u128::from(*sw), u128::from(*dw), *k as u128);
                    if k <= w && w - k <= v {
                        // The Shr rvalue resolves through the normal dispatch
                        // (unsigned gate re-applied there) — the narrowing cast
                        // is the identity on its value.
                        return sem_rvalue_of_mir_at_depth(
                            body,
                            shr_rv,
                            param_index,
                            0,
                            Some((definition_block, Some(definition_statement))),
                        );
                    }
                }
            }
        }
        return None; // any other truncation — NOT identity, fail closed.
    }
    let resolved = resolve_cast_source_operand(body, op, param_index, use_site)?;
    Some(SemRvalue::Use(resolved))
}

/// Trust: W-CMP-DISCR (2026-07-16) — interpret a RAW discriminant value `d` (as
/// the extractor stored it, e.g. `255` for the `#[repr(i8)]` tag `-1`) as a
/// SIGNED `w`-bit two's-complement integer. `255` at `w = 8` is `-1`; `0` is
/// `0`; `1` is `1`. Returns `None` for an out-of-range width (`w == 0` or
/// `w > 127`). This is the sign-recovery the `Discriminant` read + signed cast
/// performs on the `Ordering` tag.
pub(super) fn signed_at_width(d: i128, w: u32) -> Option<i128> {
    if w == 0 || w > 127 {
        return None;
    }
    let modulus = 1i128 << w; // 2^w
    let half = 1i128 << (w - 1); // 2^(w-1)
    let m = d.rem_euclid(modulus); // canonical residue in [0, 2^w)
    Some(if m >= half { m - modulus } else { m })
}

/// Trust: W-CMP-DISCR — verify that `ty` is the vendored `cmp::Ordering` enum
/// with EXACTLY the canonical three-way SIGN encoding: variants
/// `Less`/`Equal`/`Greater` whose discriminants, interpreted as SIGNED `w`-bit
/// integers, are `-1`/`0`/`1` respectively. This is the fail-closed structural
/// check against the vendored Ordering/Cmp semantics that ties the synthesized
/// `(a > 0) - (a < 0)` sign witness to the ACTUAL tag-read chain: a DIFFERENT
/// enum (name not `…Ordering`), a wrong variant set, a wrong variant count, or a
/// wrong discriminant→value mapping all DECLINE (`false`). No shape-only
/// promotion — a forged 3-variant enum whose tags are NOT the -1/0/1 sign
/// encoding is rejected here.
pub(super) fn ordering_is_three_way_sign_encoding(ty: &trust_types::Ty, disc_width: u32) -> bool {
    use trust_types::Ty;
    let Ty::Adt { name, variants, .. } = ty else {
        return false;
    };
    // The vendored core three-way-compare result type. Accept the extractor's
    // canonical spelling `cmp::Ordering` and any fully-qualified path ending in
    // `::Ordering`; reject any other enum (the "non-Ordering" forgery).
    if !(name == "cmp::Ordering" || name.ends_with("::Ordering") || name == "Ordering") {
        return false;
    }
    // EXACTLY three variants — a wider/narrower enum is not the sign encoding.
    if variants.len() != 3 {
        return false;
    }
    for (vname, want) in [("Less", -1i128), ("Equal", 0), ("Greater", 1)] {
        let Some(v) = variants.iter().find(|v| v.name == vname) else {
            return false; // a missing Less/Equal/Greater — not Ordering.
        };
        if signed_at_width(v.discriminant, disc_width) != Some(want) {
            return false; // wrong discriminant→sign mapping — fail closed.
        }
    }
    true
}

/// Trust: W-CMP-DISCR — the CORE recognizer for `signum`'s three-way-sign
/// normalization. Given the MIR place `ordering_place` holding an `Ordering`
/// value, and the `(width, signed)` of the local that RECEIVES the subsequent
/// `Discriminant` read (the sign-carrier), recognize the `signum` shape
///
/// ```text
/// _o := Cmp(a, 0)           -- three-way compare -> cmp::Ordering
/// _d := Discriminant(_o)    -- tag read: Less -> -1, Equal -> 0, Greater -> 1
/// (_0 := _d [as iN])        -- optional value-identity sign-extend
/// ```
///
/// and return the modeled sign rvalue `ArithBin(Sub, Cmp(Gt, a, 0), Cmp(Lt, a,
/// 0))` = `(a > 0) - (a < 0)` = `signum(a)`. This value is EXACTLY the composed
/// tag-read chain: `Cmp(a, 0)` yields `Less`/`Equal`/`Greater` per `a<0`/`a=0`/
/// `a>0`, whose discriminants are `-1`/`0`/`1` (VERIFIED against the vendored
/// `Ordering` representation via [`ordering_is_three_way_sign_encoding`]), so the
/// discriminant read + sign-extend recovers `signum(a)`. The synthesized
/// arithmetic witness is then kernel-checked modulo 3 by the EXISTING Lemma-1B/1C
/// adequacy (nested `Cmp`/`ArithBin` grounding) — NOT a shape-only promotion.
///
/// FAIL-CLOSED — declines (`None`) unless EVERY gate holds:
///   * the sign-carrier is SIGNED (an unsigned read cannot recover the `-1`
///     `Less` tag);
///   * `_o` is a bare, non-parameter, soundly-resolvable temp whose SOLE
///     assignment is `BinaryOp(Cmp, a, b)` (a multiply-assigned / aliased temp,
///     or a NON-`Cmp` producer, declines);
///   * `b` (the SECOND operand) is the integer constant `0` — a `Cmp` against a
///     NON-zero rhs, or a flipped `Cmp(0, a)` (= `-signum`), declines;
///   * `_o`'s declared type is the vendored `cmp::Ordering` with the exact
///     `Less→-1`/`Equal→0`/`Greater→1` sign encoding at the carrier width;
///   * `a` resolves to a modeled scalar operand.
pub(super) fn resolve_signum_ordering_sign(
    body: &trust_types::VerifiableBody,
    ordering_place: &trust_types::Place,
    disc_width: u32,
    disc_signed: bool,
    param_index: &dyn Fn(usize) -> Option<u64>,
    use_site: Option<(trust_types::BlockId, Option<usize>)>,
) -> Option<SemRvalue> {
    use trust_types::{BinOp, ConstValue, Operand, Rvalue};
    // The sign-carrier must be SIGNED — an unsigned `Discriminant`/cast cannot
    // recover the `-1` `Less` tag (`255` would stay `255`), so the sign witness
    // would be a FALSE model. Fail closed.
    if !disc_signed {
        return None;
    }
    // `_o` a bare (unprojected), non-parameter, soundly-resolvable temp.
    if !ordering_place.projections.is_empty() {
        return None;
    }
    if param_index(ordering_place.local).is_some() {
        return None;
    }
    if !crate::prove::local_soundly_resolvable(body, ordering_place.local) {
        return None; // multiply-assigned, call-dest-written, or mutably aliased.
    }
    // Its SOLE assignment must be `_o := BinaryOp(Cmp, a, b)` and must execute
    // before the Discriminant read that consumes it.
    let (_, _, definition) =
        local_definition_for_optional_use(body, ordering_place.local, use_site)?;
    let Rvalue::BinaryOp(BinOp::Cmp, a, b) = definition else {
        return None;
    };
    // `b` (the SECOND `Cmp` operand) must be the constant 0 — a NON-zero rhs, or
    // a flipped `Cmp(0, a)` where `a` is the second operand, declines here.
    match b {
        Operand::Constant(ConstValue::Int(0)) => {}
        Operand::Constant(ConstValue::Uint(0, _)) => {}
        _ => return None,
    }
    // `_o`'s declared type is the vendored `cmp::Ordering` with the exact
    // three-way sign encoding at the sign-carrier width.
    let ord_ty = &body.locals.get(ordering_place.local)?.ty;
    if !ordering_is_three_way_sign_encoding(ord_ty, disc_width) {
        return None;
    }
    // `a` (the compared value) resolves to a modeled scalar operand.
    let a_op = sem_operand_of_mir(body, a, param_index)?;
    let zero = || Box::new(SemRvalue::Use(SemOperand::Const(0)));
    // signum(a) = (a > 0) - (a < 0).
    Some(SemRvalue::ArithBin(
        SemBinOp::Sub,
        Box::new(SemRvalue::Cmp(SemCmpOp::Gt, Box::new(SemRvalue::Use(a_op.clone())), zero())),
        Box::new(SemRvalue::Cmp(SemCmpOp::Lt, Box::new(SemRvalue::Use(a_op)), zero())),
    ))
}

/// Trust: W-CMP-DISCR — the `i16`/`i32`/`i64` `signum` shape: `_0 := Cast(_d,
/// iN)`, `_d := Discriminant(_o)`, `_o := Cmp(a, 0)`. Recognize the FULL chain
/// from the CAST rvalue and return the sign rvalue `(a > 0) - (a < 0)`. The cast
/// must be a VALUE-PRESERVING SIGN-EXTEND from the signed sign-carrier `_d` to a
/// SIGNED destination (a lossy/narrowing/unsigned cast declines — the `-1`
/// `Less` tag would not survive). (The `i8` `signum` needs no cast — the
/// `Discriminant` read writes `_0` directly — and is recognized at the
/// `Rvalue::Discriminant` return arm, not here.)
pub(super) fn resolve_signum_cast_rvalue(
    body: &trust_types::VerifiableBody,
    op: &trust_types::Operand,
    dest_ty: &trust_types::Ty,
    param_index: &dyn Fn(usize) -> Option<u64>,
    use_site: Option<(trust_types::BlockId, Option<usize>)>,
) -> Option<SemRvalue> {
    use trust_types::{Operand, Rvalue, Ty};
    // `op = Move/Copy(_d)`, `_d` a bare, non-parameter temp.
    let (Operand::Copy(p) | Operand::Move(p)) = op else {
        return None;
    };
    if !p.projections.is_empty() || param_index(p.local).is_some() {
        return None;
    }
    // Destination must be a SIGNED int.
    let Ty::Int { width: dw, signed: true } = dest_ty else {
        return None;
    };
    // `_d`'s declared type: a SIGNED int no wider than the destination
    // (sign-extending widening / same-width — value-preserving).
    let Some(Ty::Int { width: sw, signed: true }) = body.locals.get(p.local).map(|l| &l.ty) else {
        return None;
    };
    let (dw, sw) = (*dw, *sw);
    if dw < sw {
        return None; // narrowing — NOT value-preserving, fail closed.
    }
    if !crate::prove::local_soundly_resolvable(body, p.local) {
        return None;
    }
    // `_d`'s SOLE assignment must be `_d := Discriminant(_o)` and must execute
    // before the outer Cast. The Ordering producer must in turn execute before
    // this Discriminant assignment.
    let (definition_block, definition_statement, definition) =
        local_definition_for_optional_use(body, p.local, use_site)?;
    let Rvalue::Discriminant(ord_place) = definition else {
        return None;
    };
    resolve_signum_ordering_sign(
        body,
        ord_place,
        sw,
        true,
        param_index,
        Some((definition_block, Some(definition_statement))),
    )
}

/// Map a Trust MIR `BinOp` into the MirSem `SemBinOp` fragment — `Add`/`Sub`/`Mul`/
/// `Div`/`Rem`, the binops the Lemma-1B anchor pins in Clean. `Div` grounds to the
/// prelude's `Opaque` `Int.div`; `Rem` (`%`) — Trust: witness-tier Rem arm — grounds
/// to the prelude's `Opaque` TRUNCATED T-remainder `Int.mod` (the SAME grounding the
/// M3 Rem promotion landed for `ground_int`'s `F::Rem` arm, checked three-way by
/// `m3_rem_three_way_agrees`); the former witness-tier coverage gap is closed, so a
/// `%`-bearing body can now enter Lemma 1B.
///
/// Trust: BITWISE SHAPE LANE (2026-07-08) — `BitAnd`/`BitOr`/`BitXor`/`Shl` NOW
/// ALSO map into the fragment (the wrapped-semantics `Int.land`/`Int.lor`/
/// `Int.xor`/`Int.shiftLeft` denotations `trustir_bridge.rs`'s kernel bridge
/// already proves — see `register_int_bitwise`). Callers MUST check the
/// BOOL-CONNECTIVE shape FIRST for the shared `BitOr`/`BitAnd` opcodes (this
/// function does NOT itself distinguish "Bool `x | y`" from "Int `x | y`" — MIR
/// uses the SAME opcode for both, differing only by operand TYPE — see
/// `sem_rvalue_of_mir_at_depth`'s dispatch order). `Shr`/`LShr`/`AShr`
/// (comparison binops are handled separately by `sem_cmpop_of_mir`) are NOT
/// modeled this increment — named residue, still fail-closed.
#[must_use]
pub fn sem_binop_of_mir(op: &trust_types::BinOp) -> Option<SemBinOp> {
    use trust_types::BinOp;
    match op {
        BinOp::Add => Some(SemBinOp::Add),
        BinOp::Sub => Some(SemBinOp::Sub),
        BinOp::Mul => Some(SemBinOp::Mul),
        BinOp::Div => Some(SemBinOp::Div),
        // Trust: witness-tier Rem arm — `%` now maps into the modeled fragment.
        BinOp::Rem => Some(SemBinOp::Rem),
        // Trust: BITWISE SHAPE LANE — genuine-`Int` bitwise/shift now maps into
        // the fragment (see this fn's doc for the BOOL-CONNECTIVE precedence
        // caveat).
        BinOp::BitAnd => Some(SemBinOp::BitAnd),
        BinOp::BitOr => Some(SemBinOp::BitOr),
        BinOp::BitXor => Some(SemBinOp::BitXor),
        BinOp::Shl => Some(SemBinOp::Shl),
        // Trust: M6 rung 6, UNSIGNED-Shr arm — `>>` now maps into the fragment,
        // but ONLY through the UNSIGNED-ONLY admission gate in
        // `sem_rvalue_of_mir_at_depth` (this type-blind opcode map alone is not
        // sufficient admission for `Shr` — see the gate's doc; a signed `>>`
        // fails closed there).
        BinOp::Shr => Some(SemBinOp::Shr),
        // DEFERRED (fail-closed): remaining unmodeled binops (comparisons are
        // handled separately by `sem_cmpop_of_mir`). No false certificate —
        // these never enter Lemma 1B.
        _ => None,
    }
}

/// Map a Trust MIR `Rvalue` into the MirSem `SemRvalue` fragment when it is a scalar
/// `Use`/`BinaryOp`/`CheckedBinaryOp` over modeled operands — the SAME rvalue forms
/// `extract_return_formula` / `resolve_local_value` reflect (`CheckedBinaryOp` is
/// the overflow-checked form whose field 0 grounds identically to `BinaryOp`).
/// `None` (fail-closed) for any rvalue or operand outside the modeled fragment.
///
/// Trust: REASSIGNED-PARAM soundness — `body` is threaded through to
/// [`sem_operand_of_mir`] so a reassigned-parameter operand fails closed here too.
#[must_use]
pub fn sem_rvalue_of_mir(
    body: &trust_types::VerifiableBody,
    rv: &trust_types::Rvalue,
    param_index: &dyn Fn(usize) -> Option<u64>,
) -> Option<SemRvalue> {
    sem_rvalue_of_mir_at_depth(body, rv, param_index, 0, None)
}

pub(super) fn sem_rvalue_of_mir_at_site(
    body: &trust_types::VerifiableBody,
    rv: &trust_types::Rvalue,
    param_index: &dyn Fn(usize) -> Option<u64>,
    use_site: Option<(trust_types::BlockId, Option<usize>)>,
) -> Option<SemRvalue> {
    sem_rvalue_of_mir_at_depth(body, rv, param_index, 0, use_site)
}

/// The depth-threaded body of [`sem_rvalue_of_mir`] — `depth` counts the
/// temp-inlining hops taken through [`resolve_cmp_side`] (0 at every public
/// entry). Only the COMPARE-AS-VALUE `Cmp` arm recurses; `Use`/`Bin` are leaves.
pub(super) fn sem_rvalue_of_mir_at_depth(
    body: &trust_types::VerifiableBody,
    rv: &trust_types::Rvalue,
    param_index: &dyn Fn(usize) -> Option<u64>,
    depth: usize,
    use_site: Option<(trust_types::BlockId, Option<usize>)>,
) -> Option<SemRvalue> {
    use trust_types::Rvalue;
    match rv {
        Rvalue::Use(op) => Some(SemRvalue::Use(sem_operand_of_mir(body, op, param_index)?)),
        Rvalue::BinaryOp(op, a, b) | Rvalue::CheckedBinaryOp(op, a, b) => {
            // Trust: BOOL-CONNECTIVE (BitOr-on-Bool multi-join, 2026-07-08) gets
            // FIRST priority for the `BitOr`/`BitAnd` opcodes, checked BEFORE the
            // generic `sem_binop_of_mir` dispatch below — Trust: BITWISE SHAPE LANE
            // now ALSO maps these SAME opcodes (for genuine `Int` operands), and
            // MIR does not distinguish "Bool `x | y`" from "Int `x | y`" by opcode
            // name, only by operand TYPE, so the Bool-typed check MUST run first or
            // a Bool connective could be mis-denoted as an integer `Int.lor`.
            if matches!(op, trust_types::BinOp::BitOr | trust_types::BinOp::BitAnd)
                && mir_operand_is_bool_typed(body, a)
                && mir_operand_is_bool_typed(body, b)
            {
                // Reuses `resolve_cmp_side` VERBATIM — the SAME temp-inlining
                // discipline `Cmp`'s sides use, so a BitOr operand that is itself a
                // nested comparison OR another BitOr/BitAnd inlines identically.
                let ra = Box::new(resolve_cmp_side(body, a, param_index, depth, use_site)?);
                let rb = Box::new(resolve_cmp_side(body, b, param_index, depth, use_site)?);
                return Some(if matches!(op, trust_types::BinOp::BitOr) {
                    SemRvalue::Or(ra, rb)
                } else {
                    SemRvalue::And(ra, rb)
                });
            }
            if let Some(bin) = sem_binop_of_mir(op) {
                // Trust: M6 rung 6, UNSIGNED-Shr arm — THE UNSIGNED-ONLY GATE.
                // `Int.shiftRight`'s unbounded `a / 2^n` (floor) denotation
                // coincides with the machine `>>` ONLY for a NONNEGATIVE shifted
                // value with a NONNEGATIVE in-range amount — i.e. the logical
                // (unsigned) right shift. A SIGNED shifted value (arithmetic
                // shift: floor semantics on negatives, which is NOT the
                // truncated `Int.div` story and whose reflected formula would
                // therefore be a FALSE model) or a signed/unknown amount fails
                // closed HERE, before any resolution. Both operands must be
                // PROVABLY unsigned from their declared types (bare unsigned
                // local or `Uint` literal — `mir_operand_is_unsigned_int_typed`).
                if matches!(bin, SemBinOp::Shr)
                    && !(mir_operand_is_unsigned_int_typed(body, a)
                        && mir_operand_is_unsigned_int_typed(body, b))
                {
                    return None;
                }
                // BYTE-IDENTICAL to the pre-COMPARE-AS-VALUE arithmetic path for
                // Add/Sub/Mul/Div/Rem: operands resolve via the bare
                // `sem_operand_of_mir` leaf, UNCHANGED. Trust: BITWISE SHAPE LANE —
                // `sem_binop_of_mir` now ALSO maps genuine-`Int` `BitAnd`/`BitOr`/
                // `BitXor`/`Shl` here (the Bool-connective shape for `BitOr`/`BitAnd`
                // was already ruled out above); for THOSE ops specifically, an
                // operand that declines the bare leaf falls back to
                // `resolve_cast_source_operand`'s EXISTING at-most-one-level
                // `Use`-wrapped temp inlining (a field read, or a further
                // param/const) — the SAME reuse discipline the cast-temp guard read
                // established, generalized to the bitwise Bin arm's operands (the
                // `memchr::One::has_needle`-class shape: `_4 := Use((*self).v1);
                // _3 := BitXor(_4, needle)`). Add/Sub/Mul/Div/Rem's operand
                // resolution is UNTOUCHED (still the bare leaf only) — no new
                // soundness surface for the pre-existing arithmetic path.
                // Trust: M6 rung 6 — `Shr` (already unsigned-gated above) joins
                // the bitwise-resolution family.
                if matches!(
                    bin,
                    SemBinOp::BitAnd
                        | SemBinOp::BitOr
                        | SemBinOp::BitXor
                        | SemBinOp::Shl
                        | SemBinOp::Shr
                ) {
                    // Trust: BIT_FIELD NESTED-RVALUE — try the EXISTING flat
                    // resolution for BOTH operands first; when it succeeds on
                    // both sides, keep the FLAT `Bin` shape byte-for-byte (no
                    // regression on the standing flat-bitwise certificates/
                    // pinning tests, e.g.
                    // `sem_rvalue_of_mir_resolves_bitand_on_non_bool_as_genuine_int`).
                    if let (Some(oa), Some(ob)) = (
                        resolve_cast_source_operand(body, a, param_index, use_site),
                        resolve_cast_source_operand(body, b, param_index, use_site),
                    ) {
                        return Some(SemRvalue::Bin(bin, oa, ob));
                    }
                    // At least one side needs the full recursive-rvalue
                    // representation — the `bit_field::get_bit`/`set_bit` shape
                    // `(*self & (1 << bit)) != 0`, where `BitAnd`'s second
                    // operand is itself a computed `Shl(1, bit)` rvalue.
                    // `resolve_bitwise_side` mirrors `resolve_cmp_side`'s
                    // depth-bounded, cycle-safe, single-static-assignment
                    // temp-inlining discipline exactly.
                    let ra = Box::new(resolve_bitwise_side(body, a, param_index, depth, use_site)?);
                    let rb = Box::new(resolve_bitwise_side(body, b, param_index, depth, use_site)?);
                    return Some(SemRvalue::BitBin(bin, ra, rb));
                }
                // Trust: ARITHMETIC NESTED-RVALUE (2026-07-18, Wave-D item 9) — the
                // ARITHMETIC twin of the BITWISE `BitBin` fallback above (this arm
                // now handles Add/Sub/Mul/Div/Rem). Try the FLAT atomic-operand
                // resolution FIRST: when BOTH sides are bare leaves, keep the exact
                // `Bin` shape byte-for-byte (every standing arithmetic certificate/
                // pinning test untouched — a flat `x + y` stays `Bin(Add, ..)`).
                if let (Some(oa), Some(ob)) = (
                    sem_operand_of_mir(body, a, param_index),
                    sem_operand_of_mir(body, b, param_index),
                ) {
                    return Some(SemRvalue::Bin(bin, oa, ob));
                }
                // At least one side is a COMPUTED rvalue, not an atomic operand —
                // the `to_ascii_lowercase` branchless case-mask `Mul(_cast, 32)`,
                // whose `_cast := Cast(<bool guard>, u8)` is a 0/1 embed (a nested
                // `And`/`Cmp` value), not a bare `Var`/`Const`. Resolve BOTH sides
                // recursively via `resolve_bitwise_side` (the SAME depth-bounded,
                // cycle-safe, single-static-assignment discipline the bitwise arm
                // uses) and build `ArithBin`, which reflects (`to_formula`) to the
                // SAME NATIVE `Int.<op>` the flat `Bin` does — so adequacy closes
                // reflexively, identically to `Bin`. Fail-closed if either side
                // declines nested too.
                let ra = Box::new(resolve_bitwise_side(body, a, param_index, depth, use_site)?);
                let rb = Box::new(resolve_bitwise_side(body, b, param_index, depth, use_site)?);
                Some(SemRvalue::ArithBin(bin, ra, rb))
            } else if let Some(cmp) = sem_cmpop_of_mir(op) {
                // Trust: COMPARE-AS-VALUE — a comparison BinaryOp used as a
                // Bool-typed VALUE. Each side resolves via `resolve_cmp_side`
                // (param/const/deref-self directly, or a single-level-inlined
                // temp), never left as a raw cross-reference.
                Some(SemRvalue::Cmp(
                    cmp,
                    Box::new(resolve_cmp_side(body, a, param_index, depth, use_site)?),
                    Box::new(resolve_cmp_side(body, b, param_index, depth, use_site)?),
                ))
            } else {
                None // an unmodeled binop (Shr/LShr/AShr/`Cmp` 3-way/…) — fail closed.
            }
        }
        // Trust: WALL-CAST-LEAF (2026-07-16) — CAST-BEFORE-COMPARE. A `Cast(op,
        // dest_ty)` rvalue INLINED through the compare-side chase
        // (`resolve_cmp_side` finds a compared temp `_k := Cast(op, dest_ty)` —
        // the `char::is_ascii` shape `_3 := *self as u32; _0 := Le(_3, 127)`,
        // where the `char` receiver's `as u32` widening precedes the return
        // compare, vs the cast-free `u8::is_ascii` `_0 := Le(*self, 127)`). A
        // SOUND WIDENING / value-identity cast is the IDENTITY on the unbounded
        // `Int` carrier, so the compared value is EXACTLY its (resolved) source:
        // delegate to [`resolve_widening_cast_rvalue`] — the SAME value-identity
        // leaf machinery the direct-return cast arm (`sem_return_of_mir`) and the
        // bitwise/checked-field arms already use, INCLUDING the just-landed
        // GAP-CROSS-SIGN-WIDEN sign-crossing widening and the M6-rung-6
        // shift-narrowed exact-width fact. Its result is `SemRvalue::Use(<resolved
        // source>)` (or the `Bin(Shr,..)` width-fact rvalue), which the enclosing
        // `Cmp` composes — the kernel adequacy witness for `Cmp(op, Use(src),
        // Const c)` then grounds the cast-identity operand against the vendored
        // `semCast`/`decide (Int.le ..)` semantics (kernel-anchored by
        // `bridge_cast_zext_widening_identity` &c. in `trustir_bridge.rs`), so the
        // promotion is grounder-connected, NOT shape-only.
        //
        // FAIL-CLOSED — [`resolve_widening_cast_rvalue`] admits ONLY a
        // value-preserving cast and declines every other shape, so a NARROWING or
        // lossy cast on the compared operand fails closed HERE (the compare then
        // declines, the whole body stays SHAPE_GAP):
        //   * a genuine NARROWING cast `u_W -> u_w` (`dw < sw`, not the
        //     shift-narrowed width fact) truncates — value NOT preserved — DECLINES;
        //   * a same-width signedness REINTERPRET (`u_w -> i_w`) changes the value
        //     of top-half inputs (`u8 255 -> i8 == -1`) — DECLINES;
        //   * a non-integer (float/pointer) cast — outside the fragment — DECLINES;
        //   * a cast whose source does not soundly resolve (multiply-assigned,
        //     call-dest/mutably-aliased temp, or a projected source) — DECLINES.
        // Trust: W-CMP-DISCR (2026-07-16) — a value-preserving widening cast is
        // tried FIRST (byte-identical); when it declines, the `signum` cast chain
        // `_0 := Cast(Discriminant(Cmp(a, 0)), iN)` is recognized as the
        // three-way sign `(a > 0) - (a < 0)` (fail-closed against the vendored
        // `cmp::Ordering` representation — see `resolve_signum_cast_rvalue`).
        Rvalue::Cast(op, dest_ty) => {
            resolve_widening_cast_rvalue(body, op, dest_ty, param_index, use_site)
                .or_else(|| resolve_signum_cast_rvalue(body, op, dest_ty, param_index, use_site))
                // Trust: BOOL→INT EMBED (2026-07-18, Wave-D item 9) — `Cast(<bool>, iN)`,
                // the 0/1 embed of a Bool value. Resolve at this exact use site so a
                // later or non-dominating temp definition cannot supply the cast.
                .or_else(|| {
                    resolve_bool_cast_embed_rvalue(
                        body,
                        op,
                        dest_ty,
                        param_index,
                        depth,
                        use_site,
                    )
                })
        }
        _ => None,
    }
}

/// Trust: BOOL→INT EMBED (2026-07-18, Wave-D item 9) — model `Cast(<bool op>, iN)`
/// (a `bool as u8` / `as i32` …) as the 0/1 INT EMBED of the Bool value: EXACTLY the
/// `SemRvalue` [`resolve_cmp_side`] already produces for that Bool operand (a bare
/// `Var`/`Const` for a bool param/literal, an inlined `Cmp` for a single-assigned
/// comparison temp, or the guarded-local `And`/`Or` tree for a range diamond). Sound
/// and value-faithful: a Rust `bool` is modeled by the opaque `Int` 0/1 carrier
/// (`bool_as_int`), and `<bool> as iN` IS that carrier value (`false ↦ 0`, `true ↦ 1`)
/// — the cond rvalue's own denotation. `None` (fail-closed) unless `dest_ty` is an
/// integer AND `op` is a genuinely `Ty::Bool`-typed operand (a non-Bool source is a
/// widening/signum/lossy cast the two resolvers above own, or an unmodeled cast).
pub(super) fn resolve_bool_cast_embed_rvalue(
    body: &trust_types::VerifiableBody,
    op: &trust_types::Operand,
    dest_ty: &trust_types::Ty,
    param_index: &dyn Fn(usize) -> Option<u64>,
    depth: usize,
    use_site: Option<(trust_types::BlockId, Option<usize>)>,
) -> Option<SemRvalue> {
    if !matches!(dest_ty, trust_types::Ty::Int { .. }) {
        return None; // a bool→float / bool→bool cast is not the int embed.
    }
    if !mir_operand_is_bool_typed(body, op) {
        return None; // the source is not a Bool value — not this fragment.
    }
    resolve_cmp_side(body, op, param_index, depth, use_site)
}

/// Trust: BOOL-CONNECTIVE (BitOr-on-Bool multi-join) — does MIR `Operand` `op`
/// denote a `Ty::Bool`-typed value: a bare place (no projections) whose
/// DECLARED local type is `Ty::Bool`, or a literal `Bool` constant. `None`
/// (`false`) for anything else — a projected place, a non-Bool-typed local, or a
/// non-Bool constant — so a genuine INTEGER `BitOr`/`BitAnd` is never swept into
/// the Bool-connective fragment.
pub(super) fn mir_operand_is_bool_typed(
    body: &trust_types::VerifiableBody,
    op: &trust_types::Operand,
) -> bool {
    use trust_types::{ConstValue, Operand, Ty};
    match op {
        Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => {
            matches!(body.locals.get(p.local).map(|l| &l.ty), Some(Ty::Bool))
        }
        Operand::Constant(ConstValue::Bool(_)) => true,
        _ => false,
    }
}

/// Trust: M6 rung 6, UNSIGNED-Shr arm — does MIR `Operand` `op` PROVABLY denote
/// an UNSIGNED integer value: a bare place (no projections) whose DECLARED local
/// type is `Ty::Int { signed: false, .. }`, or a literal `Uint` constant.
/// `false` (fail-closed) for anything else — a projected place (its type is not
/// directly declared), a signed or non-integer local, or any other constant —
/// so a SIGNED (arithmetic) right shift can never be swept into the
/// `Int.shiftRight` logical-shift denotation. Mirrors
/// [`mir_operand_is_bool_typed`]'s declared-type discipline exactly.
///
/// `pub(crate)` for Trust: M6 rung 6, SHR→TRUST-IR ANCHOR relocation —
/// `prove::straight_line_ir_body`'s `to_ir_binop` re-applies this SAME gate
/// before admitting `BinOp::Shr` into the trust-ir straight-line fragment (the
/// via-trustir lane's own copy of the admission decision, never a weaker one).
pub(crate) fn mir_operand_is_unsigned_int_typed(
    body: &trust_types::VerifiableBody,
    op: &trust_types::Operand,
) -> bool {
    use trust_types::{ConstValue, Operand, Ty};
    match op {
        Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => {
            matches!(body.locals.get(p.local).map(|l| &l.ty), Some(Ty::Int { signed: false, .. }))
        }
        Operand::Constant(ConstValue::Uint(_, _)) => true,
        _ => false,
    }
}

/// Trust: W-LEN-ISEMPTY (2026-07-17) — resolve a bare PARAM slice place to the
/// opaque-total `SemOperand::Len(Var param)` slice-length carrier — the SAME
/// carrier [`sem_guard_operand_of_mir`] already establishes for a `s.len()` in the
/// index-GUARD context (`PtrMetadata(slice)`/`Rvalue::Len`), reused here on the
/// value side. `None` (fail-closed) unless ALL hold — the discriminant lane's
/// entry-time-value gates, applied to a slice reference:
///   * the place is a BARE (unprojected) parameter local;
///   * the parameter is NOT [`param_reassigned_by_stmt`] (a reassigned /
///     mutably-aliased / call-dest-written receiver cannot be modeled as its entry
///     `Var`);
///   * the receiver's declared type is EXACTLY an IMMUTABLE slice reference
///     `&[T]` (`Ty::Ref { mutable: false, inner: Ty::Slice }`) — a `&mut`
///     receiver declines (belt-and-suspenders with the discriminant lane's
///     identical `&mut` decline), and a non-slice / by-value base is outside the
///     fat-pointer-metadata fragment.
/// HONEST TIER: uninterpreted-but-total — `Len` is the opaque total slice length
/// (the `idxElem`-family carrier), faithful to the MIR metadata read, NOT a claim
/// relating the length to element counts.
pub(super) fn slice_len_of_param_place(
    body: &trust_types::VerifiableBody,
    place: &trust_types::Place,
    param_index: &dyn Fn(usize) -> Option<u64>,
) -> Option<SemOperand> {
    use trust_types::Ty;
    if !place.projections.is_empty() {
        return None;
    }
    let idx = param_index(place.local)?;
    if param_reassigned_by_stmt(body, place.local) {
        return None;
    }
    match body.locals.get(place.local).map(|l| &l.ty) {
        Some(Ty::Ref { mutable: false, inner }) if matches!(**inner, Ty::Slice { .. }) => {}
        _ => return None, // `&mut [T]`, or a non-slice / by-value base — declines.
    }
    Some(SemOperand::Len(Box::new(SemOperand::Var(idx))))
}

/// Trust: W-LEN-ISEMPTY (2026-07-17) — resolve the OPERAND of a `UnaryOp(PtrMetadata,
/// op)` to the `SemOperand::Len` carrier: `op` (or the temp it copies) names a PARAM
/// slice, possibly behind ONE level of SAME-FAT-POINTER reinterpret `Cast`
/// (`str::len`/`str::is_empty` cast `&str` to `&[u8]` before reading metadata; the
/// extractor spells `str` as `[u8]`, so the cast's source and dest types are
/// STRUCTURALLY EQUAL). The type-equality check is the "verifiable same-fat-pointer
/// cast" gate the corpus PROVENANCE requires: a slice-element-SIZE-changing
/// reinterpret (`&[u32]` to `&[u8]`), whose `PtrMetadata` is a DIFFERENT element
/// count, has UNEQUAL source/dest types and declines fail-closed. `None` unless:
///   * `op` is a `Copy/Move` of a bare place resolving DIRECTLY as a param slice
///     ([`slice_len_of_param_place`]); OR
///   * that place is a non-parameter TEMP, [`crate::prove::local_soundly_resolvable`]
///     (single static assignment, no call-dest write, no mutable alias), whose SOLE
///     assignment is `Cast(<param slice>, dest_ty)` with `dest_ty` STRUCTURALLY EQUAL
///     to the (bare, unprojected) cast source's declared type, and the source itself
///     resolves as a param slice; and
///   * that sole cast definition strictly precedes the metadata read in the same
///     block, or its block dominates the metadata-read block. This is checked at
///     the exact use site so a later or sibling-branch cast in hostile serialized
///     MIR cannot donate a value to the returning path.
pub(super) fn resolve_ptr_metadata_slice_len(
    body: &trust_types::VerifiableBody,
    op: &trust_types::Operand,
    param_index: &dyn Fn(usize) -> Option<u64>,
    use_site: (trust_types::BlockId, Option<usize>),
) -> Option<SemOperand> {
    use trust_types::{Operand, Rvalue};
    let (Operand::Copy(p) | Operand::Move(p)) = op else { return None };
    // Direct param slice place — `slice::is_empty`/`slice::len`.
    if let Some(len) = slice_len_of_param_place(body, p, param_index) {
        return Some(len);
    }
    // Otherwise, the ONE-LEVEL same-fat-pointer cast passthrough — a NON-parameter
    // temp whose sole assignment is the reinterpret cast.
    if !p.projections.is_empty() || param_index(p.local).is_some() {
        return None;
    }
    let (_, _, rv) = unique_local_definition_dominating(body, p.local, use_site.0, use_site.1)?;
    if let Rvalue::Cast(Operand::Copy(sp) | Operand::Move(sp), dest_ty) = rv {
        if !sp.projections.is_empty() {
            return None;
        }
        let src_ty = body.locals.get(sp.local).map(|l| &l.ty)?;
        // SAME-FAT-POINTER: identical source/dest layout ⇒ `PtrMetadata` (the slice
        // length) is preserved BY CONSTRUCTION. `slice_len_of_param_place` then
        // re-checks the source is a bare, immutable, non-reassigned param slice.
        if src_ty == dest_ty {
            return slice_len_of_param_place(body, sp, param_index);
        }
    }
    None
}

/// Trust: COMPARE-AS-VALUE — resolve ONE SIDE of a value-position comparison
/// (`_0 := Eq(_2, 0)`-class) to a `SemRvalue`: a modeled scalar operand
/// (param/const/deref-self — via [`sem_operand_of_mir`], wrapped in `Use`), OR,
/// INLINE ONE LEVEL, a non-parameter TEMP whose SOLE static assignment is itself
/// a [`sem_rvalue_of_mir`]-modeled rvalue (arithmetic, a nested comparison, or
/// another `Use`), substituted DIRECTLY. Mirrors
/// [`resolve_cast_source_operand`]'s inlining discipline, generalized from a bare
/// `Use` wrap to the FULL `sem_rvalue_of_mir` fragment — so `_2 := Rem(_1, 2)`
/// feeding a comparison (`ts-is-even`'s `_0 := Eq(_2, 0)`) inlines as `Bin(Rem,
/// Var(0), Const(2))` rather than being left as an unresolvable cross-reference
/// to a non-parameter local (the SAME temp-chasing
/// `clean_ground::operand_to_formula`/`resolve_local_value`'s mutual recursion
/// already performs on the live-reflection side, so the two extraction paths stay
/// in lock-step). `None` (fail-closed) for a multiply-assigned/aliased temp that is
/// ALSO not the [`sem_guarded_local_value`] GUARDED-LOCAL shape (see below), an
/// rvalue outside the modeled fragment, or a chain deeper than
/// [`CMP_INLINE_MAX_DEPTH`] (the cycle/stack-overflow defense — see the constant's
/// doc).
///
/// Trust: GUARDED-LOCAL layer (BOOL-CONNECTIVE composition, 2026-07-08) — when `op`
/// is a bare temp that is NOT single-assignment (so [`crate::prove::local_soundly_resolvable`]
/// declines it), it may instead be a `Bool` local reified by a SMALL GUARDED sub-CFG —
/// the `is_ascii_alphanumeric`-class shape, where a `BitOr`/`BitAnd`/`Cmp` operand is
/// itself a conjunctive range check (`_3 := 48<=*self && *self<=57`), not a flat
/// single-assignment rvalue. [`sem_guarded_local_value`] recognizes that sub-CFG
/// (REUSING [`sem_conjunctive_chain`], scoped to the operand's own two arm blocks) and
/// returns the [`SemCondTree`] it denotes; [`cond_tree_to_rvalue`] translates that tree
/// into the equivalent `SemRvalue`, spliced in here exactly where the flat-inlining
/// path would otherwise leave an unresolvable cross-reference.
pub(super) fn resolve_cmp_side(
    body: &trust_types::VerifiableBody,
    op: &trust_types::Operand,
    param_index: &dyn Fn(usize) -> Option<u64>,
    depth: usize,
    use_site: Option<(trust_types::BlockId, Option<usize>)>,
) -> Option<SemRvalue> {
    use trust_types::Operand;
    if let Some(direct) = sem_operand_of_mir(body, op, param_index) {
        return Some(SemRvalue::Use(direct));
    }
    // Trust: COMPARE-AS-VALUE recursion bound — a cyclic adversarial temp chain
    // (undetectable by the PER-LOCAL `local_soundly_resolvable` gate) must
    // DECLINE, never recurse to stack overflow.
    if depth >= CMP_INLINE_MAX_DEPTH {
        return None;
    }
    let (Operand::Copy(p) | Operand::Move(p)) = op else { return None };
    if !p.projections.is_empty() || param_index(p.local).is_some() {
        return None;
    }
    if crate::prove::local_soundly_resolvable(body, p.local) {
        let (definition_block, definition_statement, rvalue) =
            local_definition_for_optional_use(body, p.local, use_site)?;
        let definition_use_site = Some((definition_block, Some(definition_statement)));
        // Trust: OPTRES-ACCESSOR DISCRIMINANT-COMPARE LEAF (2026-07-16) — a
        // compared temp whose SOLE assignment is `_t := Discriminant(place)`,
        // the enum-tag read `is_some`/`is_ok` compare against a tag constant
        // (`_2 := Discriminant((*self)); _0 := Eq(_2, K)`). Resolve it to the
        // SAME opaque `idx_elem`-keyed `SemOperand::Discriminant` carrier the
        // discriminant GUARD/VALUE leaves already establish
        // (`sem_discriminant_base_of_mir`, keyed at `MIRSEM_DISCRIMINANT_TAG_KEY`),
        // wrapped as a `SemRvalue::Use` so the enclosing `Cmp` composes it EXACTLY
        // as it composes an `Index`/`Var`/`Const` side. Its own soundness gates
        // (immutable receiver, no deref-write, single static assignment) are the
        // discriminant leaf's UNCHANGED gates — a `&mut self` receiver / a
        // non-reference base / a write-through declines fail-closed there. HONEST
        // TIER: uninterpreted-but-total, faithful to the MIR tag-compare — the
        // tag is the `idx_elem` opaque, NOT a semantic "is-Some" predicate.
        if let trust_types::Rvalue::Discriminant(place) = rvalue {
            let base = sem_discriminant_base_of_mir(body, place, param_index, definition_use_site)?;
            return Some(SemRvalue::Use(SemOperand::Discriminant(Box::new(base))));
        }
        // Trust: W-LEN-ISEMPTY (2026-07-17) — a compared temp whose SOLE assignment
        // is `_t := UnaryOp(PtrMetadata, <param slice>)` or `_t := Len(<param slice>)`
        // — the `slice::is_empty`/`str::is_empty` metadata-compare `_2 :=
        // PtrMetadata(self); _0 := Eq(_2, 0)`. Resolve it to the SAME opaque-total
        // `SemOperand::Len` slice-length carrier `sem_guard_operand_of_mir` already
        // establishes in the index-GUARD context, wrapped as `SemRvalue::Use` so the
        // enclosing `Cmp` composes it EXACTLY as it composes the Discriminant/Index
        // side — the DIRECT analogue of the discriminant-compare arm above. Its
        // fail-closed gates (bare PARAM slice, immutable receiver, not reassigned,
        // single-assignment length temp, ONE verifiable same-fat-pointer cast) live
        // in `resolve_ptr_metadata_slice_len`/`slice_len_of_param_place`. HONEST
        // TIER: uninterpreted-but-total — `Len` is the opaque total length, faithful
        // to the MIR metadata-compare, NOT a claim relating length to element counts.
        if let trust_types::Rvalue::UnaryOp(trust_types::UnOp::PtrMetadata, inner) = rvalue {
            let len = resolve_ptr_metadata_slice_len(
                body,
                inner,
                param_index,
                (definition_block, Some(definition_statement)),
            )?;
            return Some(SemRvalue::Use(len));
        }
        if let trust_types::Rvalue::Len(place) = rvalue {
            let len = slice_len_of_param_place(body, place, param_index)?;
            return Some(SemRvalue::Use(len));
        }
        return sem_rvalue_of_mir_at_depth(
            body,
            rvalue,
            param_index,
            depth + 1,
            definition_use_site,
        );
    }
    // Trust: GUARDED-LOCAL layer — the single-assignment inlining above declined;
    // try the guarded sub-CFG reification instead. Bounded and fail-closed on its own
    // terms (uniqueness/no-writes-between/bounded-switch-count — see
    // `sem_guarded_local_value`'s doc), so this adds no NEW soundness surface beyond
    // what that recognizer already gates.
    sem_guarded_local_value(body, p.local, param_index, use_site)
        .map(|cond| cond_tree_to_rvalue(&cond))
}

/// Trust: OPTRES-ACCESSOR NOT-LEAF (2026-07-16) — resolve the `is_none`/`is_err`
/// return `_0 := UnaryOp(Not, _t)`, where `_t` is the Bool-typed
/// `is_some`/`is_ok` tag-compare value `_t := Eq(Discriminant((*self)), K)`.
///
/// FAITHFUL negation via the EXISTING `Ne` machinery — NOT a no-op, NOT a new
/// kernel term. `Not(Eq a b)` is DEFINITIONALLY `Ne a b`: [`SemCmpOp::Ne`]
/// reflects to `Formula::Not(Formula::Eq a b)` and grounds/denotes to
/// `Bool.not (Int.beq (eval a) (eval b))` — i.e. the MIR `UnaryOp(Not)` IS the
/// `Bool.not` head of the flipped comparison. So flipping the outer `Eq`↔`Ne`
/// models the negation EXACTLY, reusing the shipped, kernel-checked
/// `SemRvalue::Cmp` adequacy path. Dropping the `Not` (claiming `is_none ==
/// is_some`) would emit an `Eq` with NO `Bool.not` head — a DIFFERENT grounded
/// term the kernel rejects (`check_return_adequacy`'s `claimed_rhs` probe).
///
/// FAIL-CLOSED unless:
///   * the negated operand is a bare (unprojected) local whose DECLARED type is
///     EXACTLY `Ty::Bool` — Rust `!` on `bool` IS logical negation; `!` on an
///     integer is bitwise complement (a different value), which must decline;
///   * that operand resolves (via [`resolve_cmp_side`], INCLUDING the
///     discriminant-compare leaf) to a FLAT `Eq`/`Ne` comparison. A conjunction,
///     a non-`Eq`/`Ne` comparison, or an arithmetic value is outside the
///     faithful-flip fragment and declines.
pub(super) fn resolve_not_of_bool_cmp(
    body: &trust_types::VerifiableBody,
    operand: &trust_types::Operand,
    param_index: &dyn Fn(usize) -> Option<u64>,
    use_site: Option<(trust_types::BlockId, Option<usize>)>,
) -> Option<SemRvalue> {
    use trust_types::{Operand, Ty};
    let (Operand::Copy(p) | Operand::Move(p)) = operand else { return None };
    if !p.projections.is_empty() {
        return None; // a projected place is not the plain Bool tag-compare temp.
    }
    if !matches!(body.locals.get(p.local).map(|l| &l.ty), Some(Ty::Bool)) {
        return None; // NON-bool operand — `!x` would be bitwise, not logical.
    }
    match resolve_cmp_side(body, operand, param_index, 0, use_site)? {
        SemRvalue::Cmp(SemCmpOp::Eq, ra, rb) => Some(SemRvalue::Cmp(SemCmpOp::Ne, ra, rb)),
        SemRvalue::Cmp(SemCmpOp::Ne, ra, rb) => Some(SemRvalue::Cmp(SemCmpOp::Eq, ra, rb)),
        _ => None, // outside the faithful Eq↔Ne flip fragment — fail closed.
    }
}

/// Trust: BIT_FIELD NESTED-RVALUE (2026-07-08) — resolve ONE SIDE of a
/// bitwise/shift `BinaryOp` (`BitAnd`/`BitOr`/`BitXor`/`Shl`, genuine-`Int`
/// operands) to a `SemRvalue`, trying the EXISTING flat leaf
/// ([`resolve_cast_source_operand`] — param/const/deref-self/field-read, or
/// one level of `Use`-wrapped temp inlining) FIRST, wrapped as
/// `SemRvalue::Use`; if that declines, inlining ONE level through a
/// non-parameter temp whose SOLE static assignment is itself a
/// [`sem_rvalue_of_mir_at_depth`]-modeled rvalue, substituted DIRECTLY as a
/// NESTED `SemRvalue` rather than left as an unresolvable cross-reference —
/// the `bit_field::get_bit`/`set_bit` shape `_7 := Shl(1, bit); _5 :=
/// BitAnd(_6, _7)`, where `_7` is not a flat operand.
///
/// Mirrors [`resolve_cmp_side`]'s EXACT depth-bounded, cycle-safe,
/// single-static-assignment discipline (the SAME [`CMP_INLINE_MAX_DEPTH`]
/// bound, the SAME [`crate::prove::local_soundly_resolvable`] uniqueness
/// gate that declines a multiply-assigned/aliased temp) — the ONLY
/// difference is the LEAF resolver: [`resolve_cast_source_operand`] (which
/// ALSO covers a field read, e.g. `memchr::One::has_needle`'s
/// `_4 := Use((*self).v1)` shape) in place of `resolve_cmp_side`'s bare
/// [`sem_operand_of_mir`], so the field-read-capable flat bitwise path keeps
/// resolving too, not just the plain-parameter one. `None` (fail-closed) for
/// a multiply-assigned/aliased temp, a chain deeper than the bound, or an
/// rvalue outside the modeled fragment.
pub(super) fn resolve_bitwise_side(
    body: &trust_types::VerifiableBody,
    op: &trust_types::Operand,
    param_index: &dyn Fn(usize) -> Option<u64>,
    depth: usize,
    use_site: Option<(trust_types::BlockId, Option<usize>)>,
) -> Option<SemRvalue> {
    use trust_types::Operand;
    if let Some(direct) = resolve_cast_source_operand(body, op, param_index, use_site) {
        return Some(SemRvalue::Use(direct));
    }
    // Trust: BIT_FIELD NESTED-RVALUE recursion bound — SAME cycle/stack-overflow
    // defense as `resolve_cmp_side` (a cyclic adversarial temp chain, undetectable
    // by the PER-LOCAL `local_soundly_resolvable` gate, must DECLINE, never crash).
    if depth >= CMP_INLINE_MAX_DEPTH {
        return None;
    }
    let (Operand::Copy(p) | Operand::Move(p)) = op else { return None };
    if !p.projections.is_empty() || param_index(p.local).is_some() {
        return None;
    }
    // Trust: Call-dest/mutable-alias SOUNDNESS — the SAME uniqueness gate
    // `resolve_cmp_side`/`resolve_cast_source_operand` apply: a multiply-assigned
    // OR call-dest/mutably-aliased temp is NOT soundly a single static definition.
    if !crate::prove::local_soundly_resolvable(body, p.local) {
        return None;
    }
    let (definition_block, definition_statement, rvalue) =
        local_definition_for_optional_use(body, p.local, use_site)?;
    sem_rvalue_of_mir_at_depth(
        body,
        rvalue,
        param_index,
        depth + 1,
        Some((definition_block, Some(definition_statement))),
    )
}

/// Trust: GUARDED-LOCAL layer — recognize a `Bool`-typed local `target` whose value
/// is assigned by a SMALL GUARDED sub-CFG: the SAME conjunctive 2-switch range-check
/// pattern [`sem_conjunctive_chain`] already recognizes as a TOP-LEVEL guarded-return
/// shape, reused here (COMPOSITION, NOT NEW THEORY) but scoped to a single local and
/// with the arms constrained to reify the condition AS a value (`true`/`false`
/// literals) rather than an arbitrary arm rvalue. Concretely, the
/// `is_ascii_alphanumeric`-class MIR:
///
/// ```text
/// _4 := 48 <= *self;           switchInt(_4)  { 0 => bb1, otherwise => bb3 }
/// bb3: _5 := *self <= 57;      switchInt(_5)  { 0 => bb1, otherwise => bb2 }
/// bb1: _3 := false;            goto bb4
/// bb2: _3 := true;             goto bb4
/// ```
///
/// so `_3` denotes `48 <= *self && *self <= 57` — a value later fed into a `BitOr`
/// (`_2 := BitOr(_3, _6)`) whose own operands are NOT flat comparisons.
///
/// Returns the [`SemCondTree`] `target` denotes; [`resolve_cmp_side`] splices it (via
/// [`cond_tree_to_rvalue`]) into the enclosing `Cmp`/`Or`/`And` tree.
///
/// FAIL-CLOSED (`None`) when:
///   * `target` is not `Ty::Bool`, or is written ANYWHERE other than exactly the two
///     recognized arm blocks — the UNIQUENESS gate: exactly two `Statement::Assign`s
///     total ([`crate::prove::local_write_count`] `== 2`) and never a
///     `Terminator::Call` dest (the SAME invisible-write blind spot
///     [`crate::prove::local_soundly_resolvable`]'s class-2 check closes for the
///     single-assignment case, specialized here to "exactly 2"). Because these are
///     the ONLY writes to `target` anywhere in the body, there are — by construction —
///     no writes between either arm's assignment and any later read.
///   * the two arms do not `Goto` a single common join, or either arm's value is not
///     the LITERAL `true`/`false` reification (any other arm value is a different
///     recognizer's shape — an `Ite`/`Sel`-style conditional update, not a Bool
///     connective operand).
///   * the guard is not the recognized single-comparison or conjunctive-chain shape
///     (anything [`sem_conjunctive_chain`] itself declines).
///   * the scoped candidate switch set is empty or exceeds
///     [`GUARDED_LOCAL_MAX_SWITCHES`] — the BOUNDED sub-CFG size gate.
pub(super) fn sem_guarded_local_value(
    body: &trust_types::VerifiableBody,
    target: usize,
    param_index: &dyn Fn(usize) -> Option<u64>,
    use_site: Option<(trust_types::BlockId, Option<usize>)>,
) -> Option<SemCondTree> {
    use trust_types::{BlockId, Operand, Rvalue, Statement, Terminator, Ty};

    // `target` must be Bool-typed — never denote an Int-typed local as a Cond value.
    if !matches!(body.locals.get(target).map(|l| &l.ty), Some(Ty::Bool)) {
        return None;
    }
    // Trust: uniqueness gate — EXACTLY two writes total (the two arms) and never an
    // invisible call-dest write. Specialized "exactly 2" twin of
    // `local_soundly_resolvable`'s class-1/class-2 checks.
    if !local_has_only_guarded_writes(body, target, 2, 0) {
        return None;
    }

    // The two arms: `Goto`-terminated blocks that assign `target`, converging on a
    // single common join (byte-identical shape to `sem_cf_return_of_mir`'s own
    // arm-detection, scoped to `target` instead of the convergence local).
    let assigns_target = |b: &trust_types::BasicBlock| {
        b.stmts.iter().any(|s| {
            matches!(s, Statement::Assign { place, .. } if place.local == target && place.projections.is_empty())
        })
    };
    let arms: Vec<&trust_types::BasicBlock> = body
        .blocks
        .iter()
        .filter(|b| matches!(b.terminator, Terminator::Goto(_)) && assigns_target(b))
        .collect();
    if arms.len() != 2 {
        return None;
    }
    let Terminator::Goto(j0) = arms[0].terminator else { return None };
    let Terminator::Goto(j1) = arms[1].terminator else { return None };
    if j0 != j1 {
        return None;
    }
    let arm_ids: Vec<BlockId> = arms.iter().map(|b| b.id).collect();

    // Scope the candidate switches to EXACTLY this local's own guard chain: a switch
    // belongs here iff its explicit (value-0) edge reaches one of `target`'s two arms
    // DIRECTLY (no further switches in between) — the SAME per-switch invariant
    // `sem_conjunctive_chain` itself validates for chain membership, used here to
    // SELECT membership out of the whole body's switch population instead of merely
    // checking it. A switch feeding a DIFFERENT local's chain has a value-0 edge
    // landing elsewhere, so it is excluded without any shared-block ambiguity.
    let all_switches: Vec<(&Operand, &Vec<(u128, BlockId)>, BlockId, BlockId)> = body
        .blocks
        .iter()
        .filter_map(|b| match &b.terminator {
            Terminator::SwitchInt { discr, targets, otherwise, .. } => {
                Some((discr, targets, *otherwise, b.id))
            }
            _ => None,
        })
        .collect();
    let local_switches: Vec<(&Operand, &Vec<(u128, BlockId)>, BlockId, BlockId)> = all_switches
        .iter()
        .filter(|(_, targets, _, _)| match targets.as_slice() {
            [(zero_val, else_target)] => {
                *zero_val == 0 && first_arm_on_path(body, *else_target, &arm_ids).is_some()
            }
            // Trust: GUARDED-LOCAL layer scope — plain range checks only (no
            // discriminant-guard leaf here; that shape's own top-level recognizer
            // already covers it independently).
            _ => false,
        })
        .copied()
        .collect();
    if local_switches.is_empty() || local_switches.len() > GUARDED_LOCAL_MAX_SWITCHES {
        return None;
    }
    let reachable = cfg_reachable_from(body, BlockId(0))?;
    if !reachable.contains(&j0)
        || arm_ids.iter().any(|id| !reachable.contains(id))
        || local_switches.iter().any(|(_, _, _, id)| !reachable.contains(id))
    {
        return None;
    }
    if let Some((use_block, _)) = use_site
        && !block_dominates(body, j0, use_block)
    {
        return None;
    }

    // The leaf builder — a plain scalar comparison discriminant temp, byte-identical
    // to `sem_cf_return_of_mir`'s own `switch_leaf` minus the discriminant-guard arm
    // (out of scope for a Bool-local range-check reification).
    let switch_leaf = |discr: &Operand, _tag: u128| -> Option<SemCond> {
        let (Operand::Copy(dp) | Operand::Move(dp)) = discr else { return None };
        if !dp.projections.is_empty() {
            return None;
        }
        let (definition_block, definition_statement, cmp_rvalue) =
            dominating_switch_discriminant_rvalue(body, dp.local)?;
        match cmp_rvalue {
            Rvalue::BinaryOp(cmp_op, ca, cb) => Some(SemCond {
                op: sem_cmpop_of_mir(cmp_op)?,
                a: sem_guard_operand_of_mir(
                    body,
                    ca,
                    param_index,
                    Some((definition_block, Some(definition_statement))),
                )?,
                b: sem_guard_operand_of_mir(
                    body,
                    cb,
                    param_index,
                    Some((definition_block, Some(definition_statement))),
                )?,
            }),
            _ => None,
        }
    };

    let (cond, else_arm_id, then_arm_id): (SemCondTree, BlockId, BlockId) =
        if let [(discr, targets, otherwise, _bid)] = local_switches.as_slice() {
            let [(zero_val, else_target)] = targets.as_slice() else { return None };
            if *zero_val != 0 {
                return None;
            }
            let leaf = switch_leaf(discr, 0)?;
            let else_id = first_arm_on_path(body, *else_target, &arm_ids)?;
            let then_id = first_arm_on_path(body, *otherwise, &arm_ids)?;
            (SemCondTree::Leaf(leaf), else_id, then_id)
        } else {
            sem_conjunctive_chain(body, &local_switches, &arm_ids, &switch_leaf)?
        };
    if else_arm_id == then_arm_id {
        return None;
    }
    let else_arm = *arms.iter().find(|b| b.id == else_arm_id)?;
    let then_arm = *arms.iter().find(|b| b.id == then_arm_id)?;

    // The ELSE arm must reify to the LITERAL `false` in BOTH the pure-guard and the
    // compact-conjunctive shapes below: the diamond `if guard { <then> } else { false }`
    // short-circuits to `false` when the guard fails, so a non-`false` else arm is a
    // DIFFERENT shape (`if guard { true } else { D }` ≡ `guard || D`, or an `Ite`-style
    // update) — fail-closed, never mis-denoted as a conjunction.
    match arm_value_rvalue_for(body, else_arm, target, param_index) {
        Some(SemRvalue::Use(SemOperand::Const(0))) => {}
        _ => return None,
    }

    // The THEN arm reifies the condition AS a value. Two accepted shapes:
    //   * LITERAL `true` — the `is_ascii_alphanumeric`-class literal-arm diamond
    //     (both comparisons are switches; the then arm just writes `true`): the
    //     guarded local denotes the guard `cond` itself.
    //   * Trust: COMPACT-CONJUNCTIVE DIAMOND (2026-07-18, Wave-D item 10/9) — a
    //     Bool-valued COMPARISON `D` (a bare `self <= hi` range bound, the
    //     `to_ascii_lowercase` diamond, or its `Ne(<cmp>, false)` bool-normalize,
    //     the `is_ascii_punctuation` compact diamond): here rustc keeps only the
    //     FIRST comparison as a `SwitchInt` and lowers the second as a plain rvalue
    //     in the then block, so `if guard { D } else { false } ≡ guard && D`. The
    //     result is `And(cond, <D as SemCondTree>)` — BYTE-IDENTICAL to the
    //     `SemRvalue` the two-switch literal-arm form produces (`cond_tree_to_rvalue`
    //     of the And-tree), so the whole-function certification is unchanged.
    // Anything else (an `Ite`-shaped arm value, an arithmetic value, a non-0/1
    // comparison) is a different recognizer's shape — fail-closed.
    match arm_value_rvalue_for(body, then_arm, target, param_index)? {
        SemRvalue::Use(SemOperand::Const(1)) => Some(cond),
        then_rv => {
            let d = sem_rvalue_to_cond_tree(&then_rv)?;
            Some(SemCondTree::And(Box::new(cond), Box::new(d)))
        }
    }
}

/// Trust: GUARDED-LOCAL layer — translate a recognized guard [`SemCondTree`] (the
/// `sem_conjunctive_chain`/[`sem_guarded_local_value`] output) into the EQUIVALENT
/// `SemRvalue` fragment, so a guarded-local's reified Bool value can be SPLICED into
/// an enclosing `Cmp`/`Or`/`And` tree exactly where it is read. `Leaf(c)` maps to the
/// SAME single comparison `Cmp c.op (Use c.a) (Use c.b)`; `And(l, r)` maps to the
/// PURE-ARITHMETIC `SemRvalue::And` (recursing) — REUSING the Bool-connective ctor
/// rather than adding a third parallel "Cond as Int" encoding (composition, not new
/// theory: a `Cond` and a Bool-valued `Rvalue` already denote the SAME thing,
/// `bool_as_int(eval_cond …)`, whichever constructor family reaches it).
pub(super) fn cond_tree_to_rvalue(cond: &SemCondTree) -> SemRvalue {
    match cond {
        SemCondTree::Leaf(c) => SemRvalue::Cmp(
            c.op,
            Box::new(SemRvalue::Use(c.a.clone())),
            Box::new(SemRvalue::Use(c.b.clone())),
        ),
        SemCondTree::And(l, r) => {
            SemRvalue::And(Box::new(cond_tree_to_rvalue(l)), Box::new(cond_tree_to_rvalue(r)))
        }
        // Trust: RANGE+DISJUNCTION guard — the `Or` twin, mapping to the existing
        // Bool-connective `SemRvalue::Or` (pure-arithmetic 0/1 encoding).
        SemCondTree::Or(l, r) => {
            SemRvalue::Or(Box::new(cond_tree_to_rvalue(l)), Box::new(cond_tree_to_rvalue(r)))
        }
        // Trust: ITER-NEXT VALUE-PATH — an `IterHasNext` guard has NO pure-arithmetic
        // `SemRvalue` denotation (it is an opaque dispatch head, not a comparison of two
        // Int operands). It is minted ONLY into a `SemAdtReturn.cond` (consumed by the
        // trust-ir witness's `cond_bool`) and is NEVER spliced as a guarded-local Bool
        // value through this converter, so this arm is structurally unreachable — a
        // reachable call would be a construction bug, not a forgeable input.
        SemCondTree::IterHasNext(_) => unreachable!(
            "SemCondTree::IterHasNext is minted only into a trust-ir SemAdtReturn.cond \
             (denoted by trustir_adt::cond_bool); it never reaches cond_tree_to_rvalue"
        ),
    }
}

/// Trust: COMPACT-CONJUNCTIVE DIAMOND (2026-07-18, Wave-D item 10/9) — the INVERSE
/// of [`cond_tree_to_rvalue`] over the Bool-valued rvalue fragment: recover the
/// [`SemCondTree`] a `SemRvalue` denotes, so a guarded-local THEN arm whose value is a
/// bare comparison (`_t := Le(self, hi)`, the `to_ascii_lowercase` diamond) or its
/// `!= false` bool-normalize (`_t := Ne(<cmp temp>, false)`, the `is_ascii_punctuation`
/// compact diamond) reifies to the SAME `Leaf`/`And`/`Or` tree the LITERAL-arm
/// conjunctive form would build. Faithfulness: this is `cond_tree_to_rvalue` run
/// backwards on exactly the shapes it produces, PLUS the identity `x != false ≡ x` /
/// `x == true ≡ x` on a Bool-valued `x` (a comparison is 0/1-valued, so dropping the
/// `Ne(_, 0)` / `Eq(_, 1)` wrapper preserves the value). Fail-closed (`None`) on any
/// rvalue outside `{Cmp(op, Use a, Use b), Ne(cond, false)/Eq(cond, true) normalize,
/// And, Or}` — an arithmetic value, a non-0/1 `Ne`/`Eq`, or a nested non-`Use` compare
/// side declines, never mis-denotes an integer as a Cond.
pub(super) fn sem_rvalue_to_cond_tree(rv: &SemRvalue) -> Option<SemCondTree> {
    match rv {
        // A flat comparison leaf `op (Use a) (Use b)` — the bare range-bound
        // `self <= hi` the compact diamond's then arm holds.
        SemRvalue::Cmp(op, ra, rb) => {
            // BOOL-NORMALIZE: `Ne(x, false)` / `Eq(x, true)` where `x` is itself a
            // Bool-valued cond ≡ `x` (a comparison is 0/1-valued). Try that FIRST so
            // the `is_ascii_punctuation` `Ne(<cmp>, false)` wrapper collapses.
            let is_false = |r: &SemRvalue| matches!(r, SemRvalue::Use(SemOperand::Const(0)));
            let is_true = |r: &SemRvalue| matches!(r, SemRvalue::Use(SemOperand::Const(1)));
            match op {
                SemCmpOp::Ne if is_false(rb) => return sem_rvalue_to_cond_tree(ra),
                SemCmpOp::Ne if is_false(ra) => return sem_rvalue_to_cond_tree(rb),
                SemCmpOp::Eq if is_true(rb) => return sem_rvalue_to_cond_tree(ra),
                SemCmpOp::Eq if is_true(ra) => return sem_rvalue_to_cond_tree(rb),
                _ => {}
            }
            // Otherwise it must be a flat comparison over two bare operands.
            let (SemRvalue::Use(a), SemRvalue::Use(b)) = (ra.as_ref(), rb.as_ref()) else {
                return None;
            };
            Some(SemCondTree::Leaf(SemCond { op: *op, a: a.clone(), b: b.clone() }))
        }
        SemRvalue::And(l, r) => Some(SemCondTree::And(
            Box::new(sem_rvalue_to_cond_tree(l)?),
            Box::new(sem_rvalue_to_cond_tree(r)?),
        )),
        SemRvalue::Or(l, r) => Some(SemCondTree::Or(
            Box::new(sem_rvalue_to_cond_tree(l)?),
            Box::new(sem_rvalue_to_cond_tree(r)?),
        )),
        _ => None, // arithmetic / Use / Sel / BitBin / ArithBin — not a Cond value.
    }
}

/// Map a Trust MIR comparison `BinOp` into the MirSem `SemCmpOp` fragment — the
/// integer comparison ops `Lt/Le/Eq/Ne/Gt/Ge` a guard's discriminant temp uses.
/// Each grounds to a Bool-valued, axiom-free `eval_cond` clause. `None` (fail-closed)
/// for any non-comparison binop (`Cmp` 3-way / arithmetic / bitwise are out of the
/// comparison fragment).
#[must_use]
pub fn sem_cmpop_of_mir(op: &trust_types::BinOp) -> Option<SemCmpOp> {
    use trust_types::BinOp;
    match op {
        BinOp::Lt => Some(SemCmpOp::Lt),
        BinOp::Le => Some(SemCmpOp::Le),
        BinOp::Eq => Some(SemCmpOp::Eq),
        BinOp::Ne => Some(SemCmpOp::Ne),
        BinOp::Gt => Some(SemCmpOp::Gt),
        BinOp::Ge => Some(SemCmpOp::Ge),
        _ => None,
    }
}
