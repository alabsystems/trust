// The pointer-spine call shape: a call whose argument reaches the callee
// through a chain of pointer projections. Admitting one requires the spine's
// definition to dominate the call, otherwise the argument the proof talks
// about is not the argument the call receives.

use super::*;

// ---------------------------------------------------------------------------
// Trust: PTR-INTRINSIC-PREFIX SPINE (real 3-call memchr lift, `arch::all::
// memchr::One::count`) — the CALL-RETURN shape [`sem_call_return_of_mir`]
// recognizes requires EXACTLY ONE `Terminator::Call` in the whole body (a
// "multi-call barrier"). The real memchr `One::count` is a PTR-INTRINSIC-
// PREFIXED call spine, not a general opaque multi-call:
//
//   bb0: _3 := Call(core::slice::<impl [T]>::as_ptr, [haystack])     // base ptr
//   bb1: _4 := Call(core::ptr::const_ptr::add, [_3, len(haystack)])  // end ptr
//   bb2: _0 := Call(arch::all::memchr::One::count_raw, [self, _3, _4]) // the LEAF
//   bb3: Return
//
// The two prefix calls are PTR-INTRINSICS the EXISTING ptr model
// (`clean_ground::resolve_ptr_model`/`ptr_offset_bounds_open`, from the
// `as_ptr`/`add`/`sub`/`offset`/`read` reflection) ALREADY handles — so this
// needs NO opaque ensures-forwarding (that is the separate, harder general
// multi-call shape, deliberately out of scope here). `sem_ptr_spine_call_
// return_of_mir` generalizes the single-call recognizer ADDITIVELY: a body
// with NO prefix calls is `sem_call_return_of_mir`'s own shape (recognized
// identically by construction), and every existing call site of
// `sem_call_return_of_mir` keeps calling it FIRST, falling back to this
// recognizer only when the single-call shape declines — so nothing already
// certified is renarrowed.
// ---------------------------------------------------------------------------
/// Trust: PTR-SPINE — convert a resolved pointer-arithmetic INDEX `Formula`
/// (the `index` field of a [`crate::reflect::PtrModel`]) into the EXISTING
/// `SemOperand` vocabulary, REUSING the `Index`/`Len` opaque carriers the
/// array-index leaf already grounds through (no new `SemOperand` variant, no
/// new axiom). `slice` is the model's own base-slice formula (for matching a
/// `slice_len` argument against the SAME slice) and `slice_sem` is the
/// already-built `SemOperand::Var` for that slice parameter.
///
/// Only the TRACTABLE index shapes the ptr-intrinsic model actually produces
/// for a `as_ptr` optionally followed by ONE more offset are recognized:
///   * `Int(k)`               → `Const(k)` (the `as_ptr` base, `k = 0`);
///   * `Add(Int(0), rest)` / `Add(rest, Int(0))` → recurse into `rest` (strip
///     the `as_ptr`-rooted base index's leading/trailing `+0`);
///   * `slice_len(SAME slice)` → `Len(slice_sem)` (the `add(as_ptr(s), s.len())`
///     end-pointer shape memchr's `One::count` uses).
/// Anything else (a free-parameter count, a DIFFERENT slice's length, a
/// multi-level composed offset) is OUTSIDE this tractable fragment and
/// returns `None` (fail-closed) — a named residue, not a silent absorption.
pub(super) fn formula_index_to_sem_operand(
    index: &trust_types::Formula,
    slice: &trust_types::Formula,
    slice_sem: &SemOperand,
) -> Option<SemOperand> {
    use trust_types::Formula as F;
    match index {
        F::Int(k) => Some(SemOperand::Const(*k)),
        F::Add(a, b) if matches!(a.as_ref(), F::Int(0)) => {
            formula_index_to_sem_operand(b, slice, slice_sem)
        }
        F::Add(a, b) if matches!(b.as_ref(), F::Int(0)) => {
            formula_index_to_sem_operand(a, slice, slice_sem)
        }
        F::Pred(name, args)
            if name.as_str() == "Trust.MirSem.slice_len"
                && args.len() == 1
                && &args[0] == slice =>
        {
            Some(SemOperand::Len(Box::new(slice_sem.clone())))
        }
        _ => None,
    }
}

/// Require a direct, stable parameter operand. The pointer model performs the
/// full type/deref-write validation; this site validator deliberately accepts
/// only the parameter-rooted shapes whose value cannot come from a later temp
/// definition.
pub(super) fn ptr_spine_stable_parameter_operand(
    body: &trust_types::VerifiableBody,
    op: &trust_types::Operand,
) -> bool {
    use trust_types::Operand;
    matches!(op,
        Operand::Copy(place) | Operand::Move(place)
            if place.projections.is_empty()
                && (1..=body.arg_count).contains(&place.local)
                && !param_reassigned_by_stmt(body, place.local))
}

/// Validate the definition of a pointer-spine count at the Call terminator
/// that consumes it. Constants and stable parameters are site-independent;
/// a temp must have one complete definition that dominates this exact Call and
/// must be one of the narrow count leaves understood by the pointer model.
pub(super) fn ptr_spine_count_definition_dominates(
    body: &trust_types::VerifiableBody,
    op: &trust_types::Operand,
    use_block: trust_types::BlockId,
) -> bool {
    use trust_types::{Operand, Rvalue, UnOp};
    match op {
        Operand::Constant(_) => true,
        Operand::Copy(place) | Operand::Move(place) if place.projections.is_empty() => {
            if (1..=body.arg_count).contains(&place.local) {
                return !param_reassigned_by_stmt(body, place.local);
            }
            let Some((_, _, definition)) =
                unique_local_definition_dominating(body, place.local, use_block, None)
            else {
                return false;
            };
            match definition {
                Rvalue::UnaryOp(UnOp::PtrMetadata, slice) => {
                    ptr_spine_stable_parameter_operand(body, slice)
                }
                Rvalue::Len(slice) => {
                    slice.projections.is_empty()
                        && (1..=body.arg_count).contains(&slice.local)
                        && !param_reassigned_by_stmt(body, slice.local)
                }
                Rvalue::Use(inner) => {
                    matches!(inner, Operand::Constant(_))
                        || ptr_spine_stable_parameter_operand(body, inner)
                }
                _ => false,
            }
        }
        _ => false,
    }
}

/// Validate that `local` is produced by one safe pointer-arithmetic Call whose
/// result dominates `use_block`, recursively applying the same condition to
/// its base pointer. This closes the block-order-first gap in
/// `clean_ground::resolve_ptr_model` without broadening that shared resolver:
/// only after this exact-site proof succeeds do we ask it for the value model.
pub(super) fn ptr_spine_definition_dominates(
    body: &trust_types::VerifiableBody,
    local: usize,
    use_block: trust_types::BlockId,
    visited: &mut std::collections::HashSet<usize>,
    depth: usize,
) -> bool {
    use trust_types::{Operand, Terminator};

    if depth > 64 || (1..=body.arg_count).contains(&local) || !visited.insert(local) {
        return false;
    }
    let valid = (|| {
        let (assignments, call_blocks) = call_family_local_writes(body, local)?;
        // Trust: W2 reflection — a `Rvalue::PtrOffset`-defined base pointer (exactly one
        // `Statement::Assign`, NO ptr-intrinsic Call dest): the extracted `BinOp::Offset`
        // spelling of `ptr::offset(base, count)`. Validate its base + count with the SAME
        // exact-site discipline as the `ptr::offset` Call arm below, so the spine admits a
        // BinOp-spelled `end` pointer IDENTICALLY to the intrinsic-spelled one (`resolve_
        // ptr_model`/`ptr_offset_bounds_open` — consulted by the caller — already converge
        // the two spellings onto one model).
        if call_blocks.is_empty() && assignments == 1 {
            let (definition_block, _definition_statement, rvalue) =
                unique_local_definition_dominating(body, local, use_block, None)?;
            let trust_types::Rvalue::PtrOffset { ptr, count } = rvalue else { return None };
            let (Operand::Copy(base_place) | Operand::Move(base_place)) = ptr else {
                return None;
            };
            return (base_place.projections.is_empty()
                && ptr_spine_count_definition_dominates(body, count, definition_block)
                && ptr_spine_definition_dominates(
                    body,
                    base_place.local,
                    definition_block,
                    visited,
                    depth + 1,
                ))
            .then_some(());
        }
        let [definition_block] = call_blocks.as_slice() else { return None };
        if assignments != 0
            || *definition_block == use_block
            || !block_dominates(body, *definition_block, use_block)
        {
            return None;
        }
        let block = body.blocks.iter().find(|block| block.id == *definition_block)?;
        let Terminator::Call {
            func,
            args,
            dest,
            target: Some(_),
            atomic,
            is_foreign,
            is_unsafe_sig,
            ..
        } = &block.terminator
        else {
            return None;
        };
        if dest.local != local
            || !dest.projections.is_empty()
            || atomic.is_some()
            || *is_foreign
            || *is_unsafe_sig
        {
            return None;
        }
        match crate::reflect::PtrArith::classify(func)? {
            crate::reflect::PtrArith::AsPtr => {
                let [slice] = args.as_slice() else { return None };
                ptr_spine_stable_parameter_operand(body, slice).then_some(())
            }
            crate::reflect::PtrArith::Add
            | crate::reflect::PtrArith::Sub
            | crate::reflect::PtrArith::Offset => {
                let [base, count] = args.as_slice() else { return None };
                let (Operand::Copy(base_place) | Operand::Move(base_place)) = base else {
                    return None;
                };
                if !base_place.projections.is_empty()
                    || !ptr_spine_count_definition_dominates(body, count, *definition_block)
                    || !ptr_spine_definition_dominates(
                        body,
                        base_place.local,
                        *definition_block,
                        visited,
                        depth + 1,
                    )
                {
                    return None;
                }
                Some(())
            }
            crate::reflect::PtrArith::Read => None,
        }
    })()
    .is_some();
    visited.remove(&local);
    valid
}

/// Trust: PTR-SPINE — resolve a CALL-SITE actual argument that is itself a
/// PTR-INTRINSIC-DERIVED pointer temp (the `start`/`end` arguments memchr's
/// `One::count` passes to the certified `count_raw` leaf) to the EXISTING
/// `SemOperand::Index` opaque carrier: `Index(Var(slice_param), index)`.
///
/// FAIL-CLOSED gate (every clause required, `None` on any miss):
///   * the operand is a bare `Copy`/`Move` of an UNPROJECTED place (a
///     projected place is outside this fragment);
///   * [`crate::clean_ground::resolve_ptr_model`] resolves that local to a
///     `(slice, index)` model AT ALL (a non-ptr-intrinsic-derived local
///     declines — this is the recognizer's OWN gate: internally it only ever
///     chases through `Terminator::Call`s the `PtrArith` allowlist admits);
///   * the model's `slice` is rooted at a bare PARAMETER (`Formula::Var`),
///     resolved back to its param index;
///   * the in-bounds OFFSET VC is PROVABLE
///     ([`crate::clean_ground::ptr_offset_bounds_open`] `== Some(true)`) — an
///     unbounded/unproven offset (the model's OWN fail-closed bounds
///     discipline) declines rather than silently certifying an out-of-bounds
///     pointer argument;
///   * the model's `index` is one of the tractable shapes
///     [`formula_index_to_sem_operand`] represents.
pub(super) fn sem_ptr_spine_arg_operand(
    body: &trust_types::VerifiableBody,
    op: &trust_types::Operand,
    use_block: trust_types::BlockId,
    param_index: &dyn Fn(usize) -> Option<u64>,
) -> Option<SemOperand> {
    use trust_types::{Formula as F, Operand};
    let (Operand::Copy(p) | Operand::Move(p)) = op else { return None };
    if !p.projections.is_empty() {
        return None;
    }
    if !ptr_spine_definition_dominates(
        body,
        p.local,
        use_block,
        &mut std::collections::HashSet::new(),
        0,
    ) {
        return None;
    }
    let model = crate::clean_ground::resolve_ptr_model(body, p.local)?;
    // FAIL-CLOSED bounds gate: only a PROVABLY in-bounds ptr-intrinsic chain is
    // admitted as a certified-callee argument — never silently absorb an
    // unbounded/unproven pointer offset (mirrors the ptr-intrinsic model's own
    // fail-closed discipline, `ptr_offset_bounds_open`'s doc).
    if crate::clean_ground::ptr_offset_bounds_open(body, p.local) != Some(true) {
        return None;
    }
    let F::Var(name, _) = &model.slice else { return None };
    let slice_local = body.locals.iter().position(|l| l.name.as_deref() == Some(name.as_str()))?;
    let slice_idx = param_index(slice_local)?;
    let slice_sem = SemOperand::Var(slice_idx);
    let index_sem = formula_index_to_sem_operand(&model.index, &model.slice, &slice_sem)?;
    Some(SemOperand::Index(Box::new(slice_sem), Box::new(index_sem)))
}

/// Trust: PTR-SPINE — resolve a certified-callee CALL-SITE actual argument:
/// [`sem_call_arg_operand`] (bare param/const, or the existing field-read
/// chase — BYTE-IDENTICAL, tried first) OR, when that declines, the
/// ptr-intrinsic-derived pointer argument ([`sem_ptr_spine_arg_operand`]).
pub(super) fn sem_ptr_spine_call_arg_operand(
    body: &trust_types::VerifiableBody,
    op: &trust_types::Operand,
    use_block: trust_types::BlockId,
    param_index: &dyn Fn(usize) -> Option<u64>,
) -> Option<SemOperand> {
    sem_call_arg_operand(body, op, use_block, param_index)
        .or_else(|| sem_ptr_spine_arg_operand(body, op, use_block, param_index))
}

/// Trust: PTR-SPINE — generalize [`sem_call_return_of_mir`] to admit a body
/// whose call-return spine is preceded by ZERO-OR-MORE `Terminator::Call`s to
/// the pointer-arithmetic INTRINSIC allowlist (`as_ptr`/`add`/`sub`/`offset` —
/// [`crate::reflect::PtrArith`], via `PtrArith::classify(..).is_offset()`;
/// `read` is EXCLUDED — it produces an element, not a pointer, so it can never
/// be a prefix step here) before the SOLE call to a certified registry
/// callee. This is exactly the composition the real memchr `One::count` needs
/// — see the module doc above.
///
/// The admitted shape (fail-closed on everything else, mirroring
/// [`sem_call_return_of_mir`] clause-for-clause with the prefix generalized):
///   * no `Unsupported` statement anywhere in the body;
///   * EVERY `Terminator::Call` in the body is EITHER (a) a ptr-arithmetic-
///     intrinsic OFFSET call (kept scanning — NOT the final call), OR (b) THE
///     SOLE non-ptr-intrinsic call. A SECOND non-ptr-intrinsic call is a
///     genuine opaque intermediate call — the general multi-call shape,
///     deliberately out of scope — and DECLINES THE WHOLE SHAPE; a `read`
///     intrinsic prefix ALSO declines (it is not offset-producing).
///     Every OTHER terminator (anything but `Call`/`Goto`/`Return`) declines.
///   * the sole non-ptr-intrinsic call is a direct, non-foreign, non-atomic
///     call with a live target and a bare-local integer/bool destination,
///     resolves in the certified registry (not self-recursive), and its
///     arity matches;
///   * EVERY actual argument resolves via [`sem_ptr_spine_call_arg_operand`]
///     (bare param/const, the field-read chase, OR a ptr-intrinsic-derived
///     pointer reflected via the EXISTING `SemOperand::Index` carrier), and
///     there is at least one;
///   * the return spine is linear (Goto-only to a UNIQUE `Return` block) and
///     the sole-writer discipline holds on the returned value — BYTE-
///     IDENTICAL to `sem_call_return_of_mir`.
///
/// `pub(crate)` — mirrors `sem_call_return_of_mir`'s Seam B discipline: a
/// trust-ir via-path may reuse this recognizer SHAPE-ONLY (its own kernel
/// evidence is the trust-ir `callReturnInstance`, not a MirSem certificate).
pub(crate) fn sem_ptr_spine_call_return_of_mir(
    func: &trust_types::VerifiableFunction,
    callees: &std::collections::BTreeMap<String, CalleeFact>,
) -> Option<SemCallReturn> {
    use trust_types::{Operand, Rvalue, Statement, Terminator, Ty};

    use crate::reflect::PtrArith;
    if callees.is_empty() {
        return None; // no certified callee ⇒ the shape can never be admitted.
    }
    let body = &func.body;
    let arg_count = body.arg_count;
    let param_index = move |local: usize| -> Option<u64> {
        if (1..=arg_count).contains(&local) { u64::try_from(local - 1).ok() } else { None }
    };
    let local_is_int = |local: usize| -> bool {
        matches!(body.locals.get(local).map(|l| &l.ty), Some(Ty::Int { .. }))
    };
    let local_is_int_or_bool = |local: usize| -> bool {
        local_is_int(local) || matches!(body.locals.get(local).map(|l| &l.ty), Some(Ty::Bool))
    };

    // Any `Unsupported` statement anywhere ⇒ unmodeled semantics ⇒ fail closed.
    if body.blocks.iter().flat_map(|b| &b.stmts).any(|s| matches!(s, Statement::Unsupported { .. }))
    {
        return None;
    }

    // Partition every Call terminator: ptr-intrinsic OFFSET prefix calls (kept
    // scanning, never the final call) vs the SOLE non-ptr-intrinsic call (the
    // certified-callee candidate). A `read` prefix, or a SECOND non-ptr-
    // intrinsic call, fails the whole shape closed.
    let mut call = None;
    for block in &body.blocks {
        match &block.terminator {
            Terminator::Call {
                func: callee,
                args,
                dest,
                target,
                atomic,
                is_foreign,
                is_unsafe_sig,
                ..
            } => {
                if *is_foreign || atomic.is_some() || *is_unsafe_sig || target.is_none() {
                    return None;
                }
                if let Some(op) = PtrArith::classify(callee) {
                    if !op.is_offset() {
                        return None; // a `read` (or any non-offset op) prefix — declines.
                    }
                    continue; // a ptr-intrinsic prefix call — keep scanning.
                }
                if call.is_some() {
                    return None; // a SECOND non-ptr-intrinsic call — general multi-call, out of scope.
                }
                call = Some((
                    block.id,
                    callee,
                    args,
                    dest,
                    *target,
                    atomic,
                    *is_foreign,
                    *is_unsafe_sig,
                ));
            }
            Terminator::Goto(_) | Terminator::Return => {}
            _ => return None, // any other terminator ⇒ outside the modeled spine.
        }
    }
    let (call_block_id, callee_str, args, dest, target, atomic, is_foreign, is_unsafe_sig) = call?;

    // ABI fail-closes: foreign / atomic / diverging (no return target).
    if is_foreign || atomic.is_some() || is_unsafe_sig {
        return None;
    }
    let target = target?;

    // Trust: ENTRY-REACHABILITY — the certified-callee Call block must be
    // REACHABLE from the entry block `BlockId(0)` along the happy path: Gotos and
    // the ptr-intrinsic PREFIX calls' own targets (as_ptr/add before the leaf).
    // A diverging entry with an UNREACHABLE Call+Return island otherwise
    // certifies a call that never runs — fail closed (mirror
    // `sem_call_op_call_of_mir`'s `BlockId(0)` walk).
    {
        let mut cur = trust_types::BlockId(0);
        let mut steps = 0usize;
        while cur != call_block_id {
            let blk = body.blocks.iter().find(|b| b.id == cur)?;
            match &blk.terminator {
                Terminator::Goto(g) => cur = *g,
                // A ptr-intrinsic prefix call on the happy path — follow its
                // return target toward the certified call (a diverging prefix
                // call has no continuation, so the leaf is unreachable).
                Terminator::Call { target, .. } => cur = (*target)?,
                _ => return None, // Return/other before the certified call — unreachable.
            }
            steps += 1;
            if steps > body.blocks.len() {
                return None; // cycle before the call — unreachable happy path.
            }
        }
    }
    // Dest must be a BARE local of integer (or Bool) type.
    if !dest.projections.is_empty() || !local_is_int_or_bool(dest.local) || !local_is_int_or_bool(0)
    {
        return None;
    }

    // Resolve the callee in the certified registry (exact / UNIQUE suffix).
    let (resolved, fact, callee_id) = resolve_certified_callee(callees, callee_str)?;
    // Self-recursion fails closed (by def-path AND by resolution).
    if resolved == func.def_path || *callee_str == func.def_path {
        return None;
    }
    // Arity must match the certified callee's declared parameter count.
    if fact.arg_count != args.len() {
        return None;
    }

    // EVERY actual argument must resolve via the ptr-spine arg fragment; at least one.
    if args.is_empty() {
        return None;
    }
    let mut sem_args = Vec::with_capacity(args.len());
    for a in args {
        sem_args.push(sem_ptr_spine_call_arg_operand(body, a, call_block_id, &param_index)?);
    }

    // The UNIQUE Return block.
    let mut rets = body.blocks.iter().filter(|b| matches!(b.terminator, Terminator::Return));
    let ret_block = rets.next()?;
    if rets.next().is_some() {
        return None;
    }
    // The call's continuation reaches the Return block through Gotos ONLY.
    let mut cur = target;
    let mut steps = 0usize;
    while cur != ret_block.id {
        let blk = body.blocks.iter().find(|b| b.id == cur)?;
        match &blk.terminator {
            Terminator::Goto(t) => cur = *t,
            _ => return None,
        }
        steps += 1;
        if steps > body.blocks.len() {
            return None; // cycle — not a linear return spine.
        }
    }

    // SOLE-WRITER discipline on the returned value.
    if dest.local == 0 {
        if !call_family_local_writes_exact(body, 0, 0, &[call_block_id]) {
            return None;
        }
    } else {
        let t = dest.local;
        if param_index(t).is_some() {
            return None; // a call overwriting a parameter place — unmodeled.
        }
        if !call_family_local_writes_exact(body, 0, 1, &[])
            || !call_family_local_writes_exact(body, t, 0, &[call_block_id])
        {
            return None;
        }
        let last_to_0 = ret_block
            .stmts
            .iter()
            .rev()
            .find_map(|s| crate::assignment_types::assigned_local_rvalue(body, s, 0))?;
        match last_to_0 {
            Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
                if p.local == t && p.projections.is_empty() => {}
            _ => return None,
        }
    }

    Some(SemCallReturn { callee: resolved.to_string(), callee_id, args: sem_args })
}
