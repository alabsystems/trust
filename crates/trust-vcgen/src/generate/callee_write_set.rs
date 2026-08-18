// Callee EFFECT SUMMARIES (write-sets) derived from the callee's OWN MIR.
//
// WHY THIS EXISTS
// ===============
// `terminator_def_names`'s `Call` arm havocs every mutably-borrowed and every
// mut-pointer-carrying local of the caller, by BASE name. For a `&mut self`
// method that is the single name `self`, and `place_names_overlap` makes that
// name a projection ANCESTOR of every field spelling (`self*.0.0`, `self*.1`,
// …). So ONE call to ANY helper erases every field fact the body established:
//
//     pub fn close(&mut self) ensures !self.storage.flag {
//         self.storage.flag = false;   // pins `self*.0.0 == false`
//         self.bump();                 // conservative havoc kills `self*.0.0`
//     }
//
// The postcondition's read of `self*.0.0` at the exit block then carries the
// call's version token while the establishing store carries the statement's,
// no conjunct pins the name the obligation reads, and the P0 multi-write
// tripwire in `contract_vcs` correctly refuses to emit a refutable query over
// a free post-state — the visible `SpecUnverifiable` row. Measured on the
// repro above with the shipping stage2 toolchain: `requested=3, proved=0,
// unknown=1, unsupported=2`. Delete the `self.bump()` line and the same
// function is `3 proved`.
//
// That is the whole "no method that calls anything can be proved" blocker: the
// property does not need to see INSIDE the callee, it needs ONE fact about it
// — that the callee does not write `self.storage.flag`.
//
// WHAT THIS LANE DOES
// ===================
// A callee can only reach caller memory through its ARGUMENTS. So its
// caller-visible effect is a set of projection paths off its FORMALS. This
// module DERIVES that set from the callee's own extracted body — the summary
// database already carries it (`FunctionSummary::extracted_body`, attached by
// the compiler's `extracted_callee_body_for_tracing` for every non-generic
// local callee with MIR) — and the call site havocs the MAPPED paths instead
// of the receiver's base name.
//
// SOUNDNESS DISCIPLINE — read this before touching anything here
// ==============================================================
// Shrinking a havoc set is the FALSE-PROVE direction: a name that stops being
// re-versioned lets a stale fact survive and vacuously discharge a real
// obligation. Three structural properties keep this lane safe:
//
//  1. DERIVED, NEVER DECLARED. The write-set comes from the callee's MIR, not
//     from a user annotation. There is no syntax by which a user can assert
//     "I write nothing" and be believed. An absent body is not an empty
//     write-set — it is `None`, which means "conservative havoc".
//
//  2. TOTAL AND FAIL-CLOSED. `derive_callee_write_set` enumerates EVERY
//     statement and EVERY terminator of the callee and returns `None` the
//     moment it meets anything it cannot classify — a `Drop` (drop glue runs
//     arbitrary user code with `&mut` access), an `Opaque` terminator, any
//     `&mut`/`&raw` borrow, any raw-pointer cast, any `Unsupported` sentinel,
//     a nested call whose arguments are not provably pointer-free, a
//     deref-rooted store through a local, or a write path whose formal is not
//     a plain `&mut`. `None` restores the existing conservative behaviour
//     EXACTLY — the refinement is a pure narrowing of an over-approximation,
//     applied only where the narrowing is proved.
//
//  3. ROOT-PRESERVING AT THE CALL SITE. The refinement never DROPS a
//     conservative havoc root. It REPLACES the roots that are this call's own
//     argument places with the precise paths the callee writes, and keeps
//     every OTHER conservative name (unrelated `&mut` locals, other
//     mut-pointer locals, the call destination) fully havoced. So a caller
//     local that ALIASES into the receiver is still killed wholesale through
//     its own name, and only the receiver's own untouched sibling fields
//     survive — which is exactly the fact the property needs and exactly the
//     fact the callee provably did not disturb.
//
// The negative direction is load-bearing and tested: a helper that DOES write
// the flagged field contributes that field's path, the call havocs it, the pin
// dies, and the postcondition does NOT prove. A summary lane that makes
// everything prove is worthless; this one must keep refuting.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use super::*;

/// One caller-visible write of a callee: a FORMAL parameter index (`1..=arg_count`)
/// plus the projection chain the callee applies to it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct CalleeWritePath {
    /// Formal parameter local index (MIR locals `1..=arg_count`).
    pub(crate) formal: usize,
    /// Projections applied to that formal. For a `&mut` formal this ALWAYS
    /// starts with `Deref` (enforced by [`derive_callee_write_set`]).
    pub(crate) projections: Vec<Projection>,
}

/// The complete set of caller-visible places a callee may write.
///
/// Only ever constructed by [`derive_callee_write_set`] from a callee's own
/// extracted MIR. There is deliberately no constructor that takes a
/// user-declared clause: an unverified assertion about what a callee writes
/// would license a false PROVE.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct CalleeWriteSet {
    pub(crate) paths: Vec<CalleeWritePath>,
}

/// Max nesting for the callee-body walk. Nested calls are admitted only when
/// their arguments are provably pointer-free (see
/// [`nested_call_cannot_reach_caller_memory`]), so no recursion into a nested
/// callee's body is performed; the constant exists to keep the walk's cost
/// explicitly bounded and to document that this lane is depth-1 by design.
const WRITE_SET_MAX_BLOCKS: usize = 512;

/// True iff `local` is a formal parameter of `func` (MIR locals `1..=arg_count`).
fn is_formal(func: &VerifiableFunction, local: usize) -> bool {
    local >= 1 && local <= func.body.arg_count
}

/// True iff a nested call inside a callee body provably cannot reach ANY caller
/// memory: every argument is a constant, or a `Copy`/`Move` of a place whose
/// type is a PURE VALUE (`ty_is_pure_value` — a scalar or an aggregate of
/// scalars with no reference/raw-pointer/opaque component anywhere).
///
/// This is the same reasoning `terminator_def_names`'s `args_cannot_reach_locals`
/// fast path already relies on, restated for the nested position: a callee
/// handed only pointer-free values has no channel to the CALLER-of-our-callee's
/// memory either, so it contributes nothing to our callee's caller-visible
/// write-set beyond the destination place (which the walk records separately).
///
/// `Move` is admitted here (unlike the caller-side fast path, which conservatively
/// excludes it) ONLY because the operand's TYPE is separately required to be a
/// pure value: moving a scalar transfers no ownership of anything that points
/// anywhere. Every non-pure type — including every `Adt`, whose extracted fields
/// are ERASED for opaque std types — is rejected.
fn nested_call_cannot_reach_caller_memory(callee: &VerifiableFunction, args: &[Operand]) -> bool {
    args.iter().all(|a| match a {
        Operand::Constant(_) => true,
        Operand::Copy(p) | Operand::Move(p) => {
            matches!(crate::place_ty_cow(callee, p).as_deref(), Some(ty) if ty_is_pure_value(ty))
        }
        // Symbolic / Unsupported operands carry unknown provenance.
        _ => false,
    })
}

/// Classify one written place inside a callee body.
///
/// `Some(Some(path))` — the write is caller-visible through formal `path.formal`.
/// `Some(None)`       — the write is provably CALLER-INVISIBLE (a local temp).
/// `None`             — unclassifiable; the whole derivation must fail closed.
fn classify_write_place(
    callee: &VerifiableFunction,
    place: &Place,
) -> Option<Option<CalleeWritePath>> {
    if is_formal(callee, place.local) {
        // A write rooted at a formal. The formal's declared type decides whether
        // it can reach caller memory at all.
        let ty = crate::local_ty_ref(callee, place.local)?;
        match ty {
            // A plain `&mut T`: the write reaches the caller iff it goes THROUGH
            // the reference, i.e. the projection chain starts with `Deref`.
            // A write to the reference VARIABLE itself (`formal = &mut other`,
            // projections empty) reseats the callee's own binding and is
            // invisible to the caller.
            Ty::Ref { mutable: true, inner } => {
                if place.projections.is_empty() {
                    return Some(None);
                }
                if place.projections.first() != Some(&Projection::Deref) {
                    // A non-Deref-leading projection of a reference is not a
                    // shape this lane models.
                    return None;
                }
                // A `Deref` ANYWHERE past position 0 means the callee wrote
                // through a pointer NESTED in the receiver (`(*self).ptr` is a
                // `&mut u32`; `*((*self).ptr) = v`). The pointee is an arbitrary
                // caller local this lane cannot name, so a name-based havoc of
                // `self*.ptr*` would leave a fact about the real referent stale.
                // Fail closed.
                if place.projections[1..].contains(&Projection::Deref) {
                    return None;
                }
                // Belt-and-braces: refuse when the pointee type itself carries a
                // mutable/raw pointer, so a future widening of the fragment
                // cannot silently admit the nested-pointer vector above.
                if ty_contains_mut_pointer(inner) {
                    return None;
                }
                // Only NAMED-FIELD / variant projections are admitted past the
                // deref. An `Index`/`ConstantIndex`/`Subslice` renders to an
                // element spelling whose aliasing rules (`place_names_overlap`'s
                // symbolic-index union) are subtler than this lane needs, and
                // `OpaqueCast`/`UnwrapUnsafeBinder` carry a type payload whose
                // rendering is not a place at all. Refuse rather than mint a
                // name whose overlap behaviour has not been established here.
                if !place.projections[1..]
                    .iter()
                    .all(|p| matches!(p, Projection::Field(_) | Projection::Downcast(_)))
                {
                    return None;
                }
                Some(Some(CalleeWritePath {
                    formal: place.local,
                    projections: place.projections.clone(),
                }))
            }
            // A by-value formal of a PURE VALUE type holds no pointer, so no
            // write to it (or into it) can reach caller memory.
            ty if ty_is_pure_value(ty) => Some(None),
            // Everything else — shared refs (interior mutability), raw pointers,
            // by-value aggregates that may nest a `&mut`, opaque std types whose
            // extracted fields are erased — is not modeled here.
            _ => None,
        }
    } else {
        // A write rooted at a NON-formal local.
        let ty = crate::local_ty_ref(callee, place.local)?;
        // A store THROUGH a local (`*p = v`) mutates the pointee, which may be
        // caller memory reached via some formal. Resolving that alias is exactly
        // the analysis this lane does not attempt: fail closed.
        if place.projections.first() == Some(&Projection::Deref) {
            return None;
        }
        // Otherwise the write lands in the callee's own frame slot. That is
        // invisible to the caller REGARDLESS of the local's type: writing a
        // pointer variable reseats the pointer, it does not write the pointee.
        let _ = ty;
        Some(None)
    }
}

/// Derive the caller-visible write-set of `callee` from its OWN extracted MIR,
/// or `None` when any construct falls outside the modeled fragment.
///
/// `None` is not "writes nothing" — it is "unknown", and every consumer must
/// respond by keeping the full conservative havoc.
///
/// THE ACCEPTED FRAGMENT (everything else fails closed):
///   * no `Drop` and no `Opaque` terminator anywhere (both run arbitrary code);
///   * no pointer laundering (`&raw`, raw-pointer cast, `Unsupported` rvalue)
///     — checked whole-body by [`func_has_pointer_laundering`];
///   * no `Rvalue::Ref { mutable: true, .. }` and no `Rvalue::AddressOf`
///     anywhere, so no `&mut` alias into a formal exists to be written through
///     out of sight of the place-rooted scan;
///   * every nested `Call` passes only provably pointer-free arguments;
///   * every written place classifies under [`classify_write_place`];
///   * only statement kinds with a known write effect appear.
pub(crate) fn derive_callee_write_set(callee: &VerifiableFunction) -> Option<CalleeWriteSet> {
    if callee.body.blocks.len() > WRITE_SET_MAX_BLOCKS {
        return None;
    }
    // Any laundering site anywhere in the body can smuggle a formal's address
    // through an integer and write it back later, invisibly to the place scan.
    if func_has_pointer_laundering(callee) {
        return None;
    }

    let mut paths: Vec<CalleeWritePath> = Vec::new();
    let record = |p: Option<CalleeWritePath>, paths: &mut Vec<CalleeWritePath>| {
        if let Some(path) = p
            && !paths.contains(&path)
        {
            paths.push(path);
        }
    };

    for block in &callee.body.blocks {
        for stmt in &block.stmts {
            match stmt {
                Statement::Assign { place, rvalue, .. } => {
                    // A mutable borrow / raw address creates an alias whose
                    // later deref-store is not rooted at the borrowed place.
                    // The fragment excludes them outright.
                    match rvalue {
                        Rvalue::Ref { mutable: true, .. } | Rvalue::AddressOf(..) => return None,
                        Rvalue::Unsupported { .. } => return None,
                        Rvalue::Cast(_, Ty::RawPtr { .. }) => return None,
                        _ => {}
                    }
                    record(classify_write_place(callee, place)?, &mut paths);
                }
                Statement::SetDiscriminant { place, .. }
                | Statement::Deinit { place }
                | Statement::Retag { place } => {
                    record(classify_write_place(callee, place)?, &mut paths);
                }
                // No place value changes.
                Statement::StorageLive(_)
                | Statement::StorageDead(_)
                | Statement::PlaceMention(_)
                | Statement::Coverage
                | Statement::ConstEvalCounter
                | Statement::Nop => {}
                // An intrinsic's write effect is not enumerated here, and an
                // `Unsupported` statement is unknown by construction.
                Statement::Intrinsic { .. } | Statement::Unsupported { .. } => return None,
                // `Statement` is `#[non_exhaustive]`: a variant added later must
                // fail closed rather than be silently treated as effect-free.
                _ => return None,
            }
        }

        match &block.terminator {
            Terminator::Call { args, dest, atomic, .. } => {
                // An atomic RMW carries its OWN written place (`atomic.place`)
                // beside the call destination. Rather than model a second write
                // channel here, refuse: an atomic in a callee is rare and the
                // conservative havoc is always available.
                if atomic.is_some() {
                    return None;
                }
                if !nested_call_cannot_reach_caller_memory(callee, args) {
                    return None;
                }
                record(classify_write_place(callee, dest)?, &mut paths);
            }
            // Drop glue and opaque terminators run arbitrary user code with
            // `&mut` access — the confirmed false-accept vector the conservative
            // havoc exists to close. Never narrow past them.
            Terminator::Drop { .. } | Terminator::Opaque { .. } => return None,
            Terminator::Goto { .. }
            | Terminator::SwitchInt { .. }
            | Terminator::Assert { .. }
            | Terminator::Return
            | Terminator::Unreachable
            | Terminator::Resume => {}
            _ => return None,
        }
    }

    Some(CalleeWriteSet { paths })
}

/// Derive a write-set for every summary in `summaries` that carries an extracted
/// callee body. Callees WITHOUT a body are simply absent from the map, which the
/// call site reads as "unknown" (conservative havoc).
pub(crate) fn build_callee_write_sets(
    summaries: &crate::modular::SummaryDatabase,
) -> FxHashMap<String, CalleeWriteSet> {
    let mut map = FxHashMap::default();
    if summaries.is_empty() {
        return map;
    }
    for name in summaries.names() {
        let Some(summary) = summaries.get(name) else { continue };
        let Some(body) = summary.extracted_body.as_deref() else { continue };
        if let Some(ws) = derive_callee_write_set(body) {
            map.insert(name.to_string(), ws);
        }
    }
    map
}

// ======================================================================
// Dynamically scoped registry
// ======================================================================
//
// `terminator_def_names(func, block)` is consumed by a dozen internal lanes
// (path definitions, block-entry versions, guard threading, abstract interp,
// callsite precondition VCs). Threading the summary database through all of
// them would fork the havoc oracle across lanes, which is the one thing that
// must not happen — the version MINT and the fact KILL have to agree by
// construction. So the derived map is installed once per generation entry on a
// dynamically scoped, unwind-safe stack, exactly as `VcgenContext` is (see
// its doc comment: "threading it through every internal visitor would add
// hundreds of plumbing parameters").
//
// The map is keyed by CALLEE NAME and is therefore caller-independent; every
// caller-specific gate is re-evaluated at the use site against the `func`
// actually being analysed. An absent scope yields `None` everywhere, which is
// the pre-existing conservative behaviour.

thread_local! {
    static CALLEE_WRITE_SET_STACK: std::cell::RefCell<Vec<WriteSetFrame>> =
        const { std::cell::RefCell::new(Vec::new()) };
    static CALLEE_WRITE_SET_NEXT_ID: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

struct WriteSetFrame {
    id: u64,
    map: std::rc::Rc<FxHashMap<String, CalleeWriteSet>>,
}

/// RAII scope for an installed write-set map. Removes exactly the frame it owns,
/// on normal return AND on unwind (mirrors `VcgenContextGuard`).
pub(crate) struct CalleeWriteSetGuard {
    frame_id: u64,
    _thread_affine: std::marker::PhantomData<std::rc::Rc<()>>,
}

impl Drop for CalleeWriteSetGuard {
    fn drop(&mut self) {
        let _ = CALLEE_WRITE_SET_STACK.try_with(|stack| {
            let mut stack = stack.borrow_mut();
            if let Some(index) = stack.iter().rposition(|frame| frame.id == self.frame_id) {
                stack.remove(index);
            }
        });
    }
}

/// Install the write-sets derived from `summaries` for the duration of the
/// returned guard. `None` summaries install an EMPTY map, which is
/// indistinguishable from no scope at all (every lookup misses ⇒ conservative).
pub(crate) fn enter_callee_write_sets(
    summaries: Option<&crate::modular::SummaryDatabase>,
) -> CalleeWriteSetGuard {
    let map = summaries.map(build_callee_write_sets).unwrap_or_default();
    let frame_id = CALLEE_WRITE_SET_NEXT_ID.with(|next| {
        let id = next.get();
        next.set(id.wrapping_add(1));
        id
    });
    CALLEE_WRITE_SET_STACK
        .with(|stack| stack.borrow_mut().push(WriteSetFrame { id: frame_id, map: std::rc::Rc::new(map) }));
    CalleeWriteSetGuard { frame_id, _thread_affine: std::marker::PhantomData }
}

/// Test-only installer taking an explicit map (unit tests reach helpers that no
/// public generation entry can drive directly).
#[cfg(test)]
pub(crate) fn enter_test_callee_write_sets(
    map: FxHashMap<String, CalleeWriteSet>,
) -> CalleeWriteSetGuard {
    let frame_id = CALLEE_WRITE_SET_NEXT_ID.with(|next| {
        let id = next.get();
        next.set(id.wrapping_add(1));
        id
    });
    CALLEE_WRITE_SET_STACK
        .with(|stack| stack.borrow_mut().push(WriteSetFrame { id: frame_id, map: std::rc::Rc::new(map) }));
    CalleeWriteSetGuard { frame_id, _thread_affine: std::marker::PhantomData }
}

/// The installed write-set for `callee`, or `None` (⇒ conservative havoc).
fn installed_write_set(callee: &str) -> Option<CalleeWriteSet> {
    CALLEE_WRITE_SET_STACK.with(|stack| {
        let stack = stack.borrow();
        stack.last()?.map.get(callee).cloned()
    })
}

// ======================================================================
// Call-site refinement
// ======================================================================

/// True iff the CALLER body admits name-based place reasoning across a call:
/// no pointer laundering (`&raw`, raw-pointer cast, `Unsupported` rvalue) and no
/// local whose type transitively carries a RAW pointer.
///
/// Without this, two caller locals could denote the same storage without either
/// being a `&mut` (Rust's uniqueness rule covers `&mut`, not raw pointers), so
/// havocing the argument's own spelling could leave an aliasing spelling stale.
fn caller_admits_name_based_places(func: &VerifiableFunction) -> bool {
    if func_has_pointer_laundering(func) {
        return false;
    }
    !func.body.locals.iter().any(|decl| ty_contains_raw_ptr_local(&decl.ty))
}

/// Transitive raw-pointer occurrence in a type (the `ty_contains_mut_pointer`
/// walk restricted to RAW pointers — `&mut` is excluded because Rust guarantees
/// its uniqueness, which is what makes the name-based refinement sound).
fn ty_contains_raw_ptr_local(ty: &Ty) -> bool {
    match ty {
        Ty::RawPtr { .. } => true,
        Ty::Slice { elem } | Ty::Array { elem, .. } | Ty::SymArray { elem, .. } => {
            ty_contains_raw_ptr_local(elem)
        }
        Ty::Tuple(elems) => elems.iter().any(ty_contains_raw_ptr_local),
        Ty::Adt { fields, .. } => fields.iter().any(|(_, t)| ty_contains_raw_ptr_local(t)),
        Ty::Ref { mutable: true, inner } => ty_contains_raw_ptr_local(inner),
        Ty::Closure { upvars, .. } | Ty::Coroutine { upvars, .. } => {
            upvars.iter().any(ty_contains_raw_ptr_local)
        }
        _ => false,
    }
}

/// The caller-side place a callee write path denotes at this call site, or
/// `None` when the argument shape is not resolvable.
fn caller_place_for_path(args: &[Operand], path: &CalleeWritePath) -> Option<Place> {
    // Formals are MIR locals `1..=arg_count`, so `args[formal - 1]`.
    let arg = args.get(path.formal.checked_sub(1)?)?;
    let actual = match arg {
        Operand::Copy(p) | Operand::Move(p) => p,
        // A constant cannot be the target of a write, and a symbolic/unsupported
        // operand has unknown provenance.
        _ => return None,
    };
    // `path.projections` starts with `Deref` (enforced at derivation), and the
    // actual IS the reference value, so the caller place is
    // `actual.projections ++ path.projections`.
    debug_assert_eq!(path.projections.first(), Some(&Projection::Deref));
    let mut projections = actual.projections.clone();
    projections.extend(path.projections.iter().cloned());
    Some(Place { local: actual.local, projections })
}

/// Refine the conservative ALIAS havoc `conservative` for a call to `callee`
/// with `args`, or return `None` to keep it unchanged.
///
/// `conservative` is the alias part only — `mutably_borrowed_local_names ∪
/// mutable_pointer_local_names`. The call DESTINATION is never passed here and
/// is always havoced by the caller of this function; the callee genuinely writes
/// it and no write-set can excuse that.
///
/// THE REFINEMENT, precisely. A conservative name is dropped ONLY when it is
/// the whole-local name of an argument passed as a plain `&mut T` whose pointee
/// type carries no further pointer — a REPLACEABLE ROOT. Each such root is
/// replaced by the caller-side spellings of the write paths the callee actually
/// takes through it. EVERY other conservative name is retained verbatim:
/// unrelated `&mut` locals, other mut-pointer locals, `&mut`-borrowed FIELD
/// places, and the roots of by-value / projected / non-`&mut` arguments.
///
/// Why a replaceable root may be dropped:
///   * the callee reaches caller memory only through its arguments;
///   * `caller_admits_name_based_places` has excluded raw-pointer aliasing and
///     address laundering in the caller, so within this body the only mutable
///     aliasing channel is `&mut`, which Rust guarantees is unique;
///   * the pointee type carries no nested `&mut`/`*mut`, so there is no second
///     hop out of the receiver's own tree;
///   * the derivation enumerated EVERY write in the callee and failed closed on
///     anything it could not classify, so the mapped paths are its complete
///     caller-visible effect through this argument.
///
/// A root the write-set does not mention is therefore dropped with NOTHING
/// added — which is the "pure helper" case and the point of the whole lane.
pub(crate) fn refine_call_havoc_names(
    func: &VerifiableFunction,
    callee: &str,
    args: &[Operand],
    conservative: &[String],
) -> Option<Vec<String>> {
    let write_set = installed_write_set(callee)?;
    if !caller_admits_name_based_places(func) {
        return None;
    }

    // Replaceable roots, indexed by FORMAL position (`args[k-1]` ⇒ formal `k`).
    let mut roots: Vec<(usize, usize, String)> = Vec::new(); // (formal, local, base name)
    for (i, arg) in args.iter().enumerate() {
        let place = match arg {
            Operand::Copy(p) | Operand::Move(p) => p,
            Operand::Constant(_) => continue,
            // Unknown provenance anywhere in the argument list: refuse outright
            // rather than reason about the rest.
            _ => return None,
        };
        // Only a WHOLE-LOCAL actual is replaceable: a projected actual
        // (`f(&mut s.0)` reached through a `&mut`-typed field) would drop the
        // base name `s` and with it the havoc of its sibling `s.1`.
        if !place.projections.is_empty() {
            continue;
        }
        let Some(ty) = crate::local_ty_ref(func, place.local) else { continue };
        let Ty::Ref { mutable: true, inner } = ty else { continue };
        if ty_contains_mut_pointer(inner) {
            continue;
        }
        roots.push((
            i + 1,
            place.local,
            crate::place_to_var_name(func, &Place { local: place.local, projections: Vec::new() }),
        ));
    }
    if roots.is_empty() {
        return None;
    }

    // Every write path must land inside a REPLACEABLE root, otherwise the
    // refinement would be dropping a havoc it does not reinstate.
    let mut refined_paths: Vec<String> = Vec::new();
    for path in &write_set.paths {
        if !roots.iter().any(|(formal, _, _)| *formal == path.formal) {
            return None;
        }
        let place = caller_place_for_path(args, path)?;
        if !roots.iter().any(|(_, local, _)| *local == place.local) {
            return None;
        }
        refined_paths.push(crate::place_to_var_name(func, &place));
    }

    let mut out: Vec<String> = Vec::new();
    let mut replaced_any = false;
    for name in conservative {
        if roots.iter().any(|(_, _, base)| base == name) {
            replaced_any = true;
            continue;
        }
        if !out.contains(name) {
            out.push(name.clone());
        }
    }
    if !replaced_any {
        // The conservative set never mentioned a replaceable root, so the
        // refinement would be a no-op. Return `None` so the caller keeps its
        // original vector (and ordering) byte-identically.
        return None;
    }
    for name in refined_paths {
        if !out.contains(&name) {
            out.push(name);
        }
    }
    Some(out)
}

#[cfg(test)]
mod tests;
