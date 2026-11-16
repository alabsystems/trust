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
            //
            // A write to the reference VARIABLE itself (`formal = &mut other`,
            // `p = q`, a `(p, q) = (q, p)` swap) is invisible to the caller, but it
            // RESEATS the binding every later `(*formal)` write goes through, and
            // this lane attributes those writes by the formal's local number. Trust
            // (2026-09-29): it was classified caller-invisible and the derivation
            // went on, so `fn g(mut p: &mut S, q: &mut S) { p = q; p.k = 100 }` was
            // recorded as writing `a.k` at `g(a, b)`, the refinement dropped `b`
            // with nothing put back, and a fact about `b.k` survived the call:
            // `if b.k < 4 { g(a, b); buf[b.k] }` was PROVED (an adversarial audit;
            // `tests/ui/trust/callee_reseats_its_formal_refused.rs`). Fail closed.
            Ty::Ref { mutable: true, inner } => {
                if place.projections.is_empty() {
                    return None;
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
                // cannot silently admit the nested-pointer vector above. Asked as
                // the unretagged-pointer question (2026-09-30): a `&mut` or `Box`
                // stored behind a `&` in the pointee is a second hop too — a nested
                // pure-value call writes its target through a copy stashed before
                // the call (`path_defs::ty_reaches_unretagged_pointer`).
                if ty_reaches_unretagged_pointer(inner, true) {
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
///   * every nested `Call`/`TailCall` passes only provably pointer-free arguments;
///   * every written place classifies under [`classify_write_place`];
///   * only statement kinds with a known write effect appear.
pub(crate) fn derive_callee_write_set(callee: &VerifiableFunction) -> Option<CalleeWriteSet> {
    if callee.body.blocks.len() > WRITE_SET_MAX_BLOCKS {
        return None;
    }
    let expanded = callee.with_tail_calls_expanded();
    let callee = expanded.as_ref();
    if callee.body.blocks.len() > WRITE_SET_MAX_BLOCKS {
        return None;
    }
    // Note: pointer laundering (`Rvalue::AddressOf`, `Rvalue::Unsupported`, and
    // `Rvalue::Cast(_, Ty::RawPtr { .. })`) is rejected directly inside the
    // single-pass statement loop below without a separate pre-pass over
    // `callee.body.blocks`.

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
    for (name, summary) in summaries.iter() {
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
    scope_id: u64,
    map: Option<std::sync::Arc<FxHashMap<String, CalleeWriteSet>>>,
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
    let (map, scope_id) = match summaries.filter(|s| !s.is_empty()) {
        None => (None, 0),
        Some(s) => {
            let ws = s.callee_write_sets();
            if ws.is_empty() {
                (None, 0)
            } else {
                (Some(std::sync::Arc::clone(ws)), s.revision())
            }
        }
    };
    let frame_id = CALLEE_WRITE_SET_NEXT_ID.with(|next| {
        let id = next.get();
        next.set(id.wrapping_add(1));
        id
    });
    CALLEE_WRITE_SET_STACK.with(|stack| {
        stack.borrow_mut().push(WriteSetFrame { id: frame_id, scope_id, map })
    });
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
    let (map, scope_id) = if map.is_empty() {
        (None, 0)
    } else {
        (Some(std::sync::Arc::new(map)), (1u64 << 63) | frame_id.saturating_add(1))
    };
    CALLEE_WRITE_SET_STACK.with(|stack| {
        stack.borrow_mut().push(WriteSetFrame { id: frame_id, scope_id, map })
    });
    CalleeWriteSetGuard { frame_id, _thread_affine: std::marker::PhantomData }
}

/// Identifier of the active non-empty [`CalleeWriteSetGuard`] frame (`0` when no
/// scope is active or the active scope carries an empty map). Used to key caches
/// whose values depend on the ambient callee write-set registry.
pub(crate) fn current_scope_id() -> u64 {
    CALLEE_WRITE_SET_STACK.with(|stack| stack.borrow().last().map_or(0, |f| f.scope_id))
}

/// The installed write-set map for the active scope when it contains `callee`,
/// avoiding atomic `Arc` reference-count traffic on calls with no derived entry.
/// `None` when no scope is active, when the innermost scope carries no map, or
/// when that map has no entry for `callee` — every one of which the caller reads
/// as "unknown" and answers with the conservative havoc.
///
/// The key is the name [`build_callee_write_sets`] took from the
/// `SummaryDatabase`, and the entry is derived from that summary's own extracted
/// body: no std spelling is recognized here (VCGEN-NINE-REDS-20261110, the
/// forgeable-key census classifies it outside the unsafe-contract mint).
fn installed_write_set_map_for(
    callee: &str,
) -> Option<std::sync::Arc<FxHashMap<String, CalleeWriteSet>>> {
    CALLEE_WRITE_SET_STACK.with(|stack| {
        stack
            .borrow()
            .last()?
            .map
            .as_ref()
            .filter(|map| map.contains_key(callee))
            .cloned()
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
    if func.body.locals.iter().any(|decl| ty_contains_raw_ptr_local(&decl.ty)) {
        return false;
    }
    !func_has_pointer_laundering(func)
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

/// Refine the conservative ALIAS havoc (the whole-function list, whose membership
/// `in_conservative` answers) for a call to `callee` with `args`, or return `None` to
/// keep it unchanged. The refinement is returned as a DELTA over the list
/// ([`CallHavocDelta`]): the refined list itself is `O(pointer locals)` per call, and
/// building it for every call is what made the version oracle's gen-sets
/// `O(calls x pointer locals)`. [`CallHavocDelta::apply`] builds it, byte for byte, for
/// the consumers that need the `Vec`.
///
/// The conservative list is the alias part only — `mutably_borrowed_local_names ∪
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
///   * the pointee type carries no nested `&mut`/`*mut`/`Box`, not even behind a
///     `&` ([`ty_reaches_unretagged_pointer`]), so there is no second hop out of the
///     receiver's own tree;
///   * the derivation enumerated EVERY write in the callee and failed closed on
///     anything it could not classify, so the mapped paths are its complete
///     caller-visible effect through this argument.
///
/// A root the write-set does not mention is therefore dropped with NOTHING
/// added — which is the "pure helper" case and the point of the whole lane.
pub(crate) fn refine_call_havoc_delta(
    func: &VerifiableFunction,
    callee: &str,
    args: &[Operand],
    in_conservative: &dyn Fn(&str) -> bool,
) -> Option<CallHavocDelta> {
    let write_set_map = installed_write_set_map_for(callee)?;
    let write_set = write_set_map.get(callee)?;

    // Replaceable roots, indexed by FORMAL position (`args[k-1]` ⇒ formal `k`).
    let mut roots: Vec<(usize, usize)> = Vec::new(); // (formal, local)
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
        // No second hop out of the receiver's tree: no `&mut`, raw pointer or `Box`
        // in the pointee — not even behind a `&` there, whose stored `&mut`/`Box`
        // target any code holding a copy stashed before the call can write
        // (`path_defs::ty_reaches_unretagged_pointer`, 2026-09-30).
        if ty_reaches_unretagged_pointer(inner, true) {
            continue;
        }
        roots.push((i + 1, place.local));
    }
    if roots.is_empty()
        || !write_set
            .paths
            .iter()
            .all(|path| roots.iter().any(|(formal, _)| *formal == path.formal))
    {
        return None;
    }

    let root_bases: Vec<String> = roots
        .iter()
        .map(|(_, local)| crate::place_to_var_name(func, &Place::local(*local)))
        .collect();
    if !root_bases.iter().any(|base| in_conservative(base)) {
        // The conservative set never mentioned a replaceable root, so the
        // refinement would be a no-op. Return `None` so the caller keeps its
        // original vector (and ordering) byte-identically.
        return None;
    }
    if !caller_admits_name_based_places(func) {
        return None;
    }

    // Every write path must land inside a REPLACEABLE root, otherwise the
    // refinement would be dropping a havoc it does not reinstate.
    let mut refined_paths: Vec<String> = Vec::with_capacity(write_set.paths.len() * 2);
    for path in &write_set.paths {
        let place = caller_place_for_path(args, path)?;
        if !roots.iter().any(|(_, local)| *local == place.local) {
            return None;
        }
        // Trust (2026-09-29): a write path is a written PLACE, and one holding a fat
        // pointer carries its length with it: `*s = t` of an `s: &mut &[u8]` reseats
        // `s*`, and `s*__slice_len` is a different name that no overlap reaches (`_`
        // is not a projection separator). Every other havoc source mints that twin
        // (`push_derived_slice_len` for a call destination, `mutably_borrowed_havoc_names`
        // for a borrowed root); without it here the call re-versioned `s*` but not its
        // length, and `if i <= s.len() { sset(s, t); &s[..i] }` was PROVED and
        // panicked (audit of `3b4293d06cb`, 2026-09-29; the twin also re-versions the
        // length for the version gen-sets, which read `block_written_names`). Since the
        // merge with upstream's plain-relation havoc kill (`KillSet::havoc`,
        // `TerminatorKill::survives_havoc_plain`) this twin is the ONLY channel that
        // kills the length: a refined path sits in the havoc list, which the plain
        // relation judges without the derived-length disjunct.
        let path_name = crate::place_to_var_name(func, &place);
        refined_paths.push(path_name.clone());
        push_derived_slice_len(&mut refined_paths, &path_name);
        // Trust: 2026-10-12 (UNION-SIBLING-WRITE-2) — a callee write through a union
        // field (`(*r).b = v` for a root `r: &mut U`) rewrites every overlapping
        // sibling: the caller-side cover (`r*`) rebinds them, where the path's own name
        // (`r*.1`) rebinds none. The root's base name `r`, which covered them, is the
        // name this refinement drops. A destination's cover, as every write oracle
        // carries it ([`union_write_cover_name`]).
        if let Some(cover) = union_write_cover_name(func, &place) {
            push_derived_slice_len(&mut refined_paths, &cover);
            refined_paths.push(cover);
        }
    }

    Some(CallHavocDelta {
        roots: root_bases,
        paths: refined_paths,
    })
}

/// A call-write-set refinement of the conservative havoc list, as a delta (see
/// [`refine_call_havoc_delta`]): every conservative name EQUAL to one of `roots` is
/// dropped (the list is deduplicated on the way, keeping first occurrences), and
/// `paths` — the caller-side spellings of the callee's writes — are appended, each
/// once.
#[derive(Clone, Debug)]
pub(crate) struct CallHavocDelta {
    pub(crate) roots: Vec<String>,
    pub(crate) paths: Vec<String>,
}

impl CallHavocDelta {
    /// The refined list, in the order the refinement has always produced it.
    pub(crate) fn apply(&self, conservative: &[String]) -> Vec<String> {
        let cap = conservative.len() + self.paths.len();
        let mut out: Vec<String> = Vec::with_capacity(cap);
        let mut seen: trust_types::fx::FxHashSet<&str> =
            trust_types::fx::FxHashSet::with_capacity_and_hasher(cap, Default::default());
        for name in conservative {
            if self.roots.iter().any(|base| base == name) {
                continue;
            }
            if seen.insert(name.as_str()) {
                out.push(name.clone());
            }
        }
        for name in &self.paths {
            if seen.insert(name.as_str()) {
                out.push(name.clone());
            }
        }
        out
    }
}

// ======================================================================
// Frozen leaves under a shared-reference ARGUMENT
// ======================================================================

/// Trust (2026-09-24, TRUST-10): narrow the conservative havoc of a `&mut` local `p`
/// at a call that receives a SHARED reborrow of `*p` — `self.check()` inside a
/// `&mut self` method — so the scalar fields that call cannot write keep their facts.
///
/// # What was wrong
///
/// bit-vec 0.9.1's
///
/// ```text
/// pub fn remove(&mut self, at: usize) -> bool {
///     assert!(at < self.nbits, ..);
///     self.ensure_invariant();          // fn ensure_invariant(&self)
///     self.nbits -= 1;
///     ..
/// ```
///
/// was reported `[overflow:sub] FAILED` with `self*.1 = 1` before the call and
/// `self*.1 = 0` after it: `mutable_pointer_local_names` puts the base name `self` in
/// every call's havoc list, so the call re-versioned `self.nbits` although it received
/// only `&*self`. No execution does that — the counterexample is not one.
///
/// # Why the narrowing is sound
///
/// A reference passed as a function ARGUMENT is protected for the duration of the
/// call, in Stacked Borrows and in Tree Borrows alike: while the callee runs, a write
/// to any byte the shared reference covers, through ANY pointer, is undefined
/// behaviour — unless the byte lies inside an `UnsafeCell`. It is the premise rustc
/// states to LLVM as `noalias readonly` on a `&Freeze` argument, and the premise
/// `contracts::safe_shared_collection_call_preserves_local` already relies on ("the
/// callee cannot mutate them in a well-defined execution"). So a scalar field of
/// `*p` reached from the covered place through struct fields alone, with no
/// `UnsafeCell` on the way, holds the same value after the call as before it.
///
/// That is the ONLY thing this refinement claims. It keeps every other conservative
/// name verbatim, and replaces `p`'s base name with the names of everything else
/// under `*p`:
///
///  * every field NOT on the covered path (the reborrow may cover one field only);
///  * under the covered place, every subtree that is not such a frozen scalar — an
///    `UnsafeCell` (`Cell`, atomics), an enum, a union, a `Seq`/slice/array, a
///    pointer (memory BEHIND a pointer in `*p` is not covered by the argument's
///    protection: a `Vec`'s buffer can be written through its raw pointer), a
///    generic or compacted type, a hand-built ADT with no recorded kind;
///  * with each such name, its derived `__slice_len` twin — the base name `p` killed
///    `p*.f__slice_len` as a projection descendant, and the field name alone does not.
///
/// The pointer `p` itself cannot change: `local_defs::pointer_is_pinned` — one value,
/// no call-destination, partial or unlocatable write, and no alias of `p`'s OWN
/// storage (a `&mut p` a callee could reseat it through). A borrow THROUGH `p`
/// (`&mut (*p).storage`, which every `&mut self` method that mutates a field takes)
/// does not disqualify: it cannot change the pointer. The shared reborrow must be the argument's ONE value
/// (`local_defs::unique_value_def`), passed whole and directly (a reference nested in
/// an aggregate or a closure tuple is not a protected argument), to a callee that is
/// neither foreign nor `unsafe` (the sibling lane's conservatism) and carries no
/// atomic write of its own. Anything else keeps the full conservative list.
///
/// One step of a shared-reborrow refinement: a narrowed argument's base name and the
/// names that replace it in the havoc list.
pub(crate) type ReborrowStep = (String, Vec<String>);

/// The refinement is returned as its STEPS — `(p's base name, its replacement)` per
/// narrowed argument, in argument order — not as the refined list, for the reason
/// [`refine_call_havoc_delta`] gives. `in_current(name, steps)` answers whether
/// `name` is in the list as refined by `steps` (and by the call-write-set step that
/// may precede them); `path_defs::HavocDelta::flatten` builds the refined list.
pub(crate) fn refine_shared_reborrow_havoc(
    func: &VerifiableFunction,
    args: &[Operand],
    is_foreign: bool,
    is_unsafe_sig: bool,
    has_atomic_write: bool,
    in_current: &dyn Fn(&str, &[ReborrowStep]) -> bool,
) -> Option<Vec<ReborrowStep>> {
    if is_foreign || is_unsafe_sig || has_atomic_write {
        return None;
    }
    let mut steps: Vec<ReborrowStep> = Vec::new();
    for arg in args {
        let (Operand::Copy(r) | Operand::Move(r)) = arg else { continue };
        if !r.projections.is_empty() {
            continue;
        }
        if !matches!(crate::local_ty_ref(func, r.local), Some(Ty::Ref { mutable: false, .. })) {
            continue;
        }
        let Some(Rvalue::Ref { mutable: false, place: referent }) =
            crate::local_defs::unique_value_def(func, r.local)
        else {
            continue;
        };
        let Some((Projection::Deref, covered)) = referent.projections.split_first() else {
            continue;
        };
        if !covered.iter().all(|p| matches!(p, Projection::Field(_))) {
            continue;
        }
        let p = referent.local;
        let Some(Ty::Ref { mutable: true, inner }) = crate::local_ty_ref(func, p) else {
            continue;
        };
        if !crate::local_defs::pointer_is_pinned(func, p) {
            continue;
        }
        let base = crate::place_to_var_name(func, &Place::local(p));
        if !in_current(&base, &steps) {
            continue;
        }
        let Some(replacement) = names_outside_frozen_leaves(func, p, inner, covered) else {
            continue;
        };
        steps.push((base, replacement));
    }
    (!steps.is_empty()).then_some(steps)
}

/// A struct the walk may descend into field by field: extracted from a rustc `AdtDef`
/// as a struct (`adt_kind`), no variant structure, a non-empty field list, not the
/// `UnsafeCell` type itself (`Cell`, `RefCell`, the atomics and `Mutex` all reach
/// their mutable bytes through one, so refusing it at any depth refuses them), and
/// not `Box`. Since 2026-10-14 (INTERIOR-MUT-CHANNEL-1) a cell is refused by the one
/// name list, `type_name_is_interior_mutable` (a superset of `contains("UnsafeCell")`:
/// a wrapper rendered without its fields is havocked whole too), on top of the
/// structural refusal of `UnsafeCell` at any depth.
///
/// `Box` is the one ADT MIR dereferences as a PLACE (`(*p).b*`), and the heap it owns
/// is not covered by the argument's protection; the pointee name `p*.b*` is a
/// descendant of `p*.b` only, so a `Box` field must be havoced WHOLE, never by its
/// `Unique`/`NonNull` leaves. An empty field list is a struct whose fields the
/// extractor did not record (or a zero-sized one): it is havoced whole too, which
/// costs nothing when there is nothing under it and is the fail-closed reading when
/// there is.
fn frozen_struct_fields(ty: &Ty) -> Option<&[(String, Ty)]> {
    match ty {
        Ty::Adt {
            name, fields, variants, adt_kind: Some(trust_types::AdtKind::Struct), ..
        } if variants.is_empty()
            && !fields.is_empty()
            && !type_name_is_interior_mutable(name)
            && !matches!(name.split('<').next(), Some("alloc::boxed::Box" | "std::boxed::Box")) =>
        {
            Some(fields)
        }
        _ => None,
    }
}

/// A scalar with no interior: its bytes are all the value there is.
fn is_frozen_scalar(ty: &Ty) -> bool {
    matches!(ty, Ty::Int { .. } | Ty::PtrSizedInt { .. } | Ty::Bool | Ty::Char)
}

/// The replacement for `p`'s base name — see [`refine_shared_reborrow_havoc`] — or
/// `None` when the covered path cannot be walked or no frozen scalar is under it (the
/// refinement would then exempt nothing).
fn names_outside_frozen_leaves(
    func: &VerifiableFunction,
    p: usize,
    pointee: &Ty,
    covered: &[Projection],
) -> Option<Vec<String>> {
    fn push_opaque(func: &VerifiableFunction, place: &Place, out: &mut Vec<String>) {
        let name = crate::place_to_var_name(func, place);
        push_derived_slice_len(out, &name);
        out.push(name);
    }
    fn cover(
        func: &VerifiableFunction,
        place: &mut Place,
        ty: &Ty,
        out: &mut Vec<String>,
        exempt: &mut usize,
    ) {
        if is_frozen_scalar(ty) {
            *exempt += 1;
            return;
        }
        let Some(fields) = frozen_struct_fields(ty) else {
            push_opaque(func, place, out);
            return;
        };
        for (i, (_, field_ty)) in fields.iter().enumerate() {
            place.projections.push(Projection::Field(i));
            cover(func, place, field_ty, out, exempt);
            place.projections.pop();
        }
    }

    let mut out = Vec::new();
    let mut place = Place { local: p, projections: vec![Projection::Deref] };
    // Compute the pointee root name while `place.projections == [Projection::Deref]`
    // so we do not allocate a second `vec![Projection::Deref]` after the covered walk.
    let root = crate::place_to_var_name(func, &place);
    let mut ty = pointee;
    // Down the covered path: every sibling off it is outside the argument's reach.
    for step in covered {
        let Projection::Field(k) = step else { return None };
        let fields = frozen_struct_fields(ty)?;
        let (_, next) = fields.get(*k)?;
        for i in (0..fields.len()).filter(|i| i != k) {
            place.projections.push(Projection::Field(i));
            push_opaque(func, &place, &mut out);
            place.projections.pop();
        }
        place.projections.push(Projection::Field(*k));
        ty = next;
    }
    // A derived name of the pointee itself (`p*__slice_len`) was a descendant of `p`.
    push_derived_slice_len(&mut out, &root);
    let mut exempt = 0usize;
    cover(func, &mut place, ty, &mut out, &mut exempt);
    (exempt > 0).then_some(out)
}

#[cfg(test)]
mod tests;
