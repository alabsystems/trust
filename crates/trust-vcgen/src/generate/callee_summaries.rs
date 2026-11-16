// Whole-function summaries computed once per callee and reused at every
// callsite: constant return bounds and return-value sets, trivial setters,
// returned enum discriminants, and boolean predicate returns. These are the
// interprocedural facts that let a caller's VC avoid re-analysing the callee.

use super::*;

mod monotone_counter;
// ======================================================================
// Loop-invariant min/max facts (`let n = a.min(b); for i in 0..n { … }`)
// ======================================================================
//
// `Ord::min`/`max` results obey `min(a,b) <= a, <= b` (and the dual for max)
// UNCONDITIONALLY — these methods never panic. The existing BFS semantic-guard
// modeling emits exactly these bounds, but as PATH guards they are weakened to
// nothing at a loop-header join, so they never reach a loop BODY that uses the
// result only transitively (`for i in 0..n` reads `i`, not `n`). The bounded-copy
// idiom `let n = src.len().min(dst.len()); for i in 0..n { dst[i] = src[i]; }`
// then false-refutes: the range-yield fact gives `i < n`, but `n <= dst.len()`
// is gone, so the `dst[i]`/`src[i]` bounds stay satisfiable.
//
// When the result local is SINGLE-ASSIGNMENT and every argument resolves to an
// IMMUTABLE term — a constant, or the `__slice_len` of a PARAMETER slice (a
// slice's length cannot change for the function's lifetime) — the bound is a
// GLOBAL invariant: the result symbol means one value everywhere and the argument
// symbols never change. So it may be conjoined onto every VC, exactly like the
// range-yield fact, reaching the loop body and closing `i < n <= dst.len()`.
//
// SOUNDNESS: min/max are total and panic-free, so `min(a,b) <= a` holds with no
// precondition (unlike clamp, whose `lo <= r <= hi` needs `lo <= hi` — excluded
// here). A non-stable argument (anything but a constant / parameter slice length)
// yields NO fact, never a wrong one. The fact is always TRUE, so it can only help
// PROVE genuinely-safe code; it can never make a real violation vacuously hold.
/// True iff `local` is a function PARAMETER (locals `1..=arg_count`) —
/// [`crate::local_defs::is_parameter`], the one authority on the entry definition.
pub(super) use crate::local_defs::is_parameter;

/// One write the body makes to a PARAMETER's OWN storage: the parameter local
/// (`1..=arg_count`) it reaches, and the formula name of the place written. See
/// [`rebound_parameter_places`].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ParameterRebind {
    /// The parameter local whose storage the write reaches.
    pub parameter: usize,
    /// [`place_to_var_name`] of the written place when that place is the parameter
    /// itself or a chain of `Field` projections below it; otherwise the name of the
    /// WHOLE parameter, which every name rooted at it overlaps (fail-closed).
    pub place_name: String,
}

/// Trust (2026-10-03, KNOWN_HAZARDS R-c): THE ONE AUTHORITY on which places of a
/// PARAMETER's own storage the body writes. A spec-surface `ensures` names a by-value
/// parameter's ENTRY value (E2/D2, docs/design/2026-07-09-two-language-spec-surface.md),
/// but the postcondition VC reads every name at the RETURN block, where the version
/// oracle binds a written place to its FINAL value. Each write listed here is a place
/// whose exit value an `ensures` read of it would silently take instead of the entry
/// value. Two consumers ask it, so they cannot disagree:
///
///  * vcgen's `postcondition_references_mutated_param`, which fail-closes a clause that
///    names one of these places to a bare `Not(post)`;
///  * the compiler's typed-CHC attestation (`typed_chc_rebound_parameters` in
///    `rustc_mir_transform/src/trust_verify.rs`), which must not read that placeholder
///    as an exact payload over the parameter's entry value.
///
/// The channel WALK counts a write when its place, either as spelled or as
/// `canonical_place` folds it (the storage the version oracle names it by — `*p` for
/// `p = &mut s.a` folds to `s.a`), is rooted at a parameter and does not go through a
/// `Deref` of a reference or raw pointer (a parameter declared
/// `&T`/`&mut T`/`*const T`/`*mut T`, or a reference held in one of its fields, such as
/// `Pin<&mut T>`'s). The channels:
///
///  * `Assign` destination, `SetDiscriminant`, `Deinit`, a `Call` destination, and an
///    atomic call's accessed place and result place;
///  * a `&mut` borrow (`Rvalue::Ref { mutable: true }`) of such a place: the borrow is
///    where the alias is minted, and a later `*p = v` names a different local. Named by
///    the borrowed place, because a reference cannot reach outside its referent;
///  * a raw address-of (`&raw const`/`&raw mut`) of such a place: named as the WHOLE
///    parameter, because pointer arithmetic can leave the field it was taken of. So is a
///    place named by an `Rvalue::Unsupported` operand: the extractor lowers a mutable
///    `Reborrow` of a user ADT to one (an alias not spelled as a `Ref`);
///  * `Statement::Unsupported`, `Terminator::Opaque` and any statement or terminator
///    variant this walk does not know: a write with no destination place, so EVERY
///    parameter is named whole. (The first two already fail the body closed with an
///    `UnsupportedMir` row.)
///
/// UNIONED with the `local_defs` seam (from `7f118dfc1f`, which closed the same field-store
/// hole in vcgen independently): every parameter that
/// `local_defs::body_is_single_static_assignment_modulo_pointee_borrows` rejects is
/// named WHOLE as well. A parameter keeps its entry value at every program point when it
/// is single-static-assignment: its only definition the entry, no partial write, no
/// mutable alias of its own storage, no unlocatable write. The union only ever ADDS
/// entries, so it is never weaker than either half. Neither half contains the other:
///
///  * only the walk sees a store through an owned `Box` (`LocalWrite::of_place` treats
///    every `Deref`-first place as untouched), an atomic call's accessed place, an
///    `Rvalue::Unsupported` operand, and a `canonical_place` fold;
///  * only the seam sees a `Drop` of the parameter (a partial write: a custom `Drop::drop`
///    takes `&mut self`), `Statement::Intrinsic` and `CopyNonOverlapping` (an unlocatable
///    write, charged to every parameter), and a store through a reference HELD IN A FIELD
///    (`(*(self.pointer)).x = ..` for `self: Pin<&mut S>`): `of_place` counts any place
///    whose FIRST projection is not a `Deref` as a partial write of its root. The seam
///    also names whole what the walk names per place, so after `s.b = ..` a clause over
///    `s.a` is fail-closed too. Each of these costs proofs (DECISION_QUEUE R-c); the
///    walk's own reasons for leaving the first three out are kept below.
///
/// The seam's POINTEE-borrow variant is the one the union asks, because a `&mut` borrow
/// reached THROUGH the parameter (`reset(&mut (*self).s)`) addresses the pointee and
/// cannot rebind the parameter itself. The strict variant marked a `&mut self` parameter
/// rebound, and the fail-closed shortcut then turned a correct `ensures
/// !self.s.detached` into a refutation with a counterexample
/// (`chc-entry-inputs/wedge_refutation_attests.rs`). It draws the same line as the walk's
/// `Deref` exclusion for a reference PARAMETER.
///
/// What the WALK does not count, and why each is not a write of the entry value (the seam
/// half still counts the `Pin` case of the first, and the second and third, as listed
/// above):
///
///  * a store THROUGH a reference or raw pointer (`(*self).x = ..` for `self: &mut S`,
///    `(*(self.pointer)).x = ..` for `self: Pin<&mut S>`). It changes the pointee, which
///    the caller owns. The unprimed pointee name in an `ensures` reads that pointee at
///    EXIT on purpose until the PD-15 flip (docs/DECISION_QUEUE.md PD-15; pinned by
///    `tests/ui/trust/d2-primes/wedge_primed.rs`). A `Box` is owned and is not excluded:
///    a store through one counts (whole), and so does a `Deref` of a place whose type
///    cannot be resolved.
///  * `Statement::Intrinsic` (today only `assume`, which writes nothing) and
///    `CopyNonOverlapping`, which writes through a POINTER operand. A pointer into a
///    parameter's storage exists only after a borrow or address-of of a place rooted at
///    it, which this walk records at the borrow.
///  * `Terminator::Drop`: drop glue mints no defined value, so the version oracle cannot
///    bind a later read to a value the body chose.
///  * a shared borrow (`&s.c`). A write through it needs interior mutability; an
///    `ensures` cannot spell an `UnsafeCell`'s contents today. The seam does not count
///    it either. A residual, recorded in KNOWN_HAZARDS R-c.
pub fn rebound_parameter_places(func: &VerifiableFunction) -> Vec<ParameterRebind> {
    if func.body.arg_count == 0 {
        return Vec::new();
    }
    let _analysis_memo = crate::gen_work_memo_scope_if_unscoped();
    let _func_scope = super::FuncAnalysisScope::enter(func);
    let mut out: Vec<ParameterRebind> = Vec::new();
    let mut whole_rebound: Vec<bool> = vec![false; func.body.arg_count + 1];
    let every_parameter = |out: &mut Vec<ParameterRebind>, whole_rebound: &mut [bool]| {
        for parameter in 1..=func.body.arg_count {
            if whole_rebound.get(parameter).copied() == Some(true) {
                continue;
            }
            if let Some(slot) = whole_rebound.get_mut(parameter) {
                *slot = true;
            }
            push_rebind(
                out,
                ParameterRebind {
                    parameter,
                    place_name: place_to_var_name(func, &Place::local(parameter)),
                },
            );
        }
    };
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            match stmt {
                Statement::Assign { place, rvalue, .. } => {
                    note_parameter_write(func, place, true, &mut out, &mut whole_rebound);
                    match rvalue {
                        Rvalue::Ref { mutable: true, place: borrowed } => {
                            note_parameter_write(
                                func,
                                borrowed,
                                true,
                                &mut out,
                                &mut whole_rebound,
                            );
                        }
                        Rvalue::AddressOf(_, borrowed) => {
                            note_parameter_write(
                                func,
                                borrowed,
                                false,
                                &mut out,
                                &mut whole_rebound,
                            );
                        }
                        Rvalue::Unsupported { operands, .. } => {
                            for operand in operands {
                                if let Operand::Copy(named) | Operand::Move(named) = operand {
                                    note_parameter_write(
                                        func,
                                        named,
                                        false,
                                        &mut out,
                                        &mut whole_rebound,
                                    );
                                }
                            }
                        }
                        _ => {}
                    }
                }
                Statement::SetDiscriminant { place, .. } | Statement::Deinit { place } => {
                    note_parameter_write(func, place, true, &mut out, &mut whole_rebound);
                }
                Statement::Unsupported { .. } => every_parameter(&mut out, &mut whole_rebound),
                Statement::Intrinsic { .. }
                | Statement::CopyNonOverlapping { .. }
                | Statement::StorageLive(_)
                | Statement::StorageDead(_)
                | Statement::Retag { .. }
                | Statement::PlaceMention(_)
                | Statement::Coverage
                | Statement::ConstEvalCounter
                | Statement::Nop => {}
                // `Statement` is `#[non_exhaustive]`: a variant added after this walk was
                // written may write a place it does not show here. Fail closed.
                _ => every_parameter(&mut out, &mut whole_rebound),
            }
        }
        match &block.terminator {
            Terminator::Call { dest, atomic, .. } => {
                note_parameter_write(func, dest, true, &mut out, &mut whole_rebound);
                if let Some(atomic) = atomic {
                    note_parameter_write(func, &atomic.place, true, &mut out, &mut whole_rebound);
                    if let Some(atomic_dest) = &atomic.dest {
                        note_parameter_write(
                            func,
                            atomic_dest,
                            true,
                            &mut out,
                            &mut whole_rebound,
                        );
                    }
                }
            }
            Terminator::TailCall { atomic, .. } => {
                if let Some(atomic) = atomic {
                    note_parameter_write(func, &atomic.place, true, &mut out, &mut whole_rebound);
                    if let Some(atomic_dest) = &atomic.dest {
                        note_parameter_write(
                            func,
                            atomic_dest,
                            true,
                            &mut out,
                            &mut whole_rebound,
                        );
                    }
                }
            }
            Terminator::Opaque { .. } => every_parameter(&mut out, &mut whole_rebound),
            Terminator::Goto(_)
            | Terminator::SwitchInt { .. }
            | Terminator::Return
            | Terminator::Assert { .. }
            | Terminator::Drop { .. }
            | Terminator::Unreachable
            | Terminator::Resume => {}
            // `Terminator` is `#[non_exhaustive]`; same fail-closed rule as above.
            _ => every_parameter(&mut out, &mut whole_rebound),
        }
    }
    // SOUNDNESS (2026-10-03, KNOWN_HAZARDS R-c; the `local_defs` half, from `7f118dfc1f`):
    // `fn setf(mut p: Pair) -> u32 ensures result == p.a { p.a = p.a.wrapping_add(5); p.a }`
    // exited 0 under `certify` with both postcondition rows proved, the clause's `p.0` read
    // at `p.0#s1_0` (after the store) instead of `p.0#e`. Ask the seam instead of
    // re-deriving it, and union its answer with the walk: a parameter that is not
    // single-static-assignment modulo pointee borrows is named WHOLE. See the doc above
    // for what each half sees that the other does not.
    for parameter in 1..=func.body.arg_count {
        if whole_rebound.get(parameter).copied() == Some(true) {
            continue;
        }
        if is_parameter(func, parameter)
            && !crate::local_defs::body_is_single_static_assignment_modulo_pointee_borrows(
                &func.body, parameter,
            )
        {
            if let Some(slot) = whole_rebound.get_mut(parameter) {
                *slot = true;
            }
            push_rebind(
                &mut out,
                ParameterRebind {
                    parameter,
                    place_name: place_to_var_name(func, &Place::local(parameter)),
                },
            );
        }
    }
    out
}

fn push_rebind(out: &mut Vec<ParameterRebind>, rebind: ParameterRebind) {
    if !out.contains(&rebind) {
        out.push(rebind);
    }
}

/// Record `place` in `out` when it reaches a parameter's own storage, as written or as
/// [`crate::canonical_place`] folds it. `nameable` is false for a raw address-of (and an
/// unsupported rvalue's operand), whose pointer is not confined to the place it names.
fn note_parameter_write(
    func: &VerifiableFunction,
    place: &Place,
    nameable: bool,
    out: &mut Vec<ParameterRebind>,
    whole_rebound: &mut [bool],
) {
    if let Some((rebind, is_whole)) = parameter_rebind_of(func, place, nameable, whole_rebound) {
        if is_whole && let Some(slot) = whole_rebound.get_mut(rebind.parameter) {
            *slot = true;
        }
        push_rebind(out, rebind);
    }
    // A whole local canonicalizes to itself (`canonicalize_deref` folds only a leading
    // `Deref`, `base_value_alias` only a projected place), so only a projected place can
    // fold onto a parameter's storage. Skipping the rest keeps the walk linear on the
    // temporaries that make up most destinations.
    if !place.projections.is_empty() {
        let canonical = crate::canonical_place(func, place);
        if canonical != *place
            && let Some((rebind, is_whole)) =
                parameter_rebind_of(func, &canonical, nameable, whole_rebound)
        {
            if is_whole && let Some(slot) = whole_rebound.get_mut(rebind.parameter) {
                *slot = true;
            }
            push_rebind(out, rebind);
        }
    }
}

/// True iff `place` goes through a `Deref` of a reference or raw pointer: the type of the
/// prefix before its FIRST `Deref` is `&T`/`&mut T`/`*const T`/`*mut T`. A write there
/// lands in memory the place's root does not own. An unresolvable prefix type answers
/// `false` (the write is then counted: fail-closed).
fn deref_reaches_borrowed_memory(func: &VerifiableFunction, place: &Place) -> bool {
    let Some(first_deref) = place.projections.iter().position(|p| *p == Projection::Deref) else {
        return false;
    };
    matches!(
        crate::place_prefix_ty_cow(func, place.local, &place.projections[..first_deref]).as_deref(),
        Some(Ty::Ref { .. } | Ty::RawPtr { .. })
    )
}

fn parameter_rebind_of(
    func: &VerifiableFunction,
    place: &Place,
    nameable: bool,
    whole_rebound: &[bool],
) -> Option<(ParameterRebind, bool)> {
    if !is_parameter(func, place.local) {
        return None;
    }
    let fields_only = place.projections.iter().all(|p| matches!(p, Projection::Field(_)));
    let is_whole = place.projections.is_empty() || !nameable || !fields_only;
    if is_whole && whole_rebound.get(place.local).copied() == Some(true) {
        return None;
    }
    // A store through a reference or raw pointer writes the caller's object, not the
    // parameter: out of scope (PD-15, see `rebound_parameter_places`).
    if deref_reaches_borrowed_memory(func, place) {
        return None;
    }
    let place_name = if !is_whole {
        place_to_var_name(func, place)
    } else {
        place_to_var_name(func, &Place::local(place.local))
    };
    Some((ParameterRebind { parameter: place.local, place_name }, is_whole))
}

/// SOUNDNESS (P0 false proof, 2026-06-17 hunt-6): true when a `#[ensures]` postcondition
/// names a place of a PARAMETER that the body WRITES. The v2 postcondition VC binds the
/// parameter to its RETURN-block (final, mutated) value via the path/block defs, but the
/// `ensures` semantics snapshot the parameter's ENTRY value (`move |r| *r == a` captures `a` at
/// entry). For `#[ensures(move |r| *r == a)] fn f(mut a:u32){ a = a.wrapping_add(1); a }` the VC
/// checks `r == a_final` (11==11 → vacuously PROVED) while the true `r == a_entry` (11==10) is
/// FALSE — a default-mode false proof (FULL fail-closes soundly). The caller FAIL-CLOSES on this
/// (does not credit the proof) until proper entry-snapshot modeling lands.
///
/// hunt-15 Class B added the `&mut a` / `&raw mut a` borrow channel (`let p=&mut a; *p=..`,
/// `mem::replace(&mut a, k)`, a helper `bump(&mut a)`): the store's place is `*p`, invisible
/// to a scan of `a`'s own writes.
///
/// Trust (2026-10-03, KNOWN_HAZARDS R-c): both scans used to see only WHOLE-local writes, so a
/// write to a FIELD of a by-value parameter slipped through. `fn z(mut s: S) -> u8 ensures s.a
/// == 0 { s.a = 0; 1 }` was proved and kernel-certified under `-Ztrust-policy=certify`: the VC
/// read `s.0` at its exit version, defined `== 0`. (`7f118dfc1f` closed the same hole here
/// independently, for `fn setf(mut p: Pair) -> u32 ensures result == p.a`, by asking the
/// `local_defs` seam; the two fixes are now one predicate.) The written places now come from
/// [`rebound_parameter_places`], the one predicate the compiler's typed-CHC attestation also
/// asks. A clause is fail-closed when one of its names overlaps a written place
/// ([`dest_write_rebinds`]: equal, ancestor or descendant, symbolic-index alias, or the derived
/// `__slice_len` of a reseated place). The walk's per-place names alone would leave a clause
/// over `s.a` provable after `s.b = ..`, but the seam half of the union names a non-SSA
/// parameter WHOLE, so today every write to a by-value parameter's own storage fail-closes
/// every clause that names that parameter (a capability cost, DECISION_QUEUE R-c).
pub(super) struct MutatedParamPlaces {
    reassigned: FxHashSet<String>,
    rebinds: Vec<ParameterRebind>,
}

impl MutatedParamPlaces {
    pub(super) fn of(func: &VerifiableFunction) -> Self {
        if func.body.arg_count == 0 {
            return Self { reassigned: FxHashSet::default(), rebinds: Vec::new() };
        }
        let _analysis_memo = crate::gen_work_memo_scope_if_unscoped();
        let _func_scope = super::FuncAnalysisScope::enter(func);
        // Merge 2026-10-14: the local whole-parameter scan (review round 44: a field or
        // element write of a by-value parameter, a non-`Deref` `&mut`/raw borrow, a call
        // destination) is kept beside upstream's one authority and the clause is
        // fail-closed when EITHER names it; the two were measured independently.
        let mut reassigned: FxHashSet<String> = FxHashSet::default();
        let mut seen_locals: FxHashSet<usize> = FxHashSet::default();
        let mut note = |func: &VerifiableFunction, local: usize| -> bool {
            if is_parameter(func, local) && seen_locals.insert(local) {
                reassigned.insert(crate::place_to_var_name(func, &Place::local(local)));
            }
            seen_locals.len() == func.body.arg_count
        };
        'blocks: for block in &func.body.blocks {
            for stmt in &block.stmts {
                if let Statement::Assign { place, rvalue, .. } = stmt {
                    // Review round 44: a write to a FIELD or element of a by-value
                    // parameter (`s.a = 0`, `s.0 += 1`) changes what `ensures .. s.a`
                    // reads at the return as surely as a whole write; only a write
                    // THROUGH a reference parameter (`Deref` first) leaves the parameter
                    // itself alone.
                    if !matches!(place.projections.first(), Some(Projection::Deref))
                        && note(func, place.local)
                    {
                        break 'blocks;
                    }
                    // SOUNDNESS (P0 false proof, 2026-06-17 hunt-15 Class B): a parameter
                    // MUTABLY BORROWED (`&mut a` / `&raw mut a`) can be reassigned through the
                    // borrow AFTER the entry snapshot — `let p=&mut a; *p=..` (the store's place
                    // is `*p`, invisible to the whole-local scan above), `mem::replace(&mut a, k)`,
                    // `mem::swap(&mut a, &mut other)`, or a helper `bump(&mut a)`. The `ensures`
                    // captures `a` at ENTRY (`move |r| *r == a`) but the body returns the MUTATED
                    // value, so `r == a_final` vacuously PROVES while the true `r == a_entry` is
                    // false. The hunt-6 whole-local-reassign scan misses this &mut/AddressOf vector
                    // exactly as the bounds lane did (hunt-5). Flag the borrowed param so the caller
                    // fail-closes (does not credit the postcondition). Mirrors
                    // `value_local_is_unstable` / `is_single_static_assignment`'s kill-on-Ref.
                    if let Rvalue::Ref { mutable: true, place: bp } | Rvalue::AddressOf(_, bp) =
                        rvalue
                        && !matches!(bp.projections.first(), Some(Projection::Deref))
                        && note(func, bp.local)
                    {
                        break 'blocks;
                    }
                }
            }
            if let Terminator::Call { dest, .. } = &block.terminator
                && !matches!(dest.projections.first(), Some(Projection::Deref))
                && note(func, dest.local)
            {
                break 'blocks;
            }
        }
        // Trust (2026-10-03, KNOWN_HAZARDS R-c): ONE authority, asked here and by the
        // compiler's typed-CHC twin. The whole-local scan that used to live here (hunt-6's
        // whole-local `Assign`, hunt-15 Class B's whole `&mut` / raw borrow, the whole `Call`
        // destination) is a subset of BOTH halves of `rebound_parameter_places`: of its
        // channel walk (each is a write of a place rooted at the parameter with no `Deref`),
        // and of the `local_defs` non-SSA test the walk is unioned with (a whole write is a
        // second whole value, a whole borrow an escape of the parameter's own storage). It is
        // not kept as a third copy.
        let rebinds = rebound_parameter_places(func);
        Self { reassigned, rebinds }
    }

    pub(super) fn references(&self, post: &Formula) -> bool {
        if self.rebinds.is_empty() && self.reassigned.is_empty() {
            return false;
        }
        trust_types::any_formula_node(post, &mut |node| {
            node.var_name().is_some_and(|v| {
                self.reassigned.contains(v)
                    || self.rebinds.iter().any(|rebind| dest_write_rebinds(&rebind.place_name, v))
                    || self.reassigned.iter().any(|n| write_rebinds(n, v))
            })
        })
    }
}

pub(super) fn postcondition_references_mutated_param(
    func: &VerifiableFunction,
    post: &Formula,
) -> bool {
    if func.body.arg_count == 0
        || !trust_types::any_formula_node(post, &mut |node| node.var_name().is_some())
    {
        return false;
    }
    MutatedParamPlaces::of(func).references(post)
}

pub(super) fn postcondition_references_mutated_param_cached(
    func: &VerifiableFunction,
    post: &Formula,
    cache: &std::cell::OnceCell<MutatedParamPlaces>,
) -> bool {
    if func.body.arg_count == 0
        || !trust_types::any_formula_node(post, &mut |node| node.var_name().is_some())
    {
        return false;
    }
    cache.get_or_init(|| MutatedParamPlaces::of(func)).references(post)
}

/// True iff `local` holds ONE value for the whole body with no field/index store, no
/// `SetDiscriminant`/`Deinit`, and no `&mut`/raw mutation channel —
/// [`crate::local_defs::is_single_static_assignment`], which counts the ENTRY
/// definition a PARAMETER carries. Re-exported here because this module's
/// `use super::*` vocabulary is what the fact producers read.
///
/// The discriminant/`Deinit` kill is not restated at the new home: those statements
/// classify through `LocalWrite::demote_to_partial`, so they arrive as
/// `LocalWrite::Partial`, which that predicate disqualifies.
/// `local_defs_tests::discriminant_and_deinit_writes_are_partial` fails when that
/// stops holding.
pub(super) use crate::local_defs::is_single_static_assignment;

/// Trust (countdown-loop piece, P0 root-cause fix): `true` iff `local` is ever
/// MUTABLY borrowed (`&mut local`, `Rvalue::Ref { mutable: true }`) or
/// raw-addressed (`&raw const/mut local`, `Rvalue::AddressOf`) anywhere in the
/// body — the write channels a def-site scan cannot see. A callee receiving
/// `&mut i` can reseat `i` to ANY value, so every induction-style invariant
/// derived from `i`'s visible defs (single init + self-decrements) is void: the
/// pre-fix `build_downward_induction_facts` emitted `_t.0 < s.len()` for
/// `while i > 0 { i -= 1; s[i]; bump(&mut i); }`, a fact that is FALSE at
/// runtime on the second iteration — a confirmed false PROOF of the `s[i]`
/// bounds row (panics rc=101). Raw-const is included fail-closed (a `*const`
/// cast to `*mut` write is UB in sound code, but this scan is not a UB oracle).
/// Shared `&local` borrows of these integer locals are NOT writes (no interior
/// mutability without `UnsafeCell`, which an `Int`-typed local cannot be) and
/// stay allowed.
pub(super) fn local_mut_escapes(func: &VerifiableFunction, local: usize) -> bool {
    crate::any_local_write_stmt(func, &func.body.blocks, local, |_block, s| {
        matches!(s, Statement::Assign {
            rvalue: Rvalue::Ref { mutable: true, place: borrowed }
                | Rvalue::AddressOf(_, borrowed),
            ..
        } if borrowed.local == local)
    })
}

/// The canonical `{root}__slice_len` of the slice that `operand` reads the length of,
/// following whole-local copies and a `&(*root)` / `&raw const (*root)` reborrow to
/// the ROOT — and licensed by NAME at the root: `None` unless
/// `slice_len_licence::licensed_slice_len_formula` admits the root, i.e. the place
/// owning the length metadata is `local_defs::path_is_single_static_assignment` (a
/// never-written parameter passes; a `mut` parameter with a body write `_1 = copy _2`
/// refuses — whether the user spelled the reseat or `-Copt-level=1` copy-propagated a
/// local onto the parameter; a single-write local passes; an aliased or reseated one
/// refuses). A constant length (`&[T; N]`) needs no licence and is returned as is.
///
/// Trust: 2026-09-16 (round A8) — SOUNDNESS. The licence used to be `is_parameter(root)`
/// alone ("only then is the length immutable and the symbol stable"), and every
/// consumer — `stable_min_arg_formula` and through it `build_min_max_facts`,
/// `build_modulo_bound_facts`, `build_division_lt_facts`, `build_division_exact_facts`,
/// `init_rvalue_stable_len` — inlines the returned NAME into a GLOBAL fact that
/// `generate::safety` conjoins onto every VC after the version rename. A `mut s: &[u8]`
/// parameter reseated in the body passes `is_parameter`, and the fact `n <= s__slice_len`
/// then binds to the post-reseat version: `fn f(mut s: &[u8], b: &[u8]) -> u8 { let n =
/// s.len().min(100); s = b; s[..n].len() as u8 }` PROVED, kernel-certified, on the sealed
/// driver and on stage1 at both `-O0` and `-O1`, and `f(&[1,2,3,4,5], &[1])` panics
/// ("range end index 5 out of range for slice of length 1"). Pinned on the compiler's
/// own MIR in `tests/escaped_local_seam_realmir.rs` (`a8_min_reseat_*`, `a8_min_loop_*`
/// — never proved; `a8_ctl_min_*` — must prove).
///
/// The hops are followed to the ROOT before the licence is asked so the name minted is
/// the root's canonical one (`s__slice_len`, the symbol the bounds obligation reads),
/// not a copy temp's; the licence at the root walks the same chain back
/// ([`slice_len_licence::slice_len_name_is_stable`]), so every hop is gated.
pub(super) fn param_slice_len_place(
    func: &VerifiableFunction,
    place: &Place,
    fuel: u32,
) -> Option<Formula> {
    let root = slice_len_root_place_from_place(func, place, fuel)?;
    super::slice_len_licence::licensed_slice_len_formula_place(func, &root, fuel)
}

pub(super) fn param_slice_len(
    func: &VerifiableFunction,
    operand: &Operand,
    fuel: u32,
) -> Option<Formula> {
    let (Operand::Copy(p) | Operand::Move(p)) = operand else { return None };
    param_slice_len_place(func, p, fuel)
}

/// The canonical slice length that a `PtrMetadata`/`Len` ARGUMENT of a call reads,
/// for a fact that is VERSIONED AT THE CALL — `semantic_guard`'s per-call `Ord::min`/
/// `max` result bounds, which `version_terminator_dest_fact` renames at the block
/// terminal so `{root}__slice_len` becomes the version of the root live at that
/// program point. Deliberately UNLICENSED: a versioned symbol names exactly the value
/// read at the call, whatever the root does before or after, so the name licence
/// [`param_slice_len`] needs for a GLOBAL fact would only withhold a true one. The
/// argument's own name (`_4`) is kept beside it by the caller; this is the twin that
/// reaches the obligation's symbol through the root's canonical name when the copy
/// temp's length is tied to nothing (`_5 = copy _1; _4 = PtrMetadata(move _5)`).
///
/// Trust: 2026-09-16 (round A8) — the row this exists for: `fn f(mut s, b) { s = b;
/// let n = s.len().min(100); s[..n] }` (`ctl_min_after_reseat`, correct) proved on the
/// pristine driver ONLY through the unlicensed global fact `n <= s__slice_len` renamed
/// onto the post-reseat version by luck of ordering; with that fact licensed away it
/// must prove through `n <= s__slice_len#<at the call>` instead, and the reseat-AFTER
/// twin (`min_reseat_slice_bug`, a panic) reads a later version and is name-disjoint.
///
/// MUST NOT be conjoined unversioned onto every VC: that is the hole
/// [`param_slice_len`] closes.
///
/// THE TIME AXIS. The fact is renamed at the call's TERMINAL point, so the root's
/// symbol is its version live at the call — which is the length the argument read
/// only if nothing rebinds the root between the read and the call. `let n0 = s.len();
/// s = b; let n = n0.min(100)` reads the OLD length and would be stated on the NEW one.
/// So: every link of the read chain (the `PtrMetadata`/`Len` temp and each copy /
/// reborrow / cast temp down to the root) must be defined in `block` itself, no
/// statement from the earliest link to the terminator may write or alias the root
/// on any channel, and the root may carry no mutable or raw alias anywhere in the body
/// (a store through an earlier alias between the read and the call names a place
/// this scan does not see). Anything else: no twin.
pub(super) fn call_point_slice_len_of_arg(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    arg: &Operand,
) -> Option<Formula> {
    const FUEL: u32 = 8;
    let (Operand::Copy(p) | Operand::Move(p)) = arg else { return None };
    if !p.projections.is_empty() {
        return None;
    }
    let defining_index = |local: usize| -> Option<usize> {
        block.stmts.iter().position(|s| {
            matches!(s, Statement::Assign { place, .. } if place.local == local && place.projections.is_empty())
        })
    };
    let mut earliest = defining_index(p.local)?;
    let root_local = match crate::local_defs::unique_value_def(func, p.local)? {
        Rvalue::UnaryOp(trust_types::UnOp::PtrMetadata, inner)
            if matches!(
                crate::ptr_metadata_model(func, inner),
                crate::PtrMetadataModel::Length(_)
            ) =>
        {
            // Walk the chain link by link so each link's definition is located here.
            let mut cur = inner;
            let mut fuel = FUEL;
            loop {
                if fuel == 0 {
                    return None;
                }
                fuel -= 1;
                let (Operand::Copy(q) | Operand::Move(q)) = cur else { return None };
                if !q.projections.is_empty() {
                    return None;
                }
                let next = match crate::local_defs::unique_value_def(func, q.local) {
                    Some(Rvalue::Ref { place: referent, .. } | Rvalue::AddressOf(_, referent)) => {
                        earliest = earliest.min(defining_index(q.local)?);
                        if !matches!(
                            referent.projections.as_slice(),
                            [] | [trust_types::Projection::Deref]
                        ) {
                            return None;
                        }
                        break referent.local;
                    }
                    Some(Rvalue::Use(next)) => {
                        earliest = earliest.min(defining_index(q.local)?);
                        next
                    }
                    Some(Rvalue::Cast(next, to_ty))
                        if matches!(
                            to_ty,
                            Ty::Ref { inner: t, .. } | Ty::RawPtr { pointee: t, .. }
                                if matches!(t.as_ref(), Ty::Slice { .. })
                        ) =>
                    {
                        earliest = earliest.min(defining_index(q.local)?);
                        next
                    }
                    // The root: a parameter, a call destination, an aggregate.
                    _ => break q.local,
                };
                cur = next;
            }
        }
        Rvalue::Len(place) if place.projections.is_empty() => place.local,
        _ => return None,
    };
    if local_mut_escapes(func, root_local) {
        return None;
    }
    let rebinds_root = |s: &Statement| {
        !matches!(s.local_write(root_local), trust_types::LocalWrite::Untouched)
            || crate::stmt_escapes_local(func, s, root_local)
    };
    if block.stmts[earliest..].iter().any(rebinds_root) {
        return None;
    }
    crate::place_slice_len_formula(func, &Place::local(root_local))
}

/// The projection-free ROOT place whose length `operand` reads, following whole-local
/// copies (`_t = copy root`), the `&(*root)` / `&raw const (*root)` reborrow rustc
/// spells a `&mut [T]` length read with, and a slice-preserving cast, to the local
/// that has no such hop (a parameter, a call destination, an aggregate). NO LICENCE:
/// the caller decides — [`param_slice_len`] licenses the root by NAME for a global
/// fact, [`call_point_slice_len_of_arg`] versions it at the call instead.
pub(super) fn slice_len_root_place(
    func: &VerifiableFunction,
    operand: &Operand,
    fuel: u32,
) -> Option<Place> {
    let (Operand::Copy(p) | Operand::Move(p)) = operand else { return None };
    slice_len_root_place_from_place(func, p, fuel)
}

fn slice_len_root_place_from_place(
    func: &VerifiableFunction,
    p: &Place,
    fuel: u32,
) -> Option<Place> {
    if fuel == 0 || !p.projections.is_empty() {
        return None;
    }
    match crate::local_defs::unique_value_def(func, p.local) {
        Some(Rvalue::Ref { place: referent, .. } | Rvalue::AddressOf(_, referent)) => {
            matches!(referent.projections.as_slice(), [] | [trust_types::Projection::Deref])
                .then(|| Place::local(referent.local))
        }
        Some(Rvalue::Use(inner)) => slice_len_root_place(func, inner, fuel - 1),
        // Trust (countdown-loop piece, G1): the UNSIZE coercion `&[T; N] -> &[T]`
        // (`_t = move _a as &[T]`), the shape `buf.len()` inlines to on a
        // `&mut [T; N]` parameter (`_a = &(*buf); _t = _a as &[T]; PtrMetadata(_t)`).
        // SOUND: a cast whose TARGET is a reference/raw pointer to a SLICE preserves
        // the fat-pointer metadata verbatim (rustc rejects thin->fat `as` casts, so
        // the source is either an unsize coercion from `&[T; N]` — metadata := N, the
        // exact array length — or an already-fat pointer whose metadata is copied
        // unchanged). Recursing on the SOURCE operand computes the length from the
        // source's own type through the existing param-rooted arms, which only
        // resolve immutable param-anchored lengths — nothing new is trusted.
        Some(Rvalue::Cast(inner, to_ty))
            if matches!(
                to_ty,
                Ty::Ref { inner: t, .. } | Ty::RawPtr { pointee: t, .. }
                    if matches!(t.as_ref(), Ty::Slice { .. })
            ) =>
        {
            slice_len_root_place(func, inner, fuel - 1)
        }
        // No hop: the operand IS the root — a never-written parameter, a call
        // destination, an aggregate.
        _ => Some(Place::local(p.local)),
    }
}

/// True iff `local`'s single definition is an `Ord::min`/`max` call result. Lets
/// the chained idiom `a.len().min(b.len()).min(c.len())` resolve: the outer min's
/// inner-result argument is a single-assignment local, and `min(inner, c) <= inner`
/// holds unconditionally, so `dest <= Var(inner)` chains through the inner call's
/// own (separately emitted) `inner <= a.len()` / `<= b.len()` facts.
///
/// NAME-ANCHOR-2 (2026-10-04): a primitive integer `Self`
/// (`call_facts::primitive_int_ord_method`) — a user `Ord` impl may override
/// `min`/`max`, and then `dest <= inner` is whatever its body makes it.
pub(super) fn local_is_min_max_result(func: &VerifiableFunction, local: usize) -> bool {
    if !super::terminator_presence_for(func).has_bare_dest_call {
        return false;
    }
    crate::any_local_write_term(func, &func.body.blocks, local, |_block, term| {
        matches!(term,
        Terminator::Call { func: callee, args, dest, .. }
            if dest.local == local
                && dest.projections.is_empty()
                && matches!(
                    primitive_int_ord_method(func, callee, args, dest),
                    Some("min" | "max")
                ))
    })
}

/// Resolve a min/max argument to a STABLE formula (constant or parameter slice
/// length) — see [`param_slice_len`]. None for anything whose value could change
/// between the call site and a use site, so the bound stays a sound global fact.
pub(super) fn stable_min_arg_formula(
    func: &VerifiableFunction,
    operand: &Operand,
    fuel: u32,
) -> Option<Formula> {
    if fuel == 0 {
        return None;
    }
    if let Operand::Constant(_) = operand {
        return Some(operand_to_formula(func, operand));
    }
    let (Operand::Copy(p) | Operand::Move(p)) = operand else { return None };
    if !p.projections.is_empty() {
        return None;
    }
    match crate::local_defs::unique_value_def(func, p.local) {
        Some(Rvalue::Use(inner)) => return stable_min_arg_formula(func, inner, fuel - 1),
        Some(Rvalue::UnaryOp(trust_types::UnOp::PtrMetadata, inner)) => {
            return param_slice_len(func, inner, fuel - 1);
        }
        Some(Rvalue::Len(place)) => {
            let root = slice_len_root_place_from_place(func, place, fuel - 1)?;
            return super::slice_len_licence::licensed_slice_len_formula(
                func,
                &Operand::Copy(root),
                fuel - 1,
            );
        }
        // No whole-local Assign def: fall through to the min/max-result case below
        // (the inner result of a chained `.min().min()` is a Call dest, which
        // `unique_value_def` — Assign-only — does not see).
        Some(_) => return None,
        None => {}
    }
    // A nested `Ord::min`/`max` RESULT is a single-assignment, stable symbol;
    // `min(inner, c) <= inner` is unconditionally true, so `dest <= Var(inner)` is
    // sound and chains through `inner`'s own emitted bounds.
    if is_single_static_assignment(func, p.local)
        && !crate::local_defs::is_parameter(func, p.local)
        && local_is_min_max_result(func, p.local)
    {
        return Some(Formula::Var(crate::place_to_var_name(func, p), Sort::Int));
    }
    None
}

/// Global, loop-invariant facts from `Ord::min`/`max` calls with a
/// single-assignment result and immutable arguments. Conjoined onto every VC (the
/// fact is unconditionally true), so a loop body that uses the result only
/// transitively still sees `min(a,b) <= a`. See the section banner for soundness.
/// Recognize a call to the standard-library float `abs` (`f64::abs`/`f32::abs`)
/// and return its IEEE width (64 or 32). CRATE-ORIGIN anchored (`core::`/`std::`/
/// `alloc::`) — mirroring `ord_method`'s std-shape discipline — so a user-defined
/// `mymod::f64::abs` is NOT matched (matching it would inject a false
/// value-definition about an unrelated dest, a false-PROVE). The canonical path
/// is `core::f64::<impl f64>::abs`; integer `i32::abs` (panicking) and the
/// `::math::*` intrinsic delegate are excluded (no `::f64::`/`::f32::` segment).
pub(super) fn fp_abs_call_width(callee: &str) -> Option<u32> {
    let std_origin = callee.starts_with("core::")
        || callee.starts_with("std::")
        || callee.starts_with("alloc::");
    if !std_origin {
        return None;
    }
    let last = callee.rsplit("::").next()?;
    let method = last.split('<').next().unwrap_or(last).trim();
    if method != "abs" {
        return None;
    }
    if callee.contains("::f64::") {
        Some(64)
    } else if callee.contains("::f32::") {
        Some(32)
    } else {
        None
    }
}

/// Global value-definition facts for `dest = arg.abs()` (`f32::abs`/`f64::abs`).
/// abs lowers to a `Terminator::Call` (not an Rvalue), so — like
/// `build_min_max_facts` — we emit the fact `Eq(FpFromBits(dest),
/// FpAbs(FpFromBits(arg)))` GLOBALLY, conjoined onto every VC, gated on
/// single-static-assignment of BOTH the dest and the arg's base local (the bare,
/// unversioned names are only a function-wide invariant when each is assigned
/// once). Fail-closed: any unrecognized/unstable/non-IEEE case emits nothing, so
/// `dest` stays unconstrained (a missed proof, never a false proof).
pub(super) fn build_fp_abs_facts(func: &VerifiableFunction) -> Vec<Formula> {
    if !super::terminator_presence_for(func).has_bare_dest_call {
        return Vec::new();
    }
    let mut facts = Vec::new();
    for block in &func.body.blocks {
        let Terminator::Call { func: callee, args, dest, .. } = &block.terminator else {
            continue;
        };
        if !dest.projections.is_empty() || args.len() != 1 {
            continue;
        }
        // The arg must be a bare, single-static-assignment local: a global fact
        // names it unversioned, so a reassigned arg would make the equality
        // unsound at a later VC site. Projections / constants / Move-of-temp:
        // skip (fail-closed).
        let arg_local = match &args[0] {
            Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => p.local,
            _ => continue,
        };
        if fp_abs_call_width(callee).is_none() {
            continue;
        }
        // Width from the float TYPE is authoritative; skip non-float / non-IEEE.
        let width = match crate::operand_ty_cow(func, &args[0]).as_deref() {
            Some(trust_types::Ty::Float { width }) if *width == 64 || *width == 32 => *width,
            _ => continue,
        };
        if !is_single_static_assignment(func, dest.local)
            || !is_single_static_assignment(func, arg_local)
        {
            continue;
        }
        let dest_name = crate::place_to_var_name(func, dest);
        if let Some(def) = guards::fp_abs_value_def(func, &args[0], &dest_name, width) {
            facts.push(def);
        }
    }
    facts
}

/// Global value-definition facts for `dest = arg.abs()` over a std SIGNED integer
/// (`core::num::<impl i64>::abs`): `dest == if arg < 0 { -arg } else { arg }`, in
/// mathematical integers. The call panics for `arg == MIN` (its own overflow row is
/// charged separately), so wherever `dest` holds a value the equation is exact; and
/// `dest` is otherwise a free symbol the fact cannot use to constrain `arg` (every
/// `arg` has an `|arg|`). Gated exactly like [`build_fp_abs_facts`]: a
/// single-static-assignment `dest` and an argument that is a bare single-assignment
/// local or a checked `l op r` field ([`int_abs_argument_value`]), named unversioned. The receiver must be a std `<impl iN>` path (a user type's
/// `abs` is never matched). Without it `(a - b).abs() + (c - d).abs()` over `i32`
/// casts was refuted with `dx = i64::MAX` (ordsweep2 structs/c02).
pub(super) fn build_int_abs_facts(func: &VerifiableFunction) -> Vec<Formula> {
    if !super::terminator_presence_for(func).has_bare_dest_call {
        return Vec::new();
    }
    let mut facts = Vec::new();
    for block in &func.body.blocks {
        let Terminator::Call { func: callee, args, dest, .. } = &block.terminator else {
            continue;
        };
        if !dest.projections.is_empty()
            || args.len() != 1
            || !matches!(
                &args[0],
                Operand::Copy(p) | Operand::Move(p)
                    if p.projections.is_empty()
                        || matches!(p.projections.as_slice(), [Projection::Field(0)])
            )
            || !matches!(
                crate::local_ty_ref(func, dest.local),
                Some(trust_types::Ty::Int { signed: true, .. })
            )
        {
            continue;
        }
        if !(callee.starts_with("core::") || callee.starts_with("std::"))
            || !callee.contains("::num::")
        {
            continue;
        }
        let last = callee.rsplit("::").next().unwrap_or(callee);
        if last.split('<').next().unwrap_or(last).trim() != "abs"
            || std_num_impl_receiver_width(callee).is_none()
            || std_num_impl_receiver_is_unsigned(callee)
        {
            continue;
        }
        match crate::operand_ty_cow(func, &args[0]).as_deref() {
            Some(trust_types::Ty::Int { signed: true, .. }) => {}
            _ => continue,
        }
        if !is_single_static_assignment(func, dest.local) {
            continue;
        }
        let Some(arg_value) = int_abs_argument_value(func, block.id, &args[0]) else { continue };
        let dest_var = Formula::Var(crate::place_to_var_name(func, dest), Sort::Int);
        let arg_lt = arg_value.clone();
        let arg_neg = arg_value.clone();
        facts.push(Formula::Eq(
            Box::new(dest_var),
            Box::new(Formula::Ite(
                Box::new(Formula::Lt(Box::new(arg_lt), Box::new(Formula::Int(0)))),
                Box::new(Formula::Neg(Box::new(arg_neg))),
                Box::new(arg_value),
            )),
        ));
    }
    facts
}

/// The value an integer `abs` argument denotes, as a formula over single-assignment
/// names: a bare single-assignment local, or field 0 of a single-assignment
/// `CheckedBinaryOp(Add | Sub | Mul, l, r)` temp spelled as `l op r` (a global fact on
/// `_t.0` itself would name nothing: the VC versions that field, see the memory note on
/// statement-versioned checked-op fields). The temp's block must end in the assert
/// trapping its overflow flag with `call_block` as the success target, so the call is
/// reached only when the op did not overflow and `_t.0 == l op r` there.
///
/// Trust: 2026-11-09 (WRAPPING-SUB-AND-INTERVAL-NEG-1, sibling of the wrapping-`Sub`
/// shift-amount bound) — that assert was ASSUMED ("every path to the call passed the
/// op's overflow assert"), not checked. A `CheckedBinaryOp` is also how the lowered
/// `add/sub/mul_with_overflow` intrinsics (`overflowing_*`) appear, with no assert:
/// `.0` is the WRAPPED value, and stating `dest == |l op r|` over mathematical
/// integers for it names a value `dest` never holds (out of `dest`'s type range when
/// the op wrapped, which contradicts that range and makes every later obligation
/// vacuous). Same success-edge check as [`bitcount_receiver_value`].
fn int_abs_argument_value(
    func: &VerifiableFunction,
    call_block: BlockId,
    arg: &Operand,
) -> Option<Formula> {
    let (Operand::Copy(p) | Operand::Move(p)) = arg else { return None };
    let operand_value = |operand: &Operand| -> Option<Formula> {
        match operand {
            Operand::Copy(q) | Operand::Move(q)
                if q.projections.is_empty() && is_single_static_assignment(func, q.local) =>
            {
                Some(Formula::Var(crate::place_to_var_name(func, q), Sort::Int))
            }
            Operand::Constant(_) => crate::chc::operand_to_formula_checked(func, operand).ok(),
            _ => None,
        }
    };
    match p.projections.as_slice() {
        [] if is_single_static_assignment(func, p.local) => {
            Some(Formula::Var(crate::place_to_var_name(func, p), Sort::Int))
        }
        [trust_types::Projection::Field(0)] if is_single_static_assignment(func, p.local) => {
            let def_block = crate::find_local_write_stmt(
                func,
                &func.body.blocks,
                p.local,
                |block, stmt| {
                    matches!(stmt, Statement::Assign { place, .. }
                        if place.local == p.local && place.projections.is_empty())
                    .then_some(block)
                },
            )?;
            let Terminator::Assert {
                cond: Operand::Copy(flag) | Operand::Move(flag),
                expected: false,
                target,
                ..
            } = &def_block.terminator
            else {
                return None;
            };
            if flag.local != p.local
                || !matches!(flag.projections.as_slice(), [trust_types::Projection::Field(1)])
                || *target != call_block
            {
                return None;
            }
            let Rvalue::CheckedBinaryOp(op, l, r) =
                crate::local_defs::unique_value_def(func, p.local)?
            else {
                return None;
            };
            let (l, r) = (operand_value(l)?, operand_value(r)?);
            match op {
                BinOp::Add => Some(Formula::Add(Box::new(l), Box::new(r))),
                BinOp::Sub => Some(Formula::Sub(Box::new(l), Box::new(r))),
                BinOp::Mul => Some(Formula::Mul(Box::new(l), Box::new(r))),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Trust (P0 const-bit-width FALSE PROOF): the RECEIVER's declared bit width read from
/// a std numeric inherent's own callee path — the `<impl iN>` / `<impl uN>` impl-self
/// segment of `core::num::<impl i128>::count_zeros` and its siblings.
///
/// This exists because the OPERAND's type is NOT a trustworthy width source for a
/// bit-count receiver. A width-less `ConstValue::Int` has its width INFERRED FROM ITS
/// VALUE (`operand_ty`: fits `i64` ⇒ width 64), and `Operand::Symbolic` maps `Sort::Int`
/// to width 64 unconditionally — so an `i128`/`u128` receiver whose value happens to fit
/// `i64` reported width 64 while the true bit width is 128.
///
/// `None` (⇒ NO fact) whenever the width cannot be established with certainty: a callee
/// with no decodable impl-self segment, or a receiver type name outside the primitive
/// integer set. `isize`/`usize` answer 64, the pinned target width (`Ty::int_width`);
/// on a narrower target the true width is smaller, so 64 stays a sound over-estimate.
///
/// Anchored under a `core`/`std` root — a nested user module cannot forge the segment
/// into a std-rooted path — which additionally hardens the weak
/// `is_std_num_intrinsic` (`contains("::num::")`) recognizer at every call site: a
/// `core::hostile::num::count_zeros` forgery carries no `<impl …>` and now yields no
/// fact at all. Mirrors `fp_abs_call_width`, which likewise takes its width from the
/// callee path rather than the operand.
pub(super) fn std_num_impl_receiver_width(callee: &str) -> Option<u32> {
    if !(callee.starts_with("core::") || callee.starts_with("std::")) || !callee.contains("::num::")
    {
        return None;
    }
    let at = callee.rfind("<impl ")?;
    let rest = &callee[at + "<impl ".len()..];
    let name = rest.split('>').next()?.trim();
    match name {
        "i8" | "u8" => Some(8),
        "i16" | "u16" => Some(16),
        "i32" | "u32" => Some(32),
        "i64" | "u64" => Some(64),
        "i128" | "u128" => Some(128),
        // Pointer-width integers at the pinned 64-bit target (`Ty::int_width`).
        "isize" | "usize" => Some(64),
        _ => None,
    }
}

/// A formula for the ONE value a bit-count call in `call_block` receives, for the
/// global facts above (which are stated outside any path, so the term must denote
/// that value wherever it is read):
///   * a bare single-assignment local: its bare name;
///   * field 0 of a single-assignment `CheckedBinaryOp(op, a, b)` temp whose block
///     ends in the assert trapping that op's overflow flag with `call_block` as its
///     success target (rustc's `f(x - 1)` shape, sweep r01g): the exact `a op b`,
///     since the call is reached only when the op did not overflow. The temp's
///     field carries a statement-versioned name in the VC, so its bare spelling
///     would constrain nothing; `a` and `b` must be constants or locals whose
///     versions collapse to the bare name.
fn bitcount_receiver_value(
    func: &VerifiableFunction,
    call_block: BlockId,
    receiver: &Operand,
) -> Option<Formula> {
    let (Operand::Copy(recv) | Operand::Move(recv)) = receiver else { return None };
    if !is_single_static_assignment(func, recv.local) {
        return None;
    }
    if recv.projections.is_empty() {
        return Some(Formula::Var(crate::place_to_var_name(func, recv), Sort::Int));
    }
    if !matches!(recv.projections.as_slice(), [trust_types::Projection::Field(0)]) {
        return None;
    }
    let block = crate::find_local_write_stmt(
        func,
        &func.body.blocks,
        recv.local,
        |block, stmt| {
            matches!(stmt, Statement::Assign { place, .. }
                if place.local == recv.local && place.projections.is_empty())
            .then_some(block)
        },
    )?;
    let Terminator::Assert { cond, expected: false, target, .. } = &block.terminator else {
        return None;
    };
    let (Operand::Copy(flag) | Operand::Move(flag)) = cond else { return None };
    if flag.local != recv.local
        || !matches!(flag.projections.as_slice(), [trust_types::Projection::Field(1)])
        || *target != call_block
    {
        return None;
    }
    let (op, a, b) = block.stmts.iter().find_map(|stmt| match stmt {
        Statement::Assign { place, rvalue: Rvalue::CheckedBinaryOp(op, a, b), .. }
            if place.local == recv.local && place.projections.is_empty() =>
        {
            Some((*op, a, b))
        }
        _ => None,
    })?;
    let term = |operand: &Operand| -> Option<Formula> {
        match operand {
            Operand::Constant(_) => operand_const_int(operand).map(Formula::Int),
            Operand::Copy(p) | Operand::Move(p)
                if p.projections.is_empty()
                    && super::discharge::local_versions_collapse_to_bare(func, p.local) =>
            {
                Some(Formula::Var(crate::place_to_var_name(func, p), Sort::Int))
            }
            _ => None,
        }
    };
    let (a, b) = (Box::new(term(a)?), Box::new(term(b)?));
    Some(match op {
        BinOp::Add => Formula::Add(a, b),
        BinOp::Sub => Formula::Sub(a, b),
        _ => return None,
    })
}

/// The callee is a `core::num`/`std::num` inherent method of an UNSIGNED integer
/// (`<impl u32>`, `<impl usize>`, ...), read from the same `<impl T>` segment as
/// [`std_num_impl_receiver_width`].
fn std_num_impl_receiver_is_unsigned(callee: &str) -> bool {
    std_num_impl_receiver_width(callee).is_some()
        && callee.rfind("<impl ").is_some_and(|at| {
            let rest = &callee[at + "<impl ".len()..];
            rest.split('>').next().is_some_and(|name| name.trim().starts_with('u'))
        })
}

/// The bit width to use for a `[0, bits(T)]` bit-count result bound.
///
/// The receiver's DECLARED width (from the callee path — see
/// [`std_num_impl_receiver_width`]) is authoritative and REQUIRED: without it no fact is
/// emitted (fail-closed). The operand's resolved integer width is still demanded, both
/// to keep the pre-existing "receiver must be an integer" gate and so that a path/operand
/// disagreement resolves to the WIDER — hence WEAKER, hence sound — bound rather than to
/// the narrower one that produced the false proof.
///
/// WITNESS (a live false proof before the path became the width source, no negative
/// numbers needed):
/// ```ignore (illustrative)
/// const K: i128 = 1;
/// let n = K.count_zeros();          // truly 127
/// let arr = [0u8; 65];
/// arr[n as usize]                   // "0 <= n <= 64" PROVED in-bounds; really panics
/// ```
fn bitcount_receiver_width(
    func: &VerifiableFunction,
    callee: &str,
    receiver: &Operand,
) -> Option<u32> {
    let declared = std_num_impl_receiver_width(callee)?;
    let operand_width = match crate::operand_ty_cow(func, receiver).as_deref() {
        Some(Ty::Int { width, .. }) => *width,
        _ => return None,
    };
    Some(declared.max(operand_width))
}

/// The largest `ilog2` (`decimal == false`) or `ilog10` (`decimal == true`) of a
/// `bits`-wide integer: `bits - 1`, and the decimal digit count of `2^bits - 1` less
/// one. `None` for any other width.
fn integer_log_max(decimal: bool, bits: u32) -> Option<i128> {
    match (decimal, bits) {
        (false, 8 | 16 | 32 | 64 | 128) => Some(i128::from(bits) - 1),
        (true, 8) => Some(2),
        (true, 16) => Some(4),
        (true, 32) => Some(9),
        (true, 64) => Some(19),
        (true, 128) => Some(38),
        _ => None,
    }
}

/// Global result bounds for value-bounded std intrinsics — each is UNCONDITIONALLY
/// true, so conjoining it everywhere is sound and lets a bounded index discharge:
///   * `n.rem_euclid(c)` for a CONSTANT divisor `c`: the Euclidean remainder is
///     ALWAYS in `[0, |c|-1]` (non-negative, strictly below `|c|`), so
///     `arr[n.rem_euclid(6)]` into `[_; 6]` is in bounds.
///   * `n.{trailing,leading}_zeros()` / `n.count_{ones,zeros}()`: the result is the
///     bit-count of the receiver type, in `[0, bits(T)]` — so `arr[n.count_ones()]`
///     into `[_; bits+1]` is in bounds. These are LINEAR bounds ay discharges
///     directly (unlike an equality contradiction).
pub(super) fn build_intrinsic_bound_facts(func: &VerifiableFunction) -> Vec<Formula> {
    if !super::terminator_presence_for(func).has_bare_dest_call {
        return Vec::new();
    }
    let mut facts = Vec::new();
    for block in &func.body.blocks {
        let Terminator::Call { func: callee, args, dest, .. } = &block.terminator else {
            continue;
        };
        if !dest.projections.is_empty()
            || !matches!(args.len(), 1 | 2)
            || !matches!(
                crate::local_ty_ref(func, dest.local),
                Some(
                    trust_types::Ty::Int { .. }
                        | trust_types::Ty::PtrSizedInt { .. }
                        | trust_types::Ty::Adt { .. }
                )
            )
            || !is_std_num_intrinsic(callee)
        {
            continue;
        }
        let tail = method_tail(callee);
        if !matches!(
            (tail, args.len()),
            ("rem_euclid", 2)
                | (
                    "trailing_zeros"
                        | "leading_zeros"
                        | "count_ones"
                        | "count_zeros"
                        | "ilog2"
                        | "ilog10"
                        | "checked_ilog2"
                        | "checked_ilog10",
                    1
                )
        ) || !is_single_static_assignment(func, dest.local)
        {
            continue;
        }
        let dest_var_formula = Formula::Var(crate::place_to_var_name(func, dest), Sort::Int);
        let dest_var = || dest_var_formula.clone();
        let ge0 = |facts: &mut Vec<Formula>| {
            facts.push(Formula::Ge(Box::new(dest_var()), Box::new(Formula::Int(0))));
        };
        match tail {
            // `rem_euclid(c)` (receiver + divisor): result in `[0, |c|-1]` for `|c| >= 1`.
            "rem_euclid" if args.len() == 2 => {
                if let Some(c) = operand_const_int(&args[1]) {
                    let m = c.unsigned_abs();
                    if let Ok(m) = i128::try_from(m) {
                        if m >= 1 {
                            ge0(&mut facts);
                            facts
                                .push(Formula::Lt(Box::new(dest_var()), Box::new(Formula::Int(m))));
                        }
                    }
                }
            }
            // bit-count intrinsics: result in `[0, bits(receiver_type)]`.
            "trailing_zeros" | "leading_zeros" | "count_ones" | "count_zeros"
                if args.len() == 1 =>
            {
                if let Some(width) = bitcount_receiver_width(func, callee, &args[0]) {
                    ge0(&mut facts);
                    facts.push(Formula::Le(
                        Box::new(dest_var()),
                        Box::new(Formula::Int(width as i128)),
                    ));
                    // Trust (2026-09-29): a NONZERO receiver has at least one set bit,
                    // so its leading and trailing zeros are fewer than `bits`:
                    // `recv == 0 ∨ dest <= bits - 1`. Stated on the receiver's bare
                    // name, so the receiver must hold ONE value for the whole body.
                    // Measured on the ordinary-Rust sweep: `if x == 0 { 0 } else { 63 -
                    // x.leading_zeros() }` and `t[x.trailing_zeros() as usize]` into a
                    // `[_; 64]` under `x != 0` were refuted with the count at `bits`.
                    if matches!(tail, "leading_zeros" | "trailing_zeros")
                        && let Some(recv_var) = bitcount_receiver_value(func, block.id, &args[0])
                    {
                        facts.push(Formula::Or(vec![
                            Formula::Eq(Box::new(recv_var.clone()), Box::new(Formula::Int(0))),
                            Formula::Le(
                                Box::new(dest_var()),
                                Box::new(Formula::Int(width as i128 - 1)),
                            ),
                        ]));
                        // Trust (2026-10-01): for an UNSIGNED receiver `leading_zeros`
                        // is determined by the receiver's magnitude: `lz >= k` exactly
                        // when `recv < 2^(bits-k)`, for each `k` in `1..=bits`. Both
                        // directions are stated, so `lz` takes its one value. A signed
                        // receiver is excluded: a negative value has `lz == 0` while
                        // `recv < 2^(bits-1)` holds. The declared and the operand width
                        // must agree, since the bracket names the exact width; `u128`
                        // is left out (`2^127` is not an `i128` literal).
                        // Measured on the ordinary-Rust sweep (r01g):
                        // `1u32 << (32 - (x - 1).leading_zeros())` under `x <= 1 << 31`
                        // was refuted with `lz = 0` for `x - 1 = 1`.
                        if tail == "leading_zeros"
                            && let Some(declared) = std_num_impl_receiver_width(callee)
                            && declared == width
                            && width <= 64
                            && matches!(
                                crate::operand_ty_cow(func, &args[0]).as_deref(),
                                Some(Ty::Int { signed: false, width: w }) if *w == width
                            )
                            && std_num_impl_receiver_is_unsigned(callee)
                        {
                            for k in 1..=width {
                                let t = Formula::Int(1i128 << (width - k));
                                let k = Formula::Int(i128::from(k));
                                facts.push(Formula::Or(vec![
                                    Formula::Ge(Box::new(recv_var.clone()), Box::new(t.clone())),
                                    Formula::Ge(Box::new(dest_var()), Box::new(k.clone())),
                                ]));
                                facts.push(Formula::Or(vec![
                                    Formula::Lt(Box::new(recv_var.clone()), Box::new(t)),
                                    Formula::Lt(Box::new(dest_var()), Box::new(k)),
                                ]));
                            }
                        }
                    }
                }
            }
            // Trust (2026-09-29): integer logarithms. `ilog2` of any value of a
            // `bits`-wide type is below `bits`, and `ilog10` is at most the number
            // of decimal digits of the type's unsigned MAX, less one (a signed
            // type's MAX is smaller, so the same bound holds). `checked_*` returns
            // the same value in `Some`, so the bound is stated on the `Some`
            // payload; a `None` gives that name no value to contradict. The bare
            // `ilog2`/`ilog10` still panic on a non-positive receiver — that row is
            // not this fact's business. Measured on the ordinary-Rust sweep:
            // `match x.checked_ilog10() { Some(d) => d + 1, None => 1 }` was
            // refuted with `d = u32::MAX`.
            "ilog2" | "ilog10" | "checked_ilog2" | "checked_ilog10" if args.len() == 1 => {
                let method = tail;
                if let Some(width) = bitcount_receiver_width(func, callee, &args[0])
                    && let Some(max) = integer_log_max(method.ends_with("ilog10"), width)
                {
                    let result = if method.starts_with("checked_") {
                        let payload = Place {
                            local: dest.local,
                            projections: vec![
                                trust_types::Projection::Downcast(1),
                                trust_types::Projection::Field(0),
                            ],
                        };
                        Formula::Var(crate::place_to_var_name(func, &payload), Sort::Int)
                    } else {
                        dest_var()
                    };
                    facts.push(Formula::Ge(Box::new(result.clone()), Box::new(Formula::Int(0))));
                    facts.push(Formula::Le(Box::new(result), Box::new(Formula::Int(max))));
                }
            }
            _ => {}
        }
    }
    facts
}

/// Global `dest != 0` facts for `NonZero<T>::get` call destinations.
///
/// `a / d.get()` on a `d: NonZeroU32` is refuted at `d.get() == 0`: the wrapped
/// field's `pattern_type!(u32 is 1..)` is lowered to the bare carrier `u32` by
/// `ty_convert`'s `TyKind::Pat` arm, and `get` is an opaque call, so nothing in
/// the body constrains the destination. Restoring `dest != 0` discharges the
/// divzero/remzero obligation.
///
/// `!= 0` and NOT `>= 1` — `NonZero<T>` is generic over the SIGNED integers too,
/// and `NonZeroI32::get()` may legitimately be negative. The unsigned lower
/// bound needed by e.g. `d.get() - 1` comes from the destination's own declared
/// type range (`conjoin_local_type_ranges`), not from here.
///
/// SOUNDNESS: monotone — a fact true of every DEFINED execution, so it deletes
/// only infeasible counterexamples. It is the `NonZero<T>` validity invariant
/// (holding a zero `NonZero` is immediate UB, exactly as
/// `enum_discriminant_range_preconditions` relies on a validly-constructed
/// enum's tag). Gated on: the crate-origin-anchored recognizer
/// [`is_nonzero_get_call`], arity 1, a bare SINGLE-ASSIGNMENT destination, and an
/// integer-lowered destination (a non-integer dest has no `Sort::Int` var to
/// bind). Any miss yields NO fact — fail-closed to the current free destination.
///
/// THE SINGLE-ASSIGNMENT GATE IS LOAD-BEARING, and NOT because a global fact
/// would stay unversioned. `generate::safety` conjoins this set into
/// `vc.formula` FIRST and only then calls `conjoin_preconditions_versioned_recorded`,
/// which version-renames the WHOLE formula — so the fact is renamed in lockstep
/// with the body and binds the block's TERMINAL version of `dest` EXACTLY,
/// including a version this `get` call never produced. (Preconditions are the
/// contrasting case: they are conjoined bare, AFTER that rename.) On a reassigned
/// dest that exact binding contradicts the divisor-is-zero path condition, the
/// path goes UNSAT, and everything on it is proved vacuously — a false PROVE for
/// a program that faults. `nonzero_get_reassigned_dest_still_refutes` and
/// `nonzero_get_branch_merged_dest_still_refutes` fail when the gate is deleted.
pub(super) fn build_nonzero_get_dest_facts(func: &VerifiableFunction) -> Vec<Formula> {
    if !super::terminator_presence_for(func).has_bare_dest_call {
        return Vec::new();
    }
    let mut facts = Vec::new();
    for block in &func.body.blocks {
        let Terminator::Call { func: callee, args, dest, .. } = &block.terminator else {
            continue;
        };
        if args.len() != 1
            || !dest.projections.is_empty()
            || !matches!(
                crate::local_ty_ref(func, dest.local),
                Some(Ty::Int { .. } | Ty::PtrSizedInt { .. })
            )
            || !is_nonzero_get_call(callee)
            || !is_single_static_assignment(func, dest.local)
        {
            continue;
        }
        let dest_var = Formula::Var(crate::place_to_var_name(func, dest), Sort::Int);
        facts.push(Formula::Not(Box::new(Formula::Eq(
            Box::new(dest_var),
            Box::new(Formula::Int(0)),
        ))));
    }
    facts
}

/// Global facts propagating a NON-NEGATIVE bounded value's upper bound THROUGH an `as uN` cast.
///
/// `let j = i.clamp(lo,hi); arr[j as usize]` / `arr[n.rem_euclid(C) as usize]` leave the access
/// runtime-checked: the source's bound (`j <= hi`, `rem < |C|`) is on a SEPARATE local from the
/// `as usize` cast result, and ay does not model the signed→unsigned cast as an equality, so the
/// bound never transfers. For a source provably in `[0, C]` (`cast_source_const_upper_nonneg`:
/// const clamp `[lo,hi]` with `lo>=0`, `rem_euclid` `[0,|C|-1]`, bit-counts `[0, width]` — all
/// NON-NEGATIVE), `src as uN = src mod 2^N <= C` holds UNCONDITIONALLY (truncation only lowers;
/// `src>=0` rules out the negative→huge wrap). Emit the GLOBAL fact `(src as uN) <= C`; it
/// discharges the access whenever `C < arr.len()` (via the incompatible-const-bounds discharge:
/// `(cast)<=C ∧ (cast)>=len` is UNSAT when `C < len`). ONLY the upper bound (a lower bound is
/// unsound under truncation; a usize index needs none) — SELF-LIMITING: a `C >= len` source
/// (genuine OOB) leaves compatible bounds and stays runtime-checked.
///
/// SOUNDNESS GATES (any miss → no fact):
///   * the cast SOURCE has a recognized const non-negative upper bound (above);
///   * the target type is an UNSIGNED integer (a signed target re-introduces the sign-bit edge);
///   * BOTH the source and the cast dest are single-static-assignment — so neither is reassigned
///     NOR mutably borrowed after the def (the hunt-5/7/8 staleness gate: a `let p=&mut j; *p=huge`
///     between def and cast would otherwise leave a stale `src as usize <= C`;
///     `is_single_static_assignment` kills on any `Ref{mutable}`/`AddressOf`).
pub(super) fn build_cast_bound_facts(func: &VerifiableFunction) -> Vec<Formula> {
    let mut facts = Vec::new();
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            let Statement::Assign { place: cast_dst, rvalue: Rvalue::Cast(operand, to_ty), .. } =
                stmt
            else {
                continue;
            };
            if !cast_dst.projections.is_empty() || !(to_ty.is_integer() && !to_ty.is_signed()) {
                continue;
            }
            let (Operand::Copy(src_p) | Operand::Move(src_p)) = operand else { continue };
            if !src_p.projections.is_empty() || crate::local_defs::is_parameter(func, cast_dst.local)
            {
                continue;
            }
            let is_bool_src = crate::operand_ty_cow(func, operand)
                .is_some_and(|t| matches!(t.as_ref(), Ty::Bool));
            if !is_bool_src
                && (!super::terminator_presence_for(func).has_bare_dest_call
                    || crate::local_defs::is_parameter(func, src_p.local)
                    || crate::local_defs::unique_value_def(func, src_p.local).is_some())
            {
                continue;
            }
            // Staleness: both the source value and the cast result are single-assignment
            // (and neither is mutably borrowed — SSA kills on Ref{mutable}/AddressOf).
            if !is_single_static_assignment(func, src_p.local)
                || !is_single_static_assignment(func, cast_dst.local)
            {
                continue;
            }
            // A `bool` source casts to `{0, 1}` — a total theorem (a `bool` is 0 or
            // 1, so `bool as <uint>` ≤ 1). Attaching this upper bound lets sums of
            // flag/edge counts — `(a != b) as u32 + (b != c) as u32 + …` — discharge
            // their arithmetic-overflow VCs; without it the cast result was unbounded
            // and the sum spuriously refuted (over-refutation audit: body cast
            // semantics). SOUND: the SSA gate above pins the bool's single definition,
            // and every `bool` value is 0 or 1 by construction. Otherwise fall back to
            // the const-upper-bounded producers (clamp / rem_euclid / bit-count).
            let hi = if is_bool_src {
                1
            } else {
                match cast_source_const_upper_nonneg(func, src_p.local) {
                    Some(h) => h,
                    None => continue,
                }
            };
            let cast_var = Formula::Var(crate::place_to_var_name(func, cast_dst), Sort::Int);
            facts.push(Formula::Le(Box::new(cast_var), Box::new(Formula::Int(hi))));
        }
    }
    facts
}

/// The constant LOWER bound `C` of a call defining `local` whose result is provably
/// `>= C` for ALL inputs, where the carry across a value-preserving widening cast is
/// SOUND: `max(v, C)` is `>= C` unconditionally (`max(v, C) >= C` is a total Ord
/// theorem), so for a value-preserving widening `(max(v,C) as uWider) >= C`. Only
/// `Ord::max(v, c)` with a CONSTANT `c` argument is recognized — the bound is the
/// (largest) constant operand. None for any other call.
///
/// Restricted to a const operand `c` (not a symbolic one) so the emitted bound is a
/// concrete `Ge(cast, c)`; `min`/`clamp` are NOT lower-bound producers in the sense
/// needed here (`min(v,c) <= c` is an UPPER bound, `clamp` lower bound `lo` is already
/// covered by the upper-bound path when relevant) so they are excluded.
pub(super) fn cast_source_const_lower(func: &VerifiableFunction, local: usize) -> Option<i128> {
    if !super::terminator_presence_for(func).has_bare_dest_call {
        return None;
    }
    crate::find_local_write_term(func, &func.body.blocks, local, |_block, term| {
        if let Terminator::Call { func: callee, args, dest, .. } = term
            && dest.local == local
            && dest.projections.is_empty()
        {
            // NAME-ANCHOR-2: core's `max` only (a primitive integer `Self`).
            if primitive_int_ord_method(func, callee, args, dest) == Some("max") && args.len() == 2
            {
                // `max(v, c) >= c` for the const operand `c`; if BOTH are const, the
                // result is `>= max(c1, c2)` — take the largest const operand.
                let mut best: Option<i128> = None;
                for arg in args {
                    if let Some(c) = operand_const_int(arg) {
                        best = Some(best.map_or(c, |b: i128| b.max(c)));
                    }
                }
                return Some(best);
            }
            return Some(None);
        }
        None
    })
    .flatten()
}

/// Global facts propagating a DYNAMIC LOWER bound of a `max`-with-const source THROUGH
/// a value-preserving widening `as uN` cast: `let n = v.max(C) as u64; h % n`. The
/// `.max(C)` result is `>= C` unconditionally, and a value-preserving widening cast is
/// the IDENTITY on the value, so `(v.max(C) as uWider) >= C` holds UNCONDITIONALLY.
/// Emit the GLOBAL fact `(cast) >= C`, keyed on the CAST DEST var name — which carries
/// e.g. `n >= 1` from `num_partitions.max(1) as u64`, discharging the Rem-by-zero
/// obligation on `h % n` (the divisor is provably non-zero).
///
/// SOUNDNESS GATES (mirror [`build_cast_bound_facts`] EXACTLY — any miss → no fact):
///   * the cast SOURCE is a `max(v, C)` with a CONSTANT operand `C`
///     (`cast_source_const_lower`); `max(v, C) >= C` is a total Ord theorem;
///   * the cast is a VALUE-PRESERVING widening (`is_modeled_identity_cast` of the
///     source/target int types: same width+signedness, or a widening that is NOT
///     signed→unsigned) — so the cast is the identity on the value and the lower
///     bound is preserved; a narrowing/reinterpret/signed→unsigned widening could
///     change the value and is EXCLUDED;
///   * BOTH the source and the cast dest are single-static-assignment — so neither is
///     reassigned NOR mutably borrowed after the def (the SSA staleness gate; a `&mut`
///     reassign of the source between `.max(C)` and the cast would otherwise leave a
///     stale `(cast) >= C`). `is_single_static_assignment` kills on `Ref{mutable}`/
///     `AddressOf`.
/// LOWER bound ONLY (the dual of `build_cast_bound_facts`' upper-bound-only rule): no
/// upper bound is claimed here (the source has none), and the fact is unconditionally
/// true, so it can only ever HELP discharge a real obligation, never false-prove.
pub(super) fn build_cast_lower_bound_facts(func: &VerifiableFunction) -> Vec<Formula> {
    if !super::terminator_presence_for(func).has_bare_dest_call {
        return Vec::new();
    }
    let mut facts = Vec::new();
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            let Statement::Assign { place: cast_dst, rvalue: Rvalue::Cast(operand, to_ty), .. } =
                stmt
            else {
                continue;
            };
            if !cast_dst.projections.is_empty() || crate::local_defs::is_parameter(func, cast_dst.local)
            {
                continue;
            }
            let (Operand::Copy(src_p) | Operand::Move(src_p)) = operand else { continue };
            if !src_p.projections.is_empty()
                || crate::local_defs::is_parameter(func, src_p.local)
                || crate::local_defs::unique_value_def(func, src_p.local).is_some()
            {
                continue;
            }
            // Value-preserving widening only — the cast must be the IDENTITY on the
            // value for the source lower bound to carry. Narrowing / signed→unsigned
            // widening / reinterpret change the value and are excluded.
            // verifier-perf: borrow the declared type (no fat-root clone) — only inspected.
            let Some(from_ty) = crate::local_ty_ref(func, src_p.local) else { continue };
            if !crate::is_modeled_identity_cast(from_ty, to_ty) {
                continue;
            }
            // Staleness: both the source value and the cast result are single-assignment
            // (and neither is mutably borrowed — SSA kills on Ref{mutable}/AddressOf).
            if !is_single_static_assignment(func, src_p.local)
                || !is_single_static_assignment(func, cast_dst.local)
            {
                continue;
            }
            let Some(lo) = cast_source_const_lower(func, src_p.local) else { continue };
            let cast_var = Formula::Var(crate::place_to_var_name(func, cast_dst), Sort::Int);
            facts.push(Formula::Ge(Box::new(cast_var), Box::new(Formula::Int(lo))));
        }
    }
    facts
}

/// The constant upper bound `C` of a call defining `local` whose result is a known
/// NON-NEGATIVE value bounded by `C` — so `local as uN` is value-preserving and
/// `(local as uN) <= C` holds (truncation only lowers). Recognizes:
///   * `Ord::clamp(v, lo, hi)` with const `0 <= lo <= hi` → `hi` (a negative `lo` or
///     `lo > hi` is excluded: the former admits a negative source, the latter PANICS);
///   * `n.rem_euclid(c)` with `|c| >= 1` → `|c| - 1` (euclidean remainder is always in
///     `[0, |c|-1]`, REGARDLESS of the sign of `n` — the exact case the unsigned `n % c`
///     already proves but a SIGNED `n.rem_euclid(c) as usize` did not);
///   * `trailing_zeros`/`leading_zeros`/`count_ones`/`count_zeros` on a width-`w` integer
///     → `w` (result in `[0, w]`).
/// None for any other call (unknown bound — fail open, never a wrong fact).
pub(super) fn cast_source_const_upper_nonneg(
    func: &VerifiableFunction,
    local: usize,
) -> Option<i128> {
    if !super::terminator_presence_for(func).has_bare_dest_call {
        return None;
    }
    crate::find_local_write_term(func, &func.body.blocks, local, |_block, term| {
        if let Terminator::Call { func: callee, args, dest, .. } = term
            && dest.local == local
            && dest.projections.is_empty()
        {
            // NAME-ANCHOR-2: core's `clamp` only (a primitive integer `Self`).
            if primitive_int_ord_method(func, callee, args, dest) == Some("clamp")
                && args.len() == 3
            {
                let Some(lo) = operand_const_int(&args[1]) else { return Some(None) };
                let Some(hi) = operand_const_int(&args[2]) else { return Some(None) };
                return Some((0 <= lo && lo <= hi).then_some(hi));
            }
            if is_std_num_intrinsic(callee)
                && method_tail(callee) == "rem_euclid"
                && args.len() == 2
            {
                let Some(c) = operand_const_int(&args[1]) else { return Some(None) };
                let Ok(m) = i128::try_from(c.unsigned_abs()) else { return Some(None) };
                return Some((m >= 1).then_some(m - 1));
            }
            if matches!(
                method_tail(callee),
                "trailing_zeros" | "leading_zeros" | "count_ones" | "count_zeros"
            ) && args.len() == 1
                && is_std_num_intrinsic(callee)
            {
                // Width from the RECEIVER'S DECLARED TYPE via the callee path — see
                // `bitcount_receiver_width`. This propagates the same bound through the
                // `as usize` cast, so a value-inferred width here would carry the
                // identical false proof one hop further.
                return Some(bitcount_receiver_width(func, callee, &args[0]).map(i128::from));
            }
            return Some(None);
        }
        None
    })
    .flatten()
}

/// The constant upper bound of a `min(a, b)` call whose dest is `local`:
/// `min(a, b) <= c` for any const argument `c` (the result is at most the
/// smaller operand). None unless `local` is the dest of a 2-arg ordered-min
/// call with at least one constant argument.
pub(super) fn min_call_const_upper_bound(func: &VerifiableFunction, local: usize) -> Option<i128> {
    if !super::terminator_presence_for(func).has_bare_dest_call {
        return None;
    }
    crate::find_local_write_term(func, &func.body.blocks, local, |_block, term| {
        if let Terminator::Call { func: callee, args, dest, .. } = term
            && dest.local == local
            && dest.projections.is_empty()
            // NAME-ANCHOR-2: core's `min` only (a primitive integer `Self`).
            && primitive_int_ord_method(func, callee, args, dest) == Some("min")
            && args.len() == 2
        {
            let mut best: Option<i128> = None;
            for arg in args {
                if let Some(c) = operand_const_int(arg) {
                    best = Some(best.map_or(c, |b: i128| b.min(c)));
                }
            }
            return Some(best);
        }
        None
    })
    .flatten()
}

/// Trust (clamp-via-helper, whole-crate summary): the constant UPPER bound this
/// function's return value provably satisfies, or None. SOUND by construction —
/// only Some(b) when EITHER every return site is a constant
/// (`function_return_const_sites`: the bound is the largest one) OR the return
/// local (`_0`) is single-assigned (directly, or through a unique whole-local
/// move/copy chain) from a const-bounded producer (clamp / rem_euclid /
/// bit-count via `cast_source_const_upper_nonneg`, or `min`-with-const). A
/// multi-assigned return whose sites are not all constants — distinct unknown
/// values on different paths — yields None (no summary; the call result stays
/// runtime-checked at use sites). The bound is always >= 0, so it discharges an
/// unsigned index use `arr[helper(..)]` when `bound < arr.len()`.
pub(super) fn function_return_const_upper_bound(func: &VerifiableFunction) -> Option<i128> {
    let expanded = func.with_tail_calls_expanded();
    let func = expanded.as_ref();
    let _func_scope = super::FuncAnalysisScope::enter(func);
    // Trust (2026-10-03): the value-join interval of `_0` is a second, independent
    // sound bound (see `local_value_const_interval`); keep the tighter of the two.
    let join = local_value_const_interval(func, 0).map(|(_, hi)| hi).filter(|&hi| hi >= 0);
    match (function_return_const_upper_bound_chain(func), join) {
        (Some(a), Some(b)) => Some(a.min(b)),
        (a, b) => a.or(b),
    }
}

fn function_return_const_upper_bound_chain(func: &VerifiableFunction) -> Option<i128> {
    // Multi-return-site const shape: every return site is a constant, so the
    // LARGEST one bounds the returned value on every path. Same `>= 0` filter
    // as the SSA chain below — preserving the documented "bound is always
    // >= 0" invariant this summary's consumers rely on.
    if let Some(consts) = function_return_const_sites(func) {
        let b = *consts.last()?; // sorted ascending — the max
        return (b >= 0).then_some(b);
    }
    // The return local is `_0`. Trace it through unique whole-local move/copy
    // defs (`_0 = move _k`) to the producing local. Each hop requires single
    // assignment so the traced local's bound is THE bound on every path.
    let mut local = 0usize;
    let mut ssa_verified = false;
    for _ in 0..8 {
        if crate::local_defs::is_parameter(func, local)
            || !is_single_static_assignment(func, local)
        {
            return None;
        }
        match crate::local_defs::unique_value_def(func, local) {
            Some(Rvalue::Use(Operand::Move(p) | Operand::Copy(p))) if p.projections.is_empty() => {
                local = p.local;
            }
            _ => {
                ssa_verified = true;
                break;
            }
        }
    }
    if !ssa_verified
        && (crate::local_defs::is_parameter(func, local)
            || !is_single_static_assignment(func, local))
    {
        return None;
    }
    let b = cast_source_const_upper_nonneg(func, local)
        .or_else(|| min_call_const_upper_bound(func, local))?;
    (b >= 0).then_some(b)
}

/// Trust (const-return summary): the sorted, deduplicated set of integer
/// constants this function can RETURN, provided EVERY write that can define the
/// return local `_0` is a whole-local `_0 = const c` assignment. This is the
/// multi-return-site complement of the single-SSA chain in
/// [`function_return_const_upper_bound`]: a `match`-shaped helper
/// (`match g { 0 => 1, 1 => 2, _ => 4 }`) assigns `_0` a distinct constant per
/// arm, so `is_single_static_assignment(_0)` correctly refuses it — yet on
/// every path that reaches `Return`, `_0` holds the last constant written along
/// that path, which is a member of the collected set. FAIL-CLOSED None on:
///   * any non-const or projected write of `_0` (unknown value on some path);
///   * any `Call` terminator whose dest is `_0` — the written value is the
///     CALLEE's, invisible to this scan. This is also what refuses RECURSION
///     and calls the summary cannot see: a `_0 = f(..)` return site is a call
///     dest, so a self- or cross-call return path yields None;
///   * any `&mut _0` / `&raw _0` (`Rvalue::Ref{mutable}` / `AddressOf`) — a
///     write through the borrow would bypass this def scan (the exact staleness
///     kill `is_single_static_assignment` applies, hunt skeptic #2);
///   * any `SetDiscriminant`/`Deinit` of `_0`, or any `Intrinsic`/`Unsupported`
///     statement anywhere in the body — write channels this scan cannot model
///     (strictly MORE conservative than the SSA chain, which leaves those to
///     the separate fail-closed `UnsupportedMir` lane);
///   * no const write at all (nothing returned / non-int return type).
/// PANIC PATHS need no exclusion — the same argument the upper-bound summary
/// relies on: a diverging path never executes `Return`, so a claim about the
/// RETURNED value is vacuously true there, and the call-site fact is threaded
/// only to the call's SUCCESS target by `build_semantic_guard_map` (an unwind
/// edge never sees it).
pub(super) fn function_return_const_sites(func: &VerifiableFunction) -> Option<Vec<i128>> {
    let expanded = func.with_tail_calls_expanded();
    let func = expanded.as_ref();

    let mut consts: Vec<i128> = Vec::new();
    let poisoned =
        crate::any_local_write_candidate(func, &func.body.blocks, 0, |block, item| match item {
            Some(stmt) => match stmt {
                Statement::Assign { place, rvalue, .. } => {
                    if let Rvalue::Ref { mutable: true, place: borrowed }
                    | Rvalue::AddressOf(_, borrowed) = rvalue
                        && borrowed.local == 0
                    {
                        return true;
                    }
                    if place.local != 0 {
                        return false;
                    }
                    if !place.projections.is_empty() {
                        return true;
                    }
                    let Rvalue::Use(op) = rvalue else {
                        return true;
                    };
                    let Some(c) = operand_const_int(op) else {
                        return true;
                    };
                    consts.push(c);
                    false
                }
                Statement::SetDiscriminant { place, .. } | Statement::Deinit { place } => {
                    place.local == 0
                }
                // Opaque write channels — cannot see what they define.
                Statement::Intrinsic { .. } | Statement::Unsupported { .. } => true,
                _ => false,
            },
            None => matches!(&block.terminator, Terminator::Call { dest, .. } if dest.local == 0),
        });
    if poisoned || consts.is_empty() {
        return None;
    }
    consts.sort_unstable();
    consts.dedup();
    Some(consts)
}

/// The constant LOWER bound of a call defining `local` whose result is provably
/// `>= c` for ALL inputs — the lower-direction mirror of
/// [`min_call_const_upper_bound`] and [`cast_source_const_upper_nonneg`], with
/// the same fail-closed shape (None for any unrecognized call — never a wrong
/// fact). Recognized producers, each a total theorem:
///   * `Ord::max(a, b)` with a const operand `c` → `c` (`max(v, c) >= c`
///     unconditionally; with BOTH const, the largest — the result is
///     `>= max(c1, c2)`);
///   * `Ord::clamp(v, lo, hi)` with const `0 <= lo <= hi` → `lo` (the IDENTICAL
///     gate the upper direction uses: `lo <= hi` rules out clamp's `lo > hi`
///     panic, so `result >= lo` holds on every completed call; `0 <= lo` is
///     kept so both directions recognize the same producer set);
///   * `n.rem_euclid(c)` with `|c| >= 1` → `0` (euclidean remainder is
///     non-negative regardless of the sign of `n`);
///   * `trailing_zeros`/`leading_zeros`/`count_ones`/`count_zeros` → `0`.
pub(super) fn ret_call_const_lower_bound(func: &VerifiableFunction, local: usize) -> Option<i128> {
    if !super::terminator_presence_for(func).has_bare_dest_call {
        return None;
    }
    crate::find_local_write_term(func, &func.body.blocks, local, |_block, term| {
        if let Terminator::Call { func: callee, args, dest, .. } = term
            && dest.local == local
            && dest.projections.is_empty()
        {
            // NAME-ANCHOR-2: core's `max`/`clamp` only (a primitive integer `Self`).
            let ord = primitive_int_ord_method(func, callee, args, dest);
            if ord == Some("max") && args.len() == 2 {
                let mut best: Option<i128> = None;
                for arg in args {
                    if let Some(c) = operand_const_int(arg) {
                        best = Some(best.map_or(c, |b: i128| b.max(c)));
                    }
                }
                return Some(best);
            }
            if ord == Some("clamp") && args.len() == 3 {
                let Some(lo) = operand_const_int(&args[1]) else { return Some(None) };
                let Some(hi) = operand_const_int(&args[2]) else { return Some(None) };
                return Some((0 <= lo && lo <= hi).then_some(lo));
            }
            if is_std_num_intrinsic(callee)
                && method_tail(callee) == "rem_euclid"
                && args.len() == 2
            {
                let Some(c) = operand_const_int(&args[1]) else { return Some(None) };
                return Some((c != 0).then_some(0));
            }
            if matches!(
                method_tail(callee),
                "trailing_zeros" | "leading_zeros" | "count_ones" | "count_zeros"
            ) && args.len() == 1
                && is_std_num_intrinsic(callee)
            {
                return Some(match crate::operand_ty_cow(func, &args[0]).as_deref() {
                    Some(Ty::Int { .. }) => Some(0),
                    _ => None,
                });
            }
            return Some(None);
        }
        None
    })
    .flatten()
}

/// Trust (const-return summary): the constant LOWER bound this function's
/// return value provably satisfies for ALL inputs and EVERY return path, or
/// None — the exact mirror of [`function_return_const_upper_bound`], with the
/// same two provable shapes and the same fail-closed discipline:
///   * every return site is a constant (`function_return_const_sites`) — the
///     bound is the SMALLEST one (the `small_den` shape
///     `match g { 0 => 1, 1 => 2, _ => 4 }` returns `>= 1` on every path);
///   * the single-SSA return chain ends at a call whose result is `>= c` by a
///     total theorem (`ret_call_const_lower_bound`).
/// Unlike the upper direction there is no `>= 0` FILTER on the bound: that
/// filter exists because the upper summary's purpose is unsigned-index
/// discharge (`arr[helper(i)]`), where a negative upper bound is useless; a
/// lower bound of any sign is a sound, potentially useful fact (`>= 1`
/// discharges a Rem/Div-by-zero obligation on `h % helper(..)`).
pub(super) fn function_return_const_lower_bound(func: &VerifiableFunction) -> Option<i128> {
    let expanded = func.with_tail_calls_expanded();
    let func = expanded.as_ref();
    let _func_scope = super::FuncAnalysisScope::enter(func);
    // Trust (2026-10-03): the value-join interval's lower end, kept when tighter.
    let join = local_value_const_interval(func, 0).map(|(lo, _)| lo);
    match (function_return_const_lower_bound_chain(func), join) {
        (Some(a), Some(b)) => Some(a.max(b)),
        (a, b) => a.or(b),
    }
}

fn function_return_const_lower_bound_chain(func: &VerifiableFunction) -> Option<i128> {
    if let Some(consts) = function_return_const_sites(func) {
        return consts.first().copied(); // sorted ascending — the min
    }
    // Mirror of the upper chain: trace `_0` through unique whole-local
    // move/copy defs to the producing local, each hop single-assigned.
    let mut local = 0usize;
    let mut ssa_verified = false;
    for _ in 0..8 {
        if crate::local_defs::is_parameter(func, local)
            || !is_single_static_assignment(func, local)
        {
            return None;
        }
        match crate::local_defs::unique_value_def(func, local) {
            Some(Rvalue::Use(Operand::Move(p) | Operand::Copy(p))) if p.projections.is_empty() => {
                local = p.local;
            }
            _ => {
                ssa_verified = true;
                break;
            }
        }
    }
    if !ssa_verified
        && (crate::local_defs::is_parameter(func, local)
            || !is_single_static_assignment(func, local))
    {
        return None;
    }
    ret_call_const_lower_bound(func, local)
}

/// Trust (2026-10-03, docs/issues/2026-10-03-alab-level0-precision-gaps-ranked.md,
/// "same-crate callee return"): a constant interval containing EVERY value `local` can
/// hold, joined over its complete set of value definitions
/// (`local_defs::value_defs`), or `None`.
///
/// Each definition contributes: a constant `c` gives `[c, c]`; a whole-local copy or
/// move recurses into that local; a `Range::next` loop payload with constant bounds
/// (`loop_bounds::loop_var_const_range`, the yield-set fact `start <= v < end`) gives
/// `[start, end - 1]`. ANY other definition (arithmetic, a cast, a field read) makes
/// the whole answer `None`. `value_defs` itself returns `None` for every channel whose
/// value has no `Rvalue`: a parameter's entry value, a call destination (which is also
/// what refuses recursion, self or mutual), a partial write, a mutable or raw alias, an
/// unlocatable write. So the interval is exact over what the local can hold, adds no
/// trusted fact, and fails closed on every channel it cannot see. A copy cycle or
/// running out of fuel is `None`.
///
/// Motivating shape (a3d `argmax_abs`): `let mut best = 0; for k in 1..3 { if .. { best
/// = k } } best` returns a value in `[0, 2]`, which indexes a `[f64; 3]` at the caller;
/// the single-assignment chain above refuses it because `best` is assigned twice.
pub(super) fn local_value_const_interval(
    func: &VerifiableFunction,
    local: usize,
) -> Option<(i128, i128)> {
    fn join(
        func: &VerifiableFunction,
        local: usize,
        fuel: u32,
        visiting: &mut Vec<usize>,
    ) -> Option<(i128, i128)> {
        if fuel == 0 || visiting.contains(&local) {
            return None;
        }
        if let Some((Some(start), end)) = super::loop_bounds::loop_var_const_range(func, local) {
            return (start < end).then_some((start, end - 1));
        }
        let defs = crate::local_defs::value_defs(func, local)?;
        if defs.is_empty() {
            return None;
        }
        visiting.push(local);
        let mut acc: Option<(i128, i128)> = None;
        for (_, rvalue) in defs {
            let interval = match rvalue {
                Rvalue::Use(op @ Operand::Constant(_)) => {
                    let c = operand_const_int(op)?;
                    (c, c)
                }
                Rvalue::Use(Operand::Copy(p) | Operand::Move(p)) if p.projections.is_empty() => {
                    join(func, p.local, fuel - 1, visiting)?
                }
                _ => return None,
            };
            acc = Some(match acc {
                None => interval,
                Some((lo, hi)) => (lo.min(interval.0), hi.max(interval.1)),
            });
        }
        visiting.pop();
        acc
    }
    join(func, local, 8, &mut Vec::new())
}

/// Trust (2026-10-04, monotone counters): one-sided constant bounds on EVERY value
/// `local` can hold, by induction over its writes, or `None` for a side.
///
/// Every definition (`local_defs::value_defs`, complete: it refuses a parameter's
/// entry value, a call destination, a partial write, a mutable or raw alias and an
/// unlocatable write) must be a constant, a whole-local copy, a constant range-loop
/// payload, or the `.0` of a CHECKED `x + d` / `x - d` with a constant `d >= 0` whose
/// defining block ends in rustc's overflow `Assert` on `.1` and whose successful
/// edge dominates EACH contributing `.0` read. Same-block or bypassing reads
/// decline the bound (a plain `BinaryOp`, and an
/// `overflowing_add` whose checked tuple has no such assert, can wrap and refuse). For the LOWER side an
/// add contributes `lower(x) + d` and a subtraction refuses the side; for the UPPER
/// side the reverse. A path that returns to a local already on the stack contributes
/// nothing new: it can only reach the cycle through copies and the side's monotone
/// operation, so (strong induction over the order of the writes) every value it
/// brings is bounded by the other definitions. A side with no non-cyclic definition
/// is `None`.
///
/// Motivating shape (astream_wire `crc32_tables`): `let mut k = 1; while k < 8 {
/// t[k] = t[k - 1] ^ 1; k += 1; }` — `k >= 1` everywhere, so `k - 1` cannot underflow.
pub(super) fn local_value_monotone_bounds(
    func: &VerifiableFunction,
    local: usize,
) -> (Option<i128>, Option<i128>) {
    monotone_counter::bounds(func, local)
}

pub(super) fn summary_candidates(
    funcs: &[VerifiableFunction],
) -> impl Iterator<Item = &VerifiableFunction> {
    // Trust (2026-10-05, SUMMARY-NAME-COLLIDE-1): every lane below keys its
    // summary on `def_path`, and a call site looks it up by its own rendered
    // callee name. A `def_path` two of these bodies share names neither of them:
    // a call to one would be handed the other's facts, and a single pass used to
    // keep whichever body came LAST. So a shared key summarizes nothing, in every
    // lane at once (`summary_key_collisions` has the measured pair and the
    // compiler's crate-wide half of this rule).
    let mut key_count: FxHashMap<&str, usize> = FxHashMap::default();
    for func in funcs {
        *key_count.entry(func.def_path.as_str()).or_default() += 1;
    }
    // These summaries become definitional facts at other call sites. A dead
    // assignment must not hide an unsupported image from the admission gate
    // simply because a particular return-value recognizer ignores that local.
    funcs.iter().filter(move |func| {
        key_count.get(func.def_path.as_str()) == Some(&1) && !func.body.contains_memory_image()
    })
}

/// Trust (2026-10-05, SUMMARY-NAME-COLLIDE-1): the summary KEYS that two or more
/// distinct owners render to — the keys no body-derived summary may be recorded
/// under, because a call site that spells one cannot say which body it runs.
///
/// Each item is `(key, owner)`: a rendered `def_path` and the identity of the
/// item it was rendered from (the compiler passes the `DefId`). The same pair
/// given twice is one owner, not a collision, so a caller may feed one owner
/// from two inventories.
///
/// WHY A KEY CAN BE SHARED. The lanes key on `safe_def_path_str`, which
/// canonicalizes every rendered lifetime to `'_`. rustc keeps two impls apart
/// when their self types differ only in a region under a `for<>` binder (the
/// `coherence_leak_check` future-compatibility case, rust#56105):
/// `impl Tr for W<for<'a> fn(&'a u8) -> &'static u8>` and
/// `impl Tr for W<for<'a> fn(&'a u8) -> &'a u8>` are two impls with two bodies,
/// and both methods render `<k::W<for<'_> fn(&'_ u8) -> &'_ u8> as k::Tr>::get`.
/// MEASURED on the stage 1 of `76a6ea45b2`: with the first `get` returning `x`
/// and the second `1`, the const-set summary `{1}` was recorded under that key,
/// and `get(x) + 1` through the FIRST impl was kernel-certified overflow-free
/// under certify; a binary that called it with `u32::MAX` panicked on the add
/// (`tests/ui/trust/summary_hrtb_impl_name_collision.rs`).
///
/// The extracted bodies alone cannot see every such pair (an owner that is not
/// an extracted `fn` still renders a key a call can spell), which is why the
/// compiler runs this over EVERY local body owner and refuses the result in all
/// of its summary lanes; [`summary_candidates`] applies the same rule to the
/// bodies a lane is given, as the lane's own floor.
pub fn summary_key_collisions<'a, K: Eq + std::hash::Hash>(
    owners: impl IntoIterator<Item = (&'a str, K)>,
) -> FxHashSet<String> {
    let mut owner_of: FxHashMap<&'a str, Option<K>> = FxHashMap::default();
    for (key, owner) in owners {
        match owner_of.entry(key) {
            std::collections::hash_map::Entry::Vacant(slot) => {
                slot.insert(Some(owner));
            }
            std::collections::hash_map::Entry::Occupied(mut slot) => {
                if slot.get().as_ref() != Some(&owner) {
                    slot.insert(None);
                }
            }
        }
    }
    owner_of
        .into_iter()
        .filter(|(_, owner)| owner.is_none())
        .map(|(key, _)| key.to_string())
        .collect()
}

/// Trust (clamp-via-helper): whole-crate map of function name -> constant return
/// upper bound. Computed ONCE at the analysis phase over every local function
/// (see `trust_init_backing_certificates`), then consumed at call sites via the
/// `callee_return_upper_bound` thread-local to discharge a guarded access
/// THROUGH a bounding helper — e.g. `arr[clamp_idx(i)]` where
/// `fn clamp_idx(i: usize) -> usize { i.min(LEN - 1) }`. Sound: only
/// const-certain, single-assigned, non-negative return bounds are recorded; the
/// use-site emission is itself SSA-gated and staleness-versioned.
pub fn compute_return_bound_summaries(funcs: &[VerifiableFunction]) -> FxHashMap<String, i128> {
    let _analysis_memo = crate::gen_work_memo_scope_if_unscoped();
    let mut map = FxHashMap::default();
    for func in summary_candidates(funcs) {
        if let Some(b) = function_return_const_upper_bound(func) {
            // Key on `def_path` (the full `safe_def_path_str`), NOT `name` (the
            // short item name): a call site renders its callee via
            // `func_operand_name` = `safe_def_path_str(def_id)`, so the lookup at
            // `callee_return_upper_bound(callee)` matches `def_path`, not `name`.
            map.insert(func.def_path.clone(), b);
        }
    }
    map
}

/// Trust (const-return summary): whole-crate map of function name -> constant
/// return LOWER bound — the mirror of [`compute_return_bound_summaries`], with
/// the same keying (`def_path`, matching the call site's `func_operand_name`)
/// and the same consumption shape: a call `dest = callee(..)` whose callee has
/// a recorded lower bound `c` licenses the SSA-gated, staleness-versioned fact
/// `dest >= c` at the call site (e.g. `h % small_den(g)` discharges its
/// Rem-by-zero obligation through `small_den(..) >= 1`). Sound: only bounds
/// that hold for EVERY input and EVERY return path are recorded
/// (`function_return_const_lower_bound` fails closed otherwise).
pub fn compute_return_lower_bound_summaries(
    funcs: &[VerifiableFunction],
) -> FxHashMap<String, i128> {
    let _analysis_memo = crate::gen_work_memo_scope_if_unscoped();
    let mut map = FxHashMap::default();
    for func in summary_candidates(funcs) {
        if let Some(b) = function_return_const_lower_bound(func) {
            map.insert(func.def_path.clone(), b);
        }
    }
    map
}

/// Trust (2026-09-30, return-interval summary): whole-crate map of function
/// `def_path` -> the interval its return value lies in on EVERY completed call, as
/// `(lower, upper)`, each side present only when it is tighter than the return
/// type's own range (a side equal to the type range says nothing). Derived by
/// [`crate::abstract_interp::transfer::return_interval`]: the production interval
/// fixpoint over the callee's own body, for every input. Where the recognizers
/// above find nothing, `fn widen(x: u8) -> u32 { x as u32 + 1 }` is `[1, 256]` and
/// `fn index(self) -> usize { self as usize }` over a four-variant enum is
/// `[0, 3]`. Keyed on `def_path` and consumed like its siblings, at a call that
/// reaches the summarized body.
///
/// `overflow_asserts_enforced` is whether this compilation keeps its overflow
/// asserts (`-C overflow-checks`); without them an overflow assert's success edge
/// says nothing, and the checked-result tracking is off.
pub fn compute_return_interval_summaries(
    funcs: &[VerifiableFunction],
    overflow_asserts_enforced: bool,
) -> FxHashMap<String, (Option<i128>, Option<i128>)> {
    let _analysis_memo = crate::gen_work_memo_scope_if_unscoped();
    let mut map = FxHashMap::default();
    for func in summary_candidates(funcs) {
        // A function with an authored contract is used through its contract: a
        // caller relies on what the contract says, not on what the body happens to
        // return (`postcondition_composition_upper_bound_only.rs` pins that a weak
        // `ensures` stays weak). The inferred-return lane draws the same line. The
        // compiler also drops every def whose contract bundle is non-empty, since
        // its extraction for this lane carries none.
        if !func.contracts.is_empty() || !func.postconditions.is_empty() || !func.spec.is_empty() {
            continue;
        }
        let Some(ret_ty) = crate::local_ty_ref(func, 0) else {
            continue;
        };
        let Some(ty_range) = crate::abstract_interp::type_to_interval(ret_ty) else {
            continue;
        };
        let _func_scope = super::FuncAnalysisScope::enter(func);
        let Some(interval) =
            crate::abstract_interp::transfer::return_interval(func, overflow_asserts_enforced)
        else {
            continue;
        };
        let lo = (interval.lo > ty_range.lo).then_some(interval.lo);
        let hi = (interval.hi < ty_range.hi).then_some(interval.hi);
        if lo.is_some() || hi.is_some() {
            map.insert(func.def_path.clone(), (lo, hi));
        }
    }
    map
}

/// Trust (2026-10-01, payload return-interval summary): whole-crate map of function
/// `def_path` -> `(variant, lower, upper)` for a function returning a std
/// `Option<iN>` / `Result<iN, E>`: the payload arm's variant index (`Some` = 1,
/// `Ok` = 0) and the interval its payload lies in on every completed call, each side
/// present only when tighter than the payload type's range. Derived by
/// [`crate::abstract_interp::transfer::return_payload_interval`]; the same contract
/// exclusion as [`compute_return_interval_summaries`], and consumed only at a call
/// that reaches the summarized body, on the payload a caller extracts from that
/// call's own result (`build_payload_interval_guard_map`).
pub fn compute_return_payload_interval_summaries(
    funcs: &[VerifiableFunction],
    overflow_asserts_enforced: bool,
) -> FxHashMap<String, (usize, Option<i128>, Option<i128>)> {
    let _analysis_memo = crate::gen_work_memo_scope_if_unscoped();
    let mut map = FxHashMap::default();
    for func in summary_candidates(funcs) {
        if !func.contracts.is_empty() || !func.postconditions.is_empty() || !func.spec.is_empty() {
            continue;
        }
        let _func_scope = super::FuncAnalysisScope::enter(func);
        let Some((variant, interval, ty_range)) =
            crate::abstract_interp::transfer::return_payload_interval(
                func,
                overflow_asserts_enforced,
            )
        else {
            continue;
        };
        let lo = (interval.lo > ty_range.lo).then_some(interval.lo);
        let hi = (interval.hi < ty_range.hi).then_some(interval.hi);
        if lo.is_some() || hi.is_some() {
            map.insert(func.def_path.clone(), (variant, lo, hi));
        }
    }
    map
}

/// Trust (const-return summary): whole-crate map of function name -> the exact
/// SET of constants the function can return — recorded only when EVERY return
/// site is a constant (`function_return_const_sites`, the same fail-closed scan
/// the two bound summaries build on). STRICTLY STRONGER than the bound pair:
/// `dest ∈ {1, 2, 4}` implies `1 <= dest <= 4` and additionally excludes the
/// interior non-members. Encoded at the call site as the disjunction
/// `dest == c1 ∨ … ∨ dest == ck` (sound: the callee returns one of them on
/// every completed call), keyed on `def_path` like its siblings.
pub fn compute_return_const_set_summaries(
    funcs: &[VerifiableFunction],
) -> FxHashMap<String, Vec<i128>> {
    let _analysis_memo = crate::gen_work_memo_scope_if_unscoped();
    let mut map = FxHashMap::default();
    for func in summary_candidates(funcs) {
        let _func_scope = super::FuncAnalysisScope::enter(func);
        if let Some(consts) = function_return_const_sites(func)
            && consts.len() <= RETURN_CONST_SET_MAX
        {
            map.insert(func.def_path.clone(), consts);
        }
    }
    map
}

/// Trust (2026-09-23, TRUST-10): the whole-crate RETURN SUMMARIES of a same-crate
/// callee, as GLOBAL facts about a local whose ONLY value is that call's result.
///
/// The three summaries above are consumed at the call site by
/// `build_semantic_guard_map` as PATH facts, threaded to the call's success
/// target. A path fact is weakened to nothing at a loop-header join, so it never
/// reaches a loop BODY that reads the result only transitively — the same gap the
/// `min`/`max` global facts were written for. bit-vec 0.9.1's
///
/// ```text
/// fn reverse_bits(byte: u8) -> u8 {
///     let mut result = 0;
///     for i in 0..u8::bits() {                      // <u8 as BitBlock>::bits() == 8
///         result |= ((byte >> i) & 1) << (u8::bits() - 1 - i);
///     }
///     result
/// }
/// ```
///
/// was reported `[shift:right] FAILED` with `_5 = 9, i = 8` and `[overflow:sub]
/// FAILED` with `_17 = 0` — the loop bound and the in-body `u8::bits()` each
/// havocked, although the callee is `fn bits() -> usize { 8 }` in the same crate
/// and its const-set summary `{8}` was recorded. Replayed over all 256 inputs the
/// function never panics: the counterexamples are not executions.
///
/// SOUNDNESS. Each summary holds for EVERY input and EVERY return path of the
/// callee (the computations above fail closed otherwise), so it is a fact about
/// every value the call can produce. It becomes a fact about the LOCAL only when
/// that call is the local's one value on every channel, which is exactly
/// [`crate::local_defs::unique_value_call`]: never a parameter (whose entry
/// definition reaches a path that skips the call), no second call, no `Assign`
/// beside it, no projected/discriminant write, no mutable or raw alias, no
/// unlocatable write. That is the gate `build_min_upper_bound_facts` uses, and it
/// is stricter than the path lane's `is_single_static_assignment`. Under it the
/// fact is true of the value the local holds at every read, including a read in
/// a later loop iteration of a call inside the loop, because every dynamic
/// instance of the one call satisfies the summary. A panicking callee path writes
/// no value and so reaches no read. The facts can only delete counterexamples no
/// execution realises: `for i in 0..nine() { byte >> i }` with `nine() == 9`
/// stays refuted (`i = 8` is a real input), and a local with a second definition
/// gets no fact at all.
///
/// The callee lookup is the same `def_path`-keyed lookup the path lane already
/// makes at the same call sites, so this adds no identity channel; an unknown
/// callee (foreign, generic, recursive, non-constant) has no summary and emits
/// nothing. Integer destinations only, below 128 bits (the 128-bit Int-sorted
/// literal lanes fail closed elsewhere; this does too).
pub(super) fn build_callee_return_summary_facts(func: &VerifiableFunction) -> Vec<Formula> {
    if !super::terminator_presence_for(func).has_bare_dest_call {
        return Vec::new();
    }
    let mut facts = Vec::new();
    // Candidates first, from the terminators alone: a whole-local call
    // destination whose callee HAS a summary. Only those pay for the seam's
    // every-channel write walk, so a body with no summarised callee (the common
    // case) costs one pass over its blocks — or O(1) when no return summaries
    // are installed in the active context.
    let Some(mut candidates) = crate::with_current_callee_summaries(|summaries| {
        if summaries.facts.return_bounds.is_empty()
            && summaries.facts.return_lower_bounds.is_empty()
            && summaries.facts.return_const_sets.is_empty()
        {
            return Vec::new();
        }
        func.body
            .blocks
            .iter()
            .filter_map(|block| match &block.terminator {
                Terminator::Call { func: callee, dest, .. }
                    if dest.projections.is_empty()
                        && (summaries.facts.return_bounds.contains_key(callee.as_str())
                            || summaries.facts.return_lower_bounds.contains_key(callee.as_str())
                            || summaries.facts.return_const_sets.contains_key(callee.as_str())) =>
                {
                    Some(dest.local)
                }
                _ => None,
            })
            .collect::<Vec<usize>>()
    }) else {
        return facts;
    };
    if candidates.is_empty() {
        return facts;
    }
    if candidates.len() > 1 {
        candidates.sort_unstable();
        candidates.dedup();
    }
    for local in candidates {
        let Some(Terminator::Call { func: callee, .. }) =
            crate::local_defs::unique_value_call(func, local)
        else {
            continue;
        };
        let is_narrow_int = match crate::local_ty_ref(func, local) {
            Some(Ty::Int { width, .. }) => *width < 128,
            Some(Ty::PtrSizedInt { .. }) => true,
            _ => false,
        };
        if !is_narrow_int {
            continue;
        }
        let var_formula = Formula::Var(crate::place_to_var_name(func, &Place::local(local)), Sort::Int);
        let var = || var_formula.clone();
        if let Some(bound) = crate::callee_return_upper_bound(callee) {
            facts.push(Formula::Le(Box::new(var()), Box::new(Formula::Int(bound))));
        }
        if let Some(lo) = crate::callee_return_lower_bound(callee) {
            facts.push(Formula::Ge(Box::new(var()), Box::new(Formula::Int(lo))));
        }
        if let Some(consts) = crate::callee_return_const_set(callee) {
            // FAIL CLOSED on an empty set: the membership would be `false`, and a
            // global `false` erases every obligation in the body. The summary never
            // records one (`function_return_const_sites` refuses), but this fact is
            // global, so the guard is local too.
            match consts.as_slice() {
                [] => {}
                [c] => facts.push(Formula::Eq(Box::new(var()), Box::new(Formula::Int(*c)))),
                _ => {
                    let eqs: Vec<Formula> = consts
                        .iter()
                        .map(|c| Formula::Eq(Box::new(var()), Box::new(Formula::Int(*c))))
                        .collect();
                    facts.push(Formula::Or(eqs));
                }
            }
        }
    }
    facts
}

/// Trust (derived trivial-setter summary): the fail-closed recognizer — see
/// [`SetterSummary`] for the soundness argument. ALL gates required; any miss
/// returns `None` (no summary, never a wrong one):
///   * control flow is ONE straight `Goto`-chain from entry to a `Return`
///     covering EVERY block (no `SwitchInt`/`Call`/`Drop`/`Assert`/`Opaque`/
///     `Unreachable`/`Resume` anywhere — no branch can bypass the store, no
///     callee/drop/unwind can run, and an off-chain block cannot hide a write);
///   * exactly ONE value-writing statement in the whole body — the store —
///     with every other statement an allowlisted no-value-effect marker
///     (storage/coverage/counter/nop), so `p` has NO other use;
///   * the store is `(*p) = <operand>` (exactly one `Deref` projection) where
///     `p` is a `&mut Int` PARAMETER of width < 128 (the 128-bit lowering is
///     BV-routed elsewhere; fail closed here);
///   * the operand is a whole (projection-free) DIFFERENT parameter of the
///     exact pointee type, or an integer constant within the pointee's range.
pub(super) fn function_trivial_setter(func: &VerifiableFunction) -> Option<SetterSummary> {
    let expanded = func.with_tail_calls_expanded();
    let func = expanded.as_ref();

    let arg_count = func.body.arg_count;
    if arg_count == 0 || func.body.blocks.is_empty() {
        return None;
    }

    // 1. Straight entry→return goto-chain covering every block.
    let mut chain: FxHashSet<usize> = FxHashSet::default();
    let mut cur = 0usize;
    let mut returned = false;
    for _ in 0..=func.body.blocks.len() {
        if !chain.insert(cur) {
            return None; // goto cycle — never returns
        }
        let block = func.body.blocks.get(cur).filter(|b| b.id.0 == cur)?;
        match &block.terminator {
            Terminator::Goto(t) => cur = t.0,
            Terminator::Return => {
                returned = true;
                break;
            }
            _ => return None,
        }
    }
    if !returned || chain.len() != func.body.blocks.len() {
        return None;
    }

    // 2. Classify every Assign. The pre-optimization (analysis-phase) shape of a
    //    `*p = v` setter is NOT the collapsed single store the optimizer produces
    //    (`(*_1) = _2`); it is:
    //        _3 = copy _2;        // a whole-local temp copy of the param
    //        (*_1) = move _3;     // the deref store
    //        _0 = const ();       // the implicit unit return
    //    So allow, besides the ONE deref store: (a) whole-local copies
    //    `_t = copy/move <local>` (tracked so the store source can be traced
    //    through them), and (b) the return-place unit-const assign `_0 = const ZST`.
    //    Anything else (a second deref store, a projected/computed write, a
    //    call-dest) fails closed.
    let mut store: Option<(&Place, &Rvalue)> = None;
    // whole-local copy chain: dst_local -> src_local (from `_dst = copy/move _src`)
    let mut copy_src: FxHashMap<usize, usize> = FxHashMap::default();
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            match stmt {
                Statement::Assign { place, rvalue, .. } => {
                    // The deref store `(*p) = ..`.
                    if matches!(place.projections.as_slice(), [trust_types::Projection::Deref]) {
                        if store.is_some() {
                            return None; // a second store — not a trivial setter
                        }
                        store = Some((place, rvalue));
                        continue;
                    }
                    if !place.projections.is_empty() {
                        return None; // a projected non-deref write (field store): reject
                    }
                    // A write to a PARAMETER (`v = w`, or `p = q` reseating the
                    // pointer) is not a trivial setter. The copy chain below is
                    // resolved without regard to statement order, and its ambiguity
                    // guard never sees a parameter's entry value (it is not an
                    // `Assign`), so `*p = v; v = w` resolved the stored value to `w`:
                    // `set(&mut a, 5, 9); buf[a]` was PROVED, kernel-certified, and
                    // indexes out of bounds (an adversarial audit, 2026-09-30; the
                    // 2026-09-17 pack proves it too;
                    // `tests/ui/trust/setter_that_rewrites_its_parameter_refused.rs`).
                    if (1..=arg_count).contains(&place.local) {
                        return None;
                    }
                    match rvalue {
                        // A whole-local copy `_dst = copy/move _src`: track it so the
                        // store source can be resolved through the chain.
                        Rvalue::Use(Operand::Copy(q) | Operand::Move(q))
                            if q.projections.is_empty() =>
                        {
                            if copy_src.insert(place.local, q.local).is_some() {
                                return None; // _dst reassigned — ambiguous
                            }
                        }
                        // The implicit unit return `_0 = const ZST` (return place,
                        // zero-sized value) — inert. Any OTHER constant write to a
                        // non-return local is a computed effect ⇒ reject.
                        Rvalue::Use(Operand::Constant(_)) if place.local == 0 => {}
                        _ => return None,
                    }
                }
                Statement::StorageLive(_)
                | Statement::StorageDead(_)
                | Statement::Nop
                | Statement::Coverage
                | Statement::ConstEvalCounter => {}
                _ => return None,
            }
        }
    }
    let (place, rvalue) = store?;

    // 3. The store is `(*p) = <operand>` with `p` a `&mut Int{<128}` parameter.
    if !matches!(place.projections.as_slice(), [trust_types::Projection::Deref]) {
        return None;
    }
    let p = place.local;
    if p < 1 || p > arg_count {
        return None;
    }
    let (width, signed) = match crate::local_ty_ref(func, p)? {
        Ty::Ref { mutable: true, inner } => match inner.as_ref() {
            Ty::Int { width, signed } if (1..128).contains(width) => (*width, *signed),
            _ => return None,
        },
        _ => return None,
    };

    // Resolve a whole-local operand through the copy chain (`_3` <- `_2`) to its
    // root local, bounded by the chain length to avoid a cycle.
    let resolve_root = |mut l: usize| -> usize {
        for _ in 0..=copy_src.len() {
            match copy_src.get(&l) {
                Some(&next) => l = next,
                None => break,
            }
        }
        l
    };

    // 4. The stored operand: a whole DIFFERENT parameter of the exact pointee
    //    type (possibly via the analysis-phase temp copy chain), or a
    //    pointee-range integer constant.
    let src = match rvalue {
        Rvalue::Use(Operand::Copy(q) | Operand::Move(q)) if q.projections.is_empty() => {
            let root = resolve_root(q.local);
            if root >= 1
                && root <= arg_count
                && root != p
                && crate::local_ty_ref(func, root).is_some_and(|ty| {
                    matches!(ty, Ty::Int { width: w, signed: s } if *w == width && *s == signed)
                })
            {
                SetterSrc::Param(root)
            } else {
                return None;
            }
        }
        Rvalue::Use(op @ Operand::Constant(_)) => {
            let c = operand_const_int(op)?;
            let (lo, hi) = int_type_bounds(width, signed);
            if c < lo || c > hi {
                return None;
            }
            SetterSrc::Const(c)
        }
        _ => return None,
    };

    Some(SetterSummary { param_count: arg_count, ptr_param: p, pointee: (width, signed), src })
}

/// Inclusive value range of an integer type (`width < 128` — guarded by every
/// caller; a 128-bit range does not fit `i128`).
pub(super) fn int_type_bounds(width: u32, signed: bool) -> (i128, i128) {
    if signed {
        (-(1i128 << (width - 1)), (1i128 << (width - 1)) - 1)
    } else {
        (0, (1i128 << width) - 1)
    }
}

/// Trust (derived trivial-setter summary): whole-crate map of function
/// def-path -> trivial-setter effect. Keyed on `def_path` like its const-return
/// siblings (matching the call site's `func_operand_name`); computed once at
/// the analysis phase over every local function and consumed at call sites via
/// the `callee_setter_summary` thread-local. Fail-closed by construction: only
/// bodies [`function_trivial_setter`] fully recognizes are recorded.
pub fn compute_trivial_setter_summaries(
    funcs: &[VerifiableFunction],
) -> FxHashMap<String, SetterSummary> {
    let mut map = FxHashMap::default();
    for func in summary_candidates(funcs) {
        if let Some(summary) = function_trivial_setter(func) {
            map.insert(func.def_path.clone(), summary);
        }
    }
    map
}

/// Trust (derived trivial-setter summary, call-site half): the caller local a
/// call argument `Move(_t)`/`Copy(_t)` UNAMBIGUOUSLY mut-borrows — `_t`'s ONE
/// whole-local definition is `&mut <bare local>` and nothing can reseat `_t`.
/// ALL gates required (any miss → `None`, no fact):
///   * no `Call` terminator writes `_t` (a call-returned pointer is opaque);
///   * `_t` is never itself borrowed (`& _t` / `&mut _t` / `&raw _t` could
///     reseat the pointer invisibly);
///   * exactly one whole-local def ([`crate::local_defs::unique_value_def`], which
///     also rejects projected stores), and it is `Ref { mutable: true }` of a
///     PROJECTION-FREE place (a reborrow `&mut *r` / field borrow `&mut s.f`
///     stays fail-closed).
pub(super) fn callsite_unique_mut_borrow_target(
    func: &VerifiableFunction,
    temp: usize,
) -> Option<usize> {
    if crate::local_defs::is_parameter(func, temp) {
        return None;
    }
    let Rvalue::Ref { mutable: true, place } = crate::local_defs::unique_value_def(func, temp)?
    else {
        return None;
    };
    if !place.projections.is_empty() {
        return None;
    }
    for block in &func.body.blocks {
        if let Terminator::Call { dest, .. } = &block.terminator
            && dest.local == temp
        {
            return None;
        }
        for stmt in &block.stmts {
            if let Statement::Assign { rvalue, .. } = stmt
                && let Rvalue::Ref { place, .. } | Rvalue::AddressOf(_, place) = rvalue
                && place.local == temp
            {
                return None;
            }
        }
    }
    Some(place.local)
}

/// Trust (derived trivial-setter summary): the exact, fully-VERSIONED post-call
/// fact of a recognized trivial-setter call terminating `block`, or `None`
/// (fail-closed). Returns `(target_local, Eq(target#s{b}_t, value))`.
///
/// The fact: after `set(&mut a, v)` returns, `a == v` — the callee's single
/// value write stores exactly the value argument (or the summarized constant)
/// through the pointer argument, and the recognizer admits no other effect
/// channel (see [`SetterSummary`]; the recognizer IS the proof, independent of
/// the callee's own verdict).
///
/// VERSIONING (shared by both consuming lanes): the value operand is read at
/// the block TERMINAL — its PRE-call value, which the callee cannot touch (it
/// receives it by value) — and the target is pinned to the terminator marker
/// `s{b}_t`, the SAME token the terminator-aware oracle gives every post-call
/// read of the mut-borrowed target, and name-disjoint from any later
/// reassignment (`version_terminator_dest_fact`). Both sides name one
/// consistent per-execution snapshot, so the fact is TRUE of every execution
/// that continues past this call — sound to conjoin in both the guard-threading
/// (UNSAT ⇒ proved) and the refutation (SAT ⇒ counterexample) polarity.
///
/// ALL call-site gates fail closed (no fact, never a wrong one): exact arity;
/// the ptr actual a whole local whose ONE def is `&mut <bare local>` with no
/// reseat channel ([`callsite_unique_mut_borrow_target`]); the target's
/// declared type EXACTLY the summarized pointee; the value actual a constant or
/// a whole local distinct from both the target (the `set(&mut a, a)` tautology
/// adds nothing) and the borrow temp.
pub(super) fn trivial_setter_callsite_fact(
    sv: &StmtVersionCtx,
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
) -> Option<(usize, Formula)> {
    let (target, fact) = trivial_setter_callsite_fact_unversioned(func, block)?;
    let Formula::Eq(lhs, _) = &fact else {
        return None;
    };
    let target_name = lhs.var_name()?.to_string();
    // `?`: the versioner answers `None` when an argument of this call reads the
    // subject's own name. The setter recognizer already refuses the `set(&mut a,
    // a)` tautology by local (see the value-actual gate above), so this is
    // belt-and-braces on a lane that cannot reach it — kept because the
    // precondition belongs to the CHANNEL, not to each caller's own reasoning.
    Some((target, version_terminator_dest_fact(sv, func, block, &target_name, fact)?))
}

/// The UNVERSIONED trivial-setter post-call fact `(target_local, Eq(target, value))`
/// — the raw form of [`trivial_setter_callsite_fact`] BEFORE `version_terminator_dest_fact`
/// pins the target token. The refute-lane consumer versions it (and its copy-chain
/// links) at the ASSERT use-point via `version_rename_at` instead — the same
/// reaching-def use-point versioning `stmt_defs` rely on, so the target token
/// unifies with the assert formula's own token by construction (a pre-call read
/// gets a different reaching-def token and stays inert, so staleness is still
/// caught). The pre-pinned form's terminator token did NOT match the assert's
/// post-call read token once the trust-ir flip re-versioned the copy, leaving the
/// fact disjoint (the setter-identity fixture's residual).
pub(super) fn trivial_setter_callsite_fact_unversioned(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
) -> Option<(usize, Formula)> {
    let Terminator::Call { func: callee, args, dest, target: Some(_), .. } = &block.terminator
    else {
        return None;
    };
    let setter = crate::callee_setter_summary(callee)?;
    if !crate::call_reaches_summarized_body(&block.terminator) {
        return None;
    }
    if args.len() != setter.param_count {
        return None;
    }
    let ptr_idx = setter.ptr_param.checked_sub(1)?;
    let (Operand::Copy(pp) | Operand::Move(pp)) = args.get(ptr_idx)? else {
        return None;
    };
    if !pp.projections.is_empty() {
        return None;
    }
    let target = callsite_unique_mut_borrow_target(func, pp.local)?;
    if dest.local == target
        || !crate::local_ty_ref(func, target).is_some_and(|ty| {
            matches!(ty, Ty::Int { width, signed } if (*width, *signed) == setter.pointee)
        })
    {
        return None;
    }
    let value = match &setter.src {
        SetterSrc::Const(c) => Formula::Int(*c),
        SetterSrc::Param(j) => match j.checked_sub(1).and_then(|i| args.get(i))? {
            op @ Operand::Constant(_) => Formula::Int(operand_const_int(op)?),
            op @ (Operand::Copy(q) | Operand::Move(q))
                if q.projections.is_empty() && q.local != target && q.local != pp.local =>
            {
                operand_to_formula(func, op)
            }
            _ => return None,
        },
    };
    let target_name = crate::place_to_var_name(func, &Place::local(target));
    Some((target, Formula::Eq(Box::new(Formula::Var(target_name, Sort::Int)), Box::new(value))))
}

/// The MODELED flattened std `Option`/`Result` type gate (the `lower_enum_adt`
/// shape): std enum def-path name + the explicit `__tag` slot + BOTH variant
/// defs present with their real discriminant tags. Returns the matched enum
/// name and its variant defs; `None` for every other type — in particular a
/// USER enum named like `Result` (wrong def-path) or a degraded pre-P4
/// lowering (no variant defs) never matches. Shared by the unwrap
/// panic-freedom receiver gate and the return-discriminant summary so the two
/// recognizers can never drift.
pub(crate) fn modeled_std_enum_shape(ty: &Ty) -> Option<(&str, &[trust_types::VariantDef])> {
    const MODELED: &[(&str, [&str; 2])] = &[
        ("core::option::Option", ["None", "Some"]),
        ("std::option::Option", ["None", "Some"]),
        ("core::result::Result", ["Ok", "Err"]),
        ("std::result::Result", ["Ok", "Err"]),
    ];
    let Ty::Adt { name, fields, variants, .. } = ty else { return None };
    let (_, expected) = MODELED.iter().find(|(p, _)| *p == name.as_str())?;
    (fields.iter().any(|(f, _)| f == "__tag")
        && variants.len() == 2
        && expected.iter().all(|v| variants.iter().any(|vd| vd.name == *v)))
    .then(|| (name.as_str(), variants.as_slice()))
}

/// Trust (return-discriminant summary): every `_0` construction site as
/// `(block ordinal, variant index)` — the enum-construction analogue of
/// [`function_return_const_sites`], with the IDENTICAL fail-closed write-channel
/// discipline. `None` on:
///   * any write of `_0` that is not a whole-local ADT aggregate of the
///     callee's own return enum (`Use`/`Cast`/projected store: an unknown tag
///     on some path; a `variant` out of range: a mis-lowered aggregate);
///   * any `Call` dest `_0` (the tag is the CALLEE's — invisible; this also
///     refuses recursion, exactly like the const-return scan);
///   * any `&mut _0` / `&raw _0` borrow, `SetDiscriminant`/`Deinit` of `_0`,
///     or an `Intrinsic`/`Unsupported` statement anywhere (opaque channels);
///   * no construction site at all.
/// PANIC PATHS need no exclusion — a diverging path never executes `Return`,
/// so a claim about the RETURNED tag is vacuously true there (the same
/// argument on `function_return_const_sites`).
pub(super) fn function_return_variant_sites(
    func: &VerifiableFunction,
    enum_name: &str,
    n_variants: usize,
) -> Option<Vec<(usize, usize)>> {
    let mut sites: Vec<(usize, usize)> = Vec::new();
    let poisoned =
        crate::any_local_write_candidate(func, &func.body.blocks, 0, |block, item| match item {
            Some(stmt) => match stmt {
                Statement::Assign { place, rvalue, .. } => {
                    if let Rvalue::Ref { mutable: true, place: borrowed }
                    | Rvalue::AddressOf(_, borrowed) = rvalue
                        && borrowed.local == 0
                    {
                        return true;
                    }
                    if place.local != 0 {
                        return false;
                    }
                    if !place.projections.is_empty() {
                        return true;
                    }
                    let Rvalue::Aggregate(
                        AggregateKind::Adt { name, variant, active_field: None, .. },
                        _,
                    ) = rvalue
                    else {
                        return true;
                    };
                    if name != enum_name || *variant >= n_variants {
                        return true;
                    }
                    sites.push((block.id.0, *variant));
                    false
                }
                Statement::SetDiscriminant { place, .. } | Statement::Deinit { place } => {
                    place.local == 0
                }
                Statement::Intrinsic { .. } | Statement::Unsupported { .. } => true,
                _ => false,
            },
            None => matches!(&block.terminator, Terminator::Call { dest, .. } if dest.local == 0),
        });
    if poisoned {
        return None;
    }
    (!sites.is_empty()).then_some(sites)
}

/// The ordinal of the FIRST branch point reachable from entry, provided the
/// prefix is a STRAIGHT LINE of `Goto`-terminated blocks (no call that could
/// write state the branch reads, no second decision, no early return). `None`
/// for any other prefix shape — including a `Goto` cycle, which exhausts the
/// step bound.
pub(super) fn entry_prefix_switch_ordinal(func: &VerifiableFunction) -> Option<usize> {
    let mut cur = 0usize;
    for _ in 0..=func.body.blocks.len() {
        let block = func.body.blocks.get(cur).filter(|b| b.id.0 == cur)?;
        match &block.terminator {
            Terminator::Goto(t) => cur = t.0,
            Terminator::SwitchInt { .. } => return Some(cur),
            _ => return None,
        }
    }
    None
}

/// Resolve `op` to a formula denoting a value that is IDENTICAL on every
/// execution and every program point of `func` — the vocabulary a
/// return-discriminant summary may be built from (callee side) or instantiated
/// with (caller side). Exactly three shapes, everything else `None`:
///   * an integer/bool CONSTANT (ground — trivially execution-invariant);
///   * a PINNED parameter, possibly through single-def whole-local copy/move
///     hops: `place_source_is_stable` (no projected store, no slot-write channel —
///     `&mut`, `&raw mut`, `&raw const` of an owned place — no
///     `SetDiscriminant`/`Deinit`) PLUS zero whole-local defs — a
///     parameter is initialized at entry, so ANY body store (statement or call
///     dest, counted by `local_defs::value_count`) would make it two-valued;
///   * a local whose unique stable def is a CONSTANT assignment (`x = const c`
///     — re-executing the def in a loop rewrites the SAME value), folded to
///     that constant.
/// The pinning matters on BOTH sides: the callee's `cond` must read ENTRY
/// parameter values (the values the caller's actuals denote), and a caller
/// actual substituted into the VC must still denote the call-time value at the
/// downstream unwrap block (a reassignable actual could go stale between the
/// two — the S2c staleness class — so it is refused, never versioned here).
pub(super) fn entry_stable_operand_formula(
    func: &VerifiableFunction,
    op: &Operand,
) -> Option<Formula> {
    let ground_const = |f: Formula| matches!(f, Formula::Int(_) | Formula::Bool(_)).then_some(f);
    let (Operand::Copy(p) | Operand::Move(p)) = op else {
        return ground_const(crate::operand_to_formula(func, op));
    };
    if !p.projections.is_empty() {
        return None;
    }
    let mut cur = p.local;
    for _ in 0..8 {
        if !crate::place_source_is_stable(func, cur) {
            return None;
        }
        if (1..=func.body.arg_count).contains(&cur) {
            if !crate::local_defs::never_explicitly_reseated(func, cur) {
                return None;
            }
            return Some(crate::place_to_formula(func, &Place::local(cur)));
        }
        match crate::local_defs::unique_value_def(func, cur) {
            Some(Rvalue::Use(Operand::Copy(q) | Operand::Move(q)))
                if q.projections.is_empty() && q.local != cur =>
            {
                cur = q.local;
            }
            Some(Rvalue::Use(c @ Operand::Constant(_))) => {
                return ground_const(crate::operand_to_formula(func, c));
            }
            _ => return None,
        }
    }
    None
}

/// The unique stable non-copy defining rvalue of `local`, traced through
/// single-def whole-local copy/move hops (the compiler-inserted temp chain).
/// Every hop and the terminus must be `place_source_is_stable`.
pub(super) fn stable_unique_def_through_copies<'a>(
    func: &'a VerifiableFunction,
    local: usize,
) -> Option<&'a Rvalue> {
    let mut cur = local;
    for _ in 0..8 {
        if crate::local_defs::is_parameter(func, cur) || !crate::place_source_is_stable(func, cur) {
            return None;
        }
        match crate::local_defs::unique_value_def(func, cur)? {
            Rvalue::Use(Operand::Copy(q) | Operand::Move(q))
                if q.projections.is_empty() && q.local != cur =>
            {
                cur = q.local;
            }
            rv => return Some(rv),
        }
    }
    None
}

/// A comparison `BinOp` as a `Formula` over already-resolved operands; `None`
/// for every non-comparison op (arithmetic feeding a switch is not a shape the
/// summary models).
pub(super) fn comparison_formula(op: BinOp, lhs: Formula, rhs: Formula) -> Option<Formula> {
    let (l, r) = (Box::new(lhs), Box::new(rhs));
    Some(match op {
        BinOp::Eq => Formula::Eq(l, r),
        BinOp::Ne => Formula::Not(Box::new(Formula::Eq(l, r))),
        BinOp::Lt => Formula::Lt(l, r),
        BinOp::Le => Formula::Le(l, r),
        BinOp::Gt => Formula::Gt(l, r),
        BinOp::Ge => Formula::Ge(l, r),
        _ => return None,
    })
}

/// The dominating entry condition of a TWO-WAY switch as a formula over the
/// callee's pinned parameters, plus the `(true arm, false arm)` block ordinals.
/// Recognized discriminee shapes (each fail-closed via
/// [`entry_stable_operand_formula`]):
///   * a BOOL comparison temp (`_c = Eq(den, 0); switchInt(_c)` — the real
///     `if den == 0` lowering, either polarity via [`comparison_formula`]);
///   * an entry-stable BOOL value itself (`if flag`);
///   * an entry-stable INTEGER discriminee (`match den { 0 => .., _ => .. }`):
///     `cond = (den == v0)` with the explicit target as the true arm.
pub(super) fn switch_cond_and_arms(
    func: &VerifiableFunction,
    discr: &Operand,
    v0: u128,
    t0: usize,
    otherwise: usize,
) -> Option<(Formula, usize, usize)> {
    // Bool-polarity arm split: the explicit `(v0, t0)` edge is taken when the
    // bool discriminee EQUALS v0, so v0 == 0 makes t0 the FALSE arm.
    let bool_arms = |v0: u128| match v0 {
        0 => Some((otherwise, t0)),
        1 => Some((t0, otherwise)),
        _ => None,
    };
    if let Some(f) = entry_stable_operand_formula(func, discr) {
        let is_bool = matches!(&f, Formula::Bool(_))
            || matches!(&f, Formula::Var(_, Sort::Bool) | Formula::SymVar(_, Sort::Bool));
        if is_bool {
            let (t_arm, f_arm) = bool_arms(v0)?;
            return Some((f, t_arm, f_arm));
        }
        let is_int = matches!(&f, Formula::Int(_))
            || matches!(&f, Formula::Var(_, Sort::Int) | Formula::SymVar(_, Sort::Int));
        if !is_int {
            return None;
        }
        let v = i128::try_from(v0).ok()?;
        return Some((Formula::Eq(Box::new(f), Box::new(Formula::Int(v))), t0, otherwise));
    }
    let (Operand::Copy(p) | Operand::Move(p)) = discr else { return None };
    if !p.projections.is_empty() {
        return None;
    }
    let Rvalue::BinaryOp(op, a, b) = stable_unique_def_through_copies(func, p.local)? else {
        return None;
    };
    let fa = entry_stable_operand_formula(func, a)?;
    let fb = entry_stable_operand_formula(func, b)?;
    let cond = comparison_formula(*op, fa, fb)?;
    let (t_arm, f_arm) = bool_arms(v0)?;
    Some((cond, t_arm, f_arm))
}

/// Walk the STRAIGHT-LINE continuation from arm block `start` to `Return` and
/// return the variant of the EXACTLY-ONE `_0` construction site the path
/// passes. `None` (fail-closed) on: a revisited block (a loop), a second
/// branch point (`SwitchInt`), any opaque/diverging terminator (`Opaque`,
/// `Unreachable`, `Resume`, a no-target call — an arm that never returns has
/// no returned tag to summarize), zero sites, or two sites on one path. `Goto`
/// / normally-returning `Call` / `Drop` / `Assert` continuations are allowed
/// AFTER the decision: a panicking call/assert never returns (vacuous), the
/// global site scan already refused every `_0`-writing channel they could
/// carry, and the cond parameters are pinned (never written or `&mut`-borrowed
/// anywhere), so no continuation can invalidate the entry condition.
pub(super) fn arm_single_site_variant(
    func: &VerifiableFunction,
    start: usize,
    sites: &[(usize, usize)],
) -> Option<usize> {
    let mut cur = start;
    let mut seen: FxHashSet<usize> = FxHashSet::default();
    let mut found: Option<usize> = None;
    loop {
        if !seen.insert(cur) {
            return None;
        }
        let block = func.body.blocks.get(cur).filter(|b| b.id.0 == cur)?;
        if let Some((_, v)) = sites.iter().find(|(b, _)| *b == cur) {
            if found.is_some() {
                return None;
            }
            found = Some(*v);
        }
        match &block.terminator {
            Terminator::Goto(t) => cur = t.0,
            Terminator::Call { target: Some(t), .. } => cur = t.0,
            Terminator::Drop { target, .. } => cur = target.0,
            Terminator::Assert { target, .. } => cur = target.0,
            Terminator::Return => return found,
            _ => return None,
        }
    }
}

/// Trust (return-discriminant summary): the [`ReturnDiscSummary`] of one local
/// function, or `None` for EVERY shape outside the two provable grades. See
/// the type docs for the soundness argument; the structural guarantees are:
///   * the return type is the modeled flattened std enum
///     ([`modeled_std_enum_shape`]);
///   * every `_0` write channel is a whole-local aggregate construction site
///     ([`function_return_variant_sites`] fails closed otherwise);
///   * UNCONDITIONAL: all sites construct one variant — the returned value at
///     ANY `Return` is that variant (MIR initializes `_0` before `Return`, and
///     no other write channel exists);
///   * GUARD-CONDITIONED: exactly two distinct-variant sites in distinct
///     blocks, and the WHOLE CFG is `entry --straight-line--> switch -->
///     (armT | armF) --straight-line--> Return` — so every returning execution
///     takes exactly one arm, whose single site fixes the returned tag, and
///     the arm taken is decided by `cond` over ENTRY parameter values (the
///     parameters are pinned: never written, never `&mut`-borrowed).
pub(crate) fn function_return_disc_summary(func: &VerifiableFunction) -> Option<ReturnDiscSummary> {
    let expanded = func.with_tail_calls_expanded();
    let func = expanded.as_ref();

    let ret_ty = crate::local_ty_ref(func, 0)?;
    let (enum_name, variants) = modeled_std_enum_shape(ret_ty)?;
    let _func_scope = super::FuncAnalysisScope::enter(func);
    let sites = function_return_variant_sites(func, enum_name, variants.len())?;
    let params: Vec<String> =
        (1..=func.body.arg_count).map(|i| place_to_var_name(func, &Place::local(i))).collect();
    let enum_name = enum_name.to_string();
    let first_variant = sites[0].1;
    if sites.iter().all(|(_, v)| *v == first_variant) {
        let tag = variants.get(first_variant)?.discriminant;
        return Some(ReturnDiscSummary {
            enum_name,
            params,
            cases: ReturnDiscCases::Unconditional { tag },
        });
    }
    // Two construction sites with distinct variants (in distinct blocks — a
    // double-write block would make "which write returns" order-sensitive).
    let [(blk_a, _), (blk_b, _)] = sites.as_slice() else { return None };
    if blk_a == blk_b {
        return None;
    }
    let sw = entry_prefix_switch_ordinal(func)?;
    let Terminator::SwitchInt { discr, targets, otherwise, .. } = &func.body.blocks[sw].terminator
    else {
        return None;
    };
    let [(v0, t0)] = targets.as_slice() else { return None };
    let (cond, true_arm, false_arm) = switch_cond_and_arms(func, discr, *v0, t0.0, otherwise.0)?;
    // Belt: every free var of `cond` must be a formal — the substitution keys —
    // so instantiation can never leave a callee-internal symbol to capture a
    // same-named caller local (the `postcondition_rebindable` discipline).
    if !trust_types::all_free_variable_names(&cond, &mut |v| params.iter().any(|p| p == v)) {
        return None;
    }
    let vt = arm_single_site_variant(func, true_arm, &sites)?;
    let vf = arm_single_site_variant(func, false_arm, &sites)?;
    if vt == vf {
        // Both arms funnel into ONE shared-tail site — the other site is
        // unreachable, so the returned variant is unconditional after all.
        let tag = variants.get(vt)?.discriminant;
        return Some(ReturnDiscSummary {
            enum_name,
            params,
            cases: ReturnDiscCases::Unconditional { tag },
        });
    }
    Some(ReturnDiscSummary {
        enum_name,
        params,
        cases: ReturnDiscCases::GuardConditioned {
            cond,
            then_tag: variants.get(vt)?.discriminant,
            else_tag: variants.get(vf)?.discriminant,
        },
    })
}

/// Trust (return-discriminant summary): whole-crate map of function def-path ->
/// returned-tag shape — the discriminant sibling of
/// [`compute_return_bound_summaries`], with the same keying (`def_path`,
/// matching the call site's `func_operand_name`) and the same
/// compute-once-per-crate / thread-local-copy consumption discipline. Consumed
/// by the unwrap panic-freedom lane's summary-pinned receiver shape (see
/// `unwrap_panic_freedom_body`); a function outside the two provable grades
/// records nothing (fail-closed).
pub fn compute_return_disc_summaries(
    funcs: &[VerifiableFunction],
) -> FxHashMap<String, ReturnDiscSummary> {
    let _analysis_memo = crate::gen_work_memo_scope_if_unscoped();
    let mut map = FxHashMap::default();
    for func in summary_candidates(funcs) {
        if let Some(s) = function_return_disc_summary(func) {
            map.insert(func.def_path.clone(), s);
        }
    }
    map
}

/// Trust (inferred contract): whole-crate map of function def-path ->
/// bool-pred summary — computed once per crate beside its four siblings.
/// Empty map ⇒ zero behavior change.
pub fn compute_return_bool_pred_summaries(
    funcs: &[VerifiableFunction],
) -> FxHashMap<String, ReturnBoolPredSummary> {
    let _analysis_memo = crate::gen_work_memo_scope_if_unscoped();
    let mut map = FxHashMap::default();
    for func in summary_candidates(funcs) {
        if let Some(s) = function_return_bool_pred_summary(func) {
            map.insert(func.def_path.clone(), s);
        }
    }
    map
}

/// Trust (inferred contract): derive the bool-pred summary from a callee BODY,
/// fail-closed on everything outside two rigid, whole-CFG-proven shapes:
///
///   * Tier 1 — the single-probe body: `bb0: _b = &(*_1); Call probe(_b) ->
///     dest, bbR; …; Return` where the probe is a modeled std
///     `is_some`/`is_none`/`is_ok`/`is_err` on the one pinned `&Enum` param and
///     `_0` is (or is copied from) the probe result on a straight line to the
///     single Return.
///   * Tier 2a — the discriminant-switch body (`matches!(o, Some(_))`):
///     `_d = discriminant(*_1); switch _d [k → bbA] else bbB` where bbA/bbB
///     assign `_0` opposite Bool constants and converge straight-line to
///     Return. Normalized to `==` via the two-variant complement.
///
/// Common gates: exactly one param, `&`(shared)`Enum` of the modeled flattened
/// std shape; the param is pinned (no writes, no `&mut`); `_0: Ty::Bool`;
/// no other calls in the body; every terminator ∈ {the one Call/Switch, Goto,
/// Return}; exactly one Return. SOUNDNESS: the recorded fact is checked
/// against the WHOLE CFG (any unrecognized block/stmt/terminator ⇒ `None`), a
/// shared-ref pointee's tag cannot change during the body, and the summary is
/// derived per-definition with generics erased — the shape gates are
/// instantiation-invariant (the tag layout is the flattened std shape for
/// every instantiation the extractor models).
pub(super) fn function_return_bool_pred_summary(
    func: &VerifiableFunction,
) -> Option<ReturnBoolPredSummary> {
    let expanded = func.with_tail_calls_expanded();
    let func = expanded.as_ref();

    // Common gates. MULTI-PARAM: the predicate subject is param `_1` (enum-first
    // idiom, incl. `&self`); extra params `_2..` are permitted but the body must
    // STILL bind `_0` solely from `_1`'s probe/discriminant. The entry-block
    // dominance gate (find_param_probe / tier2a) rejects any body where an extra
    // param branches into `_0` (`if flag { false } else { o.is_some() }` puts the
    // probe off-entry ⇒ declined), and the census (calls∈{0,1}, one Return)
    // rejects a second call/return an extra param would need — so
    // `ret ⇔ tag(*_1) REL T` holds for ANY values of the extra params.
    if func.body.arg_count < 1 {
        return None;
    }
    let ret_ty = crate::local_ty_ref(func, 0)?;
    if !matches!(ret_ty, Ty::Bool) {
        return None;
    }
    // Whole-CFG hygiene: exactly one non-{Goto, Return, SwitchInt} terminator
    // (the probe Call, if any), exactly one Return.
    let mut calls = 0usize;
    let mut returns = 0usize;
    for block in &func.body.blocks {
        match &block.terminator {
            Terminator::Call { .. } => calls += 1,
            Terminator::Return => returns += 1,
            Terminator::Goto(_) | Terminator::SwitchInt { .. } => {}
            _ => return None,
        }
    }
    if returns != 1 {
        return None;
    }
    let _func_scope = super::FuncAnalysisScope::enter(func);
    // Formal-parameter names at FULL arity — the consumer matches
    // `args.len() == params.len()`, so a multi-param helper only connects at a
    // call of the same arity (the pred actual is `args[pred_param-1]`).
    let make_params = || -> Vec<String> {
        (1..=func.body.arg_count).map(|i| place_to_var_name(func, &Place::local(i))).collect()
    };

    // The predicate SUBJECT may be ANY parameter, not just `_1` — try each in
    // order and return the first that yields a summary. The body probes/switches
    // on exactly ONE param (find_param_probe / tier2a anchor the receiver /
    // discriminant to `pred_local`), so at most one candidate matches; a body
    // probing a DIFFERENT param than `pred_local` fails closed. Subject shape
    // from the param type:
    //   &Enum   -> whole pointee, BY-REFERENCE (probe receiver `&(*p)`)
    //   Enum    -> whole pointee, BY-VALUE (probe receiver `&p`; Copy param)
    //   &Struct -> a modeled-enum FIELD of the pointee (field subject)
    for pred_local in 1..=func.body.arg_count {
        if !unwrap_receiver_local_is_pinned(func, pred_local) {
            continue;
        }
        let Some(param_ty) = crate::local_ty_ref(func, pred_local) else {
            continue;
        };
        let (whole_enum, by_value) = match param_ty {
            Ty::Ref { mutable: false, inner } => (modeled_std_enum_shape(inner), false),
            other => (modeled_std_enum_shape(other), true),
        };
        let found = if let Some((enum_name, variants)) = whole_enum {
            if calls == 1 {
                find_param_probe(func, enum_name, by_value, pred_local).and_then(|probe| {
                    tier1_probe_body_summary_from_probe(
                        func,
                        enum_name,
                        variants,
                        &make_params,
                        pred_local,
                        probe,
                    )
                    .or_else(|| {
                        tier2b_probe_switch_body_summary_from_probe(
                            func,
                            enum_name,
                            variants,
                            &make_params,
                            pred_local,
                            probe,
                        )
                    })
                })
            } else if calls == 0 {
                tier2a_switch_body_summary(
                    func,
                    enum_name,
                    variants,
                    &make_params,
                    by_value,
                    pred_local,
                )
            } else {
                None
            }
        } else if !by_value && calls == 1 {
            // Field subject: a `&Struct` param whose PROBED field is a modeled
            // enum (`fn is_ready(&self) -> bool { self.field.is_some() }`).
            tier1_field_probe_body_summary(func, &make_params, pred_local)
        } else {
            None
        };
        if found.is_some() {
            return found;
        }
    }
    None
}

/// Locate THE probe call (`is_some`/`is_none`/`is_ok`/`is_err` on the modeled
/// enum) whose shared-ref receiver resolves to the param `_1`, and confirm the
/// call block writes neither `_1`/`*_1` nor the result `_0`. Returns the
/// probe's bool dest local, its success block, and the probed variant name.
/// Shared by Tier 1 (result flows straight to `_0`) and Tier 2b (result feeds a
/// switch). Fail-closed on any deviation.
pub(super) fn find_param_probe(
    func: &VerifiableFunction,
    enum_name: &str,
    by_value: bool,
    pred_local: usize,
) -> Option<(usize, BlockId, &'static str)> {
    // SOUNDNESS: the probe must be the ENTRY block so it DOMINATES the Return —
    // every execution binds `_0` from the probe result. A body that branches on
    // an UNRELATED value first (`FLAG || o.is_some()`) puts the probe in a
    // non-entry block behind a bypass arm that stores `_0` a constant; walking
    // only the probe's forward path would then mis-summarize `ret ⇔ tag==T`
    // when `ret` is actually true for a non-`T` tag. Fail-closed on a non-entry
    // probe. (Tier 2b's switch is on the probe RESULT, which still dominates.)
    let call_block = func.body.blocks.first()?;
    let Terminator::Call { func: callee, args, dest, target: Some(target), .. } =
        &call_block.terminator
    else {
        return None;
    };
    let (callee, target) = (callee.as_str(), *target);
    let (probe_paths, probe_variant) = std_option_result_probe_variant(callee)?;
    if !probe_paths.contains(&enum_name) {
        return None;
    }
    // Receiver: the arg passed to the probe must resolve to the param `_1` —
    // passed directly (`is_some(copy _1)`), through bare copy/move hops, or as a
    // shared reborrow temp (`_t = &(*_1)`).
    let Some(Operand::Copy(recv) | Operand::Move(recv)) = args.first() else {
        return None;
    };
    if !recv.projections.is_empty() {
        return None;
    }
    fn chained_to_param(func: &VerifiableFunction, mut local: usize, pred_local: usize) -> bool {
        for _ in 0..4 {
            if local == pred_local {
                return true;
            }
            // SOUNDNESS (aliased reseat, audit r3): an unpinned intermediate has
            // a stale copy def (a `&mut`-alias reseat is invisible to
            // `unique_value_def`), so the receiver could actually point
            // elsewhere and the recorded summary would be WRONG. Require each hop
            // pinned before trusting its def.
            if crate::local_defs::is_parameter(func, local)
                || !unwrap_receiver_local_is_pinned(func, local)
            {
                return false;
            }
            match crate::local_defs::unique_value_def(func, local) {
                Some(Rvalue::Use(Operand::Copy(p) | Operand::Move(p)))
                    if p.projections.is_empty() =>
                {
                    local = p.local;
                }
                _ => return false,
            }
        }
        local == pred_local
    }
    // The probe's `&self` receiver borrows the SUBJECT: for a `&Enum` param
    // that is `*_1` (`&(*_1)`, or `_1` passed directly / via copy-hops since
    // `_1` is already a shared ref); for a BY-VALUE `Enum` param it is the whole
    // param `&_1` (referent `_1`, no projection).
    // The reborrow temp whose `&(*_1)`/`&_1` def we trust must itself be PINNED
    // (a `&mut`-reseated temp has a stale borrow def — audit r3 class).
    let receiver_ok = if by_value {
        !crate::local_defs::is_parameter(func, recv.local)
            && unwrap_receiver_local_is_pinned(func, recv.local)
            && matches!(
                crate::local_defs::unique_value_def(func, recv.local),
                Some(Rvalue::Ref { mutable: false, place: referent })
                    if referent.local == pred_local && referent.projections.is_empty()
            )
    } else {
        chained_to_param(func, recv.local, pred_local)
            || (!crate::local_defs::is_parameter(func, recv.local)
                && unwrap_receiver_local_is_pinned(func, recv.local)
                && matches!(
                    crate::local_defs::unique_value_def(func, recv.local),
                    Some(Rvalue::Ref { mutable: false, place: referent })
                        if referent.local == pred_local
                            && referent.projections.as_slice()
                                == [trust_types::Projection::Deref]
                ))
    };
    if !receiver_ok {
        return None;
    }
    // The call block's own statements may set up the receiver but must NOT write
    // the subject param (or its deref) or the result `_0`. Storage annotations
    // carry no data effect and are skipped.
    for stmt in &call_block.stmts {
        match stmt {
            Statement::StorageLive(_) | Statement::StorageDead(_) => {}
            Statement::Assign { place, .. } if place.local != 0 && place.local != pred_local => {}
            _ => return None,
        }
    }
    if !dest.projections.is_empty() {
        return None;
    }
    Some((dest.local, target, probe_variant))
}

/// Walk a straight-line chain of blocks that assigns `_0` a single Bool
/// constant and converges on a Return, skipping storage annotations. `None` if
/// the arm does anything else. Shared by Tier 2a and Tier 2b.
pub(super) fn straight_line_bool_arm(func: &VerifiableFunction, start: BlockId) -> Option<bool> {
    let mut cur = start;
    let mut value: Option<bool> = None;
    for _ in 0..8 {
        let block = func.body.blocks.get(cur.0)?;
        for stmt in &block.stmts {
            match stmt {
                Statement::StorageLive(_) | Statement::StorageDead(_) => continue,
                Statement::Assign {
                    place,
                    rvalue: Rvalue::Use(Operand::Constant(trust_types::ConstValue::Bool(b))),
                    ..
                } if place.local == 0 && place.projections.is_empty() && value.is_none() => {
                    value = Some(*b);
                }
                _ => return None,
            }
        }
        match &block.terminator {
            Terminator::Goto(next) => cur = *next,
            Terminator::Return => return value,
            _ => return None,
        }
    }
    None
}

/// Tier 1 of [`function_return_bool_pred_summary`].
pub(super) fn tier1_probe_body_summary(
    func: &VerifiableFunction,
    enum_name: &str,
    variants: &[trust_types::VariantDef],
    make_params: &impl Fn() -> Vec<String>,
    by_value: bool,
    pred_local: usize,
) -> Option<ReturnBoolPredSummary> {
    let probe = find_param_probe(func, enum_name, by_value, pred_local)?;
    tier1_probe_body_summary_from_probe(func, enum_name, variants, make_params, pred_local, probe)
}

fn tier1_probe_body_summary_from_probe(
    func: &VerifiableFunction,
    enum_name: &str,
    variants: &[trust_types::VariantDef],
    make_params: &impl Fn() -> Vec<String>,
    pred_local: usize,
    (dest_local, target, probe_variant): (usize, BlockId, &'static str),
) -> Option<ReturnBoolPredSummary> {
    if !probe_result_reaches_return(func, dest_local, target) {
        return None;
    }
    let pred_tag = variants.iter().find(|v| v.name == probe_variant)?.discriminant;
    let variant_tags: Vec<i128> = variants.iter().map(|v| v.discriminant).collect();
    Some(ReturnBoolPredSummary {
        enum_name: enum_name.to_string(),
        params: make_params(),
        pred_param: pred_local,
        pred_field: None,
        kind: ReturnBoolPredKind::Iff,
        pred_tag,
        pred_is_eq: true,
        variants: variant_tags,
    })
}

/// The probe result in `dest_local` flows straight-line into `_0` and reaches
/// the single Return, skipping storage annotations. Shared by Tier 1 (whole
/// pointee) and its field-subject sibling.
pub(super) fn probe_result_reaches_return(
    func: &VerifiableFunction,
    dest_local: usize,
    target: BlockId,
) -> bool {
    let mut cur = target;
    let mut ret_bound = dest_local == 0;
    for _ in 0..8 {
        let Some(block) = func.body.blocks.get(cur.0) else {
            return false;
        };
        for stmt in &block.stmts {
            match stmt {
                Statement::StorageLive(_) | Statement::StorageDead(_) => continue,
                Statement::Assign { place, rvalue, .. }
                    if place.local == 0
                        && place.projections.is_empty()
                        && matches!(rvalue, Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
                            if p.local == dest_local && p.projections.is_empty())
                        && !ret_bound =>
                {
                    ret_bound = true;
                }
                _ => return false,
            }
        }
        match &block.terminator {
            Terminator::Goto(next) => cur = *next,
            Terminator::Return => return ret_bound,
            _ => return false,
        }
    }
    false
}

/// Tier-1 for a FIELD subject: `fn is_ready(&self) -> bool {
/// self.field.is_some() }`. The `&Struct` param's PROBED field must be a
/// modeled enum; the summary records `pred_field = Some(field_idx)` and the
/// tag term is minted over the projected place `(*self).field_idx`. Fail-closed
/// on any deviation (mirrors Tier 1's gates, with a field-projection receiver).
pub(super) fn tier1_field_probe_body_summary(
    func: &VerifiableFunction,
    make_params: &impl Fn() -> Vec<String>,
    pred_local: usize,
) -> Option<ReturnBoolPredSummary> {
    let (field_idx, dest_local, target, probe_paths, probe_variant) =
        find_field_probe(func, pred_local)?;
    // The probed field's type must be a modeled std enum whose flattened shape
    // matches the probe (Option vs Result).
    let field_ty = crate::place_prefix_ty_cow(
        func,
        pred_local,
        &[trust_types::Projection::Deref, trust_types::Projection::Field(field_idx)],
    )?;
    let (enum_name, variants) = modeled_std_enum_shape(field_ty.as_ref())?;
    if !probe_paths.contains(&enum_name) {
        return None;
    }
    if !probe_result_reaches_return(func, dest_local, target) {
        return None;
    }
    let variant_tags: Vec<i128> = variants.iter().map(|v| v.discriminant).collect();
    let pred_tag = variants.iter().find(|v| v.name == probe_variant)?.discriminant;
    Some(ReturnBoolPredSummary {
        enum_name: enum_name.to_string(),
        params: make_params(),
        pred_param: pred_local,
        pred_field: Some(field_idx),
        kind: ReturnBoolPredKind::Iff,
        pred_tag,
        pred_is_eq: true,
        variants: variant_tags,
    })
}

/// Locate THE probe call whose shared-ref receiver is a borrow of a FIELD of
/// the `&Struct` param — `_r = &((*_1).field)`, `is_some(move _r)` — and
/// confirm the call block writes neither `_1` nor `_0`. Returns the field
/// index, the probe's bool dest local, its success block, the probe's enum
/// paths, and the probed variant name. Fail-closed on any deviation.
pub(super) fn find_field_probe(
    func: &VerifiableFunction,
    pred_local: usize,
) -> Option<(usize, usize, BlockId, &'static [&'static str], &'static str)> {
    // SOUNDNESS: the probe must be the ENTRY block so it dominates the Return
    // (see [`find_param_probe`]) — a non-entry field probe behind a bypass arm
    // would be mis-summarized. Fail-closed.
    let call_block = func.body.blocks.first()?;
    let Terminator::Call { func: callee, args, dest, target: Some(target), .. } =
        &call_block.terminator
    else {
        return None;
    };
    let (callee, target) = (callee.as_str(), *target);
    let (probe_paths, probe_variant) = std_option_result_probe_variant(callee)?;
    // Receiver: `&((*_1).field)` — a shared reborrow of a single field of the
    // param's pointee, reached directly or through bare copy/move hops.
    let Some(Operand::Copy(recv) | Operand::Move(recv)) = args.first() else {
        return None;
    };
    if !recv.projections.is_empty() {
        return None;
    }
    let mut cur = recv.local;
    let mut field_idx = None;
    for _ in 0..4 {
        // SOUNDNESS (aliased reseat, audit r3): each hop local must be PINNED
        // before its `&((*_1).f)` / copy def is trusted — a `&mut`-reseated
        // intermediate has a stale def and the field summary would be WRONG.
        if crate::local_defs::is_parameter(func, cur) || !unwrap_receiver_local_is_pinned(func, cur)
        {
            return None;
        }
        match crate::local_defs::unique_value_def(func, cur) {
            Some(Rvalue::Ref { mutable: false, place: referent })
                if referent.local == pred_local =>
            {
                match referent.projections.as_slice() {
                    [trust_types::Projection::Deref, trust_types::Projection::Field(i)] => {
                        field_idx = Some(*i);
                        break;
                    }
                    _ => return None,
                }
            }
            Some(Rvalue::Use(Operand::Copy(p) | Operand::Move(p)))
                if p.projections.is_empty() && p.local != cur =>
            {
                cur = p.local;
            }
            _ => return None,
        }
    }
    let field_idx = field_idx?;
    // The call block's own statements must NOT write the subject param or `_0`.
    for stmt in &call_block.stmts {
        match stmt {
            Statement::StorageLive(_) | Statement::StorageDead(_) => {}
            Statement::Assign { place, .. } if place.local != 0 && place.local != pred_local => {}
            _ => return None,
        }
    }
    if !dest.projections.is_empty() {
        return None;
    }
    Some((field_idx, dest.local, target, probe_paths, probe_variant))
}

/// Tier 2a of [`function_return_bool_pred_summary`].
pub(super) fn tier2a_switch_body_summary(
    func: &VerifiableFunction,
    enum_name: &str,
    variants: &[trust_types::VariantDef],
    make_params: &impl Fn() -> Vec<String>,
    by_value: bool,
    pred_local: usize,
) -> Option<ReturnBoolPredSummary> {
    // Entry block: exactly one statement — the discriminant read of the subject
    // (`*_1` for a `&Enum` param, `_1` for a by-value `Enum` param) — and a
    // two-way switch on it.
    let entry = func.body.blocks.first()?;
    let mut real = entry
        .stmts
        .iter()
        .filter(|s| !matches!(s, Statement::StorageLive(_) | Statement::StorageDead(_)));
    let (Some(Statement::Assign { place: d, rvalue: Rvalue::Discriminant(src), .. }), None) =
        (real.next(), real.next())
    else {
        return None;
    };
    let subject_ok = src.local == pred_local
        && if by_value {
            src.projections.is_empty()
        } else {
            src.projections.as_slice() == [trust_types::Projection::Deref]
        };
    if !d.projections.is_empty() || !subject_ok {
        return None;
    }
    let Terminator::SwitchInt { discr, targets, otherwise, .. } = &entry.terminator else {
        return None;
    };
    let (Operand::Copy(sw) | Operand::Move(sw)) = discr else {
        return None;
    };
    if sw.local != d.local || !sw.projections.is_empty() || targets.len() != 1 {
        return None;
    }
    let (case_tag, case_bb) = (targets[0].0, targets[0].1);
    let case_tag = i128::try_from(case_tag).ok()?;
    if variants.len() != 2 || !variants.iter().any(|v| v.discriminant == case_tag) {
        return None;
    }
    let other_tag = variants.iter().find(|v| v.discriminant != case_tag)?.discriminant;
    // The case arm is reached iff `tag == case_tag`; the otherwise arm iff
    // `tag == other_tag` (2-variant, exact partition). Classify each arm's
    // return value: `Some(b)` = a provably-const `b` (straight-line to Return),
    // `None` = a non-const / payload-computing arm.
    let fc = straight_line_bool_arm(func, case_bb);
    let fo = straight_line_bool_arm(func, *otherwise);
    // `matches!(o, Some(x) if PRED)` gives `ret ⇒ tag == Some` — the non-`Some`
    // arm is provably const-false, so a `true` result implies the `Some` arm's
    // tag. SOUNDNESS of the one-directional cases: the CONST arm is proven to
    // return exactly one value on every path (straight_line_bool_arm), and the
    // switch fixes the entry tag per arm, so any `true`/`false` result routes
    // through the single non-const arm whose tag is pinned by the switch. The
    // non-const arm is NOT inspected — its structure cannot admit a result under
    // the wrong tag because the const arm cannot produce it.
    let (kind, pred_tag) = match (fc, fo) {
        // IFF: both arms const, distinct — a pure tag predicate.
        (Some(a), Some(b)) => {
            if a == b {
                return None; // constant, not a predicate
            }
            (ReturnBoolPredKind::Iff, if a { case_tag } else { other_tag })
        }
        // ImpliesTrue: exactly one arm is provably const-FALSE ⇒ `true` only from
        // the OTHER arm ⇒ `ret ⇒ tag == other_arm_tag`.
        (Some(false), None) => (ReturnBoolPredKind::ImpliesTrue, other_tag),
        (None, Some(false)) => (ReturnBoolPredKind::ImpliesTrue, case_tag),
        // ImpliesFalse: exactly one arm is provably const-TRUE ⇒ `false` only from
        // the OTHER arm ⇒ `ret == false ⇒ tag == other_arm_tag`.
        (Some(true), None) => (ReturnBoolPredKind::ImpliesFalse, other_tag),
        (None, Some(true)) => (ReturnBoolPredKind::ImpliesFalse, case_tag),
        // Neither arm const — cannot conclude a tag relationship.
        (None, None) => return None,
    };
    let variant_tags: Vec<i128> = variants.iter().map(|v| v.discriminant).collect();
    Some(ReturnBoolPredSummary {
        enum_name: enum_name.to_string(),
        params: make_params(),
        pred_param: pred_local,
        pred_field: None,
        kind,
        pred_tag,
        pred_is_eq: true,
        variants: variant_tags,
    })
}

/// Tier 2b of [`function_return_bool_pred_summary`]: a probe call whose Bool
/// result feeds a two-way switch, each arm straight-line assigning `_0` a Bool
/// const — `fn f(o: &Option<u32>) -> bool { if o.is_some() { true } else {
/// false } }` and its polarity/negation variants (e.g. `{ false } else {
/// true }` = `is_none`). The switch is on the PROBE result (a bool), so the
/// value-`0` case is the probe-false arm. Normalizes to `ret ⇔ tag == K`.
pub(super) fn tier2b_probe_switch_body_summary(
    func: &VerifiableFunction,
    enum_name: &str,
    variants: &[trust_types::VariantDef],
    make_params: &impl Fn() -> Vec<String>,
    by_value: bool,
    pred_local: usize,
) -> Option<ReturnBoolPredSummary> {
    let probe = find_param_probe(func, enum_name, by_value, pred_local)?;
    tier2b_probe_switch_body_summary_from_probe(
        func,
        enum_name,
        variants,
        make_params,
        pred_local,
        probe,
    )
}

fn tier2b_probe_switch_body_summary_from_probe(
    func: &VerifiableFunction,
    enum_name: &str,
    variants: &[trust_types::VariantDef],
    make_params: &impl Fn() -> Vec<String>,
    pred_local: usize,
    (probe_dest, target, probe_variant): (usize, BlockId, &'static str),
) -> Option<ReturnBoolPredSummary> {
    // The probe's success block switches on the Bool result; only storage
    // annotations may precede the switch.
    let sw_block = func.body.blocks.get(target.0)?;
    if sw_block
        .stmts
        .iter()
        .any(|s| !matches!(s, Statement::StorageLive(_) | Statement::StorageDead(_)))
    {
        return None;
    }
    let Terminator::SwitchInt { discr, targets, otherwise, .. } = &sw_block.terminator else {
        return None;
    };
    let (Operand::Copy(sw) | Operand::Move(sw)) = discr else {
        return None;
    };
    if sw.local != probe_dest || !sw.projections.is_empty() || targets.len() != 1 {
        return None;
    }
    // A Bool switch: case `0` is the probe-false arm, case `1` the probe-true
    // arm — admit either ordering, decline anything else.
    let (case_val, case_bb) = (targets[0].0, targets[0].1);
    let (true_bb, false_bb) = match case_val {
        0 => (*otherwise, case_bb),
        1 => (case_bb, *otherwise),
        _ => return None,
    };
    // The switch fixes: `true_bb` iff probe==true iff `tag == probe_tag`;
    // `false_bb` iff `tag == other_tag` (2-variant complement). This is the
    // tier2a structure with case↔true_bb (probe_tag), otherwise↔false_bb
    // (other_tag) — classify each arm and derive the kind identically.
    let probe_tag = variants.iter().find(|v| v.name == probe_variant)?.discriminant;
    let other_tag = || -> Option<i128> {
        if variants.len() != 2 {
            return None;
        }
        variants.iter().find(|v| v.discriminant != probe_tag).map(|v| v.discriminant)
    };
    let v_true = straight_line_bool_arm(func, true_bb);
    let v_false = straight_line_bool_arm(func, false_bb);
    // `o.is_some() && extra`: the probe-FALSE arm is const-false, the probe-true
    // arm computes `extra` (non-const) ⇒ `ret ⇒ tag == Some` (ImpliesTrue).
    // SOUNDNESS mirrors tier2a: the CONST arm is proven single-valued and the
    // switch pins the entry tag per arm (the probe result is EXACTLY
    // `tag == probe_tag`, over the pinned `_1`), so any result routes through
    // the single non-const arm whose tag is fixed; the non-const arm is not
    // inspected.
    let (kind, pred_tag) = match (v_true, v_false) {
        (Some(a), Some(b)) => {
            if a == b {
                return None; // constant, not a predicate
            }
            (ReturnBoolPredKind::Iff, if a { probe_tag } else { other_tag()? })
        }
        // ImpliesTrue: exactly one arm provably const-FALSE ⇒ true only from the
        // other arm.
        (Some(false), None) => (ReturnBoolPredKind::ImpliesTrue, other_tag()?),
        (None, Some(false)) => (ReturnBoolPredKind::ImpliesTrue, probe_tag),
        // ImpliesFalse: exactly one arm provably const-TRUE ⇒ false only from the
        // other arm.
        (Some(true), None) => (ReturnBoolPredKind::ImpliesFalse, other_tag()?),
        (None, Some(true)) => (ReturnBoolPredKind::ImpliesFalse, probe_tag),
        (None, None) => return None,
    };
    let variant_tags: Vec<i128> = variants.iter().map(|v| v.discriminant).collect();
    Some(ReturnBoolPredSummary {
        enum_name: enum_name.to_string(),
        params: make_params(),
        pred_param: pred_local,
        pred_field: None,
        kind,
        pred_tag,
        pred_is_eq: true,
        variants: variant_tags,
    })
}
