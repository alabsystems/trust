// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Interprocedural condvar-pairing certification (`#[trust::paired]`).
//!
//! A `#[trust::paired]` struct `S { m: Mutex<T>, c: Condvar, … }` declares that
//! the PRIVATE `Condvar` field `c` is only ever waited on with a `MutexGuard`
//! obtained from ONE fixed sibling `Mutex` field `m` of the SAME instance. When
//! that holds for every wait site in the crate, the pthread lane's two-mutex
//! `verify()` panic (`library/std/src/sys/sync/condvar/pthread.rs:39` — the ONLY
//! name-dependent panic modeled for `Condvar::wait`; poison maps to `Err`, the
//! pal return is only `debug_assert`'ed, and blocking is out of model exactly as
//! for the allowlisted `Mutex::lock`) is unreachable: the condvar's
//! `compare_exchange`d pal-mutex ADDRESS only ever sees `m`'s pal mutex.
//!
//! **The soundness keystone** is the guard-provenance leg, an INSTANCE-PINNED
//! forward gen/kill dataflow (two confirmed false-PROVEs — cross-instance guard
//! threading and receiver rebinding — were found against weaker, name-keyed
//! designs):
//!
//!   * a guard fact is `(base local chain B, mutex field m)`, GENerated ONLY at
//!     a recognized `Mutex::lock(&(*B).m)`;
//!   * PRESERVEd only through whole-local copy/move of the guard local, through
//!     the recognized `Result` unwrapping of a lock/wait result (`unwrap`,
//!     `expect`, `unwrap_or_else` with a provably `PoisonError::into_inner`-
//!     shaped closure — std's wait returns the SAME guard, and the poison arm
//!     wraps that same guard, `poison/condvar.rs:125-132`), and through the
//!     result of a wait already VALIDATED at this same fact (never re-derived
//!     from a wait's own receiver);
//!   * KILLed at EVERY def (statement assign or call destination, whole or
//!     projected) of ANY local in `B`, at every `&mut`/raw borrow of the guard
//!     local or a `B` local, at any unrecognized move of the guard local, and
//!     ⊥-joined on merge of unequal facts.
//!
//! Kill-at-def is load-bearing beyond a unique-static-def rule: a unique def
//! re-executed on a loop back edge would otherwise let a stale fact name-match a
//! receiver holding a NEW instance. With kill-at-def, a fact live at a wait
//! proves no def of `B` on any lock-to-wait path, so `B`'s dynamic value at the
//! wait equals its value at the lock — value identity by dominance construction,
//! not name identity: any live fact `(B, m)` at `(*B).c.wait(g)` proves `g` is
//! the guard of THE SAME dynamic instance's `m`.
//!
//! The remaining legs (all fail-closed; ANY violation DECERTIFIES the whole
//! `(S, c, m)` pair, never just a site, because the use-site discharge is
//! receiver-shape-only and crate-wide):
//!
//!   * wait-site validation covers `wait`/`wait_timeout`/`wait_while`/
//!     `wait_timeout_while` (all call the pthread `verify()`; `notify_one`/
//!     `notify_all` never do and need no gating);
//!   * pair discovery is from guard evidence ONLY, and MIXED evidence (one
//!     condvar waited with guards of two different sibling mutexes) decertifies
//!     — never "select one";
//!   * every construction of `S` must initialize `c` by a same-body
//!     `Condvar::new()` call reached only through unique-def whole-local moves
//!     (a constructor-INJECTED condvar may arrive pre-bound to a foreign mutex);
//!   * crate-wide positive whitelist on every use of the paired fields: a
//!     shared borrow of `c` consumed solely as a wait/notify receiver, a shared
//!     borrow of `m` consumed solely as a `Mutex::lock` receiver, and aggregate
//!     construction of `S`. ANY other mention — `&mut`/raw borrow, projected
//!     read/write, move-out, escaping borrow (returned, passed to a helper,
//!     cast), `mem::swap` of a field — decertifies.
//!
//! **SOUNDNESS CONTRACT.** The caller MUST pass the COMPLETE set of functions of
//! the defining crate (including closures, const/static initializers and
//! promoted bodies — a skipped body could hide a rogue wait site or an escaping
//! borrow, which is why the compiler integration DECERTIFIES on any stolen or
//! unavailable body, stricter than `backing_cert`'s skip). For a struct whose
//! `Condvar`/`Mutex` fields are PRIVATE this whole-crate view is complete —
//! Rust's visibility rules forbid external naming of the fields; field privacy
//! plus the non-escaping-borrow whitelist IS the aliasing proof (the identical,
//! already-shipped `#[trust::backing]` argument, see `backing_cert.rs`). The
//! caller also vets candidate structs (attribute, privacy, genuine non-local
//! `std::sync::Condvar`/`Mutex` field types) and rejects crates containing any
//! local definition whose rendered path impersonates `std::`/`core::`/
//! `alloc::` (a local `mod std` would otherwise render callee paths
//! indistinguishable from the real recognizer targets).
//!
//! Documented residual (same acceptance as `backing_cert`): unsafe resurrection
//! of the struct or its interior is the hardened-unsafe domain. This includes
//! raw-pointer/transmute/`MaybeUninit`/`mem::zeroed` construction and a whole
//! `S` injected by FFI or another opaque unsafe producer without an observable
//! `Rvalue::Aggregate(S, ..)`. Safe local constructors are observable and
//! scanned in their defining bodies; an eventual production promotion must
//! either retain this explicit unsafe-domain boundary or add a whole-`S` origin
//! gate that authenticates every such producer.

use trust_types::fx::{FxHashMap, FxHashSet};
use trust_types::{
    AggregateKind, Operand, Place, Projection, Rvalue, Statement, Terminator, Ty,
    VerifiableFunction, operand_place, strip_generics,
};

/// A compiler-vetted `#[trust::paired]` struct: the attribute is present, every
/// listed field is PRIVATE, `condvar_fields` are genuine non-local
/// `std::sync::Condvar` fields (and NO public `Condvar` field exists on the
/// struct), and `mutex_fields` are genuine non-local private `std::sync::Mutex`
/// fields. `struct_name` is the `safe_def_path_str` rendering, matching the
/// extracted IR's `Ty::Adt` name.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PairedCondvarCandidate {
    pub struct_name: String,
    pub condvar_fields: Vec<usize>,
    pub mutex_fields: Vec<usize>,
    /// Total field count of the struct — an aggregate with a different operand
    /// count is not a recognized construction and decertifies.
    pub field_count: usize,
}

/// A certified `(S, c, m)` pair: every crate wait site on `S.c` is validated
/// against a same-instance guard of `S.m`, `c` is always freshly constructed,
/// and neither field escapes. Licenses an extraction-time, non-serialized
/// compiler sidecar for exact `S.c` wait call sites.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CertifiedCondvarPair {
    pub struct_name: String,
    pub condvar_field: usize,
    pub mutex_field: usize,
}

/// Certify the condvar pairings provable from `functions` (the complete crate
/// body set — see the module-level soundness contract) for the compiler-vetted
/// `candidates`. Returns the certified `(S, c, m)` pairs; everything else stays
/// fail-closed (the wait keeps its absent-callee panic obligation).
#[must_use]
pub fn certify_paired_condvars(
    functions: &[VerifiableFunction],
    candidates: &[PairedCondvarCandidate],
) -> Vec<CertifiedCondvarPair> {
    if candidates.is_empty() {
        return Vec::new();
    }

    // Global fail-closed gate: a statement (or opaque control flow) the IR does
    // not model could hide an arbitrary effect on a paired field (inline asm, a
    // coroutine resume, …). ANY such body decertifies every candidate.
    for func in functions {
        if !function_is_fully_modeled(func) {
            return Vec::new();
        }
    }

    let closures: FxHashMap<&str, &VerifiableFunction> =
        functions.iter().map(|f| (f.def_path.as_str(), f)).collect();

    let mut poisoned: FxHashSet<(usize, usize)> = FxHashSet::default();
    let mut evidence: FxHashMap<(usize, usize), FxHashSet<usize>> = FxHashMap::default();

    for func in functions {
        analyze_function(func, candidates, &closures, &mut poisoned, &mut evidence);
    }

    let mut certified = Vec::new();
    for (ci, cand) in candidates.iter().enumerate() {
        for &c in &cand.condvar_fields {
            if poisoned.contains(&(ci, c)) {
                continue;
            }
            let Some(ms) = evidence.get(&(ci, c)) else {
                // No validated wait evidence at all — no pair to certify (pair
                // discovery is from guard evidence ONLY).
                continue;
            };
            // Mixed evidence decertifies; a single, unpoisoned sibling mutex
            // certifies the pair.
            if ms.len() != 1 {
                continue;
            }
            let m = *ms.iter().next().expect("len checked above");
            if !cand.mutex_fields.contains(&m) || poisoned.contains(&(ci, m)) {
                continue;
            }
            certified.push(CertifiedCondvarPair {
                struct_name: cand.struct_name.clone(),
                condvar_field: c,
                mutex_field: m,
            });
        }
    }
    certified
}

// ---------------------------------------------------------------------------
// Instance-pinned dataflow domain
// ---------------------------------------------------------------------------

/// The base local chain `B` of an instance-pinned fact: the place prefix (a
/// local plus `Deref`/`Field`-only projections) up to but excluding the paired
/// field itself. Two facts pin the SAME dynamic instance iff their `B`s are
/// structurally equal AND no local of `B` was redefined between the facts'
/// generation points (enforced by kill-at-def, not stored).
#[derive(Debug, Clone, PartialEq, Eq)]
struct Base {
    local: usize,
    projections: Vec<Projection>,
}

/// One dataflow fact attached to a single whole local. `cand` indexes the
/// candidate struct; `field` is the sibling mutex (`MutexRef`/`GuardRes`/
/// `Guard`) or the condvar (`CvRef`).
#[derive(Debug, Clone, PartialEq, Eq)]
enum Fact {
    /// Holds `&(*B).m` — a shared borrow of the candidate mutex field.
    MutexRef { cand: usize, base: Base, field: usize },
    /// Holds the `Result<MutexGuard, PoisonError<..>>` of a recognized lock of
    /// `(B, m)`, or of a wait VALIDATED at `(B, m)`.
    GuardRes { cand: usize, base: Base, field: usize },
    /// Holds the `MutexGuard` of `(B, m)` itself.
    Guard { cand: usize, base: Base, field: usize },
    /// Holds `&(*B).c` — a shared borrow of the candidate condvar field.
    CvRef { cand: usize, base: Base, field: usize },
}

impl Fact {
    fn base(&self) -> &Base {
        match self {
            Fact::MutexRef { base, .. }
            | Fact::GuardRes { base, .. }
            | Fact::Guard { base, .. }
            | Fact::CvRef { base, .. } => base,
        }
    }
}

type State = FxHashMap<usize, Fact>;

/// Remove the fact held BY `local` and every fact whose base chain mentions
/// `local` (its dynamic identity is no longer the one the fact was pinned to).
fn kill_local(state: &mut State, local: usize) {
    state.retain(|l, fact| *l != local && fact.base().local != local);
}

fn join(a: &State, b: &State) -> State {
    let mut out = State::default();
    for (l, fa) in a {
        if b.get(l) == Some(fa) {
            out.insert(*l, fa.clone());
        }
    }
    out
}

// ---------------------------------------------------------------------------
// Callee recognizers (extractor callee strings, turbofish-normalized)
// ---------------------------------------------------------------------------

/// Normalize an extractor callee string for suffix matching: strip every
/// generic/turbofish group, then any residue `::` a TRAILING turbofish leaves
/// behind (`Condvar::wait::<Vec<u8>>` strips to `…::wait::`, cf. vcgen's
/// `method_tail` on the same hazard).
fn normalize_callee(callee: &str) -> String {
    let stripped = strip_generics(callee);
    stripped.trim_end_matches(':').to_string()
}

/// `std::`-anchored suffix match after [`normalize_callee`], the same
/// discipline as the bridge's trusted-callee lists (`lower.rs` "::Mutex::lock"). The compiler
/// integration guarantees no LOCAL definition renders with a `std::`/`core::`/
/// `alloc::` prefix (impersonation guard), and a foreign crate NAMED `std`
/// renders with the `__trust_crate@…::` disambiguation prefix and fails the
/// anchor.
fn std_anchored(name: &str) -> bool {
    name.starts_with("std::") || name.starts_with("core::") || name.starts_with("alloc::")
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum WaitFamily {
    /// `Condvar::wait` — the only spelling the extractor marker DISCHARGES
    /// (its result is the same guard, so the fact is preserved through it).
    Wait,
    /// `wait_timeout`/`wait_while`/`wait_timeout_while` — validated (they all
    /// reach the pthread `verify()`), but their results carry no fact (tuple
    /// payloads / user predicate) and they are never marker-discharged here.
    Other,
}

fn recognized_wait_family(name: &str) -> Option<WaitFamily> {
    if !std_anchored(name) {
        return None;
    }
    if name.ends_with("::Condvar::wait") {
        Some(WaitFamily::Wait)
    } else if name.ends_with("::Condvar::wait_timeout")
        || name.ends_with("::Condvar::wait_while")
        || name.ends_with("::Condvar::wait_timeout_while")
    {
        Some(WaitFamily::Other)
    } else {
        None
    }
}

fn is_lock_callee(name: &str) -> bool {
    std_anchored(name) && name.ends_with("::Mutex::lock")
}

fn is_notify_callee(name: &str) -> bool {
    std_anchored(name)
        && (name.ends_with("::Condvar::notify_one") || name.ends_with("::Condvar::notify_all"))
}

fn is_result_unwrap_callee(name: &str) -> bool {
    std_anchored(name) && (name.ends_with("::Result::unwrap") || name.ends_with("::Result::expect"))
}

fn is_result_unwrap_or_else_callee(name: &str) -> bool {
    std_anchored(name) && name.ends_with("::Result::unwrap_or_else")
}

fn is_condvar_new_callee(name: &str) -> bool {
    std_anchored(name) && name.ends_with("::Condvar::new")
}

fn is_poison_into_inner_callee(name: &str) -> bool {
    std_anchored(name) && name.ends_with("::PoisonError::into_inner")
}

// ---------------------------------------------------------------------------
// Place / type walking
// ---------------------------------------------------------------------------

fn local_ty<'f>(func: &'f VerifiableFunction, local: usize) -> Option<&'f Ty> {
    func.body.locals.get(local).map(|l| &l.ty)
}

/// If `place` is exactly `B ++ [Field(k)]` where the type at `B` is a candidate
/// struct, return `(candidate index, B, k)`. The base chain admits ONLY `Deref`
/// through `&T` and `Field` through a plain struct — anything else (raw-pointer
/// deref, enum downcast, indexing) yields `None` (fail closed: no fact is ever
/// generated from a base whose dynamic identity the kill-at-def discipline
/// cannot track).
fn candidate_field_borrow(
    func: &VerifiableFunction,
    place: &Place,
    candidates: &[PairedCondvarCandidate],
) -> Option<(usize, Base, usize)> {
    let (last, prefix) = place.projections.split_last()?;
    let Projection::Field(fidx) = last else {
        return None;
    };
    let mut ty = local_ty(func, place.local)?;
    for proj in prefix {
        ty = match (ty, proj) {
            (Ty::Ref { inner, .. }, Projection::Deref) => inner,
            (Ty::Adt { fields, variants, .. }, Projection::Field(i)) if variants.is_empty() => {
                &fields.get(*i)?.1
            }
            _ => return None,
        };
    }
    let Ty::Adt { name, variants, .. } = ty else {
        return None;
    };
    if !variants.is_empty() {
        return None;
    }
    let cand = candidates.iter().position(|c| c.struct_name == *name)?;
    Some((cand, Base { local: place.local, projections: prefix.to_vec() }, *fidx))
}

/// Detection walk for the crate-wide whitelist: every position in `place`'s
/// projection list where a candidate-struct field `Field(k)` (k a paired
/// condvar/mutex field) is projected. Unlike [`candidate_field_borrow`] this
/// walks through raw pointers, enums (flattened `__v{v}_` fields), tuples,
/// closures and slices so a use CANNOT hide behind them. If the walk gets stuck
/// on an unmodeled type while `Field` projections remain, it reports
/// `WalkOutcome::Opaque` and the caller poisons EVERYTHING (a candidate field
/// could be below the unmodeled node).
enum WalkOutcome {
    /// `(position, candidate index, field)` for every paired-field projection.
    Mentions(Vec<(usize, usize, usize)>),
    Opaque,
}

fn candidate_field_mentions(
    func: &VerifiableFunction,
    place: &Place,
    candidates: &[PairedCondvarCandidate],
) -> WalkOutcome {
    let mut out = Vec::new();
    let Some(mut ty) = local_ty(func, place.local) else {
        // An out-of-range local cannot be typed; if it projects any field we
        // cannot rule a paired field out.
        return if place.projections.iter().any(|p| matches!(p, Projection::Field(_))) {
            WalkOutcome::Opaque
        } else {
            WalkOutcome::Mentions(out)
        };
    };
    let mut pending_variant: Option<usize> = None;
    for (pos, proj) in place.projections.iter().enumerate() {
        let next: Option<&Ty> = match proj {
            Projection::Downcast(v) => {
                pending_variant = Some(*v);
                Some(ty)
            }
            Projection::Field(idx) => {
                if let Ty::Adt { name, fields, variants, .. } = ty {
                    if variants.is_empty() && pending_variant.is_none() {
                        // Plain struct field: record a paired-field mention.
                        if let Some(ci) = candidates.iter().position(|c| c.struct_name == *name) {
                            let cand = &candidates[ci];
                            if cand.condvar_fields.contains(idx) || cand.mutex_fields.contains(idx)
                            {
                                out.push((pos, ci, *idx));
                            }
                        }
                        fields.get(*idx).map(|(_, t)| t)
                    } else if let Some(v) = pending_variant.take() {
                        // Enum variant field via the flattened `__v{v}_` shape.
                        let prefix = format!("__v{v}_");
                        fields
                            .iter()
                            .filter(|(n, _)| n.starts_with(&prefix))
                            .nth(*idx)
                            .map(|(_, t)| t)
                    } else {
                        None
                    }
                } else {
                    match ty {
                        Ty::Tuple(fields) => fields.get(*idx),
                        Ty::Closure { upvars, .. } => upvars.get(*idx),
                        _ => None,
                    }
                }
            }
            Projection::Deref => match ty {
                Ty::Ref { inner, .. } => Some(inner),
                Ty::RawPtr { pointee, .. } => Some(pointee),
                _ => None,
            },
            Projection::Index(_) | Projection::ConstantIndex { .. } => match ty {
                Ty::Slice { elem } | Ty::Array { elem, .. } => Some(elem),
                _ => None,
            },
            Projection::Subslice { .. } => match ty {
                Ty::Slice { .. } | Ty::Array { .. } => Some(ty),
                _ => None,
            },
            _ => None,
        };
        match next {
            Some(t) => ty = t,
            None => {
                // Stuck. If any `Field` remains (including this one), a paired
                // field might be below the unmodeled node — fail closed.
                if place.projections[pos..].iter().any(|p| matches!(p, Projection::Field(_))) {
                    return WalkOutcome::Opaque;
                }
                return WalkOutcome::Mentions(out);
            }
        }
    }
    WalkOutcome::Mentions(out)
}

// ---------------------------------------------------------------------------
// Full modeling gate
// ---------------------------------------------------------------------------

/// `false` if the body contains a statement or terminator whose semantics the
/// IR does not model (its effect on a paired field is unknowable). Value-level
/// unknowns (`Rvalue::Unsupported` / `Operand::Unsupported`) stay allowed: an
/// unknown VALUE cannot write, move or borrow a field — only unmodeled
/// STATEMENTS/CONTROL FLOW can.
fn function_is_fully_modeled(func: &VerifiableFunction) -> bool {
    func.body.blocks.iter().all(|block| {
        let terminator_modeled = match &block.terminator {
            Terminator::Goto(_)
            | Terminator::SwitchInt { .. }
            | Terminator::Return
            | Terminator::Call { .. }
            | Terminator::Assert { .. }
            | Terminator::Drop { .. }
            | Terminator::Unreachable
            | Terminator::Resume => true,
            Terminator::Opaque { .. } => false,
            // `Terminator` is non-exhaustive. Every future variant starts dark
            // until this semantic lane explicitly accounts for it.
            _ => false,
        };
        terminator_modeled
            && block.stmts.iter().all(|stmt| match stmt {
                Statement::Assign { .. }
                | Statement::StorageLive(_)
                | Statement::StorageDead(_)
                | Statement::SetDiscriminant { .. }
                | Statement::Retag { .. }
                | Statement::PlaceMention(_)
                | Statement::Intrinsic { .. }
                | Statement::Coverage
                | Statement::ConstEvalCounter
                | Statement::Nop => true,
                Statement::Deinit { .. } | Statement::Unsupported { .. } => false,
                // `Statement` is non-exhaustive. Future variants fail closed.
                _ => false,
            })
    })
}

// ---------------------------------------------------------------------------
// Transfer function
// ---------------------------------------------------------------------------

/// Kill every fact invalidated by a `&mut`/raw borrow of a place based at
/// `local` (its value — or a value reachable through it — can now change
/// through the alias, so instance pinning is void).
fn kill_aliased(state: &mut State, local: usize) {
    kill_local(state, local);
}

/// The function-wide set of locals whose address is EVER taken raw
/// (`&raw const`/`&raw mut`, either mutability — a `*const` can be cast to
/// `*mut` and written). Raw pointers escape the borrow checker entirely, so a
/// deref-store through one is invisible to the flow-sensitive kills; no fact
/// may be held by, or pinned through, such a local.
fn raw_exposed_locals(func: &VerifiableFunction) -> FxHashSet<usize> {
    let mut out = FxHashSet::default();
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign { rvalue: Rvalue::AddressOf(_, place), .. } = stmt {
                out.insert(place.local);
            }
        }
    }
    out
}

fn may_hold_fact(raw_exposed: &FxHashSet<usize>, local: usize, fact: &Fact) -> bool {
    !raw_exposed.contains(&local) && !raw_exposed.contains(&fact.base().local)
}

fn operand_whole_local(op: &Operand) -> Option<usize> {
    match op {
        Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => Some(p.local),
        _ => None,
    }
}

/// Apply one statement to the state. `raw_exposed` is the function-wide set of
/// locals whose address is EVER taken raw (`&raw const/mut`): raw pointers
/// escape the borrow checker, so a later deref-store through them is invisible
/// to the flow-sensitive kills — no fact may ever be HELD by such a local or
/// PINNED through one (fail closed). `&mut` borrows need only the
/// flow-sensitive kill: borrowck guarantees the borrow is dead before any
/// subsequent def/use of the borrowed local that could regenerate a fact.
fn apply_statement(
    state: &mut State,
    stmt: &Statement,
    func: &VerifiableFunction,
    candidates: &[PairedCondvarCandidate],
    raw_exposed: &FxHashSet<usize>,
) {
    match stmt {
        Statement::Assign { place, rvalue, .. } => {
            // Compute the generated fact from the PRE state.
            let generated: Option<Fact> = if place.projections.is_empty() {
                match rvalue {
                    Rvalue::Use(Operand::Move(src) | Operand::Copy(src))
                        if src.projections.is_empty() =>
                    {
                        state.get(&src.local).cloned()
                    }
                    // Guard extraction from a lock/wait Result (post-inline
                    // `unwrap_or_else` shape): `(r as Ok).0` and
                    // `((r as Err).0).0` both carry THE SAME guard.
                    Rvalue::Use(Operand::Move(src)) => match src.projections.as_slice() {
                        [Projection::Downcast(0), Projection::Field(0)]
                        | [Projection::Downcast(1), Projection::Field(0), Projection::Field(0)] => {
                            match state.get(&src.local) {
                                Some(Fact::GuardRes { cand, base, field }) => Some(Fact::Guard {
                                    cand: *cand,
                                    base: base.clone(),
                                    field: *field,
                                }),
                                _ => None,
                            }
                        }
                        _ => None,
                    },
                    Rvalue::Ref { mutable: false, place: p } => {
                        candidate_field_borrow(func, p, candidates).and_then(|(cand, base, k)| {
                            if candidates[cand].condvar_fields.contains(&k) {
                                Some(Fact::CvRef { cand, base, field: k })
                            } else if candidates[cand].mutex_fields.contains(&k) {
                                Some(Fact::MutexRef { cand, base, field: k })
                            } else {
                                None
                            }
                        })
                    }
                    _ => None,
                }
            } else {
                None
            };

            // KILLS. (1) `&mut`/raw borrows void pinning of the borrowed base.
            match rvalue {
                Rvalue::Ref { mutable: true, place: p } | Rvalue::AddressOf(_, p) => {
                    kill_aliased(state, p.local);
                }
                _ => {}
            }
            // (2) Every whole-local MOVE consumes its source; a projected move
            // partially deinitializes its base. (Copies/reads preserve value
            // identity and kill nothing.)
            for_each_rvalue_operand(rvalue, &mut |op| {
                if let Operand::Move(p) = op {
                    kill_local(state, p.local);
                }
            });
            // (3) The destination def kills the destination local (whole OR
            // projected — kill-at-def is the keystone) and every fact pinned
            // through it.
            kill_local(state, place.local);

            if let Some(fact) = generated {
                if may_hold_fact(raw_exposed, place.local, &fact) {
                    state.insert(place.local, fact);
                }
            }
        }
        Statement::StorageLive(l) | Statement::StorageDead(l) => kill_local(state, *l),
        Statement::SetDiscriminant { place, .. }
        | Statement::Deinit { place }
        | Statement::Retag { place } => kill_local(state, place.local),
        Statement::PlaceMention(_) => {}
        Statement::Intrinsic { args, .. } => {
            for op in args {
                if let Operand::Move(p) | Operand::Copy(p) = op {
                    // An intrinsic's semantics on its operands are not tracked
                    // here — kill both moves AND copies (fail closed).
                    kill_local(state, p.local);
                }
            }
        }
        // `function_is_fully_modeled` already decertified any body containing
        // this; clearing the state keeps even that path fail-closed.
        Statement::Unsupported { .. } => state.clear(),
        _ => state.clear(),
    }
}

fn for_each_rvalue_operand(rvalue: &Rvalue, f: &mut impl FnMut(&Operand)) {
    match rvalue {
        Rvalue::Use(op) | Rvalue::UnaryOp(_, op) | Rvalue::Cast(op, _) | Rvalue::Repeat(op, _) => {
            f(op)
        }
        Rvalue::BinaryOp(_, a, b) | Rvalue::CheckedBinaryOp(_, a, b) => {
            f(a);
            f(b);
        }
        Rvalue::Aggregate(_, ops) => ops.iter().for_each(f),
        Rvalue::Unsupported { operands, .. } => operands.iter().for_each(f),
        Rvalue::Ref { .. }
        | Rvalue::Discriminant(_)
        | Rvalue::Len(_)
        | Rvalue::AddressOf(..)
        | Rvalue::CopyForDeref(_) => {}
        _ => {}
    }
}

/// The wait-site outcome computed by the terminator transfer: `Some` iff the
/// call is a recognized wait-family call. `validated` carries `(cand, c, m)`
/// when receiver and guard facts are live, instance-equal and candidate-paired.
struct WaitSite {
    validated: Option<(usize, usize, usize)>,
}

/// Apply a terminator to the state; returns the wait-site outcome for
/// recognized wait-family calls (used by the accounting pass).
fn apply_terminator(
    state: &mut State,
    term: &Terminator,
    func: &VerifiableFunction,
    closures: &FxHashMap<&str, &VerifiableFunction>,
    raw_exposed: &FxHashSet<usize>,
) -> Option<WaitSite> {
    match term {
        Terminator::Call { func: callee, args, dest, .. } => {
            let name = normalize_callee(callee);
            let mut wait_site = None;
            // Recognition against the PRE state.
            let generated: Option<Fact> = if is_lock_callee(&name) && args.len() == 1 {
                match operand_whole_local(&args[0]).and_then(|l| state.get(&l)) {
                    Some(Fact::MutexRef { cand, base, field }) => {
                        Some(Fact::GuardRes { cand: *cand, base: base.clone(), field: *field })
                    }
                    _ => None,
                }
            } else if is_result_unwrap_callee(&name) && !args.is_empty() {
                match operand_whole_local(&args[0]).and_then(|l| state.get(&l)) {
                    Some(Fact::GuardRes { cand, base, field }) => {
                        Some(Fact::Guard { cand: *cand, base: base.clone(), field: *field })
                    }
                    _ => None,
                }
            } else if is_result_unwrap_or_else_callee(&name) && args.len() == 2 {
                let res = operand_whole_local(&args[0]).and_then(|l| state.get(&l)).cloned();
                match res {
                    Some(Fact::GuardRes { cand, base, field })
                        if closure_is_poison_into_inner(func, &args[1], closures) =>
                    {
                        Some(Fact::Guard { cand, base, field })
                    }
                    _ => None,
                }
            } else if let Some(family) = recognized_wait_family(&name) {
                let recv =
                    args.first().and_then(operand_whole_local).and_then(|l| state.get(&l)).cloned();
                let guard =
                    args.get(1).and_then(operand_whole_local).and_then(|l| state.get(&l)).cloned();
                let validated = match (&recv, &guard) {
                    (
                        Some(Fact::CvRef { cand: rc, base: rb, field: c }),
                        Some(Fact::Guard { cand: gc, base: gb, field: m }),
                    ) if rc == gc && rb == gb => Some((*rc, *c, *m)),
                    _ => None,
                };
                wait_site = Some(WaitSite { validated });
                match (family, validated, guard) {
                    // std's `wait` returns the SAME guard (poison wraps the same
                    // guard, `poison/condvar.rs:125-132`) — the fact is invariant
                    // across a VALIDATED wait, so the wait's Result inherits it.
                    (WaitFamily::Wait, Some((cand, _c, m)), Some(Fact::Guard { base, .. })) => {
                        Some(Fact::GuardRes { cand, base, field: m })
                    }
                    _ => None,
                }
            } else {
                None
            };

            // KILLS: every moved argument is consumed; the destination def
            // kills its local.
            for op in args {
                if let Operand::Move(p) = op {
                    kill_local(state, p.local);
                }
            }
            kill_local(state, dest.local);
            if dest.projections.is_empty() {
                if let Some(fact) = generated {
                    if may_hold_fact(raw_exposed, dest.local, &fact) {
                        state.insert(dest.local, fact);
                    }
                }
            }
            wait_site
        }
        Terminator::Drop { place, .. } => {
            kill_local(state, place.local);
            None
        }
        Terminator::SwitchInt { discr: op, .. } | Terminator::Assert { cond: op, .. } => {
            if let Operand::Move(p) = op {
                kill_local(state, p.local);
            }
            None
        }
        Terminator::Goto(_) | Terminator::Return | Terminator::Unreachable | Terminator::Resume => {
            None
        }
        // `function_is_fully_modeled` already decertified `Opaque` bodies.
        _ => {
            state.clear();
            None
        }
    }
}

/// `true` iff the `unwrap_or_else` closure operand provably IS
/// `|p| p.into_inner()` over a `PoisonError`: its unique def is a zero-capture
/// closure aggregate whose extracted body does nothing but return
/// `PoisonError::into_inner(param)` (call form) or `param.0` (inlined form),
/// reached only through whole-local moves. Anything else — a capture, an
/// unknown closure, a body with any other effect — is `false`: an arbitrary
/// `unwrap_or_else` closure could substitute a DIFFERENT guard.
fn closure_is_poison_into_inner(
    func: &VerifiableFunction,
    op: &Operand,
    closures: &FxHashMap<&str, &VerifiableFunction>,
) -> bool {
    let Some(cl_local) = operand_whole_local(op) else {
        return false;
    };
    // Unique whole-local def of the closure local, no projected writes.
    let mut def: Option<&Rvalue> = None;
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign { place, rvalue, .. } = stmt {
                if place.local == cl_local {
                    if !place.projections.is_empty() || def.is_some() {
                        return false;
                    }
                    def = Some(rvalue);
                }
            }
        }
        if let Terminator::Call { dest, .. } = &block.terminator {
            if dest.local == cl_local {
                return false;
            }
        }
    }
    let Some(Rvalue::Aggregate(AggregateKind::Closure { name, captures, .. }, ops)) = def else {
        return false;
    };
    if !ops.is_empty() || !captures.is_empty() {
        return false;
    }
    let Some(body) = closures.get(name.as_str()) else {
        return false;
    };
    closure_body_is_into_inner(body)
}

fn closure_body_is_into_inner(f: &VerifiableFunction) -> bool {
    // `FnOnce::call_once(closure_env, poison_error)` — 2 args, and the poison
    // param (local 2) must be a genuine `std::sync::PoisonError`.
    if f.body.arg_count != 2 {
        return false;
    }
    match local_ty(f, 2) {
        Some(Ty::Adt { name, .. }) if std_anchored(name) && name.ends_with("::PoisonError") => {}
        _ => return false,
    }
    // Chase the value returned in _0: allow only StorageLive/Dead statements,
    // whole-local moves, ONE `PoisonError::into_inner` call (or the inlined
    // `param.0` field move), and Goto/Return terminators.
    let mut ret_from_into_inner = false;
    for block in &f.body.blocks {
        for stmt in &block.stmts {
            match stmt {
                Statement::StorageLive(_) | Statement::StorageDead(_) => {}
                Statement::Assign { place, rvalue, .. } => {
                    if !place.projections.is_empty() {
                        return false;
                    }
                    match rvalue {
                        // Whole-local rearranging moves — but never INTO the
                        // return local (only `into_inner` may produce `_0`).
                        Rvalue::Use(Operand::Move(src))
                            if src.projections.is_empty() && place.local != 0 => {}
                        // Inlined `into_inner`: `_0 = move (_2.0)`.
                        Rvalue::Use(Operand::Move(src))
                            if src.projections.as_slice() == [Projection::Field(0)]
                                && place.local == 0 =>
                        {
                            if chases_to_param(f, src.local) {
                                ret_from_into_inner = true;
                            } else {
                                return false;
                            }
                        }
                        _ => return false,
                    }
                }
                _ => return false,
            }
        }
        match &block.terminator {
            Terminator::Goto(_) | Terminator::Return | Terminator::Resume => {}
            Terminator::Call { func: callee, args, dest, .. } => {
                let name = normalize_callee(callee);
                if !is_poison_into_inner_callee(&name)
                    || args.len() != 1
                    || !dest.projections.is_empty()
                    || dest.local != 0
                {
                    return false;
                }
                match operand_whole_local(&args[0]) {
                    Some(l) if chases_to_param(f, l) => ret_from_into_inner = true,
                    _ => return false,
                }
            }
            Terminator::Drop { .. } => return false,
            _ => return false,
        }
    }
    ret_from_into_inner
}

/// Does `local` chase back to the closure's `PoisonError` param (local 2)
/// through whole-local moves only? The param itself must never be REDEFINED in
/// the body (a redefinition could substitute a different `PoisonError`).
fn chases_to_param(f: &VerifiableFunction, mut local: usize) -> bool {
    let mut fuel = f.body.locals.len() + 1;
    loop {
        if local == 2 {
            return !local_has_any_def(f, 2);
        }
        if fuel == 0 {
            return false;
        }
        fuel -= 1;
        let mut def: Option<usize> = None;
        for block in &f.body.blocks {
            for stmt in &block.stmts {
                if let Statement::Assign { place, rvalue, .. } = stmt {
                    if place.local == local {
                        if !place.projections.is_empty() || def.is_some() {
                            return false;
                        }
                        match rvalue {
                            Rvalue::Use(Operand::Move(src)) if src.projections.is_empty() => {
                                def = Some(src.local);
                            }
                            _ => return false,
                        }
                    }
                }
            }
            if let Terminator::Call { dest, .. } = &block.terminator {
                if dest.local == local {
                    return false;
                }
            }
        }
        match def {
            Some(src) => local = src,
            None => return false,
        }
    }
}

/// Any def (whole or projected, assign or call destination) of `local`?
fn local_has_any_def(f: &VerifiableFunction, local: usize) -> bool {
    f.body.blocks.iter().any(|block| {
        block
            .stmts
            .iter()
            .any(|stmt| matches!(stmt, Statement::Assign { place, .. } if place.local == local))
            || matches!(&block.terminator, Terminator::Call { dest, .. } if dest.local == local)
    })
}

// ---------------------------------------------------------------------------
// Per-function analysis: fixpoint + whitelist accounting + constructor scan
// ---------------------------------------------------------------------------

fn terminator_successors(term: &Terminator) -> Vec<usize> {
    match term {
        Terminator::Goto(b) => vec![b.0],
        Terminator::SwitchInt { targets, otherwise, .. } => {
            let mut out: Vec<usize> = targets.iter().map(|(_, b)| b.0).collect();
            out.push(otherwise.0);
            out
        }
        Terminator::Call { target, .. } => target.iter().map(|b| b.0).collect(),
        Terminator::Assert { target, .. } | Terminator::Drop { target, .. } => vec![target.0],
        Terminator::Opaque { targets, .. } => targets.iter().map(|b| b.0).collect(),
        Terminator::Return | Terminator::Unreachable | Terminator::Resume => Vec::new(),
        _ => Vec::new(),
    }
}

fn analyze_function(
    func: &VerifiableFunction,
    candidates: &[PairedCondvarCandidate],
    closures: &FxHashMap<&str, &VerifiableFunction>,
    poisoned: &mut FxHashSet<(usize, usize)>,
    evidence: &mut FxHashMap<(usize, usize), FxHashSet<usize>>,
) {
    let nblocks = func.body.blocks.len();
    if nblocks == 0 {
        return;
    }
    let poison_all = |poisoned: &mut FxHashSet<(usize, usize)>| {
        for (ci, cand) in candidates.iter().enumerate() {
            for &k in cand.condvar_fields.iter().chain(&cand.mutex_fields) {
                poisoned.insert((ci, k));
            }
        }
    };

    // ---- 1. Fixpoint of the instance-pinned dataflow. ------------------
    let raw_exposed = raw_exposed_locals(func);
    let mut entry: Vec<Option<State>> = vec![None; nblocks];
    entry[0] = Some(State::default());
    let mut work: Vec<usize> = vec![0];
    while let Some(b) = work.pop() {
        let Some(block) = func.body.blocks.get(b) else { continue };
        let mut state = entry[b].clone().unwrap_or_default();
        for stmt in &block.stmts {
            apply_statement(&mut state, stmt, func, candidates, &raw_exposed);
        }
        let _ = apply_terminator(&mut state, &block.terminator, func, closures, &raw_exposed);
        for succ in terminator_successors(&block.terminator) {
            if succ >= nblocks {
                continue;
            }
            let merged = match &entry[succ] {
                None => state.clone(),
                Some(old) => join(old, &state),
            };
            if entry[succ].as_ref() != Some(&merged) {
                entry[succ] = Some(merged);
                work.push(succ);
            }
        }
    }

    // ---- 2. Final pass: wait-site validation results per block. --------
    // Unvisited blocks are processed with the EMPTY state (fail closed: any
    // wait site there is unvalidated).
    let mut wait_sites: FxHashMap<usize, Option<(usize, usize, usize)>> = FxHashMap::default();
    for (b, block) in func.body.blocks.iter().enumerate() {
        let mut state = entry[b].clone().unwrap_or_default();
        for stmt in &block.stmts {
            apply_statement(&mut state, stmt, func, candidates, &raw_exposed);
        }
        if let Some(site) =
            apply_terminator(&mut state, &block.terminator, func, closures, &raw_exposed)
        {
            wait_sites.insert(b, site.validated);
        }
    }

    // ---- 3. Crate-wide field-use whitelist (pass A: detection). --------
    // A paired-field mention is allowed ONLY as the TERMINAL projection of a
    // shared-borrow rvalue (vetted by consumer accounting in pass B). Every
    // other mention — write, read, move-out, `&mut`, raw borrow, drop, deeper
    // projection INTO the field — poisons the field.
    let mut opaque = false;
    for_each_place(func, &mut |place, ctx, loc| match candidate_field_mentions(
        func, place, candidates,
    ) {
        WalkOutcome::Opaque => opaque = true,
        WalkOutcome::Mentions(mentions) => {
            for (pos, ci, k) in mentions {
                let terminal = pos + 1 == place.projections.len();
                let allowed =
                    terminal && ctx == PlaceCtx::RefShared && matches!(loc, Loc::Stmt(..));
                if !allowed {
                    poisoned.insert((ci, k));
                }
            }
        }
    });
    if opaque {
        poison_all(poisoned);
        return;
    }

    // ---- 4. Pass B: shared-borrow consumer accounting. -----------------
    for (b, block) in func.body.blocks.iter().enumerate() {
        for (s, stmt) in block.stmts.iter().enumerate() {
            let Statement::Assign { place, rvalue, .. } = stmt else { continue };
            let Rvalue::Ref { mutable: false, place: borrowed } = rvalue else { continue };
            let Some((ci, _base, k)) = candidate_field_borrow(func, borrowed, candidates) else {
                // A terminal shared borrow is provisionally allowed by pass A
                // so the precise consumer accounting can run here. If its
                // projection reaches a paired field but the STRICT instance
                // parser rejects its base (raw-pointer deref, enum/index path,
                // unsupported type, ...), it is not an accountable safe borrow:
                // poison every paired field the detection walk found.
                match candidate_field_mentions(func, borrowed, candidates) {
                    WalkOutcome::Mentions(mentions) => {
                        for (_, mention_ci, mention_k) in mentions {
                            poisoned.insert((mention_ci, mention_k));
                        }
                    }
                    WalkOutcome::Opaque => poison_all(poisoned),
                }
                continue;
            };
            let cand = &candidates[ci];
            let is_c = cand.condvar_fields.contains(&k);
            let is_m = cand.mutex_fields.contains(&k);
            if !is_c && !is_m {
                continue;
            }
            if !place.projections.is_empty() {
                poisoned.insert((ci, k));
                continue;
            }
            let x = place.local;
            // The borrow local must have EXACTLY this one def and no aliasing.
            if !single_def_unaliased(func, x, b, s) {
                poisoned.insert((ci, k));
                continue;
            }
            // Every other mention must be an allowed consumer.
            let allowed = consumers_allowed(func, x, (b, s), is_c, ci, k, &wait_sites, evidence);
            if !allowed {
                poisoned.insert((ci, k));
            }
        }
    }

    // ---- 5. Constructor scan: every `S { … }` must build `c` fresh. -----
    let aliased = mut_aliased_locals(func);
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            let Statement::Assign { rvalue, .. } = stmt else { continue };
            let Rvalue::Aggregate(AggregateKind::Adt { name, variant, active_field, .. }, ops) = rvalue
            else {
                continue;
            };
            let Some(ci) = candidates.iter().position(|c| c.struct_name == *name) else {
                continue;
            };
            let cand = &candidates[ci];
            if *variant != 0 || active_field.is_some() || ops.len() != cand.field_count {
                for &k in cand.condvar_fields.iter().chain(&cand.mutex_fields) {
                    poisoned.insert((ci, k));
                }
                continue;
            }
            for &c in &cand.condvar_fields {
                if !ops.get(c).is_some_and(|op| operand_is_fresh_condvar(func, op, &aliased)) {
                    poisoned.insert((ci, c));
                }
            }
        }
    }
}

/// `local` has exactly one def — the given statement — no call-dest or
/// projected writes, and is never `&mut`/raw borrowed.
fn single_def_unaliased(func: &VerifiableFunction, local: usize, db: usize, ds: usize) -> bool {
    let mut defs = 0usize;
    for (b, block) in func.body.blocks.iter().enumerate() {
        for (s, stmt) in block.stmts.iter().enumerate() {
            match stmt {
                Statement::Assign { place, rvalue, .. } => {
                    if place.local == local {
                        if !place.projections.is_empty() || (b, s) != (db, ds) {
                            return false;
                        }
                        defs += 1;
                    }
                    match rvalue {
                        Rvalue::Ref { mutable: true, place: p } | Rvalue::AddressOf(_, p)
                            if p.local == local =>
                        {
                            return false;
                        }
                        _ => {}
                    }
                }
                _ => {}
            }
        }
        if let Terminator::Call { dest, .. } = &block.terminator {
            if dest.local == local {
                return false;
            }
        }
    }
    defs == 1
}

/// Locations where `local` is mentioned (any place occurrence, statement or
/// terminator), with per-location multiplicity. Storage markers are not
/// mentions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Loc {
    Stmt(usize, usize),
    Term(usize),
}

fn local_mention_sites(func: &VerifiableFunction, local: usize) -> Vec<(Loc, usize)> {
    let mut out: Vec<(Loc, usize)> = Vec::new();
    let mut push = |loc: Loc| match out.iter_mut().find(|(l, _)| *l == loc) {
        Some((_, n)) => *n += 1,
        None => out.push((loc, 1)),
    };
    for_each_place(func, &mut |place, _ctx, loc| {
        if place.local == local
            || place.projections.iter().any(|p| matches!(p, Projection::Index(i) if *i == local))
        {
            push(loc);
        }
    });
    out
}

/// Every mention of borrow local `x` (other than its def) must be a recognized
/// consumer call: wait-family/notify receiver for a condvar borrow, lock
/// receiver for a mutex borrow — appearing EXACTLY once, at argument 0. Wait
/// consumers must additionally be dataflow-VALIDATED; their sibling-mutex
/// evidence is recorded.
#[allow(clippy::too_many_arguments)]
fn consumers_allowed(
    func: &VerifiableFunction,
    x: usize,
    def: (usize, usize),
    is_condvar: bool,
    ci: usize,
    k: usize,
    wait_sites: &FxHashMap<usize, Option<(usize, usize, usize)>>,
    evidence: &mut FxHashMap<(usize, usize), FxHashSet<usize>>,
) -> bool {
    // MIR local 0 is the implicit return place. `Return` carries no explicit
    // operand in `Terminator`, so a borrow written directly to `_0` would have
    // no second place mention for the accounting loop below. It is nevertheless
    // an escape to the caller and must always decertify.
    if x == 0 {
        return false;
    }
    for (loc, count) in local_mention_sites(func, x) {
        if loc == Loc::Stmt(def.0, def.1) {
            if count != 1 {
                return false; // the def statement mentions x more than once
            }
            continue;
        }
        let Loc::Term(tb) = loc else {
            return false; // any statement-level consumer is unrecognized
        };
        let Some(Terminator::Call { func: callee, args, .. }) =
            func.body.blocks.get(tb).map(|bl| &bl.terminator)
        else {
            return false;
        };
        // x must appear exactly once, as the whole-local receiver (arg 0).
        if count != 1 || args.first().and_then(operand_whole_local) != Some(x) {
            return false;
        }
        let name = normalize_callee(callee);
        if is_condvar {
            if recognized_wait_family(&name).is_some() {
                match wait_sites.get(&tb) {
                    Some(Some((vc, vk, m))) if *vc == ci && *vk == k => {
                        evidence.entry((ci, k)).or_default().insert(*m);
                    }
                    _ => return false, // unvalidated wait site
                }
            } else if !is_notify_callee(&name) {
                return false;
            }
        } else if !is_lock_callee(&name) {
            return false;
        }
    }
    true
}

/// The constructor-freshness chase: `op` must be a whole-local move whose value
/// chains, through unique-def unaliased whole-local moves each mentioned
/// exactly at its def and its single consumption, to a same-body
/// `Condvar::new()` call.
fn operand_is_fresh_condvar(
    func: &VerifiableFunction,
    op: &Operand,
    aliased: &FxHashSet<usize>,
) -> bool {
    let Operand::Move(p) = op else { return false };
    if !p.projections.is_empty() {
        return false;
    }
    let mut local = p.local;
    let mut fuel = func.body.locals.len() + 1;
    loop {
        if fuel == 0 || aliased.contains(&local) {
            return false;
        }
        fuel -= 1;
        // Mentions: exactly 2 (one def + one consumption).
        let mentions: usize = local_mention_sites(func, local).iter().map(|(_, n)| n).sum();
        if mentions != 2 {
            return false;
        }
        // Unique def.
        let mut assign_def: Option<&Rvalue> = None;
        let mut call_def: Option<&Terminator> = None;
        for block in &func.body.blocks {
            for stmt in &block.stmts {
                if let Statement::Assign { place, rvalue, .. } = stmt {
                    if place.local == local {
                        if !place.projections.is_empty()
                            || assign_def.is_some()
                            || call_def.is_some()
                        {
                            return false;
                        }
                        assign_def = Some(rvalue);
                    }
                }
            }
            if let Terminator::Call { dest, .. } = &block.terminator {
                if dest.local == local {
                    if !dest.projections.is_empty() || assign_def.is_some() || call_def.is_some() {
                        return false;
                    }
                    call_def = Some(&block.terminator);
                }
            }
        }
        match (assign_def, call_def) {
            (None, Some(Terminator::Call { func: callee, args, .. })) => {
                let name = normalize_callee(callee);
                return is_condvar_new_callee(&name) && args.is_empty();
            }
            (Some(Rvalue::Use(Operand::Move(src))), None) if src.projections.is_empty() => {
                local = src.local;
            }
            _ => return false,
        }
    }
}

fn mut_aliased_locals(func: &VerifiableFunction) -> FxHashSet<usize> {
    let mut out = FxHashSet::default();
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign { rvalue, .. } = stmt {
                match rvalue {
                    Rvalue::Ref { mutable: true, place } | Rvalue::AddressOf(_, place) => {
                        out.insert(place.local);
                    }
                    _ => {}
                }
            }
        }
    }
    out
}

// ---------------------------------------------------------------------------
// Exhaustive place enumeration
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PlaceCtx {
    /// The rvalue of `_x = &place` (shared).
    RefShared,
    /// Everything else: writes, reads, `&mut`, raw borrows, drops, call args…
    Other,
}

/// Visit EVERY place occurring in the function — assign destinations, all
/// rvalue operands and borrow/inspect places, call args + destinations, drop /
/// switch / assert / intrinsic operands, and `Unsupported` payload operands —
/// so no paired-field use can hide from the whitelist scan.
fn for_each_place(func: &VerifiableFunction, f: &mut impl FnMut(&Place, PlaceCtx, Loc)) {
    for (b, block) in func.body.blocks.iter().enumerate() {
        for (s, stmt) in block.stmts.iter().enumerate() {
            let loc = Loc::Stmt(b, s);
            match stmt {
                Statement::Assign { place, rvalue, .. } => {
                    f(place, PlaceCtx::Other, loc);
                    match rvalue {
                        Rvalue::Ref { mutable: false, place: p } => f(p, PlaceCtx::RefShared, loc),
                        Rvalue::Ref { mutable: true, place: p }
                        | Rvalue::AddressOf(_, p)
                        | Rvalue::Discriminant(p)
                        | Rvalue::Len(p)
                        | Rvalue::CopyForDeref(p) => f(p, PlaceCtx::Other, loc),
                        _ => {}
                    }
                    for_each_rvalue_operand(rvalue, &mut |op| {
                        if let Some(p) = operand_place(op) {
                            f(p, PlaceCtx::Other, loc);
                        }
                    });
                }
                Statement::SetDiscriminant { place, .. }
                | Statement::Deinit { place }
                | Statement::Retag { place }
                | Statement::PlaceMention(place) => f(place, PlaceCtx::Other, loc),
                Statement::Intrinsic { args, .. } => {
                    for op in args {
                        if let Some(p) = operand_place(op) {
                            f(p, PlaceCtx::Other, loc);
                        }
                    }
                }
                Statement::Unsupported { operands, .. } => {
                    for op in operands {
                        if let Some(p) = operand_place(op) {
                            f(p, PlaceCtx::Other, loc);
                        }
                    }
                }
                Statement::StorageLive(_) | Statement::StorageDead(_) => {}
                _ => {}
            }
        }
        let loc = Loc::Term(b);
        match &block.terminator {
            Terminator::Call { args, dest, .. } => {
                for op in args {
                    if let Some(p) = operand_place(op) {
                        f(p, PlaceCtx::Other, loc);
                    }
                }
                f(dest, PlaceCtx::Other, loc);
            }
            Terminator::SwitchInt { discr, .. } => {
                if let Some(p) = operand_place(discr) {
                    f(p, PlaceCtx::Other, loc);
                }
            }
            Terminator::Assert { cond, .. } => {
                if let Some(p) = operand_place(cond) {
                    f(p, PlaceCtx::Other, loc);
                }
            }
            Terminator::Drop { place, .. } => f(place, PlaceCtx::Other, loc),
            _ => {}
        }
    }
}

// ---------------------------------------------------------------------------
// Tests — the positive control and the falsification mutants from the
// adversarial review. Every mutant MUST decertify (0 false-PROVE tolerance).
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use trust_types::{
        BasicBlock, BlockId, ClosureCallKind, ConstValue, LocalDecl, SourceSpan, VerifiableBody,
    };

    use super::*;

    fn span() -> SourceSpan {
        SourceSpan::default()
    }

    fn adt(name: &str, fields: Vec<(&str, Ty)>) -> Ty {
        Ty::Adt { adt_kind: None, layout: None, 
            variants: Vec::new(),
            name: name.into(),
            fields: fields.into_iter().map(|(n, t)| (n.to_string(), t)).collect(),
            disc_index_safe: false,
            faithful_enum_repr: None, enum_layout: None, }
    }

    fn condvar_ty() -> Ty {
        adt("std::sync::Condvar", vec![])
    }
    fn mutex_ty() -> Ty {
        adt("std::sync::Mutex", vec![])
    }
    fn guard_ty() -> Ty {
        adt("std::sync::MutexGuard", vec![])
    }
    fn result_ty() -> Ty {
        adt("std::result::Result", vec![])
    }
    fn poison_ty() -> Ty {
        adt("std::sync::PoisonError", vec![])
    }
    /// `Shared { lock: Mutex<()>, spill: Mutex<Vec<u8>>, drained: Condvar }` —
    /// the aterm shape, TWO mutex fields (one benign refactor from mixed
    /// evidence).
    fn shared_ty() -> Ty {
        adt("Shared", vec![("lock", mutex_ty()), ("spill", mutex_ty()), ("drained", condvar_ty())])
    }
    fn shared_ref() -> Ty {
        Ty::Ref { mutable: false, inner: Box::new(shared_ty()) }
    }

    fn cand() -> PairedCondvarCandidate {
        PairedCondvarCandidate {
            struct_name: "Shared".into(),
            condvar_fields: vec![2],
            mutex_fields: vec![0, 1],
            field_count: 3,
        }
    }

    const LOCK: &str = "std::sync::Mutex::<Vec<u8>>::lock";
    const LOCK0: &str = "std::sync::Mutex::<()>::lock";
    const WAIT: &str = "std::sync::Condvar::wait::<Vec<u8>>";
    const WAIT_TIMEOUT: &str = "std::sync::Condvar::wait_timeout::<Vec<u8>>";
    const UNWRAP: &str = "std::result::Result::<std::sync::MutexGuard<'_, Vec<u8>>, \
                          std::sync::PoisonError<std::sync::MutexGuard<'_, Vec<u8>>>>::unwrap";
    const UNWRAP_OR_ELSE: &str = "std::result::Result::<std::sync::MutexGuard<'_, Vec<u8>>, \
         std::sync::PoisonError<std::sync::MutexGuard<'_, Vec<u8>>>>::unwrap_or_else::<{closure}>";
    const CONDVAR_NEW: &str = "std::sync::Condvar::new";
    const MUTEX_NEW: &str = "std::sync::Mutex::<Vec<u8>>::new";
    const INTO_INNER: &str =
        "std::sync::PoisonError::<std::sync::MutexGuard<'_, Vec<u8>>>::into_inner";
    const NOTIFY_ALL: &str = "std::sync::Condvar::notify_all";

    fn func(
        name: &str,
        arg_count: usize,
        locals: Vec<Ty>,
        blocks: Vec<BasicBlock>,
    ) -> VerifiableFunction {
        VerifiableFunction {
            name: name.into(),
            def_path: name.into(),
            span: span(),
            body: VerifiableBody {
                return_ty: Ty::Unit,
                locals: locals
                    .into_iter()
                    .enumerate()
                    .map(|(index, ty)| LocalDecl { index, ty, name: None })
                    .collect(),
                blocks,
                arg_count,
            },
            contracts: Vec::new(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            spec: Default::default(),
        }
    }

    fn block(id: usize, stmts: Vec<Statement>, terminator: Terminator) -> BasicBlock {
        BasicBlock { id: BlockId(id), stmts, terminator }
    }

    fn assign(local: usize, rvalue: Rvalue) -> Statement {
        Statement::Assign { place: Place::local(local), rvalue, span: span() }
    }

    fn mv(local: usize) -> Operand {
        Operand::Move(Place::local(local))
    }

    /// `_dst = &((*_base).field)` — the canonical field-borrow shape.
    fn borrow_field(dst: usize, base: usize, field: usize) -> Statement {
        assign(
            dst,
            Rvalue::Ref {
                mutable: false,
                place: Place {
                    local: base,
                    projections: vec![Projection::Deref, Projection::Field(field)],
                },
            },
        )
    }

    fn call(callee: &str, args: Vec<Operand>, dest: usize, target: usize) -> Terminator {
        Terminator::Call {
            unwind: trust_types::UnwindEdge::Unreachable,
            func: callee.into(),
            args,
            dest: Place::local(dest),
            target: Some(BlockId(target)),
            span: span(),
            atomic: None,
            is_foreign: false,
            is_unsafe_sig: false,
        }
    }

    fn closure_agg(name: &str) -> Rvalue {
        Rvalue::Aggregate(
            AggregateKind::Closure {
                name: name.into(),
                captures: Vec::new(),
                call_kind: ClosureCallKind::FnOnce,
            },
            Vec::new(),
        )
    }

    /// `|p| p.into_inner()` — pre-inline shape: `_3 = move _2;
    /// _0 = PoisonError::into_inner(move _3); return`.
    fn into_inner_closure(def_path: &str) -> VerifiableFunction {
        func(
            def_path,
            2,
            vec![guard_ty(), Ty::Unit, poison_ty(), poison_ty()],
            vec![
                block(
                    0,
                    vec![Statement::StorageLive(3), assign(3, Rvalue::Use(mv(2)))],
                    call(INTO_INNER, vec![mv(3)], 0, 1),
                ),
                block(1, vec![Statement::StorageDead(3)], Terminator::Return),
            ],
        )
    }

    /// The POSITIVE CONTROL: the aterm `spill_append` shape —
    /// `let mut s = self.spill.lock().unwrap_or_else(|p| p.into_inner());
    ///  while cond { s = self.drained.wait(s).unwrap_or_else(|p| p.into_inner()); }`
    /// (single instance, loop-carried guard).
    fn spill_append() -> VerifiableFunction {
        func(
            "Shared::spill_append",
            1,
            vec![
                Ty::Unit,     // 0: return
                shared_ref(), // 1: self
                guard_ty(),   // 2: s
                result_ty(),  // 3: lock result
                mutex_ty(),   // 4: &spill temp (Ref ty elided — unused by walker)
                Ty::Unit,     // 5: closure env
                Ty::Bool,     // 6: loop condition
                guard_ty(),   // 7: wait guard arg temp
                result_ty(),  // 8: wait result
                condvar_ty(), // 9: &drained temp
                Ty::Unit,     // 10: closure env
                guard_ty(),   // 11: unwrapped wait guard
            ],
            vec![
                block(0, vec![borrow_field(4, 1, 1)], call(LOCK, vec![mv(4)], 3, 1)),
                block(
                    1,
                    vec![assign(5, closure_agg("Shared::spill_append::{closure#0}"))],
                    call(UNWRAP_OR_ELSE, vec![mv(3), mv(5)], 2, 2),
                ),
                block(2, vec![], Terminator::Goto(BlockId(3))),
                block(
                    3,
                    vec![],
                    Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(6)),
                        targets: vec![(0, BlockId(7))],
                        otherwise: BlockId(4),
                        exhaustive_enum_unreachable: false,
                        span: span(),
                    },
                ),
                block(
                    4,
                    vec![borrow_field(9, 1, 2), assign(7, Rvalue::Use(mv(2)))],
                    call(WAIT, vec![mv(9), mv(7)], 8, 5),
                ),
                block(
                    5,
                    vec![assign(10, closure_agg("Shared::spill_append::{closure#1}"))],
                    call(UNWRAP_OR_ELSE, vec![mv(8), mv(10)], 11, 6),
                ),
                block(6, vec![assign(2, Rvalue::Use(mv(11)))], Terminator::Goto(BlockId(3))),
                block(
                    7,
                    vec![],
                    Terminator::Drop {
                        place: Place::local(2),
                        target: BlockId(8),
                        span: span(),
                        unwind: Default::default(),
                    },
                ),
                block(8, vec![], Terminator::Return),
            ],
        )
    }

    /// `Shared::new()` — all three fields freshly constructed in-body.
    fn shared_ctor() -> VerifiableFunction {
        func(
            "Shared::new",
            0,
            vec![shared_ty(), mutex_ty(), mutex_ty(), condvar_ty()],
            vec![
                block(0, vec![], call(MUTEX_NEW, vec![], 1, 1)),
                block(1, vec![], call(MUTEX_NEW, vec![], 2, 2)),
                block(2, vec![], call(CONDVAR_NEW, vec![], 3, 3)),
                block(
                    3,
                    vec![assign(
                        0,
                        Rvalue::Aggregate(
                            AggregateKind::Adt {
                                name: "Shared".into(),
                                variant: 0,
                                active_field: None,
                                args: None,
                            },
                            vec![mv(1), mv(2), mv(3)],
                        ),
                    )],
                    Terminator::Return,
                ),
            ],
        )
    }

    fn positive_set() -> Vec<VerifiableFunction> {
        vec![
            shared_ctor(),
            spill_append(),
            into_inner_closure("Shared::spill_append::{closure#0}"),
            into_inner_closure("Shared::spill_append::{closure#1}"),
        ]
    }

    fn certify(functions: &[VerifiableFunction]) -> Vec<CertifiedCondvarPair> {
        certify_paired_condvars(functions, &[cand()])
    }

    #[test]
    fn positive_control_loop_carried_wait_certifies() {
        let certified = certify(&positive_set());
        assert_eq!(
            certified,
            vec![CertifiedCondvarPair {
                struct_name: "Shared".into(),
                condvar_field: 2,
                mutex_field: 1,
            }],
            "the aterm spill_append shape (single instance, loop-carried \
             `s = self.drained.wait(s).unwrap_or_else(|p| p.into_inner())`) must certify"
        );
    }

    /// Attack A (confirmed false-PROVE against field-keyed designs):
    /// `g = a.spill.lock().unwrap(); g = a.drained.wait(g).unwrap();
    ///  b.drained.wait(g)` — std's wait returns the SAME guard, so a
    /// field-keyed fixed point accepts the cross-instance thread. The
    /// instance-pinned fact (B = `a`) must NOT validate the `b.drained` site.
    #[test]
    fn attack_a_cross_instance_guard_threading_decertifies() {
        let attack = func(
            "cross_instance",
            2,
            vec![
                Ty::Unit,     // 0
                shared_ref(), // 1: a
                shared_ref(), // 2: b
                mutex_ty(),   // 3: &a.spill
                result_ty(),  // 4
                guard_ty(),   // 5
                condvar_ty(), // 6: &a.drained
                result_ty(),  // 7
                guard_ty(),   // 8
                condvar_ty(), // 9: &b.drained
                result_ty(),  // 10
            ],
            vec![
                block(0, vec![borrow_field(3, 1, 1)], call(LOCK, vec![mv(3)], 4, 1)),
                block(1, vec![], call(UNWRAP, vec![mv(4)], 5, 2)),
                block(2, vec![borrow_field(6, 1, 2)], call(WAIT, vec![mv(6), mv(5)], 7, 3)),
                block(3, vec![], call(UNWRAP, vec![mv(7)], 8, 4)),
                block(4, vec![borrow_field(9, 2, 2)], call(WAIT, vec![mv(9), mv(8)], 10, 5)),
                block(
                    5,
                    vec![],
                    Terminator::Drop {
                        place: Place::local(10),
                        target: BlockId(6),
                        span: span(),
                        unwind: Default::default(),
                    },
                ),
                block(6, vec![], Terminator::Return),
            ],
        );
        let mut fns = positive_set();
        fns.push(attack);
        assert_eq!(certify(&fns), vec![], "cross-instance guard threading must decertify");
    }

    /// Attack B (confirmed false-PROVE against name-identity designs):
    /// `let mut r = &a; let g = r.spill.lock().unwrap(); r = &b;
    ///  r.drained.wait(g)` — same base local NAME, different dynamic instance.
    /// Kill-at-def of `r` must void the guard fact.
    #[test]
    fn attack_b_receiver_rebinding_decertifies() {
        let attack = func(
            "rebinding",
            2,
            vec![
                Ty::Unit,     // 0
                shared_ref(), // 1: a
                shared_ref(), // 2: b
                shared_ref(), // 3: r
                mutex_ty(),   // 4: &r.spill
                result_ty(),  // 5
                guard_ty(),   // 6
                condvar_ty(), // 7: &r.drained
                result_ty(),  // 8
            ],
            vec![
                block(
                    0,
                    vec![
                        assign(3, Rvalue::Use(Operand::Copy(Place::local(1)))),
                        borrow_field(4, 3, 1),
                    ],
                    call(LOCK, vec![mv(4)], 5, 1),
                ),
                block(1, vec![], call(UNWRAP, vec![mv(5)], 6, 2)),
                block(
                    2,
                    vec![
                        assign(3, Rvalue::Use(Operand::Copy(Place::local(2)))), // r = &b
                        borrow_field(7, 3, 2),
                    ],
                    call(WAIT, vec![mv(7), mv(6)], 8, 3),
                ),
                block(
                    3,
                    vec![],
                    Terminator::Drop {
                        place: Place::local(8),
                        target: BlockId(4),
                        span: span(),
                        unwind: Default::default(),
                    },
                ),
                block(4, vec![], Terminator::Return),
            ],
        );
        let mut fns = positive_set();
        fns.push(attack);
        assert_eq!(certify(&fns), vec![], "receiver rebinding must decertify");
    }

    /// Attack C (kill-at-def variant): the guard is loop-carried but the BASE
    /// local's def sits INSIDE the loop — each back edge re-executes it with a
    /// possibly-new instance, so the fact must die on the back edge and the
    /// merged loop-head state must not validate the wait.
    #[test]
    fn attack_c_base_def_inside_loop_decertifies() {
        let attack = func(
            "loop_base_def",
            0,
            vec![
                Ty::Unit,     // 0
                Ty::Unit,     // 1 (unused)
                shared_ref(), // 2: r (defined by pick(), re-defined in loop)
                mutex_ty(),   // 3: &r.spill
                result_ty(),  // 4
                guard_ty(),   // 5: g
                condvar_ty(), // 6: &r.drained
                result_ty(),  // 7
                guard_ty(),   // 8
            ],
            vec![
                block(0, vec![], call("pick", vec![], 2, 1)),
                block(1, vec![borrow_field(3, 2, 1)], call(LOCK, vec![mv(3)], 4, 2)),
                block(2, vec![], call(UNWRAP, vec![mv(4)], 5, 3)),
                // loop head: wait with g, then unwrap, re-assign g, REDEFINE r.
                block(3, vec![borrow_field(6, 2, 2)], call(WAIT, vec![mv(6), mv(5)], 7, 4)),
                block(4, vec![], call(UNWRAP, vec![mv(7)], 8, 5)),
                block(5, vec![assign(5, Rvalue::Use(mv(8)))], call("pick", vec![], 2, 3)),
            ],
        );
        let mut fns = positive_set();
        fns.push(attack);
        assert_eq!(
            certify(&fns),
            vec![],
            "a base-local def inside the loop must kill the loop-carried fact"
        );
    }

    /// Attack D: mixed sibling evidence. One site waits `drained` with the
    /// `spill` guard, another with the `lock: Mutex<()>` guard — `Shared` is
    /// one benign refactor from this. NEVER select a winner: decertify.
    #[test]
    fn attack_d_mixed_sibling_evidence_decertifies() {
        let wrong_sibling = func(
            "wrong_sibling",
            1,
            vec![
                Ty::Unit,     // 0
                shared_ref(), // 1
                mutex_ty(),   // 2: &self.lock (field 0!)
                result_ty(),  // 3
                guard_ty(),   // 4
                condvar_ty(), // 5
                result_ty(),  // 6
            ],
            vec![
                block(0, vec![borrow_field(2, 1, 0)], call(LOCK0, vec![mv(2)], 3, 1)),
                block(1, vec![], call(UNWRAP, vec![mv(3)], 4, 2)),
                block(2, vec![borrow_field(5, 1, 2)], call(WAIT, vec![mv(5), mv(4)], 6, 3)),
                block(
                    3,
                    vec![],
                    Terminator::Drop {
                        place: Place::local(6),
                        target: BlockId(4),
                        span: span(),
                        unwind: Default::default(),
                    },
                ),
                block(4, vec![], Terminator::Return),
            ],
        );
        let mut fns = positive_set(); // evidence m=1 (spill)…
        fns.push(wrong_sibling); //     …plus evidence m=0 (lock): MIXED.
        assert_eq!(certify(&fns), vec![], "mixed sibling evidence must decertify");
    }

    /// Pair discovery is from guard evidence only: a crate that CONSISTENTLY
    /// pairs `drained` with `lock: Mutex<()>` (never `spill`) certifies THAT
    /// pair — the pairing axiom holds for it just as well.
    #[test]
    fn consistent_alternative_sibling_certifies_that_pair() {
        let wrong_sibling = func(
            "consistent_lock_pairing",
            1,
            vec![
                Ty::Unit,
                shared_ref(),
                mutex_ty(),
                result_ty(),
                guard_ty(),
                condvar_ty(),
                result_ty(),
            ],
            vec![
                block(0, vec![borrow_field(2, 1, 0)], call(LOCK0, vec![mv(2)], 3, 1)),
                block(1, vec![], call(UNWRAP, vec![mv(3)], 4, 2)),
                block(2, vec![borrow_field(5, 1, 2)], call(WAIT, vec![mv(5), mv(4)], 6, 3)),
                block(
                    3,
                    vec![],
                    Terminator::Drop {
                        place: Place::local(6),
                        target: BlockId(4),
                        span: span(),
                        unwind: Default::default(),
                    },
                ),
                block(4, vec![], Terminator::Return),
            ],
        );
        let certified = certify(&[shared_ctor(), wrong_sibling]);
        assert_eq!(
            certified,
            vec![CertifiedCondvarPair {
                struct_name: "Shared".into(),
                condvar_field: 2,
                mutex_field: 0,
            }],
        );
    }

    /// Mutant (f): a constructor-injected `Condvar` may arrive PRE-BOUND to a
    /// foreign mutex — freshness is not provable, so the pair decertifies.
    #[test]
    fn constructor_injected_condvar_decertifies() {
        let injected = func(
            "Shared::with_condvar",
            1,
            vec![shared_ty(), condvar_ty(), mutex_ty(), mutex_ty()],
            vec![
                block(0, vec![], call(MUTEX_NEW, vec![], 2, 1)),
                block(1, vec![], call(MUTEX_NEW, vec![], 3, 2)),
                block(
                    2,
                    vec![assign(
                        0,
                        Rvalue::Aggregate(
                            AggregateKind::Adt {
                                name: "Shared".into(),
                                variant: 0,
                                active_field: None,
                                args: None,
                            },
                            vec![mv(2), mv(3), mv(1)], // field 2 (drained) = param!
                        ),
                    )],
                    Terminator::Return,
                ),
            ],
        );
        let mut fns = positive_set();
        fns.push(injected);
        assert_eq!(certify(&fns), vec![], "constructor-injected condvar must decertify");
    }

    /// Mutant (g): `&mut self.drained` (the `mem::swap` vector) — ANY `&mut`
    /// of a paired field decertifies via the field-use whitelist.
    #[test]
    fn mut_borrow_of_field_decertifies() {
        let swapper = func(
            "swapper",
            1,
            vec![Ty::Unit, shared_ref(), condvar_ty()],
            vec![block(
                0,
                vec![assign(
                    2,
                    Rvalue::Ref {
                        mutable: true,
                        place: Place {
                            local: 1,
                            projections: vec![Projection::Deref, Projection::Field(2)],
                        },
                    },
                )],
                Terminator::Return,
            )],
        );
        let mut fns = positive_set();
        fns.push(swapper);
        assert_eq!(certify(&fns), vec![], "&mut of a paired field must decertify");
    }

    /// Mutant (h): `&self.drained` escaping (returned / passed to a helper) —
    /// an unaccounted consumer of the condvar borrow decertifies.
    #[test]
    fn escaping_condvar_borrow_decertifies() {
        let escape = func(
            "escape",
            1,
            vec![condvar_ty(), shared_ref(), condvar_ty()],
            vec![block(
                0,
                vec![borrow_field(2, 1, 2), assign(0, Rvalue::Use(mv(2)))],
                Terminator::Return,
            )],
        );
        let mut fns = positive_set();
        fns.push(escape);
        assert_eq!(certify(&fns), vec![], "an escaping &self.c must decertify");
    }

    /// The direct MIR return shape `_0 = &self.drained; return` has no explicit
    /// `_0` operand on `Terminator::Return`; local 0 itself must be recognized as
    /// an escape rather than appearing to have only its allowed defining use.
    #[test]
    fn direct_return_place_condvar_borrow_decertifies() {
        let escape = func(
            "escape_direct",
            1,
            vec![condvar_ty(), shared_ref()],
            vec![block(0, vec![borrow_field(0, 1, 2)], Terminator::Return)],
        );
        let mut fns = positive_set();
        fns.push(escape);
        assert_eq!(
            certify(&fns),
            vec![],
            "a paired field borrowed directly into MIR return place _0 must decertify"
        );
    }

    /// One UNVALIDATED wait site poisons the WHOLE pair (the discharge is
    /// receiver-shape-only and crate-wide): here a wait whose guard is an
    /// opaque parameter, not a recognized lock of the same instance.
    #[test]
    fn unvalidated_wait_site_poisons_whole_pair() {
        let rogue = func(
            "rogue_wait",
            2,
            vec![
                result_ty(),  // 0 (dest)
                shared_ref(), // 1
                guard_ty(),   // 2: guard PARAM — provenance unknown
                condvar_ty(), // 3
            ],
            vec![
                block(0, vec![borrow_field(3, 1, 2)], call(WAIT, vec![mv(3), mv(2)], 0, 1)),
                block(1, vec![], Terminator::Return),
            ],
        );
        let mut fns = positive_set();
        fns.push(rogue);
        assert_eq!(certify(&fns), vec![], "one unvalidated wait site must poison the pair");
    }

    /// `notify_one`/`notify_all` receivers are whitelisted consumers (they
    /// never reach the pthread verify()); their presence must not decertify.
    #[test]
    fn notify_receiver_is_allowed() {
        let notifier = func(
            "notifier",
            1,
            vec![Ty::Unit, shared_ref(), condvar_ty()],
            vec![
                block(0, vec![borrow_field(2, 1, 2)], call(NOTIFY_ALL, vec![mv(2)], 0, 1)),
                block(1, vec![], Terminator::Return),
            ],
        );
        let mut fns = positive_set();
        fns.push(notifier);
        assert_eq!(certify(&fns).len(), 1, "a notify site must not decertify");
    }

    /// `wait_timeout` is VALIDATED like `wait` (it reaches the same pthread
    /// verify()), but its tuple result carries no fact (fail closed) and it is
    /// never marker-discharged.
    #[test]
    fn wait_timeout_site_validates() {
        let wt = func(
            "waits_with_timeout",
            1,
            vec![
                Ty::Unit,     // 0
                shared_ref(), // 1
                mutex_ty(),   // 2
                result_ty(),  // 3
                guard_ty(),   // 4
                condvar_ty(), // 5
                result_ty(),  // 6
            ],
            vec![
                block(0, vec![borrow_field(2, 1, 1)], call(LOCK, vec![mv(2)], 3, 1)),
                block(1, vec![], call(UNWRAP, vec![mv(3)], 4, 2)),
                block(
                    2,
                    vec![borrow_field(5, 1, 2)],
                    call(
                        WAIT_TIMEOUT,
                        vec![mv(5), mv(4), Operand::Constant(ConstValue::Int(1))],
                        6,
                        3,
                    ),
                ),
                block(
                    3,
                    vec![],
                    Terminator::Drop {
                        place: Place::local(6),
                        target: BlockId(4),
                        span: span(),
                        unwind: Default::default(),
                    },
                ),
                block(4, vec![], Terminator::Return),
            ],
        );
        let certified = certify(&[shared_ctor(), wt]);
        assert_eq!(certified.len(), 1, "a validated wait_timeout site must not decertify");
    }

    /// The `unwrap_or_else` closure gate: an arbitrary closure could return a
    /// DIFFERENT guard, so a non-`into_inner` closure must block the fact (and
    /// the downstream wait site then poisons the pair).
    #[test]
    fn arbitrary_unwrap_or_else_closure_blocks_fact() {
        let evil_closure = func(
            "Shared::spill_append::{closure#0}",
            2,
            vec![guard_ty(), Ty::Unit, poison_ty()],
            vec![
                block(0, vec![], call("evil::guard_source", vec![], 0, 1)),
                block(1, vec![], Terminator::Return),
            ],
        );
        let mut fns = positive_set();
        // Replace closure#0's body with the evil one.
        fns.retain(|f| f.def_path != "Shared::spill_append::{closure#0}");
        fns.push(evil_closure);
        assert_eq!(
            certify(&fns),
            vec![],
            "an unwrap_or_else closure that is not PoisonError::into_inner must decertify"
        );
    }

    /// Unmodeled control flow (inline asm, coroutine resume, …) anywhere in
    /// the crate decertifies everything — its effect on the fields is
    /// unknowable.
    #[test]
    fn opaque_terminator_decertifies_crate() {
        let opaque = func(
            "has_asm",
            0,
            vec![Ty::Unit],
            vec![block(
                0,
                vec![],
                Terminator::Opaque { kind: "InlineAsm".into(), targets: vec![], span: span() },
            )],
        );
        let mut fns = positive_set();
        fns.push(opaque);
        assert_eq!(certify(&fns), vec![], "unmodeled control flow must decertify the crate");
    }

    /// A raw address-of the base local escapes the borrow checker: a later
    /// deref-store through it is invisible to the flow-sensitive kills, so no
    /// fact may be pinned through that local.
    #[test]
    fn raw_address_of_base_blocks_facts() {
        let mut f = spill_append();
        // Prepend `_7 = &raw const (*_1)` (locals[7] reused as scratch —
        // the AddressOf set is keyed by the BORROWED base, local 1).
        f.body.blocks[0].stmts.insert(
            0,
            assign(
                7,
                Rvalue::AddressOf(false, Place { local: 1, projections: vec![Projection::Deref] }),
            ),
        );
        let mut fns = positive_set();
        fns.retain(|x| x.def_path != "Shared::spill_append");
        fns.push(f);
        assert_eq!(
            certify(&fns),
            vec![],
            "a raw address-of the base local must block instance pinning"
        );
    }

    /// A shared borrow reached through `*const Shared` is outside the safe,
    /// instance-pinned projection grammar. Pass A must not let the terminal
    /// `Field` shape hide that rejected raw-pointer base.
    #[test]
    fn shared_borrow_through_raw_base_decertifies() {
        let raw_borrow = func(
            "raw_borrow",
            1,
            vec![
                Ty::Unit,
                Ty::RawPtr { mutable: false, pointee: Box::new(shared_ty()) },
                condvar_ty(),
            ],
            vec![block(
                0,
                vec![assign(
                    2,
                    Rvalue::Ref {
                        mutable: false,
                        place: Place {
                            local: 1,
                            projections: vec![Projection::Deref, Projection::Field(2)],
                        },
                    },
                )],
                Terminator::Return,
            )],
        );
        let mut fns = positive_set();
        fns.push(raw_borrow);
        assert_eq!(
            certify(&fns),
            vec![],
            "a paired-field borrow through a raw-pointer base must decertify"
        );
    }

    /// Compiler-side legs (pub field, missing attribute, impersonating local
    /// `mod std`, stolen bodies) all manifest here as an EMPTY candidate list:
    /// nothing certifies.
    #[test]
    fn no_candidates_certifies_nothing() {
        assert_eq!(certify_paired_condvars(&positive_set(), &[]), vec![]);
    }

    /// No guard evidence (a crate that never waits) certifies nothing — pair
    /// discovery is from evidence only.
    #[test]
    fn no_wait_evidence_certifies_nothing() {
        assert_eq!(certify(&[shared_ctor()]), vec![]);
    }
}
