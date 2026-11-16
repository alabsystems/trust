//! TINV step 4b: the place-write classifier, keyed by the parent ADT of every field a
//! write reaches (`docs/design/2026-10-04-type-invariant-tinv.md` §6 step 4).
//!
//! [`classify_writes`] lists, for one function, every write to a field of a struct and
//! every call argument whose type can reach one, and fails closed on writes it cannot
//! place. It grants no authority. Two lanes read it: the backing certifier, where it only
//! ADDS denials to the old index-only scan ([`writes_fields_of`]), and TINV (steps 6-7),
//! which refuses a candidate on any write it cannot attribute ([`tinv_refusal`]).
//!
//! The classification sits on the trust-types write taxonomy
//! ([`Statement::place_writes`], [`Terminator::place_writes`], [`Terminator::call_args`]),
//! which is exhaustive over every statement, rvalue and terminator variant.
//!
//! Three rules decide what a `Deref` in a written place means:
//! * BOX PROVENANCE. After `ElaborateBoxDerefs`, a write into a `Box`'s pointee reaches
//!   the model as `_t = Cast(Copy(<box>.0.0), *const T)` (or `Use`) followed by
//!   `(*_t).f = ..`. A single-valued local defined that way from an authenticated sysroot
//!   `Box` continues the box place's own field hits, as `Via::Owned` (the census's
//!   `box_deref_temps`). Without this, a write into storage `S` owns through a `Box`
//!   would lose every `S` hit.
//! * Any other `Deref` of a reference CUTS the hits (`Via::ThroughRef`) and of a raw
//!   pointer cuts them and records the pointee (`Via::ThroughRaw`); a `Deref` of a base
//!   whose type does not resolve is `Unresolved`.
//! * FAKE METADATA. A local defined once by `&raw const p` whose only use is
//!   `PtrMetadata(_)` is the extractor's spelling of rustc's
//!   `RawPtrKind::FakeForPtrMetadata` (it erases the kind), and is not a write (the
//!   census's `metadata_temps`). Every other `&raw const` is a `RawBorrow`.

use std::borrow::Cow;

use trust_types::{
    Operand, Place, PlaceWriteChannel, PlaceWrites, Projection, Rvalue, Statement, Terminator, Ty,
    TypeInvariantSite, UnOp, VerifiableBody, VerifiableFunction, fx::FxHashSet,
};

/// How a written field is reached from the written place's root.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Via {
    /// Through owned storage only (fields, a `Box` the place owns).
    Owned,
    /// The field sits behind a reference the written place dereferences.
    ThroughRef,
    /// The field sits behind a raw pointer; `pointee` is that pointer's pointee type.
    ThroughRaw { pointee: Ty },
}

/// One `(ADT, field)` a place passes through.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FieldHit {
    pub adt: String,
    pub field: usize,
    /// The place the field hangs off (the written place's prefix before the field
    /// projection; for a Box-temp write, the owning place's prefix).
    pub owner: Place,
    /// An `Index`, `ConstantIndex` or `Subslice` follows the field: only element storage
    /// is written, never the field's own length or pointer.
    pub element_only: bool,
}

/// One classified write or call argument.
#[derive(Debug, Clone, PartialEq)]
pub enum WriteFinding {
    /// A write that passes through field `field` of `adt`.
    Field {
        adt: String,
        field: usize,
        /// The place `field` hangs off: TINV's root identity (step 7).
        owner: Place,
        channel: PlaceWriteChannel,
        site: TypeInvariantSite,
        element_only: bool,
        via: Via,
    },
    /// The written place's own type is the ADT: the whole value is replaced.
    WholeValue { adt: String, owner: Place, channel: PlaceWriteChannel, site: TypeInvariantSite },
    /// The place's type could not be followed to its end; `prefix_hits` are the fields
    /// it was known to pass through before that.
    Unresolved {
        root_local: usize,
        channel: PlaceWriteChannel,
        site: TypeInvariantSite,
        prefix_hits: Vec<FieldHit>,
    },
    /// Memory no place names is written (an intrinsic, a pointer copy, an opaque
    /// terminator).
    Unlocatable { site: TypeInvariantSite, kind: &'static str },
    /// A place named by an operand of an `Rvalue::Unsupported`: the extractor could not
    /// say whether the rvalue aliases it.
    UnsupportedOperand { place: Place, site: TypeInvariantSite, prefix_hits: Vec<FieldHit> },
    /// A call argument; whether its type reaches a given ADT is asked per candidate
    /// ([`type_reaches`]).
    CallArg { arg_idx: usize, site: TypeInvariantSite, ty: Ty },
}

/// What [`resolve_place`] learned about one place.
#[derive(Debug, Clone, PartialEq)]
struct Resolution<'a> {
    hits: Vec<FieldHit>,
    via: Via,
    /// The place's own type, when every step resolved.
    ty: Option<Cow<'a, Ty>>,
}

const BOX_DEPTH: usize = 4;

/// Whether `ty` is the authenticated sysroot `Box` (the same check the sep engine makes).
fn is_sysroot_box(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Adt { name, adt_kind: Some(trust_types::AdtKind::Struct), .. }
            if trust_types::path_root_is_authenticated_sysroot_crate(name)
                && name.ends_with("::boxed::Box")
    )
}

/// The box place a single-valued raw-pointer local was taken from:
/// `_t = Cast(Copy|Move(<box>.0.0), RawPtr)` or `_t = Use(Copy|Move(<box>.0.0))`.
/// Trust (1.101): the cast operand is `<box>.0` typed `alloc::boxed::BoxRaw`
/// (the dedicated BoxDerefTransmute extracts the pointer), so that one-field
/// spelling over a `Box` base is the same temp source.
pub(crate) fn box_temp_source(func: &VerifiableFunction, local: usize) -> Option<&Place> {
    // PERF-COMPILER-VCGEN-587: parameters never have `unique_value_def == Some(..)`.
    if crate::local_defs::is_parameter(func, local)
        || !matches!(crate::local_ty_ref(func, local), Some(Ty::RawPtr { .. }))
    {
        return None;
    }
    let src = match crate::local_defs::unique_value_def(func, local)? {
        Rvalue::Cast(Operand::Copy(p) | Operand::Move(p), _)
        | Rvalue::Use(Operand::Copy(p) | Operand::Move(p)) => p,
        _ => return None,
    };
    let fields = match src.projections.as_slice() {
        [.., Projection::Field(0), Projection::Field(0)] => 2,
        [.., Projection::Field(0)]
            if matches!(
                crate::place_ty_cow(func, src).as_deref(),
                Some(Ty::Adt { name, .. }) if name == "alloc::boxed::BoxRaw"
            ) =>
        {
            1
        }
        _ => return None,
    };
    let base_ty =
        crate::place_prefix_ty_cow(func, src.local, &src.projections[..src.projections.len() - fields])?;
    is_sysroot_box(&base_ty).then_some(src)
}

fn adt_name(ty: &Ty) -> Option<&str> {
    match ty {
        Ty::Adt { name, .. } | Ty::Datatype { name, .. } => Some(name),
        _ => None,
    }
}

/// Walk `place`'s projections with [`crate::place_ty_step`], collecting the ADT fields
/// it passes through and how.
fn resolve_place<'a>(func: &'a VerifiableFunction, place: &Place, depth: usize) -> Resolution<'a> {
    let defs = &func.body.datatype_defs;
    let mut hits: Vec<FieldHit> = Vec::new();
    let mut via = Via::Owned;
    let Some(root) = crate::local_ty_ref(func, place.local) else {
        return Resolution { hits, via, ty: None };
    };
    let mut ty: Cow<'a, Ty> = Cow::Borrowed(root);
    let mut pending_variant = None;
    for (i, proj) in place.projections.iter().enumerate() {
        if let Some(resolved) = trust_types::datatype_marker_definition(defs, &ty) {
            ty = Cow::Borrowed(resolved);
        }
        match proj {
            Projection::Field(field) => {
                if let Some(name) = adt_name(&ty) {
                    hits.push(FieldHit {
                        adt: name.to_owned(),
                        field: *field,
                        owner: Place {
                            local: place.local,
                            projections: place.projections[..i].to_vec(),
                        },
                        element_only: false,
                    });
                }
            }
            Projection::Index(_)
            | Projection::ConstantIndex { .. }
            | Projection::Subslice { .. } => {
                for hit in &mut hits {
                    hit.element_only = true;
                }
            }
            Projection::Deref => {
                let source = (i == 0 && depth < BOX_DEPTH)
                    .then(|| box_temp_source(func, place.local))
                    .flatten();
                if let Some(src) = source {
                    let owner = resolve_place(func, src, depth + 1);
                    hits = owner.hits;
                    via = owner.via;
                } else {
                    match ty.as_ref() {
                        Ty::Ref { .. } => {
                            hits.clear();
                            via = Via::ThroughRef;
                        }
                        Ty::RawPtr { pointee, .. } => {
                            hits.clear();
                            via = Via::ThroughRaw { pointee: pointee.as_ref().clone() };
                        }
                        // A `Box` the place owns: its pointee is owned storage.
                        other if is_sysroot_box(other) => {}
                        _ => return Resolution { hits, via, ty: None },
                    }
                }
            }
            _ => {}
        }
        match crate::place_ty_step(defs, ty, proj, &mut pending_variant) {
            Some(next) => ty = next,
            None => return Resolution { hits, via, ty: None },
        }
    }
    Resolution { hits, via, ty: Some(ty) }
}

/// Every place an operand list mentions (a whole local or a local used as an index).
fn mentions(operand: &Operand, local: usize) -> usize {
    match operand {
        Operand::Copy(p) | Operand::Move(p) => place_mentions(p, local),
        _ => 0,
    }
}

fn place_mentions(place: &Place, local: usize) -> usize {
    usize::from(place.local == local)
        + place
            .projections
            .iter()
            .filter(|p| matches!(p, Projection::Index(l) if *l == local))
            .count()
}

/// How many times `local` is mentioned anywhere in the body, counting every statement
/// and terminator kind this function cannot list operands for as a mention (so an
/// unknown use never exempts a local).
#[cfg(test)]
pub(crate) fn mention_count(func: &VerifiableFunction, local: usize) -> usize {
    body_mention_count(&func.body, local)
}

/// Whether `local` is mentioned exactly `expected` times in `func.body`, short-circuiting
/// as soon as the running count exceeds `expected`.
pub(crate) fn has_mention_count(
    func: &VerifiableFunction,
    local: usize,
    expected: usize,
) -> bool {
    let mut n = 0usize;
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            n += stmt_mentions_count(stmt, local);
            if n > expected {
                return false;
            }
        }
        n += terminator_mentions_count(&block.terminator, local);
        if n > expected {
            return false;
        }
    }
    n == expected
}

/// [`mention_count`] over a bare body.
#[cfg(test)]
fn body_mention_count(body: &VerifiableBody, local: usize) -> usize {
    let mut n = 0;
    for block in &body.blocks {
        for stmt in &block.stmts {
            n += stmt_mentions_count(stmt, local);
        }
        n += terminator_mentions_count(&block.terminator, local);
    }
    n
}

fn stmt_mentions_count(stmt: &Statement, local: usize) -> usize {
    match stmt {
        Statement::Assign { place, rvalue, .. } => {
            place_mentions(place, local)
                + match rvalue {
                    Rvalue::Use(a)
                    | Rvalue::UnaryOp(_, a)
                    | Rvalue::Cast(a, _)
                    | Rvalue::Repeat(a, _) => mentions(a, local),
                    Rvalue::BinaryOp(_, a, b)
                    | Rvalue::CheckedBinaryOp(_, a, b)
                    | Rvalue::UncheckedBinaryOp(_, a, b) => mentions(a, local) + mentions(b, local),
                    Rvalue::PtrOffset { ptr, count } => {
                        mentions(ptr, local) + mentions(count, local)
                    }
                    Rvalue::Aggregate(_, ops) | Rvalue::Unsupported { operands: ops, .. } => {
                        ops.iter().map(|o| mentions(o, local)).sum()
                    }
                    Rvalue::Ref { place, .. }
                    | Rvalue::AddressOf(_, place)
                    | Rvalue::Discriminant(place)
                    | Rvalue::Len(place)
                    | Rvalue::CopyForDeref(place) => place_mentions(place, local),
                    _ => 1,
                }
        }
        Statement::StorageLive(_)
        | Statement::StorageDead(_)
        | Statement::Coverage
        | Statement::ConstEvalCounter
        | Statement::Nop => 0,
        Statement::SetDiscriminant { place, .. }
        | Statement::Deinit { place }
        | Statement::Retag { place }
        | Statement::PlaceMention(place) => place_mentions(place, local),
        _ => 1,
    }
}

fn terminator_mentions_count(terminator: &Terminator, local: usize) -> usize {
    match terminator {
        Terminator::Goto(_)
        | Terminator::Return
        | Terminator::Unreachable
        | Terminator::Resume => 0,
        Terminator::SwitchInt { discr, .. } => mentions(discr, local),
        Terminator::Call { args, dest, .. } => {
            args.iter().map(|a| mentions(a, local)).sum::<usize>() + place_mentions(dest, local)
        }
        Terminator::TailCall { args, .. } => args.iter().map(|a| mentions(a, local)).sum(),
        Terminator::Assert { cond, .. } => mentions(cond, local),
        Terminator::Drop { place, .. } => place_mentions(place, local),
        _ => 1,
    }
}

/// Whether the `&raw const` in `stmt` is the extractor's spelling of a fake borrow for
/// pointer metadata: its destination is a single-valued whole local whose only mention
/// besides its definition is one `PtrMetadata(_)`.
fn is_fake_metadata_borrow(func: &VerifiableFunction, stmt: &Statement) -> bool {
    body_is_fake_metadata_borrow(&func.body, stmt)
}

/// [`is_fake_metadata_borrow`] over a bare body.
fn body_is_fake_metadata_borrow(body: &VerifiableBody, stmt: &Statement) -> bool {
    let Statement::Assign { place: dest, rvalue: Rvalue::AddressOf(false, _), .. } = stmt else {
        return false;
    };
    // PERF-COMPILER-VCGEN-703: a parameter is never a compiler-synthesized fake metadata
    // temporary (`RawPtrKind::FakeForPtrMetadata`), so reject parameters in O(1) before
    // querying `body_has_one_explicit_def` and walking the body.
    if !dest.projections.is_empty()
        || crate::local_defs::body_is_parameter(body, dest.local)
        || !crate::local_defs::body_has_one_explicit_def(body, dest.local)
    {
        return false;
    }
    let t = dest.local;
    // The definition itself is one mention; the PtrMetadata read is the other.
    let mut has_metadata_read = false;
    let mut n = 0usize;
    for block in &body.blocks {
        for s in &block.stmts {
            if matches!(
                s,
                Statement::Assign {
                    rvalue: Rvalue::UnaryOp(UnOp::PtrMetadata, Operand::Copy(p) | Operand::Move(p)),
                    ..
                } if p.local == t && p.projections.is_empty()
            ) {
                if has_metadata_read {
                    return false;
                }
                has_metadata_read = true;
            }
            n += stmt_mentions_count(s, t);
            if n > 2 {
                return false;
            }
        }
        n += terminator_mentions_count(&block.terminator, t);
        if n > 2 {
            return false;
        }
    }
    has_metadata_read && n == 2
}

/// Trust (INT-RAWCONST-HAVOC-1, 2026-10-06): the place `stmt` lends out through a borrow
/// that can WRITE it, if `wanted` accepts that place. The borrows are `&mut p`,
/// `&raw mut p` and `&raw const p`.
///
/// `&raw const` counts. A `*const` is a valid `*const -> *mut` cast root, and under Tree
/// Borrows a write through it to a `mut` local is defined (DECISION_QUEUE UF-1(c); TCB
/// "call-pinned result"). The write needs no `unsafe` at the write site:
/// `AtomicU8::from_ptr(p as *mut u8).store(k, ..)` is a safe call, and so is an
/// edition-2024 `safe fn memset`. Before this predicate, the general havoc list and its
/// siblings counted `&mut` and `&raw mut` only, so `let mut x = 5; let p = &raw const x;`
/// followed by such a write kept the fact `x == 5`. The `x + 1` overflow row was then
/// kernel-certified and its check elided, and the advisory binary printed `0` where the
/// verify-off binary panics.
///
/// A shared `&p` does not count. A write through it is undefined behaviour for a
/// `Freeze` place, and `invalid_reference_casting` rejects the `&T -> *mut T` cast.
///
/// Two `&raw const` borrows are left out, both because they grant no more than a shared
/// borrow:
///
/// * A `&raw const` of a place reached THROUGH a shared reference (`&raw const (*r)`,
///   `&raw const (*r).f`, with `r: &T`): the pointer carries exactly the permissions of
///   the shared reborrow `&(*r)`, which does not count. It cannot change `r` itself, and
///   a write through it to the referent's non-`UnsafeCell` bytes is undefined behaviour
///   under Stacked and Tree Borrows — the premise the TCB "call-pinned result" row
///   already states for a pointer derived from a shared borrow. `slice::as_ptr`,
///   `Iter::new` and `into_iter` take exactly this `&raw const (*s)` of a `&[T]`
///   parameter; counting it reassigned `s` in trust-clean's parameter gate and broke
///   the pointer-provenance lanes built on it.
/// * The extractor's spelling of rustc's `RawPtrKind::FakeForPtrMetadata` borrow
///   ([`is_fake_metadata_borrow`]): its pointer has one definition and one other
///   mention, a `PtrMetadata` read, so it cannot reach a write. rustc emits one for
///   every `.len()` and bounds check of a slice place that is not a bare `Copy`
///   reference (a `&mut [T]`, or a slice field such as `self.buf`).
///
/// A `&raw const` of the local's own storage, or of a place reached through a `&mut`,
/// a raw pointer or a `Box`, counts.
///
/// `wanted` runs first, so the fake-metadata scan (two whole-body walks) runs only for a
/// borrow the caller is asking about.
pub fn write_capable_borrow<'s>(
    body: &VerifiableBody,
    stmt: &'s Statement,
    wanted: impl FnOnce(&Place) -> bool,
) -> Option<&'s Place> {
    let Statement::Assign { rvalue, .. } = stmt else { return None };
    let (Rvalue::Ref { mutable: true, place } | Rvalue::AddressOf(_, place)) = rvalue else {
        return None;
    };
    if !wanted(place) {
        return None;
    }
    if matches!(rvalue, Rvalue::AddressOf(false, _))
        && (reached_through_shared_reference(body, place)
            || body_is_fake_metadata_borrow(body, stmt))
    {
        return None;
    }
    Some(place)
}

/// Whether `place` is reached through a SHARED reference: its first projection is a
/// `Deref` of a local whose declared type is `&T`. A local whose declaration cannot be
/// found at its own index answers `false` (the borrow then counts).
fn reached_through_shared_reference(body: &VerifiableBody, place: &Place) -> bool {
    matches!(place.projections.first(), Some(Projection::Deref))
        && body.locals.get(place.local).is_some_and(|decl| {
            decl.index == place.local && matches!(decl.ty, Ty::Ref { mutable: false, .. })
        })
}

fn site(block: usize, statement_index: usize) -> TypeInvariantSite {
    TypeInvariantSite { block, statement_index }
}

fn push_place(
    out: &mut Vec<WriteFinding>,
    func: &VerifiableFunction,
    place: &Place,
    channel: PlaceWriteChannel,
    at: TypeInvariantSite,
) {
    let resolved = resolve_place(func, place, 0);
    let Some(ty) = resolved.ty else {
        out.push(WriteFinding::Unresolved {
            root_local: place.local,
            channel,
            site: at,
            prefix_hits: resolved.hits,
        });
        return;
    };
    let mut push_field = |hit: FieldHit, via| {
        out.push(WriteFinding::Field {
            adt: hit.adt,
            field: hit.field,
            owner: hit.owner,
            channel,
            site: at,
            element_only: hit.element_only,
            via,
        });
    };
    let mut hits = resolved.hits;
    if let Some(last) = hits.pop() {
        for hit in hits {
            push_field(hit, resolved.via.clone());
        }
        push_field(last, resolved.via);
    }
    if let Some(name) = adt_name(&ty) {
        out.push(WriteFinding::WholeValue {
            adt: name.to_owned(),
            owner: place.clone(),
            channel,
            site: at,
        });
    }
}

/// Every write in `func` (with its tail calls expanded, as the backing lane reads it).
#[must_use]
pub fn classify_writes(func: &VerifiableFunction) -> Vec<WriteFinding> {
    let expanded = func.with_tail_calls_expanded();
    classify_writes_expanded(expanded.as_ref())
}

pub(crate) fn classify_writes_expanded(func: &VerifiableFunction) -> Vec<WriteFinding> {
    let mut out = Vec::new();
    for block in &func.body.blocks {
        let b = block.id.0;
        for (k, stmt) in block.stmts.iter().enumerate() {
            match stmt.place_writes() {
                PlaceWrites::None => {}
                PlaceWrites::Unlocatable => {
                    out.push(WriteFinding::Unlocatable { site: site(b, k), kind: "statement" });
                }
                PlaceWrites::Places(writes) => {
                    for (place, channel) in writes {
                        if matches!(channel, PlaceWriteChannel::RawBorrow { mutable: false })
                            && is_fake_metadata_borrow(func, stmt)
                        {
                            continue;
                        }
                        push_place(&mut out, func, place, channel, site(b, k));
                    }
                }
            }
            for place in stmt.unsupported_rvalue_operands() {
                out.push(WriteFinding::UnsupportedOperand {
                    place: place.clone(),
                    site: site(b, k),
                    prefix_hits: resolve_place(func, place, 0).hits,
                });
            }
        }
        let at = site(b, block.stmts.len());
        let term = &block.terminator;
        match term.place_writes() {
            PlaceWrites::None => {}
            PlaceWrites::Unlocatable => {
                // An `UnwindTerminate` abort is an Opaque with no write (convert.rs).
                let abort = matches!(term, Terminator::Opaque { kind, .. }
                    if kind.starts_with("UnwindTerminate"));
                if !abort {
                    out.push(WriteFinding::Unlocatable { site: at, kind: "terminator" });
                }
            }
            PlaceWrites::Places(writes) => {
                for (place, channel) in writes {
                    push_place(&mut out, func, place, channel, at);
                }
            }
        }
        for (arg_idx, arg) in term.call_args().unwrap_or_default().iter().enumerate() {
            let (Operand::Copy(p) | Operand::Move(p)) = arg else { continue };
            match crate::place_ty_cow(func, p) {
                Some(ty) => {
                    out.push(WriteFinding::CallArg { arg_idx, site: at, ty: ty.into_owned() })
                }
                None => out.push(WriteFinding::Unresolved {
                    root_local: p.local,
                    channel: PlaceWriteChannel::CallDest,
                    site: at,
                    prefix_hits: Vec::new(),
                }),
            }
        }
    }
    out
}

/// Whether a value of type `ty` can reach a value of the ADT `name`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Reach {
    No,
    Yes,
    Unknown,
}

/// Decision TINV-33: crate-level evidence, per candidate, that a type the extraction
/// cannot see through reaches no value of it. Both default to `false` (no evidence: the
/// walk answers `Unknown` there, as before).
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct OpaqueReach {
    /// No `dyn` of the crate can hide the candidate: it is crate-private, never unsized
    /// into a `dyn` by any scanned body, never handed to code the census does not scan,
    /// and no opaque type of the crate hides it.
    pub dyn_cannot_reach: bool,
    /// Additionally, no local generic item is ever instantiated with a type reaching it,
    /// so a type parameter (`TyKind::Param`) of a polymorphic body cannot be one.
    pub param_cannot_reach: bool,
}

/// [`type_reaches`] under the TINV-33 evidence `opaque`: a trait object answers `No` when
/// `opaque.dyn_cannot_reach`, a bare type parameter when `opaque.param_cannot_reach`.
/// Every other opaque shape (a coroutine, an alias, any other unsupported type, an
/// undefined marker, running out of fuel) stays `Unknown`.
#[must_use]
pub fn type_reaches_with(
    ty: &Ty,
    name: &str,
    defs: &trust_types::DatatypeDefs,
    opaque: OpaqueReach,
) -> Reach {
    type_reaches_impl(ty, name, defs, opaque)
}

/// Bounded walk: does `ty` contain, own, or point at a value of the ADT `name`?
/// A coroutine (its upvars omit the saved locals), a trait object, an unsupported type,
/// an undefined datatype marker, or running out of fuel answers `Unknown`.
///
/// Recursive datatypes: the walk is a least fixpoint over bare datatype markers. Each
/// marker name is expanded at most once per call; a second visit answers `No`. That is
/// sound because a marker resolves through the explicit `defs` table by its full,
/// identity-bearing name (`Big<u8>` and `Big<i32>` are different keys), so a re-expansion
/// would walk the very same subtree, and the walk only searches for a path: `Yes`
/// returns at once and `Unknown` from the first expansion already propagates to the
/// root, so the back edge's `No` can never hide either. A marker missing from `defs`
/// stays `Unknown`. Before this, a self-recursive type (`enum Json { Arr(Vec<Json>) }`)
/// burnt the fuel and answered `Unknown` for every candidate.
#[must_use]
pub fn type_reaches(ty: &Ty, name: &str, defs: &trust_types::DatatypeDefs) -> Reach {
    type_reaches_impl(ty, name, defs, OpaqueReach::default())
}

fn type_reaches_impl(
    ty: &Ty,
    name: &str,
    defs: &trust_types::DatatypeDefs,
    opaque: OpaqueReach,
) -> Reach {
    fn walk<'d>(
        ty: &'d Ty,
        name: &str,
        defs: &'d trust_types::DatatypeDefs,
        opaque: OpaqueReach,
        fuel: &mut u32,
        seen: &mut FxHashSet<&'d str>,
    ) -> Reach {
        if *fuel == 0 {
            return Reach::Unknown;
        }
        *fuel -= 1;
        let mut all = |tys: &mut dyn Iterator<Item = &'d Ty>, fuel: &mut u32| {
            let mut out = Reach::No;
            for t in tys {
                match walk(t, name, defs, opaque, fuel, seen) {
                    Reach::Yes => return Reach::Yes,
                    Reach::Unknown => out = Reach::Unknown,
                    Reach::No => {}
                }
            }
            out
        };
        match ty {
            Ty::Adt { name: n, .. } if n == name => Reach::Yes,
            Ty::Datatype { name: n, .. } if n == name => Reach::Yes,
            Ty::Adt { fields, .. } => all(&mut fields.iter().map(|(_, t)| t), fuel),
            Ty::Datatype { variants, .. } if variants.is_empty() => {
                let Some(marker) = trust_types::bare_datatype_marker_name(ty) else {
                    return Reach::Unknown;
                };
                match trust_types::datatype_marker_definition(defs, ty) {
                    // A table entry is keyed by the full marker name, so the second
                    // expansion of `marker` would walk the same subtree the first did.
                    Some(def) => {
                        if !seen.insert(marker) {
                            return Reach::No;
                        }
                        walk(def, name, defs, opaque, fuel, seen)
                    }
                    None => Reach::Unknown,
                }
            }
            Ty::Datatype { variants, .. } => {
                all(&mut variants.iter().flat_map(|(_, fs)| fs.iter().map(|(_, t)| t)), fuel)
            }
            Ty::Tuple(tys) => all(&mut tys.iter(), fuel),
            Ty::Closure { upvars, .. } => all(&mut upvars.iter(), fuel),
            Ty::Ref { inner: elem, .. }
            | Ty::RawPtr { pointee: elem, .. }
            | Ty::Slice { elem, .. }
            | Ty::Seq { elem, .. }
            | Ty::Array { elem, .. }
            | Ty::SymArray { elem, .. } => walk(elem, name, defs, opaque, fuel, seen),
            Ty::Dynamic { .. } if opaque.dyn_cannot_reach => Reach::No,
            Ty::Unsupported { kind, .. } if opaque.param_cannot_reach && kind == PARAM_KIND => {
                Reach::No
            }
            Ty::Coroutine { .. } | Ty::Dynamic { .. } | Ty::Unsupported { .. } => Reach::Unknown,
            Ty::Bool
            | Ty::Int { .. }
            | Ty::PtrSizedInt { .. }
            | Ty::Char
            | Ty::Float { .. }
            | Ty::Str
            | Ty::Bv(_)
            | Ty::Unit
            | Ty::Never
            | Ty::FnDef { .. }
            | Ty::FnPtr { .. }
            | Ty::BignumNat => Reach::No,
            _ => Reach::Unknown,
        }
    }
    let mut fuel = 4096;
    let mut seen = FxHashSet::default();
    walk(ty, name, defs, opaque, &mut fuel, &mut seen)
}

/// The extractor's spelling of a bare type parameter (`ty_convert`'s `TyKind::Param` arm).
const PARAM_KIND: &str = "TyKind::Param";

/// Backing lane: whether `func` writes field `fields[i]` of the ADT `name` through any
/// channel the classifier places (owned or through a reference; element-only writes do
/// not count). `Unresolved`, `Unlocatable` and call arguments are the rustc census's to
/// deny, not this scan's.
#[must_use]
pub fn writes_fields_of(func: &VerifiableFunction, name: &str, fields: &[usize]) -> bool {
    if fields.is_empty() {
        return false;
    }
    let expanded = func.with_tail_calls_expanded();
    writes_fields_of_expanded(expanded.as_ref(), name, fields)
}

pub(crate) fn writes_fields_of_expanded(
    func: &VerifiableFunction,
    name: &str,
    fields: &[usize],
) -> bool {
    if fields.is_empty() {
        return false;
    }
    let can_hit_field = |place: &Place| -> bool {
        place
            .projections
            .iter()
            .any(|proj| matches!(proj, Projection::Field(f) if fields.contains(f)))
            || (matches!(place.projections.first(), Some(Projection::Deref))
                && matches!(crate::local_ty_ref(func, place.local), Some(Ty::RawPtr { .. })))
    };
    let place_writes_field = |place: &Place| -> bool {
        let resolved = resolve_place(func, place, 0);
        resolved.ty.is_some()
            && resolved
                .hits
                .iter()
                .any(|hit| !hit.element_only && hit.adt == name && fields.contains(&hit.field))
    };
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            if let PlaceWrites::Places(writes) = stmt.place_writes() {
                for (place, channel) in writes {
                    // PERF-COMPILER-VCGEN-702: check `can_hit_field(place)` before
                    // `is_fake_metadata_borrow(func, stmt)` so `&raw const` borrows whose
                    // target place cannot reach `fields` skip the two whole-body scans.
                    if place.projections.is_empty() || !can_hit_field(place) {
                        continue;
                    }
                    if matches!(channel, PlaceWriteChannel::RawBorrow { mutable: false })
                        && is_fake_metadata_borrow(func, stmt)
                    {
                        continue;
                    }
                    if place_writes_field(place) {
                        return true;
                    }
                }
            }
        }
        if let PlaceWrites::Places(writes) = block.terminator.place_writes() {
            for (place, _) in writes {
                if can_hit_field(place) && place_writes_field(place) {
                    return true;
                }
            }
        }
    }
    false
}

/// TINV: why a candidate type `name` must be refused on `func`'s writes, if it must
/// (design §6 step 4; recorded beside TINV-8 in docs/DECISION_QUEUE.md).
#[must_use]
pub fn tinv_refusal(
    func: &VerifiableFunction,
    findings: &[WriteFinding],
    name: &str,
) -> Option<String> {
    tinv_refusal_with(func, findings, name, OpaqueReach::default())
}

/// [`tinv_refusal`] under the TINV-33 evidence `opaque` ([`type_reaches_with`]).
#[must_use]
pub fn tinv_refusal_with(
    func: &VerifiableFunction,
    findings: &[WriteFinding],
    name: &str,
    opaque: OpaqueReach,
) -> Option<String> {
    let defs = &func.body.datatype_defs;
    let reaches = |ty: &Ty| type_reaches_with(ty, name, defs, opaque);
    for finding in findings {
        let why = match finding {
            WriteFinding::Unlocatable { site, kind } => {
                Some(format!("an unlocatable {kind} write at {site}"))
            }
            WriteFinding::Unresolved { root_local, site, prefix_hits, .. } => {
                let root = crate::local_ty_ref(func, *root_local);
                let hit = prefix_hits.iter().any(|h| h.adt == name);
                (hit || root.is_none_or(|t| reaches(t) != Reach::No))
                    .then(|| format!("an unresolved write at {site}"))
            }
            WriteFinding::UnsupportedOperand { place, site, prefix_hits } => {
                let ty = crate::place_ty_cow(func, place);
                let hit = prefix_hits.iter().any(|h| h.adt == name);
                (hit || ty.is_none_or(|t| reaches(&t) != Reach::No))
                    .then(|| format!("an unsupported rvalue may alias it at {site}"))
            }
            WriteFinding::Field { via: Via::ThroughRaw { pointee }, site, .. } => {
                (reaches(pointee) != Reach::No)
                    .then(|| format!("a write through a raw pointer at {site}"))
            }
            WriteFinding::CallArg { ty, site, .. } => (reaches(ty) == Reach::Unknown).then(|| {
                format!("a call argument of unknown reach at {site} in `{}`", func.def_path)
            }),
            WriteFinding::Field { .. } | WriteFinding::WholeValue { .. } => None,
        };
        if why.is_some() {
            return why;
        }
    }
    None
}

#[cfg(test)]
#[path = "place_write_tests.rs"]
mod tests;
