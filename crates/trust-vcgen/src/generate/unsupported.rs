// Fail-closed detection of MIR outside the modeled fragment. Anything not
// recognised here must surface as an `UnsupportedMir` row rather than be
// silently skipped, so these collectors are the boundary between "proved" and
// "not modeled" for types, statements and terminators.

use super::*;

pub(crate) fn unsupported_mir_vcs(func: &VerifiableFunction) -> Vec<VerificationCondition> {
    let mut vcs = Vec::new();

    collect_body_type_unsupported(func, &mut vcs);

    for block in &func.body.blocks {
        for (stmt_index, stmt) in block.stmts.iter().enumerate() {
            collect_statement_unsupported(func, block.id, stmt_index, stmt, &mut vcs);
        }
        collect_terminator_unsupported(func, block.id, &block.terminator, &mut vcs);
    }

    dedup_unsupported_by_display_key(vcs)
}

/// verifier-perf: collapse the unsupported-VC stream to display-key
/// granularity at generation time. Every VC produced by `unsupported_mir_vcs`
/// is `UnsupportedMir`, which the compiler preclassifies to `Unknown` and never
/// dispatches to a solver — so any dedup among these is sound: it can never drop
/// a provable or violating obligation. The retained key `(kind, location)` is
/// exactly the `(function, kind, file, line/col)` display key the compiler's
/// `coalesce_display_obligation_results` keeps (the function is constant across
/// one function's VCs), so the visible report is unchanged while the raw
/// obligation count stops exploding. One walk of a recursive `syn`-shaped type
/// emits thousands of identical-`kind` leaves at a single span that otherwise
/// flow downstream as distinct raw obligations and feed the result-assembly
/// pass; here they coalesce to one entry per distinct display key.
///
/// The collapse must not lose WHY a collapsed row stopped (determinism plan
/// §3.7): a marker left by a per-function budget trip carries a stop token in
/// its detail (`[stop:steps]`, or `[stop:wall-backstop]` when the clock tripped),
/// and the rows sharing its display key may carry none. The kept row therefore
/// takes the least reproducible cause any collapsed row stated
/// ([`trust_types::determinism::StopCause::combine`]); otherwise a clock-degraded
/// marker could be dropped behind a sibling that reads as a deterministic
/// `unsupported`. Between deterministic causes the kept row's text stands.
#[derive(Clone, Debug)]
enum KeptDisplaySlot {
    One(usize),
    Many(Vec<usize>),
}

impl KeptDisplaySlot {
    #[inline]
    fn find(
        &self,
        out: &[VerificationCondition],
        kind: &str,
        location: &SourceSpan,
    ) -> Option<usize> {
        let matches_at = |idx: usize| {
            out.get(idx).is_some_and(|kept| {
                kept.location == *location
                    && matches!(
                        &kept.kind,
                        VcKind::UnsupportedMir { kind: kept_kind, .. } if kept_kind == kind
                    )
            })
        };
        match self {
            Self::One(idx) => matches_at(*idx).then_some(*idx),
            Self::Many(indices) => indices.iter().copied().find(|&idx| matches_at(idx)),
        }
    }

    #[inline]
    fn push(&mut self, idx: usize) {
        match self {
            Self::One(first) => *self = Self::Many(vec![*first, idx]),
            Self::Many(indices) => indices.push(idx),
        }
    }
}

pub(super) fn dedup_unsupported_by_display_key(
    vcs: Vec<VerificationCondition>,
) -> Vec<VerificationCondition> {
    if vcs.len() <= 1 {
        return vcs;
    }
    use std::hash::{Hash, Hasher};
    use trust_types::determinism::StopCause;
    use trust_types::fx::FxHasher;
    // Hash `(kind, &vc.location)` in-place and verify exact equality against
    // `out[idx]` so neither unique nor duplicate rows clone `kind: String` or
    // `vc.location.file: String`.
    let mut kept_at: FxHashMap<u64, KeptDisplaySlot> = FxHashMap::default();
    let mut out: Vec<VerificationCondition> = Vec::with_capacity(vcs.len());
    for vc in vcs {
        match &vc.kind {
            VcKind::UnsupportedMir { kind, detail } => {
                let mut hasher = FxHasher::default();
                kind.hash(&mut hasher);
                vc.location.hash(&mut hasher);
                let hash = hasher.finish();
                let found = match kept_at.entry(hash) {
                    std::collections::hash_map::Entry::Vacant(vacant) => {
                        vacant.insert(KeptDisplaySlot::One(out.len()));
                        None
                    }
                    std::collections::hash_map::Entry::Occupied(mut occupied) => {
                        if let Some(index) = occupied.get().find(&out, kind, &vc.location) {
                            Some(index)
                        } else {
                            occupied.get_mut().push(out.len());
                            None
                        }
                    }
                };
                let Some(index) = found else {
                    out.push(vc);
                    continue;
                };
                let Some(dropped) = StopCause::from_reason(detail) else { continue };
                if let Some(kept_vc) = out.get_mut(index)
                    && let VcKind::UnsupportedMir { detail: kept_detail, .. } = &mut kept_vc.kind
                {
                    // A row with no token reads as `unsupported` (deterministic).
                    let kept_rank = StopCause::from_reason(kept_detail)
                        .map_or(0, |cause| cause.reproducibility().rank());
                    if dropped.reproducibility().rank() > kept_rank {
                        *kept_detail = dropped.stamp(kept_detail);
                    }
                }
            }
            // Defensive: anything that is not an UnsupportedMir obligation is
            // kept verbatim and never deduped, so this pass can only ever remove
            // redundant Unknown obligations.
            _ => out.push(vc),
        }
    }
    out
}

pub(super) fn collect_body_type_unsupported(
    func: &VerifiableFunction,
    vcs: &mut Vec<VerificationCondition>,
) {
    // verifier-perf: dedup the per-type "unsupported" walk by structural
    // type. A single function's MIR often threads one large (or recursive) type
    // — e.g. a `syn::Item` — through hundreds of temporaries; without this guard
    // `collect_type_unsupported` re-walks and re-emits the identical obligation
    // set once per local, exploding the obligation count (observed: 1.9M
    // obligations from one function whose distinct (kind, span) set is ~51).
    // Walk each distinct type once. Sound: identical types yield identical
    // (kind, span) obligations that already coalesce to a single display key, so
    // no distinct obligation is lost; provable obligations come from the
    // per-statement generators, not this type walk.
    let mut seen_types: FxHashSet<&Ty> = FxHashSet::default();
    // PERF-COMPILER-VCGEN-808: `collect_type_unsupported` emits nothing for a type
    // with no unsupported declaration (its own first test), so ask that cheap,
    // short-circuiting walk BEFORE structurally hashing the whole type into
    // `seen_types`. Hashing a large recursive ADT per local dominated this pass on
    // the measured fixture corpus; the emitted set is identical.
    if ty_has_unsupported_declaration(&func.body.return_ty)
        && seen_types.insert(&func.body.return_ty)
    {
        collect_type_unsupported(func, &"return type", &func.body.return_ty, &func.span, vcs);
    }
    for local in &func.body.locals {
        if ty_has_unsupported_declaration(&local.ty) && seen_types.insert(&local.ty) {
            collect_type_unsupported(
                func,
                &format_args!("local _{} type", local.index),
                &local.ty,
                &func.span,
                vcs,
            );
        }
    }
}

fn ty_has_unsupported_declaration(ty: &Ty) -> bool {
    match ty {
        Ty::Unsupported { kind, detail }
            if kind == "TyKind::Adt" && detail.starts_with("recursive") =>
        {
            false
        }
        Ty::Unsupported { kind, .. } if kind == "TyKind::Param" || kind == "TyKind::Array" => false,
        Ty::Unsupported { .. } if ty.is_pre_mono_alias_marker() => false,
        Ty::Unsupported { .. } => true,
        Ty::Ref { inner, .. }
        | Ty::RawPtr { pointee: inner, .. }
        | Ty::Slice { elem: inner }
        | Ty::Array { elem: inner, .. }
        | Ty::SymArray { elem: inner, .. } => ty_has_unsupported_declaration(inner),
        Ty::Tuple(fields) => fields.iter().any(ty_has_unsupported_declaration),
        Ty::Adt { fields, .. } => {
            fields.iter().any(|(_, field_ty)| ty_has_unsupported_declaration(field_ty))
        }
        Ty::Closure { upvars, .. } | Ty::Coroutine { upvars, .. } => {
            upvars.iter().any(ty_has_unsupported_declaration)
        }
        Ty::FnDef { sig, .. } | Ty::FnPtr { sig } => {
            sig.params.iter().any(ty_has_unsupported_declaration)
                || ty_has_unsupported_declaration(&sig.ret)
        }
        _ => false,
    }
}

pub(super) fn collect_type_unsupported(
    func: &VerifiableFunction,
    context: &dyn std::fmt::Display,
    ty: &Ty,
    span: &SourceSpan,
    vcs: &mut Vec<VerificationCondition>,
) {
    if !ty_has_unsupported_declaration(ty) {
        return;
    }
    match ty {
        // Precision: a *recursive* ADT/enum (e.g. `clean_kernel::Expr`, a tree,
        // a linked list) is a legitimate, inhabited Rust value type that merely
        // refers to itself; trust-mir-extract gives up *modeling* it as a single
        // SMT sort and lowers it to `Ty::Unsupported { kind: "TyKind::Adt",
        // detail: "recursive ..." }`. But a TYPE DECLARATION is not an operation:
        // a value of a recursive ADT carries NO safety obligation by itself, so a
        // pure constructor/builder like `trust-semantics::int_ty()` /
        // `noOverflow_app(min, result, max)` — whose params and return are the
        // recursive `Expr` term and whose body only constructs/returns — must
        // verify cleanly (0 obligations / Proved), not fail closed to Unknown on
        // the declaration walk.
        //
        // Soundness: this skips ONLY the recursive-ADT *declaration* signal. It
        // can never hide unsafe behavior:
        //   - We do NOT give the recursive ADT a modeled SMT sort. Any panic-able
        //     USE of such a value still fails closed independently at its use
        //     site — `place_sort` stays `None`, so `collect_place_type_unsupported`
        //     / `collect_aggregate_field_sort_unsupported` still stamp a marker
        //     when the value is an assignment destination/source or an aggregate
        //     field, and `Operand::Unsupported` / opaque terminators still stamp.
        //   - Arithmetic/bounds/divide/deref VCs are emitted only for operands of
        //     a *modeled* (integer / pointer) sort; a recursive ADT never matches
        //     those, so suppressing its declaration marker cannot manufacture a
        //     false overflow/bounds proof.
        // Every OTHER `Ty::Unsupported` kind (unnormalized `TyKind::Alias`, `dyn`
        // trait objects, higher-ranked fn pointers, coroutines, …) is genuinely
        // unsupported and STILL fails closed below — only the self-referential
        // value-type case is relaxed. Mirrors the `place_sort` recovery in
        // `collect_place_type_unsupported`, which likewise only stamps where a
        // well-formed VC is genuinely required and never turns an unmodelable
        // place into a false proof.
        Ty::Unsupported { kind, detail }
            if kind == "TyKind::Adt" && detail.starts_with("recursive") => {}
        // Precision (generics): a `TyKind::Param` is the polymorphic-MIR
        // appearance of a generic parameter `T` (trust-mir-extract lowers it to
        // `Ty::Unsupported { kind: "TyKind::Param", detail: "generic parameter …
        // needs monomorphization" }`). Exactly like the recursive-ADT case
        // above, a *value* of generic type `T` carries NO direct safety
        // obligation by itself: you cannot arithmetic/index/deref/shift an
        // opaque `T` in Rust without going through a trait method, which is its
        // own call obligation whose *modeled* result is checked independently.
        // So a `T`-typed *type declaration* (a forwarded/unused param or local —
        // e.g. the `_items: &[T]` of `fn g<T>(_items: &[T], x: u32) -> u32 { if
        // x >= 1 { x - 1 } else { 0 } }`) must NOT stamp an `UnsupportedMir`
        // marker. Stamping it loses the (sound, and *strong*) ability to prove a
        // generic function panic-free FOR ALL T w.r.t. its T-INDEPENDENT
        // obligations: that `x - 1` already PROVES on the modeled `u32`, yet the
        // spurious `&[T]` declaration marker alone would force the whole function
        // to Unknown.
        //
        // Soundness — identical to the recursive-ADT relaxation above; this
        // skips ONLY the `Param` *declaration* signal:
        //   - We do NOT give `T` a modeled SMT sort. Any panic-able USE of a `T`
        //     value still fails closed independently at its use site: `place_sort`
        //     stays `None` for a `Param`-typed place, so
        //     `collect_place_type_unsupported` still stamps when it is an
        //     assignment destination/source, and `Operand::Unsupported` / opaque
        //     terminators still stamp.
        //   - Arithmetic/bounds/divide/deref VCs are emitted only for operands of
        //     a *modeled* (integer / pointer) sort; an opaque `T` never matches,
        //     so suppressing its declaration marker cannot manufacture a false
        //     proof. A T-VALUE-dependent panic (`let x: u32 = t.into(); x - 1`)
        //     is either left fully un-analyzed (the generic trait call bails the
        //     body — trustc makes no claim) or checked on its modeled result —
        //     never falsely PROVED. The generics soundness oracle
        //     (`scripts/trustc_generics_soundness_oracle.py`) is the standing net
        //     for exactly this: `g_panic_sub<T>` must stay refuted and
        //     `g_panic_t_value` must never be proved.
        Ty::Unsupported { kind, .. } if kind == "TyKind::Param" => {}
        // Precision (arrays): a `TyKind::Array` lowers to `Ty::Unsupported` ONLY
        // when its length is not a concrete target `usize` — a generic-const /
        // unevaluated-const length `[T; N]` (trust-mir-extract/ty_convert.rs: a
        // concrete length folds to `Ty::Array { len }` instead). Like a Param or a
        // recursive ADT, a *value* of such an array type carries NO direct safety
        // obligation by its DECLARATION: the only panic-able array operation is an
        // index/slice, and that fails closed INDEPENDENTLY at its use site — the
        // verifier emits a `bounds` VC keyed on the symbolic length `N` and
        // discharges it (`arr[i]` REFUTES unguarded, PROVES under `if i < N`),
        // empirically confirmed by `scripts/trustc_array_bounds_soundness_oracle.py`.
        // So the array-TYPE declaration marker is spurious noise (it drags e.g. any
        // BTreeMap-handling function — whose node's `edges: [_; 2*B]` has an
        // unevaluated length — to Unknown even when every real obligation proves).
        //
        // Soundness — identical to the Param / recursive-ADT relaxations above;
        // this skips ONLY the `TyKind::Array` *declaration* signal:
        //   - We do NOT give the unmodeled array a modeled SMT sort. A safe index
        //     `arr[i]` still emits its `bounds` obligation (failed/proved, never
        //     dropped); an index whose destination/source has no recoverable sort
        //     still stamps a use-site marker via `collect_place_type_unsupported`
        //     (`project_ty_ref` returns `None` for `Index` on `Ty::Unsupported`);
        //     unsafe raw-pointer access into the array fails closed via the unsafe
        //     wall. Suppressing the declaration marker cannot manufacture a false
        //     proof — the bounds-soundness oracle (`idx_unmodeled_len` must stay
        //     REFUTED) is the standing net for exactly this.
        Ty::Unsupported { kind, .. } if kind == "TyKind::Array" => {}
        // Trust (R3, generics): a PARAM-BEARING projection alias (`<S as
        // Serializer>::Ok`, `<B as Flags>::Bits`) is the polymorphic-MIR
        // appearance of an associated type whose projection typeck itself could
        // not resolve. EXACTLY the `TyKind::Param` relaxation above: a
        // *declaration* of a value of such a type carries no safety obligation;
        // every panic-able USE fails closed independently (`place_sort` stays
        // `None`, `Operand::Unsupported` stamps, opaque terminators stamp, calls
        // hit the bridge's absent-callee arm, drops hit the drop-glue arm — and
        // both of those arms now force a COUNTED whole-function panic-freedom
        // carrier, so the may-panic rows are never silently dropped).
        // SCOPE (load-bearing): ONLY the pre-monomorphization detail
        // (`trust_types::PRE_MONO_ALIAS_DETAIL`, matched via
        // `is_pre_mono_alias_marker`). A MONOMORPHIC alias that merely failed
        // normalization ("did not resolve…", "nest ADTs too deep…", "no typing
        // env…") may have a concrete primitive runtime type on which MIR
        // performs primitive ops — relaxing those could hide a genuine
        // obligation, so they stay fail-closed in the catch-all stamp below.
        // Standing nets: `scripts/trustc_generics_soundness_oracle.py` (the
        // r3_* twins) and the `r3_generic_alias_*` falsification pairs.
        Ty::Unsupported { .. } if ty.is_pre_mono_alias_marker() => {}
        Ty::Unsupported { kind, detail } => vcs.push(unsupported_mir_vc(
            func,
            kind.clone(),
            format!("{context}: {detail}"),
            span.clone(),
        )),
        Ty::Ref { inner, .. } => {
            collect_type_unsupported(func, &format_args!("{context} pointee"), inner, span, vcs);
        }
        Ty::RawPtr { pointee, .. } => {
            collect_type_unsupported(
                func,
                &format_args!("{context} raw pointee"),
                pointee,
                span,
                vcs,
            );
        }
        Ty::Slice { elem } => {
            collect_type_unsupported(
                func,
                &format_args!("{context} slice element"),
                elem,
                span,
                vcs,
            );
        }
        Ty::Array { elem, .. } => {
            collect_type_unsupported(
                func,
                &format_args!("{context} array element"),
                elem,
                span,
                vcs,
            );
        }
        // Trust: piece #7a — a const-generic array's DECLARATION carries no direct
        // obligation (identical to the `TyKind::Array` relaxation above: the only
        // panic-able array op is an index/slice, which fails closed at its use
        // site via the `bounds` VC on the symbolic length). We DO descend into the
        // element type so a `[SomeUnsupportedElem; N]` still stamps the element's
        // marker. The SymArray itself stamps no spurious declaration marker.
        Ty::SymArray { elem, .. } => {
            collect_type_unsupported(
                func,
                &format_args!("{context} array element"),
                elem,
                span,
                vcs,
            );
        }
        Ty::Tuple(fields) => {
            for (index, field_ty) in fields.iter().enumerate() {
                collect_type_unsupported(
                    func,
                    &format_args!("{context} tuple field {index}"),
                    field_ty,
                    span,
                    vcs,
                );
            }
        }
        Ty::Adt { fields, .. } => {
            for (name, field_ty) in fields {
                collect_type_unsupported(
                    func,
                    &format_args!("{context} field {name}"),
                    field_ty,
                    span,
                    vcs,
                );
            }
        }
        Ty::Closure { upvars, .. } | Ty::Coroutine { upvars, .. } => {
            for (index, upvar_ty) in upvars.iter().enumerate() {
                collect_type_unsupported(
                    func,
                    &format_args!("{context} upvar {index}"),
                    upvar_ty,
                    span,
                    vcs,
                );
            }
        }
        Ty::FnDef { sig, .. } | Ty::FnPtr { sig } => {
            for (index, param_ty) in sig.params.iter().enumerate() {
                collect_type_unsupported(
                    func,
                    &format_args!("{context} param {index}"),
                    param_ty,
                    span,
                    vcs,
                );
            }
            collect_type_unsupported(
                func,
                &format_args!("{context} return"),
                &sig.ret,
                span,
                vcs,
            );
        }
        _ => {}
    }
}

pub(super) fn collect_place_type_unsupported(
    func: &VerifiableFunction,
    context: &dyn std::fmt::Display,
    span: &SourceSpan,
    place: &trust_types::Place,
    vcs: &mut Vec<VerificationCondition>,
) {
    // Use `place_sort` (a strict superset of `place_ty`: it first tries
    // `symbolic_assignment_sort_for_place`, then falls back to `place_ty.map(sort_for_ty)`)
    // so a deeply-projected destination whose `place_ty` is None but whose SMT sort IS
    // recoverable does not spuriously stamp an unsupported-MIR marker. Sound: when
    // `place_sort` is Some, the assignment's VC is built with a concrete sort, so this
    // only SUPPRESSES the marker where a well-formed VC is genuinely producible — it
    // never turns an unmodelable place into a (false) proof.
    // Trust: piece #13 — a coroutine FRAME access (the resume body's `self`
    // deref, a former across-await frame field) intentionally has NO SMT sort:
    // the frame is modeled opaquely so that a value read out of it is havoc'd
    // (unconstrained) — the sound over-approximation for "anything the executor
    // left across the suspend". Suppress the missing-sort stamp here; the
    // OPACITY is deliberate, not a modeling gap. This never manufactures a
    // proof: a havoc'd value discharges no bound (an index/arith over it stays
    // unproved), and the frame's discriminant/state selector feeds no
    // obligation. Only the frame's own place is spared — a well-typed local
    // that merely PROJECTS through the frame to a modeled sub-place still gets a
    // concrete sort from `place_sort` and is unaffected.
    if crate::place_sort(func, place).is_none() && !place_is_coroutine_frame(func, place) {
        vcs.push(unsupported_mir_vc(
            func,
            "TrustSymbolicAggregateFieldSortMissing".to_string(),
            format!(
                "{context}: place `{}` has missing aggregate/field sort metadata; schema-aware proof consumers require a concrete SMT sort declaration",
                crate::place_to_var_name(func, place)
            ),
            span.clone(),
        ));
    }

    for (index, projection) in place.projections.iter().enumerate() {
        match projection {
            trust_types::Projection::OpaqueCast(ty)
            | trust_types::Projection::UnwrapUnsafeBinder(ty) => collect_type_unsupported(
                func,
                &format_args!("{context} projection {index}"),
                ty,
                span,
                vcs,
            ),
            _ => {}
        }
    }
}

/// The violation formula EVERY `UnsupportedMir` row must carry, whether the row
/// is built fresh or an existing row is demoted into one.
///
/// A VC is a VIOLATION formula: discharge means UNSAT. `Bool(true)` is SAT, so a
/// consumer that reads `vc.formula` without first preclassifying by kind gets
/// "not discharged", which is the honest reading of "unsupported". `Bool(false)`
/// is UNSAT and those same consumers would read it as DISCHARGED — a proof
/// manufactured out of a row that means "I do not know".
///
/// `UnsupportedMir::proof_level()` is `L0Safety`, so any consumer that selects
/// obligations by proof level rather than by kind admits this row and then reads
/// only its formula. `trust_clean::whole_program::{certify_function_in_graph,
/// ensures_certified_modulo_3}` were exactly that, and they now refuse a
/// declined row by KIND before the formula is consulted — so this polarity is
/// the SECOND, independent defence there rather than the only one. It stays the
/// first and only defence for every direct-solver caller;
/// `crates/trust-vcgen/src/tests.rs` pins that path.
pub(crate) fn unsupported_mir_fail_closed_formula() -> Formula {
    Formula::Bool(true)
}

/// Rewrite `vc` in place into a fail-closed `UnsupportedMir` row.
///
/// Demotion is DROP-ONLY: the row's verdict can only become Unknown. The
/// formula is reset to [`unsupported_mir_fail_closed_formula`] so no consumer
/// can read the demoted row as discharged, and the safety-row payload
/// (`obligation`, `contract_metadata`) is cleared because it describes an
/// obligation this row no longer states.
pub(super) fn demote_to_unsupported_mir(
    vc: &mut VerificationCondition,
    kind: String,
    detail: String,
) {
    vc.kind = VcKind::UnsupportedMir { kind, detail };
    vc.formula = unsupported_mir_fail_closed_formula();
    vc.obligation = None;
    vc.contract_metadata = None;
}

/// Whether `vc` is an `UnsupportedMir` row carrying anything OTHER than the
/// fail-closed violation formula — i.e. a row a kind-blind consumer could read
/// as discharged. Used by the emitters' own post-conditions.
///
/// The required formula is written here as the LITERAL `Bool(true)` rather than
/// as a call to [`unsupported_mir_fail_closed_formula`], deliberately: a check
/// that reads the same definition it is checking moves with it, and would go
/// silently inert the moment that definition is changed. This is the independent
/// oracle, so it must state the value itself.
pub(super) fn is_unsupported_mir_with_wrong_formula(vc: &VerificationCondition) -> bool {
    matches!(vc.kind, VcKind::UnsupportedMir { .. }) && vc.formula != Formula::Bool(true)
}

pub(super) fn unsupported_mir_vc(
    func: &VerifiableFunction,
    kind: String,
    detail: String,
    span: SourceSpan,
) -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::UnsupportedMir { kind, detail },
        function: func.name.as_str().into(),
        location: span,
        // Direct solver callers fail closed: VCs are violation formulas, so
        // `true` is SAT and must never be reported as a proof. The compiler
        // path preclassifies this VC as Unknown before solver dispatch.
        formula: unsupported_mir_fail_closed_formula(),
        contract_metadata: None,
        obligation: None,
    }
}

/// Convert a typed public-body admission failure into the ordinary fail-closed
/// VC representation used by infallible generation APIs.  The fallible
/// [`crate::try_generate_vcs`] entry returns the same error directly.
pub(crate) fn malformed_trust_ir_vc(
    func: &VerifiableFunction,
    error: &crate::VcgenError,
) -> VerificationCondition {
    unsupported_mir_vc(func, "MalformedTrustIr".to_string(), error.to_string(), func.span.clone())
}

pub(super) fn collect_statement_unsupported(
    func: &VerifiableFunction,
    block: BlockId,
    stmt_index: usize,
    stmt: &Statement,
    vcs: &mut Vec<VerificationCondition>,
) {
    match stmt {
        Statement::Assign { place, rvalue, span } => {
            collect_place_type_unsupported(
                func,
                &format_args!("bb{} stmt{} assignment place", block.0, stmt_index),
                span,
                place,
                vcs,
            );
            if let Rvalue::Aggregate(kind, operands) = rvalue {
                collect_aggregate_field_sort_unsupported(
                    func,
                    &format_args!("bb{} stmt{} aggregate field", block.0, stmt_index),
                    span,
                    place,
                    kind,
                    operands,
                    vcs,
                );
            }
            collect_rvalue_unsupported(
                func,
                &format_args!("bb{} stmt{}", block.0, stmt_index),
                span,
                place,
                rvalue,
                vcs,
            );
        }
        Statement::SetDiscriminant { place, variant_index } => {
            let span = SourceSpan::default();
            // Trust: piece #13 — a `SetDiscriminant` on a coroutine FRAME writes
            // the resume-STATE selector (`discriminant((*self)) = k`), not a data
            // value. The frame is modeled opaquely, so this carries no safety
            // obligation and defines no fact used by any bound. Obligation-free.
            if place_is_coroutine_frame(func, place) {
                return;
            }
            collect_place_type_unsupported(
                func,
                &format_args!("bb{} stmt{} set-discriminant place", block.0, stmt_index),
                &span,
                place,
                vcs,
            );
            let Some(detail) = set_discriminant_support_error(func, place, *variant_index) else {
                return;
            };
            vcs.push(unsupported_mir_vc(
                func,
                "StatementKind::SetDiscriminant".to_string(),
                format!(
                    "bb{} stmt{} writes variant {variant_index}; {detail}",
                    block.0, stmt_index
                ),
                span,
            ));
        }
        Statement::Deinit { place } => {
            let span = SourceSpan::default();
            collect_place_type_unsupported(
                func,
                &format_args!("bb{} stmt{} deinit place", block.0, stmt_index),
                &span,
                place,
                vcs,
            );
            vcs.push(unsupported_mir_vc(
                func,
                "Statement::Deinit".to_string(),
                format!(
                    "bb{} stmt{} stale/internal TrustIr Deinit compatibility variant is not present in current rustc StatementKind; treating as unsupported because deinitialization effects require initializedness semantics",
                    block.0, stmt_index
                ),
                span,
            ));
        }
        Statement::Retag { place } => {
            let span = SourceSpan::default();
            collect_place_type_unsupported(
                func,
                &format_args!("bb{} stmt{} retag place", block.0, stmt_index),
                &span,
                place,
                vcs,
            );
            if retag_is_metadata_noop(func, place) {
                return;
            }
            vcs.push(unsupported_mir_vc(
                func,
                "StatementKind::Retag".to_string(),
                format!(
                    "bb{} stmt{} Stacked Borrows retag requires provenance semantics for raw-pointer or unresolved places",
                    block.0, stmt_index
                ),
                span,
            ));
        }
        Statement::PlaceMention(place) => {
            let span = SourceSpan::default();
            collect_place_type_unsupported(
                func,
                &format_args!("bb{} stmt{} place mention", block.0, stmt_index),
                &span,
                place,
                vcs,
            );
        }
        Statement::Intrinsic { name, args } => {
            let span = SourceSpan::default();
            collect_operands_unsupported(
                func,
                &format_args!("bb{} stmt{} intrinsic args", block.0, stmt_index),
                &span,
                args,
                vcs,
            );
            if intrinsic_is_metadata_noop(func, name, args) {
                return;
            }
            vcs.push(unsupported_mir_vc(
                func,
                "StatementKind::Intrinsic".to_string(),
                format!(
                    "bb{} stmt{} intrinsic `{name}` requires intrinsic-specific semantics",
                    block.0, stmt_index
                ),
                span,
            ));
        }
        Statement::Unsupported { kind, detail, operands, span } => {
            vcs.push(unsupported_mir_vc(
                func,
                kind.clone(),
                format!("bb{} stmt{}: {detail}", block.0, stmt_index),
                span.clone(),
            ));
            collect_operands_unsupported(
                func,
                &format_args!("bb{} stmt{} unsupported operands", block.0, stmt_index),
                span,
                operands,
                vcs,
            );
        }
        // MODELED statement: its bounds/overlap obligations come from the sep
        // engine (`SepEngine::interpret_statement` -> `interpret_ptr_copy`), so
        // no `UnsupportedMir` marker is owed for the statement itself. Its
        // OPERANDS still fail closed here exactly like `Intrinsic`/`Unsupported`
        // operands do — an `Operand::Unsupported` or rejected symbolic formula
        // inside the copy must surface, not slide through the wildcard.
        Statement::CopyNonOverlapping { src, dst, count, span, .. } => {
            for (slot, operand) in [("src", src), ("dst", dst), ("count", count)] {
                collect_operand_unsupported(
                    func,
                    &format_args!("bb{} stmt{} copy_nonoverlapping {slot}", block.0, stmt_index),
                    span,
                    operand,
                    vcs,
                );
            }
        }
        _ => {}
    }
}

pub(super) fn retag_is_metadata_noop(
    func: &VerifiableFunction,
    place: &trust_types::Place,
) -> bool {
    // Retag only changes Stacked Borrows/provenance metadata. It is verification-inert
    // for safe MIR, but raw-pointer or unresolved places need a provenance model.
    crate::place_ty_cow(func, place).is_some() && !has_intrinsic_unsafe_surface(func)
}

/// `pub(crate)` (2026-10-09, trust-interval-drop-havoc) for the interval lane's
/// statement transfer (`abstract_interp::transfer::StmtWrite::of`), which forgets
/// every tracked name at an intrinsic statement this predicate does not clear.
pub(crate) fn intrinsic_is_metadata_noop(
    func: &VerifiableFunction,
    name: &str,
    args: &[Operand],
) -> bool {
    // trust-mir-extract lowers rustc's NonDivergingIntrinsic::Assume to this
    // statement form. We deliberately do not add it as a solver assumption;
    // ignoring it over-approximates behavior and avoids proving from optimizer
    // metadata. Other intrinsics may mutate memory or enforce UB preconditions.
    name == "assume"
        && args.len() == 1
        && crate::operand_ty_cow(func, &args[0]).is_some_and(|t| matches!(t.as_ref(), Ty::Bool))
}

/// Trust: piece #13 (safe-async data-safety) — whether `place` is rooted at a
/// coroutine FRAME (the `self` of a resume body, a coroutine-typed local). The
/// resume body reads/writes the frame's state DISCRIMINANT (`discriminant((*self)) = k`
/// / `_ = discriminant((*self))`) and its across-await FIELDS through such a
/// place. A coroutine frame is modeled OPAQUELY (`Ty::Coroutine`, no fields), so
/// its discriminant is the *resume-state selector*, NOT a data value any safety
/// obligation depends on. Writing/reading it must be OBLIGATION-FREE (no
/// `UnsupportedMir` stamp) AND must not define any fact — the state is never
/// used to justify an arithmetic/bounds bound, and havocing across the suspend
/// is exactly the sound over-approximation. We detect the frame by peeling the
/// base local's declared type through `&`/`&mut`/`*mut`: a coroutine `self` is
/// spelled `Pin<&mut {coroutine}>`→`&mut {coroutine}`, so the frame place bases
/// on a local whose type dereferences to `Ty::Coroutine`.
pub(crate) fn place_is_coroutine_frame(
    func: &VerifiableFunction,
    place: &trust_types::Place,
) -> bool {
    let Some(mut ty) = crate::local_ty_ref(func, place.local) else {
        return false;
    };
    // Peel reference/raw-pointer layers (Pin's inner `&mut {coroutine}` is a Ref).
    loop {
        match ty {
            Ty::Ref { inner, .. } => ty = inner,
            Ty::RawPtr { pointee, .. } => ty = pointee,
            _ => break,
        }
    }
    matches!(ty, Ty::Coroutine { .. })
}

/// The DECODED declared discriminant a `SetDiscriminant` of `variant_index` on
/// `place` writes (`Ty::variant_tag`); `Err` when the place's type is unknown or
/// its variant descriptor has no such variant.
fn set_discriminant_tag(
    func: &VerifiableFunction,
    place: &trust_types::Place,
    variant_index: usize,
) -> Result<i128, String> {
    crate::place_ty_cow(func, place).and_then(|ty| ty.variant_tag(variant_index)).ok_or_else(
        || {
            format!(
                "variant {variant_index} has no declared discriminant in the variant descriptor of `{}`",
                place_to_var_name(func, place)
            )
        },
    )
}

/// Trust (triage ticket 216): the names a `SetDiscriminant` on `place` writes
/// besides the place itself — the canonical `discr_<place>` variable and the
/// explicit tag field's variable, the two names `set_discriminant_definitions`
/// defines.
///
/// The write oracle (`extend_with_assigned_place_dests`, `stmt_direct_write_names`)
/// adds these even when `set_discriminant_definitions` refuses the write (a tag
/// the field cannot hold) and so defines nothing: `discr_<place>` is not a
/// projection of the place, so killing the bare place never reached it, and a
/// stale `discr_<place> == old` fact survived the write. When the definitions
/// succeed, the block-level sets already held both names as the definitions' own
/// def names; the per-statement sets (`stmt_direct_write_names`) gain
/// `discr_<place>` in both cases. Adding a written name only kills or versions
/// more, so it can turn a proof into a failure, never the reverse.
pub(crate) fn set_discriminant_synthetic_write_names(
    func: &VerifiableFunction,
    place: &trust_types::Place,
) -> [Option<String>; 2] {
    let discr = crate::discriminant_formula_var_name(&place_to_var_name(func, place));
    let tag_field = crate::explicit_discriminant_field_for_place(func, place)
        .ok()
        .map(|explicit| place_to_var_name(func, &explicit.place));
    [Some(discr), tag_field]
}

pub(crate) fn set_discriminant_definitions(
    func: &VerifiableFunction,
    place: &trust_types::Place,
    variant_index: usize,
) -> Result<Vec<Formula>, String> {
    set_discriminant_definitions_with_place_name(func, place, variant_index, None)
}

fn set_discriminant_definitions_with_place_name(
    func: &VerifiableFunction,
    place: &trust_types::Place,
    variant_index: usize,
    place_name_hint: Option<&str>,
) -> Result<Vec<Formula>, String> {
    // TrustIr's simple tagged-ADT abstraction stores the DECODED declared
    // discriminant in an explicit tag field, and the canonical discr_* fact
    // carries the same value — the one `enum_variant_tag_set` constrains discr_*
    // to and every tag reader compares against. Never the variant index (triage
    // ticket 216): for `enum E { A = 5, B = 9 }` an index fact `discr_e == 1`
    // contradicted `discr_e ∈ {5, 9}`.
    let explicit = crate::explicit_discriminant_field_for_place(func, place)?;
    let tag = set_discriminant_tag(func, place, variant_index)?;
    let (explicit_sort, explicit_value) =
        crate::explicit_discriminant_value_formula(&explicit.ty, tag, variant_index)?;
    let canonical_value = Formula::Int(tag);
    let owned_place_name;
    let place_name = match place_name_hint {
        Some(name) => name,
        None => {
            owned_place_name = place_to_var_name(func, place);
            owned_place_name.as_str()
        }
    };
    let explicit_name = place_to_var_name(func, &explicit.place);

    Ok(vec![
        Formula::Eq(Box::new(Formula::Var(explicit_name, explicit_sort)), Box::new(explicit_value)),
        Formula::Eq(
            Box::new(Formula::Var(crate::discriminant_formula_var_name(place_name), Sort::Int)),
            Box::new(canonical_value),
        ),
    ])
}

pub(super) fn set_discriminant_support_error(
    func: &VerifiableFunction,
    place: &trust_types::Place,
    variant_index: usize,
) -> Option<String> {
    match crate::explicit_discriminant_field_for_place(func, place) {
        Ok(explicit) => set_discriminant_tag(func, place, variant_index)
            .and_then(|tag| {
                crate::explicit_discriminant_value_formula(&explicit.ty, tag, variant_index)
            })
            .err()
            .map(|detail| {
                format!(
                    "ADT discriminant/tag field `{}` exists but the discriminant of variant {variant_index} is not representable: {detail}",
                    explicit.name
                )
            }),
        Err(detail) => Some(format!(
            "{detail}; SetDiscriminant support is limited to simple tagged ADTs with explicit bool/integer discriminant storage"
        )),
    }
}

pub(super) fn extract_set_discriminant_definitions(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
) -> Vec<Formula> {
    extract_set_discriminant_definitions_until(func, block, block.stmts.len())
}

pub(super) fn extract_set_discriminant_definitions_until(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    end_stmt_exclusive: usize,
) -> Vec<Formula> {
    let mut groups: Vec<Vec<Formula>> = Vec::new();
    let mut seen_places = FxHashSet::default();

    for stmt in block.stmts.iter().take(end_stmt_exclusive).rev() {
        let Statement::SetDiscriminant { place, variant_index } = stmt else {
            continue;
        };
        let key = place_to_var_name(func, place);
        if seen_places.contains(key.as_str()) {
            continue;
        }
        if let Ok(defs) = set_discriminant_definitions_with_place_name(
            func,
            place,
            *variant_index,
            Some(key.as_str()),
        ) {
            groups.push(defs);
        }
        seen_places.insert(key);
    }

    if groups.len() <= 1 {
        return groups.pop().unwrap_or_default();
    }
    groups.reverse();
    groups.into_iter().flatten().collect()
}

pub(super) fn collect_terminator_unsupported(
    func: &VerifiableFunction,
    block: BlockId,
    terminator: &Terminator,
    vcs: &mut Vec<VerificationCondition>,
) {
    match terminator {
        Terminator::Opaque { kind, targets, span } => vcs.push(unsupported_mir_vc(
            func,
            kind.clone(),
            format!("bb{} targets {:?}", block.0, targets),
            span.clone(),
        )),
        Terminator::SwitchInt { discr, span, .. } => collect_operand_unsupported(
            func,
            &format_args!("bb{} switch discriminant", block.0),
            span,
            discr,
            vcs,
        ),
        Terminator::Assert { cond, span, .. } => collect_operand_unsupported(
            func,
            &format_args!("bb{} assert condition", block.0),
            span,
            cond,
            vcs,
        ),
        Terminator::Call { func: callee, args, dest, target, span, callee_key, .. } => {
            // Trust: a `panic!`/`assert!` lowers to a diverging call to a panic
            // intrinsic whose arguments are the panic message/location (e.g. a
            // `&str` constant). Those arguments are irrelevant to safety — the
            // obligation that matters is that the panic site is unreachable,
            // which is generated as a panic-freedom obligation during TrustIr
            // lowering. Emitting an `unsupported_mir` VC for an unrepresentable
            // panic-message constant would wedge every `assert!`/`panic!` at
            // Unknown, so skip operand collection for the sysroot's own panic
            // entries — decided by the extractor's DIVERGE-ENTRY-1 stamp and the
            // absence of a continuation, never by the rendered name alone
            // (PANIC-SKIP-ANCHOR-1; see `diverging_panic_entry_operands_unread`).
            if !diverging_panic_entry_operands_unread(callee_key.as_ref(), callee, target.is_none())
            {
                collect_operands_unsupported(
                    func,
                    &format_args!("bb{} call args", block.0),
                    span,
                    args,
                    vcs,
                );
            }
            // SOUNDNESS/honesty (hunt-15 Class D): a NORMALLY-RETURNING call to a
            // known-panicking std method — `Option`/`Result` `unwrap`/`expect`/
            // `unwrap_err`/`expect_err` — carries an UNMODELED panic path (it panics
            // on None/Err). Without an explicit receiver model, leaving this silent
            // lets a function with ANOTHER provable obligation report
            // "fully proved" while the unwrap panics at runtime — the DEFAULT-mode
            // analogue of the -full #47/#48 unmodeled-panicking-call hole. Surface it as
            // an UnsupportedMir obligation, which the compiler preclassifies to Unknown
            // (NEVER Proved) and never dispatches to a solver — so this can only make the
            // headline MORE honest ("N proved, 1 unknown", not fully proved), never
            // introduce a false proof or a vacuous discharge. The match/`if let` idiom
            // (the modeled, panic-free equivalent) is unaffected; the strict default
            // already fails these closed.
            //
            // Trust (unwrap panic-freedom, dominated-safe): when the receiver is a
            // MODELED std `Option`/`Result` whose discriminant is PINNED by real
            // dataflow (`unwrap_panic_freedom_modeled`, the SAME recognizer the
            // solvable lane keys on), the UnsupportedMir row is REPLACED by the
            // refutation-grade VC from `generate_unwrap_panic_freedom_vcs` —
            // never silently dropped: every other case keeps this fail-closed row.
            if target.is_some() {
                let m = method_tail(callee);
                if matches!(m, "unwrap" | "expect" | "unwrap_err" | "expect_err")
                    && (callee.contains("Option") || callee.contains("Result"))
                    && !unwrap_is_infallible_slice_to_array(func, callee, args, dest)
                    // Trust (countdown-loop piece, B0): a const-int `try_into().expect()`
                    // that provably fits its target is success-by-construction — the
                    // panic path is unreachable, so no Unknown row (see
                    // `expect_infallible_const_int_conversion` for the hard gates).
                    && expect_infallible_const_int_conversion(func, callee, args, dest).is_none()
                    && !unwrap_panic_freedom_modeled(func, callee, args)
                {
                    vcs.push(unsupported_mir_vc(
                        func,
                        format!("Call::{m}::panic-freedom-unverified"),
                        format!(
                            "bb{}: `{m}` panics on None/Err and its panic-freedom is not \
                             modeled — match / `if let` to prove it; use `-Z trust-policy=advisory` only \
                             for non-proof triage",
                            block.0
                        ),
                        span.clone(),
                    ));
                }
                // SOUNDNESS/honesty (reliability E1): a NORMALLY-RETURNING call to a
                // bounds-panicking slice/`Vec` mutator — `rotate_left`/`rotate_right`
                // (`<[T]>`: panic `mid > len`) or `split_off` (`Vec`/`String`/`VecDeque`:
                // panic `at > len`). Unlike `s.split_at(mid)` (modeled precisely by the
                // `SliceMethodPanic::SplitAt` lane), these lower to a `Terminator::Call`
                // carrying NO caller-visible `Projection::Index` AND are not in
                // `is_known_panicking_method`/`slice_method_panic`, so an unmodeled call is
                // vacuously safe — a default-mode headline OVER-CREDIT ("N proved" while
                // `s.rotate_left(99)` panics at runtime). Surface them as an UnsupportedMir
                // obligation, which the compiler preclassifies to Unknown (NEVER Proved)
                // and never dispatches to a solver, so this can ONLY make the headline more
                // honest ("N proved, 1 unknown"), never introduce a false proof or a
                // vacuous discharge. This is a near-exact mirror of the Class-D Unknown
                // shape above, deliberately CONSERVATIVE (an unmodeled Unknown, not the
                // precise `mid <= len` bound the `SplitAt` arm models) — modeling the bound
                // precisely is a follow-up; the strict default already fails these
                // closed. The recognizer is gated on a confirmed slice/`Vec` receiver so a
                // TOTAL integer `u32::rotate_left`/`rotate_right` is NEVER flagged.
                let slice_mutator = matches!(
                    m,
                    "rotate_left"
                        | "rotate_right"
                        | "split_off"
                        | "drain"
                        | "copy_within"
                        | "select_nth_unstable"
                        | "select_nth_unstable_by"
                        | "select_nth_unstable_by_key"
                        | "extend_from_within"
                ) && is_bounds_panicking_slice_mutator(func, callee, args);
                if slice_mutator {
                    vcs.push(unsupported_mir_vc(
                        func,
                        format!("Call::{m}::panic-freedom-unverified"),
                        format!(
                            "bb{}: `{m}` panics on an out-of-range argument (`> len`) and its \
                             panic-freedom is not modeled — guard the argument; use `-Z trust-policy=advisory` \
                             only for non-proof triage",
                            block.0
                        ),
                        span.clone(),
                    ));
                }
                // Index-panicking `Vec`/`String` mutators (`remove`/`insert`/
                // `swap_remove`/`insert_str`) — exact-path gated (see the
                // recognizer): their panic set is known (`index >= len` /
                // `index > len` / char-boundary) and reachable for a caller-supplied
                // container, so an unguarded, unmodeled call must surface the same
                // `panic-freedom-unverified` row, which strict policy counts as
                // FAILED rather than silently accepting a callee the verifier
                // never saw (`absent_callee_call_only_mono`).
                // `char::encode_utf8`/`encode_utf8_raw` panic on a destination
                // buffer shorter than the encoding — the caller's own buffer, so the
                // same family and the same row. See the recognizer for why this
                // replaces an accident (the callee being absent from the tolerance
                // ledger) with the actual reason.
                // Trust (2026-10-09, sweep p56): `encode_utf8` panics only when the buffer
                // is shorter than `len_utf8() <= 4`. A destination that is exactly an
                // unsize cast of `&mut [u8; N]` with `N >= 4` (the coercion fixes its
                // length to `N`) can never be too short.
                // (Merge 2026-10-14: `encode_utf16` is not this row's. Review round 90's
                // `N >= 2` arm left with it: the UTF-16 twins carry their own ROOT-call
                // row below, which models no buffer length — UTF8-ENCODE-UTF16-SHORTBUF-1.)
                // Trust (1.101 migration, 2026-10-18): `encode_utf8_raw` too —
                // upstream's `char::encode_utf8` is now inlined into the root MIR
                // the extractor reads, so the root call names the raw encoder
                // directly. Same buffer, same bound (`len_utf8(code) <= 4` for
                // every `u32`), same unsize-length proof.
                if matches!(m, "encode_utf8" | "encode_utf8_raw")
                    && is_buffer_panicking_char_encoder(callee)
                {
                    let buffer_always_fits = args
                        .get(1)
                        .and_then(|dst| super::loop_bounds::unsized_array_len(func, dst))
                        .is_some_and(|len| len >= 4);
                    if !buffer_always_fits {
                        vcs.push(unsupported_mir_vc(
                            func,
                            format!("Call::{m}::panic-freedom-unverified"),
                            format!(
                                "bb{}: `{m}` panics when the destination buffer is shorter than the \
                                 encoding and its panic-freedom is not modeled — size the buffer with \
                                 `char::len_utf8()` (or use a 4-byte buffer); use \
                                 `-Z trust-policy=advisory` only for non-proof triage",
                                block.0
                            ),
                            span.clone(),
                        ));
                    }
                }
                // Trust (UTF8-ENCODE-UTF16-SHORTBUF-1, 2026-10-05): `char::encode_utf16` /
                // `encode_utf16_raw` panic on the same short caller buffer. Its own
                // recognizer, asked of ROOT call sites only (this lane, and the
                // compiler's root-call tolerance): core's `EncodeUtf16::next` calls it
                // with a buffer of its own, and the bundle walk must not refuse that.
                // No buffer length is modeled, so every call is refused — a 2-element
                // buffer, which cannot panic, included (the over-refusal `encode_utf8`
                // has for a 4-byte buffer; docs/DECISION_QUEUE.md).
                if matches!(m, "encode_utf16" | "encode_utf16_raw")
                    && is_buffer_panicking_char_utf16_encoder(callee)
                {
                    vcs.push(unsupported_mir_vc(
                        func,
                        format!("Call::{m}::panic-freedom-unverified"),
                        format!(
                            "bb{}: `{m}` panics when the destination buffer is shorter than the \
                             character's UTF-16 length (`char::len_utf16()`, at most 2) and the \
                             buffer's length is not modeled, so the call is refused whatever its \
                             buffer; use `-Z trust-policy=advisory` only for non-proof triage",
                            block.0
                        ),
                        span.clone(),
                    ));
                }
                // Trust (W4 fix round 1, 2026-09-25): `VecDeque`'s caller-value members
                // that no call-site lane charges (`insert`, `splice`, `extract_if`,
                // `prepend_from_within`) — the same family and the same row as the
                // `Vec`/`String` mutators below, which exclude `collections::`
                // wholesale. The members `is_bounds_panicking_slice_mutator` already
                // rows above (`split_off`, `rotate_*`, `drain`, `extend_from_within`)
                // are not rowed twice. No guard discharges this row: `insert` resizes
                // its receiver, and no length tie survives a resize here (the argument
                // main's `collection_range` makes for `insert_mut`), so a GUARDED call is
                // an over-refusal, pinned in `tests/ui/trust/vecdeque_caller_value_panic.rs`.
                // `swap`/`range`/`range_mut`/`insert_mut`/`d[i]` are charged by
                // `collection_range` (precise over a stable length) and are NOT rowed
                // here whenever that recognizer names the call (reconciled with
                // 92e7829ca5, W4 salvage 2026-09-28; see the recognizer).
                if !slice_mutator
                    && matches!(
                        m,
                        "drain"
                            | "splice"
                            | "extract_if"
                            | "extend_from_within"
                            | "prepend_from_within"
                            | "insert"
                            | "split_off"
                            | "rotate_left"
                            | "rotate_right"
                            | "swap"
                            | "range"
                            | "range_mut"
                            | "insert_mut"
                    )
                    && is_caller_value_panicking_deque_method(callee)
                    // Trust (cap vec-drain, 2026-10-03): `d.drain(..)` (and `0..`, `..0`)
                    // left the row above because its range check cannot fail; it must not
                    // fall through to this one.
                    && !super::collection_range::std_vec_drain_range_cannot_panic(
                        func, callee, args,
                    )
                {
                    vcs.push(unsupported_mir_vc(
                        func,
                        format!("Call::{m}::panic-freedom-unverified"),
                        format!(
                            "bb{}: `VecDeque::{m}` panics on an out-of-range index or range and \
                             its panic-freedom is not modeled — use a checked form (`get`, \
                             `get_mut`) or guard the argument; use `-Z trust-policy=advisory` \
                             only for non-proof triage",
                            block.0
                        ),
                        span.clone(),
                    ));
                }
                // Trust (W4 salvage, 2026-09-28): the BACKSTOP for `d[i]` / `d[i] = x`.
                // `collection_range::deque_scalar_index_body` charges the scalar deque
                // index at this call (precise, or its own fail-honest row); it answers
                // `None` only when it cannot read the receiver or the index operand's
                // type. The compiler no longer withholds the vanilla tolerance for the
                // `Index`/`IndexMut` callee by name (that refused the guarded forms main
                // proves), so a call that lane cannot read must not go silent: it gets
                // the fail-closed row. Never fires where main's row exists — no guarded
                // program main proves is refused by it.
                if matches!(m, "index" | "index_mut")
                    && super::unwrap_panic::is_deque_scalar_index_call(callee)
                    && super::collection_range::deque_scalar_index_body(func, args).is_none()
                {
                    vcs.push(unsupported_mir_vc(
                        func,
                        format!("Call::{m}::panic-freedom-unverified"),
                        format!(
                            "bb{}: indexing a `VecDeque` panics (\"Out of bounds access\") when the \
                             index is not below the length, and this call's receiver or index could \
                             not be read to charge it — use `get`/`get_mut` or guard the index; use \
                             `-Z trust-policy=advisory` only for non-proof triage",
                            block.0
                        ),
                        span.clone(),
                    ));
                }
                // (2026-10-09) The sole, last resize of a `&mut Vec` parameter carries the
                // real index precondition instead (`panic_calls`, VecPanicMethod arm).
                // Trust (VEC-INSERT, 2026-09-25): a `Vec` mutator reached inside its
                // base's pre-mutation region is charged its REAL index precondition by
                // the safety lane (`vec_mutator_index_violation`) instead.
                if matches!(m, "remove" | "insert" | "swap_remove" | "insert_str")
                    && is_index_panicking_container_mutator(callee)
                {
                    let sole_vec_resize = args
                        .first()
                        .and_then(|recv| match recv {
                            Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => {
                                if crate::local_defs::is_parameter(func, p.local) {
                                    Some(trust_types::Place::local(p.local))
                                } else {
                                    crate::guards::base_collection_place_unique(func, p.local)
                                }
                            }
                            _ => None,
                        })
                        .is_some_and(|base| {
                            base.projections.is_empty()
                                && super::value_facts::vec_sole_mutator_block(func, base.local)
                                    .is_some()
                        });
                    let modeled_in_region = func
                        .body
                        .blocks
                        .get(block.0)
                        .filter(|candidate| candidate.id == block)
                        .or_else(|| func.body.blocks.iter().find(|candidate| candidate.id == block))
                        .is_some_and(|call_block| {
                            vec_mutator_index_violation(func, call_block).is_some()
                        });
                    if !sole_vec_resize && !modeled_in_region {
                        vcs.push(unsupported_mir_vc(
                            func,
                            format!("Call::{m}::panic-freedom-unverified"),
                            format!(
                                "bb{}: `{m}` panics on an out-of-range index (or non-char-boundary) and \
                                 its panic-freedom is not modeled — guard the index; use \
                                 `-Z trust-policy=advisory` only for non-proof triage",
                                block.0
                            ),
                            span.clone(),
                        ));
                    }
                }
            }
        }
        Terminator::TailCall { func: callee, args, span, callee_key, .. } => {
            // The bridge handles this through the ordinary call path with the
            // implicit return destination. Keep every unsupported argument
            // visible here rather than silently dropping it. The one exception is
            // the Call arm's: the bridge lowers a tail call as a call with NO
            // continuation (`lower_terminator_normal`, `target: None`), so a
            // stamped sysroot panic entry reached by `become` takes the same
            // must-be-unreachable site encoding and its arguments are read by no
            // proof (PANIC-SKIP-ANCHOR-1).
            if !diverging_panic_entry_operands_unread(callee_key.as_ref(), callee, true) {
                collect_operands_unsupported(
                    func,
                    &format_args!("bb{} tail-call args", block.0),
                    span,
                    args,
                    vcs,
                );
            }
        }
        _ => {}
    }
}

/// PANIC-SKIP-ANCHOR-1 (2026-10-05): may this call site's ARGUMENTS go
/// uncollected by [`collect_operands_unsupported`]?
///
/// Only when the site is a call to one of the SYSROOT's own panic entry points
/// that the bridge lowers as "this program point must be proven unreachable"
/// (`Assert(false)` + one `PanicFreedom` row, then `Unreachable`: the
/// diverging-site arm of `trust-ir-bridge`'s `lower.rs`). At such a site the
/// arguments — a panic message, a `fmt::Arguments`, an identity-less payload —
/// are read by no proof, and an `UnsupportedMir` row for one of them would only
/// wedge every real `assert!`/`panic!` at Unknown. Every conjunct below is one
/// the bridge arm also requires, so every site skipped here is a site the bridge
/// charges as must-be-unreachable:
///
/// * `no_continuation`: the bridge sees the call with no normal-return target —
///   a `Call` whose `target` is `None`, or any `TailCall`, which the bridge
///   rewrites to a `Call` with `target: None` (`lower_terminator_normal`). A
///   call WITH a continuation takes the ordinary call arms, where its
///   arguments flow into the callee and its result, so they are proof input
///   whatever the callee is called;
/// * the extractor's DIVERGE-ENTRY-1 stamp, read through
///   [`trust_types::CalleeKey::opt_diverging_entry`]: the callee's `DefId` is in
///   a real sysroot crate, is not a trait item, and its GENERIC-FREE definition
///   path is a panic, abort or UB entry. `None` (no key, an indirect call, a
///   frozen dump or hand-built key, any user crate) keeps every row;
/// * [`is_panic_intrinsic_call`] on the rendering, the first disjunct of the
///   bridge arm's own second conjunct (`is_panic_call`). For a stamped panic
///   entry it holds by construction, so it can only NARROW: the stamped R177
///   terminals (`unwrap_failed`, `expect_failed`, `handle_error`, `abort`, …)
///   and the UB family keep their argument rows exactly as before this anchor.
///   Widening the skip to them is a separate, unmeasured capability change
///   (DECISION_QUEUE PANIC-SKIP-ANCHOR-1).
///
/// Before this, the rendering alone decided. A user `fn panic(x: u64) -> u64`
/// that returns normally, or any fn in a user module named `panicking`, had the
/// `ConstValue::OpaqueScalar` row of its identity-less `T::LIMIT` argument
/// dropped, and `-Ztrust-policy=certify` accepted the caller where the same body
/// under another name was refused (measured on the stage 1 of `76a6ea45b2`;
/// `tests/ui/trust/panic_skip_user_fn_named_panic.rs`).
pub(super) fn diverging_panic_entry_operands_unread(
    callee_key: Option<&trust_types::CalleeKey>,
    callee: &str,
    no_continuation: bool,
) -> bool {
    no_continuation
        && trust_types::CalleeKey::opt_diverging_entry(callee_key).is_some()
        && is_panic_intrinsic_call(callee)
}

#[cfg(test)]
mod dedup_stop_cause_tests {
    use trust_types::determinism::StopCause;

    use super::*;

    fn unsupported(kind: &str, detail: &str, line: u32) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::UnsupportedMir { kind: kind.to_string(), detail: detail.to_string() },
            function: "m::f".into(),
            location: SourceSpan {
                file: "src/lib.rs".to_string(),
                line_start: line,
                col_start: 1,
                line_end: line,
                col_end: 2,
            },
            formula: unsupported_mir_fail_closed_formula(),
            contract_metadata: None,
            obligation: None,
        }
    }

    fn detail_cause(vc: &VerificationCondition) -> Option<StopCause> {
        match &vc.kind {
            VcKind::UnsupportedMir { detail, .. } => StopCause::from_reason(detail),
            _ => None,
        }
    }

    /// Determinism review 2026-09-29: a type-lowering marker left by a CLOCK
    /// trip must not disappear behind a deduplicated sibling at the same display
    /// key that reads as the deterministic `unsupported`.
    #[test]
    fn a_collapsed_clock_stop_survives_on_the_kept_row() {
        let clock = StopCause::WallBackstop
            .stamp("type lowering exceeded the per-function verification budget");
        let kept = dedup_unsupported_by_display_key(vec![
            unsupported("TyKind", "local _3: dyn Trait", 7),
            unsupported("TyKind", &format!("local _4: {clock}"), 7),
            unsupported("TyKind", "another line", 9),
        ]);
        assert_eq!(kept.len(), 2, "one row per display key");
        assert_eq!(detail_cause(&kept[0]), Some(StopCause::WallBackstop), "{:?}", kept[0].kind);
        assert!(
            matches!(&kept[0].kind, VcKind::UnsupportedMir { detail, .. }
                if detail.starts_with("local _3: dyn Trait")),
            "the kept row keeps its own text: {:?}",
            kept[0].kind
        );
        assert_eq!(detail_cause(&kept[1]), None);
    }

    #[test]
    fn a_collapsed_deterministic_stop_leaves_the_kept_row_as_it_was() {
        let steps =
            StopCause::Steps.stamp("type lowering exceeded the per-function verification budget");
        let kept = dedup_unsupported_by_display_key(vec![
            unsupported("TyKind", "local _3: dyn Trait", 7),
            unsupported("TyKind", &format!("local _4: {steps}"), 7),
        ]);
        assert_eq!(kept.len(), 1);
        assert_eq!(detail_cause(&kept[0]), None, "{:?}", kept[0].kind);
        // A kept clock stop is never downgraded by a later deterministic one.
        let clock = StopCause::WallBackstop.stamp("budget");
        let kept = dedup_unsupported_by_display_key(vec![
            unsupported("TyKind", &clock, 7),
            unsupported("TyKind", &steps, 7),
        ]);
        assert_eq!(detail_cause(&kept[0]), Some(StopCause::WallBackstop));
    }

    #[test]
    fn dedup_preserves_distinct_kinds_and_spans_without_cloning_duplicates() {
        let mut slot = KeptDisplaySlot::One(0);
        slot.push(1);
        slot.push(2);
        let rows = vec![
            unsupported("TyKind", "a", 7),
            unsupported("RvalueKind", "b", 7),
            unsupported("TyKind", "c", 8),
        ];
        assert_eq!(slot.find(&rows, "TyKind", &rows[0].location), Some(0));
        assert_eq!(slot.find(&rows, "RvalueKind", &rows[1].location), Some(1));
        assert_eq!(slot.find(&rows, "TyKind", &rows[2].location), Some(2));
        assert_eq!(slot.find(&rows, "OtherKind", &rows[0].location), None);

        let kept = dedup_unsupported_by_display_key(vec![
            unsupported("TyKind", "first", 7),
            unsupported("RvalueKind", "second", 7),
            unsupported("TyKind", "dup-first", 7),
            unsupported("TyKind", "third", 8),
            unsupported("RvalueKind", "dup-second", 7),
        ]);
        assert_eq!(kept.len(), 3);
        assert!(matches!(&kept[0].kind, VcKind::UnsupportedMir { kind, detail }
            if kind == "TyKind" && detail == "first"));
        assert!(matches!(&kept[1].kind, VcKind::UnsupportedMir { kind, detail }
            if kind == "RvalueKind" && detail == "second"));
        assert!(matches!(&kept[2].kind, VcKind::UnsupportedMir { kind, detail }
            if kind == "TyKind" && detail == "third"));
    }
}
