// Fail-closed detection of MIR outside the modeled fragment. Anything not
// recognised here must surface as an `UnsupportedMir` row rather than be
// silently skipped, so these collectors are the boundary between "proved" and
// "not modeled" for types, statements and terminators.

use super::*;

pub(super) fn unsupported_mir_vcs(func: &VerifiableFunction) -> Vec<VerificationCondition> {
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
pub(super) fn dedup_unsupported_by_display_key(vcs: Vec<VerificationCondition>) -> Vec<VerificationCondition> {
    let mut seen: FxHashSet<(String, SourceSpan)> = FxHashSet::default();
    let mut out = Vec::new();
    for vc in vcs {
        match &vc.kind {
            VcKind::UnsupportedMir { kind, .. } => {
                if seen.insert((kind.clone(), vc.location.clone())) {
                    out.push(vc);
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

pub(super) fn collect_body_type_unsupported(func: &VerifiableFunction, vcs: &mut Vec<VerificationCondition>) {
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
    if seen_types.insert(&func.body.return_ty) {
        collect_type_unsupported(
            func,
            "return type".to_string(),
            &func.body.return_ty,
            &func.span,
            vcs,
        );
    }
    for local in &func.body.locals {
        if seen_types.insert(&local.ty) {
            collect_type_unsupported(
                func,
                format!("local _{} type", local.index),
                &local.ty,
                &func.span,
                vcs,
            );
        }
    }
}

pub(super) fn collect_type_unsupported(
    func: &VerifiableFunction,
    context: String,
    ty: &Ty,
    span: &SourceSpan,
    vcs: &mut Vec<VerificationCondition>,
) {
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
            collect_type_unsupported(func, format!("{context} pointee"), inner, span, vcs);
        }
        Ty::RawPtr { pointee, .. } => {
            collect_type_unsupported(func, format!("{context} raw pointee"), pointee, span, vcs);
        }
        Ty::Slice { elem } => {
            collect_type_unsupported(func, format!("{context} slice element"), elem, span, vcs);
        }
        Ty::Array { elem, .. } => {
            collect_type_unsupported(func, format!("{context} array element"), elem, span, vcs);
        }
        // Trust: piece #7a — a const-generic array's DECLARATION carries no direct
        // obligation (identical to the `TyKind::Array` relaxation above: the only
        // panic-able array op is an index/slice, which fails closed at its use
        // site via the `bounds` VC on the symbolic length). We DO descend into the
        // element type so a `[SomeUnsupportedElem; N]` still stamps the element's
        // marker. The SymArray itself stamps no spurious declaration marker.
        Ty::SymArray { elem, .. } => {
            collect_type_unsupported(func, format!("{context} array element"), elem, span, vcs);
        }
        Ty::Tuple(fields) => {
            for (index, field_ty) in fields.iter().enumerate() {
                collect_type_unsupported(
                    func,
                    format!("{context} tuple field {index}"),
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
                    format!("{context} field {name}"),
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
                    format!("{context} upvar {index}"),
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
                    format!("{context} param {index}"),
                    param_ty,
                    span,
                    vcs,
                );
            }
            collect_type_unsupported(func, format!("{context} return"), &sig.ret, span, vcs);
        }
        _ => {}
    }
}

pub(super) fn collect_place_type_unsupported(
    func: &VerifiableFunction,
    context: String,
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
                format!("{context} projection {index}"),
                ty,
                span,
                vcs,
            ),
            _ => {}
        }
    }
}

pub(super) fn unsupported_mir_vc(
    func: &VerifiableFunction,
    kind: String,
    detail: String,
    span: SourceSpan,
) -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::UnsupportedMir { kind, detail },
        function: func.name.clone().into(),
        location: span,
        // Direct solver callers fail closed: VCs are violation formulas, so
        // `true` is SAT and must never be reported as a proof. The compiler
        // path preclassifies this VC as Unknown before solver dispatch.
        formula: Formula::Bool(true),
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
                format!("bb{} stmt{} assignment place", block.0, stmt_index),
                span,
                place,
                vcs,
            );
            if let Rvalue::Aggregate(kind, operands) = rvalue {
                collect_aggregate_field_sort_unsupported(
                    func,
                    format!("bb{} stmt{} aggregate field", block.0, stmt_index),
                    span,
                    place,
                    kind,
                    operands,
                    vcs,
                );
            }
            collect_rvalue_unsupported(
                func,
                format!("bb{} stmt{}", block.0, stmt_index),
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
                format!("bb{} stmt{} set-discriminant place", block.0, stmt_index),
                &span,
                place,
                vcs,
            );
            if set_discriminant_definitions(func, place, *variant_index).is_ok() {
                return;
            }
            let detail = set_discriminant_support_error(func, place, *variant_index)
                .unwrap_or_else(|| "SetDiscriminant layout could not be validated".to_string());
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
                format!("bb{} stmt{} deinit place", block.0, stmt_index),
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
                format!("bb{} stmt{} retag place", block.0, stmt_index),
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
                format!("bb{} stmt{} place mention", block.0, stmt_index),
                &span,
                place,
                vcs,
            );
        }
        Statement::Intrinsic { name, args } => {
            let span = SourceSpan::default();
            collect_operands_unsupported(
                func,
                format!("bb{} stmt{} intrinsic args", block.0, stmt_index),
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
                format!("bb{} stmt{} unsupported operands", block.0, stmt_index),
                span,
                operands,
                vcs,
            );
        }
        _ => {}
    }
}

pub(super) fn retag_is_metadata_noop(func: &VerifiableFunction, place: &trust_types::Place) -> bool {
    // Retag only changes Stacked Borrows/provenance metadata. It is verification-inert
    // for safe MIR, but raw-pointer or unresolved places need a provenance model.
    crate::place_ty(func, place).is_some() && !has_intrinsic_unsafe_surface(func)
}

pub(super) fn intrinsic_is_metadata_noop(func: &VerifiableFunction, name: &str, args: &[Operand]) -> bool {
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

pub(crate) fn set_discriminant_definitions(
    func: &VerifiableFunction,
    place: &trust_types::Place,
    variant_index: usize,
) -> Result<Vec<Formula>, String> {
    // TrustIr's simple tagged-ADT abstraction stores the variant index in an
    // explicit tag field; the canonical discr_* fact preserves existing readers.
    let explicit = crate::explicit_discriminant_field_for_place(func, place)?;
    let (explicit_sort, explicit_value) =
        crate::explicit_discriminant_value_formula(&explicit.ty, variant_index)?;
    let canonical_value = crate::u128_to_formula(variant_index as u128);
    let place_name = place_to_var_name(func, place);
    let explicit_name = place_to_var_name(func, &explicit.place);

    Ok(vec![
        Formula::Eq(Box::new(Formula::Var(explicit_name, explicit_sort)), Box::new(explicit_value)),
        Formula::Eq(
            Box::new(Formula::Var(crate::discriminant_formula_var_name(&place_name), Sort::Int)),
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
        Ok(explicit) => crate::explicit_discriminant_value_formula(&explicit.ty, variant_index)
            .err()
            .map(|detail| {
                format!(
                    "ADT discriminant/tag field `{}` exists but variant index is not representable: {detail}",
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
        if !seen_places.insert(key) {
            continue;
        }
        if let Ok(defs) = set_discriminant_definitions(func, place, *variant_index) {
            groups.push(defs);
        }
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
            format!("bb{} switch discriminant", block.0),
            span,
            discr,
            vcs,
        ),
        Terminator::Assert { cond, span, .. } => collect_operand_unsupported(
            func,
            format!("bb{} assert condition", block.0),
            span,
            cond,
            vcs,
        ),
        Terminator::Call { func: callee, args, dest, target, span, .. } => {
            // Trust: a `panic!`/`assert!` lowers to a diverging call to a panic
            // intrinsic whose arguments are the panic message/location (e.g. a
            // `&str` constant). Those arguments are irrelevant to safety — the
            // obligation that matters is that the panic site is unreachable,
            // which is generated as a panic-freedom obligation during TrustIr
            // lowering. Emitting an `unsupported_mir` VC for an unrepresentable
            // panic-message constant would wedge every `assert!`/`panic!` at
            // Unknown, so skip operand collection for recognized panic calls.
            if !is_panic_intrinsic_call(callee) {
                collect_operands_unsupported(
                    func,
                    format!("bb{} call args", block.0),
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
            if target.is_some()
                && is_known_panicking_method(callee)
                && !unwrap_is_infallible_slice_to_array(func, callee, args, dest)
                // Trust (countdown-loop piece, B0): a const-int `try_into().expect()`
                // that provably fits its target is success-by-construction — the
                // panic path is unreachable, so no Unknown row (see
                // `expect_infallible_const_int_conversion` for the hard gates).
                && expect_infallible_const_int_conversion(func, callee, args, dest).is_none()
                && !unwrap_panic_freedom_modeled(func, callee, args)
            {
                let m = method_tail(callee);
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
            if target.is_some() && is_bounds_panicking_slice_mutator(func, callee, args) {
                let m = method_tail(callee);
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
        }
        _ => {}
    }
}
