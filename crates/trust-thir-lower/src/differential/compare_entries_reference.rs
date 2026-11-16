//! Trust (R8-SEAM, `docs/DECISION_QUEUE.md`, taken 2026-10-05): `compare_entries`,
//! `build_pointee_wrapper` and `paired_admitted_promoted_globals` AS THEY WERE before R8-SEAM split
//! the first at its step boundaries, added the in-place spelling, and enumerated the third's
//! candidates from the oracle side — the pre-R8-SEAM text of `differential.rs` (blob
//! `dda61d2863c927a4d11addf6c89ff7bdf95e5461`), verbatim but for the third's `pub(super)` and
//! trust-ir D1b's two refusing table doors in `build_pointee_wrapper` (the same doors
//! `differential.rs` takes, each a `None` like the function's other declines); trust-ir
//! train T8 (a0715f99d4, blob `14974f63dc255c73205b7f0b592fe595b7aeeb87`) changed none of the
//! three, so they are also that blob's text. Every
//! other function they call is unchanged by R8-SEAM, so this file and `differential.rs` together
//! are the pre-R8-SEAM differential. Two consumers:
//!
//! * A TEST-BUILD ORACLE: in a test build, every `compare_entries` call also runs
//!   `compare_entries_in_place` on copies of its two modules, every `compare_entries_in_place`
//!   call also runs the copying spelling on copies, and both run this one; [`cross_check`] asserts
//!   the reports are one report and the in-place spelling returned both modules as they came.
//!   Every unit test that reaches the differential is therefore an old-against-new comparison.
//! * THE PRE-R8-SEAM SEAM's differential, in every build: `crate_module/seam_reference.rs` (the
//!   pre-R8-SEAM crate seam, reached only through the TEST-ONLY `-Ztrust-ir-seam-reference` hook)
//!   calls this `compare_entries`, not `differential::compare_entries`, so that hook compares the
//!   whole old seam — both files' old code — against the whole new one in a production compiler,
//!   on the run-make fixtures and on `core`. No other production path reaches this file.
//!
//! R-2's deletion of the differential deletes this file with it.

use super::*;

/// The three spellings agree on `(thir_module, oracle)`, and the in-place one restores both.
#[cfg(test)]
pub(super) fn cross_check(
    thir_module: &Module,
    thir_entry: FuncId,
    oracle: &Module,
    oracle_entry: FuncId,
    report: &DiffReport,
) {
    let key = |r: &DiffReport| {
        (r.equal, r.unsupported.clone(), r.notes.clone(), r.samples_checked, r.mode)
    };
    let reference = compare_entries(thir_module, thir_entry, oracle, oracle_entry);
    assert_eq!(key(report), key(&reference), "R8-SEAM: a spelling differs from the reference");
    let copying = super::compare_entries_copying(thir_module, thir_entry, oracle, oracle_entry);
    assert_eq!(key(&copying), key(&reference), "R8-SEAM: the copying spelling differs");
    let (mut thir_copy, mut oracle_copy) = (thir_module.clone(), oracle.clone());
    let (in_place, _) =
        super::compare_entries_appending(&mut thir_copy, thir_entry, &mut oracle_copy, oracle_entry);
    assert_eq!(key(&in_place), key(&reference), "R8-SEAM: the in-place spelling differs");
    assert!(&thir_copy == thir_module, "R8-SEAM: the in-place spelling did not restore the THIR side");
    assert!(&oracle_copy == oracle, "R8-SEAM: the in-place spelling did not restore the oracle");
}

/// Trust (B9-A): the interpretation-differential CORE, parameterized over the entry function on
/// each side — verbatim the former body of `compare` steps (2)-(8) (entry lookup, signature
/// resolve + vararg/param-class gates, structural signature agreement with the dual-spelling
/// reclass, sampled interpretation, the value-sample floor, and the Agreed tail). The per-body
/// hook path calls it with `FuncId::new(0)` on both sides; the crate-finalize SEAM calls it with
/// the assembled crate module's spliced entry vs the linked oracle BUNDLE's positional entry —
/// converting call-bearing clean bodies (the former clean-skip-direct-call class) into real
/// verdicts. Every note string is byte-identical to the pre-B9-A wording (classifier-stable).
pub(crate) fn compare_entries(
    thir_module: &Module,
    thir_entry: FuncId,
    oracle: &Module,
    oracle_entry: FuncId,
) -> DiffReport {
    let mut report = DiffReport::default();
    // (2) Both lowerings place the body's function at FuncId::new(0).
    let thir_fn = match thir_module.function_by_id(thir_entry) {
        Some(f) => f,
        None => {
            report.equal = false;
            report.mode = DiffMode::NotRun;
            report.notes.push("THIR-side module has no FuncId(0) (coverage-only skip)".to_string());
            return report;
        }
    };
    let oracle_fn = match oracle.function_by_id(oracle_entry) {
        Some(f) => f,
        None => {
            report.equal = false;
            report.mode = DiffMode::NotRun;
            report.notes.push("oracle module has no FuncId(0) (coverage-only skip)".to_string());
            return report;
        }
    };

    // (3) Resolve both signatures.
    let thir_sig: &FuncTy = match thir_module.func_type(thir_fn.ty) {
        Some(s) => s,
        None => {
            report.mode = DiffMode::NotRun;
            report.notes.push("THIR-side func type missing (coverage-only skip)".to_string());
            return report;
        }
    };
    let oracle_sig: &FuncTy = match oracle.func_type(oracle_fn.ty) {
        Some(s) => s,
        None => {
            report.mode = DiffMode::NotRun;
            report.notes.push("oracle func type missing (coverage-only skip)".to_string());
            return report;
        }
    };

    // (4) Interpretability gate: non-vararg; scalar int/bool/float params sample normally; Ptr/Unit
    //     params are admitted OPAQUELY when proven never-read in BOTH modules (module docs);
    //     everything else is a precise coverage-only skip. Only scalars count against the cap.
    if thir_sig.is_vararg || oracle_sig.is_vararg {
        report.mode = DiffMode::NotRun;
        report.notes.push("vararg signature is non-interpretable (coverage-only skip)".to_string());
        return report;
    }
    // Trust (Q1): decide the pointer-param INPUT lane before classifying, because three of its
    // conditions are whole-signature (exactly one read pointer, every other param id-free, no
    // pointer return). `None` leaves every note below byte-identical to today.
    let pointer_lane =
        pointer_param_input_lane(thir_module, thir_fn, thir_sig, oracle, oracle_fn, oracle_sig);
    let mut classes: Vec<ParamClass> = Vec::with_capacity(thir_sig.params.len());
    // Trust (aggregate param lane): which of the aggregate admissions this body actually used.
    // ATTRIBUTION ONLY — it is appended to the agreed note's suffix so one measurement sweep can
    // separate four lanes, and it gates nothing. Empty for every body admitted on the
    // pre-existing all-scalar struct rule, which keeps those notes byte-identical.
    let mut aggregate_tags: BTreeSet<&'static str> = BTreeSet::new();
    for (i, t) in thir_sig.params.iter().enumerate() {
        if is_interpretable_scalar(t) {
            classes.push(ParamClass::Scalar);
            continue;
        }
        // Trust (Q1): the materialized-referent lane claims this param before the opacity
        // machinery sees it; the pointee it samples over is carried in `ptr_pointees` below.
        if matches!(&pointer_lane, Some(PointerLane::Scalar { index, .. }) if *index == i) {
            classes.push(ParamClass::PtrTo);
            continue;
        }
        // Trust (Slice B): the same claim one shape up — an AGGREGATE referent. The lane is
        // minted only when `struct_layout_agrees` AND `aggregate_param_admission` both passed
        // two-sidedly, and only when `sig_tys_agree` is not `Ok(false)` (see
        // `pointer_param_input_lane`), so by the time the param is claimed here every gate the
        // by-value aggregate lane applies has already been applied to the REFERENT.
        if matches!(&pointer_lane, Some(PointerLane::Aggregate { index, .. }) if *index == i) {
            classes.push(ParamClass::PtrToAggregate);
            continue;
        }
        // Trust (B3/E6): an eligible FIRST-CLASS enum param samples as EnumDef-valid
        // (variant, payload) values, realized per side at the args site. Eligibility
        // here is THIR-LOCAL only (resolvable def, canonical tag, all-scalar payload
        // fields); cross-side structural identity — variant count, field arity + tys,
        // EFFECTIVE discriminants, canonical tag repr — is proven by sig_tys_agree
        // below BEFORE any sample is built (the mid-B3 spelling-split bodies fail
        // closed there, never sampled). Ineligible enums fall through to the
        // byte-identical non-scalar refusal.
        if let Ty::Enum(eid) = t {
            let eligible = thir_module.enum_def(*eid).is_some_and(|d| {
                !d.variants.is_empty()
                    && d.variants.len() <= MAX_ENUM_SAMPLES
                    && d.canonical_tag_repr().is_some()
                    && d.effective_discriminants().is_some()
                    && d.variants.iter().all(|v| {
                        v.fields
                            .iter()
                            // Trust (B3-2c): a canonical Unit field (the ZST-family
                            // admission respell) samples value-lessly — its
                            // realization is InterpretValueKind::Unit, no raw needed.
                            .all(|f| is_interpretable_scalar(f) || matches!(f, Ty::Unit))
                    })
            });
            if eligible {
                classes.push(ParamClass::Enum);
                continue;
            }
        }
        // Trust (aggregate param lane): an eligible BY-VALUE AGGREGATE param samples as a
        // positional aggregate of its leaves, realized per side at the args site.
        //
        // Trust (B4): `Ty::Tuple` is a SIBLING alternative here, not a second class. Both kinds
        // take `ParamClass::Struct` and its column discipline — see that variant's doc for the
        // two non-compiler-checked `matches!` filters a `ParamClass::Tuple` would have had to
        // be threaded through by hand. The two sides must agree on the KIND (struct/struct or
        // tuple/tuple); a cross-kind pair is refused by `aggregate_param_admission`, because a
        // tuple-vs-struct reclass is exactly the divergence-manufacturing hole this lane's
        // two-sided admission exists to prevent.
        //
        // Unlike the `Enum` arm above, eligibility here is TWO-SIDED and is checked BEFORE
        // the body is admitted, not left to `sig_tys_agree` at step (5). That is deliberate:
        // today every aggregate param returns the byte-identical non-scalar refusal below and
        // therefore NEVER REACHES step (5), so admitting one on a THIR-local test alone would
        // newly expose it to the divergence-publication channel on a SPELLING split — exactly
        // the divergence-manufacturing hole the B3-3 tuple-vs-struct reclass and TEST_P1S3_Foo
        // both came from. Two-sided admission keeps an unmarshallable shape on its existing
        // `not-run`, and admits only shapes whose marshalling is identical on both sides.
        //
        // `aggregate_param_admission` is also STRICTER than `tys_agree`'s struct arm, which
        // compares field COUNT and field TYPES only: it additionally requires the two
        // `StructDef`s to agree on field NAMES, pairwise and recursively. Both producers read
        // that name from the SAME rustc `FieldDef` in source-declaration index order
        // (`trust-thir-lower`'s `register_struct` over `non_enum_variant().fields`;
        // `trust-mir-extract`'s `convert_ty_inner` over `adt_def.all_fields()`), so equality
        // is provable and cheap — and it is what pins FIELD IDENTITY rather than merely field
        // shape. Without it, `MemoryRegion { AllocationId, usize, usize }` would compare equal
        // to itself with its two `usize` fields transposed, and a positional marshalling would
        // then feed the two sides semantically different inputs.
        if let (Ty::Struct(_), Some(ot @ Ty::Struct(_))) | (Ty::Tuple(_), Some(ot @ Ty::Tuple(_))) =
            (t, oracle_sig.params.get(i))
        {
            match aggregate_param_admission(thir_module, oracle, t, ot, thir_sig, oracle_sig) {
                // `lanes` is EMPTY for a param that was already admissible before this batch, so
                // such a body collects no attribution tag and its agreed note stays byte-identical
                // to the one the burn-down ratchet already holds.
                AggregateParamAdmission::Admitted(lanes) => {
                    // Trust (P1 residual): measure the name split this admission accepts. Gates
                    // nothing — see `aggregate_name_split_probe`.
                    if tracing::enabled!(tracing::Level::DEBUG) {
                        aggregate_name_split_probe(thir_module, oracle, t, ot, MAX_STRUCT_DEPTH);
                    }
                    // Trust (B5 stage 1b, reads): a `Ty::Ptr` LEAF is sampled as `NullPtr` —
                    // a placeholder, not a value — so it needs the two-sided never-read proof
                    // its top-level twin gets at `param_never_read` below. Without it, a leaf
                    // the ORACLE reborrows (`Inst::Borrow`, null-checked by the interpreter)
                    // and the PRODUCER merely returns manufactures a divergence about an
                    // input no Rust caller can pass: measured, 7 rows on the first read-side
                    // coroutine sweep (`async fn f(&self) -> &A { self }`, built MIR
                    // `_0 = &(*_3)`). Refused = NotRun with its own note, never a verdict.
                    match (
                        aggregate_ptr_leaf_is_read(thir_fn, i),
                        aggregate_ptr_leaf_is_read(oracle_fn, i),
                    ) {
                        (Ok(false), Ok(false)) => {}
                        (Ok(true), _) | (_, Ok(true)) => {
                            report.mode = DiffMode::NotRun;
                            report.notes.push(format!(
                                "ptr-leaf-read: aggregate param {i} ({t}) has a pointer leaf that \
                                 is READ (dereferenced/reborrowed/passed) on at least one side — \
                                 opaque null sampling refused (coverage-only skip)"
                            ));
                            return report;
                        }
                        (Err(e), _) | (_, Err(e)) => {
                            report.mode = DiffMode::NotRun;
                            report.notes.push(format!(
                                "ptr-leaf-read probe failed for aggregate param {i}: {e} \
                                 (coverage-only skip)"
                            ));
                            return report;
                        }
                    }
                    aggregate_tags.extend(lanes);
                    classes.push(ParamClass::Struct);
                    continue;
                }
                // Conjunct (v), which only a NEWLY-admitted param can reach. Its OWN note, not
                // the verbatim non-scalar one: this body is marshallable and is being held back
                // solely by a whole-signature spelling split, and that population is what the
                // next measurement has to be able to count. Returning here rather than falling
                // through is what keeps a body that has NEVER had a verdict out of step (5)'s
                // divergence channel — while a param that was already admissible does NOT come
                // through here and still publishes its divergence at step (5), unchanged.
                AggregateParamAdmission::SignatureSplit => {
                    report.mode = DiffMode::NotRun;
                    report.notes.push(
                        "aggregate param admissible but signature spelling split; \
                         coverage-only skip"
                            .to_string(),
                    );
                    return report;
                }
                AggregateParamAdmission::Refused => {}
            }
        }
        // Trust (B2-3): a trait-object fat param joins the opacity-provable set — like
        // `Ty::Ptr` it is admitted ONLY under the two-sided `param_never_read` proof
        // below, preserving the Opaque-sampleability the class had when `&dyn` was
        // spelled thin. Slice/Str fat params stay non-interpretable (their values are
        // READ by the slice lanes; sampling them needs the B4 memory model).
        if !matches!(t, Ty::Ptr | Ty::Unit | Ty::FatPtr(trust_ir::FatPtrKind::TraitObject { .. })) {
            report.mode = DiffMode::NotRun;
            report.notes.push(
                "non-scalar parameter type is non-interpretable (coverage-only skip)".to_string(),
            );
            return report;
        }
        // Fail-closed opacity proof, on BOTH sides.
        match (param_never_read(thir_fn, i), param_never_read(oracle_fn, i)) {
            (Ok(true), Ok(true)) => classes.push(ParamClass::Opaque),
            (Ok(false), _) | (_, Ok(false)) => {
                report.mode = DiffMode::NotRun;
                // Trust (Q1 / Slice B): the referent is a whole AGGREGATE whose byte layout was
                // proven to agree across both sides, so the body is materializable — but the
                // sampler DECLINED it, for one of exactly two reasons, and each gets its own
                // note. A held-back population that shares one note is a population nobody can
                // rank; a held-back population with NO note falls into `clean-skip-other`, which
                // is the anonymous-catch-all failure this project has already paid for once.
                //
                // BOTH notes deliberately still carry the phrase `layout-agreeing AGGREGATE
                // referent`, which is the classifier key for `clean-skip-ptr-pointee-aggregate`.
                // That is what makes the sweep's own gate readable WITHOUT a scorecard edit: the
                // class falls from its pre-lane count to exactly the number of declines, so the
                // delta is the sampler's yield and the residue is still in a NAMED class. Each
                // note additionally LEADS with a distinct token so a finer rule can split them
                // later — leading, not trailing, because the artifact stores notes truncated to
                // 160 characters and a marker past that offset is unreadable offline.
                if matches!(
                    &pointer_lane,
                    Some(PointerLane::AggregateCeiling { index }) if *index == i
                ) {
                    report.notes.push(format!(
                        "ptr-aggregate-unmarshallable: param {i} ({t}) is READ through a \
                         layout-agreeing AGGREGATE referent, but the referent is not exactly \
                         marshallable (leaf/depth/name/placeholder admission refused); \
                         coverage-only skip"
                    ));
                    return report;
                }
                if matches!(
                    &pointer_lane,
                    Some(PointerLane::AggregateSignatureSplit { index }) if *index == i
                ) {
                    report.notes.push(format!(
                        "ptr-aggregate-sig-split: param {i} ({t}) is READ through a \
                         layout-agreeing AGGREGATE referent and IS marshallable, but the two \
                         signatures are a spelling split (sig_tys_agree Ok(false)); withheld so a \
                         body that has never reached step (5) cannot publish a divergence; \
                         coverage-only skip"
                    ));
                    return report;
                }
                report.notes.push(format!(
                    "param {i} ({t}) is READ (dereferenced/used) — opaque sampling refused \
                     (coverage-only skip)"
                ));
                return report;
            }
            (Err(e), _) | (_, Err(e)) => {
                report.mode = DiffMode::NotRun;
                report.notes.push(format!("opacity scan failed ({e}); coverage-only skip"));
                return report;
            }
        }
    }
    // Trust (B3/E6): enum columns enter the product, so they count against the cap
    // (the note string stays verbatim — it is a classifier key).
    // Trust (aggregate param lane): struct columns do too, for the same reason.
    // Trust (Q1): so does a materialized-referent column — it is a scalar column over the POINTEE.
    // Trust (Slice B): AND SO DOES `PtrToAggregate`. This used to be a `matches!` — one of the
    // two filters `ParamClass::Struct`'s doc names as NOT COMPILER-CHECKED, where adding a class
    // without adding it here does not fail to build, it silently UNDERCOUNTS and so relaxes
    // `MAX_PARAMS`. It is now `consumes_sample_column`, an exhaustive `match`, shared with
    // `build_side_args`' `expected_columns`: the next class to be added fails to COMPILE at one
    // site instead of desynchronizing two.
    let scalar_params = classes.iter().filter(|c| consumes_sample_column(c)).count();
    if scalar_params > MAX_PARAMS {
        report.mode = DiffMode::NotRun;
        report.notes.push(format!(
            "scalar param count {} exceeds differential cap {} (coverage-only skip)",
            scalar_params, MAX_PARAMS
        ));
        return report;
    }

    // (5) Interface divergence: the two front-ends must agree on the signature. Comparison is
    //     STRUCTURAL, not id-wise: each module numbers its own `StructId`/`TyId`/`FuncTyId`
    //     spaces (the producer's ids are first-seen positional; the oracle's are
    //     registration-order), so `Ty::Struct(0) == Ty::Struct(0)` raw-id equality would be
    //     both unsound (equal ids, different defs → false agreement) and incomplete (different
    //     ids, same def → false divergence). `tys_agree` resolves table-indexed types through
    //     their OWN module's tables and compares the resolved field-type shape, failing CLOSED
    //     (`Err` → coverage-only skip, never a silent verdict) on an unresolvable id, an
    //     unbounded nesting (recursive defs), or any table-indexed variant it does not model.
    match sig_tys_agree(&thir_module, &oracle, thir_sig, oracle_sig) {
        Ok(true) => {}
        Ok(false) => {
            // Trust (B3-3, RETIRED 2026-07-24): the legacy tuple-vs-struct
            // dual-spelling reclass lived here. B3-2c deleted the producer's
            // legacy `(I64-tag, payload)` enum model, so the split it papered
            // over cannot occur; a one-cycle LOUD tripwire then confirmed it
            // on the 9014-body burn-in (postbuild-b33-final: ZERO hits, and
            // the 7 tuple-vs-struct divergences of the waveYDCH baseline are
            // gone). Every signature mismatch is now published as a real
            // divergence — no enum-shaped exemption remains.
            // Trust (wave-DS, wave-full-0901b): a disagreement attributable ENTIRELY to a
            // producer-side DEGRADED spelling — a `Ty::Unit` placeholder standing where the
            // oracle resolves a real type (the RMW/opaque field degradation, e.g. the
            // `NonNull<dyn Fn> { () }` chain inside `Option<Box<dyn Fn>>`) — is a
            // comparability LIMITATION, not a semantic divergence: the producer chose an
            // opaque spelling and the comparator cannot equate what one side declines to
            // spell. Published on the Err channel's coverage-only skip, exactly like an
            // unresolvable id. Asymmetric on purpose: an oracle-side Unit against a producer
            // real type is NOT a producer degradation and stays a published divergence.
            // Measured: the 113793 `next` signature row — the LAST wave-full-0901 divergence
            // — printed IDENTICAL sigs (`[Ptr]->[Enum(0)]` both sides) because the
            // disagreement was three tables deep in the degraded payload chain.
            if sig_tys_agree_modulo_degraded_unit(&thir_module, &oracle, thir_sig, oracle_sig)
                .unwrap_or(false)
            {
                report.equal = false;
                report.mode = DiffMode::NotRun;
                report.notes.push(
                    "signature comparability failure (producer-degraded spelling); \
                     coverage-only skip (fail-closed)"
                        .to_string(),
                );
                return report;
            }
            report.equal = false;
            report.mode = DiffMode::MirOracle;
            report.notes.push(format!(
                "signature divergence: THIR {:?}->{:?} vs MIR {:?}->{:?}",
                thir_sig.params, thir_sig.returns, oracle_sig.params, oracle_sig.returns
            ));
            return report;
        }
        Err(why) => {
            report.equal = false;
            report.mode = DiffMode::NotRun;
            report.notes.push(format!(
                "signature comparability failure ({why}); coverage-only skip (fail-closed)"
            ));
            return report;
        }
    }

    // (5.5) Trust (wave-DA): THE ADT-INTERIOR BYTE-ARITHMETIC GATE. A body that walks an ADT
    //       interior by a literal rustc byte offset must not be interpreted, because the
    //       interpreter derives its own ADT image rather than reading that offset — see
    //       `first_adt_interior_byte_arithmetic` for the two consumer rules and why neither is a
    //       claim of rustc parity. Interpreting such a body compares two addresses that were
    //       derived by different rules and reports the result as a verdict.
    //
    //       This is where the invariant "no verdict in this programme has ever been minted from
    //       an executed ADT-interior byte offset" stops being a measurement and becomes a gate.
    //       Placed LAST among the pre-sampling guards on purpose: every body already skipped for
    //       an earlier reason keeps its existing note verbatim (the notes are the burn-down
    //       ratchet's classifier keys), so this fires only on a body that would OTHERWISE HAVE
    //       RUN. Measured at the time of landing: of the 1,270 clean-kernel bodies that emit this
    //       shape, ZERO reach this point at either opt level — every one is held by a gate that
    //       exists for some other reason (1,256 by the cross-module-call guard, 6 by the
    //       pointer-parameter gate, 8 by an oracle incapacity) — so it costs no verdict today and
    //       refuses the class the moment one of those reasons is relaxed.
    //
    //       SCOPED to the entry's REACHABLE CLOSURE, and that scoping is load-bearing rather than
    //       tidy: the whole-module spelling was measured withdrawing two real `seam: agreed`
    //       verdicts over a byte walk in `cache::TypeCheckCache::stats`, which neither entry can
    //       reach. See `first_adt_interior_byte_arithmetic`.
    //
    //       BOTH sides are checked. The oracle does not emit this shape today (the bridge's five
    //       `Inst::GEP` sites all carry a typed `pointee_ty`), so the second conjunct is free; it
    //       is present because the hazard is a property of the SHAPE, not of which front-end
    //       produced it.
    //
    //       FREEZE, as scoped: this edit makes the oracle ACCEPT STRICTLY LESS — it can only turn
    //       a would-be sample into `NotRun`, never a `NotRun` into an `Agreed`. That is the
    //       permitted direction.
    let adt_byte_walk = first_adt_interior_byte_arithmetic(thir_module, thir_entry)
        .map(|why| format!("THIR side: {why}"))
        .or_else(|| {
            first_adt_interior_byte_arithmetic(oracle, oracle_entry)
                .map(|why| format!("MIR oracle side: {why}"))
        });
    if let Some(why) = adt_byte_walk {
        report.equal = false;
        report.mode = DiffMode::NotRun;
        report.notes.push(format!(
            "ADT-interior literal byte arithmetic ({why}); the interpreter derives its own ADT \
             layout and would execute an offset it did not derive; coverage-only skip"
        ));
        return report;
    }

    // (6) Sample space: cross-product of per-SCALAR-param boundary+mid values (one empty
    //     tuple when every param is opaque or there are none); opaque params contribute one
    //     placeholder each, outside the product.
    // Trust (B3/E6): enum params contribute an INDEX-ENCODED column (0..samples.len())
    // over a parallel abstract-samples table — the i128 product machinery stays
    // untouched; realization happens per side at the args site.
    let mut enum_samples: Vec<Option<Vec<(usize, Vec<i128>)>>> = vec![None; thir_sig.params.len()];
    // Trust (aggregate param lane): the struct twin of `enum_samples` — one abstract sample is
    // the FLAT depth-first list of scalar-leaf raws, side-portable because the two `StructDef`s
    // were proven to agree (shape AND field names) at the admission gate.
    //
    // Trust (Slice B): SHARED with `ParamClass::PtrToAggregate`, whose payload is the identical
    // flat leaf list realized through the identical `realize_aggregate_arg`. The difference is
    // only WHICH type the leaves describe — the param type for `Struct`, the recovered POINTEE
    // for `PtrToAggregate` — and that difference is resolved here, once, when the table is
    // filled, so every consumer downstream sees one uniform table.
    let mut struct_samples: Vec<Option<Vec<Vec<i128>>>> = vec![None; thir_sig.params.len()];
    // Trust (Q1): the recovered referent type per param — the pointer twin of `enum_samples`.
    // `Some` exactly at the `ParamClass::PtrTo` / `ParamClass::PtrToAggregate` index; the
    // wrapper's signature and the args site both read the sampled column at the POINTEE type,
    // never at `Ty::Ptr`.
    //
    // Trust (Slice B): the THIR side's spelling is stored, and using it to build the ABSTRACT
    // samples is sound for both sides because `aggregate_param_admission`'s conjunct (i) proved
    // the two sides' leaf sequences EQUAL. Each side then realizes those raws against its OWN
    // module (`build_side_args`), which is the same discipline the by-value aggregate lane runs.
    let mut ptr_pointees: Vec<Option<Ty>> = vec![None; thir_sig.params.len()];
    match &pointer_lane {
        Some(PointerLane::Scalar { index, pointee }) => {
            ptr_pointees[*index] = Some(pointee.clone());
        }
        Some(PointerLane::Aggregate { index, pointee_a, .. }) => {
            ptr_pointees[*index] = Some(pointee_a.clone());
        }
        Some(PointerLane::AggregateCeiling { .. })
        | Some(PointerLane::AggregateSignatureSplit { .. })
        | None => {}
    }
    let mut per_param: Vec<Vec<i128>> = Vec::new();
    for (i, (t, c)) in thir_sig.params.iter().zip(classes.iter()).enumerate() {
        match c {
            ParamClass::Scalar => per_param.push(sample_values(t)),
            ParamClass::PtrTo => {
                let Some(pointee) = ptr_pointees[i].clone() else {
                    report.mode = DiffMode::NotRun;
                    report.notes.push(
                        "could not build sample argument (coverage-only skip): recovered \
                         referent type unavailable"
                            .to_string(),
                    );
                    return report;
                };
                per_param.push(sample_values(&pointee));
            }
            // Trust (Slice B): THE POSITION THAT DECIDES WHETHER THIS LANE MEASURES ANYTHING.
            //
            // `sample_values(&Ty::Struct(_))` is an EMPTY vec — it handles `Ty::Ptr`, `Ty::Bool`,
            // the floats and `Ty::Char`, then falls to `int_shape`, which answers `None`. An
            // empty column makes `CartesianProduct::new` set `finished` immediately, the sample
            // loop never runs, `value_samples` stays 0, and step (8) returns `NotRun` with a note
            // no `classify_note` rule matches — i.e. +0 Agreed AND the whole population silently
            // relocated into the anonymous `clean-skip-other`. So the column here is INDEX-ENCODED
            // over `aggregate_abstract_samples`, exactly like `ParamClass::Struct`, and the type
            // it is taken over is the recovered POINTEE, never the `Ty::Ptr` param type (which
            // `aggregate_component_tys` refuses, producing the same empty-column death one step
            // earlier).
            ParamClass::PtrToAggregate => {
                let Some(pointee) = ptr_pointees[i].clone() else {
                    report.mode = DiffMode::NotRun;
                    report.notes.push(
                        "could not build sample argument (coverage-only skip): recovered \
                         aggregate referent type unavailable"
                            .to_string(),
                    );
                    return report;
                };
                let Some(samples) = aggregate_abstract_samples(thir_module, &pointee) else {
                    report.mode = DiffMode::NotRun;
                    report.notes.push(
                        "could not build sample argument (coverage-only skip): aggregate \
                         referent sample description unavailable"
                            .to_string(),
                    );
                    return report;
                };
                per_param.push((0..samples.len() as i128).collect());
                struct_samples[i] = Some(samples);
            }
            ParamClass::Struct => {
                // Trust (B4): dispatched on the `Ty`, so `Ty::Struct` and `Ty::Tuple` share the
                // one column. Trust (B3): a FIELDLESS aggregate legitimately answers with a
                // single ZERO-LEAF sample, so this is `Some(vec![vec![]])` and NOT `None` — a
                // `None` here would land the body on "struct sample description unavailable",
                // which is a coverage skip that reads like a regression.
                let samples = aggregate_abstract_samples(thir_module, t);
                let Some(samples) = samples else {
                    report.mode = DiffMode::NotRun;
                    report.notes.push(
                        "could not build sample argument (coverage-only skip): struct sample \
                         description unavailable"
                            .to_string(),
                    );
                    return report;
                };
                per_param.push((0..samples.len() as i128).collect());
                struct_samples[i] = Some(samples);
            }
            ParamClass::Enum => {
                let samples = (|| {
                    let Ty::Enum(eid) = t else { return None };
                    enum_abstract_samples(thir_module.enum_def(*eid)?)
                })();
                let Some(samples) = samples else {
                    report.mode = DiffMode::NotRun;
                    report.notes.push(
                        "could not build sample argument (coverage-only skip): enum sample \
                         description unavailable"
                            .to_string(),
                    );
                    return report;
                };
                per_param.push((0..samples.len() as i128).collect());
                enum_samples[i] = Some(samples);
            }
            ParamClass::Opaque => {}
        }
    }
    // (7) Differential interpretation: run both modules on every sample, compare return vectors.
    //
    // Asymmetry is deliberate. The MIR-side is the TRUSTED oracle; the THIR-side is UNDER TEST. So:
    //   * If only the ORACLE errors with an *incapacity* code (e.g. a SignatureMismatch from the
    //     MIR-bridge typing a constant at the wrong width — a known oracle limitation), that is NOT
    //     evidence the THIR lowering is wrong. We downgrade to coverage-only (`NotRun`), never a
    //     divergence verdict. The oracle erroring with a genuine *trap* (`Panic`/`UB`) while the
    //     THIR side produced a value IS a real divergence (the THIR failed to trap).
    //   * If only the THIR side errors, it is a verdict against THIR ONLY for THIR-internal defect
    //     codes (malformed IR, signature/type errors, traps); infra limits (fuel/unsupported) are
    //     coverage-only.
    //   * `Err`/`Err` is an agreement only when both reproduce the *same genuine trap*.
    // `Agreed` further requires at least one `(Ok, Ok)` value sample, so a value-returning function
    // can never pass vacuously on trap-only agreement.
    // Trust (Q1): materialize the referent. Both sides get an identically-shaped wrapper that
    // allocates the pointee, stores the sampled value, and calls the entry with the slot; the
    // sample column is over the POINTEE type, so `exec_sig` (not the entry signature) is what the
    // args site marshals against.
    //
    // `first_unmodeled_observation` below is deliberately NOT re-pointed at the wrapper — it stays
    // on `thir_entry`/`oracle_entry`. `wrappers_agree` is what pays for that: the wrapper's own
    // memory effects go uncompared, which is sound only because the two wrappers are the same
    // program, and that is ASSERTED here rather than argued.
    //
    // Trust (Slice B): THE REFERENT IS TWO-SIDED. `pointee_a` builds the THIR wrapper and
    // `pointee_b` builds the ORACLE's — never one shared value. For `PointerLane::Scalar` the
    // two ARE the same `Ty` (the lane requires `a == b`), so the pair spelling is byte-identical
    // in behaviour there; for an aggregate they are two module-local `StructId`s naming the same
    // proven layout in two different tables, and feeding one side's id to the other is the
    // manufactured-agreement trap the module docs name. The proven pair is handed to
    // `wrappers_agree` so its exemption is keyed on exactly these two types and no others.
    let mut wrapped: Option<(Module, FuncId, FuncTy, Module, FuncId, FuncTy)> = None;
    let referent: Option<(usize, &Ty, &Ty)> = match &pointer_lane {
        Some(PointerLane::Scalar { index, pointee }) => Some((*index, pointee, pointee)),
        Some(PointerLane::Aggregate { index, pointee_a, pointee_b }) => {
            Some((*index, pointee_a, pointee_b))
        }
        Some(PointerLane::AggregateCeiling { .. })
        | Some(PointerLane::AggregateSignatureSplit { .. })
        | None => None,
    };
    if let Some((index, pointee_a, pointee_b)) = referent {
        let built = build_pointee_wrapper(thir_module, thir_entry, thir_sig, index, pointee_a)
            .zip(build_pointee_wrapper(oracle, oracle_entry, oracle_sig, index, pointee_b));
        let Some(((tm, tf, ts), (om, of, os))) = built else {
            report.mode = DiffMode::NotRun;
            report.notes.push(
                "could not build sample argument (coverage-only skip): referent wrapper \
                 construction failed"
                    .to_string(),
            );
            return report;
        };
        // The referent exemption is passed ONLY for the aggregate lane. The scalar lane keeps
        // exact structural equality end to end — `None` here is what makes that a checkable
        // statement rather than a claim, and `wrappers_agree_across_identically_shaped_sides`
        // (which passes `None` on both of its assertions) pins it.
        let exemption = match &pointer_lane {
            Some(PointerLane::Aggregate { .. }) => Some((index, pointee_a, pointee_b)),
            _ => None,
        };
        // Scoped so the two wrapper borrows END before the modules move into `wrapped` below.
        let agreement = match (tm.function_by_id(tf), om.function_by_id(of)) {
            (Some(wa), Some(wb)) => wrappers_agree(wa, thir_entry, wb, oracle_entry, exemption),
            _ => Err("a wrapper is unresolvable after construction".to_string()),
        };
        if let Err(why) = agreement {
            report.mode = DiffMode::NotRun;
            report.notes.push(format!(
                "returns/traps not sampled: the two materialized-referent wrappers are not the \
                 same program ({why}); the uncompared-wrapper argument does not hold \
                 (coverage-only skip)"
            ));
            return report;
        }
        wrapped = Some((tm, tf, ts, om, of, os));
    }
    let (thir_exec_module, thir_exec_entry, thir_exec_sig) = match &wrapped {
        Some((m, f, s, ..)) => (m, *f, s),
        None => (thir_module, thir_entry, thir_sig),
    };
    let (oracle_exec_module, oracle_exec_entry, oracle_exec_sig) = match &wrapped {
        Some((.., m, f, s)) => (m, *f, s),
        None => (oracle, oracle_entry, oracle_sig),
    };

    let thir_interp = Interpreter::with_module(thir_exec_module);
    let oracle_interp = Interpreter::with_module(oracle_exec_module);
    let mut checked = 0usize;
    let mut value_samples = 0usize;
    // A comparison gap is coverage-only, but it must never hide a concrete mismatch in a later
    // return position or sampled execution. Retain the first diagnostic and continue searching;
    // only downgrade after the complete sample stream has produced no negative witness.
    let mut return_comparability_gap: Option<(Vec<i128>, String)> = None;

    // Stream the cartesian product. The previous eager helper retained up to
    // 4096 separately allocated tuples per body and repeatedly cloned every
    // prefix while constructing them; the interpreter consumes one tuple at a
    // time, so that memory and copying had no semantic purpose.
    for tuple in CartesianProduct::new(&per_param) {
        // Positional arg assembly: scalars consume the tuple left-to-right; opaque params
        // get their (never-evaluated, type-correct) placeholder.
        // Trust (B3/E6): args are constructed PER SIDE from that side's OWN module +
        // signature — a table-indexed param ty (`Ty::Enum(id)` today; FatPtr(Slice)
        // when its opacity lands) carries a module-LOCAL id, and the interpreter's
        // entry check is exact Ty equality. A one-sided construction failure must
        // never reach execute_func: a mistyped THIR-side sample would surface as a
        // THIR-defect error code and MINT A FALSE DIVERGENCE via the (Err, Ok) arm.
        // Trust (Q1): marshalled against the EXEC signature — for a materialized-referent body
        // that is the wrapper's, whose param `i` is the pointee type, so the `PtrTo` column
        // realizes as an ordinary scalar and the wrapper turns it into a pointer.
        let thir_args = build_side_args(
            thir_exec_module,
            thir_exec_sig,
            &classes,
            &enum_samples,
            &struct_samples,
            &tuple,
        );
        let oracle_args = build_side_args(
            oracle_exec_module,
            oracle_exec_sig,
            &classes,
            &enum_samples,
            &struct_samples,
            &tuple,
        );
        let (args_thir, args_oracle) = match (thir_args, oracle_args) {
            (Ok(a), Ok(b)) => (a, b),
            (Err(why), _) | (_, Err(why)) => {
                report.mode = DiffMode::NotRun;
                report
                    .notes
                    .push(format!("could not build sample argument (coverage-only skip): {why}"));
                return report;
            }
        };
        let decoded =
            decoded_enum_sample_suffix(&thir_module, thir_sig, &classes, &enum_samples, &tuple);

        let thir_out = thir_interp.execute_func(thir_exec_entry, args_thir);
        let oracle_out = oracle_interp.execute_func(oracle_exec_entry, args_oracle);

        match (thir_out, oracle_out) {
            (Ok(a), Ok(b)) => {
                checked += 1;
                value_samples += 1;
                // Trust: STRUCTURAL return comparison (same rationale as the step-(5)
                // signature comparison): a returned value's `ty` may be `Ty::Struct`/
                // `Ty::Array` under each module's own id numbering, so raw `InterpretValue`
                // equality would manufacture false verdicts either way. Kinds are compared
                // recursively (aggregates element-wise), types via `tys_agree`; an
                // unresolvable/unmodeled shape fails CLOSED as a coverage-only skip.
                match returns_agree(&thir_module, &oracle, &a.returns, &b.returns) {
                    Ok(true) => {}
                    Ok(false) => {
                        // Trust (divergences D5/D6 root-fix, wave-full-0831): a disagreement
                        // ONLY in MATERIALIZED-POINTER lanes is NOT a genuine negative
                        // witness — `InterpretPointer { allocation, .. }` numbers are
                        // per-execution artifacts (globals materialize lazily, first-touch
                        // order), so two sides returning the SAME str constant can differ as
                        // `allocation 0` vs `allocation 1` (measured twice: `action_to_str`,
                        // `match_bool`). This is the exact SYMMETRIC completion of the
                        // provenance TAIL GATE: that gate already degrades a would-be-GREEN
                        // on a body that materializes module-global provenance (closing the
                        // numbering-coincidence false-agree); this arm degrades the would-be
                        // false-DIVERGENCE the same way. A disagreement with any
                        // NON-pointer lane differing stays the genuine `MirOracle` witness
                        // it always was.
                        if disagreement_only_in_materialized_ptrs(&a.returns, &b.returns) {
                            if return_comparability_gap.is_none() {
                                return_comparability_gap = Some((
                                    tuple.clone(),
                                    "materialized-pointer identity across independently-\
                                     numbered executions is not adjudicable (allocation ids \
                                     are per-execution artifacts)"
                                        .to_string(),
                                ));
                            }
                        } else {
                            report.equal = false;
                            report.mode = DiffMode::MirOracle;
                            report.samples_checked = checked;
                            report.notes.push(format!(
                                "DIVERGENCE on input {:?}{decoded}: THIR returned {:?}, MIR oracle returned {:?}",
                                tuple, a.returns, b.returns
                            ));
                            return report;
                        }
                    }
                    Err(why) => {
                        if return_comparability_gap.is_none() {
                            return_comparability_gap = Some((tuple.clone(), why));
                        }
                    }
                }
            }
            // Both errored: a genuine agreement ONLY when both reproduce the same trap.
            (Err(ea), Err(eb)) => {
                if ea.code == eb.code && is_trap(ea.code) {
                    checked += 1;
                } else if errerr_thir_defect_divergence(ea.code, eb.code) {
                    // The THIR side errored with a genuine LOWERING DEFECT (malformed
                    // IR / type / signature error — see `is_thir_defect`) while the
                    // oracle's error is merely an infra limit (e.g. `OutOfFuel`,
                    // `Unsupported*`). Without this arm the differing codes fall through
                    // to the `NotRun` coverage-only skip below, HIDING a real THIR
                    // defect behind the oracle's incidental incapacity. Report it as a
                    // verdict against THIR, mirroring the `(Err, Ok)` MirOracle arm.
                    report.equal = false;
                    report.mode = DiffMode::MirOracle;
                    report.samples_checked = checked;
                    report.notes.push(format!(
                        "DIVERGENCE on input {:?}{decoded}: THIR errored with a lowering defect ({}) \
                         while the MIR oracle only hit an infra limit ({}) — a genuine THIR \
                         defect masked by the oracle's incapacity, NOT a trap agreement",
                        tuple, ea, eb
                    ));
                    return report;
                } else {
                    report.equal = false;
                    report.mode = DiffMode::NotRun;
                    report.notes.push(format!(
                        "both sides errored non-trappily on input {:?} (THIR {}, oracle {}); \
                         coverage-only skip",
                        tuple, ea, eb
                    ));
                    return report;
                }
            }
            // Only the ORACLE errored. Incapacity ⇒ coverage-only; a real trap ⇒ THIR failed to trap.
            (Ok(a), Err(eb)) => {
                if is_trap(eb.code) {
                    report.equal = false;
                    report.mode = DiffMode::MirOracle;
                    report.samples_checked = checked;
                    report.notes.push(format!(
                        "DIVERGENCE on input {:?}{decoded}: THIR returned {:?} but MIR oracle proved a trap ({})",
                        tuple, a.returns, eb
                    ));
                    return report;
                }
                report.equal = false;
                report.mode = DiffMode::NotRun;
                report.notes.push(format!(
                    "MIR oracle could not interpret (incapacity {}); coverage-only skip — \
                     NOT a THIR divergence",
                    eb
                ));
                return report;
            }
            // Only the THIR side errored. A verdict against THIR only for THIR-internal defects.
            (Err(ea), Ok(b)) => {
                if is_thir_defect(ea.code) {
                    report.equal = false;
                    report.mode = DiffMode::MirOracle;
                    report.samples_checked = checked;
                    report.notes.push(format!(
                        "DIVERGENCE on input {:?}{decoded}: THIR errored ({}) but MIR oracle returned {:?}",
                        tuple, ea, b.returns
                    ));
                    return report;
                }
                report.equal = false;
                report.mode = DiffMode::NotRun;
                report
                    .notes
                    .push(format!("THIR side hit an infra limit ({}); coverage-only skip", ea));
                return report;
            }
        }
    }

    // (8) Agreement requires at least one real value sample (never a vacuous trap-only pass).
    if value_samples == 0 {
        report.equal = false;
        report.mode = DiffMode::NotRun;
        report.notes.push(format!(
            "no value samples interpretable ({} trap-agreement sample(s)); coverage-only skip",
            checked
        ));
        return report;
    }

    if let Some((tuple, why)) = return_comparability_gap {
        report.equal = false;
        report.mode = DiffMode::NotRun;
        report.samples_checked = checked;
        report.notes.push(format!(
            "return comparability failure on input {:?} ({why}); coverage-only skip \
             (fail-closed after checking every sample for a concrete divergence)",
            tuple
        ));
        return report;
    }

    // Trust: a return/trap match proves agreement only for the part of execution represented by
    // `InterpretOutcome`. Preserve every hard `MirOracle` return above, but never mint the green
    // tail when either entry's direct-call closure can mutate or expose discarded state. This is
    // deliberately a TAIL gate: an effectful pair whose returned values differ still supplies a
    // genuine negative witness and remains `MirOracle`; only an otherwise-green claim degrades to
    // the coverage-only state.
    //
    // Trust (vtable slice 7): the walk takes the PAIRED promoted-global admission set —
    // pairing is by NAME over the `__trust_promoted_*`/`__trust_bytes_*` mints with
    // bit-exact initializer-content equality; see `paired_admitted_promoted_globals` for
    // why each conjunct is load-bearing.
    //
    // Trust (vtable slice 13): the call-free bound (`closure_contains_call`) is RETIRED.
    // It existed because a callee could return the admitted address as an un-audited
    // ordinary call result (`ptr_to_int(callee())` would then compare synthetic addresses
    // as a verdict). That hole is now closed INSIDE the audit instead of by disabling
    // admission wholesale: a tracked address may cross a direct call boundary only into a
    // linked bodyful callee whose seeded-parameter audit passes and REFUSES return
    // positions (`seeded_param_uses_modeled`); call results never join the tracked set;
    // and a multi-function walk refuses any tracked address in a Return position and any
    // second distinct admitted name per side (`first_unmodeled_observation`'s post-walk
    // constraints). Every single-function walk behaves byte-identically to slice 7.
    let paired: BTreeSet<String> = paired_admitted_promoted_globals(thir_module, oracle);
    let thir_walk = first_unmodeled_observation(thir_module, thir_entry, &paired);
    let mut oracle_admitted: BTreeSet<String> = BTreeSet::new();
    let mut observation_gap = thir_walk.gap.map(|why| format!("THIR side: {why}"));
    if observation_gap.is_none() {
        let oracle_walk = first_unmodeled_observation(oracle, oracle_entry, &paired);
        observation_gap = oracle_walk.gap.map(|why| format!("MIR oracle side: {why}"));
        oracle_admitted = oracle_walk.admitted;
    }
    // Trust (vtable slice 7): if the two sides each admitted a paired global but DIFFERENT
    // ones, the "same immutable object" argument above does not connect them — a returned
    // address on one side would be compared against a different object's address on the
    // other. Held fail-closed rather than assumed (set-shaped since slice 13; each side's
    // walk already refuses >1 distinct admitted name, so this compares two singletons).
    if observation_gap.is_none()
        && !thir_walk.admitted.is_empty()
        && !oracle_admitted.is_empty()
        && thir_walk.admitted != oracle_admitted
    {
        observation_gap = Some(format!(
            "the two sides admitted different paired module globals ({:?} vs {:?})",
            thir_walk.admitted, oracle_admitted
        ));
    }
    if let Some(why) = observation_gap {
        report.equal = false;
        report.mode = DiffMode::NotRun;
        report.samples_checked = checked;
        report.notes.push(format!(
            "returns/traps matched on {checked} sampled execution(s), but {why}; \
             observable-effect comparison is not modeled (coverage-only skip)"
        ));
        return report;
    }

    report.equal = true;
    report.mode = DiffMode::Agreed;
    report.samples_checked = checked;
    let opaque_params = classes.iter().filter(|c| **c == ParamClass::Opaque).count();
    // Trust (aggregate param lane): ATTRIBUTION SUFFIX. One measurement sweep pays for four
    // admissions (fieldless, ptr-leaf, tuple, cap widening) and a bare agreed count cannot say
    // which one bought which body. Tags are emitted in `BTreeSet` order and joined with `+` when
    // a body used more than one.
    //
    // The PREFIX `"THIR-trust-ir == MIR-trust-ir on"` is untouched — the notes are the burn-down
    // ratchet's keys — and the suffix is appended INSIDE the existing parenthetical only when at
    // least one tag applies. A body admitted on the pre-existing all-scalar struct rule collects
    // no tags, so its note is byte-identical to the one already in the ratchet.
    let aggregate_suffix = if aggregate_tags.is_empty() {
        String::new()
    } else {
        format!(
            "; aggregate param admitted [{}]",
            aggregate_tags.iter().copied().collect::<Vec<_>>().join("+")
        )
    };
    report.notes.push(if opaque_params > 0 {
        format!(
            "THIR-trust-ir == MIR-trust-ir on {} sampled input(s) (differential \
             interpretation; {} proven-never-read opaque param(s) as placeholders{})",
            checked, opaque_params, aggregate_suffix
        )
    } else {
        format!(
            "THIR-trust-ir == MIR-trust-ir on {} sampled input(s) (differential \
             interpretation{})",
            checked, aggregate_suffix
        )
    });
    report
}


/// Trust (Q1): the SYNTHESIZED WRAPPER — `Alloca` the referent, `Store` the sampled value, `Call`
/// the entry with the slot, return whatever the entry returned.
///
/// Returns the mutated module (the wrapper appended), the wrapper's `FuncId`, and its signature.
/// The signature MUST be registered with `Module::add_func_type`: the interpreter resolves
/// `Function::ty` through the module's func-type table on every call and hard-errors
/// `signature_mismatch` on an unregistered id, so an unregistered wrapper would fail every body
/// rather than none.
///
/// The wrapper is built from the ENTRY SIGNATURE, the lane index, and `pointee` — and `pointee`
/// MUST be the referent recovered on **this** side's module. For `PointerLane::Scalar` the two
/// sides' pointees are the same `Ty` by admission (`a == b`), so the distinction is invisible
/// there; for `PointerLane::Aggregate` it is `Ty::Struct(id)` with a MODULE-LOCAL id and passing
/// the other side's value builds a wrapper that allocates, stores and loads under a struct
/// definition this module does not have — while simultaneously making `wrappers_agree` pass
/// vacuously. See the module docs, "THE TRAP THIS SHAPE INVITES".
///
/// Every OTHER position in the wrapper is id-free (`pointer_lane_param_ok` guarantees the
/// pass-through types are), so the referent is the sole position `wrappers_agree` cannot compare
/// by plain equality.
fn build_pointee_wrapper(
    module: &Module,
    entry: FuncId,
    sig: &FuncTy,
    index: usize,
    pointee: &Ty,
) -> Option<(Module, FuncId, FuncTy)> {
    let mut wrapper_sig = sig.clone();
    *wrapper_sig.params.get_mut(index)? = pointee.clone();

    let mut out = module.clone();
    // Trust (trust-ir D1b): the table doors refuse instead of panicking; `out` is a copy, so a
    // refusal drops it and the lane declines exactly as every other `None` here.
    let ty_id = out.add_func_type(wrapper_sig.clone()).ok()?;
    // The wrapper's id must be PROVABLY ABSENT from this module, and `functions.len()` does not
    // establish that for an arbitrary Trust-IR input. Current producer modules are dense after
    // assembly, but this helper also operates on independently supplied modules, whose ids may be
    // sparse: a module holding the body at 0 and one callee at 2 has `len() == 2`, and a wrapper
    // minted at 2 would collide — `function_by_id(2)` resolves index-first and could dispatch the
    // callee's own call to the wrapper. One past the observed maximum is absent for both dense and
    // sparse modules; `checked_add` fails the lane closed at the top of the id space.
    let func_id = FuncId::new(match out.functions.iter().map(|f| f.id.index()).max() {
        Some(max) => max.checked_add(1)?,
        None => 0,
    });
    // Deterministic, module-independent value numbering: params 0..n, then the slot, then the
    // call results. Both sides run this identical arithmetic, so the ids match by construction.
    let param_ids: Vec<ValueId> =
        (0..wrapper_sig.params.len()).map(|i| ValueId::new(u32::try_from(i).unwrap())).collect();
    let slot = ValueId::new(u32::try_from(wrapper_sig.params.len()).ok()?);
    let results: Vec<ValueId> = (0..sig.returns.len())
        .map(|i| ValueId::new(u32::try_from(wrapper_sig.params.len() + 1 + i).unwrap()))
        .collect();

    let mut block = Block::new(trust_ir::BlockId::new(0));
    for (id, ty) in param_ids.iter().zip(&wrapper_sig.params) {
        block.params.push((*id, ty.clone()));
    }
    block.body.push(InstrNode::new(Inst::Alloca {
        ty: pointee.clone(),
        count: None,
        align: None,
    })
    .with_results(vec![slot]));
    block.body.push(InstrNode::new(Inst::Store {
        ty: pointee.clone(),
        ptr: slot,
        value: param_ids[index],
        volatile: false,
        align: None,
    }));
    let mut call_args = param_ids.clone();
    call_args[index] = slot;
    block.body.push(
        InstrNode::new(Inst::Call { callee: entry, args: call_args })
            .with_results(results.clone()),
    );
    block.body.push(InstrNode::new(Inst::Return { values: results }));

    let mut func =
        Function::new(func_id, "__trust_diff_pointee_wrapper", ty_id, trust_ir::BlockId::new(0));
    func.blocks = vec![block];
    out.try_add_function(func).ok()?;
    Some((out, func_id, wrapper_sig))
}


/// Trust (vtable slice 7): the PAIRED promoted-global admission set — the names a
/// `first_unmodeled_observation` walk may treat as modeled module state.
///
/// A name is admitted only when EVERY conjunct below holds; each is load-bearing:
///
/// * **`__trust_promoted_*` or `__trust_bytes_*` name grammar on BOTH sides.** Post-slice-6 both
///   spellings of a promoted SCALAR borrow use the promoted mint (producer wave-16; oracle
///   `respell_promoted_slots_as_globals`); post-slice-8 both spellings of a promoted
///   string/byte-string LITERAL use the bytes mint (producer wave-17 `emit_bytes_global`; oracle
///   `emit_str_const_bytes_global`, the bridge's slice-8 mirror). Slice 7's "name grammar covers
///   the producer's bytes globals" was read off the CRATE module, where `prepare_body_tables`
///   renames every spliced global `__trust_promoted_{n}` — the PER-BODY modules this function
///   compares carry `__trust_bytes_{idx}`, so the bytes grammar must be admitted explicitly.
///   The slice-4 warning stands: a shape test alone (immutable, even initializer-less) would also
///   admit symbolic-const carriers — scoping to the two mint families plus the initializer
///   requirement below keeps the admission on exactly the promoted-allocation provenance question.
/// * **Unique per module.** A duplicated name would make "the paired global" ambiguous.
/// * **Immutable + initializer-BEARING on both sides.** An initializer-less global is BSS
///   (zero-filled) — value agreement over zero-fill was slice 4's measured trap; refuse it.
/// * **Data-only, BIT-EXACT equal initializer content** (`Constant`'s hand-written float-bit-exact
///   `Eq`). Content equality is what makes the two globals THE SAME immutable object. Without it,
///   an ADDRESS-returning body (`const A: &i32 = &2` returns the pointer, never loads) would
///   raw-agree on `Ptr{0,0}` while the two cells hold different values — the slice-5 blindness
///   in reverse. Identity-bearing constants (`FnDef`/`SymbolAddr`/`Closure`) refuse via
///   `constant_materializes_uncomparable_identity`. Trust (vtable slice 12): equality is
///   `promoted_init_content_eq` — plain `Eq` plus the one deliberate cross-VARIANT arm
///   (producer `Aggregate` vs oracle `Array`, elementwise bit-exact) the array spelling
///   split forces.
/// * **Cross-module structural type agreement** — `promoted_pair_tys_agree`: `tys_agree`
///   (fail-closed on `Err`) plus the one deliberate cross-SPELLING arm (homogeneous
///   producer `Tuple` vs oracle `Array`, length + per-element agreement), scoped to this
///   pairing site; `tys_agree` itself quarantines the pair so it can never mint a verdict.
/// * **Address-free type.** A paired global whose type contains a pointer would let a
///   `Load`-through manufacture an address VALUE outside the audited closure
///   (`promoted_addr_closure`); every population type is scalar/aggregate-of-scalars.
pub(super) fn paired_admitted_promoted_globals(am: &Module, bm: &Module) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    for ga in &am.globals {
        if !(ga.name.starts_with("__trust_promoted_") || ga.name.starts_with("__trust_bytes_")) {
            continue;
        }
        if am.globals.iter().filter(|g| g.name == ga.name).count() != 1 {
            continue; // duplicated name on the A side -> ambiguous pairing, refuse
        }
        let mut bs = bm.globals.iter().filter(|g| g.name == ga.name);
        let (Some(gb), None) = (bs.next(), bs.next()) else {
            continue; // absent or duplicated on the B side -> unpaired/ambiguous, refuse
        };
        if ga.mutable || gb.mutable {
            continue;
        }
        let (Some(ia), Some(ib)) = (&ga.initializer, &gb.initializer) else { continue };
        if constant_materializes_uncomparable_identity(ia) || !promoted_init_content_eq(ia, ib) {
            continue;
        }
        if !ty_is_address_free(am, &ga.ty, TY_CMP_DEPTH)
            || !ty_is_address_free(bm, &gb.ty, TY_CMP_DEPTH)
        {
            continue;
        }
        if !promoted_pair_tys_agree(am, bm, &ga.ty, &gb.ty) {
            continue;
        }
        out.insert(ga.name.clone());
    }
    out
}
