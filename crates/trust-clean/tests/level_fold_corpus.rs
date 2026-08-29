// level_fold_corpus — RUNG B's REAL-CODE pilot for the structural-fold lane
// (docs/design/2026-07-10-structural-fold-lane.md §5 Rung B): the first REAL
// clean-kernel functions any lane certifies self-recursively. REAL trustc MIR
// dumps of `clean_kernel::Level`'s bool-fold family (never hand-transcribed —
// see fixtures/level-fold-corpus/PROVENANCE.md), through the production
// `prove_dump_dir` pipeline.
//
// What this pins:
//   * `Level::is_zero` / `Level::is_nonzero` certify FULLY_FAITHFUL via the
//     rung-B BOOL fold lane: 5-ctor `TLevel` mirror registered from the dump's
//     own type info, niche-encoded logical-tag map, SHARED (`A | B =>`) arm
//     blocks, the opaque `Param(Name)` payload atom, short-circuit `&&`/`||`
//     cond-trees.
//   * `Level::has_params_impl` certifies with its recursion routed through
//     `stack_safe(|| …)` closures — the P-STACK fingerprint debut (trampoline
//     body + closure body + capture provenance, each fail-closed); with an
//     EMPTY sibling-body map it honestly declines.
//   * `Level::has_params` (the public wrapper) certifies via the rung-B
//     stack-safe WRAPPER arm over the impl's fold witness.
//   * The `substitute_map`/`substitute_slice` family (the judge E-sort rows'
//     blocked callees) declines BY NAME — the honest rung-B blocker rows (the
//     OptE/ADT value domain is rung C; smart-ctor rebuilds are rung-E
//     transport; see the PROVENANCE's blocker catalog).
//   * `collect_params_impl` (TWO accumulators, insert-bool-guarded push)
//     declines `param_shape_unsupported` — outside the one-accumulator model.
//   * Forgery/drift probes: a mutated trampoline literal, a re-targeted
//     closure body, and a wrong-polarity kernel claim all fail closed.
//   * THE SIBLING-BODY JOIN: since the 2026-08-05 regeneration every callee in
//     this corpus carries its INSTANTIATION (`::<bool, {closure@…}>` plus the
//     `::<__trust_args@…>` disambiguator) while every dump is keyed by the
//     args-FREE def path. `trustir_fold::sibling_body` bridges the two; the
//     probes pin that every instantiation reaches the ONE generic body, that
//     near-misses and unknown callees still decline, and that removing the
//     generic body puts the recognizer straight back to `stack_safe_drift`.
//
// Run with:
//   RUSTC_BOOTSTRAP=1 cargo test -p trust-clean --manifest-path crates/Cargo.toml \
//       --test level_fold_corpus -- --nocapture
//
// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT

use std::path::{Path, PathBuf};

use trust_clean::prove_dump_dir;
use trust_clean::trustir_anchor::RefinementVerdict;
use trust_clean::trustir_fold::{
    DumpBodies, FoldDecline, FoldExpr, FoldFieldKind, FoldSort, check_structural_fold_refinement,
    sem_stack_safe_wrapper_of, sem_structural_fold_shape_of,
    sem_structural_fold_shape_of_with_bodies,
};
use trust_types::VerifiableFunction;

fn corpus_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures/level-fold-corpus")
}

fn load(name: &str) -> VerifiableFunction {
    let path = corpus_dir().join(format!("{name}.json"));
    let bytes = std::fs::read(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    serde_json::from_slice(&bytes).unwrap_or_else(|e| panic!("parse {}: {e}", path.display()))
}

/// The whole fixture directory as a sibling-body map — exactly what
/// `prove_dump_dir_with_budget` builds for the production pass.
///
/// A def-path COLLISION is LOUD here (`expr_fold_corpus.rs`'s discipline), not
/// silently resolved. `std::fs::read_dir` yields OS order, so a plain `insert`
/// would pick a body by filesystem accident, and `or_insert` would pick one
/// silently — neither is a thing a fixture corpus should ever do. The map is
/// keyed by the args-free `def_path` while callees carry their instantiation
/// (see `trust_clean::trustir_fold::sibling_body`), so two dumps under one key
/// would make the JOIN ambiguous as well as the build order.
fn all_bodies() -> DumpBodies {
    let mut m = DumpBodies::new();
    for entry in std::fs::read_dir(corpus_dir()).expect("read corpus dir") {
        let path = entry.expect("dir entry").path();
        if path.extension().and_then(|e| e.to_str()) != Some("json") {
            continue;
        }
        let bytes = std::fs::read(&path).expect("read dump");
        let f: VerifiableFunction = serde_json::from_slice(&bytes).expect("parse dump");
        let owner = f.def_path.clone();
        assert!(
            m.insert(owner.clone(), f).is_none(),
            "duplicate corpus def_path owner {owner} — the sibling-body map cannot \
             name one body for it",
        );
    }
    m
}

/// THE HEADLINE — the full production `prove_dump_dir` pass over the REAL
/// clean-kernel Level dumps: the two direct-recursion bool folds + the
/// stack_safe-routed impl + its public wrapper certify FULLY_FAITHFUL, all
/// via trust-ir, and the kernel never rejects a constructed witness.
#[test]
fn level_fold_corpus_scorecard() {
    let dir = corpus_dir();
    assert!(dir.exists(), "level-fold-corpus fixtures missing at {}", dir.display());
    let sc = prove_dump_dir(&dir).expect("read level-fold-corpus dumps");

    println!("\n========= level-fold-corpus scorecard =========");
    println!("total                       : {}", sc.total);
    println!("fully_faithful              : {}", sc.fully_faithful);
    println!("  via_trustir               : {}", sc.fully_faithful_via_trustir);
    println!("  mirsem_fallback           : {}", sc.fully_faithful_mirsem_fallback);
    println!("kernel_rejected             : {}", sc.kernel_rejected);
    println!("===============================================\n");

    // Soundness: the kernel must never reject a constructed witness.
    assert_eq!(sc.kernel_rejected, 0, "UNSOUND kernel acceptance: {:?}", sc.rejections);
    assert_eq!(sc.total, 14, "expected all fourteen level-fold-corpus dumps to load");
    // RUNG-B REAL-CODE HEADLINE: is_zero + is_nonzero (direct recursion) +
    // has_params_impl (stack_safe-routed recursion) + has_params (the
    // wrapper) — four REAL clean-kernel rows, all trust-ir-primary — PLUS
    // `has_params::{closure#0}`, the wrapper's delegation closure.
    //
    // The fifth row is NOT a new lane and not a relaxation: its whole body is
    // `|_| self.has_params_impl(upvar)`, which the ordinary callees-first
    // call-spine lane certifies as soon as `has_params_impl`'s certificate is
    // in the registry. Before the 2026-08-05 regeneration `has_params_impl`
    // declined (`stack_safe_drift`), so the registry was empty for it and the
    // closure declined with it; measured on the pre-regeneration bytes the
    // whole directory certified exactly ONE row (`has_params`), which is what
    // the deleted staleness proof recorded. Nothing in the corpus certifies
    // that is not either a recognized fold, its wrapper, or a direct
    // delegation to one of those.
    assert_eq!(
        sc.fully_faithful, 5,
        "exactly is_zero/is_nonzero/has_params_impl/has_params + the wrapper's \
         delegation closure must be fully faithful"
    );
    assert_eq!(sc.fully_faithful_via_trustir, 5, "every certificate here is trust-ir-primary");
    assert_eq!(sc.fully_faithful_mirsem_fallback, 0, "no MirSem lane exists for these shapes");
}

/// `is_zero`'s recognized shape, pinned exactly: the 5-ctor Level mirror with
/// the REAL niche-encoded enum's LOGICAL tags, the shared `Succ|Param` arm,
/// the opaque `Param(Name)` payload, and the `&&` cond-tree.
#[test]
fn is_zero_shape_is_the_level_mirror() {
    let shape = sem_structural_fold_shape_of(&load("level__Level__is_zero"))
        .expect("is_zero must recognize");
    // CRATE-QUALIFIED since the 2026-08-05 regeneration, for the same reason
    // the owner pins below are (`bd2d6ed1fc`, `with_resolve_crate_name!`): this
    // is the same `DefId` under the definition-site rendering. EXACT, not a
    // suffix test.
    assert_eq!(shape.enum_name, "extract_foldmemo::level::Level");
    assert_eq!(shape.sort, FoldSort::Bool);
    let names: Vec<&str> = shape.variants.iter().map(|v| v.name.as_str()).collect();
    assert_eq!(names, ["Zero", "Succ", "Max", "IMax", "Param"]);
    let tags: Vec<i128> = shape.variants.iter().map(|v| v.tag).collect();
    assert_eq!(tags, [0, 1, 2, 3, 4], "the LOGICAL discriminants, niche layout notwithstanding");
    // Field classification: Succ/Max/IMax children recursive; Param opaque.
    assert_eq!(shape.variants[1].fields, vec![FoldFieldKind::Recursive]);
    assert_eq!(shape.variants[2].fields, vec![FoldFieldKind::Recursive, FoldFieldKind::Recursive]);
    assert_eq!(shape.variants[4].fields, vec![FoldFieldKind::PayloadOpaque]);
    // Arms: Zero => true; Succ => false; Max(a,b) => f(a) && f(b);
    // IMax(_,b) => f(b); Param(_) => false.
    assert_eq!(shape.variants[0].arm, FoldExpr::BoolConst(true));
    assert_eq!(shape.variants[1].arm, FoldExpr::BoolConst(false));
    assert_eq!(
        shape.variants[2].arm,
        FoldExpr::Cond(
            Box::new(FoldExpr::Ih(0)),
            Box::new(FoldExpr::Ih(1)),
            Box::new(FoldExpr::BoolConst(false))
        )
    );
    assert_eq!(shape.variants[3].arm, FoldExpr::Ih(1));
    assert_eq!(shape.variants[4].arm, FoldExpr::BoolConst(false));
    assert_eq!(
        check_structural_fold_refinement(&shape),
        RefinementVerdict::ProvenModulo3,
        "the TLevel witness must mint modulo 3"
    );
}

/// `is_nonzero` — the `||` dual (shared `Zero|Param` arm).
#[test]
fn is_nonzero_recognizes_and_mints() {
    let shape = sem_structural_fold_shape_of(&load("level__Level__is_nonzero"))
        .expect("is_nonzero must recognize");
    assert_eq!(shape.sort, FoldSort::Bool);
    assert_eq!(shape.variants[0].arm, FoldExpr::BoolConst(false)); // Zero
    assert_eq!(shape.variants[1].arm, FoldExpr::BoolConst(true)); // Succ
    assert_eq!(
        shape.variants[2].arm, // Max(a,b) => f(a) || f(b)
        FoldExpr::Cond(
            Box::new(FoldExpr::Ih(0)),
            Box::new(FoldExpr::BoolConst(true)),
            Box::new(FoldExpr::Ih(1))
        )
    );
    assert_eq!(shape.variants[3].arm, FoldExpr::Ih(1)); // IMax(_,b) => f(b)
    assert_eq!(shape.variants[4].arm, FoldExpr::BoolConst(false)); // Param
    assert_eq!(check_structural_fold_refinement(&shape), RefinementVerdict::ProvenModulo3);
}

/// P-STACK DEBUT — `has_params_impl`'s recursion routes through `stack_safe`
/// closures: WITH the sibling bodies each trampoline call resolves to its IH
/// slot; WITHOUT them the function honestly declines (no visible recursion).
#[test]
fn has_params_impl_certifies_through_stack_safe_fingerprints() {
    let f = load("level__Level__has_params_impl");
    // Without sibling bodies: fail-closed, by name.
    let d = sem_structural_fold_shape_of(&f)
        .expect_err("has_params_impl must decline without sibling bodies");
    assert_eq!(d.name(), "not_self_recursive", "empty-bodies decline: {d:?}");
    // With the real sibling bodies: the full bool-fold shape.
    let bodies = all_bodies();
    let shape = sem_structural_fold_shape_of_with_bodies(&f, &bodies)
        .expect("has_params_impl must recognize with bodies");
    assert_eq!(shape.sort, FoldSort::Bool);
    // Zero => false; Succ(l) => f(l); Max/IMax(a,b) => f(a) || f(b);
    // Param(_) => true.
    assert_eq!(shape.variants[0].arm, FoldExpr::BoolConst(false));
    assert_eq!(shape.variants[1].arm, FoldExpr::Ih(0));
    for v_idx in [2usize, 3] {
        assert_eq!(
            shape.variants[v_idx].arm,
            FoldExpr::Cond(
                Box::new(FoldExpr::Ih(0)),
                Box::new(FoldExpr::BoolConst(true)),
                Box::new(FoldExpr::Ih(1))
            ),
            "the shared Max|IMax or-pattern arm walks per-variant"
        );
    }
    assert_eq!(shape.variants[4].arm, FoldExpr::BoolConst(true));
    assert_eq!(check_structural_fold_refinement(&shape), RefinementVerdict::ProvenModulo3);
}

/// The WRAPPER arm — `has_params` delegates to `has_params_impl` through the
/// fingerprinted trampoline; the wrapper recognizer pins the delegation.
#[test]
fn has_params_wrapper_recognizes_the_delegation() {
    let bodies = all_bodies();
    let w = sem_stack_safe_wrapper_of(&load("level__Level__has_params"), &bodies)
        .expect("has_params must recognize as a stack_safe wrapper");
    // CRATE-QUALIFIED since the 2026-08-05 regeneration (`bd2d6ed1fc`,
    // `with_resolve_crate_name!`): every owner in this corpus gained its crate
    // segment. EXACT, not a suffix test.
    assert_eq!(w.inner_def_path, "extract_foldmemo::level::Level::has_params_impl");
}

/// DRIFT PROBE — mutate the trampoline's red-zone literal (32768 → 999) in the
/// sibling map: every stack_safe resolution must decline `stack_safe_drift`
/// (P-STACK is quarantined to the EXACT two-literal shape).
#[test]
fn mutated_trampoline_literal_is_stack_safe_drift() {
    let mut bodies = all_bodies();
    {
        let tramp =
            bodies.get_mut("extract_foldmemo::expr::stack_safe").expect("stack_safe dump present");
        let trust_types::Terminator::Call { args, .. } = &mut tramp.body.blocks[0].terminator
        else {
            panic!("stack_safe bb0 must be a call");
        };
        assert!(
            matches!(
                &args[0],
                trust_types::Operand::Constant(trust_types::ConstValue::Uint(32768, _)),
            ),
            "the probe must MUTATE the pinned red-zone literal, not agree with it: {:?}",
            args[0],
        );
        args[0] = trust_types::Operand::Constant(trust_types::ConstValue::Uint(999, 64));
    }
    let d =
        sem_structural_fold_shape_of_with_bodies(&load("level__Level__has_params_impl"), &bodies)
            .expect_err("a mutated trampoline must decline");
    assert_eq!(d.name(), "stack_safe_drift", "mutated trampoline: {d:?}");
    // MEANINGFUL, not merely red: the decline must be the LITERAL check, which
    // only runs once the instantiated callee has already JOINED the mutated
    // body. "no sibling dump body" here would mean the probe stopped exercising
    // its mutation and started exercising a broken join.
    assert!(
        matches!(&d, FoldDecline::StackSafeDrift(s)
            if s.contains("is not the pinned two-literal maybe_grow forwarding shape")),
        "the decline must be the two-literal shape check, not a missing body: {d:?}",
    );
    // The wrapper declines on the same mutation, for the same reason.
    let d = sem_stack_safe_wrapper_of(&load("level__Level__has_params"), &bodies)
        .expect_err("the wrapper must decline on a mutated trampoline");
    assert_eq!(d.name(), "stack_safe_drift", "mutated trampoline (wrapper): {d:?}");
    assert!(
        matches!(&d, FoldDecline::StackSafeDrift(s)
            if s.contains("is not the pinned two-literal maybe_grow forwarding shape")),
        "wrapper: the decline must be the two-literal shape check: {d:?}",
    );
}

/// DRIFT PROBE — re-target the recursion closure's inner call (to `is_zero`
/// instead of `has_params_impl`): the fingerprint requires the closure to call
/// the RECOGNIZED function.
#[test]
fn retargeted_closure_body_is_stack_safe_drift() {
    let mut bodies = all_bodies();
    {
        let cl = bodies
            .get_mut("extract_foldmemo::level::Level::has_params_impl::{closure#0}")
            .expect("closure dump present");
        let trust_types::Terminator::Call { func, .. } = &mut cl.body.blocks[1].terminator else {
            panic!("closure bb1 must be a call");
        };
        assert_eq!(
            func, "extract_foldmemo::level::Level::has_params_impl",
            "the probe must RE-TARGET the recursive call, not agree with it",
        );
        *func = "extract_foldmemo::level::Level::is_zero".to_string();
    }
    let d =
        sem_structural_fold_shape_of_with_bodies(&load("level__Level__has_params_impl"), &bodies)
            .expect_err("a re-targeted closure must decline");
    assert_eq!(d.name(), "stack_safe_drift", "re-targeted closure: {d:?}");
    // MEANINGFUL, not merely red: reaching the closure's recursive-call target
    // at all means the instantiated trampoline callee already JOINED its
    // generic body and passed the two-literal fingerprint. The decline must
    // NAME the re-targeted callee.
    assert!(
        matches!(&d, FoldDecline::StackSafeDrift(s)
            if s.contains("calls extract_foldmemo::level::Level::is_zero, \
                           not the recognized function")),
        "the decline must name the re-targeted callee, not a missing body: {d:?}",
    );
}

/// FORGERY PROBE against the REAL shape — claiming `is_zero`'s `Zero` arm with
/// the wrong polarity is `KernelRejected` (the recipe is genuine on real code,
/// not only on fixtures).
#[test]
fn is_zero_wrong_polarity_claim_is_kernel_rejected() {
    use trust_clean::trustir_fold::{check_structural_fold_refinement_claimed, probe_arm_rhs};
    let honest =
        sem_structural_fold_shape_of(&load("level__Level__is_zero")).expect("is_zero recognizes");
    let mut wrong = honest.clone();
    wrong.variants[0].arm = FoldExpr::BoolConst(false);
    let claims = vec![Some(probe_arm_rhs(&wrong, 0).expect("wrong RHS renders"))];
    assert!(
        matches!(
            check_structural_fold_refinement_claimed(&honest, &claims),
            RefinementVerdict::KernelRejected(_)
        ),
        "a wrong-polarity claim against the REAL is_zero shape must be KernelRejected"
    );
}

/// The E-sort blocker rows decline BY NAME — the honest rung-B outcome the
/// PROVENANCE catalogs (OptE domain = rung C; smart-ctor rebuild = rung-E
/// transport; multi-accumulator out of the one-acc model).
#[test]
fn blocked_family_declines_by_name() {
    let bodies = all_bodies();
    for name in [
        "level__Level__substitute_map_impl_opt",
        "level__Level__substitute_slice_impl_opt",
        "level__Level__substitute_map_impl",
    ] {
        let d = sem_structural_fold_shape_of_with_bodies(&load(name), &bodies)
            .expect_err("the blocked family must decline");
        assert_eq!(d.name(), "non_int_return", "{name}: {d:?}");
    }
    // The substitute_map WRAPPER takes TWO params (self + subst; its closure
    // captures both) — outside the one-param wrapper fingerprint, declined at
    // the signature gate before any body inspection.
    let d = sem_stack_safe_wrapper_of(&load("level__Level__substitute_map"), &bodies)
        .expect_err("substitute_map must decline as a wrapper");
    assert_eq!(d.name(), "param_shape_unsupported", "substitute_map wrapper: {d:?}");
    // collect_params_impl threads TWO accumulators — outside the one-acc model.
    let d = sem_structural_fold_shape_of_with_bodies(
        &load("level__Level__collect_params_impl"),
        &bodies,
    )
    .expect_err("collect_params_impl must decline");
    assert_eq!(d.name(), "param_shape_unsupported", "collect_params_impl: {d:?}");
    assert!(
        matches!(&d, FoldDecline::ParamShapeUnsupported(s) if s.contains("3 params")),
        "collect_params_impl detail: {d:?}"
    );
}

// ─── THE SIBLING-BODY JOIN: an INSTANTIATED callee names a GENERIC body ────
//
// A dump's `def_path` is the args-FREE `safe_def_path_str(def_id)`; a
// `Terminator::Call.func` is `safe_def_path_str_with_args(def_id, args)` plus
// the fixed-format `::<__trust_args@…>` disambiguator. So ONE dumped body is
// named by AS MANY callee strings as it has call-site instantiations, and an
// exact map lookup joins none of them. `trustir_fold::sibling_body` is the
// bridge; these are its live probes against the REAL corpus.
//
// (This section replaces the staleness proof that stood here until 2026-08-05.
// That test rewrote the SHIPPED bytes the way a post-flip producer would emit
// them, to show the red scorecard measured fixture provenance rather than a
// recognizer defect. Its own docstring said to delete it "on the day the corpus
// is regenerated by a post-flip trustc"; the corpus now IS post-flip — it
// carries `datatype_defs` and by-name cut-point markers — so the rewrite is a
// no-op and its load-bearing assertion, "the SHIPPED bytes must still carry the
// defect on three of the four rows", is false by construction. The scorecard
// above now measures the same fact directly. The technique itself survives in
// the twin section of `structural_fold_corpus.rs`, whose corpus is still
// pre-flip.)

/// THE JOIN — the trampoline callee in the REAL corpus is
/// `extract_foldmemo::expr::stack_safe::<bool, {closure@…}>::<__trust_args@…>`
/// and the only dumped body is the args-free `extract_foldmemo::expr::stack_safe`.
/// Every instantiation must find that ONE generic body, and nothing else may.
#[test]
fn instantiated_callees_join_the_one_generic_stack_safe_body() {
    use trust_clean::trustir_fold::sibling_body;

    let bodies = all_bodies();
    const GENERIC: &str = "extract_foldmemo::expr::stack_safe";
    assert!(bodies.contains_key(GENERIC), "the corpus holds ONE stack_safe dump");

    // Every DISTINCT instantiation the corpus actually contains, harvested from
    // the fixtures themselves rather than hand-written, so this cannot drift
    // away from the bytes it is about.
    let mut instantiations: Vec<String> = Vec::new();
    for f in bodies.values() {
        for b in &f.body.blocks {
            if let trust_types::Terminator::Call { func, .. } = &b.terminator {
                if func.starts_with(GENERIC) && func != GENERIC && !instantiations.contains(func) {
                    instantiations.push(func.clone());
                }
            }
        }
    }
    // EXACT, like `sc.total` above: a change here is a regeneration event and
    // should be seen, not absorbed.
    assert_eq!(
        instantiations.len(),
        18,
        "the corpus carries exactly eighteen distinct stack_safe instantiations: \
         {instantiations:?}",
    );
    // MANY-TO-ONE, and the one is the generic body: instantiations differ in
    // both the return type and the closure, and every one of them resolves to
    // the SAME dump — which is exactly what monomorphisation does to it.
    for callee in &instantiations {
        let joined = sibling_body(&bodies, callee)
            .unwrap_or_else(|| panic!("instantiated callee {callee} must join the generic body"));
        assert_eq!(joined.def_path, GENERIC, "{callee} joined the wrong body");
        assert!(
            std::ptr::eq(joined, &bodies[GENERIC]),
            "{callee} must resolve to the corpus's own stack_safe dump",
        );
    }
    assert!(
        instantiations.iter().any(|c| c.contains("<bool,"))
            && instantiations.iter().any(|c| c.contains("<(),")),
        "the probe must cover instantiations at DIFFERENT return types: {instantiations:?}",
    );

    // The exact tier still wins, and is still exact.
    assert_eq!(sibling_body(&bodies, GENERIC).map(|f| f.def_path.as_str()), Some(GENERIC));

    // FAIL-CLOSED. An unknown callee, a near-miss on the disambiguator, and a
    // sibling item of the generic body all decline — no prefix, suffix or
    // "unique shorthand" tier exists to catch them.
    for absent in [
        // Never dumped at all.
        "extract_foldmemo::expr::not_a_real_function",
        "extract_foldmemo::expr::not_a_real_function::<bool>::<__trust_args@8a2184a43a70782505085d99a82ff886>",
        // A DIFFERENT item whose path merely EXTENDS the dumped one.
        "extract_foldmemo::expr::stack_safe_v2::<bool>::<__trust_args@8a2184a43a70782505085d99a82ff886>",
        // The dumped path as a PREFIX of a longer real path.
        "extract_foldmemo::expr::stack_safe::helper",
        // Malformed disambiguators: 31 hex, an uppercase digit, no `@`, and an
        // unbalanced turbofish. Each leaves a key the corpus does not hold.
        "extract_foldmemo::expr::stack_safe::<bool>::<__trust_args@8a2184a43a70782505085d99a82ff88>",
        "extract_foldmemo::expr::stack_safe::<bool>::<__trust_args@8A2184A43A70782505085D99A82FF886>",
        "extract_foldmemo::expr::stack_safe::<bool>::<__trust_args8a2184a43a70782505085d99a82ff886>",
        "extract_foldmemo::expr::stack_safe::<bool::<__trust_args@8a2184a43a70782505085d99a82ff886>",
        // The same item reached through a SECOND crate of the same name: the
        // producer prefixes such a callee with `disambiguate_direct_call_path`'s
        // stable crate id, which the derivation retains and no dump carries.
        "__trust_crate@0123456789abcdef::extract_foldmemo::expr::stack_safe::<bool>::<__trust_args@8a2184a43a70782505085d99a82ff886>",
    ] {
        assert!(sibling_body(&bodies, absent).is_none(), "{absent} must NOT join any sibling body",);
    }
}

/// The join is what carries `has_params_impl`'s P-STACK recognition, and it is
/// the ONLY thing standing between the instantiated callee and the decline: put
/// the trampoline's dump under a key the derivation cannot reach and the
/// recognizer declines by name again, exactly as it did before the bridge.
#[test]
fn without_the_generic_body_the_instantiated_trampoline_declines_by_name() {
    let mut bodies = all_bodies();
    // Re-file the trampoline under ONE instantiation's full spelling. That
    // spelling is a legitimate `TRUST_DUMP_MONO` dump key, so the exact tier
    // must still find THAT call site — while every OTHER instantiation, and the
    // generic key, must now miss.
    //
    // BYTE-EXACT callee spellings, harvested from the two fixtures that carry
    // them (`has_params_impl` calls the 1297 instantiation, `has_params` the
    // 1285 one). They must be the producer's real text: an earlier draft of this
    // test used hand-typed literals carrying runs of spaces the extractor never
    // emits, which made BOTH assertions below vacuous — the strings simply
    // failed to parse, so `is_some()` held only because the test had inserted
    // that exact key and `is_none()` held for the wrong reason. A probe that
    // stops probing is worse than one that fails, so the parse is asserted
    // first, on both strings, before either is used as evidence.
    let mono = "extract_foldmemo::expr::stack_safe::<bool, {closure@src/level/mod.rs:1297:42: 1297:44}>::<__trust_args@e1c529e04f3c8c1ad7298f767fcfb3ee>";
    let other = "extract_foldmemo::expr::stack_safe::<bool, {closure@src/level/mod.rs:1285:20: 1285:22}>::<__trust_args@8a2184a43a70782505085d99a82ff886>";
    // Prove the strings PARSE and derive, through the public bridge, while the
    // generic key is still present. If either spelling were unparseable this
    // loop fails here rather than silently hollowing out the two assertions
    // after it.
    for spelling in [mono, other] {
        assert!(
            trust_clean::trustir_fold::sibling_body(&bodies, spelling).is_some(),
            "the probe string must be a REAL instantiated callee that tier 2 \
             derives onto the generic body, or the assertions below prove \
             nothing: {spelling}",
        );
    }

    let tramp =
        bodies.remove("extract_foldmemo::expr::stack_safe").expect("stack_safe dump present");
    bodies.insert(mono.to_string(), tramp);
    assert!(
        trust_clean::trustir_fold::sibling_body(&bodies, mono).is_some(),
        "TIER 1 (exact) must win: a per-monomorphisation dump is filed under the \
         instantiated spelling, and that call site must find it",
    );
    assert!(
        trust_clean::trustir_fold::sibling_body(&bodies, other).is_none(),
        "a DIFFERENT instantiation must not reach a per-monomorphisation dump — \
         tier 2 derives `…::stack_safe`, which is no longer a key here",
    );

    // `has_params` (the wrapper) calls the 1285 instantiation, which now has no
    // body under any key the derivation produces.
    let d = sem_stack_safe_wrapper_of(&load("level__Level__has_params"), &bodies)
        .expect_err("the wrapper must decline without the trampoline body");
    assert_eq!(d.name(), "stack_safe_drift", "missing trampoline body: {d:?}");
    assert!(
        matches!(&d, FoldDecline::StackSafeDrift(s) if s.contains("no sibling dump body")),
        "the decline must NAME the missing sibling body: {d:?}",
    );
}
