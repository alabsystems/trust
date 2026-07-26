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
    check_structural_fold_refinement, sem_stack_safe_wrapper_of, sem_structural_fold_shape_of,
    sem_structural_fold_shape_of_with_bodies, DumpBodies, FoldDecline, FoldExpr, FoldFieldKind,
    FoldSort,
};
use trust_types::VerifiableFunction;

fn corpus_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures/level-fold-corpus")
}

fn load(name: &str) -> VerifiableFunction {
    let path = corpus_dir().join(format!("{name}.json"));
    let bytes =
        std::fs::read(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    serde_json::from_slice(&bytes).unwrap_or_else(|e| panic!("parse {}: {e}", path.display()))
}

/// The whole fixture directory as a sibling-body map — exactly what
/// `prove_dump_dir_with_budget` builds for the production pass.
fn all_bodies() -> DumpBodies {
    let mut m = DumpBodies::new();
    for entry in std::fs::read_dir(corpus_dir()).expect("read corpus dir") {
        let path = entry.expect("dir entry").path();
        if path.extension().and_then(|e| e.to_str()) != Some("json") {
            continue;
        }
        let bytes = std::fs::read(&path).expect("read dump");
        let f: VerifiableFunction = serde_json::from_slice(&bytes).expect("parse dump");
        m.insert(f.def_path.clone(), f);
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
    // wrapper) — four REAL clean-kernel rows, all trust-ir-primary.
    assert_eq!(
        sc.fully_faithful, 4,
        "exactly is_zero/is_nonzero/has_params_impl/has_params must be fully faithful"
    );
    assert_eq!(sc.fully_faithful_via_trustir, 4, "every certificate here is trust-ir-primary");
    assert_eq!(sc.fully_faithful_mirsem_fallback, 0, "no MirSem lane exists for these shapes");
}

/// `is_zero`'s recognized shape, pinned exactly: the 5-ctor Level mirror with
/// the REAL niche-encoded enum's LOGICAL tags, the shared `Succ|Param` arm,
/// the opaque `Param(Name)` payload, and the `&&` cond-tree.
#[test]
fn is_zero_shape_is_the_level_mirror() {
    let shape = sem_structural_fold_shape_of(&load("level__Level__is_zero"))
        .expect("is_zero must recognize");
    assert_eq!(shape.enum_name, "level::Level");
    assert_eq!(shape.sort, FoldSort::Bool);
    let names: Vec<&str> = shape.variants.iter().map(|v| v.name.as_str()).collect();
    assert_eq!(names, ["Zero", "Succ", "Max", "IMax", "Param"]);
    let tags: Vec<i128> = shape.variants.iter().map(|v| v.tag).collect();
    assert_eq!(tags, [0, 1, 2, 3, 4], "the LOGICAL discriminants, niche layout notwithstanding");
    // Field classification: Succ/Max/IMax children recursive; Param opaque.
    assert_eq!(shape.variants[1].fields, vec![FoldFieldKind::Recursive]);
    assert_eq!(
        shape.variants[2].fields,
        vec![FoldFieldKind::Recursive, FoldFieldKind::Recursive]
    );
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
    assert_eq!(w.inner_def_path, "level::Level::has_params_impl");
}

/// DRIFT PROBE — mutate the trampoline's red-zone literal (32768 → 999) in the
/// sibling map: every stack_safe resolution must decline `stack_safe_drift`
/// (P-STACK is quarantined to the EXACT two-literal shape).
#[test]
fn mutated_trampoline_literal_is_stack_safe_drift() {
    let mut bodies = all_bodies();
    {
        let tramp = bodies.get_mut("expr::stack_safe").expect("stack_safe dump present");
        let trust_types::Terminator::Call { args, .. } =
            &mut tramp.body.blocks[0].terminator
        else {
            panic!("stack_safe bb0 must be a call");
        };
        args[0] = trust_types::Operand::Constant(trust_types::ConstValue::Uint(999, 64));
    }
    let d = sem_structural_fold_shape_of_with_bodies(
        &load("level__Level__has_params_impl"),
        &bodies,
    )
    .expect_err("a mutated trampoline must decline");
    assert_eq!(d.name(), "stack_safe_drift", "mutated trampoline: {d:?}");
    // The wrapper declines on the same mutation.
    let d = sem_stack_safe_wrapper_of(&load("level__Level__has_params"), &bodies)
        .expect_err("the wrapper must decline on a mutated trampoline");
    assert_eq!(d.name(), "stack_safe_drift", "mutated trampoline (wrapper): {d:?}");
}

/// DRIFT PROBE — re-target the recursion closure's inner call (to `is_zero`
/// instead of `has_params_impl`): the fingerprint requires the closure to call
/// the RECOGNIZED function.
#[test]
fn retargeted_closure_body_is_stack_safe_drift() {
    let mut bodies = all_bodies();
    {
        let cl = bodies
            .get_mut("level::Level::has_params_impl::{closure#0}")
            .expect("closure dump present");
        let trust_types::Terminator::Call { func, .. } = &mut cl.body.blocks[1].terminator
        else {
            panic!("closure bb1 must be a call");
        };
        *func = "level::Level::is_zero".to_string();
    }
    let d = sem_structural_fold_shape_of_with_bodies(
        &load("level__Level__has_params_impl"),
        &bodies,
    )
    .expect_err("a re-targeted closure must decline");
    assert_eq!(d.name(), "stack_safe_drift", "re-targeted closure: {d:?}");
}

/// FORGERY PROBE against the REAL shape — claiming `is_zero`'s `Zero` arm with
/// the wrong polarity is `KernelRejected` (the recipe is genuine on real code,
/// not only on fixtures).
#[test]
fn is_zero_wrong_polarity_claim_is_kernel_rejected() {
    use trust_clean::trustir_fold::{check_structural_fold_refinement_claimed, probe_arm_rhs};
    let honest = sem_structural_fold_shape_of(&load("level__Level__is_zero"))
        .expect("is_zero recognizes");
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
