// structural_fold_corpus — pinning regression for RUNGS A + B of the
// structural-fold lane (docs/design/2026-07-10-structural-fold-lane.md §5
// Rungs A-B, §4). REAL trustc MIR dumps (never hand-transcribed — see
// fixtures/structural-fold-corpus/PROVENANCE.md) of structural folds over a
// 3-constructor `Arc`-recursive tree enum, plus the adversarial members the
// design's §6/§4 kill-tables name.
//
// What this pins, end-to-end through the REAL production `prove_dump_dir`
// pipeline:
//   * `xor_all` / `first_leaf` / `tag_xor` certify FULLY_FAITHFUL via the
//     trust-ir structural-fold witness (recursor-defined-total interpreter +
//     IH-slot mapping + strict-subterm provenance) — the first self-recursive
//     functions ANY lane certifies (rung A).
//   * RUNG B — `has_leaf_zero` / `all_leaves_pos` certify FULLY_FAITHFUL on
//     the BOOL result sort (short-circuit `||`/`&&` reconstructed as cond-tree
//     arms; `==`/`>` comparisons as Bool leaves), and `collect_leaves` on the
//     ACCUMULATOR sort (design §4: motive `Acc → Acc`, opaque `insertAcc`, the
//     exact program-order insert/recursion sequence).
//   * `tag_xor`'s `#[repr(i64)]` explicit discriminants (10/20/30) pin the
//     "never assume tag == declaration index" rule with a live corpus member.
//   * `size` / `sum` (the design doc's literal `+`-combining members) are
//     SHAPE-recognized and their kernel witness mints, but their i64
//     ArithmeticOverflow safety VC over an unbounded recursive result is
//     genuinely satisfiable — so they honestly stop short of FULLY_FAITHFUL
//     at the safety-discharge gate (a measured residue, not a recognizer gap).
//   * `bad_self` / `bad_rebuilt` / `bad_nonsub` DECLINE BY NAME
//     (`non_subterm_recursive_arg`) with provenance-specific detail.
//   * RUNG B — `bad_acc_escape` / `bad_acc_read` / `bad_acc_alias` DECLINE BY
//     NAME (`accumulator_escape` / `accumulator_read` / `accumulator_alias`),
//     the design §4 rules (iii)/(ii)/(i).
//
// Run with:
//   RUSTC_BOOTSTRAP=1 cargo test -p trust-clean --manifest-path crates/Cargo.toml \
//       --test structural_fold_corpus -- --nocapture
//
// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT

use std::path::{Path, PathBuf};

use trust_clean::prove_dump_dir;
use trust_clean::trustir_anchor::RefinementVerdict;
use trust_clean::trustir_fold::{
    check_structural_fold_refinement, sem_structural_fold_shape_of, FoldDecline,
};
use trust_types::VerifiableFunction;

fn corpus_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures/structural-fold-corpus")
}

fn load(name: &str) -> VerifiableFunction {
    let path = corpus_dir().join(format!("{name}.json"));
    let bytes = std::fs::read(&path)
        .unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    serde_json::from_slice(&bytes)
        .unwrap_or_else(|e| panic!("parse {}: {e}", path.display()))
}

/// THE HEADLINE — the full production `prove_dump_dir` pass over the corpus:
/// exactly the three overflow-free folds mint FULLY_FAITHFUL, all via the
/// trust-ir lane, and the kernel never rejects a constructed witness.
#[test]
fn structural_fold_corpus_scorecard() {
    let dir = corpus_dir();
    assert!(dir.exists(), "structural-fold-corpus fixtures missing at {}", dir.display());
    let sc = prove_dump_dir(&dir).expect("read structural-fold-corpus dumps");

    println!("\n========= structural-fold-corpus scorecard =========");
    println!("total                       : {}", sc.total);
    println!("fully_faithful              : {}", sc.fully_faithful);
    println!("  via_trustir               : {}", sc.fully_faithful_via_trustir);
    println!("  mirsem_fallback           : {}", sc.fully_faithful_mirsem_fallback);
    println!("kernel_rejected             : {}", sc.kernel_rejected);
    println!("=====================================================\n");

    // Soundness: the kernel must never reject a constructed witness.
    assert_eq!(sc.kernel_rejected, 0, "UNSOUND kernel acceptance: {:?}", sc.rejections);
    // All sixteen real fixtures deserialize and load (5 Int folds + 2 bool
    // folds + 4 accumulator folds + 3 adversarial + pick + sink).
    assert_eq!(sc.total, 16, "expected all sixteen structural-fold-corpus dumps to load");
    // RUNGS A+B HEADLINE: the three overflow-free Int folds (rung A) + the two
    // bool folds + the good accumulator fold (rung B) are FULLY_FAITHFUL via
    // the trust-ir structural-fold witness. The seventh FF row is `pick`
    // (`&Tree -> &Tree` identity), which certifies via the PRE-EXISTING
    // straight-line lane, not this one (`sem_structural_fold_shape_of` declines
    // it `non_int_return` — pinned below). `size`/`sum` are shape-recognized
    // and their witness mints, but they are held at the safety-discharge gate
    // by their genuine i64 overflow obligation; the adversarial members
    // decline by name.
    assert_eq!(
        sc.fully_faithful, 7,
        "exactly xor_all/first_leaf/tag_xor/has_leaf_zero/all_leaves_pos/collect_leaves \
         (fold lane) + pick (straight-line lane) must be fully faithful — got {}",
        sc.fully_faithful
    );
    assert_eq!(
        sc.fully_faithful_via_trustir, 7,
        "every certificate here must be trust-ir-primary"
    );
    assert_eq!(sc.fully_faithful_mirsem_fallback, 0, "no MirSem lane exists for a recursive fold");
}

/// Per-member verdict lines through the production per-function gate — the
/// rung-A report's exact evidence rows.
#[test]
fn structural_fold_member_verdicts() {
    use trust_clean::prove::diagnose_fully_faithful_gate;
    let callees = std::collections::BTreeMap::new();
    let expect: &[(&str, bool)] = &[
        ("xor_all", true),
        ("first_leaf", true),
        ("tag_xor", true),
        ("size", false),
        ("sum", false),
        ("bad_self", false),
        ("bad_rebuilt", false),
        ("bad_nonsub", false),
        // `pick` certifies via the PRE-EXISTING straight-line lane (a
        // parameter-reflecting identity), NOT the fold lane — see
        // `adversarial_members_decline_by_name`'s `non_int_return` pin.
        ("pick", true),
        // RUNG B — the bool lane:
        ("has_leaf_zero", true),
        ("all_leaves_pos", true),
        // RUNG B — the accumulator lane (design §4):
        ("collect_leaves", true),
        ("bad_acc_escape", false),
        ("bad_acc_read", false),
        ("bad_acc_alias", false),
    ];
    for (name, want_ff) in expect {
        let f = load(name);
        let d = diagnose_fully_faithful_gate(&f, &callees);
        println!(
            "VERDICT {name}: fully_faithful={} via_ir_shape={} via_ir_safety={} cluster={}",
            d.fully_faithful,
            d.via_ir_shape,
            d.via_ir_safety,
            d.cluster_tag()
        );
        assert_eq!(
            d.fully_faithful, *want_ff,
            "{name}: expected fully_faithful={want_ff}, got {}",
            d.fully_faithful
        );
    }
}

/// The two design-literal `+`-folds are SHAPE-recognized and their kernel
/// witness MINTS (recursor totality + per-variant adequacy prove modulo 3);
/// what withholds FULLY_FAITHFUL is exactly the undischarged overflow VC —
/// their `fully_faithful=false` rows are pinned by
/// `structural_fold_member_verdicts` / the scorecard above. (NB the production
/// diagnosis's `via_ir_shape` bit reports these `false` too, because — by the
/// standing via-trustir ARM convention — each arm bundles its own
/// `function_safety_vcs_all_discharged` discharge gate, so a safety-held arm
/// reads as shape-declined in the coarse cluster tag. The two asserts below
/// are the precise split: shape recognized, witness minted.)
#[test]
fn size_and_sum_are_recognized_and_their_witness_mints() {
    for name in ["size", "sum"] {
        let f = load(name);
        let shape = sem_structural_fold_shape_of(&f)
            .unwrap_or_else(|d| panic!("{name} must be shape-recognized, declined: {d:?}"));
        assert_eq!(
            check_structural_fold_refinement(&shape),
            RefinementVerdict::ProvenModulo3,
            "{name}: the kernel witness must mint"
        );
    }
}

/// The three good folds' recognized shapes: real tags read from the dump type
/// info — `tag_xor` pins tag != declaration index (10/20/30 vs 0/1/2).
#[test]
fn recognizer_reads_real_tags_never_declaration_indices() {
    let shape = sem_structural_fold_shape_of(&load("tag_xor")).expect("tag_xor recognizes");
    assert_eq!(shape.enum_name, "TaggedTree");
    let tags: Vec<i128> = shape.variants.iter().map(|v| v.tag).collect();
    assert_eq!(tags, vec![10, 20, 30], "TaggedTree's REAL discriminants must be carried");

    let shape = sem_structural_fold_shape_of(&load("xor_all")).expect("xor_all recognizes");
    assert_eq!(shape.enum_name, "Tree");
    assert_eq!(shape.variants.len(), 3);
    assert_eq!(shape.variants[0].tag, 0);
    assert_eq!(shape.variants[2].tag, 2);
}

/// Design §6 kill-table, pinned against REAL MIR: each adversarial member
/// declines BY NAME (`non_subterm_recursive_arg`) with provenance-specific
/// detail; the non-recursive helper declines as out-of-lane.
#[test]
fn adversarial_members_decline_by_name() {
    // bad_self — recursion on the scrutinee itself (f(x) = f(x)).
    let d = sem_structural_fold_shape_of(&load("bad_self"))
        .expect_err("bad_self must decline");
    assert_eq!(d.name(), "non_subterm_recursive_arg", "bad_self: {d:?}");
    let FoldDecline::NonSubtermRecursiveArg { detail } = &d else { unreachable!() };
    assert!(detail.contains("scrutinee"), "bad_self detail: {detail}");

    // bad_rebuilt — recursion on a reconstructed node.
    let d = sem_structural_fold_shape_of(&load("bad_rebuilt"))
        .expect_err("bad_rebuilt must decline");
    assert_eq!(d.name(), "non_subterm_recursive_arg", "bad_rebuilt: {d:?}");
    let FoldDecline::NonSubtermRecursiveArg { detail } = &d else { unreachable!() };
    assert!(detail.contains("rebuilt"), "bad_rebuilt detail: {detail}");

    // bad_nonsub — recursion on a sibling-call result.
    let d = sem_structural_fold_shape_of(&load("bad_nonsub"))
        .expect_err("bad_nonsub must decline");
    assert_eq!(d.name(), "non_subterm_recursive_arg", "bad_nonsub: {d:?}");
    let FoldDecline::NonSubtermRecursiveArg { detail } = &d else { unreachable!() };
    assert!(
        detail.contains("foreign-call result") && detail.contains("pick"),
        "bad_nonsub detail: {detail}"
    );

    // pick — not a fold at all (non-Int return, not self-recursive): the lane
    // never even considers it.
    let d = sem_structural_fold_shape_of(&load("pick")).expect_err("pick must decline");
    assert_eq!(d.name(), "non_int_return", "pick: {d:?}");
}

/// RUNG B — the bool folds' recognized shapes: Bool sort, comparison leaves,
/// short-circuit `||`/`&&` reconstructed as cond-trees over IH slots.
#[test]
fn bool_folds_recognize_with_cond_tree_arms() {
    use trust_clean::trustir_fold::{FoldCmpOp, FoldExpr, FoldSort};

    let shape = sem_structural_fold_shape_of(&load("has_leaf_zero")).expect("has_leaf_zero");
    assert_eq!(shape.sort, FoldSort::Bool);
    assert_eq!(shape.enum_name, "Tree");
    // Leaf(v) => v == 0
    assert_eq!(
        shape.variants[0].arm,
        FoldExpr::Cmp(
            FoldCmpOp::Eq,
            Box::new(FoldExpr::Payload(0)),
            Box::new(FoldExpr::Const(0))
        )
    );
    // Two(a,b) => f(a) || f(b)  ≡  if f(a) { true } else { f(b) }
    assert_eq!(
        shape.variants[2].arm,
        FoldExpr::Cond(
            Box::new(FoldExpr::Ih(0)),
            Box::new(FoldExpr::BoolConst(true)),
            Box::new(FoldExpr::Ih(1))
        )
    );
    assert_eq!(
        check_structural_fold_refinement(&shape),
        RefinementVerdict::ProvenModulo3,
        "has_leaf_zero's kernel witness must mint"
    );

    let shape = sem_structural_fold_shape_of(&load("all_leaves_pos")).expect("all_leaves_pos");
    assert_eq!(shape.sort, FoldSort::Bool);
    // Two(a,b) => f(a) && f(b)  ≡  if f(a) { f(b) } else { false }
    assert_eq!(
        shape.variants[2].arm,
        FoldExpr::Cond(
            Box::new(FoldExpr::Ih(0)),
            Box::new(FoldExpr::Ih(1)),
            Box::new(FoldExpr::BoolConst(false))
        )
    );
    assert_eq!(
        check_structural_fold_refinement(&shape),
        RefinementVerdict::ProvenModulo3,
        "all_leaves_pos's kernel witness must mint"
    );
}

/// RUNG B — the accumulator fold's recognized shape: the EXACT program-order
/// insert/recursion sequence (design §4's honest claim; set-commutativity is
/// never asserted).
#[test]
fn collect_leaves_recognizes_with_exact_sequence() {
    use trust_clean::trustir_fold::{FoldExpr, FoldSort};

    let shape = sem_structural_fold_shape_of(&load("collect_leaves")).expect("collect_leaves");
    assert_eq!(shape.sort, FoldSort::Acc);
    // Leaf(v) => insert(acc, v)
    assert_eq!(
        shape.variants[0].arm,
        FoldExpr::AccInsert(Box::new(FoldExpr::AccParam), Box::new(FoldExpr::Payload(0)))
    );
    // One(a) => f(a, acc)
    assert_eq!(shape.variants[1].arm, FoldExpr::AccRec(0, Box::new(FoldExpr::AccParam)));
    // Two(a,b) => f(b, f(a, acc)) — a THEN b, exactly the program order.
    assert_eq!(
        shape.variants[2].arm,
        FoldExpr::AccRec(1, Box::new(FoldExpr::AccRec(0, Box::new(FoldExpr::AccParam))))
    );
    assert_eq!(
        check_structural_fold_refinement(&shape),
        RefinementVerdict::ProvenModulo3,
        "collect_leaves' kernel witness must mint"
    );
}

/// RUNG B — design §4's kill-table, pinned against REAL MIR: each accumulator
/// adversary declines BY NAME.
#[test]
fn accumulator_adversaries_decline_by_name() {
    // bad_acc_escape — the accumulator (a shared re-borrow of it) is passed to
    // the foreign callee `sink` (rule iii).
    let d = sem_structural_fold_shape_of(&load("bad_acc_escape"))
        .expect_err("bad_acc_escape must decline");
    assert_eq!(d.name(), "accumulator_escape", "bad_acc_escape: {d:?}");
    let FoldDecline::AccumulatorEscape(detail) = &d else { unreachable!() };
    assert!(detail.contains("sink"), "bad_acc_escape detail: {detail}");

    // bad_acc_read — insert's bool result is consumed (rule ii: control flow
    // must never be accumulator-dependent).
    let d = sem_structural_fold_shape_of(&load("bad_acc_read"))
        .expect_err("bad_acc_read must decline");
    assert_eq!(d.name(), "accumulator_read", "bad_acc_read: {d:?}");

    // bad_acc_alias — the One arm recurses with a FRESH accumulator (rule i).
    let d = sem_structural_fold_shape_of(&load("bad_acc_alias"))
        .expect_err("bad_acc_alias must decline");
    assert_eq!(d.name(), "accumulator_alias", "bad_acc_alias: {d:?}");

    // sink — not a fold at all (a one-param Unit signature: accumulator-SHAPED
    // but outside the one-folded-param + one-accumulator model; declined at
    // the signature gate before any recursion/accumulator reasoning).
    let d = sem_structural_fold_shape_of(&load("sink")).expect_err("sink must decline");
    assert_eq!(d.name(), "param_shape_unsupported", "sink: {d:?}");
}
