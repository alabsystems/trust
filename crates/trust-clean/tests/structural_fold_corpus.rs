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
//   * `pick` (`&Tree -> &Tree`) is a RECORDED RETRACTION, not a fold row — see
//     `pick_retraction_is_pinned_to_the_int_bool_carrier_gate` below and the
//     RETRACTION block on its expectation row. It used to be this corpus's
//     seventh FULLY_FAITHFUL row via the straight-line trust-ir lane; it no
//     longer claims full faithfulness, and the expectation table says so
//     explicitly.
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
    // the trust-ir structural-fold witness. `size`/`sum` are shape-recognized
    // and their witness mints, but they are held at the safety-discharge gate
    // by their genuine i64 overflow obligation; the adversarial members
    // decline by name.
    //
    // RETRACTED 6 <- 7 (RC-2, recorded 2026-08-01). The seventh row used to be
    // `pick` (`&Tree -> &Tree` identity) via the PRE-EXISTING straight-line
    // trust-ir lane. That certificate is withdrawn; the full rationale — the
    // gate, the commit that introduced it, and why the row cannot re-earn the
    // claim with the carrier the anchor has today — is on `pick`'s row in
    // `structural_fold_member_verdicts` and enforced by
    // `pick_retraction_is_pinned_to_the_int_bool_carrier_gate`. This is a
    // capability LOSS honestly booked, not a recognizer gap and not a
    // relaxation: nothing about the gate, the comparator or the corpus fixtures
    // was touched to obtain it.
    assert_eq!(
        sc.fully_faithful, 6,
        "exactly xor_all/first_leaf/tag_xor/has_leaf_zero/all_leaves_pos/collect_leaves \
         (the fold lane) must be fully faithful — `pick` is RETRACTED, see its row in \
         structural_fold_member_verdicts — got {}",
        sc.fully_faithful
    );
    assert_eq!(
        sc.fully_faithful_via_trustir, 6,
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
        // ------------------------------------------------------------------
        // RETRACTION — `pick` (`&Tree -> &Tree`, body `_0 := Use(Copy(_1))`).
        //
        // WAS `true`. `pick` used to certify FULLY_FAITHFUL via the
        // PRE-EXISTING straight-line trust-ir lane
        // (`prove::straight_line_fully_faithful_via_trustir`), never via the
        // fold lane (`sem_structural_fold_shape_of` declines it
        // `non_int_return` — still pinned by
        // `adversarial_members_decline_by_name`).
        //
        // THE GATE THAT NOW DECLINES IT: `prove.rs:7824`
        //     if !matches!(body.return_ty, Ty::Int { .. } | Ty::Bool) {
        //         return None;
        //     }
        // in `straight_line_ir_body`, together with its sibling operand gate at
        // `prove.rs:7854` (`place_type(body, p)` must be `Int`/`Bool` before a
        // bare `Copy`/`Move` becomes an `IrOperand::Var`). Both appear 0 times
        // at 43feddf372 and 2 times at HEAD; both were introduced by
        // 938f11049a ("Merge origin/main with audited TrustClean authority
        // fixes"). Stated purpose, in `straight_line_ir_body`'s own SOUNDNESS
        // paragraph: "The scalar trust-ir carrier admits only MIR `Int`/`Bool`
        // values; floats and other typed values fail closed before
        // translation."
        //
        // WHY `pick` TRIPS IT: `pick`'s return type and its parameter's type
        // are both `&Tree` — not `Int`, not `Bool`. Nothing else about `pick`
        // declines: `trust_vcgen::validate_function` passes,
        // `assignment_types::all_assignments_match` passes (so this is NOT the
        // equirecursive-lowering RC-1 that holds the fold rows), its safety VCs
        // are vacuously discharged, and its trust-ir safety adequacy holds.
        //
        // WHY THE DECLINE IS CORRECT, NOT AN OVER-REJECTION. Measured, by
        // disabling exactly these two gates and rerunning the lane:
        //   * `pick` certifies again — so they are the whole cause; AND
        //   * `fn fadd(a: f64, b: f64) -> f64 { a + b }` ALSO certifies
        //     FULLY_FAITHFUL, as the Int-sorted trust-ir body
        //     `Bin(Add, Var 0, Var 1)`. That claim is materially FALSE (IEEE-754
        //     addition rounds; `Int` addition does not), and it is the exact
        //     hazard the gates were written for.
        // `pick`'s old certificate rode on that same admission: it modeled a
        // `&Tree` value as a trust-ir `Int` variable. The refinement theorem the
        // lane mints is `Eq` at `Int` (every statement builder in
        // `trustir_anchor.rs` is `Expr::apps(eq, [int_ty(), lhs, rhs])`), so for
        // a `&Tree`-valued function it is a sort-mismatched adequacy claim — a
        // true theorem about `Int`s that says nothing about `pick`.
        //
        // WHY THE ROW IS NOT RE-EARNED HERE. Option (B) — mint a sort-neutral
        // parameter-identity witness — needs a carrier the anchor does not have:
        // `trustir_anchor.rs` has exactly one value sort (`Int`, `int_ty()`),
        // so a legitimate `f(x) = x` at an arbitrary type requires NEW
        // `Trust.TrustIr.*` registrations in `trustir_env_uncached` (new trusted
        // spec surface, its own axiom-closure audit and fail-closed probe).
        // That is a ratified design increment with its own kernel-facing
        // soundness budget, not a test-table edit. Until that carrier exists,
        // this row honestly claims nothing.
        //
        // DO NOT flip this back to `true` by relaxing `prove.rs:7824`/`:7854`.
        // Flip it back only by landing the non-`Int` carrier above.
        ("pick", false),
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

/// RC-2 — the RECORDED RETRACTION of the `pick` row, made ENFORCEABLE rather
/// than merely commented (see the RETRACTION block on `pick`'s expectation row
/// in `structural_fold_member_verdicts` for the full rationale).
///
/// This pins the ATTRIBUTION, so a future reader cannot mistake the retraction
/// for either a lowering bug or a recognizer gap, and cannot quietly re-flip the
/// expectation without first supplying the missing carrier:
///
///   1. `pick` is well-formed and assignment-typed — `validate_function` passes.
///      So the retraction is NOT the equirecursive-lowering defect (RC-1) that
///      holds the fold rows; that one fails closed at `all_assignments_match`,
///      which `pick` passes.
///   2. `pick`'s return type and its parameter's type are the SAME type, and
///      that type is neither `Int` nor `Bool` — it is `&Tree`. That is exactly
///      and only what `prove.rs:7824`
///      (`!matches!(body.return_ty, Ty::Int { .. } | Ty::Bool)`) and its sibling
///      operand gate at `prove.rs:7854` reject, because the trust-ir straight-
///      line carrier has one value sort (`Int`) and would have to model a
///      `&Tree` as an `Int` variable to proceed.
///   3. The production gate therefore declines it, and the decline is a SHAPE
///      decline (no recognizer accepted the body) — not a safety-VC residue:
///      `pick`'s safety obligations are vacuous.
///
/// The day the anchor grows a sort-neutral value carrier, this test is the
/// place that must be revisited together with the expectation row.
#[test]
fn pick_retraction_is_pinned_to_the_int_bool_carrier_gate() {
    use trust_types::Ty;

    let f = load("pick");

    // (1) Well-formed: the retraction is not RC-1 and not a malformed fixture.
    assert!(
        trust_vcgen::validate_function(&f).is_ok(),
        "pick must remain a well-formed, assignment-typed dump — if this fails the \
         retraction rationale below no longer describes the actual decline"
    );

    // (2) The exact predicate `prove.rs:7824` tests, evaluated on the fixture.
    let ret = &f.body.return_ty;
    assert!(
        !matches!(ret, Ty::Int { .. } | Ty::Bool),
        "pick's return type must be the NON-scalar `&Tree` this retraction is about; \
         got {ret:?}"
    );
    let param_ty = &f
        .body
        .locals
        .get(1)
        .expect("pick takes one parameter")
        .ty;
    assert_eq!(
        ret, param_ty,
        "pick is the parameter-identity `&Tree -> &Tree`; the retraction is precisely \
         that the anchor cannot state `f(x) = x` at a non-`Int` sort"
    );

    // (3) The production verdict, and its shape/safety split.
    let callees = std::collections::BTreeMap::new();
    let d = trust_clean::prove::diagnose_fully_faithful_gate(&f, &callees);
    println!(
        "RETRACTED pick: fully_faithful={} via_ir_shape={} via_mirsem_shape={} cluster={}",
        d.fully_faithful,
        d.via_ir_shape,
        d.via_mirsem_shape,
        d.cluster_tag()
    );
    assert!(
        !d.fully_faithful,
        "pick's FULLY_FAITHFUL claim is RETRACTED — if it certifies again, either the \
         non-`Int` carrier landed (then update the expectation row and this test \
         together) or prove.rs:7824/:7854 were relaxed (which is forbidden: the same \
         relaxation admits `fn fadd(a: f64, b: f64) -> f64 {{ a + b }}` as the Int-sorted \
         `Bin(Add, Var 0, Var 1)`)"
    );
    assert!(
        !d.via_ir_shape && !d.via_mirsem_shape,
        "the retraction must be a SHAPE decline (no recognizer admits the body), not a \
         safety-VC residue — pick raises no arithmetic obligation"
    );
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
