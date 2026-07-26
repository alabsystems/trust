// fold_crate_lambda_calculus — pinning regression for the structural-fold
// lane's FIRST published-crate intake (fixtures/fold-crate-lambda-calculus-
// 3.5.0/PROVENANCE.md): `lambda_calculus` 3.5.0 (crates.io, zero-dependency,
// `#![deny(unsafe_code)]`), the first committed corpus with REAL direct
// self-recursion over a recursive ADT (`Term { Var(usize), Abs(Box<Term>),
// App(Box<(Term, Term)>) }`).
//
// RUNG G LANDED (2026-07-12; P-BOX-DEREF + G2 pair slots + G3 fold params).
// The intake's BLOCKED state flipped DELIBERATELY, one named row at a time:
//
//   * `term::Term::has_free_variables_helper` — the intake's named first
//     target (Bool sort, ZERO foreign callees) — now RECOGNIZES
//     (`fold_shape_ok`: Box children through the G1b fingerprint, App's boxed
//     pair as TWO per-component IH slots, `depth` threaded) and its KERNEL
//     WITNESS MINTS modulo 3: the first published-crate self-recursive
//     structural-fold certificate. It stays HONESTLY short of FULLY_FAITHFUL
//     at exactly the measured `depth + 1` Add-overflow VC (the PROVENANCE §5
//     honesty note — NOT forced, pinned below as the one gated-undischarged
//     safety VC kind).
//   * `term::Term::max_depth` — previously the headline `opaque_payload_read`
//     Box gap — now walks THROUGH both Box arms and declines at the NEXT
//     named gate: `foreign_value_in_arm` on `std::cmp::Ord::max` (the G4
//     pinned-pure-callee queue).
//   * `term::Term::max_free_index_helper` — admitted by the G3 signature,
//     declines at its Var arm's `saturating_sub` foreign callee (G4 queue).
//   * Box-specific FORGERIES (doctored fingerprint blocks, swapped ub-check
//     asserts, non-Box `Unique` walks) decline `box_deref_drift` /
//     KernelReject — the premise quarantine is load-bearing.
//
// Run with:
//   RUSTC_BOOTSTRAP=1 cargo test -p trust-clean --manifest-path crates/Cargo.toml \
//       --test fold_crate_lambda_calculus -- --nocapture
//
// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use trust_clean::trustir_anchor::RefinementVerdict;
use trust_clean::trustir_fold::{
    check_structural_fold_refinement, check_structural_fold_refinement_claimed, probe_arm_rhs,
    sem_structural_fold_shape_of_with_bodies, DumpBodies, FoldCmpOp, FoldDecline, FoldExpr,
    FoldFieldKind, FoldSort,
};
use trust_types::{
    AssertMessage, BinOp, ConstValue, Operand, Rvalue, Statement, Terminator, Ty, UnOp,
    VerifiableFunction,
};

fn corpus_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures/fold-crate-lambda-calculus-3.5.0")
}

fn load_all() -> Vec<VerifiableFunction> {
    let dir = corpus_dir();
    let mut out = Vec::new();
    let mut entries: Vec<_> = std::fs::read_dir(&dir)
        .unwrap_or_else(|e| panic!("read {}: {e}", dir.display()))
        .filter_map(Result::ok)
        .map(|e| e.path())
        .collect();
    entries.sort();
    for path in entries {
        if path.extension().and_then(|e| e.to_str()) != Some("json") {
            continue;
        }
        let bytes = std::fs::read(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
        let f: VerifiableFunction = serde_json::from_slice(&bytes)
            .unwrap_or_else(|e| panic!("parse {}: {e}", path.display()));
        out.push(f);
    }
    out
}

fn load_one(def_path: &str) -> VerifiableFunction {
    load_all()
        .into_iter()
        .find(|f| f.def_path == def_path)
        .unwrap_or_else(|| panic!("{def_path} missing from the corpus"))
}

fn bodies_of(funcs: &[VerifiableFunction]) -> DumpBodies {
    let mut m = DumpBodies::new();
    for f in funcs {
        m.entry(f.def_path.clone()).or_insert_with(|| f.clone());
    }
    m
}

fn is_direct_self_recursive(f: &VerifiableFunction) -> bool {
    f.body.blocks.iter().any(|b| {
        matches!(&b.terminator, Terminator::Call { func: callee, .. } if *callee == f.def_path)
    })
}

fn fold_verdicts(
    funcs: &[VerifiableFunction],
    bodies: &DumpBodies,
) -> BTreeMap<String, Result<(), FoldDecline>> {
    funcs
        .iter()
        .map(|f| {
            let v = trust_clean::trustir_fold::sem_structural_fold_shape_of_with_bodies(f, bodies)
                .map(|_| ());
            (f.def_path.clone(), v)
        })
        .collect()
}

/// The corpus census: 90 core-module dumps, 18 direct-self-recursive — the
/// first committed published-crate corpus with a real recursion population.
#[test]
fn corpus_recursion_population() {
    let funcs = load_all();
    assert_eq!(funcs.len(), 90, "expected all 90 core-module dumps to load");
    let rec: Vec<&str> = funcs
        .iter()
        .filter(|f| is_direct_self_recursive(f))
        .map(|f| f.def_path.as_str())
        .collect();
    assert_eq!(rec.len(), 18, "direct-self-recursive population drifted: {rec:?}");
    for expected in [
        "term::Term::max_depth",
        "term::Term::has_free_variables_helper",
        "term::Term::max_free_index_helper",
        "term::Term::is_isomorphic_to",
        "reduction::<impl term::Term>::beta_nor",
        "parser::fold_exprs",
    ] {
        assert!(rec.contains(&expected), "{expected} missing from the recursion population");
    }
}

/// RUNG G HEADLINE — `has_free_variables_helper` is the ONE recognized fold
/// in the crate (`fold_shape_ok`): Box children through the P-BOX-DEREF
/// fingerprint, the boxed App pair as TWO per-component IH slots (G2), the
/// `depth` parameter threaded (G3). Its recognized arms are pinned EXACTLY,
/// and the kernel witness mints modulo 3 — the first published-crate
/// self-recursive structural-fold certificate.
#[test]
fn has_free_variables_helper_certifies_kernel_witness() {
    let funcs = load_all();
    let bodies = bodies_of(&funcs);
    let verdicts = fold_verdicts(&funcs, &bodies);

    let ok_rows: Vec<&str> =
        verdicts.iter().filter(|(_, v)| v.is_ok()).map(|(k, _)| k.as_str()).collect();
    assert_eq!(
        ok_rows,
        vec!["term::Term::has_free_variables_helper"],
        "the recognized-fold population drifted"
    );

    let f = load_one("term::Term::has_free_variables_helper");
    let shape = sem_structural_fold_shape_of_with_bodies(&f, &bodies)
        .expect("has_free_variables_helper must recognize");
    assert_eq!(shape.enum_name, "term::Term");
    assert_eq!(shape.sort, FoldSort::Bool);
    assert!(shape.depth, "the depth parameter must be threaded (G3)");
    assert_eq!(shape.variants.len(), 3);

    // Var(i) => if i > depth { true } else { i == 0 }.
    assert_eq!(shape.variants[0].name, "Var");
    assert_eq!(shape.variants[0].fields, vec![FoldFieldKind::PayloadInt]);
    assert_eq!(
        shape.variants[0].arm,
        FoldExpr::Cond(
            Box::new(FoldExpr::Cmp(
                FoldCmpOp::Gt,
                Box::new(FoldExpr::Payload(0)),
                Box::new(FoldExpr::DepthParam),
            )),
            Box::new(FoldExpr::BoolConst(true)),
            Box::new(FoldExpr::Cmp(
                FoldCmpOp::Eq,
                Box::new(FoldExpr::Payload(0)),
                Box::new(FoldExpr::Const(0)),
            )),
        )
    );

    // Abs(t) => f(t, depth + 1) — ONE slot from Box<Term> (G1).
    assert_eq!(shape.variants[1].name, "Abs");
    assert_eq!(shape.variants[1].fields, vec![FoldFieldKind::Recursive]);
    assert_eq!(
        shape.variants[1].arm,
        FoldExpr::IhApp(
            0,
            Box::new(FoldExpr::Bin(
                trust_clean::trustir_fold::FoldBinOp::Add,
                Box::new(FoldExpr::DepthParam),
                Box::new(FoldExpr::Const(1)),
            )),
        )
    );

    // App(t) => f(t.0, depth) || f(t.1, depth) — TWO slots from ONE
    // Box<(Term, Term)> MIR field (G2 per-component IHs).
    assert_eq!(shape.variants[2].name, "App");
    assert_eq!(
        shape.variants[2].fields,
        vec![FoldFieldKind::Recursive, FoldFieldKind::Recursive]
    );
    assert_eq!(
        shape.variants[2].arm,
        FoldExpr::Cond(
            Box::new(FoldExpr::IhApp(0, Box::new(FoldExpr::DepthParam))),
            Box::new(FoldExpr::BoolConst(true)),
            Box::new(FoldExpr::IhApp(1, Box::new(FoldExpr::DepthParam))),
        )
    );

    // THE CERTIFICATE: recursor-defined-total interpreter + per-variant
    // adequacy, kernel-checked modulo 3.
    assert_eq!(check_structural_fold_refinement(&shape), RefinementVerdict::ProvenModulo3);
}

/// The HONEST FULLY_FAITHFUL hostage (PROVENANCE §5's honesty note, NOT
/// engineered around): the recognized fold's emitted safety VCs are exactly
/// {3× constant `Sub` (the fingerprint's `align − 1`, trivially refutable),
/// 1× `Add` (the Abs arm's `depth + 1` — GENUINELY satisfiable over an
/// unbounded depth)} on the GATED side, plus the two premise-discharged
/// ub-check kinds (UnsupportedMir/Misaligned + Assertion/null — outside the
/// discharge gate's kind filter BY DESIGN: they are P-BOX-DEREF's burden and
/// the recognizer validated every one of them against the fingerprint).
/// The expensive satisfiable-Add refutation itself is exercised by the
/// census/ff-gate evidence, not re-run here.
#[test]
fn has_free_variables_helper_overflow_residue_is_the_measured_hostage() {
    let f = load_one("term::Term::has_free_variables_helper");
    let vcs = trust_vcgen::generate_vcs(&f);
    let mut gated_sub = 0usize;
    let mut gated_add = 0usize;
    let mut misaligned = 0usize;
    let mut null_custom = 0usize;
    let mut other_gated = Vec::new();
    for vc in &vcs {
        use trust_types::VcKind;
        let gated = trust_clean::mirsem::is_safety_vc_kind_pub(&vc.kind);
        match &vc.kind {
            VcKind::ArithmeticOverflow { op: BinOp::Sub, .. } if gated => gated_sub += 1,
            VcKind::ArithmeticOverflow { op: BinOp::Add, .. } if gated => gated_add += 1,
            VcKind::UnsupportedMir { kind, .. }
                if kind.contains("MisalignedPointerDereference") =>
            {
                assert!(!gated, "the Misaligned ub-check must stay premise-scoped");
                misaligned += 1;
            }
            VcKind::Assertion { message } if message == "null reference constructed" => {
                assert!(!gated, "the null ub-check must stay premise-scoped");
                null_custom += 1;
            }
            k if gated => other_gated.push(format!("{k:?}")),
            _ => {}
        }
    }
    assert_eq!((gated_sub, gated_add), (3, 1), "gated safety-VC population drifted");
    assert_eq!((misaligned, null_custom), (3, 3), "ub-check assert population drifted");
    assert!(other_gated.is_empty(), "unexpected gated safety VCs: {other_gated:?}");
}

/// `max_depth` — the former `opaque_payload_read` headline — now walks
/// THROUGH both Box arms (the premise quarantine admits the fingerprint) and
/// declines at the NEXT named gate: the `Ord::max` foreign callee combining
/// the two App IHs (the G4 pinned-pure-callee queue).
#[test]
fn max_depth_advances_to_the_foreign_callee_gate() {
    let funcs = load_all();
    let bodies = bodies_of(&funcs);
    let verdicts = fold_verdicts(&funcs, &bodies);

    let Err(d) = &verdicts["term::Term::max_depth"] else {
        panic!("max_depth unexpectedly recognized (Ord::max is not pinned)")
    };
    assert_eq!(d.name(), "foreign_value_in_arm", "max_depth decline drifted: {d:?}");
    let FoldDecline::ForeignValueInArm(who) = d else { unreachable!() };
    assert!(who.contains("Ord::max"), "max_depth foreign callee drifted: {who}");

    // max_free_index_helper: G3-admitted, declines at its Var arm's
    // saturating_sub foreign callee.
    let Err(d) = &verdicts["term::Term::max_free_index_helper"] else {
        panic!("max_free_index_helper unexpectedly recognized")
    };
    assert_eq!(d.name(), "foreign_value_in_arm", "max_free_index_helper drifted: {d:?}");
    let FoldDecline::ForeignValueInArm(who) = d else { unreachable!() };
    assert!(who.contains("saturating_sub"), "max_free_index_helper callee drifted: {who}");
}

/// The rest of the recursion population still declines by SIGNATURE — pinned
/// per class so a lane extension that admits any of these flips a named row.
#[test]
fn recursion_population_signature_declines() {
    let funcs = load_all();
    let bodies = bodies_of(&funcs);
    let verdicts = fold_verdicts(&funcs, &bodies);

    // The binary tree fold: 2 params but the second is &Term, not an Int
    // scalar — NOT the G3 depth family; stays the signature-class decline.
    let Err(d) = &verdicts["term::Term::is_isomorphic_to"] else {
        panic!("is_isomorphic_to unexpectedly recognized")
    };
    assert_eq!(d.name(), "non_int_return", "is_isomorphic_to decline drifted: {d:?}");

    // 3-param `&mut Term -> Unit` reduction engines: outside the pure-fold
    // model's param shape (they MUTATE the tree — not a fold at all).
    for f in [
        "reduction::<impl term::Term>::_apply",
        "reduction::<impl term::Term>::beta_app",
        "reduction::<impl term::Term>::beta_cbn",
        "reduction::<impl term::Term>::beta_cbv",
        "reduction::<impl term::Term>::beta_hap",
        "reduction::<impl term::Term>::beta_hno",
        "reduction::<impl term::Term>::beta_hsp",
        "reduction::<impl term::Term>::beta_nor",
        "reduction::<impl term::Term>::update_free_variables",
    ] {
        let Err(d) = &verdicts[f] else { panic!("{f} unexpectedly recognized") };
        assert_eq!(d.name(), "param_shape_unsupported", "{f} decline drifted: {d:?}");
    }

    // Slice-recursion parser functions: recursive, but not over the ADT.
    for f in ["parser::_convert_classic_tokens", "parser::_get_ast", "parser::fold_exprs"] {
        let Err(d) = &verdicts[f] else { panic!("{f} unexpectedly recognized") };
        assert_eq!(d.name(), "non_int_return", "{f} decline drifted: {d:?}");
    }
}

/// The premise-level pin: the dump's own type info lowers `Abs.0` through
/// exactly `std::boxed::Box → std::ptr::Unique → std::ptr::NonNull → RawPtr
/// → term::Term` (and `App.0` to the same chain ending in a 2-tuple of Term
/// back-references) — the measured P-BOX-DEREF walk rung G pins, and
/// NOT the `std::sync::Arc → ptr → NonNull → pointer → ArcInner → data`
/// chain P-ARC-DEREF pins.
#[test]
fn box_field_lowering_chain() {
    let funcs = load_all();
    let f = funcs.iter().find(|f| f.def_path == "term::Term::max_depth").expect("max_depth dump");
    let Ty::Ref { inner, .. } = &f.body.locals[1].ty else { panic!("param not a ref") };
    let Ty::Adt { name, variants, .. } = inner.as_ref() else { panic!("param not an enum") };
    assert_eq!(name, "term::Term");
    assert_eq!(variants.len(), 3);
    assert_eq!(
        (variants[0].name.as_str(), variants[1].name.as_str(), variants[2].name.as_str()),
        ("Var", "Abs", "App")
    );

    // Var(usize) — a real Int payload (the lane already classifies this).
    assert!(matches!(&variants[0].fields[0].1, Ty::Int { .. }), "Var.0 lowering drifted");

    // Abs(Box<Term>): Box → Unique → NonNull → RawPtr → Datatype(term::Term).
    let walk = |field: &Ty| -> Option<Ty> {
        let Ty::Adt { name, fields, .. } = field else { return None };
        assert_eq!(name, "std::boxed::Box", "field is not a Box: {name}");
        let (_, unique) = fields.iter().find(|(n, _)| n == "0")?;
        let Ty::Adt { name: un, fields: uf, .. } = unique else { return None };
        assert_eq!(un, "std::ptr::Unique", "Box.0 is not Unique: {un}");
        let (_, nonnull) = uf.iter().find(|(n, _)| n == "pointer")?;
        let Ty::Adt { name: nn, fields: nf, .. } = nonnull else { return None };
        assert_eq!(nn, "std::ptr::NonNull", "Unique.pointer is not NonNull: {nn}");
        let (_, raw) = nf.iter().find(|(n, _)| n == "pointer")?;
        let Ty::RawPtr { pointee, .. } = raw else { return None };
        Some(pointee.as_ref().clone())
    };

    let abs_pointee = walk(&variants[1].fields[0].1).expect("Abs.0 Box walk broke");
    assert!(
        matches!(&abs_pointee, Ty::Datatype { name, .. } if name == "term::Term"),
        "Abs.0 pointee drifted: {abs_pointee:?}"
    );

    let app_pointee = walk(&variants[2].fields[0].1).expect("App.0 Box walk broke");
    let Ty::Tuple(elems) = &app_pointee else {
        panic!("App.0 pointee is not the boxed 2-tuple: {app_pointee:?}")
    };
    assert_eq!(elems.len(), 2);
    for e in elems {
        assert!(
            matches!(e, Ty::Datatype { name, .. } if name == "term::Term"),
            "App tuple component drifted: {e:?}"
        );
    }
}

// ===========================================================================
// Box-specific FORGERIES — the P-BOX-DEREF quarantine is load-bearing.
// Doctored real dumps (never accepted): every mutation of the fingerprint
// declines `box_deref_drift` by name; a claimed wrong RHS over the honest
// witness is KernelRejected.
// ===========================================================================

/// The align block's index (first Misaligned assert) + its null partner.
fn first_ubcheck_pair(f: &VerifiableFunction) -> (usize, usize) {
    for (i, b) in f.body.blocks.iter().enumerate() {
        if let Terminator::Assert { msg: AssertMessage::MisalignedPointerDereference, target, .. } =
            &b.terminator
        {
            let null_idx = f
                .body
                .blocks
                .iter()
                .position(|nb| nb.id == *target)
                .expect("null partner block exists");
            return (i, null_idx);
        }
    }
    panic!("no Misaligned assert in the dump");
}

fn recognize(f: &VerifiableFunction) -> Result<(), FoldDecline> {
    let bodies = DumpBodies::new();
    sem_structural_fold_shape_of_with_bodies(f, &bodies).map(|_| ())
}

/// FORGERY 1 — SWAPPED UB-CHECK ASSERTS: the alignment block asserting the
/// null message and vice versa. The premise must NOT transfer: named decline.
#[test]
fn forgery_swapped_ubcheck_asserts_declines_box_deref_drift() {
    let mut f = load_one("term::Term::has_free_variables_helper");
    let (align_idx, null_idx) = first_ubcheck_pair(&f);
    {
        let Terminator::Assert { msg, .. } = &mut f.body.blocks[align_idx].terminator else {
            unreachable!()
        };
        *msg = AssertMessage::Custom("null reference constructed".to_string());
    }
    {
        let Terminator::Assert { msg, .. } = &mut f.body.blocks[null_idx].terminator else {
            panic!("null partner does not end in an assert")
        };
        *msg = AssertMessage::MisalignedPointerDereference;
    }
    let d = recognize(&f).expect_err("swapped ub-check asserts must decline");
    assert_eq!(d.name(), "box_deref_drift", "swapped-asserts decline drifted: {d:?}");
}

/// FORGERY 2 — DOCTORED FINGERPRINT BLOCK (a): the alignment mask constant
/// is not a power of two (`7 - 1` instead of `8 - 1`).
#[test]
fn forgery_non_pow2_alignment_mask_declines_box_deref_drift() {
    let mut f = load_one("term::Term::has_free_variables_helper");
    let (align_idx, _) = first_ubcheck_pair(&f);
    let mut doctored = false;
    for s in &mut f.body.blocks[align_idx].stmts {
        if let Statement::Assign {
            rvalue: Rvalue::BinaryOp(BinOp::Sub, Operand::Constant(ConstValue::Uint(a, _)), _),
            ..
        } = s
        {
            *a = 7;
            doctored = true;
        }
    }
    assert!(doctored, "alignment-mask statement not found");
    let d = recognize(&f).expect_err("a non-power-of-two mask must decline");
    assert_eq!(d.name(), "box_deref_drift", "mask decline drifted: {d:?}");
}

/// FORGERY 3 — DOCTORED FINGERPRINT BLOCK (b): the null block's `Not` is
/// dropped (asserting `addr == 0` INSTEAD of its negation — the polarity an
/// attacker would want). Must decline, never premise-discharge.
#[test]
fn forgery_dropped_null_negation_declines_box_deref_drift() {
    let mut f = load_one("term::Term::has_free_variables_helper");
    let (_, null_idx) = first_ubcheck_pair(&f);
    let mut doctored = false;
    for s in &mut f.body.blocks[null_idx].stmts {
        if let Statement::Assign { rvalue, .. } = s {
            if let Rvalue::UnaryOp(UnOp::Not, op) = rvalue {
                *rvalue = Rvalue::Use(op.clone());
                doctored = true;
            }
        }
    }
    assert!(doctored, "null-negation statement not found");
    let d = recognize(&f).expect_err("a dropped null negation must decline");
    assert_eq!(d.name(), "box_deref_drift", "dropped-Not decline drifted: {d:?}");
}

/// FORGERY 4 — NON-BOX UNIQUE WALK: the same Unique/NonNull chain under a
/// type that is NOT `std::boxed::Box` (and, separately, a Box whose "0"
/// field is not `std::ptr::Unique`). The G1a walk is a whole-chain pin.
#[test]
fn forgery_non_box_unique_walk_declines() {
    let raw = std::fs::read_to_string(
        corpus_dir().join("term__Term__has_free_variables_helper.json"),
    )
    .expect("read dump");

    // (a) `Box` renamed: the fields no longer classify as recursive Box
    // children, so the fingerprinted idiom has no pinned-Box provenance.
    let fake_box: VerifiableFunction =
        serde_json::from_str(&raw.replace("std::boxed::Box", "fake::BoxLike"))
            .expect("doctored dump parses");
    let d = recognize(&fake_box).expect_err("a fake Box type must decline");
    assert_eq!(d.name(), "box_deref_drift", "fake-Box decline drifted: {d:?}");

    // (b) `Unique` renamed inside a real Box: the pointee walk breaks.
    let fake_unique: VerifiableFunction =
        serde_json::from_str(&raw.replace("std::ptr::Unique", "fake::Unique"))
            .expect("doctored dump parses");
    let d = recognize(&fake_unique).expect_err("a fake Unique chain must decline");
    assert_eq!(d.name(), "box_deref_drift", "fake-Unique decline drifted: {d:?}");
}

/// FORGERY 5 — KERNEL REJECT over the REAL recognized witness: claim App's
/// arm with the pair components SWAPPED (`f(t.1,d) || f(t.0,d)`) against the
/// honest interpreter — not def-eq, KernelRejected (the same probe discipline
/// as the authored corpus's swapped-children member).
#[test]
fn forgery_swapped_real_pair_claim_is_kernel_rejected() {
    let funcs = load_all();
    let bodies = bodies_of(&funcs);
    let f = load_one("term::Term::has_free_variables_helper");
    let honest =
        sem_structural_fold_shape_of_with_bodies(&f, &bodies).expect("honest shape recognizes");
    let mut wrong = honest.clone();
    wrong.variants[2].arm = FoldExpr::Cond(
        Box::new(FoldExpr::IhApp(1, Box::new(FoldExpr::DepthParam))),
        Box::new(FoldExpr::BoolConst(true)),
        Box::new(FoldExpr::IhApp(0, Box::new(FoldExpr::DepthParam))),
    );
    let wrong_rhs = probe_arm_rhs(&wrong, 2).expect("swapped RHS renders");
    let claims = vec![None, None, Some(wrong_rhs)];
    assert!(
        matches!(
            check_structural_fold_refinement_claimed(&honest, &claims),
            RefinementVerdict::KernelRejected(_)
        ),
        "a swapped-pair claim over the real witness must be KernelRejected"
    );
}
