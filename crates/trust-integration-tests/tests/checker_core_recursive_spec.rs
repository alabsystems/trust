// trust-integration-tests/tests/checker_core_recursive_spec.rs
//
// Gap-A (recursive-spec Formula) STATE + EMIT + fail-closed control.
//
// The rung this exercises sits ABOVE the arithmetic functional postcondition
// (`result >= step`, grounded on a literal clean-kernel fn's MIR in
// `functional_postcondition_mir_loop.rs`): it carries a CHECKER-CORE
// STRUCTURAL/INDUCTIVE property of the result — `is_whnf(result)` (the returned
// kernel expression is in weak-head normal form) — through the SAME standard
// vcgen pipeline to an emitted `VcKind::Postcondition` VC, and shows that the
// SAME `trust_certify::certify_violation` that DISCHARGES an arithmetic
// contradiction FAILS CLOSED on the opaque checker-core predicate (no false
// PROVE). The recursive semantics of `is_whnf` is bound (by the trust-types
// semantics registry) to clean-verify's inductive `is_whnf : KExpr -> Prop`
// (ctors is_whnf.sort/lam/pi; DerivedProved lemma `value_is_whnf`); realizing
// that semantics as a kernel-checked discharge is the next (DISCHARGE) rung,
// mapped in scratch/trust-gap-a-recursive-spec.md.
//
// No fork required (pure in-process vcgen + certify): the built rustc fork's
// contract-lowering grammar (`compiler/rustc_mir_transform/src/
// trust_contract_query.rs`) has no `Call` arm and no `Expr` carrier type, so it
// rejects a predicate-call `#[ensures]` (`__trust_unsupported_compiler_contract__`).
// The parser + vcgen lanes exercised here are the trust-crate half that a fork
// rebuild would feed end-to-end.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{
    BasicBlock, BlockId, Formula, FunctionSpec, LocalDecl, Sort, SourceSpan, Terminator, Ty,
    VcKind, VerifiableBody, VerifiableFunction,
};

/// A minimal well-formed `VerifiableFunction` with a single `Return` block, so
/// the standard vcgen postcondition lane runs. The `#[ensures]` spec clause is
/// supplied as its SOURCE STRING (parsed by the production `parse_spec_expr` that
/// `generate_vcs` calls), never a hand-built Formula.
fn fn_with_ensures(ensures: &str) -> VerifiableFunction {
    VerifiableFunction {
        name: "kernel_result_fn".to_string(),
        def_path: "test::kernel_result_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::usize(), name: None },
                LocalDecl { index: 1, ty: Ty::usize(), name: Some("x".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::usize(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: FunctionSpec {
            requires: vec![],
            ensures: vec![ensures.to_string()],
            invariants: vec![],
        },
    }
}

/// STATE + EMIT: the checker-core recursive-spec predicate `is_whnf(result)` is
/// parsed from its `#[ensures]` string and EMITTED by the standard
/// `generate_vcs` pipeline as a `VcKind::Postcondition` VC negating the opaque
/// `is_whnf` predicate over the return slot `_0`.
#[test]
fn checker_core_is_whnf_postcondition_emitted_and_shaped() {
    let func = fn_with_ensures("is_whnf(result)");
    let vcs = trust_vcgen::generate_vcs(&func);

    let post: Vec<_> = vcs.iter().filter(|vc| matches!(vc.kind, VcKind::Postcondition)).collect();
    assert!(!post.is_empty(), "`is_whnf(result)` must emit at least one Postcondition VC");

    for vc in &post {
        let mut saw = false;
        vc.formula.visit(&mut |f| {
            if let Formula::Pred(name, args) = f
                && name.as_str() == "is_whnf"
            {
                saw = true;
                assert_eq!(args.len(), 1, "is_whnf is unary");
                assert_eq!(args[0].var_name(), Some("_0"), "applied to the return slot _0");
            }
        });
        assert!(saw, "emitted Postcondition VC must carry the opaque `is_whnf` predicate: {:?}", vc.formula);
    }
}

/// NEGATIVE CONTROL (no masquerade, mandatory): every emitted checker-core
/// Postcondition VC FAILS CLOSED under `trust_certify::certify_violation` —
/// `None`, never a false `Certified`. The opaque `is_whnf` predicate is outside
/// the solver's supported (linear-integer / disequality) discharge fragment, so
/// the negated postcondition is not refutable and no certificate is minted.
#[test]
fn checker_core_is_whnf_postcondition_fails_closed_under_certify() {
    let func = fn_with_ensures("is_whnf(result)");
    let vcs = trust_vcgen::generate_vcs(&func);
    let post: Vec<_> = vcs.iter().filter(|vc| matches!(vc.kind, VcKind::Postcondition)).collect();
    assert!(!post.is_empty(), "expected checker-core Postcondition VCs to gate");

    for vc in &post {
        assert!(
            trust_certify::certify_violation(&vc.formula).is_none(),
            "opaque checker-core `is_whnf(result)` must FAIL CLOSED (no false Certified); \
             formula was {:?}",
            vc.formula
        );
    }
}

/// DISCRIMINATION CONTROL: the SAME `certify_violation` is LIVE — it DOES mint a
/// kernel-checked `CleanCic` for a genuine single-variable interval contradiction
/// (`x >= 5 ∧ x <= 2`). This witnesses that the `None` above is genuine OPACITY
/// of the checker-core predicate, not a dead / always-`None` pipeline.
#[test]
fn certify_violation_is_live_on_a_real_contradiction() {
    let contradiction = Formula::And(vec![
        Formula::Ge(
            Box::new(Formula::var("x", Sort::Int)),
            Box::new(Formula::Int(5)),
        ),
        Formula::Le(
            Box::new(Formula::var("x", Sort::Int)),
            Box::new(Formula::Int(2)),
        ),
    ]);
    let evidence = trust_certify::certify_violation(&contradiction);
    assert!(
        matches!(evidence, Some(trust_ir::ProofEvidence::CleanCic { .. })),
        "certify_violation must discharge `x >= 5 ∧ x <= 2` to a kernel-checked CleanCic \
         (proves the fail-closed on `is_whnf` is discrimination, not a dead pipeline)"
    );
}
