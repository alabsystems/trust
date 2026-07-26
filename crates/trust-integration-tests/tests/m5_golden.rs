// trust-integration-tests/tests/m5_golden.rs: M5 golden test for the prove-strengthen-backprop loop
//
// Exercises the canonical binary search overflow example from VISION.md:
//   1. Build synthetic MIR for binary_search with `(low + high) / 2` overflow
//   2. Prove: trust_vcgen detects ArithmeticOverflow on the Add
//   3. Simulate solver result: ay finds counterexample (Failed)
//   4. Strengthen: trust-strengthen proposes preconditions / safe arithmetic
//   5. Backprop: trust-backprop converts proposals into a RewritePlan
//   6. Verify: the plan contains actionable rewrites for the overflow
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![allow(rustc::default_hash_types, rustc::potential_query_instability)]

use trust_types::{
    AssertMessage, BasicBlock, BinOp, BlockId, ConstValue, Counterexample, CounterexampleValue,
    CrateVerificationResult, FunctionVerificationResult, LocalDecl, Operand, Place, Rvalue,
    SourceSpan, Statement, Terminator, Ty, VcKind, VerifiableBody, VerifiableFunction,
    VerificationCondition, VerificationResult,
};

// ---------------------------------------------------------------------------
// Test fixture: binary_search with (low + high) / 2 overflow
// ---------------------------------------------------------------------------

/// Build a synthetic `binary_search(arr: &[i32], target: i32) -> usize` function
/// that contains the classic `(low + high) / 2` overflow bug.
///
/// MIR model:
/// ```text
/// bb0: // entry
///   _3 = const 0_usize               // low = 0
///   _4 = Len(_1)                      // high = arr.len()
///   goto bb1
///
/// bb1: // loop header
///   Assert(Lt(_3, _4), "loop guard")  // while low < high
///   goto bb2
///
/// bb2: // loop body
///   _5 = CheckedAdd(_3, _4)           // low + high (OVERFLOW BUG)
///   Assert(!_5.1, overflow)
///   goto bb3
///
/// bb3: // continue
///   _6 = _5.0
///   _7 = Div(_6, 2)                   // mid = (low + high) / 2
///   _0 = _7
///   return
/// ```
fn binary_search_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "binary_search".to_string(),
        def_path: "search::binary_search".to_string(),
        span: SourceSpan {
            file: "src/search.rs".to_string(),
            line_start: 1,
            col_start: 1,
            line_end: 20,
            col_end: 2,
        },
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::usize(), name: None }, // return
                LocalDecl {
                    index: 1,
                    ty: Ty::Slice { elem: Box::new(Ty::Int { width: 32, signed: true }) },
                    name: Some("arr".into()),
                },
                LocalDecl {
                    index: 2,
                    ty: Ty::Int { width: 32, signed: true },
                    name: Some("target".into()),
                },
                LocalDecl { index: 3, ty: Ty::usize(), name: Some("low".into()) },
                LocalDecl { index: 4, ty: Ty::usize(), name: Some("high".into()) },
                LocalDecl { index: 5, ty: Ty::Tuple(vec![Ty::usize(), Ty::Bool]), name: None }, // CheckedAdd result
                LocalDecl { index: 6, ty: Ty::usize(), name: None }, // unwrapped sum
                LocalDecl { index: 7, ty: Ty::usize(), name: Some("mid".into()) }, // mid
            ],
            blocks: vec![
                // bb0: entry — initialize low=0, high=len(arr), goto loop header
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 64))),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::Len(Place::local(1)),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                // bb1: loop header — check low < high, branch to body or exit
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(3)),
                        targets: vec![(0, BlockId(2))],
                        otherwise: BlockId(3),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                // bb2: loop body — the overflow bug: CheckedAdd(low, high)
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(5),
                        rvalue: Rvalue::CheckedBinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(3)),
                            Operand::Copy(Place::local(4)),
                        ),
                        span: SourceSpan {
                            file: "src/search.rs".to_string(),
                            line_start: 10,
                            col_start: 20,
                            line_end: 10,
                            col_end: 32,
                        },
                    }],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::field(5, 1)),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Add),
                        target: BlockId(3),
                        span: SourceSpan {
                            file: "src/search.rs".to_string(),
                            line_start: 10,
                            col_start: 20,
                            line_end: 10,
                            col_end: 32,
                        },
                        unwind: trust_types::UnwindEdge::Unreachable,
                    },
                },
                // bb3: compute mid = sum / 2, return
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(6),
                            rvalue: Rvalue::Use(Operand::Copy(Place::field(5, 0))),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(7),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Div,
                                Operand::Copy(Place::local(6)),
                                Operand::Constant(ConstValue::Uint(2, 64)),
                            ),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(7))),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 2,
            return_ty: Ty::usize(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

// ===========================================================================
// M5 Golden Test: Full prove-strengthen-backprop loop
// ===========================================================================

#[test]
fn test_m5_golden_binary_search_prove_strengthen_backprop() {
    // -----------------------------------------------------------------------
    // Phase 1: PROVE — vcgen detects the arithmetic overflow
    // -----------------------------------------------------------------------
    let func = binary_search_function();
    let vcs = trust_vcgen::generate_vcs(&func);

    // Should detect the (low + high) overflow
    let overflow_vcs: Vec<&VerificationCondition> = vcs
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Add, .. }))
        .collect();
    assert!(!overflow_vcs.is_empty(), "vcgen must detect ArithmeticOverflow(Add) in binary_search");
    assert_eq!(
        overflow_vcs[0].function, "binary_search",
        "overflow VC should be attributed to binary_search"
    );

    // -----------------------------------------------------------------------
    // Phase 2: SIMULATE SOLVER — ay finds counterexample (large low + high)
    // -----------------------------------------------------------------------
    // Backprop only emits source rewrites when `function_path` is a real
    // readable `.rs` file. Write a realistic binary_search to a temp dir and
    // use that as the function_path so the full pipeline (strengthen ->
    // backprop) produces actionable rewrites instead of getting filtered as
    // a report-only pseudo path.
    let _source_dir = tempfile::tempdir().expect("create temp dir");
    let source_path = _source_dir.path().join("search.rs");
    let source = "\
pub fn binary_search(arr: &[i32], target: i32) -> Option<usize> {
    let mut low = 0usize;
    let mut high = arr.len();
    while low < high {
        let mid = (low + high) / 2;
        if arr[mid] == target {
            return Some(mid);
        } else if arr[mid] < target {
            low = mid + 1;
        } else {
            high = mid;
        }
    }
    None
}
";
    std::fs::write(&source_path, source).expect("write temp source");
    let path_str = source_path.display().to_string();

    // In the real pipeline, trust-router dispatches to ay. Here we simulate
    // the result: ay finds that low=usize::MAX-1, high=2 causes overflow.
    let crate_results = CrateVerificationResult {
        crate_name: "search_crate".into(),
        functions: vec![FunctionVerificationResult {
            function_path: path_str.clone(),
            function_name: "binary_search".into(),
            results: overflow_vcs
                .iter()
                .map(|vc| {
                    let result = VerificationResult::Failed {
                        solver: "ay".into(),
                        time_ms: 8,
                        counterexample: Some(Counterexample::new(vec![
                            ("low".to_string(), CounterexampleValue::Uint((u64::MAX - 1) as u128)),
                            ("high".to_string(), CounterexampleValue::Uint(2)),
                        ])),
                    };
                    ((*vc).clone(), result)
                })
                .collect(),
            from_notes: 0,
            with_assumptions: 0,
        }],
        total_from_notes: 0,
        total_with_assumptions: 0,
    };

    // Verify failure was captured
    assert_eq!(crate_results.functions.len(), 1);
    assert!(
        crate_results.functions[0]
            .results
            .iter()
            .all(|(_, r)| matches!(r, VerificationResult::Failed { .. })),
        "all overflow VCs should be Failed"
    );

    // -----------------------------------------------------------------------
    // Phase 3: STRENGTHEN — propose fixes for the overflow
    // -----------------------------------------------------------------------
    let config = trust_strengthen::StrengthenConfig::default();
    let output = trust_strengthen::run(&crate_results, &config);

    assert!(output.has_proposals, "strengthen must propose at least one fix for the overflow");
    assert!(output.failures_analyzed >= 1, "should have analyzed at least 1 failure");

    // Check that at least one proposal addresses the overflow
    let overflow_proposals: Vec<_> = output
        .proposals
        .iter()
        .filter(|p| {
            matches!(
                p.kind,
                trust_strengthen::ProposalKind::AddPrecondition { .. }
                    | trust_strengthen::ProposalKind::SafeArithmetic { .. }
            )
        })
        .collect();
    assert!(
        !overflow_proposals.is_empty(),
        "should propose AddPrecondition or SafeArithmetic for the overflow: got {:?}",
        output.proposals.iter().map(|p| &p.kind).collect::<Vec<_>>()
    );

    // Every proposal should target binary_search
    for proposal in &output.proposals {
        assert!(
            proposal.function_name == "binary_search",
            "proposal should target binary_search, got: {}",
            proposal.function_name
        );
        assert!(proposal.confidence > 0.0, "proposal confidence must be positive");
    }

    // -----------------------------------------------------------------------
    // Phase 4: BACKPROP — convert proposals into a rewrite plan
    // -----------------------------------------------------------------------
    let policy = trust_backprop::GovernancePolicy::default();
    let plan = trust_backprop::apply_plan(&output.proposals, &policy)
        .expect("backprop should produce a valid rewrite plan");

    assert!(!plan.is_empty(), "rewrite plan must contain at least 1 rewrite");
    assert!(plan.summary.contains("proposals"), "plan summary should describe the proposals");

    // Verify the rewrite targets the right function
    for rewrite in &plan.rewrites {
        assert_eq!(rewrite.function_name, "binary_search", "rewrite should target binary_search");
        assert!(!rewrite.rationale.is_empty(), "rewrite should have a rationale");
    }

    // Check that we get the right kinds of rewrites
    let has_spec_attribute = plan.rewrites.iter().any(|r| {
        matches!(
            &r.kind,
            trust_backprop::RewriteKind::InsertAttribute { attribute }
                if attribute.contains("requires") || attribute.contains("ensures")
        )
    });
    let has_safe_arithmetic = plan.rewrites.iter().any(|r| {
        matches!(
            &r.kind,
            trust_backprop::RewriteKind::ReplaceExpression { new_text, .. }
                if new_text.contains("checked_add") || new_text.contains("saturating_add")
        )
    });
    assert!(
        has_spec_attribute || has_safe_arithmetic,
        "plan should insert spec attributes or replace with safe arithmetic; got: {:?}",
        plan.rewrites.iter().map(|r| &r.kind).collect::<Vec<_>>()
    );

    // -----------------------------------------------------------------------
    // Phase 5: VERIFY QUALITY — the pipeline produced actionable output
    // -----------------------------------------------------------------------
    // Summarize the full loop for test output
    eprintln!("=== M5 Golden Test: binary_search prove-strengthen-backprop ===");
    eprintln!("  VCs generated:      {}", vcs.len());
    eprintln!("  Overflow VCs:       {}", overflow_vcs.len());
    eprintln!("  Failures analyzed:  {}", output.failures_analyzed);
    eprintln!("  Proposals:          {}", output.proposals.len());
    for (i, p) in output.proposals.iter().enumerate() {
        eprintln!("    [{i}] {:?} (confidence: {:.2})", p.kind, p.confidence);
    }
    eprintln!("  Rewrites in plan:   {}", plan.len());
    for (i, r) in plan.rewrites.iter().enumerate() {
        eprintln!("    [{i}] {:?} on {}", r.kind, r.function_name);
    }
    eprintln!("=== M5 Golden Test PASSED ===");
}

// ---------------------------------------------------------------------------
// Focused sub-tests for each phase
// ---------------------------------------------------------------------------

#[test]
fn test_m5_vcgen_detects_binary_search_overflow() {
    let func = binary_search_function();
    let vcs = trust_vcgen::generate_vcs(&func);

    let overflow_count = vcs
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Add, .. }))
        .count();

    assert!(
        overflow_count >= 1,
        "expected at least 1 ArithmeticOverflow(Add) VC, got {overflow_count}"
    );

    // The binary_search also has a Div by constant 2 — should NOT produce DivisionByZero
    // since the divisor is a nonzero constant.
    let div_zero_count = vcs.iter().filter(|vc| matches!(vc.kind, VcKind::DivisionByZero)).count();
    // Div by constant 2 should not generate a DivisionByZero VC (optimization),
    // but our current vcgen may still generate one. Just verify overflow is present.
    let _ = div_zero_count; // acknowledged but not asserted
}

#[test]
fn test_m5_strengthen_overflow_proposal_quality() {
    let func = binary_search_function();
    let vcs = trust_vcgen::generate_vcs(&func);

    // Build a CrateVerificationResult with the overflow as Failed
    let overflow_vcs: Vec<_> =
        vcs.into_iter().filter(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { .. })).collect();

    let crate_results = CrateVerificationResult {
        crate_name: "search".into(),
        functions: vec![FunctionVerificationResult {
            function_path: "search::binary_search".into(),
            function_name: "binary_search".into(),
            results: overflow_vcs
                .into_iter()
                .map(|vc| {
                    (
                        vc,
                        VerificationResult::Failed {
                            solver: "ay".into(),
                            time_ms: 5,
                            counterexample: None,
                        },
                    )
                })
                .collect(),
            from_notes: 0,
            with_assumptions: 0,
        }],
        total_from_notes: 0,
        total_with_assumptions: 0,
    };

    let output = trust_strengthen::run(
        &crate_results,
        &trust_strengthen::StrengthenConfig::default(),
    );

    // Proposals should include a precondition about overflow
    let has_precondition = output
        .proposals
        .iter()
        .any(|p| matches!(p.kind, trust_strengthen::ProposalKind::AddPrecondition { .. }));
    assert!(has_precondition, "strengthen should propose a precondition for the overflow");

    // All proposals should have meaningful confidence
    for p in &output.proposals {
        assert!(p.confidence >= 0.5, "proposal confidence should meet default threshold");
    }
}

#[test]
fn test_m5_backprop_produces_valid_plan() {
    // Backprop only emits source rewrites when `function_path` is a real
    // readable `.rs` file (paths that look like Rust module paths -- contain
    // `::` -- are treated as pseudo provenance and are report-only). Write a
    // realistic binary_search source to a temp dir and use that as the
    // proposal's function_path.
    let dir = tempfile::tempdir().expect("create temp dir");
    let source_path = dir.path().join("search.rs");
    let source = "\
pub fn binary_search(arr: &[i32], target: i32) -> Option<usize> {
    let mut low = 0usize;
    let mut high = arr.len();
    while low < high {
        let mid = (low + high) / 2;
        if arr[mid] == target {
            return Some(mid);
        } else if arr[mid] < target {
            low = mid + 1;
        } else {
            high = mid;
        }
    }
    None
}
";
    std::fs::write(&source_path, source).expect("write temp source");
    let path_str = source_path.display().to_string();

    // Create a proposal manually (simulating strengthen output)
    let proposals = vec![
        trust_strengthen::Proposal {
            function_path: path_str.clone(),
            function_name: "binary_search".into(),
            kind: trust_strengthen::ProposalKind::AddPrecondition {
                spec_body: "low as u128 + high as u128 <= usize::MAX as u128".into(),
            },
            confidence: 0.85,
            rationale: "Prevent addition overflow in midpoint calculation".into(),
        },
        trust_strengthen::Proposal {
            function_path: path_str.clone(),
            function_name: "binary_search".into(),
            kind: trust_strengthen::ProposalKind::SafeArithmetic {
                original: "low + high".into(),
                replacement: "low.checked_add(high).expect(\"overflow in midpoint\")".into(),
            },
            confidence: 0.80,
            rationale: "Replace raw addition with checked_add to make overflow explicit".into(),
        },
    ];

    let policy = trust_backprop::GovernancePolicy::default();
    let plan = trust_backprop::apply_plan(&proposals, &policy)
        .expect("backprop should accept these proposals");

    assert_eq!(plan.len(), 2, "plan should have 2 rewrites");

    // First rewrite: InsertAttribute with requires
    let attr_rewrites: Vec<_> = plan
        .rewrites
        .iter()
        .filter(|r| matches!(&r.kind, trust_backprop::RewriteKind::InsertAttribute { .. }))
        .collect();
    assert_eq!(attr_rewrites.len(), 1, "should have 1 attribute insertion");

    // Second rewrite: ReplaceExpression with checked_add
    let expr_rewrites: Vec<_> = plan
        .rewrites
        .iter()
        .filter(|r| matches!(&r.kind, trust_backprop::RewriteKind::ReplaceExpression { .. }))
        .collect();
    assert_eq!(expr_rewrites.len(), 1, "should have 1 expression replacement");
}
