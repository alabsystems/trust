// trust_vcgen/unsafe_verify/tests.rs: Tests for unsafe code verification
//
// Part of #79, #137: Unsafe code verification
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashSet;

use super::detection::{
    attach_safety_comments, detect_unsafe_blocks, generate_inline_asm_vcs, generate_safety_vcs,
    has_raw_deref, is_unsafe_fn_call, parse_safety_comment,
};
use super::verifier::{
    UnsafeVerifier, classify_vc_from_assertion, deref_operand_name, generate_unsafe_vcs,
};
use super::*;

fn collect_free_vars(formula: &Formula) -> FxHashSet<String> {
    let mut vars = FxHashSet::default();
    collect_vars_recursive(formula, &mut vars);
    vars
}

fn collect_vars_recursive(formula: &Formula, vars: &mut FxHashSet<String>) {
    match formula {
        Formula::Var(name, _) => {
            vars.insert(name.clone());
        }
        _ => {
            for child in formula.children() {
                collect_vars_recursive(child, vars);
            }
        }
    }
}

fn is_conservative_or_concrete_check(formula: &Formula) -> bool {
    match formula {
        Formula::Bool(true) | Formula::Bool(false) => true,
        Formula::Eq(lhs, rhs) => {
            !matches!(lhs.as_ref(), Formula::Var(_, _))
                || !matches!(rhs.as_ref(), Formula::Var(_, _))
        }
        _ => false,
    }
}

/// Build a function with an unsafe ptr::read call.
fn unsafe_ptr_read_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "read_raw".to_string(),
        def_path: "test::read_raw".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u32()) },
                    name: Some("ptr".into()),
                },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("val".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "core::ptr::read".to_string(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(2),
                        target: Some(BlockId(1)),
                        span: SourceSpan {
                            file: "test.rs".into(),
                            line_start: 10,
                            col_start: 8,
                            line_end: 10,
                            col_end: 30,
                        },
                        atomic: None,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 1,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// Build a function with a raw pointer deref in a statement.
fn unsafe_deref_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "deref_raw".to_string(),
        def_path: "test::deref_raw".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u32()) },
                    name: Some("raw_ptr".into()),
                },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("value".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::Use(Operand::Copy(Place {
                        local: 1,
                        projections: vec![Projection::Deref],
                    })),
                    span: SourceSpan {
                        file: "test.rs".into(),
                        line_start: 5,
                        col_start: 4,
                        line_end: 5,
                        col_end: 15,
                    },
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// Build a safe function with no unsafe blocks.
fn safe_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "safe_add".to_string(),
        def_path: "test::safe_add".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("b".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Add,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// Build a function with a transmute call.
fn transmute_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "transmute_fn".to_string(),
        def_path: "test::transmute_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("input".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("output".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "core::mem::transmute".to_string(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(2),
                        target: Some(BlockId(1)),
                        span: SourceSpan {
                            file: "test.rs".into(),
                            line_start: 8,
                            col_start: 4,
                            line_end: 8,
                            col_end: 40,
                        },
                        atomic: None,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 1,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// Build a function with an FFI call.
fn ffi_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "call_ffi".to_string(),
        def_path: "test::call_ffi".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref {
                        mutable: false,
                        inner: Box::new(Ty::Int { width: 8, signed: false }),
                    },
                    name: Some("buf".into()),
                },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("result".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    // T5A: this fixture models a GENUINE extern import; the
                    // deleted "::ffi::" name entry used to detect it, so it now
                    // carries the authoritative `is_foreign` flag — exactly what
                    // extraction records for a libc import (round-19 #3).
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: true,
                        func: "libc::ffi::write".to_string(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(2),
                        target: Some(BlockId(1)),
                        span: SourceSpan {
                            file: "test.rs".into(),
                            line_start: 12,
                            col_start: 4,
                            line_end: 12,
                            col_end: 30,
                        },
                        atomic: None,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 1,
            return_ty: Ty::i32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

// ── Existing tests (preserved) ──────────────────────────────────────

#[test]
fn test_detect_unsafe_blocks_ptr_read() {
    let func = unsafe_ptr_read_function();
    let blocks = detect_unsafe_blocks(&func);
    assert_eq!(blocks.len(), 1, "should detect 1 unsafe block for ptr::read");
    assert_eq!(blocks[0].block_id, BlockId(0));
    assert_eq!(blocks[0].span.line_start, 10);
}

#[test]
fn test_detect_unsafe_blocks_deref() {
    let func = unsafe_deref_function();
    let blocks = detect_unsafe_blocks(&func);
    assert_eq!(blocks.len(), 1, "should detect 1 unsafe block for raw deref");
    assert_eq!(blocks[0].block_id, BlockId(0));
}

#[test]
fn test_detect_unsafe_blocks_safe_function() {
    let func = safe_function();
    let blocks = detect_unsafe_blocks(&func);
    assert!(blocks.is_empty(), "safe function should have no unsafe blocks");
}

#[test]
fn test_parse_safety_comment_single_line_because() {
    let comment = "// SAFETY: pointer is non-null because we checked it above";
    let claim = parse_safety_comment(comment);
    assert_eq!(claim.invariant, "pointer is non-null");
    assert_eq!(claim.justification, "we checked it above");
}

#[test]
fn test_parse_safety_comment_multiline() {
    let comment = "// SAFETY: pointer is valid and aligned\n// the caller guarantees this via the function contract";
    let claim = parse_safety_comment(comment);
    assert_eq!(claim.invariant, "pointer is valid and aligned");
    assert_eq!(claim.justification, "the caller guarantees this via the function contract");
}

#[test]
fn test_parse_safety_comment_invariant_only() {
    let comment = "// SAFETY: pointer is non-null";
    let claim = parse_safety_comment(comment);
    assert_eq!(claim.invariant, "pointer is non-null");
    assert_eq!(claim.justification, "no justification provided");
}

#[test]
fn test_parse_safety_comment_empty() {
    let claim = parse_safety_comment("");
    assert!(claim.invariant.is_empty());
    assert_eq!(claim.justification, "no justification provided");
}

#[test]
fn test_parse_safety_comment_no_prefix() {
    let comment = "// this is just a regular comment";
    let claim = parse_safety_comment(comment);
    // No SAFETY: prefix, so the whole comment becomes invariant
    assert_eq!(claim.invariant, "this is just a regular comment");
    assert_eq!(claim.justification, "no justification provided");
}

#[test]
fn test_generate_safety_vcs_with_claim() {
    let func = unsafe_ptr_read_function();
    let blocks = vec![UnsafeBlock {
        span: SourceSpan {
            file: "test.rs".into(),
            line_start: 10,
            col_start: 8,
            line_end: 10,
            col_end: 30,
        },
        safety_comment: Some("// SAFETY: pointer is non-null and aligned".into()),
        safety_claim: Some(SafetyClaim {
            invariant: "pointer is non-null and aligned".to_string(),
            justification: "no justification provided".to_string(),
        }),
        block_id: BlockId(0),
    }];

    let vcs = generate_safety_vcs(&func, &blocks, &FxHashSet::default());

    // Should produce: invariant VC + null check VC + alignment check VC
    assert_eq!(vcs.len(), 3, "claim with non-null + aligned = 3 VCs");

    // First VC: the invariant assertion
    assert!(matches!(&vcs[0].kind, VcKind::Assertion { message } if message.contains("[unsafe]")));
    assert!(
        matches!(&vcs[0].kind, VcKind::Assertion { message } if message.contains("SAFETY claim"))
    );

    // Second VC: null pointer check
    assert!(
        matches!(&vcs[1].kind, VcKind::Assertion { message } if message.contains("null pointer check"))
    );

    // Third VC: alignment check
    assert!(
        matches!(&vcs[2].kind, VcKind::Assertion { message } if message.contains("alignment check"))
    );

    // All should be L0Safety level
    for vc in &vcs {
        assert_eq!(vc.kind.proof_level(), ProofLevel::L0Safety);
    }
}

#[test]
fn generated_claim_pointer_cannot_alias_source_parameter() {
    let mut func = unsafe_ptr_read_function();
    // This legal source spelling was the old block-derived null-check symbol.
    func.body.locals[1].name = Some("ptr_0".into());
    func.preconditions = vec![Formula::Eq(
        Box::new(Formula::Var("ptr_0".into(), Sort::Int)),
        Box::new(Formula::Int(1)),
    )];
    let blocks = vec![UnsafeBlock {
        span: SourceSpan::default(),
        safety_comment: Some("// SAFETY: pointer is non-null".into()),
        safety_claim: Some(SafetyClaim {
            invariant: "pointer is non-null".into(),
            justification: "caller guarantees it".into(),
        }),
        block_id: BlockId(0),
    }];

    let vcs = generate_safety_vcs(&func, &blocks, &FxHashSet::default());
    let null_vc = vcs
        .iter()
        .find(|vc| {
            matches!(&vc.kind, VcKind::Assertion { message }
                if message.contains("null pointer check"))
        })
        .expect("non-null claim should emit a null check");
    let Formula::Eq(lhs, _) = &null_vc.formula else {
        panic!("null check should be an equality, got {:?}", null_vc.formula)
    };
    let Formula::Var(name, Sort::Int) = lhs.as_ref() else {
        panic!("null check lhs should be a generated integer variable")
    };
    assert_eq!(name, &generated_unsafe_symbol("claim_ptr_bb0"));
    assert_ne!(name, "ptr_0");
    assert_eq!(crate::place_to_var_name(&func, &Place::local(1)), "ptr_0");

    // Under the legacy spelling this was `ptr_0 == 1 ∧ ptr_0 == 0`, an
    // immediate false proof.  The actual cohabiting formula retains two
    // distinct leaves, so the source precondition cannot discharge the check.
    let combined = Formula::And(vec![func.preconditions[0].clone(), null_vc.formula.clone()]);
    let vars = combined.free_variables();
    assert!(vars.contains("ptr_0"));
    assert!(vars.contains(&generated_unsafe_symbol("claim_ptr_bb0")));
}

#[test]
fn test_safety_claim_vc_not_vacuously_true() {
    let func = unsafe_ptr_read_function();
    let blocks = vec![UnsafeBlock {
        span: SourceSpan {
            file: "test.rs".into(),
            line_start: 10,
            col_start: 8,
            line_end: 10,
            col_end: 30,
        },
        safety_comment: Some("// SAFETY: pointer is aligned".into()),
        safety_claim: Some(SafetyClaim {
            invariant: "pointer is aligned".to_string(),
            justification: "caller guarantees it".to_string(),
        }),
        block_id: BlockId(0),
    }];

    let vcs = generate_safety_vcs(&func, &blocks, &FxHashSet::default());
    assert_eq!(vcs.len(), 2, "claim + alignment check = 2 VCs");

    let alignment_vc = vcs
        .iter()
        .find(|vc| {
            matches!(
                &vc.kind,
                VcKind::Assertion { message } if message.contains("alignment check")
            )
        })
        .expect("alignment VC present");
    assert!(matches!(alignment_vc.formula, Formula::Bool(true)));
    assert!(matches!(
        &alignment_vc.kind,
        VcKind::Assertion { message } if message.contains("(unverified)")
    ));

    for vc in &vcs {
        let vars = collect_free_vars(&vc.formula);
        assert!(
            matches!(vc.formula, Formula::Bool(true) | Formula::Bool(false)) || vars.is_empty(),
            "safety claim VC should not leave free vars in a trivially dischargeable formula: {:?}",
            vc.formula
        );
    }
}

#[test]
fn test_generate_safety_vcs_without_claim() {
    let func = unsafe_ptr_read_function();
    let blocks = vec![UnsafeBlock {
        span: SourceSpan::default(),
        safety_comment: None,
        safety_claim: None,
        block_id: BlockId(0),
    }];

    let vcs = generate_safety_vcs(&func, &blocks, &FxHashSet::default());

    assert_eq!(vcs.len(), 1, "missing claim should produce 1 VC");
    assert!(matches!(
        &vcs[0].kind,
        VcKind::Assertion { message } if message.contains("missing SAFETY comment")
    ));
    // Missing SAFETY comment VC is always SAT (finding)
    assert!(matches!(vcs[0].formula, Formula::Bool(true)));
}

#[test]
fn test_generate_safety_vcs_skips_trusted_std_macro_span() {
    // A compiler/std-macro-generated unsafe block whose OWN span is in the sysroot
    // std tree (e.g. the `thread_local!` expansion's `unsafe { … }`, charged to the
    // ARENA closures `rational::ARENA::{constant#0}::{closure#0,1}`) is code the
    // user cannot annotate, so the documentation lint must NOT charge it — even
    // when the different-file skip is inapplicable (here the func span is
    // unknown/empty, so that skip is disabled, isolating the std-span exemption).
    let func = unsafe_ptr_read_function(); // span: SourceSpan::default() (empty file)
    let std_block = vec![UnsafeBlock {
        span: SourceSpan {
            file: "/private/tmp/trust-merge-wt/library/std/src/sys/thread_local/native/mod.rs"
                .to_string(),
            line_start: 92,
            col_start: 20,
            line_end: 98,
            col_end: 21,
        },
        safety_comment: None,
        safety_claim: None,
        block_id: BlockId(0),
    }];
    assert!(
        generate_safety_vcs(&func, &std_block, &FxHashSet::default()).is_empty(),
        "a std-macro-generated (sysroot-std-span) unsafe block must not be charged a \
         missing-SAFETY-comment documentation lint"
    );

    // SOUNDNESS BOUNDARY — a genuine first-party (ny-cert) unsafe block is NOT a std
    // span, so it STILL gets its fail-closed missing-SAFETY-comment lint.
    let user_block = vec![UnsafeBlock {
        span: SourceSpan {
            file: "crates/ny-cert/src/rational.rs".to_string(),
            line_start: 10,
            col_start: 4,
            line_end: 10,
            col_end: 20,
        },
        safety_comment: None,
        safety_claim: None,
        block_id: BlockId(0),
    }];
    assert_eq!(
        generate_safety_vcs(&func, &user_block, &FxHashSet::default()).len(),
        1,
        "a first-party unsafe block must keep its missing-SAFETY-comment lint"
    );
}

#[test]
fn test_generate_safety_vcs_never_reads_ambient_source_comments() {
    // Security regression: SourceSpan paths are descriptive metadata, not a
    // dependency-tracked source input. A same-named or subsequently edited file
    // must not suppress the fail-closed finding. Only comments explicitly passed
    // through `attach_safety_comments` may affect generated VCs.
    let dir = std::env::temp_dir().join(format!("trust_unsafe_safety_{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let documented = dir.join("documented.rs");
    let undocumented = dir.join("undocumented.rs");

    std::fs::write(
        &documented,
        "pub fn f(p: *const u8) -> u8 {\n    \
         // SAFETY: caller guarantees p is valid and aligned.\n    \
         unsafe { *p }\n}\n",
    )
    .unwrap();
    std::fs::write(
        &undocumented,
        "pub fn f(p: *const u8) -> u8 {\n    \
         // no documentation here\n    \
         unsafe { *p }\n}\n",
    )
    .unwrap();

    let func = unsafe_ptr_read_function();

    // Even a matching ambient comment must not suppress the finding.
    let documented_blocks = vec![UnsafeBlock {
        span: SourceSpan {
            file: documented.to_string_lossy().into_owned(),
            line_start: 3,
            col_start: 4,
            line_end: 3,
            col_end: 16,
        },
        safety_comment: None,
        safety_claim: None,
        block_id: BlockId(0),
    }];
    let documented_vcs = generate_safety_vcs(&func, &documented_blocks, &FxHashSet::default());
    assert!(
        documented_vcs
            .iter()
            .any(|vc| matches!(&vc.kind, VcKind::Assertion { message } if message.contains("missing SAFETY comment"))),
        "ambient // SAFETY: text must not bypass dependency-tracked comment extraction"
    );

    // Undocumented: same op layout but no SAFETY comment -> still flagged.
    let undocumented_blocks = vec![UnsafeBlock {
        span: SourceSpan {
            file: undocumented.to_string_lossy().into_owned(),
            line_start: 3,
            col_start: 4,
            line_end: 3,
            col_end: 16,
        },
        safety_comment: None,
        safety_claim: None,
        block_id: BlockId(0),
    }];
    let undocumented_vcs = generate_safety_vcs(&func, &undocumented_blocks, &FxHashSet::default());
    assert!(
        undocumented_vcs
            .iter()
            .any(|vc| matches!(&vc.kind, VcKind::Assertion { message } if message.contains("missing SAFETY comment"))),
        "genuinely undocumented unsafe must still be flagged (no false negative)"
    );

    let _ = std::fs::remove_file(&documented);
    let _ = std::fs::remove_file(&undocumented);
    let _ = std::fs::remove_dir(&dir);
}

#[test]
fn test_generate_safety_vcs_dropped_for_synthesized_box_deref_span() {
    // A raw-deref UnsafeBlock whose span the compiler flagged as a synthesized
    // Box deref (ElaborateBoxDerefs / drop-glue Transmute of a Box's Unique.NonNull
    // field) must NOT mint the always-Bool(true) "missing SAFETY comment" doc lint;
    // an otherwise identical first-party block (span NOT in the set) MUST still mint it.
    let func = unsafe_ptr_read_function();
    let block_span = SourceSpan {
        // No safety comment is attached and ambient source is never read
        // (dependency-tracked comment extraction is the only admitted input),
        // so nothing suppresses the lint; func.span is empty (default) ⇒ the
        // cross-file guard does not fire — the control path reaches the mint,
        // isolating the box-deref-set effect.
        file: "nonexistent_box_deref.rs".into(),
        line_start: 240,
        col_start: 44,
        line_end: 240,
        col_end: 54,
    };
    let blocks = vec![UnsafeBlock {
        span: block_span.clone(),
        safety_comment: None,
        safety_claim: None,
        block_id: BlockId(0),
    }];

    // Control: empty set ⇒ first-party unsafe still gets the doc lint.
    let empty = FxHashSet::default();
    let control = generate_safety_vcs(&func, &blocks, &empty);
    assert!(
        control.iter().any(|vc| matches!(
            &vc.kind,
            VcKind::Assertion { message } if message == MISSING_SAFETY_MSG
        )),
        "a first-party unsafe block (span NOT in the box-deref set) must still mint the missing-SAFETY lint"
    );

    // Fix: the SAME span present in the synthesized-box-deref set ⇒ lint dropped.
    let mut box_deref_spans = FxHashSet::default();
    box_deref_spans.insert(block_span.clone());
    let fixed = generate_safety_vcs(&func, &blocks, &box_deref_spans);
    assert!(
        !fixed.iter().any(|vc| matches!(
            &vc.kind,
            VcKind::Assertion { message } if message == MISSING_SAFETY_MSG
        )),
        "a synthesized Box-deref span in the set must drop the false missing-SAFETY lint (drop-only)"
    );

    // A DIFFERENT span in the set must NOT suppress this block (precision guard).
    let mut other = FxHashSet::default();
    other.insert(SourceSpan { file: "other.rs".into(), line_start: 1, col_start: 0, line_end: 1, col_end: 1 });
    let unaffected = generate_safety_vcs(&func, &blocks, &other);
    assert!(
        unaffected.iter().any(|vc| matches!(
            &vc.kind,
            VcKind::Assertion { message } if message == MISSING_SAFETY_MSG
        )),
        "an unrelated span in the set must not suppress a different block's lint"
    );
}

#[test]
fn test_generate_safety_vcs_never_brace_walks_ambient_source() {
    // Security regression for the former filesystem brace-walk: even when a
    // SourceSpan points inside a multi-line unsafe block whose source file has a
    // block-level SAFETY comment, vcgen must not reopen that path. Compiler-owned,
    // dependency-tracked comment extraction is the only admitted input.
    let dir =
        std::env::temp_dir().join(format!("trust_unsafe_block_safety_{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let file = dir.join("multiline.rs");
    std::fs::write(
        &file,
        concat!(
            "pub fn f(fd: i32) -> i32 {\n",
            "    // SAFETY: fd plumbing only; EBADF is errno, never UB.\n",
            "    unsafe {\n",
            "        let d = dup(fd);\n",
            "        if d < 0 {\n",
            "            let _ = close(d);\n",
            "        }\n",
            "        d\n",
            "    }\n",
            "}\n",
            "pub fn g(fd: i32) -> i32 {\n",
            "    fd + 1\n",
            "}\n",
        ),
    )
    .unwrap();

    let func = unsafe_ptr_read_function();
    let vc_for_line = |line: u32| {
        let blocks = vec![UnsafeBlock {
            span: SourceSpan {
                file: file.to_string_lossy().into_owned(),
                line_start: line,
                col_start: 8,
                line_end: line,
                col_end: 20,
            },
            safety_comment: None,
            safety_claim: None,
            block_id: BlockId(0),
        }];
        generate_safety_vcs(&func, &blocks, &FxHashSet::default())
    };

    // Op on line 4 (`dup`, directly under `unsafe {` on line 3): fail-closed.
    assert!(
        vc_for_line(4).iter().any(|vc| matches!(
            &vc.kind,
            VcKind::Assertion { message } if message.contains("missing SAFETY comment")
        )),
        "ambient block-level comments must not suppress an op below the unsafe opener"
    );
    // Op on line 6 (`close`, nested inside `if d < 0 {`): also fail-closed.
    assert!(
        vc_for_line(6).iter().any(|vc| matches!(
            &vc.kind,
            VcKind::Assertion { message } if message.contains("missing SAFETY comment")
        )),
        "ambient brace walking must not suppress an op nested in an inner block"
    );
    // Line 12 (`fd + 1` in `g`, outside any unsafe block in the fixture) is
    // likewise unaffected by ambient bytes; this synthetic UnsafeBlock remains
    // a finding.
    assert!(
        vc_for_line(12).iter().any(|vc| matches!(
            &vc.kind,
            VcKind::Assertion { message } if message.contains("missing SAFETY comment")
        )),
        "a closed earlier unsafe block's SAFETY comment must not document later code"
    );

    let _ = std::fs::remove_file(&file);
    let _ = std::fs::remove_dir(&dir);
}

#[test]
fn test_generate_safety_vcs_empty() {
    let func = safe_function();
    let blocks: Vec<UnsafeBlock> = vec![];
    let vcs = generate_safety_vcs(&func, &blocks, &FxHashSet::default());
    assert!(vcs.is_empty(), "no unsafe blocks = no VCs");
}

#[test]
fn test_attach_safety_comments_matches_by_span() {
    let mut blocks = vec![UnsafeBlock {
        span: SourceSpan {
            file: "test.rs".into(),
            line_start: 10,
            col_start: 8,
            line_end: 10,
            col_end: 30,
        },
        safety_comment: None,
        safety_claim: None,
        block_id: BlockId(0),
    }];

    let comments = vec![(
        SourceSpan {
            file: "test.rs".into(),
            line_start: 8,
            col_start: 4,
            line_end: 9,
            col_end: 50,
        },
        "// SAFETY: pointer is valid because caller guarantees it".to_string(),
    )];

    attach_safety_comments(&mut blocks, &comments);

    assert!(blocks[0].safety_comment.is_some());
    assert!(blocks[0].safety_claim.is_some());
    let claim = blocks[0].safety_claim.as_ref().unwrap();
    assert_eq!(claim.invariant, "pointer is valid");
    assert_eq!(claim.justification, "caller guarantees it");
}

#[test]
fn test_attach_safety_comments_selects_closest_independent_of_order() {
    let block = || UnsafeBlock {
        span: SourceSpan {
            file: "test.rs".into(),
            line_start: 10,
            col_start: 8,
            line_end: 10,
            col_end: 30,
        },
        safety_comment: None,
        safety_claim: None,
        block_id: BlockId(0),
    };
    let farther = (
        SourceSpan {
            file: "test.rs".into(),
            line_start: 8,
            col_start: 0,
            line_end: 8,
            col_end: 40,
        },
        "// SAFETY: pointer is non-null".to_string(),
    );
    let closer = (
        SourceSpan {
            file: "test.rs".into(),
            line_start: 9,
            col_start: 0,
            line_end: 9,
            col_end: 40,
        },
        "// SAFETY: pointer is aligned".to_string(),
    );

    for comments in [vec![farther.clone(), closer.clone()], vec![closer.clone(), farther.clone()]] {
        let mut blocks = vec![block()];
        attach_safety_comments(&mut blocks, &comments);
        assert_eq!(
            blocks[0].safety_claim.as_ref().map(|claim| claim.invariant.as_str()),
            Some("pointer is aligned"),
            "the closest comment must win regardless of input order"
        );
    }
}

#[test]
fn test_attach_safety_comments_equidistant_tie_is_deterministic() {
    let block = || UnsafeBlock {
        span: SourceSpan {
            file: "test.rs".into(),
            line_start: 10,
            col_start: 8,
            line_end: 10,
            col_end: 30,
        },
        safety_comment: None,
        safety_claim: None,
        block_id: BlockId(0),
    };
    let span = SourceSpan {
        file: "test.rs".into(),
        line_start: 9,
        col_start: 0,
        line_end: 9,
        col_end: 40,
    };
    let alpha = (span.clone(), "// SAFETY: alpha alignment".to_string());
    let zeta = (span, "// SAFETY: zeta non-null".to_string());

    for comments in [vec![zeta.clone(), alpha.clone()], vec![alpha.clone(), zeta.clone()]] {
        let mut blocks = vec![block()];
        attach_safety_comments(&mut blocks, &comments);
        assert_eq!(
            blocks[0].safety_claim.as_ref().map(|claim| claim.invariant.as_str()),
            Some("alpha alignment"),
            "equal source positions must use the stable lexical tie-break"
        );
    }
}

#[test]
fn test_attach_safety_comments_uses_parser_marker_grammar() {
    let block = || UnsafeBlock {
        span: SourceSpan {
            file: "test.rs".into(),
            line_start: 10,
            col_start: 8,
            line_end: 10,
            col_end: 30,
        },
        safety_comment: None,
        safety_claim: None,
        block_id: BlockId(0),
    };
    let span = SourceSpan {
        file: "test.rs".into(),
        line_start: 9,
        col_start: 0,
        line_end: 9,
        col_end: 40,
    };

    let mut spaced = vec![block()];
    attach_safety_comments(
        &mut spaced,
        &[(span.clone(), "// SAFETY : pointer is aligned".to_string())],
    );
    assert_eq!(
        spaced[0].safety_claim.as_ref().map(|claim| claim.invariant.as_str()),
        Some("pointer is aligned")
    );

    let mut embedded = vec![block()];
    attach_safety_comments(
        &mut embedded,
        &[(span, "// This prose mentions SAFETY: but is not a declaration".to_string())],
    );
    assert!(
        embedded[0].safety_claim.is_none(),
        "an embedded marker that the parser would not accept must fail closed"
    );
}

#[test]
fn test_attach_safety_comments_no_match_wrong_file() {
    let mut blocks = vec![UnsafeBlock {
        span: SourceSpan {
            file: "test.rs".into(),
            line_start: 10,
            col_start: 0,
            line_end: 10,
            col_end: 30,
        },
        safety_comment: None,
        safety_claim: None,
        block_id: BlockId(0),
    }];

    let comments = vec![(
        SourceSpan {
            file: "other.rs".into(),
            line_start: 9,
            col_start: 0,
            line_end: 9,
            col_end: 50,
        },
        "// SAFETY: this is in another file".to_string(),
    )];

    attach_safety_comments(&mut blocks, &comments);
    assert!(blocks[0].safety_comment.is_none(), "wrong file should not match");
}

#[test]
fn test_attach_safety_comments_no_match_too_far() {
    let mut blocks = vec![UnsafeBlock {
        span: SourceSpan {
            file: "test.rs".into(),
            line_start: 20,
            col_start: 0,
            line_end: 20,
            col_end: 30,
        },
        safety_comment: None,
        safety_claim: None,
        block_id: BlockId(0),
    }];

    let comments = vec![(
        SourceSpan {
            file: "test.rs".into(),
            line_start: 5,
            col_start: 0,
            line_end: 5,
            col_end: 50,
        },
        "// SAFETY: too far away".to_string(),
    )];

    attach_safety_comments(&mut blocks, &comments);
    assert!(blocks[0].safety_comment.is_none(), "comment too far should not match");
}

#[test]
fn test_is_unsafe_fn_call() {
    assert!(is_unsafe_fn_call("core::ptr::read"));
    assert!(is_unsafe_fn_call("std::ptr::write"));
    assert!(is_unsafe_fn_call("core::slice::from_raw_parts"));
    assert!(is_unsafe_fn_call("std::mem::transmute"));
    assert!(is_unsafe_fn_call("core::intrinsics::copy"));
    // T5A: "::ffi::" was a NAMESPACE match, not a fn match — it flagged safe
    // std::ffi paths (OsStr::to_str, …). Deleted; unsafe calls under ::ffi::
    // are now caught authoritatively via `Terminator::Call::is_unsafe_sig`,
    // and genuine extern imports via `is_foreign`.
    assert!(!is_unsafe_fn_call("some::ffi::extern_call"));
    assert!(is_unsafe_fn_call("alloc::alloc::alloc"));
    assert!(is_unsafe_fn_call("std::str::from_utf8_unchecked"));
    // Completeness: ops MODELED by sep_engine must also be DETECTED as unsafe, so
    // a block whose only unsafe op is one of these is still flagged/caught.
    assert!(is_unsafe_fn_call("core::slice::<impl [T]>::get_unchecked"));
    assert!(is_unsafe_fn_call("std::slice::<impl [T]>::get_unchecked_mut"));
    assert!(is_unsafe_fn_call("core::mem::MaybeUninit::<T>::assume_init"));
    assert!(is_unsafe_fn_call("std::vec::Vec::<T>::set_len"));
    assert!(is_unsafe_fn_call("core::ptr::NonNull::<T>::new_unchecked"));
    assert!(is_unsafe_fn_call("core::hint::unreachable_unchecked"));
    assert!(is_unsafe_fn_call("core::char::from_u32_unchecked"));
    assert!(!is_unsafe_fn_call("std::vec::Vec::push"));
    assert!(!is_unsafe_fn_call("core::result::Result::unwrap"));
    // Negative controls: safe APIs whose names are NEAR an unsafe pattern must
    // NOT be flagged (guard against the substring heuristic over-matching).
    assert!(!is_unsafe_fn_call("std::vec::Vec::len"));
    assert!(!is_unsafe_fn_call("core::option::Option::get_or_insert"));
}

#[test]
fn test_inline_asm_is_caught_fail_closed() {
    // Inline asm extracts to `Terminator::Opaque { kind: "InlineAsm" }`. It must
    // produce an always-finding obligation so it is CAUGHT, never silently
    // dropped — the completeness guarantee that no unsafe op escapes.
    let func = VerifiableFunction {
        name: "asm_fn".into(),
        def_path: "test::asm_fn".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            return_ty: Ty::Unit,
            locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
            arg_count: 0,
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Opaque {
                        kind: "InlineAsm".into(),
                        targets: vec![BlockId(1)],
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let vcs = generate_inline_asm_vcs(&func);
    assert_eq!(vcs.len(), 1, "inline asm must emit exactly one obligation");
    assert!(
        matches!(&vcs[0].kind, VcKind::Assertion { message } if message.contains("[unsafe:asm]")),
        "must be the [unsafe:asm] obligation, got {:?}",
        vcs[0].kind
    );
    assert_eq!(
        vcs[0].formula,
        Formula::Bool(true),
        "must be always-SAT (fail-closed): asm can never be proved safe without a model"
    );

    // A function with no asm produces no such obligation.
    let safe = VerifiableFunction {
        name: "safe".into(),
        def_path: "test::safe".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            return_ty: Ty::Unit,
            locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
            arg_count: 0,
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Return,
            }],
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    assert!(generate_inline_asm_vcs(&safe).is_empty(), "no asm ⇒ no asm obligation");
}

#[test]
fn test_has_raw_deref() {
    let raw_func = unsafe_deref_function();
    assert!(has_raw_deref(
        &raw_func,
        &Rvalue::Use(Operand::Copy(Place { local: 1, projections: vec![Projection::Deref] }))
    ));

    assert!(!has_raw_deref(&raw_func, &Rvalue::Use(Operand::Copy(Place::local(1)))));

    assert!(has_raw_deref(
        &raw_func,
        &Rvalue::Ref {
            mutable: false,
            place: Place { local: 1, projections: vec![Projection::Deref] },
        }
    ));

    let safe_ref_func = VerifiableFunction {
        name: "safe_ref".to_string(),
        def_path: "test::safe_ref".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref { mutable: false, inner: Box::new(Ty::u32()) },
                    name: Some("ptr".into()),
                },
            ],
            blocks: vec![],
            arg_count: 1,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    assert!(!has_raw_deref(
        &safe_ref_func,
        &Rvalue::Use(Operand::Copy(Place { local: 1, projections: vec![Projection::Deref] }))
    ));
    assert!(!has_raw_deref(
        &safe_ref_func,
        &Rvalue::Ref {
            mutable: false,
            place: Place { local: 1, projections: vec![Projection::Deref] },
        }
    ));
}

#[test]
fn test_check_unsafe_integration() {
    let func = unsafe_ptr_read_function();
    let comments = vec![(
        SourceSpan {
            file: "test.rs".into(),
            line_start: 9,
            col_start: 4,
            line_end: 9,
            col_end: 60,
        },
        "// SAFETY: pointer is non-null because allocated on the heap".to_string(),
    )];

    let mut vcs = Vec::new();
    check_unsafe(&func, &comments, &FxHashSet::default(), &mut vcs);

    // Should have VCs from the unsafe block with the attached comment
    assert!(!vcs.is_empty(), "should generate VCs for unsafe block");
    assert!(
        vcs.iter().any(|vc| matches!(
            &vc.kind,
            VcKind::Assertion { message } if message.contains("[unsafe]")
        )),
        "should have [unsafe] tagged assertions"
    );
}

#[test]
fn test_check_unsafe_safe_function_no_vcs() {
    let func = safe_function();
    let mut vcs = Vec::new();
    check_unsafe(&func, &[], &FxHashSet::default(), &mut vcs);
    assert!(vcs.is_empty(), "safe function should produce no unsafe VCs");
}

#[test]
fn test_check_unsafe_no_comments_produces_missing_vc() {
    let func = unsafe_ptr_read_function();
    let mut vcs = Vec::new();
    check_unsafe(&func, &[], &FxHashSet::default(), &mut vcs);

    assert_eq!(vcs.len(), 1, "unsafe block without comment = 1 missing-comment VC");
    assert!(matches!(
        &vcs[0].kind,
        VcKind::Assertion { message } if message.contains("missing SAFETY comment")
    ));
}

// ── New tests: UnsafeVcKind, UnsafeVerifier, generate_unsafe_vcs ──

#[test]
fn test_unsafe_vc_kind_descriptions() {
    let deref = UnsafeVcKind::RawPointerDeref { pointer_expr: "*ptr".into() };
    assert_eq!(deref.description(), "raw pointer dereference: *ptr");

    let transmute = UnsafeVcKind::Transmute { from_ty: "u32".into(), to_ty: "i32".into() };
    assert_eq!(transmute.description(), "transmute from u32 to i32");

    let union_access =
        UnsafeVcKind::UnionAccess { union_name: "MyUnion".into(), field_name: "value".into() };
    assert_eq!(union_access.description(), "union field access: MyUnion.value");

    let ffi = UnsafeVcKind::FfiCall { callee: "libc::write".into() };
    assert_eq!(ffi.description(), "FFI call to libc::write");

    let asm = UnsafeVcKind::InlineAsm { label: "cpuid".into() };
    assert_eq!(asm.description(), "inline assembly: cpuid");

    let mutable_static = UnsafeVcKind::MutableStaticAccess { static_name: "GLOBAL_STATE".into() };
    assert_eq!(mutable_static.description(), "mutable static access: GLOBAL_STATE");
}

#[test]
fn test_unsafe_vc_kind_serialization_roundtrip() {
    let kinds = vec![
        UnsafeVcKind::RawPointerDeref { pointer_expr: "*p".into() },
        UnsafeVcKind::Transmute { from_ty: "u32".into(), to_ty: "f32".into() },
        UnsafeVcKind::UnionAccess { union_name: "U".into(), field_name: "f".into() },
        UnsafeVcKind::FfiCall { callee: "libc::read".into() },
        UnsafeVcKind::InlineAsm { label: "nop".into() },
        UnsafeVcKind::MutableStaticAccess { static_name: "G".into() },
    ];

    for kind in &kinds {
        let json = serde_json::to_string(kind).expect("serialize UnsafeVcKind");
        let round: UnsafeVcKind = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(&round, kind);
    }
}

#[test]
fn test_unsafe_verifier_safe_function_empty() {
    let func = safe_function();
    let mut verifier = UnsafeVerifier::new(&func);
    assert_eq!(verifier.block_count(), 0);
    let vcs = verifier.generate();
    assert!(vcs.is_empty(), "safe function produces no unsafe VCs");
}

#[test]
fn test_unsafe_verifier_ptr_read_no_comments() {
    let func = unsafe_ptr_read_function();
    let mut verifier = UnsafeVerifier::new(&func);
    assert_eq!(verifier.block_count(), 1);
    let vcs = verifier.generate();

    // Should have: 1 missing-comment VC (from claim pass)
    // No typed VCs for ptr::read call (not a deref in stmts, it's a Call terminator)
    assert!(
        vcs.iter().any(|uvc| matches!(
            &uvc.vc.kind,
            VcKind::Assertion { message } if message.contains("missing SAFETY comment")
        )),
        "should have missing-comment VC"
    );
}

#[test]
fn test_unsafe_verifier_deref_generates_typed_vcs() {
    let func = unsafe_deref_function();
    let mut verifier = UnsafeVerifier::new(&func);
    assert_eq!(verifier.block_count(), 1);
    let vcs = verifier.generate();

    // Claim pass: 1 missing-comment VC
    // Typed pass: 3 VCs (null, alignment, bounds) for the deref
    assert_eq!(vcs.len(), 4, "1 missing-comment + 3 deref VCs = 4 total");

    // Check typed VCs
    let deref_vcs: Vec<_> = vcs
        .iter()
        .filter(|uvc| matches!(&uvc.unsafe_kind, UnsafeVcKind::RawPointerDeref { .. }))
        .collect();
    assert_eq!(deref_vcs.len(), 4, "all 4 VCs should be RawPointerDeref");

    // Check VC messages
    let messages: Vec<_> = vcs
        .iter()
        .map(|uvc| match &uvc.vc.kind {
            VcKind::Assertion { message } => message.clone(),
            _ => String::new(),
        })
        .collect();

    assert!(messages.iter().any(|m| m.contains("null check")));
    assert!(messages.iter().any(|m| m.contains("alignment check")));
    assert!(messages.iter().any(|m| m.contains("bounds check")));
}

#[test]
fn test_no_unconstrained_vars_in_deref_vcs() {
    let func = unsafe_deref_function();
    let mut verifier = UnsafeVerifier::new(&func);
    let vcs = verifier.generate();

    let deref_vcs: Vec<_> = vcs
        .iter()
        .filter(|unsafe_vc| matches!(&unsafe_vc.unsafe_kind, UnsafeVcKind::RawPointerDeref { .. }))
        .collect();
    assert!(!deref_vcs.is_empty(), "expected raw deref VCs");

    let bounds_vc = deref_vcs
        .iter()
        .find(|unsafe_vc| {
            matches!(
                &unsafe_vc.vc.kind,
                VcKind::Assertion { message } if message.contains("bounds check")
            )
        })
        .expect("bounds VC present");
    assert!(matches!(bounds_vc.vc.formula, Formula::Bool(true)));
    assert!(matches!(
        &bounds_vc.vc.kind,
        VcKind::Assertion { message } if message.contains("(unverified)")
    ));

    for unsafe_vc in &deref_vcs {
        let vars = collect_free_vars(&unsafe_vc.vc.formula);
        if !vars.is_empty() {
            assert!(
                is_conservative_or_concrete_check(&unsafe_vc.vc.formula),
                "deref VC contains unconstrained vars in unsafe shape: {:?}",
                unsafe_vc.vc.formula
            );
        }
    }
}

#[test]
fn test_unsafe_verifier_transmute_generates_layout_and_validity_vcs() {
    let func = transmute_function();
    let mut verifier = UnsafeVerifier::new(&func);
    assert_eq!(verifier.block_count(), 1);
    let vcs = verifier.generate();

    // Should have:
    // 1 missing-comment VC (from claim pass)
    // 2 transmute VCs (layout + validity)
    let transmute_vcs: Vec<_> = vcs
        .iter()
        .filter(|uvc| matches!(&uvc.unsafe_kind, UnsafeVcKind::Transmute { .. }))
        .collect();
    assert!(transmute_vcs.len() >= 2, "should have at least 2 transmute VCs");

    let messages: Vec<_> = transmute_vcs
        .iter()
        .map(|uvc| match &uvc.vc.kind {
            VcKind::Assertion { message } => message.clone(),
            _ => String::new(),
        })
        .collect();
    assert!(messages.iter().any(|m| m.contains("layout compatibility")));
    assert!(messages.iter().any(|m| m.contains("validity invariant")));
}

#[test]
fn test_no_unconstrained_vars_in_transmute_vcs() {
    let func = transmute_function();
    let mut verifier = UnsafeVerifier::new(&func);
    let vcs = verifier.generate();

    let transmute_vcs: Vec<_> = vcs
        .iter()
        .filter(|unsafe_vc| matches!(&unsafe_vc.unsafe_kind, UnsafeVcKind::Transmute { .. }))
        .collect();
    assert!(!transmute_vcs.is_empty(), "expected transmute VCs");

    let layout_vc = transmute_vcs
        .iter()
        .find(|unsafe_vc| {
            matches!(
                &unsafe_vc.vc.kind,
                VcKind::Assertion { message } if message.contains("layout compatibility")
            )
        })
        .expect("layout VC present");
    assert!(matches!(layout_vc.vc.formula, Formula::Bool(true)));
    assert!(matches!(
        &layout_vc.vc.kind,
        VcKind::Assertion { message } if message.contains("(unverified)")
    ));

    for unsafe_vc in &transmute_vcs {
        let vars = collect_free_vars(&unsafe_vc.vc.formula);
        if !vars.is_empty() {
            assert!(
                is_conservative_or_concrete_check(&unsafe_vc.vc.formula),
                "transmute VC contains unconstrained vars in unsafe shape: {:?}",
                unsafe_vc.vc.formula
            );
        }
    }
}

#[test]
fn test_unsafe_verifier_ffi_generates_pre_post_null_vcs() {
    let func = ffi_function();
    let mut verifier = UnsafeVerifier::new(&func);
    assert_eq!(verifier.block_count(), 1);
    let vcs = verifier.generate();

    let ffi_vcs: Vec<_> =
        vcs.iter().filter(|uvc| matches!(&uvc.unsafe_kind, UnsafeVcKind::FfiCall { .. })).collect();
    assert!(ffi_vcs.len() >= 3, "should have at least 3 FFI VCs");

    let messages: Vec<_> = ffi_vcs
        .iter()
        .map(|uvc| match &uvc.vc.kind {
            VcKind::Assertion { message } => message.clone(),
            _ => String::new(),
        })
        .collect();
    assert!(messages.iter().any(|m| m.contains("precondition")));
    assert!(messages.iter().any(|m| m.contains("postcondition")));
    assert!(messages.iter().any(|m| m.contains("null pointer argument")));
}

#[test]
fn test_no_unconstrained_vars_in_ffi_vcs() {
    let func = ffi_function();
    let mut verifier = UnsafeVerifier::new(&func);
    let vcs = verifier.generate();

    let ffi_vcs: Vec<_> = vcs
        .iter()
        .filter(|unsafe_vc| matches!(&unsafe_vc.unsafe_kind, UnsafeVcKind::FfiCall { .. }))
        .collect();
    assert!(!ffi_vcs.is_empty(), "expected FFI VCs");

    for unsafe_vc in &ffi_vcs {
        let vars = collect_free_vars(&unsafe_vc.vc.formula);
        if !vars.is_empty() {
            assert!(
                is_conservative_or_concrete_check(&unsafe_vc.vc.formula),
                "FFI VC contains unconstrained vars in unsafe shape: {:?}",
                unsafe_vc.vc.formula
            );
        }
    }
}

#[test]
fn test_generate_unsafe_vcs_entry_point() {
    let func = unsafe_deref_function();
    let vcs = generate_unsafe_vcs(&func, &[]);

    assert!(!vcs.is_empty(), "should produce VCs for unsafe function");
    // All VCs should have an unsafe_kind
    for uvc in &vcs {
        let _ = uvc.unsafe_kind.description();
    }
}

#[test]
fn test_generate_unsafe_vcs_with_comments() {
    let func = unsafe_ptr_read_function();
    let comments = vec![(
        SourceSpan {
            file: "test.rs".into(),
            line_start: 9,
            col_start: 4,
            line_end: 9,
            col_end: 60,
        },
        "// SAFETY: pointer is non-null because allocated on the heap".to_string(),
    )];

    let vcs = generate_unsafe_vcs(&func, &comments);

    // With a matching comment, we should get claim VCs (not missing-comment)
    assert!(
        vcs.iter().any(|uvc| matches!(
            &uvc.vc.kind,
            VcKind::Assertion { message } if message.contains("SAFETY claim")
        )),
        "should have SAFETY claim VC"
    );
    assert!(
        !vcs.iter().any(|uvc| matches!(
            &uvc.vc.kind,
            VcKind::Assertion { message } if message.contains("missing SAFETY comment")
        )),
        "should NOT have missing-comment VC when comment is present"
    );
}

#[test]
fn test_unsafe_verifier_with_comments_builder() {
    let func = unsafe_ptr_read_function();
    let comments = vec![(
        SourceSpan {
            file: "test.rs".into(),
            line_start: 9,
            col_start: 4,
            line_end: 9,
            col_end: 60,
        },
        "// SAFETY: pointer is non-null because allocated on the heap".to_string(),
    )];

    let mut verifier = UnsafeVerifier::new(&func).with_comments(comments);
    assert_eq!(verifier.block_count(), 1);
    let vcs = verifier.generate();
    assert!(!vcs.is_empty());
}

#[test]
fn test_classify_vc_from_assertion_transmute() {
    let vc = VerificationCondition {
        kind: VcKind::Assertion { message: "[unsafe:transmute] layout check".into() },
        function: "f".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };
    let kind = classify_vc_from_assertion(&vc);
    assert!(matches!(kind, UnsafeVcKind::Transmute { .. }));
}

#[test]
fn test_classify_vc_from_assertion_ffi() {
    let vc = VerificationCondition {
        kind: VcKind::Assertion { message: "[unsafe] FFI precondition".into() },
        function: "f".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };
    let kind = classify_vc_from_assertion(&vc);
    assert!(matches!(kind, UnsafeVcKind::FfiCall { .. }));
}

#[test]
fn test_classify_vc_from_assertion_default() {
    let vc = VerificationCondition {
        kind: VcKind::Assertion { message: "[unsafe] something generic".into() },
        function: "f".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
    };
    let kind = classify_vc_from_assertion(&vc);
    assert!(matches!(kind, UnsafeVcKind::RawPointerDeref { .. }));
}

#[test]
fn test_deref_operand_name() {
    let rvalue =
        Rvalue::Use(Operand::Copy(Place { local: 5, projections: vec![Projection::Deref] }));
    assert_eq!(deref_operand_name(&rvalue), "_5");

    let rvalue_ref = Rvalue::Ref {
        mutable: false,
        place: Place { local: 3, projections: vec![Projection::Deref] },
    };
    assert_eq!(deref_operand_name(&rvalue_ref), "_3");

    let rvalue_other = Rvalue::BinaryOp(
        BinOp::Add,
        Operand::Copy(Place::local(1)),
        Operand::Copy(Place::local(2)),
    );
    assert_eq!(deref_operand_name(&rvalue_other), "unknown");
}

// ---------------------------------------------------------------------------
// Regression: OP-IDENTITY suppression of the "[unsafe] missing SAFETY comment"
// documentation lint. This guards the certified-unsafe `get_unchecked`
// beachhead against the span-collision false-PROVE caught by adversarial audit:
// the lint is dropped ONLY for a block whose OWN terminator is a scalar-index
// slice/array `get_unchecked` (for which the sep engine emits the real
// `index >= len` obligation) — NEVER by span co-location. A blanket-only unsafe
// op (`mem::zeroed`) MUST keep its fail-closed lint. See
// `detection::block_is_bounds_complete_unchecked_index`.
// ---------------------------------------------------------------------------

const MISSING_SAFETY_MSG: &str = "[unsafe] missing SAFETY comment on unsafe block";

/// A single-block function whose Call terminator is `callee(recv, idx)`, with a
/// span pointing at a file that does not exist (so `source_has_preceding_safety_
/// comment` fails closed and the lint is emitted unless op-identity suppresses it).
fn unchecked_call_fn(callee: &str, recv_ty: Ty, idx_ty: Ty) -> VerifiableFunction {
    let span = SourceSpan {
        file: "nonexistent_trust_regression_test_file.rs".into(),
        line_start: 5,
        col_start: 4,
        line_end: 5,
        col_end: 24,
    };
    VerifiableFunction {
        name: "uc".to_string(),
        def_path: "test::uc".to_string(),
        span: span.clone(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: recv_ty, name: Some("s".into()) },
                LocalDecl { index: 2, ty: idx_ty, name: Some("i".into()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: Some("out".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: callee.to_string(),
                        args: vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
                        dest: Place::local(3),
                        target: Some(BlockId(1)),
                        span,
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn emits_missing_safety_lint(func: &VerifiableFunction) -> bool {
    let blocks = detect_unsafe_blocks(func);
    let vcs = generate_safety_vcs(func, &blocks, &FxHashSet::default());
    vcs.iter().any(
        |vc| matches!(&vc.kind, VcKind::Assertion { message } if message == MISSING_SAFETY_MSG),
    )
}

fn ref_slice_u8(mutable: bool) -> Ty {
    Ty::Ref { mutable, inner: Box::new(Ty::Slice { elem: Box::new(Ty::u8()) }) }
}

#[test]
fn get_unchecked_scalar_slice_suppresses_missing_safety_lint() {
    // The beachhead: the sep engine emits the real `index >= len` obligation, so
    // the always-`Bool(true)` doc lint is redundant and suppressed for this block.
    let func = unchecked_call_fn(
        "core::slice::<impl [T]>::get_unchecked",
        ref_slice_u8(false),
        Ty::usize(),
    );
    assert!(
        !emits_missing_safety_lint(&func),
        "scalar-index slice get_unchecked must suppress the doc lint (sep bounds obligation covers it)"
    );
}

#[test]
fn get_unchecked_mut_scalar_slice_suppresses_missing_safety_lint() {
    // `get_unchecked_mut` on `&mut [T]` is in the same bounds-complete envelope.
    let func = unchecked_call_fn(
        "core::slice::<impl [T]>::get_unchecked_mut",
        ref_slice_u8(true),
        Ty::usize(),
    );
    assert!(
        !emits_missing_safety_lint(&func),
        "scalar-index get_unchecked_mut must suppress the doc lint"
    );
}

#[test]
fn get_unchecked_array_receiver_suppresses_missing_safety_lint() {
    // Array receiver: the sep engine bounds by the concrete length `Int(N)`.
    let arr =
        Ty::Ref { mutable: false, inner: Box::new(Ty::Array { elem: Box::new(Ty::u8()), len: 8 }) };
    let func = unchecked_call_fn("core::slice::<impl [T]>::get_unchecked", arr, Ty::usize());
    assert!(
        !emits_missing_safety_lint(&func),
        "scalar-index array get_unchecked must suppress the doc lint"
    );
}

#[test]
fn mem_zeroed_retains_missing_safety_lint() {
    // THE AUDIT'S FALSE-PROVE CASE (must never regress): a blanket-only unsafe op
    // with NO bounds obligation must KEEP its fail-closed lint. Its terminator is
    // not a `get_unchecked`, so op-identity keying never suppresses it — even if
    // its source span byte-collided with a guarded index elsewhere.
    let func = unchecked_call_fn("core::mem::zeroed", ref_slice_u8(false), Ty::usize());
    assert!(
        emits_missing_safety_lint(&func),
        "mem::zeroed must retain its fail-closed lint — suppressing it would certify UB (false-PROVE)"
    );
}

#[test]
fn get_unchecked_non_scalar_index_retains_lint() {
    // A non-scalar index (a range `a..b` is a struct, not `Ty::Int`) is outside
    // the bounds-complete envelope: its precondition is `a <= b <= len`, not
    // `i < len`, so the lint must stay. `Ty::Bool` stands in for any non-int index.
    let func =
        unchecked_call_fn("core::slice::<impl [T]>::get_unchecked", ref_slice_u8(false), Ty::Bool);
    assert!(
        emits_missing_safety_lint(&func),
        "non-scalar-index get_unchecked must retain its lint"
    );
}

#[test]
fn get_unchecked_non_slice_receiver_retains_lint() {
    // A non-slice receiver (e.g. `str::get_unchecked`, extra char-boundary UB) is
    // outside the envelope; the lint stays (fail closed).
    let func = unchecked_call_fn("core::str::<impl str>::get_unchecked", Ty::u32(), Ty::usize());
    assert!(
        emits_missing_safety_lint(&func),
        "non-slice-receiver get_unchecked must retain its lint"
    );
}

// ---------------------------------------------------------------------------
// T5A: authoritative unsafe-call signal (`Terminator::Call::is_unsafe_sig`).
// The "::ffi::" NAMESPACE entry in `is_unsafe_fn_call` flagged SAFE std::ffi
// paths and demanded SAFETY comments on safe code (aterm-uds 4, aterm-types 2,
// aterm-pty up to 29 false demands). Detection now keys on the extraction-time
// signature-safety flag; the name list is only a synthetic-MIR fallback.
// ---------------------------------------------------------------------------

/// A single-block function calling `callee` with explicit `is_unsafe_sig` /
/// `is_foreign` flags, span pointing at a nonexistent file (comment lookup
/// fails closed, so the lint fires for every DETECTED block — isolating
/// detection behavior).
fn flagged_call_fn(callee: &str, is_unsafe_sig: bool, is_foreign: bool) -> VerifiableFunction {
    let span = SourceSpan {
        file: "nonexistent_trust_regression_test_file.rs".into(),
        line_start: 5,
        col_start: 4,
        line_end: 5,
        col_end: 24,
    };
    VerifiableFunction {
        name: "t5a".to_string(),
        def_path: "test::t5a".to_string(),
        span: span.clone(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig,
                        is_foreign,
                        func: callee.to_string(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span,
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn safe_std_ffi_path_call_is_not_detected_as_unsafe() {
    // THE T5A KILL. `OsStr::to_str` is a SAFE fn whose path contains "::ffi::".
    // Pre-fix this test FAILED: the "::ffi::" UNSAFE_PATTERNS entry matched the
    // namespace, detect_unsafe_blocks flagged the block, and a "[unsafe]
    // missing SAFETY comment" demand fired on 100%-safe code. Both
    // authoritative flags false (what extraction records for a safe, non-
    // foreign callee) must mean: no unsafe block, no demand.
    let func = flagged_call_fn("std::ffi::OsStr::to_str", false, false);
    assert!(
        detect_unsafe_blocks(&func).is_empty(),
        "safe std::ffi call (is_unsafe_sig=false, is_foreign=false) must not be detected as an unsafe block"
    );
    assert!(
        !emits_missing_safety_lint(&func),
        "safe std::ffi call must not demand a SAFETY comment (the aterm false-demand class)"
    );
}

#[test]
fn unsafe_sig_call_demands_safety_comment() {
    // The authoritative signal GAINS the demand the name list can no longer
    // supply for this path: same safe-LOOKING callee name, but extraction says
    // the signature is unsafe -> exactly one missing-SAFETY demand (no
    // comment reachable: the span file does not exist).
    let func = flagged_call_fn("std::ffi::OsStr::to_str", true, false);
    let blocks = detect_unsafe_blocks(&func);
    assert_eq!(blocks.len(), 1, "is_unsafe_sig=true must detect exactly the call block");
    let vcs = generate_safety_vcs(&func, &blocks, &FxHashSet::default());
    let demands = vcs
        .iter()
        .filter(
            |vc| matches!(&vc.kind, VcKind::Assertion { message } if message == MISSING_SAFETY_MSG),
        )
        .count();
    assert_eq!(
        demands, 1,
        "undocumented unsafe-sig call must fire exactly one missing-SAFETY demand"
    );
}

#[test]
fn foreign_call_still_demands_safety_comment() {
    // `is_foreign` (round-19 #3, the authoritative FFI signal) keeps its
    // demand: a body-less extern import with an arbitrary name — invisible to
    // the name heuristic — is an unsafe boundary and must stay flagged.
    let func = flagged_call_fn("compute_hash", false, true);
    assert_eq!(
        detect_unsafe_blocks(&func).len(),
        1,
        "is_foreign=true must detect the call block regardless of the callee name"
    );
    assert!(
        emits_missing_safety_lint(&func),
        "undocumented foreign call must keep its missing-SAFETY demand"
    );
}

#[test]
fn synthetic_mir_name_fallback_still_detects_known_unsafe_names() {
    // Serde-default world (both flags false, e.g. old serialized MIR or
    // synthetic fixtures): the name list must still catch its known-unsafe
    // fns, or every existing synthetic fixture silently loses coverage.
    let func = flagged_call_fn("core::ptr::read", false, false);
    assert_eq!(
        detect_unsafe_blocks(&func).len(),
        1,
        "name fallback must still detect core::ptr::read when both flags are serde-default false"
    );
}
