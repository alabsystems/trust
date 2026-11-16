// trust_vcgen/unsafe_verify/tests.rs: Tests for unsafe code verification
//
// Part of #79: Unsafe code verification
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashSet;

use super::detection::{
    attach_safety_comments, detect_unsafe_blocks, generate_inline_asm_vcs, generate_safety_vcs,
    has_raw_deref, is_unsafe_fn_call, parse_safety_comment,
};
use super::*;

/// The symbol an unsafe-family formula variable would carry, for asserting
/// that no such variable leaks into a row.
fn generated_unsafe_symbol(unqualified: &str) -> String {
    crate::generated_formula_symbol("unsafe", unqualified)
}

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
                        callee_identity: None,
                        callee_key: crate::sep_engine::tests::fixture_key("core::ptr::read"),
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
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
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
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
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
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
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
        origin: UnsafeOrigin::Call { is_unsafe_sig: false, is_foreign: false },
    }];

    let vcs =
        generate_safety_vcs(&func, &blocks, &FxHashSet::default(), &UnsafeCoverage::default());

    // Exactly the invariant row. The two prose-triggered follow-ups ("null pointer
    // check" on "non-null", "alignment check" on "align") were deleted at the
    // mint: an unconstrained fresh variable and a `Bool(true)` constrain nothing
    // and refuted a block harder the better its comment was written.
    assert_eq!(vcs.len(), 1, "claim = 1 VC (no prose-triggered follow-up rows)");
    assert!(matches!(&vcs[0].kind, VcKind::Assertion { message } if message.contains("[unsafe]")));
    assert!(
        matches!(&vcs[0].kind, VcKind::Assertion { message } if message.contains("SAFETY claim"))
    );
    assert!(matches!(vcs[0].formula, Formula::Bool(true)));
    assert_eq!(vcs[0].kind.proof_level(), ProofLevel::L0Safety);
}

#[test]
fn a_non_null_claim_mints_no_prose_null_row() {
    // The retired "null pointer check" row keyed on the substring "non-null" and
    // compared a fresh, unconstrained generated symbol (`claim_ptr_bb0`) with 0:
    // always SAT, never connected to the pointer it named. A comment stating the
    // invariant must not add a refutation the block's own operation does not owe.
    let mut func = unsafe_ptr_read_function();
    func.body.locals[1].name = Some("ptr_0".into());
    let blocks = vec![UnsafeBlock {
        span: SourceSpan::default(),
        safety_comment: Some("// SAFETY: pointer is non-null".into()),
        safety_claim: Some(SafetyClaim {
            invariant: "pointer is non-null".into(),
            justification: "caller guarantees it".into(),
        }),
        block_id: BlockId(0),
        origin: UnsafeOrigin::Call { is_unsafe_sig: false, is_foreign: false },
    }];

    let vcs =
        generate_safety_vcs(&func, &blocks, &FxHashSet::default(), &UnsafeCoverage::default());
    assert_eq!(vcs.len(), 1);
    assert!(
        !vcs.iter().any(|vc| matches!(&vc.kind, VcKind::Assertion { message }
            if message.contains("null pointer check"))),
        "no prose-triggered null row"
    );
    let vars = collect_free_vars(&vcs[0].formula);
    assert!(!vars.contains(&generated_unsafe_symbol("claim_ptr_bb0")));
    assert!(!vars.contains("ptr_0"));
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
        origin: UnsafeOrigin::Call { is_unsafe_sig: false, is_foreign: false },
    }];

    let vcs =
        generate_safety_vcs(&func, &blocks, &FxHashSet::default(), &UnsafeCoverage::default());
    assert_eq!(vcs.len(), 1, "claim only (the prose-triggered alignment row was deleted)");
    assert!(
        !vcs.iter().any(|vc| matches!(&vc.kind, VcKind::Assertion { message }
            if message.contains("alignment check"))),
        "no prose-triggered alignment row"
    );

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
        origin: UnsafeOrigin::Call { is_unsafe_sig: false, is_foreign: false },
    }];

    let vcs =
        generate_safety_vcs(&func, &blocks, &FxHashSet::default(), &UnsafeCoverage::default());

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
    //
    // AUTHENTICATED SINCE 2026-09-20: the exemption is bought by the compiler's
    // `TrustedStdSourceFiles` table (artifact residency, keyed on
    // `SourceFile::cnum`), not by the shape of the path. The table below is what
    // a real compilation would install for this file; the arm AFTER the
    // soundness boundary compiles the IDENTICAL path with the table absent and
    // shows the lint comes back.
    let func = unsafe_ptr_read_function(); // span: SourceSpan::default() (empty file)
    const STD_TLS_FILE: &str =
        "/private/tmp/trust-merge-wt/library/std/src/sys/thread_local/native/mod.rs";
    let authenticated = trust_types::TrustedStdSourceFiles::from_authenticated_files([(
        STD_TLS_FILE.to_string(),
        true,
    )]);
    let std_block = vec![UnsafeBlock {
        span: SourceSpan {
            file: STD_TLS_FILE.to_string(),
            line_start: 92,
            col_start: 20,
            line_end: 98,
            col_end: 21,
        },
        safety_comment: None,
        safety_claim: None,
        block_id: BlockId(0),
        origin: UnsafeOrigin::Call { is_unsafe_sig: false, is_foreign: false },
    }];
    let authenticated_ctx = crate::VcgenContext::for_function(func.def_path.clone())
        .with_trusted_std_source_files(authenticated);
    let std_vcs = crate::with_function_vcgen_context(&func.def_path, &authenticated_ctx, || {
        generate_safety_vcs(&func, &std_block, &FxHashSet::default(), &UnsafeCoverage::default())
    });
    assert!(
        std_vcs.is_empty(),
        "a std-macro-generated (sysroot-std-span) unsafe block must not be charged a \
         missing-SAFETY-comment documentation lint: {std_vcs:?}"
    );

    // THE FILE-PATH KEY IS GONE. With NO authenticated table installed, the
    // BYTE-IDENTICAL span — `library/std/src/…`, the exact shape the deleted
    // `is_trusted_std_file` accepted — buys nothing and the lint is charged.
    // FAILS ON UNFIXED CODE, where the path alone was the whole decision.
    assert_eq!(
        generate_safety_vcs(&func, &std_block, &FxHashSet::default(), &UnsafeCoverage::default())
            .len(),
        1,
        "a `library/std/src/…` path with no authenticated table behind it must keep its \
         fail-closed lint"
    );

    // Enabling behavioral memory-safety rows for a local stdlib SUBJECT must
    // not broaden the separate source-documentation lint. The same std block
    // remains user-unannotatable and therefore yields no documentation VC even
    // inside the exact-owner context that unsuppresses sep-engine rows.
    let stdlib_subject = crate::VcgenContext::for_function(func.def_path.clone())
        .with_stdlib_subject_memory_safety(true)
        .with_trusted_std_source_files(
            trust_types::TrustedStdSourceFiles::from_authenticated_files([(
                STD_TLS_FILE.to_string(),
                true,
            )]),
        );
    let subject_std_vcs =
        crate::with_function_vcgen_context(&func.def_path, &stdlib_subject, || {
            generate_safety_vcs(
                &func,
                &std_block,
                &FxHashSet::default(),
                &UnsafeCoverage::default(),
            )
        });
    assert!(
        subject_std_vcs.is_empty(),
        "stdlib-subject behavioral policy must not charge the separate \
         missing-SAFETY-comment documentation lint: {subject_std_vcs:?}"
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
        origin: UnsafeOrigin::Call { is_unsafe_sig: false, is_foreign: false },
    }];
    let subject_user_vcs =
        crate::with_function_vcgen_context(&func.def_path, &stdlib_subject, || {
            generate_safety_vcs(
                &func,
                &user_block,
                &FxHashSet::default(),
                &UnsafeCoverage::default(),
            )
        });
    assert_eq!(
        subject_user_vcs.len(),
        1,
        "a first-party unsafe block must keep its missing-SAFETY-comment lint \
         under stdlib-subject behavioral policy"
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
        origin: UnsafeOrigin::Call { is_unsafe_sig: false, is_foreign: false },
    }];
    let documented_vcs = generate_safety_vcs(
        &func,
        &documented_blocks,
        &FxHashSet::default(),
        &UnsafeCoverage::default(),
    );
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
        origin: UnsafeOrigin::Call { is_unsafe_sig: false, is_foreign: false },
    }];
    let undocumented_vcs = generate_safety_vcs(
        &func,
        &undocumented_blocks,
        &FxHashSet::default(),
        &UnsafeCoverage::default(),
    );
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

/// Locals: `_1: &Box<u32>` (arg), `_2: *const u32` (the pointer
/// `ElaborateBoxDerefs` synthesises), `_3: u32`, `_4: *const u32` (arg),
/// `_5: u32`, `_6: &u32`. One block; every operation carries the SAME span
/// (`span`), exactly as a proc-macro `Span::call_site()` expansion stamps them:
/// `[0] _2 = Cast(Copy((*_1).0.0))`, `[1] _3 = *_2` (the synthesized box
/// deref), `[2] _5 = *_4` (a user deref of a parameter), terminator
/// `_6 = core::mem::zeroed::<&u32>()`.
fn synthesized_box_deref_fixture(span: &SourceSpan) -> VerifiableFunction {
    let global = struct_ty("alloc::alloc::Global", vec![]);
    let boxed = struct_ty("alloc::boxed::Box", vec![("0", raw(Ty::u32())), ("1", global)]);
    VerifiableFunction {
        name: "eval".to_string(),
        def_path: "test::eval".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: reference(boxed), name: Some("b".into()) },
                LocalDecl { index: 2, ty: raw(Ty::u32()), name: None },
                LocalDecl { index: 3, ty: Ty::u32(), name: None },
                LocalDecl { index: 4, ty: raw(Ty::u32()), name: Some("p".into()) },
                LocalDecl { index: 5, ty: Ty::u32(), name: None },
                LocalDecl { index: 6, ty: reference(Ty::u32()), name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::Cast(
                                Operand::Copy(Place {
                                    local: 1,
                                    projections: vec![
                                        Projection::Deref,
                                        Projection::Field(0),
                                        Projection::Field(0),
                                    ],
                                }),
                                raw(Ty::u32()),
                            ),
                            span: span.clone(),
                        },
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::Use(Operand::Copy(Place {
                                local: 2,
                                projections: vec![Projection::Deref],
                            })),
                            span: span.clone(),
                        },
                        Statement::Assign {
                            place: Place::local(5),
                            rvalue: Rvalue::Use(Operand::Copy(Place {
                                local: 4,
                                projections: vec![Projection::Deref],
                            })),
                            span: span.clone(),
                        },
                    ],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: true,
                        callee_identity: None,
                        callee_key: crate::sep_engine::tests::fixture_key(
                            "core::mem::zeroed::<&u32>",
                        ),
                        is_foreign: false,
                        func: "core::mem::zeroed::<&u32>".to_string(),
                        args: vec![],
                        dest: Place::local(6),
                        target: Some(BlockId(1)),
                        span: span.clone(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: Ty::u32(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

#[test]
fn test_generate_safety_vcs_dropped_for_synthesized_box_deref_span() {
    // A raw-deref STATEMENT of the pointer ElaborateBoxDerefs synthesises
    // (`Cast` of a Box's `.0:Unique.0:NonNull`), whose OPERATION the compiler
    // collected, must NOT mint the always-Bool(true) "missing SAFETY comment"
    // stand-in — and nothing else may be dropped with it.
    //
    // THE SET IS KEYED ON `(BlockId, statement index)` SINCE 2026-09-20. All
    // three operations below share ONE span, which is what a proc-macro
    // `Span::call_site()` expansion produces; under the old `SourceSpan` key
    // the set could not say which operation it meant. `func.span` is empty
    // (default) so the cross-file guard does not fire and the control path
    // reaches the mint, isolating the box-deref-set effect.
    let block_span = SourceSpan {
        file: "nonexistent_box_deref.rs".into(),
        line_start: 240,
        col_start: 44,
        line_end: 240,
        col_end: 54,
    };
    let func = synthesized_box_deref_fixture(&block_span);
    let blocks = detect_unsafe_blocks(&func);
    assert_eq!(blocks.len(), 3, "the call, the box deref and the user deref: {blocks:?}");
    let rows = |set: &FxHashSet<(BlockId, usize)>| -> Vec<String> {
        generate_safety_vcs(&func, &blocks, set, &UnsafeCoverage::default())
            .into_iter()
            .map(|vc| match vc.kind {
                VcKind::Assertion { message } => message,
                other => panic!("unexpected kind {other:?}"),
            })
            .collect()
    };

    // Control: empty set ⇒ every site keeps its obligation (the call its typed
    // refutation, both derefs the stand-in).
    let control = rows(&FxHashSet::default());
    assert_eq!(control.len(), 3, "{control:?}");
    assert!(control[0].starts_with("[unsafe:zeroed]"), "{control:?}");
    assert_eq!(&control[1..], [MISSING_SAFETY_MSG, MISSING_SAFETY_MSG]);

    // Fix: the synthesized deref's OPERATION — block 0, statement 1 — in the
    // set ⇒ ONLY that statement is dropped. The same-span user deref (block 0,
    // statement 2) keeps its stand-in and the same-span CALL keeps its typed
    // refutation, because neither is that operation.
    let mut box_deref_ops = FxHashSet::default();
    box_deref_ops.insert((BlockId(0), 1));
    let fixed = rows(&box_deref_ops);
    assert_eq!(fixed.len(), 2, "{fixed:?}");
    assert!(fixed[0].starts_with("[unsafe:zeroed]"), "{fixed:?}");
    assert_eq!(fixed[1], MISSING_SAFETY_MSG);

    // A DIFFERENT OPERATION in the set must NOT suppress anything, even though
    // it carries the very same span. This is the assertion a span key cannot
    // make: statement 2 is the user deref, statement 0 is the box-ptr cast, and
    // block 1 has no statements at all.
    for other_op in [(BlockId(0), 0), (BlockId(0), 2), (BlockId(1), 1), (BlockId(7), 1)] {
        let mut other = FxHashSet::default();
        other.insert(other_op);
        assert_eq!(rows(&other), control, "{other_op:?}");
    }

    // The shape check is exact: with the pointer local's definition no longer
    // a cast of a Box's two-field projection (a Box-typed base is required),
    // the nominated statement is not the synthesized shape and keeps its row.
    let mut not_a_box = func.clone();
    not_a_box.body.locals[1].ty = reference(struct_ty("test::NotABox", vec![]));
    let blocks2 = detect_unsafe_blocks(&not_a_box);
    let kept =
        generate_safety_vcs(&not_a_box, &blocks2, &box_deref_ops, &UnsafeCoverage::default());
    assert_eq!(kept.len(), 3, "{kept:?}");
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
            origin: UnsafeOrigin::Call { is_unsafe_sig: false, is_foreign: false },
        }];
        generate_safety_vcs(&func, &blocks, &FxHashSet::default(), &UnsafeCoverage::default())
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
    let vcs =
        generate_safety_vcs(&func, &blocks, &FxHashSet::default(), &UnsafeCoverage::default());
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
        origin: UnsafeOrigin::Call { is_unsafe_sig: false, is_foreign: false },
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
        origin: UnsafeOrigin::Call { is_unsafe_sig: false, is_foreign: false },
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
        origin: UnsafeOrigin::Call { is_unsafe_sig: false, is_foreign: false },
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
        origin: UnsafeOrigin::Call { is_unsafe_sig: false, is_foreign: false },
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
        origin: UnsafeOrigin::Call { is_unsafe_sig: false, is_foreign: false },
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
        origin: UnsafeOrigin::Call { is_unsafe_sig: false, is_foreign: false },
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
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
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
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
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
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
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
    check_unsafe(&func, &comments, &FxHashSet::default(), &UnsafeCoverage::default(), &mut vcs);

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
    check_unsafe(&func, &[], &FxHashSet::default(), &UnsafeCoverage::default(), &mut vcs);
    assert!(vcs.is_empty(), "safe function should produce no unsafe VCs");
}

#[test]
fn test_check_unsafe_no_comments_produces_missing_vc() {
    let func = unsafe_ptr_read_function();
    let mut vcs = Vec::new();
    check_unsafe(&func, &[], &FxHashSet::default(), &UnsafeCoverage::default(), &mut vcs);

    assert_eq!(vcs.len(), 1, "unsafe block without comment = 1 missing-comment VC");
    assert!(matches!(
        &vcs[0].kind,
        VcKind::Assertion { message } if message.contains("missing SAFETY comment")
    ));
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
                        callee_identity: None,
                        callee_key: crate::sep_engine::tests::fixture_key(&callee.to_string()),
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
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// The coverage the separation engine produces for `unchecked_call_fn`: its
/// `VcKind::UncheckedIndexBounds` row, minted while interpreting `bb0`'s
/// terminator. The supersession is MEASURED against this, not predicted.
fn unchecked_index_coverage(func: &VerifiableFunction) -> UnsafeCoverage {
    let mut coverage = UnsafeCoverage::default();
    coverage.record_sep_row(
        &VerificationCondition {
            kind: VcKind::UncheckedIndexBounds {
                callee: "core::slice::<impl [T]>::get_unchecked".into(),
                detail: "unchecked index must be < the container length in uc".into(),
            },
            function: func.name.as_str().into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
            obligation: None,
        },
        BlockId(0),
        MirOp::Terminator,
    );
    coverage
}

fn emits_missing_safety_lint_under(func: &VerifiableFunction, coverage: &UnsafeCoverage) -> bool {
    let blocks = detect_unsafe_blocks(func);
    let vcs = generate_safety_vcs(func, &blocks, &FxHashSet::default(), coverage);
    vcs.iter().any(
        |vc| matches!(&vc.kind, VcKind::Assertion { message } if message == MISSING_SAFETY_MSG),
    )
}

fn emits_missing_safety_lint(func: &VerifiableFunction) -> bool {
    emits_missing_safety_lint_under(func, &unchecked_index_coverage(func))
}

#[test]
fn get_unchecked_supersession_requires_the_engines_row_to_have_been_minted() {
    // The shape predicate alone is a PREDICTION of the engine's
    // `UncheckedIndexBounds` row. With no such row recorded for this block's
    // terminator (the engine declined the body, or its own recognizer did not
    // match), the stand-in is kept.
    let func = unchecked_call_fn(
        "core::slice::<impl [T]>::get_unchecked",
        ref_slice_u8(false),
        Ty::usize(),
    );
    assert!(emits_missing_safety_lint_under(&func, &UnsafeCoverage::default()));
    // The row recorded for a STATEMENT of the block, or for another block, does
    // not count either.
    let row = VerificationCondition {
        kind: VcKind::UncheckedIndexBounds { callee: "x".into(), detail: "y".into() },
        function: func.name.as_str().into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(true),
        contract_metadata: None,
        obligation: None,
    };
    let mut stmt = UnsafeCoverage::default();
    stmt.record_sep_row(&row, BlockId(0), MirOp::Statement(0));
    assert!(emits_missing_safety_lint_under(&func, &stmt));
    let mut other = UnsafeCoverage::default();
    other.record_sep_row(&row, BlockId(1), MirOp::Terminator);
    assert!(emits_missing_safety_lint_under(&func, &other));
    // Recorded for this block's terminator: superseded.
    assert!(!emits_missing_safety_lint(&func));
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
                        callee_identity: None,
                        callee_key: crate::sep_engine::tests::fixture_key(&callee.to_string()),
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
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn flagged_tail_call_fn(callee: &str, is_unsafe_sig: bool, is_foreign: bool) -> VerifiableFunction {
    let mut func = flagged_call_fn(callee, is_unsafe_sig, is_foreign);
    let Terminator::Call { func: callee, args, span, atomic, callee_identity, callee_key, .. } =
        func.body.blocks[0].terminator.clone()
    else {
        unreachable!();
    };
    func.body.blocks[0].terminator = Terminator::TailCall {
        func: callee,
        args,
        span,
        atomic,
        is_unsafe_sig,
        is_foreign,
        callee_identity,
        callee_key,
    };
    func.body.blocks.truncate(1);
    func
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
    let vcs =
        generate_safety_vcs(&func, &blocks, &FxHashSet::default(), &UnsafeCoverage::default());
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
fn tail_call_uses_the_same_authenticated_unsafe_boundary() {
    let safe = flagged_tail_call_fn("std::ffi::OsStr::to_str", false, false);
    assert!(detect_unsafe_blocks(&safe).is_empty());

    for func in [
        flagged_tail_call_fn("std::ffi::OsStr::to_str", true, false),
        flagged_tail_call_fn("compute_hash", false, true),
    ] {
        let blocks = detect_unsafe_blocks(&func);
        assert_eq!(blocks.len(), 1, "authenticated tail-call boundary was dropped");
        let vcs =
            generate_safety_vcs(&func, &blocks, &FxHashSet::default(), &UnsafeCoverage::default());
        assert!(vcs.iter().any(
            |vc| matches!(&vc.kind, VcKind::Assertion { message } if message == MISSING_SAFETY_MSG)
        ));
    }
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

// ────────────────────────────────────────────────────────────────────────────
// Mint-side replacement of the always-`Bool(true)` stand-in (2026-09-19).
//
// Each test below pins one arm of `detection::decide_site` / the two type
// predicates. `UnsafeCoverage::default()` is EMPTY and is the fail-closed
// baseline: with it, every site keeps the byte-frozen stand-in exactly as before.
// ────────────────────────────────────────────────────────────────────────────

use super::detection::{
    MISSING_SAFETY_STANDIN_MSG, RAW_REBORROW_MSG_PREFIX, callee_is_authenticated_sysroot,
    callee_is_sysroot_item, raw_reborrow_message, uninitialized_zst_verdict,
    zeroed_all_zero_verdict,
};

/// The COMPILER'S OWN `[unsafe:unmodeled-call]` row for block 0 — the positive
/// evidence `decide_site` requires before it drops a site's stand-in.
///
/// In production this set is the row vector
/// `rustc_mir_transform::trust_verify::synthetic_unmodeled_unsafe_call_vcs`
/// actually produced over the same body, handed across in
/// `VcgenContext::with_compiler_unmodeled_call_blocks`. A test that wants the
/// "the compiler already refutes this call" arm has to SAY SO, exactly as the
/// compiler has to; there is no predicate here that can guess it.
fn compiler_refuted_block_zero() -> UnsafeCoverage {
    let mut coverage = UnsafeCoverage::default();
    coverage.compiler_unmodeled_call_blocks.insert(BlockId(0));
    coverage
}

fn mint_site_span() -> SourceSpan {
    SourceSpan { file: "mint.rs".into(), line_start: 7, col_start: 13, line_end: 7, col_end: 40 }
}

/// One-block fixture: `_2 = <callee>()` (dest local 2 of type `dest_ty`) with
/// the given extractor flags, followed by `Return`. `target: None` models a
/// diverging callee.
fn call_fixture(
    callee: &str,
    dest_ty: Ty,
    is_unsafe_sig: bool,
    is_foreign: bool,
    diverges: bool,
) -> VerifiableFunction {
    VerifiableFunction {
        name: "mint_site".to_string(),
        def_path: "test::mint_site".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: dest_ty, name: Some("out".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig,
                        callee_identity: None,
                        callee_key: crate::sep_engine::tests::fixture_key(&callee.to_string()),
                        is_foreign,
                        func: callee.to_string(),
                        args: vec![],
                        dest: Place::local(2),
                        target: if diverges { None } else { Some(BlockId(1)) },
                        span: mint_site_span(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::u32(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn unsafe_rows(func: &VerifiableFunction, coverage: &UnsafeCoverage) -> Vec<String> {
    let blocks = detect_unsafe_blocks(func);
    generate_safety_vcs(func, &blocks, &FxHashSet::default(), coverage)
        .into_iter()
        .map(|vc| match vc.kind {
            VcKind::Assertion { message } => {
                assert!(
                    matches!(vc.formula, Formula::Bool(true)),
                    "every row this mint produces is a constant `Bool(true)` finding"
                );
                message
            }
            other => panic!("unexpected kind {other:?}"),
        })
        .collect()
}

fn option_of(inner: Ty) -> Ty {
    Ty::adt_enum(
        "core::option::Option",
        vec![
            VariantDef { name: "None".into(), discriminant: 0, fields: vec![] },
            VariantDef { name: "Some".into(), discriminant: 1, fields: vec![("0".into(), inner)] },
        ],
    )
}

fn direct_tagged_enum(variants: Vec<VariantDef>) -> Ty {
    let Ty::Adt { name, fields, variants, .. } = Ty::adt_enum("test::E", variants) else {
        unreachable!()
    };
    Ty::Adt {
        name,
        fields,
        variants,
        disc_index_safe: true,
        faithful_enum_repr: None,
        layout: None,
        enum_layout: None,
        adt_kind: Some(AdtKind::Enum),
        arbitrary_precision: None,
        validity_wrapper: None,
    }
}

fn struct_ty(name: &str, fields: Vec<(&str, Ty)>) -> Ty {
    let Ty::Adt { name, fields, variants, .. } =
        Ty::adt(name, fields.into_iter().map(|(n, t)| (n.to_string(), t)).collect())
    else {
        unreachable!()
    };
    Ty::Adt {
        name,
        fields,
        variants,
        disc_index_safe: false,
        faithful_enum_repr: None,
        layout: None,
        enum_layout: None,
        adt_kind: Some(AdtKind::Struct),
        arbitrary_precision: None,
        validity_wrapper: None,
    }
}

fn raw(pointee: Ty) -> Ty {
    Ty::RawPtr { mutable: false, pointee: Box::new(pointee) }
}

fn reference(inner: Ty) -> Ty {
    Ty::Ref { mutable: false, inner: Box::new(inner) }
}

/// `alloc::boxed::Box<u8, A>` as the extractor lowers it: `(Unique<u8>, A)`,
/// the allocator substituted into the second field.
fn box_with_allocator(alloc: Ty) -> Ty {
    let unique = struct_ty("core::ptr::unique::Unique", vec![("pointer", raw(Ty::u8()))]);
    struct_ty("alloc::boxed::Box", vec![("0", unique), ("1", alloc)])
}

/// The proc-macro `Span::call_site()` span every operation of an expansion
/// shares.
fn pm_span() -> SourceSpan {
    SourceSpan { file: "pm.rs".into(), line_start: 1, col_start: 0, line_end: 1, col_end: 0 }
}

/// Locals: `_0: u64`, `_1: *const u64` (arg), `_2: u64`, `_3: *const u64`
/// (arg), `_4: &u64`, `_5: u64`. `bb0` holds `stmts` and `terminator`, all
/// meant to carry `pm_span()`; `bb1` returns.
fn one_span_block(stmts: Vec<Statement>, terminator: Terminator) -> VerifiableFunction {
    VerifiableFunction {
        name: "expanded".to_string(),
        def_path: "test::expanded".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: None },
                LocalDecl { index: 1, ty: raw(Ty::u64()), name: Some("p".into()) },
                LocalDecl { index: 2, ty: Ty::u64(), name: Some("a".into()) },
                LocalDecl { index: 3, ty: raw(Ty::u64()), name: Some("q".into()) },
                LocalDecl { index: 4, ty: reference(Ty::u64()), name: Some("b".into()) },
                LocalDecl { index: 5, ty: Ty::u64(), name: Some("c".into()) },
            ],
            blocks: vec![
                BasicBlock { id: BlockId(0), stmts, terminator },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: Ty::u64(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// `_dest = *_ptr` at `pm_span()`.
fn deref_stmt(dest: usize, ptr: usize) -> Statement {
    Statement::Assign {
        place: Place::local(dest),
        rvalue: Rvalue::Use(Operand::Copy(Place {
            local: ptr,
            projections: vec![Projection::Deref],
        })),
        span: pm_span(),
    }
}

/// `_dest = &*_ptr` at `pm_span()` — a reborrow, which the separation engine
/// does not interpret (no row is ever minted for it).
fn reborrow_stmt(dest: usize, ptr: usize) -> Statement {
    Statement::Assign {
        place: Place::local(dest),
        rvalue: Rvalue::Ref {
            mutable: false,
            place: Place { local: ptr, projections: vec![Projection::Deref] },
        },
        span: pm_span(),
    }
}

/// `_dest = <callee>(args)` at `pm_span()`, unsafe by signature.
fn pm_call(callee: &str, args: Vec<Operand>, dest: usize) -> Terminator {
    Terminator::Call {
        unwind: UnwindEdge::Unreachable,
        is_unsafe_sig: true,
        callee_identity: None,
        callee_key: crate::sep_engine::tests::fixture_key(&callee.to_string()),
        is_foreign: false,
        func: callee.to_string(),
        args,
        dest: Place::local(dest),
        target: Some(BlockId(1)),
        span: pm_span(),
        atomic: None,
    }
}

/// A `[unsafe:sep:deref]` row at `pm_span()`, as the engine mints for a raw
/// deref it interprets (statement or `ptr::read`/`ptr::write` call).
fn sep_deref_row(func: &VerifiableFunction) -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::Assertion { message: "[unsafe:sep:deref] null check for *p".into() },
        function: func.name.as_str().into(),
        location: pm_span(),
        formula: Formula::Bool(true),
        contract_metadata: None,
        obligation: None,
    }
}

#[test]
fn zeroed_predicate_admits_only_positively_recognised_types() {
    let admitted = [
        Ty::u64(),
        Ty::Int { width: 8, signed: true },
        Ty::PtrSizedInt { signed: false },
        Ty::Float { width: 32 },
        Ty::Bool,
        Ty::Char,
        Ty::Unit,
        raw(Ty::u32()),
        raw(Ty::Slice { elem: Box::new(Ty::u32()) }),
        raw(Ty::Str),
        Ty::Array { elem: Box::new(Ty::u32()), len: 4 },
        Ty::Tuple(vec![Ty::u32(), Ty::Float { width: 64 }, raw(Ty::u32())]),
        option_of(reference(Ty::u64())),
        option_of(Ty::Ref { mutable: true, inner: Box::new(Ty::u64()) }),
        option_of(struct_ty("core::ptr::non_null::NonNull", vec![("pointer", raw(Ty::u32()))])),
        option_of(box_with_allocator(struct_ty("alloc::alloc::Global", vec![]))),
        // Direct-tagged enum: the all-zero pattern is the discriminant-0 variant
        // with an all-zero payload.
        direct_tagged_enum(vec![
            VariantDef { name: "A".into(), discriminant: 0, fields: vec![("0".into(), Ty::u32())] },
            VariantDef { name: "B".into(), discriminant: 1, fields: vec![] },
        ]),
    ];
    for ty in &admitted {
        assert_eq!(zeroed_all_zero_verdict(ty), Ok(()), "must admit {ty:?}");
    }
}

#[test]
fn zeroed_predicate_refutes_everything_it_cannot_prove() {
    let non_null_like =
        struct_ty("core::ptr::non_null::NonNull", vec![("pointer", raw(Ty::u32()))]);
    let non_zero_like = struct_ty("core::num::nonzero::NonZero", vec![("0", Ty::u32())]);
    let refuted = [
        reference(Ty::u32()),
        Ty::FnPtr { sig: Box::new(FnSig { params: vec![], ret: Box::new(Ty::Unit) }) },
        // Pattern-type erasure: these two look like plain newtypes and MUST refute.
        non_null_like,
        non_zero_like,
        // Every plain struct refutes for the same reason.
        struct_ty("test::Plain", vec![("a", Ty::u32())]),
        struct_ty("alloc::boxed::Box", vec![("0", Ty::u32())]),
        raw(Ty::Dynamic { trait_name: "core::fmt::Debug".into(), principal_key: None }),
        raw(struct_ty("test::MaybeDst", vec![("tail", Ty::Slice { elem: Box::new(Ty::u32()) })])),
        Ty::Array { elem: Box::new(reference(Ty::u32())), len: 2 },
        Ty::Tuple(vec![Ty::u32(), reference(Ty::u32())]),
        Ty::Seq { drop_auth: None, elem: Box::new(Ty::u32()) },
        Ty::Str,
        Ty::Never,
        Ty::Unsupported { kind: "TyKind".into(), detail: "Param".into() },
        // Direct-tagged enum without a discriminant-0 variant.
        direct_tagged_enum(vec![
            VariantDef { name: "A".into(), discriminant: 1, fields: vec![] },
            VariantDef { name: "B".into(), discriminant: 2, fields: vec![] },
        ]),
        // Direct-tagged enum whose discriminant-0 payload holds a reference.
        direct_tagged_enum(vec![
            VariantDef {
                name: "A".into(),
                discriminant: 0,
                fields: vec![("0".into(), reference(Ty::u32()))],
            },
            VariantDef { name: "B".into(), discriminant: 1, fields: vec![] },
        ]),
        // Layout-unknown (niche or otherwise) enum that is not the Option shape.
        Ty::adt_enum(
            "test::E",
            vec![
                VariantDef { name: "A".into(), discriminant: 0, fields: vec![] },
                VariantDef { name: "B".into(), discriminant: 1, fields: vec![] },
            ],
        ),
        // Option whose payload is not a null-niche pointer.
        option_of(raw(Ty::u32())),
        option_of(Ty::u32()),
        // `Option<Box<T, A>>`: the NPO guarantee is for the DEFAULT allocator
        // only; a Box whose extracted field list does not show `Global` refutes.
        option_of(struct_ty("alloc::boxed::Box", vec![("0", Ty::u32())])),
        option_of(struct_ty("alloc::boxed::Box", vec![])),
        // Option with the right payload but the wrong shape (three variants).
        Ty::adt_enum(
            "core::option::Option",
            vec![
                VariantDef { name: "None".into(), discriminant: 0, fields: vec![] },
                VariantDef {
                    name: "Some".into(),
                    discriminant: 1,
                    fields: vec![("0".into(), reference(Ty::u32()))],
                },
                VariantDef { name: "Other".into(), discriminant: 2, fields: vec![] },
            ],
        ),
    ];
    for ty in &refuted {
        assert!(zeroed_all_zero_verdict(ty).is_err(), "must refute {ty:?}");
    }
    // Impersonation: the extractor stamps a non-sysroot crate wearing a sysroot
    // name, and the stamped spelling is not the authenticated one.
    let Ty::Adt { fields, variants, .. } = option_of(reference(Ty::u32())) else { unreachable!() };
    let forged = Ty::Adt {
        name: format!(
            "{}0123456789abcdef::core::option::Option",
            TRUST_UNAUTHENTICATED_CRATE_PATH_PREFIX
        ),
        fields,
        variants,
        disc_index_safe: false,
        faithful_enum_repr: None,
        layout: None,
        enum_layout: None,
        adt_kind: Some(AdtKind::Enum),
        arbitrary_precision: None,
        validity_wrapper: None,
    };
    assert!(
        zeroed_all_zero_verdict(&forged).is_err(),
        "a stamped Option name is not the sysroot one"
    );
}

#[test]
fn uninitialized_predicate_admits_only_zero_sized_types() {
    let phantom = struct_ty("core::marker::PhantomData", vec![]);
    let admitted = [
        Ty::Unit,
        Ty::Tuple(vec![]),
        Ty::Tuple(vec![Ty::Unit, Ty::Unit]),
        Ty::Array { elem: Box::new(Ty::u64()), len: 0 },
        Ty::Array { elem: Box::new(Ty::Unit), len: 3 },
        phantom.clone(),
        struct_ty("test::Marker", vec![("p", phantom.clone()), ("u", Ty::Unit)]),
    ];
    for ty in &admitted {
        assert_eq!(uninitialized_zst_verdict(ty), Ok(()), "must admit {ty:?}");
    }
    let refuted = [
        Ty::u64(),
        Ty::Bool,
        Ty::Array { elem: Box::new(Ty::u8()), len: 1 },
        Ty::Tuple(vec![Ty::Unit, Ty::u8()]),
        struct_ty("test::Byte", vec![("b", Ty::u8())]),
        // Extractor-unstamped ADT (hand-built / pre-migration): kind unknown.
        Ty::adt("test::Unknown", vec![]),
        // Enum and Never are never admitted.
        direct_tagged_enum(vec![VariantDef { name: "A".into(), discriminant: 0, fields: vec![] }]),
        Ty::Never,
        raw(Ty::Unit),
        Ty::Unsupported { kind: "TyKind".into(), detail: "Param".into() },
    ];
    for ty in &refuted {
        assert!(uninitialized_zst_verdict(ty).is_err(), "must refute {ty:?}");
    }
}

#[test]
fn callee_matching_is_exact_and_authenticated() {
    assert!(callee_is_sysroot_item("core::mem::zeroed", "core::mem::zeroed"));
    assert!(callee_is_sysroot_item("core::mem::zeroed::<u64>", "core::mem::zeroed"));
    assert!(!callee_is_sysroot_item("core::mem::zeroed_like::<u64>", "core::mem::zeroed"));
    assert!(!callee_is_sysroot_item("mycrate::core::mem::zeroed::<u64>", "core::mem::zeroed"));
    assert!(!callee_is_sysroot_item(
        &format!(
            "{TRUST_UNAUTHENTICATED_CRATE_PATH_PREFIX}00000000deadbeef::core::mem::zeroed::<u64>"
        ),
        "core::mem::zeroed"
    ));
}

#[test]
fn covered_requires_the_compilers_row_to_exist_not_a_prediction_of_it() {
    // THE `Covered` ASYMMETRY, closed (2026-09-20). This arm used to fire on a
    // vcgen-side PREDICTION that the compiler would mint `[unsafe:unmodeled-call]`
    // for the call. The prediction mirrored a string predicate the compiler
    // evaluates on a DIFFERENT spelling, and a spurious FALSE on this side — the
    // only direction a byte-comparing normalizer can drift — deleted the
    // byte-frozen stand-in and got nothing back: an unsafe site with ZERO
    // obligations.
    //
    // Now the row must EXIST. With no evidence, every one of these keeps its
    // stand-in, whatever its spelling: a user `unsafe fn`, a callee the compiler
    // really would refute, and a callee the compiler really would suppress all
    // land on the same fail-closed answer, because from here they are
    // indistinguishable and the honest answer to "is there another obligation?"
    // is "I cannot see one".
    let empty = UnsafeCoverage::default();
    for callee in [
        "misc_calls::danger",
        "alloc::boxed::Box::<u8>::from_raw",
        "core::ffi::c_str::CStr::from_ptr::<'_>",
        "user::set_len",
    ] {
        let f = call_fixture(callee, Ty::u32(), true, false, false);
        assert_eq!(
            unsafe_rows(&f, &empty),
            vec![MISSING_SAFETY_STANDIN_MSG.to_string()],
            "{callee}: no evidence, so the stand-in stays"
        );
    }
    // WITH the compiler's row for this block, the stand-in is dropped — one
    // obligation, the compiler's, not two.
    let evidence = compiler_refuted_block_zero();
    for callee in ["misc_calls::danger", "user::set_len"] {
        let f = call_fixture(callee, Ty::u32(), true, false, false);
        assert!(unsafe_rows(&f, &evidence).is_empty(), "{callee}");
    }
    // The evidence is keyed on the MIR OPERATION, so a row minted for ANOTHER
    // block does not speak for this one.
    let mut elsewhere = UnsafeCoverage::default();
    elsewhere.compiler_unmodeled_call_blocks.insert(BlockId(7));
    let f = call_fixture("misc_calls::danger", Ty::u32(), true, false, false);
    assert_eq!(unsafe_rows(&f, &elsewhere), vec![MISSING_SAFETY_STANDIN_MSG.to_string()]);
}

#[test]
fn zeroed_site_is_decided_on_the_destination_type() {
    let empty = UnsafeCoverage::default();
    // Admitted `T`: no row at all — the obligation is discharged at the mint.
    let ok = call_fixture("core::mem::zeroed::<u64>", Ty::u64(), true, false, false);
    assert!(unsafe_rows(&ok, &empty).is_empty());
    let ok_opt = call_fixture(
        "core::mem::zeroed::<Option<&u64>>",
        option_of(reference(Ty::u64())),
        true,
        false,
        false,
    );
    assert!(unsafe_rows(&ok_opt, &empty).is_empty());
    // Refuted `T`: exactly one typed `[unsafe:zeroed]` row, NOT the stand-in.
    let bad = call_fixture("core::mem::zeroed::<&u64>", reference(Ty::u64()), true, false, false);
    let rows = unsafe_rows(&bad, &empty);
    assert_eq!(rows.len(), 1, "{rows:?}");
    assert!(rows[0].starts_with("[unsafe:zeroed]"), "{}", rows[0]);
    assert!(rows[0].contains("reference"), "{}", rows[0]);
    // Name fallback only (safe signature / pre-flag MIR): the callee identity is
    // not trusted, so the byte-frozen stand-in is kept.
    let unflagged = call_fixture("core::mem::zeroed::<u64>", Ty::u64(), false, false, false);
    assert_eq!(unsafe_rows(&unflagged, &empty), vec![MISSING_SAFETY_STANDIN_MSG.to_string()]);
    // A stamped (impersonating) callee keeps the stand-in even for an admitted `T`.
    let forged = call_fixture(
        &format!(
            "{TRUST_UNAUTHENTICATED_CRATE_PATH_PREFIX}00000000deadbeef::core::mem::zeroed::<u64>"
        ),
        Ty::u64(),
        true,
        false,
        false,
    );
    assert_eq!(unsafe_rows(&forged, &empty), vec![MISSING_SAFETY_STANDIN_MSG.to_string()]);
}

/// G1: a struct `T` the structural verdict cannot admit (it refutes every
/// struct, because the extracted `Ty` erases niches) is covered ONLY when the
/// compiler named this exact block in `compiler_zero_valid_zeroed_blocks` (its
/// exact-layout validity check of all-zero bytes passed). An empty set, or a set
/// naming another block, refutes exactly as before. That the compiler never
/// names a site whose `T` rejects all-zero bytes (a struct with a `&T` field) is
/// pinned on the compiler side by `tests/ui/trust/mem_zeroed_exact_layout.rs`.
#[test]
fn zeroed_struct_is_covered_only_by_the_compilers_exact_layout_verdict() {
    let sigaction_like = struct_ty(
        "libc::unix::bsd::apple::sigaction",
        vec![("sa_sigaction", Ty::usize()), ("sa_mask", Ty::u32()), ("sa_flags", Ty::i32())],
    );
    let site = call_fixture(
        "core::mem::zeroed::<libc::unix::bsd::apple::sigaction>",
        sigaction_like,
        true,
        false,
        false,
    );
    // Negative control: no compiler verdict, the struct refutes.
    let empty = UnsafeCoverage::default();
    let rows = unsafe_rows(&site, &empty);
    assert_eq!(rows.len(), 1, "{rows:?}");
    assert!(rows[0].starts_with("[unsafe:zeroed]"), "{}", rows[0]);
    // A verdict for a DIFFERENT block does not reach this one.
    let mut elsewhere = UnsafeCoverage::default();
    elsewhere.compiler_zero_valid_zeroed_blocks.insert(BlockId(1));
    assert_eq!(unsafe_rows(&site, &elsewhere), rows);
    // The compiler's positive verdict for this block covers the site.
    let mut admitted = UnsafeCoverage::default();
    admitted.compiler_zero_valid_zeroed_blocks.insert(BlockId(0));
    assert!(unsafe_rows(&site, &admitted).is_empty());
    // The set never reaches a site that is not a keyed, unsafe-signature
    // `mem::zeroed`: the name fallback keeps its stand-in.
    let unflagged = call_fixture(
        "core::mem::zeroed::<libc::unix::bsd::apple::sigaction>",
        struct_ty("libc::unix::bsd::apple::sigaction", vec![("sa_mask", Ty::u32())]),
        false,
        false,
        false,
    );
    assert_eq!(unsafe_rows(&unflagged, &admitted), vec![MISSING_SAFETY_STANDIN_MSG.to_string()]);
}

#[test]
fn uninitialized_site_admits_only_a_zst_destination() {
    let empty = UnsafeCoverage::default();
    let zst = call_fixture("core::mem::uninitialized::<()>", Ty::Unit, true, false, false);
    assert!(unsafe_rows(&zst, &empty).is_empty());
    let int = call_fixture("core::mem::uninitialized::<u64>", Ty::u64(), true, false, false);
    let rows = unsafe_rows(&int, &empty);
    assert_eq!(rows.len(), 1, "{rows:?}");
    assert!(rows[0].starts_with("[unsafe:uninitialized]"), "{}", rows[0]);
}

#[test]
fn unreachable_unchecked_site_is_covered_by_the_unreachable_row() {
    let func = call_fixture("core::hint::unreachable_unchecked", Ty::Never, true, false, true);
    // The shared classifier names the call, so arm 1b mints `VcKind::Unreachable`
    // for every reached block — the same classifier the mint re-checks.
    assert!(
        trust_types::terminator_obligations::unreachable_terminator_span(
            &func,
            &func.body.blocks[0]
        )
        .is_some()
    );
    // Not reached by the path-guard walk (dead or budget-collapsed): stand-in kept.
    let empty = UnsafeCoverage::default();
    assert_eq!(unsafe_rows(&func, &empty), vec![MISSING_SAFETY_STANDIN_MSG.to_string()]);
    // Reached: the `Unreachable` row carries the obligation; no stand-in.
    let mut reached = UnsafeCoverage::default();
    reached.reached_blocks.insert(BlockId(0));
    assert!(unsafe_rows(&func, &reached).is_empty());
    // A different diverging unsafe callee with the same shape is NOT the
    // classifier's, and keeps its stand-in even when reached.
    let other = call_fixture("core::intrinsics::abort_unchecked", Ty::Never, true, false, true);
    assert_eq!(unsafe_rows(&other, &reached), vec![MISSING_SAFETY_STANDIN_MSG.to_string()]);
}

#[test]
fn a_site_with_a_behavioural_row_mints_no_standin() {
    // (a1) the separation engine minted a `[unsafe:sep:*]` row for this call.
    let func = unsafe_ptr_read_function(); // bb0: `core::ptr::read`, name fallback only
    let empty = UnsafeCoverage::default();
    assert_eq!(unsafe_rows(&func, &empty), vec![MISSING_SAFETY_STANDIN_MSG.to_string()]);
    let call_span = match &func.body.blocks[0].terminator {
        Terminator::Call { span, .. } => span.clone(),
        _ => unreachable!(),
    };
    let row = |message: &str| VerificationCondition {
        kind: VcKind::Assertion { message: message.into() },
        function: func.name.as_str().into(),
        location: call_span.clone(),
        formula: Formula::Bool(true),
        contract_metadata: None,
        obligation: None,
    };
    let mut covered = UnsafeCoverage::default();
    covered.record_sep_row(
        &row("[unsafe:sep:deref] null check for *arg0_core_ptr_read"),
        BlockId(0),
        MirOp::Terminator,
    );
    assert!(unsafe_rows(&func, &covered).is_empty());
    // WRONG block: not this site.
    let mut other_block = UnsafeCoverage::default();
    other_block.sep_call_sites.insert(BlockId(1));
    assert_eq!(unsafe_rows(&func, &other_block), vec![MISSING_SAFETY_STANDIN_MSG.to_string()]);
    // Right block, but the row was minted for a STATEMENT of it (same span or
    // not — the span is not consulted): not this site.
    let mut stmt_row = UnsafeCoverage::default();
    stmt_row.record_sep_row(
        &row("[unsafe:sep:deref] null check for *arg0_core_ptr_read"),
        BlockId(0),
        MirOp::Statement(0),
    );
    assert!(stmt_row.sep_call_sites.is_empty());
    assert_eq!(unsafe_rows(&func, &stmt_row), vec![MISSING_SAFETY_STANDIN_MSG.to_string()]);
    // A non-`[unsafe:sep:` row is never recorded.
    let mut ignored = UnsafeCoverage::default();
    ignored.record_sep_row(&row("panic freedom: …"), BlockId(0), MirOp::Terminator);
    assert!(ignored.sep_call_sites.is_empty() && ignored.sep_deref_sites.is_empty());

    // (a2) the compiler's OWN `[unsafe:unmodeled-call]` row for this block —
    // evidence, not a prediction (2026-09-20). Without it the site keeps its
    // stand-in even for the callee the compiler certainly would refute, because
    // from here the two cases are indistinguishable.
    let danger = call_fixture("mycrate::danger", Ty::u32(), true, false, false);
    assert_eq!(unsafe_rows(&danger, &empty), vec![MISSING_SAFETY_STANDIN_MSG.to_string()]);
    assert!(unsafe_rows(&danger, &compiler_refuted_block_zero()).is_empty());
    let danger_unflagged = call_fixture("mycrate::danger", Ty::u32(), false, false, false);
    assert!(
        detect_unsafe_blocks(&danger_unflagged).is_empty(),
        "a safe-signature call with a non-unsafe name is not an unsafe site at all"
    );
    let foreign = call_fixture("libc::abs", Ty::u32(), true, true, false);
    assert_eq!(unsafe_rows(&foreign, &empty), vec![MISSING_SAFETY_STANDIN_MSG.to_string()]);
    // A modeled-but-rowless unsafe callee outside the three typed ops keeps the
    // stand-in (blanket-only class: `ptr::swap`, `::ffi::`, `::intrinsics::`, …).
    for standin in [
        "core::ptr::swap::<u64>",
        "core::ffi::c_str::CStr::from_ptr::<'_>",
        "core::intrinsics::volatile_load::<u64>",
    ] {
        let f = call_fixture(standin, Ty::u32(), true, false, false);
        assert_eq!(
            unsafe_rows(&f, &empty),
            vec![MISSING_SAFETY_STANDIN_MSG.to_string()],
            "{standin}"
        );
    }
}

#[test]
fn a_raw_deref_statement_needs_a_deref_family_row_minted_for_that_statement() {
    let func = unsafe_deref_function();
    let stmt_span = match &func.body.blocks[0].stmts[0] {
        Statement::Assign { span, .. } => span.clone(),
        _ => unreachable!(),
    };
    let row = |message: &str| VerificationCondition {
        kind: VcKind::Assertion { message: message.into() },
        function: func.name.as_str().into(),
        location: stmt_span.clone(),
        formula: Formula::Bool(true),
        contract_metadata: None,
        obligation: None,
    };
    let empty = UnsafeCoverage::default();
    assert_eq!(unsafe_rows(&func, &empty), vec![MISSING_SAFETY_STANDIN_MSG.to_string()]);
    // A `[unsafe:sep:deref]` row minted while interpreting THIS statement covers it.
    let mut deref = UnsafeCoverage::default();
    deref.record_sep_row(&row("[unsafe:sep:deref] null check"), BlockId(0), MirOp::Statement(0));
    assert!(unsafe_rows(&func, &deref).is_empty());
    // The same row minted for ANOTHER statement of the block does not.
    let mut other_stmt = UnsafeCoverage::default();
    other_stmt.record_sep_row(
        &row("[unsafe:sep:deref] null check"),
        BlockId(0),
        MirOp::Statement(1),
    );
    assert_eq!(unsafe_rows(&func, &other_stmt), vec![MISSING_SAFETY_STANDIN_MSG.to_string()]);
    // The same row minted for the block's TERMINATOR (a `ptr::read` call whose
    // proc-macro span collides with the statement's) does not.
    let mut term_row = UnsafeCoverage::default();
    term_row.record_sep_row(&row("[unsafe:sep:deref] null check"), BlockId(0), MirOp::Terminator);
    assert!(term_row.sep_deref_sites.is_empty());
    assert_eq!(unsafe_rows(&func, &term_row), vec![MISSING_SAFETY_STANDIN_MSG.to_string()]);
    // A row of another `[unsafe:sep:*]` family minted for this statement does not.
    let mut other_family = UnsafeCoverage::default();
    other_family.record_sep_row(
        &row("[unsafe:sep:offset] bounds"),
        BlockId(0),
        MirOp::Statement(0),
    );
    assert!(other_family.sep_deref_sites.is_empty());
    assert_eq!(unsafe_rows(&func, &other_family), vec![MISSING_SAFETY_STANDIN_MSG.to_string()]);
}

// ────────────────────────────────────────────────────────────────────────────
// Round-two regressions (2026-09-19): the three reviewer counterexamples.
// Each test below FAILS on `f780f03f22` (measured) and passes on the fix.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn a_call_through_an_unsafe_fn_pointer_keeps_its_standin() {
    // DEFECT 1. The compiler's `synthetic_unmodeled_unsafe_call_vcs` does
    // `let ty::FnDef(..) = callee_kind.kind() else { continue }`: a call through
    // an `unsafe fn` POINTER gets no `[unsafe:unmodeled-call]` row. The extractor
    // spells that call with the `@trust-indirect-callee` sentinel,
    // `is_unsafe_sig` from the pointer type, `is_foreign: false` — so the three
    // mirrored conjuncts alone predicted a row that never comes, and the site had
    // no obligation at all. It must keep the byte-frozen stand-in.
    // The sentinel can never appear in the compiler's row set — the generator
    // `continue`s before it reaches the row — so the evidence is absent by
    // construction and the site keeps the byte-frozen stand-in. (Until
    // 2026-09-20 the three mirrored conjuncts PREDICTED a row for it, and the
    // site had no obligation at all: the round-two `fnptr.rs` refutation.)
    let f = call_fixture(TRUST_INDIRECT_CALLEE_PATH, Ty::u8(), true, false, false);
    assert_eq!(
        unsafe_rows(&f, &UnsafeCoverage::default()),
        vec![MISSING_SAFETY_STANDIN_MSG.to_string()]
    );
    // And it stays kept even beside a row the compiler minted for ANOTHER block.
    let mut elsewhere = UnsafeCoverage::default();
    elsewhere.compiler_unmodeled_call_blocks.insert(BlockId(3));
    assert_eq!(unsafe_rows(&f, &elsewhere), vec![MISSING_SAFETY_STANDIN_MSG.to_string()]);
}

#[test]
fn the_std_unsafe_call_skip_gate_can_only_withhold_the_evidence() {
    // The compiler generator's other `continue`: under
    // `TRUST_STD_UNSAFE_CALL_SKIP` it declines to mint for a non-local callee at
    // a trusted-std `fn_span`. vcgen used to have to MIRROR that scope from the
    // terminator span it holds, and could not (it knows neither `fn_span` nor
    // `is_local`), so it answered `false` for every call while the variable was
    // present — a superset of the compiler's skip, kept only by discipline.
    //
    // There is nothing left to mirror. A row the gate suppressed is a row the
    // compiler never minted, so it is simply not in the evidence set, and the
    // site keeps its stand-in for the same reason every unwitnessed site does.
    let f = call_fixture("fnptr::danger", Ty::u8(), true, false, false);
    assert_eq!(
        unsafe_rows(&f, &UnsafeCoverage::default()),
        vec![MISSING_SAFETY_STANDIN_MSG.to_string()]
    );
    assert!(unsafe_rows(&f, &compiler_refuted_block_zero()).is_empty());
}

#[test]
fn proc_macro_collision_deref_statement_rows_do_not_cover_the_zeroed_call() {
    // DEFECT 2, call direction: `pub fn two(p) { let a = unsafe { *p }; let b =
    // unsafe { zeroed::<&u64>() }; .. }` emitted by a proc macro — the deref
    // statement and the `zeroed` terminator share one block and ONE span. The
    // engine mints `[unsafe:sep:deref]` rows for the STATEMENT; they must not
    // cover the CALL, whose typed `[unsafe:zeroed]` refutation is owed.
    let func = one_span_block(
        vec![deref_stmt(2, 1)],
        pm_call("core::mem::zeroed::<&'static u64>", vec![], 4),
    );
    let blocks = detect_unsafe_blocks(&func);
    assert_eq!(blocks.len(), 2);
    let mut coverage = UnsafeCoverage::default();
    coverage.record_sep_row(&sep_deref_row(&func), BlockId(0), MirOp::Statement(0));
    let rows = unsafe_rows(&func, &coverage);
    assert_eq!(rows.len(), 1, "the deref is covered, the call is refuted: {rows:?}");
    assert!(rows[0].starts_with("[unsafe:zeroed]"), "{}", rows[0]);
    assert!(rows[0].contains("reference"), "{}", rows[0]);
    // Same collision, a `ptr::swap` / foreign call instead of `zeroed`: the
    // stand-in (blanket-only class) must survive the statement's rows too.
    let swap = one_span_block(
        vec![deref_stmt(2, 1)],
        pm_call("core::ptr::swap::<u64>", vec![Operand::Copy(Place::local(1))], 5),
    );
    let mut coverage = UnsafeCoverage::default();
    coverage.record_sep_row(&sep_deref_row(&swap), BlockId(0), MirOp::Statement(0));
    assert_eq!(unsafe_rows(&swap, &coverage), vec![MISSING_SAFETY_STANDIN_MSG.to_string()]);
}

#[test]
fn proc_macro_collision_call_rows_do_not_cover_the_deref_statement() {
    // DEFECT 2, deref direction: `let a = unsafe { *p }; let c = unsafe {
    // ptr::read(q) };` in one block, one span. `ptr::read` mints the SAME
    // `[unsafe:sep:deref]` family for the TERMINATOR; it must not cover the
    // deref STATEMENT, which the engine did not reach.
    let func = one_span_block(
        vec![deref_stmt(2, 1)],
        pm_call("core::ptr::read::<u64>", vec![Operand::Copy(Place::local(3))], 5),
    );
    assert_eq!(detect_unsafe_blocks(&func).len(), 2);
    let mut coverage = UnsafeCoverage::default();
    coverage.record_sep_row(&sep_deref_row(&func), BlockId(0), MirOp::Terminator);
    // The call is covered; the statement keeps exactly its stand-in.
    assert_eq!(unsafe_rows(&func, &coverage), vec![MISSING_SAFETY_STANDIN_MSG.to_string()]);
}

#[test]
fn proc_macro_collision_one_statements_rows_do_not_cover_another() {
    // DEFECT 2, statement/statement (the reviewer's `mk_reborrow`): `let a =
    // unsafe { *p }; let b = unsafe { &*q };` in one block, one span. The engine
    // interprets the first (deref rows) and never the second (`Rvalue::Ref`);
    // the second must keep its own row (since T10 the typed `[unsafe:reborrow]`
    // row, not the stand-in).
    let func = one_span_block(vec![deref_stmt(2, 1), reborrow_stmt(4, 3)], Terminator::Return);
    let blocks = detect_unsafe_blocks(&func);
    assert_eq!(blocks.len(), 2);
    assert!(matches!(blocks[1].origin, UnsafeOrigin::RawDeref { stmt: 1 }));
    let mut coverage = UnsafeCoverage::default();
    coverage.record_sep_row(&sep_deref_row(&func), BlockId(0), MirOp::Statement(0));
    assert_eq!(unsafe_rows(&func, &coverage), vec![raw_reborrow_message(false)]);
    // Both interpreted: nothing owed.
    coverage.record_sep_row(&sep_deref_row(&func), BlockId(0), MirOp::Statement(1));
    assert!(unsafe_rows(&func, &coverage).is_empty());
}

#[test]
fn option_box_is_admitted_only_with_the_global_allocator() {
    // DEFECT 3. `Option<Box<T, A>>` is NPO-guaranteed for the DEFAULT allocator
    // only; with an `allocator_api` allocator carrying a bigger niche than
    // `NonNull` (a `bool`, a 3-variant enum) rustc puts Option's niche in the
    // allocator field and the all-zero pattern is `Some(Box { ptr: null, .. })`.
    let global = struct_ty("alloc::alloc::Global", vec![]);
    let bool_alloc = struct_ty("optbox::BoolAlloc", vec![("0", Ty::Bool)]);
    let enum_alloc = direct_tagged_enum(vec![
        VariantDef { name: "X".into(), discriminant: 0, fields: vec![] },
        VariantDef { name: "Y".into(), discriminant: 1, fields: vec![] },
        VariantDef { name: "Z".into(), discriminant: 2, fields: vec![] },
    ]);
    assert_eq!(zeroed_all_zero_verdict(&option_of(box_with_allocator(global.clone()))), Ok(()));
    let refuted = [
        option_of(box_with_allocator(bool_alloc.clone())),
        option_of(box_with_allocator(enum_alloc.clone())),
        // The recursion admits nothing through arrays and tuples either.
        Ty::Array { elem: Box::new(option_of(box_with_allocator(enum_alloc.clone()))), len: 2 },
        Ty::Tuple(vec![Ty::u32(), option_of(box_with_allocator(enum_alloc.clone()))]),
        // A unit-struct allocator that is NOT the authenticated `Global` — the
        // extractor's stamp on an impersonating crate is a different string.
        option_of(box_with_allocator(struct_ty("optbox::Global", vec![]))),
        option_of(box_with_allocator(struct_ty(
            &format!(
                "{TRUST_UNAUTHENTICATED_CRATE_PATH_PREFIX}00000000deadbeef::alloc::alloc::Global"
            ),
            vec![],
        ))),
        // A `Global`-named ADT that carries fields or variants is not the unit struct.
        option_of(box_with_allocator(struct_ty("alloc::alloc::Global", vec![("0", Ty::Bool)]))),
        // The allocator field absent (one field / no fields): not shown to be
        // `Global`, so refuted — the documented cost of the erased-args name.
        option_of(struct_ty("alloc::boxed::Box", vec![("0", Ty::u32())])),
        // Three fields: not the `(Unique<T>, A)` shape.
        option_of(struct_ty(
            "alloc::boxed::Box",
            vec![("0", Ty::u32()), ("1", global.clone()), ("2", global.clone())],
        )),
    ];
    for ty in &refuted {
        assert!(zeroed_all_zero_verdict(ty).is_err(), "must refute {ty:?}");
    }
    // Through the mint: the reviewer's `zero_opt_box_alloc` / `_enum_alloc`,
    // array and tuple sites all refute with the typed row; the plain
    // `Option<Box<u8>>` site is admitted.
    for (callee, ty) in [
        (
            "core::mem::zeroed::<Option<Box<u8, BoolAlloc>>>",
            option_of(box_with_allocator(bool_alloc)),
        ),
        (
            "core::mem::zeroed::<Option<Box<u8, EnumAlloc>>>",
            option_of(box_with_allocator(enum_alloc.clone())),
        ),
        (
            "core::mem::zeroed::<[Option<Box<u8, EnumAlloc>>; 2]>",
            Ty::Array { elem: Box::new(option_of(box_with_allocator(enum_alloc.clone()))), len: 2 },
        ),
        (
            "core::mem::zeroed::<(u32, Option<Box<u8, EnumAlloc>>)>",
            Ty::Tuple(vec![Ty::u32(), option_of(box_with_allocator(enum_alloc))]),
        ),
    ] {
        let f = call_fixture(callee, ty, true, false, false);
        let rows = unsafe_rows(&f, &UnsafeCoverage::default());
        assert_eq!(rows.len(), 1, "{callee}: {rows:?}");
        assert!(rows[0].starts_with("[unsafe:zeroed]"), "{callee}: {}", rows[0]);
    }
    let plain = call_fixture(
        "core::mem::zeroed::<Option<Box<u8>>>",
        option_of(box_with_allocator(global)),
        true,
        false,
        false,
    );
    assert!(unsafe_rows(&plain, &UnsafeCoverage::default()).is_empty());
}

// ────────────────────────────────────────────────────────────────────────────
// 2026-09-20 — the substring class, closed fail-closed (rules 1–3)
// ────────────────────────────────────────────────────────────────────────────

/// Coverage exactly as `generate::entry` builds it: every row the separation
/// engine minted for `func`, indexed by the `(block, op)` it was interpreting.
fn engine_coverage(func: &VerifiableFunction) -> UnsafeCoverage {
    let mut coverage = UnsafeCoverage::default();
    for (vc, block, op) in crate::sep_engine::check_sep_unsafe_blocked_ops(
        func,
        &FxHashSet::default(),
        &FxHashSet::default(),
    ) {
        coverage.record_sep_row(&vc, block, op);
    }
    coverage
}

/// [`call_fixture`] with the call given ONE `u32` argument (`x`, local 1) — the
/// shape the arithmetic recognizers (`new_unchecked`, `from_u32_unchecked`)
/// mint their obligation over.
fn unsafe_call_with_u32_arg(callee: &str, dest_ty: Ty) -> VerifiableFunction {
    let mut func = call_fixture(callee, dest_ty, true, false, false);
    match &mut func.body.blocks[0].terminator {
        Terminator::Call { args, .. } => {
            *args = vec![trust_types::Operand::Copy(Place::local(1))];
        }
        _ => unreachable!("call_fixture's first block is the call"),
    }
    func
}

#[test]
fn a_user_defined_unsafe_fn_named_like_a_std_recognizer_keeps_its_standin() {
    // The 2026-09-19 refutation, mint side (`scratchpad/dl/xc`), through the
    // REAL engine → coverage → mint pipeline. A downstream call to a user
    // `unsafe fn` whose name collides with a std recognizer
    // (`dep::nonzero::Handle::new_unchecked`, `dep::from_u32_unchecked`) must NOT
    // acquire a std contract: the engine mints NO separation row for it (the
    // recognizers name the sysroot items exactly), the compiler's name fallback
    // still suppresses its `[unsafe:unmodeled-call]` row, and so `decide_site`
    // keeps the byte-frozen stand-in — ONE fail-closed obligation, no wrong
    // contract. At `a351ee124e` the first callee carried a PROVED `x == 0` and
    // the second the Unicode-scalar contract, each covering the site.
    for callee in ["dep::nonzero::Handle::new_unchecked", "dep::from_u32_unchecked"] {
        let f = unsafe_call_with_u32_arg(callee, Ty::u32());
        let coverage = engine_coverage(&f);
        assert!(
            coverage.sep_call_sites.is_empty(),
            "{callee}: no separation row may be minted for a user callee"
        );
        assert_eq!(
            unsafe_rows(&f, &coverage),
            vec![MISSING_SAFETY_STANDIN_MSG.to_string()],
            "{callee}"
        );
    }
}

#[test]
fn a_genuine_nonzero_new_unchecked_is_covered_by_exactly_its_niche_row() {
    // The REAL extracted spelling `core::num::nonzero::NonZero::<u32>::new_unchecked(x)`
    // still gets exactly its `x == 0` row, charged to this block's terminator,
    // and that row covers the site: no stand-in.
    let f =
        unsafe_call_with_u32_arg("core::num::nonzero::NonZero::<u32>::new_unchecked", Ty::u32());
    let rows = crate::sep_engine::check_sep_unsafe_blocked_ops(
        &f,
        &FxHashSet::default(),
        &FxHashSet::default(),
    );
    let sep: Vec<_> = rows
        .iter()
        .filter(|(vc, ..)| {
            matches!(&vc.kind, VcKind::Assertion { message }
                if message.starts_with(VcKind::SEP_UNSAFE_ASSERTION_PREFIX))
        })
        .collect();
    assert_eq!(sep.len(), 1, "exactly one separation row, got {rows:?}");
    let (vc, block, op) = sep[0];
    assert!(matches!(&vc.kind, VcKind::Assertion { message }
        if message.contains("[unsafe:sep:new_unchecked]")));
    assert_eq!(
        vc.formula,
        Formula::Eq(
            Box::new(Formula::Var("x".into(), trust_types::Sort::Int)),
            Box::new(Formula::Int(0))
        ),
    );
    assert_eq!(*block, BlockId(0));
    assert!(matches!(op, MirOp::Terminator));
    assert!(unsafe_rows(&f, &engine_coverage(&f)).is_empty(), "the niche row covers; no stand-in");
}

#[test]
fn mem_zeroed_option_box_with_a_global_type_argument_reaches_the_typed_verdict() {
    // RULE 3. The reviewer's spelling carries `alloc::alloc::Global` INSIDE the
    // turbofish; the old `contains("alloc::alloc")` read it as an allocation
    // callee, admitted the body to the engine, minted `[unsafe:sep:alloc]` rows
    // for the zeroed terminator and so covered the site before the typed
    // `[unsafe:zeroed]` verdict was reached.
    let callee =
        "core::mem::zeroed::<core::option::Option<alloc::boxed::Box<u8, alloc::alloc::Global>>>";
    // Admitted: the extracted allocator field IS the authenticated `Global`.
    let global = struct_ty("alloc::alloc::Global", vec![]);
    let admitted = call_fixture(callee, option_of(box_with_allocator(global)), true, false, false);
    let coverage = engine_coverage(&admitted);
    assert!(
        coverage.sep_call_sites.is_empty(),
        "no [unsafe:sep:alloc] row may be minted from a type argument"
    );
    assert!(unsafe_rows(&admitted, &coverage).is_empty(), "admitted: Global allocator");
    // Refuted: a user allocator — the typed verdict is REACHED and states why.
    let bool_alloc = struct_ty("optbox::BoolAlloc", vec![("0", Ty::Bool)]);
    let refuted =
        call_fixture(callee, option_of(box_with_allocator(bool_alloc)), true, false, false);
    let coverage = engine_coverage(&refuted);
    assert!(coverage.sep_call_sites.is_empty());
    let rows = unsafe_rows(&refuted, &coverage);
    assert_eq!(rows.len(), 1, "{rows:?}");
    assert!(rows[0].starts_with("[unsafe:zeroed]"), "{rows:?}");
}

#[test]
fn rule1_a_separation_row_covers_only_a_sysroot_authenticated_callee() {
    // RULE 1. Even with a separation row RECORDED for the block, `decide_site`
    // trusts it to cover the call only when the callee is sysroot-authenticated.
    // The gate leans on the extractor's stamp: an impersonating crate cannot
    // forge a genuine `core`/`alloc`/`std` root, and a UFCS spelling is admitted
    // only when both of its halves are sysroot.
    for genuine in [
        "core::num::nonzero::NonZero::<u32>::new_unchecked",
        "alloc::vec::Vec::<u8>::set_len",
        "core::ptr::read::<u8>",
        "<alloc::alloc::Global as core::alloc::Allocator>::deallocate",
        "<core::ptr::NonNull<u8>>::new_unchecked",
        "<*const u8>::read",
    ] {
        assert!(callee_is_authenticated_sysroot(genuine), "{genuine}");
    }
    for user in [
        "dep::nonzero::Handle::new_unchecked",
        "mycrate::core::ptr::read",
        "<optbox::BoolAlloc as core::alloc::Allocator>::deallocate",
        "<core::num::nonzero::NonZero<u32> as mycrate::Forge>::new_unchecked",
        "<mycrate::Fake>::read",
        "memmap2::MmapMut::map_mut",
        &format!("{TRUST_UNAUTHENTICATED_CRATE_PATH_PREFIX}00000000deadbeef::core::mem::zeroed"),
        &format!(
            "<{TRUST_UNAUTHENTICATED_CRATE_PATH_PREFIX}00000000deadbeef::alloc::alloc::Global as \
             core::alloc::Allocator>::deallocate"
        ),
    ] {
        assert!(!callee_is_authenticated_sysroot(user), "{user}");
    }

    let mut cov = UnsafeCoverage::default();
    cov.sep_call_sites.insert(BlockId(0));
    // A recorded row on a NON-sysroot callee does not cover: the stand-in stays.
    for user in [
        "dep::nonzero::Handle::new_unchecked",
        "<optbox::BoolAlloc as core::alloc::Allocator>::deallocate",
        "<core::num::nonzero::NonZero<u32> as mycrate::Forge>::new_unchecked",
    ] {
        let f = call_fixture(user, Ty::u32(), true, false, false);
        assert_eq!(unsafe_rows(&f, &cov), vec![MISSING_SAFETY_STANDIN_MSG.to_string()], "{user}");
    }
    // The same recorded row on a genuine sysroot callee covers.
    for genuine in [
        "core::num::nonzero::NonZero::<u32>::new_unchecked",
        "<alloc::alloc::Global as core::alloc::Allocator>::deallocate",
    ] {
        let f = call_fixture(genuine, Ty::u32(), true, false, false);
        assert!(unsafe_rows(&f, &cov).is_empty(), "{genuine}");
    }
    // The external-memory-map recognizer is the deliberate exception: its
    // legitimate targets are third-party, so its row covers its own callee.
    let mmap = call_fixture("memmap2::MmapMut::map_mut", Ty::u32(), true, false, false);
    assert!(unsafe_rows(&mmap, &cov).is_empty(), "an external-map row covers its own callee");
}

#[test]
fn an_impersonating_sysroot_callee_keeps_its_standin_with_no_mirror_left() {
    // THE ROUND-5 FAIL-OPEN, now unreachable by construction. An impersonating
    // `core`/`alloc` arrives here wearing the extractor's identity stamp, which
    // the anchored recognizers refuse — so the engine mints no separation row
    // for it. The compiler, reading the UNSTAMPED `safe_def_path_str`, finds the
    // callee modeled and mints nothing either. The old mirror had to be taught
    // to evaluate the unstamped spelling as well, or it would have PREDICTED the
    // compiler's row and answered `Covered` with no obligation anywhere.
    //
    // There is no mirror to teach. Nothing minted a row for this call, so
    // nothing is in the evidence set, and the site keeps the one obligation it
    // has.
    let stamp = format!("{TRUST_UNAUTHENTICATED_CRATE_PATH_PREFIX}00000000deadbeef::");
    for stamped in [
        format!("{stamp}core::option::Option::<u32>::unwrap_unchecked"),
        format!("{stamp}core::ptr::read::<u8>"),
        format!("{stamp}alloc::vec::Vec::<u8>::set_len"),
        format!("{stamp}core::num::nonzero::NonZero::<u32>::new_unchecked"),
    ] {
        let f = unsafe_call_with_u32_arg(&stamped, Ty::u32());
        let cov = engine_coverage(&f);
        assert!(cov.sep_call_sites.is_empty(), "{stamped}: the recognizers refuse the stamp");
        assert_eq!(
            unsafe_rows(&f, &cov),
            vec![MISSING_SAFETY_STANDIN_MSG.to_string()],
            "{stamped}"
        );
    }
}

#[test]
fn an_unsafe_block_around_safe_code_owes_nothing() {
    // Detection is per unsafe OPERATION: a body with no unsafe-signature /
    // foreign / unsafe-named call and no raw deref has no site to decide.
    let func = safe_function();
    assert!(detect_unsafe_blocks(&func).is_empty());
    let mut vcs = Vec::new();
    check_unsafe(&func, &[], &FxHashSet::default(), &UnsafeCoverage::default(), &mut vcs);
    assert!(vcs.is_empty());
}

// ────────────────────────────────────────────────────────────────────────────
// AW-1 (2026-10-03): rustc's own `.await` lowering. `make_lowered_await` emits
// `Future::poll(Pin::new_unchecked(&mut __awaitee), get_context(_task_context))`
// inside an `UnsafeSource::CompilerGenerated` block; the compiler names those
// call blocks (`collect_await_desugared_unsafe_call_blocks`: span marked
// `DesugaringKind::Await` AND callee the `PinNewUnchecked`/`GetContext` lang
// item) and only those lose the stand-in. Every test pairs the credited site
// with a control that keeps its row.
// ────────────────────────────────────────────────────────────────────────────

const AWAIT_PIN_NEW_UNCHECKED: &str = "core::pin::Pin::<&mut F>::new_unchecked";

fn await_credit(blocks: &[usize]) -> UnsafeCoverage {
    let mut coverage = UnsafeCoverage::default();
    coverage.await_desugared_unsafe_call_blocks.extend(blocks.iter().map(|&b| BlockId(b)));
    coverage
}

#[test]
fn await_lowering_call_block_owes_no_safety_stand_in() {
    let func = call_fixture(AWAIT_PIN_NEW_UNCHECKED, Ty::Unit, true, false, false);
    // CONTROL: no compiler credit — today's row.
    assert_eq!(
        unsafe_rows(&func, &UnsafeCoverage::default()),
        vec![MISSING_SAFETY_STANDIN_MSG.to_string()],
        "without the compiler's await credit the call keeps its stand-in"
    );
    assert!(
        unsafe_rows(&func, &await_credit(&[0])).is_empty(),
        "the compiler-identified `.await` lowering call must owe no stand-in"
    );
}

#[test]
fn await_credit_is_per_block() {
    // A credit naming another block (the user's own unsafe call in an async body
    // is a different block from the lowering's) keeps this block's row.
    let func = call_fixture(AWAIT_PIN_NEW_UNCHECKED, Ty::Unit, true, false, false);
    assert_eq!(
        unsafe_rows(&func, &await_credit(&[1])),
        vec![MISSING_SAFETY_STANDIN_MSG.to_string()],
        "an await credit for block 1 must not reach block 0's call"
    );
}

#[test]
fn await_credit_never_covers_a_raw_deref_in_the_same_block() {
    // The credit is keyed on the block's CALL TERMINATOR. A raw-pointer deref
    // statement in the credited block is a different operation and keeps its row.
    let mut func = call_fixture(AWAIT_PIN_NEW_UNCHECKED, Ty::Unit, true, false, false);
    func.body.locals.push(LocalDecl {
        index: 3,
        ty: Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u32()) },
        name: Some("p".into()),
    });
    func.body.blocks[0].stmts.push(Statement::Assign {
        place: Place::local(1),
        rvalue: Rvalue::Use(Operand::Copy(Place {
            local: 3,
            projections: vec![Projection::Deref],
        })),
        span: mint_site_span(),
    });
    let control = unsafe_rows(&func, &UnsafeCoverage::default());
    assert_eq!(control.len(), 2, "control: the deref and the call each keep a row: {control:?}");
    let credited = unsafe_rows(&func, &await_credit(&[0]));
    assert_eq!(
        credited,
        vec![MISSING_SAFETY_STANDIN_MSG.to_string()],
        "only the call's row may go; the same-block raw deref keeps its stand-in"
    );
}

/// The full generation entry, through the owner-checked context the compiler
/// installs: the credit reaches the mint, and a context owned by another
/// function (or none) drops nothing.
#[test]
fn await_credit_reaches_generation_only_through_the_owning_context() {
    let func = call_fixture(AWAIT_PIN_NEW_UNCHECKED, Ty::Unit, true, false, false);
    let stand_ins = |context: &crate::VcgenContext| {
        crate::generate_vcs_with_context(&func, context)
            .into_iter()
            .filter(|vc| {
                matches!(&vc.kind, VcKind::Assertion { message }
                    if message == MISSING_SAFETY_STANDIN_MSG)
            })
            .count()
    };
    let none = crate::VcgenContext::for_function(func.def_path.clone());
    assert_eq!(stand_ins(&none), 1, "control: no credit installed keeps the row");
    let other_fn = crate::VcgenContext::for_function("test::someone_else")
        .with_await_desugared_unsafe_call_blocks([BlockId(0)].into_iter().collect());
    assert_eq!(stand_ins(&other_fn), 1, "a credit owned by another function drops nothing");
    let owned = crate::VcgenContext::for_function(func.def_path.clone())
        .with_await_desugared_unsafe_call_blocks([BlockId(0)].into_iter().collect());
    assert_eq!(stand_ins(&owned), 0, "the owning context's credit drops the call's stand-in");
}

// ────────────────────────────────────────────────────────────────────────────
// T10 (2026-10-10): `tla-shapes-families` `cvw.rs:532/540` were reported
// "[unsafe] missing SAFETY comment on unsafe block" although a two-line
// `// SAFETY:` comment directly precedes each block. Root cause: production
// attaches NO comment (`check_unsafe(func, &[], …)`), and a raw-pointer
// reborrow `&*p` — which the separation engine never interprets — fell to the
// stand-in, whose text is false for a commented site. The exact shape:
//
//     // SAFETY: non-null and aligned; the caller's contract: it begins with a
//     // `TopFrontend` that lives for `'a`.
//     let header: &'a TopFrontend = unsafe { &*header };
// ────────────────────────────────────────────────────────────────────────────

/// `_2 = &*_1` (or `&mut *_1`) with `_1: *const u64`, at `span`.
fn cvw_reborrow_function(mutable: bool, span: SourceSpan) -> VerifiableFunction {
    let mut func = one_span_block(
        vec![Statement::Assign {
            place: Place::local(4),
            rvalue: Rvalue::Ref {
                mutable,
                place: Place { local: 1, projections: vec![Projection::Deref] },
            },
            span: span.clone(),
        }],
        Terminator::Return,
    );
    func.span = SourceSpan { file: span.file.clone(), ..SourceSpan::default() };
    func
}

fn cvw_span(line: u32, col_start: u32, col_end: u32) -> SourceSpan {
    SourceSpan {
        file: "crates/tla-shapes-families/src/cvw.rs".into(),
        line_start: line,
        col_start,
        line_end: line,
        col_end,
    }
}

#[test]
fn t10_raw_reborrow_mints_typed_row_not_missing_safety_stand_in() {
    for mutable in [false, true] {
        let func = cvw_reborrow_function(mutable, cvw_span(532, 43, 51));
        let rows = unsafe_rows(&func, &UnsafeCoverage::default());
        assert_eq!(rows, vec![raw_reborrow_message(mutable)], "mutable={mutable}");
        let row = &rows[0];
        // Still the `[unsafe` family (forced `failed` downstream), never the stand-in.
        assert!(row.starts_with(RAW_REBORROW_MSG_PREFIX) && row.starts_with("[unsafe"));
        assert!(!row.contains("missing SAFETY comment"), "{row}");
        // Not a definite violation: it stays `unproved_fail_closed`.
        assert!(!trust_types::unsafe_demand_is_definite_violation(row));
    }
}

#[test]
fn t10_raw_reborrow_row_is_identical_with_or_without_a_safety_comment() {
    // The comment is documentation: it must neither remove the row nor turn it
    // into anything a solver could prove. Production passes `&[]`; the
    // test-only attach path must not drop the row either.
    let func = cvw_reborrow_function(false, cvw_span(532, 43, 51));
    let comments = vec![
        (
            cvw_span(530, 4, 77),
            "// SAFETY: non-null and aligned; the caller's contract: it begins with a".to_string(),
        ),
        (cvw_span(531, 4, 42), "// `TopFrontend` that lives for `'a`.".to_string()),
    ];
    let mut without = Vec::new();
    check_unsafe(&func, &[], &FxHashSet::default(), &UnsafeCoverage::default(), &mut without);
    assert_eq!(without.len(), 1);
    assert!(matches!(&without[0].kind,
        VcKind::Assertion { message } if message.starts_with(RAW_REBORROW_MSG_PREFIX)));
    let mut with = Vec::new();
    check_unsafe(&func, &comments, &FxHashSet::default(), &UnsafeCoverage::default(), &mut with);
    assert_eq!(with.len(), 1, "a SAFETY comment never removes the row");
    for vc in without.iter().chain(&with) {
        assert!(matches!(vc.formula, Formula::Bool(true)), "constant: never provable");
    }
}

#[test]
fn t10_raw_read_and_unknown_statement_keep_their_existing_decisions() {
    // A raw READ the engine did not reach keeps the stand-in (unchanged), and a
    // reborrow the engine DID cover mints nothing (unchanged).
    let func = one_span_block(vec![deref_stmt(2, 1)], Terminator::Return);
    assert_eq!(
        unsafe_rows(&func, &UnsafeCoverage::default()),
        vec![MISSING_SAFETY_STANDIN_MSG.to_string()]
    );
    let func = cvw_reborrow_function(false, pm_span());
    let mut coverage = UnsafeCoverage::default();
    coverage.record_sep_row(&sep_deref_row(&func), BlockId(0), MirOp::Statement(0));
    assert!(unsafe_rows(&func, &coverage).is_empty());
}

fn cvw_block(line: u32, col: u32) -> UnsafeBlock {
    UnsafeBlock {
        span: cvw_span(line, col, col + 8),
        safety_comment: None,
        safety_claim: None,
        block_id: BlockId(0),
        origin: UnsafeOrigin::RawDeref { stmt: 0 },
    }
}

#[test]
fn t10_attach_two_line_safety_comment_exact_cvw_shapes() {
    // cvw.rs:530-532 and :538-540, each `//` line its own comment entry.
    for (safety_line, block_line, col, first, second, invariant) in [
        (
            530,
            532,
            43,
            "// SAFETY: non-null and aligned; the caller's contract: it begins with a",
            "// `TopFrontend` that lives for `'a`.",
            "non-null and aligned; the caller's contract: it begins with a",
        ),
        (
            538,
            540,
            41,
            "// SAFETY: `check` refused a null scope, and it is aligned; the caller's",
            "// contract: a non-null scope is a `ClassScope` that lives for `'a`.",
            "`check` refused a null scope, and it is aligned; the caller's",
        ),
    ] {
        let comments = vec![
            (cvw_span(safety_line, 4, 80), first.to_string()),
            (cvw_span(safety_line + 1, 4, 80), second.to_string()),
        ];
        for order in [comments.clone(), comments.iter().rev().cloned().collect()] {
            let mut blocks = vec![cvw_block(block_line, col)];
            attach_safety_comments(&mut blocks, &order);
            assert_eq!(
                blocks[0].safety_claim.as_ref().map(|c| c.invariant.as_str()),
                Some(invariant),
                "line {block_line}"
            );
        }
    }
}

#[test]
fn t10_attach_safety_line_with_many_continuations() {
    // A SAFETY line followed by three continuation lines (distance 4) attaches
    // through the chain; the old two-line window missed it.
    let comments = vec![
        (cvw_span(10, 4, 60), "// SAFETY: aligned and non-null".to_string()),
        (cvw_span(11, 4, 60), "// more prose".to_string()),
        (cvw_span(12, 4, 60), "// more prose".to_string()),
        (cvw_span(13, 4, 60), "// more prose".to_string()),
    ];
    let mut blocks = vec![cvw_block(14, 20)];
    attach_safety_comments(&mut blocks, &comments);
    assert_eq!(
        blocks[0].safety_claim.as_ref().map(|c| c.invariant.as_str()),
        Some("aligned and non-null")
    );
}

#[test]
fn t10_attach_refuses_a_comment_separated_by_code_or_blank_line() {
    // `// SAFETY: …` / `let x = 1;` / `unsafe { &*p }`: the comment documents the
    // `let`, not the block. The old "≤ 2 lines" window attached it (fail-open).
    let comments = vec![(cvw_span(10, 4, 60), "// SAFETY: aligned and non-null".to_string())];
    let mut blocks = vec![cvw_block(12, 20)];
    attach_safety_comments(&mut blocks, &comments);
    assert!(blocks[0].safety_claim.is_none(), "a code/blank line breaks attachment");
    // A non-SAFETY comment directly above does not bridge a gap either.
    let comments = vec![
        (cvw_span(9, 4, 60), "// SAFETY: aligned and non-null".to_string()),
        (cvw_span(11, 4, 60), "// unrelated note".to_string()),
    ];
    let mut blocks = vec![cvw_block(12, 20)];
    attach_safety_comments(&mut blocks, &comments);
    assert!(blocks[0].safety_claim.is_none(), "line 10 is not a comment: chain broken");
    // A comment AFTER the block on its own line is not attached.
    let comments = vec![(cvw_span(12, 40, 70), "/* SAFETY: after */".to_string())];
    let mut blocks = vec![cvw_block(12, 20)];
    attach_safety_comments(&mut blocks, &comments);
    assert!(blocks[0].safety_claim.is_none(), "a trailing comment is not attached");
    // A leading comment on the block's own line, before it, is attached.
    let comments = vec![(cvw_span(12, 4, 18), "/* SAFETY: inline */".to_string())];
    let mut blocks = vec![cvw_block(12, 20)];
    attach_safety_comments(&mut blocks, &comments);
    assert_eq!(blocks[0].safety_claim.as_ref().map(|c| c.invariant.as_str()), Some("inline"));
}

// ────────────────────────────────────────────────────────────────────────────
// SAFETY-ASSUME-1 (ruled 2026-10-17): a site the compiler DECLARED — inside a user
// `unsafe { }` block with a clippy-placed `// SAFETY:` comment — mints no stand-in
// and no `[unsafe:reborrow]` row, and the declaration scope records it, so the
// compiler can charge the block its `assumption:safety-comment` row.
// ────────────────────────────────────────────────────────────────────────────

fn declared_terminator(block: usize) -> crate::SafetyDeclaredUnsafeOps {
    let mut declared = crate::SafetyDeclaredUnsafeOps::default();
    declared.declare_terminator(BlockId(block));
    declared
}

#[test]
fn a_declared_unsafe_call_mints_no_standin_and_is_recorded() {
    let func = call_fixture("dep::adopt_startup_bridge_lanes", Ty::u32(), true, false, false);
    let empty = UnsafeCoverage::default();
    let (rows, withheld) =
        crate::with_safety_declared_unsafe_ops(&func, declared_terminator(0), || {
            unsafe_rows(&func, &empty)
        });
    assert!(rows.is_empty(), "{rows:?}");
    assert!(withheld.terminators.contains(&BlockId(0)), "{withheld:?}");
    assert!(withheld.statements.is_empty());
    // A foreign call is declared the same way (the FFI lane's own rows stay).
    let foreign = call_fixture("compute_hash", Ty::u32(), false, true, false);
    let (rows, withheld) =
        crate::with_safety_declared_unsafe_ops(&foreign, declared_terminator(0), || {
            unsafe_rows(&foreign, &empty)
        });
    assert!(rows.is_empty(), "{rows:?}");
    assert!(withheld.terminators.contains(&BlockId(0)));
}

#[test]
fn an_undeclared_site_keeps_its_standin_and_records_nothing() {
    let func = call_fixture("dep::adopt_startup_bridge_lanes", Ty::u32(), true, false, false);
    let empty = UnsafeCoverage::default();
    // No scope at all: today's row, byte-identical.
    assert_eq!(unsafe_rows(&func, &empty), vec![MISSING_SAFETY_STANDIN_MSG.to_string()]);
    // A scope that declares another block.
    let (rows, withheld) =
        crate::with_safety_declared_unsafe_ops(&func, declared_terminator(1), || {
            unsafe_rows(&func, &empty)
        });
    assert_eq!(rows, vec![MISSING_SAFETY_STANDIN_MSG.to_string()]);
    assert_eq!(withheld, crate::SafetyDeclaredWithheld::default());
    // A scope opened for ANOTHER body (another def path, or a twin at another
    // span) lends this one nothing.
    let mut other = func.clone();
    other.def_path = "test::other".to_string();
    let (rows, withheld) =
        crate::with_safety_declared_unsafe_ops(&other, declared_terminator(0), || {
            unsafe_rows(&func, &empty)
        });
    assert_eq!(rows, vec![MISSING_SAFETY_STANDIN_MSG.to_string()]);
    assert_eq!(withheld, crate::SafetyDeclaredWithheld::default());
    let mut twin = func.clone();
    twin.span = mint_site_span();
    let (rows, _) = crate::with_safety_declared_unsafe_ops(&twin, declared_terminator(0), || {
        unsafe_rows(&func, &empty)
    });
    assert_eq!(rows, vec![MISSING_SAFETY_STANDIN_MSG.to_string()]);
    // And the scope is closed afterwards.
    assert_eq!(unsafe_rows(&func, &empty), vec![MISSING_SAFETY_STANDIN_MSG.to_string()]);
}

#[test]
fn a_declaration_never_replaces_a_typed_refutation_or_a_covered_site() {
    let empty = UnsafeCoverage::default();
    // `mem::zeroed::<&u64>()` is decided on the type: it stays refuted.
    let bad = call_fixture("core::mem::zeroed::<&u64>", reference(Ty::u64()), true, false, false);
    let (rows, withheld) =
        crate::with_safety_declared_unsafe_ops(&bad, declared_terminator(0), || {
            unsafe_rows(&bad, &empty)
        });
    assert_eq!(rows.len(), 1, "{rows:?}");
    assert!(rows[0].starts_with("[unsafe:zeroed]"), "{}", rows[0]);
    assert_eq!(withheld, crate::SafetyDeclaredWithheld::default());
    // A site another row already covers mints nothing and is NOT recorded: the
    // compiler then charges no assumption for it.
    let func = call_fixture("misc_calls::danger", Ty::u32(), true, false, false);
    let evidence = compiler_refuted_block_zero();
    let (rows, withheld) =
        crate::with_safety_declared_unsafe_ops(&func, declared_terminator(0), || {
            unsafe_rows(&func, &evidence)
        });
    assert!(rows.is_empty(), "{rows:?}");
    assert_eq!(withheld, crate::SafetyDeclaredWithheld::default());
}

#[test]
fn a_declared_raw_reborrow_is_withheld_only_at_its_own_statement_and_span() {
    let span = cvw_span(532, 43, 51);
    let func = cvw_reborrow_function(false, span.clone());
    let empty = UnsafeCoverage::default();
    let mut declared = crate::SafetyDeclaredUnsafeOps::default();
    declared.declare_statement(BlockId(0), 0, span.clone());
    let (rows, withheld) =
        crate::with_safety_declared_unsafe_ops(&func, declared, || unsafe_rows(&func, &empty));
    assert!(rows.is_empty(), "{rows:?}");
    assert!(withheld.statements.contains(&(BlockId(0), 0)));
    // A statement recorded with another span (a numbering that diverged between
    // the compiler and the extractor) keeps the typed row.
    let mut skewed = crate::SafetyDeclaredUnsafeOps::default();
    skewed.declare_statement(BlockId(0), 0, cvw_span(540, 43, 51));
    let (rows, withheld) =
        crate::with_safety_declared_unsafe_ops(&func, skewed, || unsafe_rows(&func, &empty));
    assert_eq!(rows, vec![raw_reborrow_message(false)]);
    assert_eq!(withheld, crate::SafetyDeclaredWithheld::default());
    // A declared TERMINATOR never speaks for a statement of the same block.
    let (rows, _) = crate::with_safety_declared_unsafe_ops(&func, declared_terminator(0), || {
        unsafe_rows(&func, &empty)
    });
    assert_eq!(rows, vec![raw_reborrow_message(false)]);
}

// SAFETY-ASSUME-1, review 2026-10-17: a declaration covers only what Trust does NOT
// model. A call Trust MODELS whose row the engine did not mint (a body it declined,
// a budget, a shape its recognizer missed) is an engine gap, so it keeps its FAILED
// stand-in in a declared block and is not recorded. Each test declares BOTH
// terminators of one body, as one source `unsafe { }` block holding two calls would,
// and the unmodeled call beside the modeled one is the negative control: it is
// withheld and recorded.

fn declared_terminators(blocks: &[usize]) -> crate::SafetyDeclaredUnsafeOps {
    let mut declared = crate::SafetyDeclaredUnsafeOps::default();
    for &block in blocks {
        declared.declare_terminator(BlockId(block));
    }
    declared
}

/// `func` (a one-call fixture: `bb0` calls, `bb1` returns) with a SECOND unsafe call
/// at `bb1`, to the user `unsafe fn` `dep::danger`, which carries no vocabulary tag;
/// `bb2` returns. The new call reuses `bb0`'s span, so both sites sit in one block.
fn with_unmodeled_call_after(mut func: VerifiableFunction) -> VerifiableFunction {
    let span = match &func.body.blocks[0].terminator {
        Terminator::Call { span, .. } => span.clone(),
        _ => unreachable!("the fixture's first block is the call"),
    };
    let callee = "dep::danger";
    func.body.blocks[1] = BasicBlock {
        id: BlockId(1),
        stmts: vec![],
        terminator: Terminator::Call {
            unwind: UnwindEdge::Unreachable,
            is_unsafe_sig: true,
            callee_identity: None,
            callee_key: crate::sep_engine::tests::fixture_key(callee),
            is_foreign: false,
            func: callee.to_string(),
            args: vec![],
            dest: Place::local(0),
            target: Some(BlockId(2)),
            span,
            atomic: None,
        },
    };
    func.body.blocks.push(BasicBlock {
        id: BlockId(2),
        stmts: vec![],
        terminator: Terminator::Return,
    });
    func
}

fn block_set(blocks: &[usize]) -> FxHashSet<BlockId> {
    blocks.iter().map(|&block| BlockId(block)).collect()
}

#[test]
fn a_declared_unchecked_index_with_no_bounds_row_keeps_its_standin() {
    // A scalar `get_unchecked` on a slice: the one shape whose stand-in the engine's
    // `UncheckedIndexBounds` row supersedes. No row was minted for its terminator.
    let func = with_unmodeled_call_after(unchecked_call_fn(
        "core::slice::<impl [T]>::get_unchecked",
        ref_slice_u8(false),
        Ty::usize(),
    ));
    let empty = UnsafeCoverage::default();
    let (rows, withheld) =
        crate::with_safety_declared_unsafe_ops(&func, declared_terminators(&[0, 1]), || {
            unsafe_rows(&func, &empty)
        });
    // The modeled index keeps its FAILED stand-in, and is not recorded.
    assert_eq!(rows, vec![MISSING_SAFETY_STANDIN_MSG.to_string()]);
    // Negative control: the unmodeled call in the same declared block is withheld.
    assert_eq!(withheld.terminators, block_set(&[1]), "{withheld:?}");
    assert!(withheld.statements.is_empty());
    // With the engine's row minted for `bb0` the index is superseded, so the block's
    // only stand-in left is the withheld one: no row at all.
    let (rows, withheld) =
        crate::with_safety_declared_unsafe_ops(&func, declared_terminators(&[0, 1]), || {
            unsafe_rows(&func, &unchecked_index_coverage(&func))
        });
    assert!(rows.is_empty(), "{rows:?}");
    assert_eq!(withheld.terminators, block_set(&[1]), "{withheld:?}");
}

#[test]
fn a_declared_vocabulary_call_with_no_separation_row_keeps_its_standin() {
    // Sysroot items of the declared vocabulary (`modeled_sysroot_item` is `Some`),
    // none of them one of the three typed blanket-only operations, and none with a
    // `sep_call_sites` row: the engine minted nothing for the call.
    let empty = UnsafeCoverage::default();
    for modeled in [
        "core::ptr::read::<u8>",
        "core::ptr::drop_in_place::<u8>",
        "core::mem::transmute::<u32, f32>",
        "core::alloc::layout::Layout::from_size_align_unchecked",
    ] {
        assert!(
            crate::sep_engine::tests::fixture_key(modeled)
                .is_some_and(|key| key.modeled_sysroot_item().is_some()),
            "{modeled}: the fixture must name a vocabulary item"
        );
        let func = with_unmodeled_call_after(call_fixture(modeled, Ty::u32(), true, false, false));
        let (rows, withheld) =
            crate::with_safety_declared_unsafe_ops(&func, declared_terminators(&[0, 1]), || {
                unsafe_rows(&func, &empty)
            });
        assert_eq!(rows, vec![MISSING_SAFETY_STANDIN_MSG.to_string()], "{modeled}");
        // Negative control: the unmodeled call beside it is withheld.
        assert_eq!(withheld.terminators, block_set(&[1]), "{modeled}: {withheld:?}");
    }
    // A FOREIGN memory-map callee (the `extern`-block `mmap` the map recognizer
    // names, `libc`'s or the caller's own) is modeled the same way: the compiler
    // mints no `[unsafe:unmodeled-call]` for a foreign item, and the `[unsafe:sep:map]`
    // row is the one the coverage arm trusts for it.
    for foreign_map in ["libc::{extern#0}::mmap", "localextern::{extern#0}::mmap64"] {
        let mmap =
            with_unmodeled_call_after(call_fixture(foreign_map, Ty::u32(), true, true, false));
        let (rows, withheld) =
            crate::with_safety_declared_unsafe_ops(&mmap, declared_terminators(&[0, 1]), || {
                unsafe_rows(&mmap, &empty)
            });
        assert_eq!(rows, vec![MISSING_SAFETY_STANDIN_MSG.to_string()], "{foreign_map}");
        assert_eq!(withheld.terminators, block_set(&[1]), "{foreign_map}: {withheld:?}");
        // With the engine's `[unsafe:sep:map]` row recorded for `bb0`, it is covered.
        let mut mapped = UnsafeCoverage::default();
        mapped.sep_call_sites.insert(BlockId(0));
        let (rows, withheld) =
            crate::with_safety_declared_unsafe_ops(&mmap, declared_terminators(&[0, 1]), || {
                unsafe_rows(&mmap, &mapped)
            });
        assert!(rows.is_empty(), "{foreign_map}: {rows:?}");
        assert_eq!(withheld.terminators, block_set(&[1]), "{foreign_map}: {withheld:?}");
    }
    // With the engine's row recorded for `bb0`, the vocabulary call is covered.
    let func = with_unmodeled_call_after(call_fixture(
        "core::ptr::read::<u8>",
        Ty::u32(),
        true,
        false,
        false,
    ));
    let mut covered = UnsafeCoverage::default();
    covered.sep_call_sites.insert(BlockId(0));
    let (rows, withheld) =
        crate::with_safety_declared_unsafe_ops(&func, declared_terminators(&[0, 1]), || {
            unsafe_rows(&func, &covered)
        });
    assert!(rows.is_empty(), "{rows:?}");
    assert_eq!(withheld.terminators, block_set(&[1]), "{withheld:?}");
    // And when `bb0`'s callee is unmodeled too, both sites are withheld.
    let func = with_unmodeled_call_after(call_fixture(
        "dep::adopt_startup_bridge_lanes",
        Ty::u32(),
        true,
        false,
        false,
    ));
    let (rows, withheld) =
        crate::with_safety_declared_unsafe_ops(&func, declared_terminators(&[0, 1]), || {
            unsafe_rows(&func, &empty)
        });
    assert!(rows.is_empty(), "{rows:?}");
    assert_eq!(withheld.terminators, block_set(&[0, 1]), "{withheld:?}");
}

#[test]
fn a_declared_rust_wrapper_map_call_is_unmodeled_and_never_keeps_a_standin() {
    // `memmap2::MmapMut::map_mut` is a Rust `unsafe fn` outside the sysroot. The map
    // recognizer names it, so the coverage arm trusts its `[unsafe:sep:map]` row, but
    // the COMPILER does not model it (`call_has_unsafe_model_keyed` is false), so
    // vcgen does not count it modeled either: no declared block can hold a stand-in
    // for it that production would ever mint.
    let callee = "memmap2::MmapMut::map_mut";
    assert!(crate::sep_engine::is_external_map_call(&callee.to_lowercase()));
    let key = crate::sep_engine::tests::fixture_key(callee).expect("a key");
    assert!(key.modeled_sysroot_item().is_none() && !key.krate_is_real_sysroot);
    assert!(!crate::call_has_unsafe_model_keyed(&key, callee));
    let mmap = with_unmodeled_call_after(call_fixture(callee, Ty::u32(), true, false, false));
    // No compiler evidence (a caller that is not the compiler): declared like any
    // other unmodeled call, beside the negative control.
    let (rows, withheld) =
        crate::with_safety_declared_unsafe_ops(&mmap, declared_terminators(&[0, 1]), || {
            unsafe_rows(&mmap, &UnsafeCoverage::default())
        });
    assert!(rows.is_empty(), "{rows:?}");
    assert_eq!(withheld.terminators, block_set(&[0, 1]), "{withheld:?}");
    // PRODUCTION'S SHAPE: the compiler minted `[unsafe:unmodeled-call]` for `bb0` and
    // withheld it in the declared block itself, so the evidence set still names
    // `bb0`. The compiler-evidence arm answers `Covered`: no stand-in, and vcgen does
    // not record `bb0` (the compiler charges the block for its own withholding).
    let evidence = compiler_refuted_block_zero();
    let (rows, withheld) =
        crate::with_safety_declared_unsafe_ops(&mmap, declared_terminators(&[0, 1]), || {
            unsafe_rows(&mmap, &evidence)
        });
    assert!(rows.is_empty(), "{rows:?}");
    assert_eq!(withheld.terminators, block_set(&[1]), "{withheld:?}");
    // And with the engine's `[unsafe:sep:map]` row for `bb0` as well, the separation
    // arm covers it first; that row is a real obligation and is never withheld.
    let mut mapped = compiler_refuted_block_zero();
    mapped.sep_call_sites.insert(BlockId(0));
    let (rows, withheld) =
        crate::with_safety_declared_unsafe_ops(&mmap, declared_terminators(&[0, 1]), || {
            unsafe_rows(&mmap, &mapped)
        });
    assert!(rows.is_empty(), "{rows:?}");
    assert_eq!(withheld.terminators, block_set(&[1]), "{withheld:?}");
}

#[test]
fn a_declared_raw_read_with_no_deref_row_keeps_its_standin() {
    // One block: two raw-pointer READS (`_2 = copy (*_1)`, `_5 = CopyForDeref(*_1)`)
    // and a raw REBORROW (`_4 = &(*_3)`), every statement declared. Trust models a
    // raw read (the engine's `[unsafe:sep:deref]` rows), so a read the engine did
    // not interpret is an engine gap: it keeps its FAILED stand-in and is not
    // recorded. The reborrow, which the engine never interprets, is the negative
    // control: it is withheld and recorded.
    let copy_for_deref = Statement::Assign {
        place: Place::local(5),
        rvalue: Rvalue::CopyForDeref(Place { local: 1, projections: vec![Projection::Deref] }),
        span: pm_span(),
    };
    let func = one_span_block(
        vec![deref_stmt(2, 1), copy_for_deref, reborrow_stmt(4, 3)],
        Terminator::Return,
    );
    let declared = || {
        let mut declared = crate::SafetyDeclaredUnsafeOps::default();
        for index in 0..3 {
            declared.declare_statement(BlockId(0), index, pm_span());
        }
        declared
    };
    let only_the_reborrow: FxHashSet<(BlockId, usize)> = [(BlockId(0), 2)].into_iter().collect();
    let (rows, withheld) = crate::with_safety_declared_unsafe_ops(&func, declared(), || {
        unsafe_rows(&func, &UnsafeCoverage::default())
    });
    assert_eq!(rows, vec![MISSING_SAFETY_STANDIN_MSG.to_string(); 2]);
    assert_eq!(withheld.statements, only_the_reborrow, "{withheld:?}");
    assert!(withheld.terminators.is_empty());
    // With the engine's `[unsafe:sep:deref]` row recorded for each read, both are
    // covered, and the reborrow is still the one site withheld.
    let mut coverage = UnsafeCoverage::default();
    for index in 0..2 {
        coverage.record_sep_row(&sep_deref_row(&func), BlockId(0), MirOp::Statement(index));
    }
    let (rows, withheld) =
        crate::with_safety_declared_unsafe_ops(&func, declared(), || unsafe_rows(&func, &coverage));
    assert!(rows.is_empty(), "{rows:?}");
    assert_eq!(withheld.statements, only_the_reborrow, "{withheld:?}");
}
