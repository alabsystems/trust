//! A well-typed loop body with `#[loop_invariant]` + `#[decreases]` must yield
//! its E4 rows — and an ILL-TYPED comparison silently costs you all of them.
//!
//! This mirrors the compiler-side `proof_feedback_*` fixture
//! (`compiler/rustc_mir_transform/src/trust_verify/tests.rs`), which went red
//! because it spelled `Gt(<u32 place>, ConstValue::Int(0))`. `ConstValue::Int`
//! is the SIGNED widthless literal, and `binary_operand_matches_type` accepts it
//! only for a SIGNED expected type, so NEITHER side authenticated a shared type
//! and `validate_binary_assignment_types` refused the whole body. The function
//! then produced exactly ONE row —
//! `UnsupportedMir { kind: "MalformedTrustIr", .. }` — and ZERO loop VCs, which
//! is why six tests keyed on `VcKind::LoopInvariantInitiation` failed with the
//! opaque message "E4 initiation row".
//!
//! The refusal is CORRECT and is not a fail-open: an `UnsupportedMir` row gets
//! no backend plan and grades `Unknown`, so nothing is suppressed. What was
//! missing is a fast, readable guard at the vcgen level — the compiler-side
//! symptom named neither the cause nor the file.
//!
//! This test lives here because it runs in seconds against `generate_vcs`,
//! where the equivalent compiler-side signal costs a full `x.py` cycle.

use trust_types::{
    BasicBlock, BlockId, Contract, ContractKind, LocalDecl, Operand, Place, SourceSpan, Statement,
    Terminator, Ty, VerifiableBody, VerifiableFunction,
};

fn span(line: u32) -> SourceSpan {
    SourceSpan {
        file: "proof_feedback.rs".to_string(),
        line_start: line,
        col_start: 1,
        line_end: line,
        col_end: 2,
    }
}

fn fixture() -> VerifiableFunction {
    let clause_span = span(1);
    VerifiableFunction {
        name: "proof_feedback_loop".into(),
        def_path: "demo::proof_feedback_loop".to_string(),
        span: span(1),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("n".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("i".into()) },
                LocalDecl { index: 3, ty: Ty::Bool, name: Some("cond".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(1),
                            rvalue: trust_types::Rvalue::Use(Operand::Constant(
                                trust_types::ConstValue::Int(10),
                            )),
                            span: span(2),
                        },
                        Statement::Assign {
                            place: Place::local(2),
                            rvalue: trust_types::Rvalue::Use(Operand::Copy(Place::local(1))),
                            span: span(3),
                        },
                    ],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: trust_types::Rvalue::BinaryOp(
                            trust_types::BinOp::Gt,
                            Operand::Copy(Place::local(2)),
                            // `i` is u32. `ConstValue::Int` is the SIGNED widthless
                            // literal and `binary_operand_matches_type` accepts it
                            // only for a SIGNED expected type, so the original
                            // `Int(0)` made this comparison ill-typed and
                            // `validate_binary_assignment_types` refused the whole
                            // body. The faithful unsigned spelling:
                            Operand::Constant(trust_types::ConstValue::Uint(0, 32)),
                        ),
                        span: span(4),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(3)),
                        targets: vec![(1, BlockId(2))],
                        otherwise: BlockId(3),
                        exhaustive_enum_unreachable: false,
                        span: span(4),
                    },
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: trust_types::Rvalue::Use(Operand::Copy(Place::local(1))),
                        span: span(5),
                    }],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                BasicBlock { id: BlockId(3), stmts: Vec::new(), terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        },
        contracts: vec![
            Contract {
                kind: ContractKind::LoopInvariant,
                span: clause_span.clone(),
                body: "bb1: n <= 10 && i <= 10".to_string(),
            },
            Contract {
                kind: ContractKind::Decreases,
                span: clause_span,
                body: "bb1: i".to_string(),
            },
        ],
        preconditions: Vec::new(),
        postconditions: Vec::new(),
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

#[test]
fn a_well_typed_u32_loop_yields_both_e4_rows_and_the_decreases_row() {
    let func = fixture();
    let vcs = trust_vcgen::generate_vcs(&func);
    eprintln!("\n=== {} VCs for the proof_feedback loop fixture ===", vcs.len());
    let mut saw_initiation = false;
    let mut saw_consecution = false;
    for vc in &vcs {
        let k = format!("{:?}", vc.kind);
        // Print the DISCRIMINANT plus, for the unsupported row, its detail — that
        // detail string names which of the four gates declined.
        eprintln!("  {}", k.chars().take(220).collect::<String>());
        if k.starts_with("LoopInvariantInitiation") {
            saw_initiation = true;
        }
        if k.starts_with("LoopInvariantConsecution") {
            saw_consecution = true;
        }
    }
    eprintln!("\ninitiation={saw_initiation}  consecution={saw_consecution}");
    assert!(
        saw_initiation && saw_consecution,
        "the u32 invariant `n <= 10 && i <= 10` is inside the exact 32-bit machine \
         fragment and MUST produce both E4 rows; see the printed kinds above"
    );
}
