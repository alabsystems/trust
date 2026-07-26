// Regression: the guarded-index bounds VC formula must carry the dominating
// guard (it is wrapped by v2_formula_with_path_guards inside
// generate_v2_safety_vcs) — a bare guard-negation would be satisfiable and
// unprovable by every engine.
use trust_types::*;
use trust_vcgen::generate_vcs;

#[test]
fn guarded_index_bounds_vc_formula_carries_dominating_guard() {
    // if i < 16 { palette[i] } else { 0 }  (palette: [u32; 16], i: usize)
    let func = VerifiableFunction {
        name: "palette_lookup".to_string(),
        def_path: "diag::palette_lookup".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::Array { elem: Box::new(Ty::u32()), len: 16 }, name: Some("palette".into()) },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("i".into()) },
                LocalDecl { index: 3, ty: Ty::Bool, name: None },
                LocalDecl { index: 4, ty: Ty::Bool, name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Lt,
                            Operand::Copy(Place::local(2)),
                            Operand::Constant(ConstValue::Uint(16, 64)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(3)),
                        targets: vec![(0, BlockId(3))],
                        otherwise: BlockId(1),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Lt,
                            Operand::Copy(Place::local(2)),
                            Operand::Constant(ConstValue::Uint(16, 64)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Assert { unwind: trust_types::UnwindEdge::Unreachable,
                        cond: Operand::Copy(Place::local(4)),
                        expected: true,
                        msg: AssertMessage::BoundsCheck,
                        target: BlockId(2),
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place {
                            local: 1,
                            projections: vec![Projection::Index(2)],
                        })),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
                BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let vcs = generate_vcs(&func);
    let vc = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::IndexOutOfBounds))
        .expect("guarded indexing should produce an IndexOutOfBounds VC");
    let dbg = format!("{:?}", vc.formula);
    assert!(
        dbg.contains("Lt(Var(\"i\", Int), Int(16))"),
        "the dominating guard i < 16 must be conjoined: {dbg}"
    );
    assert!(
        dbg.contains("Ge(Var(\"i\", Int), Int(16))"),
        "the violation i >= 16 must be present: {dbg}"
    );
}
