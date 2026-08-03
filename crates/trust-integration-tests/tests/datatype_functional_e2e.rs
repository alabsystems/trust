//! Non-recursive datatype functional lane, end to end.
//!
//! The VC generator emits a positive constructor equation through its dedicated
//! API; trust-certify consumes that exact typed VC and kernel-checks the
//! corresponding reflexivity proof. It is deliberately not routed through the
//! generic violation-formula solver path, where SAT has the opposite meaning.

use trust_certify::datatype_functional::{
    certify_datatype_functional_vc, recheck_datatype_functional_vc, sort_arm_functional_vc_formula,
};
use trust_ir::ProofEvidence;
use trust_types::{
    AggregateKind, BasicBlock, BlockId, LocalDecl, Operand, Place, Rvalue, SourceSpan, Statement,
    Terminator, Ty, VerifiableBody, VerifiableFunction,
};
use trust_vcgen::datatype_functional::datatype_functional_vcs;

fn level_ref() -> Ty {
    Ty::Datatype { name: "Level".to_string(), variants: Vec::new() }
}

fn exprkind_ref() -> Ty {
    Ty::Datatype { name: "ExprKind".to_string(), variants: Vec::new() }
}

fn level_dt() -> Ty {
    Ty::Datatype {
        name: "Level".to_string(),
        variants: vec![
            ("Zero".to_string(), vec![]),
            ("Succ".to_string(), vec![("0".to_string(), level_ref())]),
            (
                "Max".to_string(),
                vec![("0".to_string(), level_ref()), ("1".to_string(), level_ref())],
            ),
            (
                "IMax".to_string(),
                vec![("0".to_string(), level_ref()), ("1".to_string(), level_ref())],
            ),
            ("Param".to_string(), vec![("0".to_string(), Ty::Int { width: 64, signed: false })]),
        ],
    }
}

fn exprkind_dt() -> Ty {
    Ty::Datatype {
        name: "ExprKind".to_string(),
        variants: vec![
            ("BVar".to_string(), vec![("0".to_string(), Ty::Int { width: 32, signed: false })]),
            ("Sort".to_string(), vec![("0".to_string(), level_ref())]),
            ("Const".to_string(), vec![("0".to_string(), Ty::Int { width: 64, signed: false })]),
        ],
    }
}

fn expr_dt() -> Ty {
    Ty::Datatype {
        name: "Expr".to_string(),
        variants: vec![(
            "Expr".to_string(),
            vec![
                ("kind".to_string(), exprkind_ref()),
                ("meta".to_string(), Ty::Int { width: 64, signed: false }),
            ],
        )],
    }
}

fn local(index: usize, ty: Ty, name: Option<&str>) -> LocalDecl {
    LocalDecl { index, ty, name: name.map(str::to_string) }
}

fn assign(local: usize, rvalue: Rvalue) -> Statement {
    Statement::Assign { place: Place::local(local), rvalue, span: SourceSpan::default() }
}

fn representative_sort_arm() -> VerifiableFunction {
    VerifiableFunction {
        name: "infer_sort_arm".to_string(),
        def_path: "test::infer_sort_arm".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                local(0, expr_dt(), None),
                local(1, level_dt(), Some("l")),
                local(2, Ty::Int { width: 64, signed: false }, Some("meta")),
                local(3, level_dt(), None),
                local(4, exprkind_dt(), None),
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    assign(
                        3,
                        Rvalue::Aggregate(
                            AggregateKind::Adt {
                                name: "Level".to_string(),
                                variant: 1,
                                active_field: None,
                                args: None,
                            },
                            vec![Operand::Move(Place::local(1))],
                        ),
                    ),
                    assign(
                        4,
                        Rvalue::Aggregate(
                            AggregateKind::Adt {
                                name: "ExprKind".to_string(),
                                variant: 1,
                                active_field: None,
                                args: None,
                            },
                            vec![Operand::Move(Place::local(3))],
                        ),
                    ),
                    assign(
                        0,
                        Rvalue::Aggregate(
                            AggregateKind::Adt {
                                name: "Expr".to_string(),
                                variant: 0,
                                active_field: None,
                                args: None,
                            },
                            vec![Operand::Move(Place::local(4)), Operand::Move(Place::local(2))],
                        ),
                    ),
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: expr_dt(),
        },
        contracts: Vec::new(),
        preconditions: Vec::new(),
        postconditions: Vec::new(),
        spec: Default::default(),
    }
}

#[test]
fn emitted_nonrecursive_sort_arm_equation_is_kernel_certified() {
    let vcs = datatype_functional_vcs(&representative_sort_arm());
    assert_eq!(vcs.len(), 1);
    assert_eq!(vcs[0].formula, sort_arm_functional_vc_formula());

    let evidence = certify_datatype_functional_vc(&vcs[0])
        .expect("the exact emitted positive equation is certified by the dedicated lane");
    let ProofEvidence::CleanCic { term, context, lineage, .. } = evidence else {
        panic!("datatype functional lane must mint CleanCic evidence");
    };
    assert!(recheck_datatype_functional_vc(&vcs[0], &term, &context, &lineage));

    let mut substituted = vcs[0].clone();
    substituted.function = trust_types::Symbol::intern("different_public_function");
    assert!(
        certify_datatype_functional_vc(&substituted).is_none(),
        "an identical formula under a different typed obligation identity must fail closed"
    );
    assert!(
        !recheck_datatype_functional_vc(&substituted, &term, &context, &lineage),
        "lineage must bind the producer's full VC identity"
    );
}
