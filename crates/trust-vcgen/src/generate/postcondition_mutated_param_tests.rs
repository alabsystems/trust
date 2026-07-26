use trust_types::{
    BasicBlock, BlockId, Formula, LocalDecl, Operand, Place, Rvalue, Sort, SourceSpan,
    Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
};

use super::postcondition_references_mutated_param;

// ensures `*r == a` — references the parameter named "a".
fn ensures_eq_ret_a() -> Formula {
    Formula::Eq(
        Box::new(Formula::Var("__ret".into(), Sort::Int)),
        Box::new(Formula::Var("a".into(), Sort::Int)),
    )
}

fn func_with(stmts: Vec<Statement>) -> VerifiableFunction {
    VerifiableFunction {
        name: "f".into(),
        def_path: "f".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::usize(), name: None },
                LocalDecl { index: 1, ty: Ty::usize(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::usize(), name: None },
            ],
            blocks: vec![BasicBlock { id: BlockId(0), stmts, terminator: Terminator::Return }],
            arg_count: 1,
            return_ty: Ty::usize(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn mut_borrow_of_param_in_ensures_is_flagged() {
    // f(mut a) { let p = &mut a; ...; a } — the &mut staleness vector. The whole-local
    // reassign scan misses `*p = ..` (place is `*p`), but the `_2 = &mut _1` borrow flags it.
    let func = func_with(vec![
        Statement::Assign {
            place: Place::local(2),
            rvalue: Rvalue::Ref { mutable: true, place: Place::local(1) },
            span: SourceSpan::default(),
        },
        Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
            span: SourceSpan::default(),
        },
    ]);
    assert!(
        postcondition_references_mutated_param(&func, &ensures_eq_ret_a()),
        "an ensures over a param mutably borrowed (&mut a) must be flagged (fail-closed)"
    );
}

#[test]
fn unborrowed_param_in_ensures_is_not_flagged() {
    // identity f(a) { a } — no mutation, `*r == a` is genuinely true and must still prove.
    let func = func_with(vec![Statement::Assign {
        place: Place::local(0),
        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
        span: SourceSpan::default(),
    }]);
    assert!(
        !postcondition_references_mutated_param(&func, &ensures_eq_ret_a()),
        "an identity ensures with no param mutation must NOT be flagged (still proves)"
    );
}
