use trust_types::UnwindEdge;
use trust_types::{
    BasicBlock, BlockId, Formula, LocalDecl, Operand, Place, SourceSpan, Statement, Terminator,
    Ty, VerifiableBody, VerifiableFunction,
};

use super::build_vec_index_dest_value_tie_facts;

fn u32_ty() -> Ty {
    Ty::Int { width: 32, signed: false }
}
fn usize_ty() -> Ty {
    Ty::Int { width: 64, signed: false }
}
fn vec_u32() -> Ty {
    Ty::adt("std::vec::Vec<u32>", vec![])
}
fn shared_vec() -> Ty {
    Ty::Ref { mutable: false, inner: Box::new(vec_u32()) }
}
fn elem_ref() -> Ty {
    Ty::Ref { mutable: false, inner: Box::new(u32_ty()) }
}
fn index_call(recv: usize, idx: usize, dest: usize, target: usize) -> Terminator {
    Terminator::Call {
        unwind: UnwindEdge::Unreachable,
        func: "<std::vec::Vec<u32> as core::ops::index::Index<usize>>::index".to_string(),
        args: vec![Operand::Copy(Place::local(recv)), Operand::Copy(Place::local(idx))],
        dest: Place::local(dest),
        target: Some(BlockId(target)),
        span: SourceSpan::default(),
        atomic: None,
        is_unsafe_sig: false,
        is_foreign: false,
    }
}

/// `fn f(v: &Vec<u32>, i: usize)` with TWO `<Vec as Index>::index(v, _k)` calls
/// through distinct index temps — the guard-read / use-read pair of `v[i]`.
fn two_index_call_func() -> VerifiableFunction {
    VerifiableFunction {
        name: "two_calls".to_string(),
        def_path: "test::two_calls".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("ret".into()) },
                LocalDecl { index: 1, ty: shared_vec(), name: Some("v".into()) },
                LocalDecl { index: 2, ty: usize_ty(), name: Some("i".into()) },
                LocalDecl { index: 3, ty: usize_ty(), name: None },
                LocalDecl { index: 4, ty: usize_ty(), name: None },
                LocalDecl { index: 5, ty: elem_ref(), name: None },
                LocalDecl { index: 6, ty: elem_ref(), name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: trust_types::Rvalue::Use(Operand::Copy(Place::local(2))),
                        span: SourceSpan::default(),
                    }],
                    terminator: index_call(1, 3, 5, 1),
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(4),
                        rvalue: trust_types::Rvalue::Use(Operand::Copy(Place::local(2))),
                        span: SourceSpan::default(),
                    }],
                    terminator: index_call(1, 4, 6, 2),
                },
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// Base case: two index calls on one shared-&Vec root emit exactly one
/// congruence fact `Or(idx_a != idx_b, (*dest_a) == (*dest_b))`.
#[test]
fn shared_vec_two_index_calls_emit_deref_congruence() {
    let func = two_index_call_func();
    let facts = build_vec_index_dest_value_tie_facts(&func);
    assert_eq!(facts.len(), 1, "expected one pair fact; got {facts:?}");
    match &facts[0] {
        Formula::Or(djs) => {
            assert_eq!(djs.len(), 2, "hypothesis + deref tie; got {djs:?}");
            assert!(
                matches!(&djs[0], Formula::Not(inner) if matches!(&**inner, Formula::Eq(..)))
            );
            assert!(matches!(&djs[1], Formula::Eq(..)));
        }
        other => panic!("expected Or(..); got {other:?}"),
    }
}

/// N1 (fact level): a `&mut Vec` root must emit NOTHING (a resize/element write
/// between the two derefs would make the tie a false-PROVE vector).
#[test]
fn mut_vec_root_declines() {
    let mut func = two_index_call_func();
    func.body.locals[1].ty = Ty::Ref { mutable: true, inner: Box::new(vec_u32()) };
    assert!(build_vec_index_dest_value_tie_facts(&func).is_empty());
}

/// `index_mut` must decline even if the types looked right — its `&mut` result
/// can write the element between the derefs.
#[test]
fn index_mut_callee_declines() {
    let mut func = two_index_call_func();
    for b in &mut func.body.blocks {
        if let Terminator::Call { func: callee, .. } = &mut b.terminator {
            *callee = "<std::vec::Vec<u32> as core::ops::index::IndexMut<usize>>::index_mut"
                .to_string();
        }
    }
    assert!(build_vec_index_dest_value_tie_facts(&func).is_empty());
}

/// A user ADT named e.g. `MyVec` must NOT inherit the Vec element-immutability
/// tie (its `index` semantics are its own).
#[test]
fn user_adt_root_declines() {
    let mut func = two_index_call_func();
    func.body.locals[1].ty =
        Ty::Ref { mutable: false, inner: Box::new(Ty::adt("mycrate::MyVec", vec![])) };
    assert!(build_vec_index_dest_value_tie_facts(&func).is_empty());
}

/// A reseated root (`v = other;` between the calls) must emit NOTHING.
#[test]
fn reseated_root_declines() {
    let mut func = two_index_call_func();
    func.body.locals.push(LocalDecl { index: 7, ty: shared_vec(), name: None });
    func.body.blocks[1].stmts.insert(
        0,
        Statement::Assign {
            place: Place::local(1),
            rvalue: trust_types::Rvalue::Use(Operand::Copy(Place::local(7))),
            span: SourceSpan::default(),
        },
    );
    assert!(build_vec_index_dest_value_tie_facts(&func).is_empty());
}
