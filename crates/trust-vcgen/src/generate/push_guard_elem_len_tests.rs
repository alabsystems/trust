use trust_types::UnwindEdge;
use trust_types::{
    BasicBlock, BinOp, BlockId, ConstValue, Formula, LocalDecl, Operand, Place, Rvalue,
    SourceSpan, Statement, Terminator, Ty, VcKind, VerifiableBody, VerifiableFunction,
};

use super::{build_push_guard_elem_len_map, generate_vcs};

fn vec_i64() -> Ty {
    Ty::adt("std::vec::Vec<i64>", vec![])
}
fn vec_vec_i64() -> Ty {
    Ty::adt("std::vec::Vec<std::vec::Vec<i64>>", vec![])
}
fn shared(inner: Ty) -> Ty {
    Ty::Ref { mutable: false, inner: Box::new(inner) }
}
fn mutref(inner: Ty) -> Ty {
    Ty::Ref { mutable: true, inner: Box::new(inner) }
}
fn sp() -> SourceSpan {
    SourceSpan::default()
}
fn call(func: &str, args: Vec<Operand>, dest: usize, target: usize) -> Terminator {
    Terminator::Call {
        unwind: UnwindEdge::Unreachable,
        func: func.to_string(),
        args,
        dest: Place::local(dest),
        target: Some(BlockId(target)),
        span: sp(),
        atomic: None,
        is_unsafe_sig: false,
        is_foreign: false,
    }
}
fn assign(local: usize, rvalue: Rvalue) -> Statement {
    Statement::Assign { place: Place::local(local), rvalue, span: sp() }
}
fn cp(l: usize) -> Operand {
    Operand::Copy(Place::local(l))
}
fn mv(l: usize) -> Operand {
    Operand::Move(Place::local(l))
}
fn uconst(v: u128) -> Operand {
    Operand::Constant(ConstValue::Uint(v, 64))
}

/// A push-guarded nested `Vec<Vec<i64>>` builder, faithful to the
/// `let mut m = Vec::new(); for .. { row; if row.len()<=n {return}; m.push(row) } .. m[r][col]`
/// MIR shape. Flags carve out the fail-closed variants without changing the core.
///
/// n is param local 1; m local 2; row local 3. `guarded=false` drops the length
/// guard; `pop`/`index_mut_store` add a second `&mut m` feeding a non-push method;
/// `reassign_n` reassigns the by-value param `n`.
fn build_matrix(
    guarded: bool,
    pop: bool,
    index_mut_store: bool,
    reassign_n: bool,
    write_through: bool,
) -> VerifiableFunction {
    let locals = vec![
        LocalDecl { index: 0, ty: Ty::i64(), name: Some("ret".into()) },
        LocalDecl { index: 1, ty: Ty::usize(), name: Some("n".into()) },
        LocalDecl { index: 2, ty: vec_vec_i64(), name: Some("m".into()) },
        LocalDecl { index: 3, ty: vec_i64(), name: Some("row".into()) },
        LocalDecl { index: 4, ty: shared(vec_i64()), name: None },
        LocalDecl { index: 5, ty: Ty::usize(), name: None },
        LocalDecl { index: 6, ty: Ty::Bool, name: None },
        LocalDecl { index: 7, ty: mutref(vec_vec_i64()), name: None },
        LocalDecl { index: 8, ty: Ty::Unit, name: None },
        LocalDecl { index: 9, ty: shared(vec_vec_i64()), name: None },
        LocalDecl { index: 10, ty: Ty::usize(), name: Some("r".into()) },
        LocalDecl { index: 11, ty: shared(vec_i64()), name: None },
        LocalDecl { index: 12, ty: Ty::usize(), name: Some("col".into()) },
        LocalDecl { index: 13, ty: shared(Ty::i64()), name: None },
        LocalDecl { index: 14, ty: mutref(vec_vec_i64()), name: None },
        LocalDecl { index: 15, ty: Ty::Unit, name: None },
        LocalDecl { index: 16, ty: shared(vec_i64()), name: None },
    ];

    let has_extra = pop || index_mut_store || write_through;
    let push_target = if has_extra { 9 } else { 6 };

    // bb3 guard/no-guard.
    let bb3_term = if guarded {
        Terminator::SwitchInt {
            discr: mv(6),
            targets: vec![(0, BlockId(5))],
            otherwise: BlockId(4),
            exhaustive_enum_unreachable: false,
            span: sp(),
        }
    } else {
        Terminator::Goto(BlockId(5))
    };

    // bb6: outer element read `elem = m[r]`, plus optional `n` reassignment.
    let mut bb6_stmts = vec![
        assign(9, Rvalue::Ref { mutable: false, place: Place::local(2) }),
        assign(10, Rvalue::Use(uconst(0))),
    ];
    if reassign_n {
        bb6_stmts.push(assign(1, Rvalue::Use(uconst(0))));
    }

    let mut blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![],
            terminator: call("std::vec::Vec::<Vec<i64>>::new", vec![], 2, 1),
        },
        BasicBlock {
            id: BlockId(1),
            stmts: vec![],
            terminator: call("std::vec::Vec::<i64>::new", vec![], 3, 2),
        },
        BasicBlock {
            id: BlockId(2),
            stmts: vec![assign(4, Rvalue::Ref { mutable: false, place: Place::local(3) })],
            terminator: call("std::vec::Vec::<i64>::len", vec![mv(4)], 5, 3),
        },
        BasicBlock {
            id: BlockId(3),
            stmts: vec![assign(6, Rvalue::BinaryOp(BinOp::Le, mv(5), cp(1)))],
            terminator: bb3_term,
        },
        BasicBlock { id: BlockId(4), stmts: vec![], terminator: Terminator::Return },
        BasicBlock {
            id: BlockId(5),
            stmts: vec![assign(7, Rvalue::Ref { mutable: true, place: Place::local(2) })],
            terminator: call(
                "std::vec::Vec::<Vec<i64>>::push",
                vec![mv(7), mv(3)],
                8,
                push_target,
            ),
        },
        BasicBlock {
            id: BlockId(6),
            stmts: bb6_stmts,
            terminator: call("std::ops::Index::index", vec![mv(9), cp(10)], 11, 7),
        },
        BasicBlock {
            id: BlockId(7),
            stmts: vec![assign(12, Rvalue::Use(uconst(0)))],
            terminator: call("std::ops::Index::index", vec![cp(11), cp(12)], 13, 8),
        },
        BasicBlock { id: BlockId(8), stmts: vec![], terminator: Terminator::Return },
    ];

    if has_extra {
        let mut bb9_stmts =
            vec![assign(14, Rvalue::Ref { mutable: true, place: Place::local(2) })];
        let bb9_term = if pop {
            call("std::vec::Vec::<Vec<i64>>::pop", vec![mv(14)], 15, 6)
        } else if index_mut_store {
            // `m[0] = x` lowers to an `index_mut(&mut m, 0)` call.
            call("std::ops::IndexMut::index_mut", vec![mv(14), uconst(0)], 16, 6)
        } else {
            // `*(&mut m) = other` — a write THROUGH the conduit replaces m entirely.
            bb9_stmts.push(Statement::Assign {
                place: Place { local: 14, projections: vec![trust_types::Projection::Deref] },
                rvalue: Rvalue::Use(uconst(0)),
                span: sp(),
            });
            Terminator::Goto(BlockId(6))
        };
        blocks.push(BasicBlock { id: BlockId(9), stmts: bb9_stmts, terminator: bb9_term });
    }

    VerifiableFunction {
        name: "matrix".to_string(),
        def_path: "test::matrix".to_string(),
        span: sp(),
        body: VerifiableBody { locals, blocks, arg_count: 1, return_ty: Ty::i64() },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn map_is_empty(func: &VerifiableFunction) -> bool {
    build_push_guard_elem_len_map(func).values().all(|v| v.is_empty())
}

#[test]
fn base_emits_element_length_fact() {
    let func = build_matrix(true, false, false, false, false);
    let map = build_push_guard_elem_len_map(&func);
    let facts: Vec<&Formula> = map.values().flatten().collect();
    assert!(!facts.is_empty(), "the push-guarded matrix must emit an element-length fact");
    // Every emitted fact is a strict lower bound `coll_len(m[k]) > n`.
    for f in &facts {
        assert!(
            matches!(f, Formula::Gt(_, _)) && f.to_smtlib().contains(" n)"),
            "fact must be `coll_len(m[k]) > n`, got {}",
            f.to_smtlib()
        );
    }
}

#[test]
fn inner_bounds_vc_carries_the_fact() {
    // End-to-end wiring: the inner `m[r][col]` SliceBoundsCheck VC must carry the
    // element-length upper bound `(> _NN n)`, so `col < n < len(m[r])` discharges.
    let func = build_matrix(true, false, false, false, false);
    let vcs = generate_vcs(&func);
    let carried = vcs.iter().any(|vc| {
        matches!(vc.kind, VcKind::SliceBoundsCheck | VcKind::IndexOutOfBounds)
            && vc.formula.to_smtlib().contains("(> _")
            && vc.formula.to_smtlib().contains(" n)")
    });
    assert!(carried, "inner bounds VC must carry the `coll_len(m[r]) > n` fact");
}

#[test]
fn pop_after_pushes_fails_closed() {
    // A `Vec::pop` (a `&mut m` NOT feeding push) breaks the push-only invariant.
    assert!(map_is_empty(&build_matrix(true, true, false, false, false)));
}

#[test]
fn index_mut_store_fails_closed() {
    // `m[i] = x` (`index_mut(&mut m, i)`) can overwrite an element — no invariant.
    assert!(map_is_empty(&build_matrix(true, false, true, false, false)));
}

#[test]
fn write_through_mut_conduit_fails_closed() {
    // `*(&mut m) = other` REPLACES m with an unguarded value — must fail closed.
    assert!(map_is_empty(&build_matrix(true, false, false, false, true)));
}

#[test]
fn unguarded_push_fails_closed() {
    // No dominating `row.len() <= n` guard ⇒ a pushed row may have `len <= n`.
    assert!(map_is_empty(&build_matrix(false, false, false, false, false)));
}

#[test]
fn reassigned_bound_fails_closed() {
    // `n` reassigned between the guard and the read ⇒ the bound is not stable.
    assert!(map_is_empty(&build_matrix(true, false, false, true, false)));
}
