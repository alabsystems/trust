use trust_types::UnwindEdge;
use trust_types::{
    BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan, Statement,
    Terminator, Ty, VerifiableBody, VerifiableFunction,
};

use super::terminator_def_names;

/// `fn f(r: &mut u32, a: u32)` with a `&mut x`-style borrow statement and a
/// call terminator whose args we vary.
fn call_func(args: Vec<Operand>, extra_stmt: Option<Statement>) -> VerifiableFunction {
    let mut stmts = vec![Statement::Assign {
        place: Place::local(3),
        rvalue: Rvalue::Ref { mutable: true, place: Place::local(4) },
        span: SourceSpan::default(),
    }];
    stmts.extend(extra_stmt);
    VerifiableFunction {
        name: "f".to_string(),
        def_path: "test::f".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("ret".into()) },
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref {
                        mutable: true,
                        inner: Box::new(Ty::Int { width: 32, signed: false }),
                    },
                    name: Some("r".into()),
                },
                LocalDecl {
                    index: 2,
                    ty: Ty::Int { width: 32, signed: false },
                    name: Some("a".into()),
                },
                LocalDecl {
                    index: 3,
                    ty: Ty::Ref {
                        mutable: true,
                        inner: Box::new(Ty::Int { width: 32, signed: false }),
                    },
                    name: None,
                },
                LocalDecl {
                    index: 4,
                    ty: Ty::Int { width: 32, signed: false },
                    name: Some("x".into()),
                },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts,
                terminator: Terminator::Call {
                    unwind: UnwindEdge::Unreachable,
                    func: "test::callee".to_string(),
                    args,
                    dest: Place::local(0),
                    target: Some(BlockId(1)),
                    span: SourceSpan::default(),
                    atomic: None,
                    is_unsafe_sig: false,
                    is_foreign: false,
                },
            }],
            arg_count: 2,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// Pure-scalar args (a Copy u32 + a constant): the callee cannot reach any
/// local, so ONLY the dest is killed — guard facts on `*r`/`x` survive.
#[test]
fn scalar_args_skip_the_global_havoc() {
    let func = call_func(
        vec![Operand::Copy(Place::local(2)), Operand::Constant(ConstValue::Uint(7, 32))],
        None,
    );
    let names = terminator_def_names(&func, &func.body.blocks[0]);
    assert_eq!(names, vec!["ret".to_string()], "only the dest; got {names:?}");
}

/// A `&mut`-typed arg keeps the FULL havoc (the callee-write class).
#[test]
fn mut_ref_arg_keeps_full_havoc() {
    let func = call_func(vec![Operand::Copy(Place::local(1))], None);
    let names = terminator_def_names(&func, &func.body.blocks[0]);
    assert!(names.len() > 1, "full havoc expected; got {names:?}");
    assert!(names.iter().any(|n| n == "r"), "the &mut param must be havoced");
    assert!(names.iter().any(|n| n == "x"), "the &mut-borrowed local must be havoced");
}

/// A Move arg fails closed (ownership escapes into the callee).
#[test]
fn move_arg_keeps_full_havoc() {
    let func = call_func(vec![Operand::Move(Place::local(2))], None);
    let names = terminator_def_names(&func, &func.body.blocks[0]);
    assert!(names.len() > 1, "full havoc expected; got {names:?}");
}

/// An in-function raw-pointer laundering site (`&raw`/cast-to-raw) fails
/// the skip for the WHOLE function even with pure-scalar args: the local's
/// address could have been smuggled through an integer to an earlier callee.
#[test]
fn pointer_laundering_site_keeps_full_havoc() {
    let func = call_func(
        vec![Operand::Copy(Place::local(2))],
        Some(Statement::Assign {
            place: Place::local(3),
            rvalue: Rvalue::AddressOf(true, Place::local(4)),
            span: SourceSpan::default(),
        }),
    );
    let names = terminator_def_names(&func, &func.body.blocks[0]);
    assert!(names.len() > 1, "laundering must fail the skip; got {names:?}");
}
