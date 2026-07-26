use trust_types::{
    BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan,
    Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
};

use super::build_const_param_range_facts;

/// `fn f<const N: usize>(i: usize)` with a guard compare `i < N` — the N
/// operand carries (width=64, signed=false).
fn constparam_cmp_func() -> VerifiableFunction {
    VerifiableFunction {
        name: "cp".to_string(),
        def_path: "test::cp".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("ret".into()) },
                LocalDecl {
                    index: 1,
                    ty: Ty::Int { width: 64, signed: false },
                    name: Some("i".into()),
                },
                LocalDecl { index: 2, ty: Ty::Bool, name: None },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Lt,
                        Operand::Copy(Place::local(1)),
                        Operand::Constant(ConstValue::ConstParam {
                            index: 0,
                            name: "N".to_string(),
                            width: 64,
                            signed: false,
                        }),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// A usize const-param symbol gets pinned to `0 <= N <= u64::MAX` — the range
/// whose absence let the solver pick `N = 2^64` and false-refute `i += 1` in
/// a `while i < N` loop.
#[test]
fn usize_const_param_pinned_to_type_range() {
    let func = constparam_cmp_func();
    let facts = build_const_param_range_facts(&func);
    assert_eq!(facts.len(), 2, "lower + upper bound; got {facts:?}");
    let rendered: Vec<String> = facts.iter().map(|f| format!("{f:?}")).collect();
    assert!(
        rendered.iter().any(|s| s.contains("__trust_constparam_0_N") && s.contains("18446744073709551615")),
        "upper bound must be u64::MAX; got {rendered:?}"
    );
    assert!(
        rendered.iter().any(|s| s.contains("Int(0)")),
        "lower bound must be 0; got {rendered:?}"
    );
}

/// A BOOL const-generic (width 1, unsigned) is Bool-sorted — NO integer range
/// fact may be emitted for it (an Int bound on a Bool var would be ill-sorted).
#[test]
fn bool_const_param_skipped() {
    let mut func = constparam_cmp_func();
    if let Statement::Assign { rvalue: Rvalue::BinaryOp(_, _, op), .. } =
        &mut func.body.blocks[0].stmts[0]
    {
        *op = Operand::Constant(ConstValue::ConstParam {
            index: 0,
            name: "B".to_string(),
            width: 1,
            signed: false,
        });
    }
    assert!(build_const_param_range_facts(&func).is_empty());
}

/// A `SymArray` length symbol in a local's TYPE is pinned even with no value
/// operand in the body (the bounds VC reads the length symbol directly).
#[test]
fn symarray_len_symbol_pinned_from_type() {
    let mut func = constparam_cmp_func();
    func.body.blocks[0].stmts.clear();
    func.body.locals.push(LocalDecl {
        index: 3,
        ty: Ty::Ref {
            mutable: false,
            inner: Box::new(Ty::SymArray {
                elem: Box::new(Ty::Int { width: 32, signed: false }),
                len_sym: trust_types::ConstLen { index: 0, name: "N".to_string() },
            }),
        },
        name: Some("a".into()),
    });
    let facts = build_const_param_range_facts(&func);
    assert_eq!(facts.len(), 2, "SymArray len must be pinned; got {facts:?}");
}
