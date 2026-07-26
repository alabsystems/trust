use trust_types::UnwindEdge;
use trust_types::{
    BasicBlock, BlockId, Formula, LocalDecl, Operand, Place, Sort, SourceSpan, Terminator, Ty,
    VerifiableBody, VerifiableFunction,
};

use super::build_semantic_guard_map;

/// `fn f(x: T) { _2 = callee(copy x) }` — one call, one successor block.
fn wrapping_neg_fn(ty: Ty, callee: &str) -> VerifiableFunction {
    VerifiableFunction {
        name: "f".into(),
        def_path: "f".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".into()) },
                LocalDecl { index: 1, ty: ty.clone(), name: Some("x".into()) },
                LocalDecl { index: 2, ty, name: Some("n".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        func: callee.into(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(2),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_unsafe_sig: false,
                        is_foreign: false,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn successor_guards(func: &VerifiableFunction) -> Vec<Formula> {
    build_semantic_guard_map(func).get(&BlockId(1)).cloned().unwrap_or_default()
}

#[test]
fn signed_i128_wrapping_neg_gets_exact_ite_definition() {
    let func = wrapping_neg_fn(Ty::i128(), "core::num::<impl i128>::wrapping_neg");
    let x = || Box::new(Formula::Var("x".into(), Sort::Int));
    let min = || Box::new(Formula::Int(i128::MIN));
    let expected = Formula::Eq(
        Box::new(Formula::Var("n#s0_t".into(), Sort::Int)),
        Box::new(Formula::Ite(
            Box::new(Formula::Eq(x(), min())),
            min(),
            Box::new(Formula::Sub(Box::new(Formula::Int(0)), x())),
        )),
    );
    assert!(
        successor_guards(&func).contains(&expected),
        "signed wrapping_neg must pin dest == ite(x == MIN, MIN, -x) at FULL i128 width: {:?}",
        successor_guards(&func)
    );
}

#[test]
fn bare_ssa_variant_renames_versioned_call_dest_to_bare() {
    // The wrapping_neg guard names its subject `n#s0_t`; the SSA local `n`
    // (single call-dest write) makes the bare-renamed copy an identity —
    // this is what lets the fact bind a callsite ¬P[σ]'s bare `n`.
    let func = wrapping_neg_fn(Ty::i64(), "core::num::<impl i64>::wrapping_neg");
    let guards = successor_guards(&func);
    let versioned = guards
        .iter()
        .find(|g| format!("{g:?}").contains("n#s0_t"))
        .expect("wrapping_neg fact present");
    let variant = super::bare_ssa_guard_variant(&func, versioned)
        .expect("SSA call dest must yield a bare variant");
    let repr = format!("{variant:?}");
    assert!(
        repr.contains("\"n\"") && !repr.contains("n#"),
        "variant must be fully bare-renamed: {repr}"
    );
}

#[test]
fn unsigned_u128_wrapping_neg_fails_closed() {
    // 2^128 - x needs a modulus Formula::Int cannot represent — no fact.
    let func = wrapping_neg_fn(Ty::u128(), "core::num::<impl u128>::wrapping_neg");
    assert!(
        successor_guards(&func).iter().all(|f| !format!("{f:?}").contains("n#")),
        "u128 wrapping_neg must emit NO dest fact (fail-closed)"
    );
}

#[test]
fn user_defined_wrapping_neg_is_not_modeled() {
    let func = wrapping_neg_fn(Ty::i64(), "mymod::wrapping_neg");
    assert!(
        successor_guards(&func).iter().all(|f| !format!("{f:?}").contains("n#")),
        "a user wrapping_neg must NOT be modeled — false value-definition channel"
    );
}
