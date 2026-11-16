//! Trust (2026-09-30, P4 — hunter Finding 1): the TRANSITIVE return pin
//! (`_0 = copy _L` plus `_L`'s defining rvalue) may only pin the definition of
//! `_L` that REACHES the copy.
//!
//! The scan used to walk the PREDECESSOR's statements first and every block
//! backwards from its END, taking the first `_L = ..` it met. Two measured false
//! proofs through the falsification gate's flags came out of that:
//!
//!  * TOO LATE — `replace(slot, v) ensures result == v`, MIR
//!    `_3 = copy (*_1); _0 = copy _3; _3 = copy _2; ...`: the write AFTER the copy
//!    was pinned, so `_0 == v` was assumed although the function returns the
//!    old value.
//!  * TOO EARLY — `let mut r = a; extr(&r); r = !r; r` with the Return block
//!    rewriting `r` before the copy: the predecessor's `r = a` was pinned, and
//!    `ensures result && !result` was PROVED.
//!
//! Each case pins the definition that reaches the copy and never the other one.

use trust_types::{
    BasicBlock, BlockId, Formula, LocalDecl, Operand, Place, Rvalue, Sort, SourceSpan, Statement,
    Terminator, Ty, VerifiableBody, VerifiableFunction,
};

use super::generate_v2_contract_vcs_impl;

fn assign(local: usize, rvalue: Rvalue) -> Statement {
    Statement::Assign { place: Place::local(local), rvalue, span: SourceSpan::default() }
}

fn copy_of(local: usize) -> Rvalue {
    Rvalue::Use(Operand::Copy(Place::local(local)))
}

/// `fn f(a: u64, v: u64) -> u64` with one named body local `r` (`_3`), `ensures`
/// `result == <param>`.
fn func(blocks: Vec<BasicBlock>, ensures_param: usize) -> VerifiableFunction {
    let local = |index: usize, name: Option<&str>| LocalDecl {
        index,
        ty: Ty::u64(),
        name: name.map(Into::into),
    };
    let param = ["", "a", "v"][ensures_param];
    VerifiableFunction {
        name: "f".into(),
        def_path: "f".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                local(0, None),
                local(1, Some("a")),
                local(2, Some("v")),
                local(3, Some("r")),
            ],
            blocks,
            arg_count: 2,
            return_ty: Ty::u64(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![Formula::Eq(
            Box::new(Formula::Var("_0".into(), Sort::Int)),
            Box::new(Formula::Var(param.into(), Sort::Int)),
        )],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn postcondition_formulas(f: &VerifiableFunction) -> Vec<String> {
    generate_v2_contract_vcs_impl(f, None)
        .into_iter()
        .filter(|vc| matches!(vc.kind, trust_types::VcKind::Postcondition))
        .map(|vc| format!("{:?}", vc.formula))
        .collect()
}

/// `r = a; _0 = r; r = v; return` — the returned value is `a`.
#[test]
fn a_write_after_the_copy_is_never_pinned() {
    let f = func(
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![assign(3, copy_of(1)), assign(0, copy_of(3)), assign(3, copy_of(2))],
            terminator: Terminator::Return,
        }],
        2,
    );
    let formulas = postcondition_formulas(&f);
    assert!(!formulas.is_empty(), "the clause must raise a postcondition row");
    for formula in &formulas {
        assert!(
            !formula.contains(r#"Eq(Var("_0", Int), Var("v", Int)), Eq("#)
                && !formula.contains(r#"[Eq(Var("_0", Int), Var("v", Int))"#),
            "the write `r = v` AFTER `_0 = copy r` must not be pinned as the return \
             value: {formula}"
        );
    }
}

/// `bb0: r = a; goto bb1` / `bb1: r = v; _0 = r; return` — the returned value is
/// `v`, and the predecessor's `r = a` must not be pinned.
#[test]
fn a_predecessor_write_the_return_block_overwrites_is_never_pinned() {
    let f = func(
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![assign(3, copy_of(1))],
                terminator: Terminator::Goto(BlockId(1)),
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![assign(3, copy_of(2)), assign(0, copy_of(3))],
                terminator: Terminator::Return,
            },
        ],
        1,
    );
    let formulas = postcondition_formulas(&f);
    assert!(!formulas.is_empty(), "the clause must raise a postcondition row");
    for formula in &formulas {
        assert!(
            !formula.contains(r#"[Eq(Var("_0", Int), Var("a", Int))"#),
            "the predecessor's `r = a`, overwritten before the copy, must not be \
             pinned as the return value: {formula}"
        );
    }
}
