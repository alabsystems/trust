//! Trust (2026-10-15, TRUST-KI-1015-1): `skip_edge_join_definitions` on synthetic
//! bodies, one predicate per test. The real-MIR rows (aterm-digest `Sha256::finalize`,
//! its correct reproducers and the panicking twins) are `tests/finalize_tail_realmir.rs`.
//!
//! Every body is the guard-then-clamp shape the facts exist for, an `if` without `else`:
//!
//! ```text
//! bb0: <bb0's statements>; c = Gt(copy t, const 8);
//!      switchInt(copy c) -> [0: bb2, otherwise: bb1]     // bb0 -> bb2 is the skip edge
//! bb1: <bb1's statements>; goto bb2                       // the arm the guard selects
//! bb2: return                                             // the join
//! ```
//!
//! `a` is the parameter `_1`; `k` `_2`, `n` `_3`, `t` `_4`, `c` `_5`, a spare `_6`.

use trust_types::{
    BasicBlock, BinOp, BlockId, ConstValue, Formula, LocalDecl, Operand, Place, Rvalue, Sort,
    SourceSpan, Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
};

fn assign(local: usize, rvalue: Rvalue) -> Statement {
    Statement::Assign { place: Place::local(local), rvalue, span: SourceSpan::default() }
}

fn copy(local: usize) -> Rvalue {
    Rvalue::Use(Operand::Copy(Place::local(local)))
}

fn zero() -> Rvalue {
    Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 64)))
}

/// The guard `c = t > 8`, the last statement of `bb0`.
fn guard() -> Statement {
    assign(
        5,
        Rvalue::BinaryOp(
            BinOp::Gt,
            Operand::Copy(Place::local(4)),
            Operand::Constant(ConstValue::Uint(8, 64)),
        ),
    )
}

/// The shape above with `bb0`'s statements (before the guard) and `bb1`'s given.
fn body(bb0: Vec<Statement>, bb1: Vec<Statement>) -> VerifiableFunction {
    let names = ["ret", "a", "k", "n", "t", "c", "s"];
    let tys =
        [Ty::usize(), Ty::usize(), Ty::usize(), Ty::usize(), Ty::usize(), Ty::Bool, Ty::usize()];
    let mut stmts = bb0;
    stmts.push(guard());
    VerifiableFunction {
        name: "f".into(),
        def_path: "c::f".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: names
                .iter()
                .zip(tys)
                .enumerate()
                .map(|(index, (name, ty))| LocalDecl { index, ty, name: Some((*name).into()) })
                .collect(),
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts,
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(5)),
                        targets: vec![(0, BlockId(2))],
                        otherwise: BlockId(1),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock { id: BlockId(1), stmts: bb1, terminator: Terminator::Goto(BlockId(2)) },
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::usize(),
            datatype_defs: Default::default(),
        },
        contracts: Vec::new(),
        preconditions: Vec::new(),
        postconditions: Vec::new(),
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// The facts reaching the join `bb2`.
fn at_join(func: &VerifiableFunction) -> Vec<Formula> {
    crate::generate::v2_build_path_definition_map_pub(func)
        .remove(&BlockId(2))
        .expect("the join is reached")
}

/// The skip edge's route guard `!c`, and the arm's `!!c`.
fn skip() -> Formula {
    Formula::Not(Box::new(Formula::Var("c".into(), Sort::Bool)))
}

fn arm() -> Formula {
    Formula::Not(Box::new(skip()))
}

/// `guard => lhs == rhs` is among `facts` (`rhs: None` matches any right-hand side).
fn implies(facts: &[Formula], guard: &Formula, lhs: &str, rhs: Option<&str>) -> bool {
    facts.iter().any(|f| {
        matches!(f, Formula::Implies(g, eq)
            if g.as_ref() == guard
                && matches!(eq.as_ref(), Formula::Eq(l, r)
                    if l.var_name() == Some(lhs)
                        && rhs.is_none_or(|rhs| r.var_name() == Some(rhs))))
    })
}

/// `lhs == rhs` (bare names, unguarded) is among `facts`.
fn holds(facts: &[Formula], lhs: &str, rhs: &str) -> bool {
    facts.iter().any(|f| {
        matches!(f, Formula::Eq(l, r) if l.var_name() == Some(lhs) && r.var_name() == Some(rhs))
    })
}

/// `t = copy a` reads the parameter's ENTRY value, which has no definition; the arm
/// writes `a`. At the join: `!c => t == a` (the skip edge) and `!!c => a == 0` (the arm,
/// `a`'s only definer, which the partial merge leaves alone). Red without the facts.
#[test]
fn the_skip_edge_keeps_the_guard_copy_of_an_entry_value() {
    let join = at_join(&body(vec![assign(4, copy(1))], vec![assign(1, zero())]));
    assert!(implies(&join, &skip(), "t", Some("a")), "the skip edge's `t == a`: {join:#?}");
    assert!(implies(&join, &arm(), "a", None), "the arm's `a == 0`: {join:#?}");
    assert!(!implies(&join, &arm(), "t", Some("a")), "never on the arm's route: {join:#?}");
    assert!(
        !join.iter().any(|f| matches!(f, Formula::Eq(l, _) if l.var_name() == Some("t"))),
        "no unguarded fact on `t` reaches the join: {join:#?}"
    );
}

/// aterm's spelling: the guard copies a subject the switch block itself just wrote
/// (`n = copy k; t = copy n`), and the arm writes `n` again. `n` has a total merge at
/// the join, so only the copy is restated: `!c => t == n`, and nothing more on `n`.
#[test]
fn the_guard_copy_of_a_merged_subject_is_restated_on_the_skip_edge() {
    let join =
        at_join(&body(vec![assign(3, copy(2)), assign(4, copy(3))], vec![assign(3, zero())]));
    assert!(implies(&join, &skip(), "t", Some("n")), "the skip edge's `t == n`: {join:#?}");
    assert!(!implies(&join, &arm(), "n", None), "`n`'s merge already says it: {join:#?}");
    assert!(!holds(&join, "t", "n"), "`t == n` is lost on the arm's route: {join:#?}");
}

/// A copy the switch block outlives (a later statement of the block rewrites what it
/// read) is not on the skip edge, so nothing restates it.
#[test]
fn a_copy_its_own_block_overwrites_is_not_restated() {
    let join =
        at_join(&body(vec![assign(4, copy(1)), assign(1, copy(2))], vec![assign(1, zero())]));
    assert!(!implies(&join, &skip(), "t", Some("a")), "`t == a` died in bb0: {join:#?}");
    assert!(!implies(&join, &arm(), "a", None), "no copy reads `a` at bb0's exit: {join:#?}");
}

/// A copy the join keeps (the arm writes neither side) needs no route guard and gets
/// none.
#[test]
fn a_copy_the_join_keeps_is_not_restated() {
    let join = at_join(&body(vec![assign(4, copy(1))], vec![assign(6, zero())]));
    assert!(holds(&join, "t", "a"), "`t == a` holds on both edges: {join:#?}");
    assert!(!implies(&join, &skip(), "t", Some("a")), "no guarded duplicate: {join:#?}");
}

/// A spent verify budget stops before the first outflow is computed. The join keeps
/// whatever the merges say (here nothing: `a` has one definer) and gets no restated fact.
/// Fewer facts is the sound degradation: PROVE can turn into FAIL, never the reverse.
#[test]
fn a_spent_verify_budget_restates_nothing() {
    let func = body(vec![assign(4, copy(1))], vec![assign(1, zero())]);
    let base = crate::generate::v2_path_def_pass1_pub(&func);
    let full = super::branch_merge_definitions(&func, BlockId(2), &base);
    assert!(implies(&full, &skip(), "t", Some("a")), "with budget, `!c => t == a`: {full:#?}");
    assert!(implies(&full, &arm(), "a", None), "with budget, `!!c => a == 0`: {full:#?}");
    let spent = {
        let _budget = trust_types::verify_budget::VerifyBudgetGuard::install(None, 0);
        super::branch_merge_definitions(&func, BlockId(2), &base)
    };
    assert!(spent.iter().all(|f| full.contains(f)), "only fewer facts: {spent:#?}");
    assert!(!implies(&spent, &skip(), "t", Some("a")), "no skip-edge fact: {spent:#?}");
    assert!(!implies(&spent, &arm(), "a", None), "no arm fact: {spent:#?}");
}
