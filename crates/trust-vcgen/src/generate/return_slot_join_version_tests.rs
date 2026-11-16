//! The RETURN-SLOT twin of `early_return_postcondition_tests`: an `ensures`
//! whose clause is an EQUALITY on `result` (`result == <expr>`), over a body
//! whose `&&`-lowering diamond writes `_0` in TWO predecessor blocks.
//!
//! THE DEFECT (probe f53, measured 2026-08-25). `pub fn in_range(x: i64) ->
//! bool ensures result == (x >= -128 && x <= 127) { x >= -128 && x <= 127 }`
//! was FALSELY REFUTED by the native trust-mc lane: `0 proved, 3 failed,
//! counterexample: verified_counterexample = true` against a tautologically
//! TRUE postcondition. The emitted per-predecessor VC negated the clause at the
//! Return block's MERGED reaching-def token (`_0#s1_0_s2_0`) while the
//! return-value pin carried THIS predecessor's single establish token
//! (`_0#s1_0` / `_0#s2_0`). Nothing equated the two names, so the negated
//! clause was a refutable query over a FREE return value, and the
//! "counterexample" was a model of that formula about nothing.
//!
//! The result read is now stamped at the exact per-predecessor return point
//! before body facts are combined. Pin shape no longer decides which value the
//! clause reads, and historical return-slot reads keep their own identities.
//!
//! Every case runs in BOTH directions: the TRUE clause must CONNECT to the
//! genuine return value, and its FALSE twin must stay refutable.

use trust_types::{
    BasicBlock, BinOp, BlockId, ConstValue, Formula, LocalDecl, Operand, Place, Rvalue, Sort,
    SourceSpan, Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
};

use super::generate_v2_contract_vcs_impl;

fn span() -> SourceSpan {
    SourceSpan::default()
}

fn assign(place: Place, rvalue: Rvalue) -> Statement {
    Statement::Assign { place, rvalue, span: span() }
}

fn block(id: usize, stmts: Vec<Statement>, terminator: Terminator) -> BasicBlock {
    BasicBlock { id: BlockId(id), stmts, terminator }
}

fn bool_const(value: bool) -> Rvalue {
    Rvalue::Use(Operand::Constant(ConstValue::Bool(value)))
}

/// `<cmp>(x, <k>)` as the body spells it: a `BinaryOp` over the parameter local.
fn cmp_x(op: BinOp, k: i128) -> Rvalue {
    Rvalue::BinaryOp(op, Operand::Copy(Place::local(1)), Operand::Constant(ConstValue::Int(k)))
}

fn x_var() -> Formula {
    Formula::Var("x".into(), Sort::Int)
}

/// `result == <rhs>` — the Eq-shaped clause, spelled on the parser's `_0`.
fn ensures_result_eq(rhs: Formula) -> Formula {
    Formula::Eq(Box::new(Formula::Var("_0".into(), Sort::Bool)), Box::new(rhs))
}

/// `x >= -128 && x <= 127` — the clause RHS of probe f53.
fn range_conj() -> Formula {
    Formula::And(vec![
        Formula::Ge(Box::new(x_var()), Box::new(Formula::Int(-128))),
        Formula::Le(Box::new(x_var()), Box::new(Formula::Int(127))),
    ])
}

/// The f53 body at `-O`: the `&&` short-circuit diamond.
///
/// ```text
/// bb0: _2 = Ge(x, -128); switchInt(_2) [0 -> bb2, otherwise -> bb1]
/// bb1: _0 = Le(x, 127);  goto bb3          // token s1_0
/// bb2: _0 = false;       goto bb3          // token s2_0
/// bb3: return                              // _0's merged token: s1_0_s2_0
/// ```
fn bool_conj_diamond(clause: Formula) -> VerifiableFunction {
    VerifiableFunction {
        name: "in_range".into(),
        def_path: "in_range".into(),
        span: span(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Bool, name: None },
                LocalDecl { index: 1, ty: Ty::i64(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::Bool, name: None },
            ],
            blocks: vec![
                block(
                    0,
                    vec![assign(Place::local(2), cmp_x(BinOp::Ge, -128))],
                    Terminator::SwitchInt {
                        discr: Operand::Move(Place::local(2)),
                        targets: vec![(0, BlockId(2))],
                        otherwise: BlockId(1),
                        exhaustive_enum_unreachable: false,
                        span: span(),
                    },
                ),
                block(
                    1,
                    vec![assign(Place::local(0), cmp_x(BinOp::Le, 127))],
                    Terminator::Goto(BlockId(3)),
                ),
                block(
                    2,
                    vec![assign(Place::local(0), bool_const(false))],
                    Terminator::Goto(BlockId(3)),
                ),
                block(3, vec![], Terminator::Return),
            ],
            arg_count: 1,
            return_ty: Ty::Bool,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![clause],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// All Postcondition VC formulas (one per return predecessor).
fn postcondition_formulas(f: &VerifiableFunction) -> Vec<Formula> {
    let found: Vec<Formula> = generate_v2_contract_vcs_impl(f, None)
        .into_iter()
        .filter(|vc| matches!(vc.kind, trust_types::VcKind::Postcondition))
        .map(|vc| vc.formula)
        .collect();
    assert_eq!(found.len(), 2, "expected one Postcondition VC per return predecessor");
    found
}

/// Every distinct return-slot spelling (`_0` / `_0#tok`) free in `formula`.
fn return_slot_names(formula: &Formula) -> Vec<String> {
    let mut names: Vec<String> = formula
        .free_variables()
        .into_iter()
        .filter(|name| name == "_0" || name.starts_with("_0#"))
        .collect();
    names.sort();
    names.dedup();
    names
}

/// THE CONNECTION INVARIANT. On each per-predecessor VC, the negated clause's
/// return-slot read and the return-value pin must share ONE name; a second
/// surviving spelling is exactly the free-join-name defect (the extra name has
/// no defining conjunct, so `Not(post)` is satisfiable by havoc and the row
/// "refutes" a tautology).
#[test]
fn bool_conj_true_clause_connects_clause_to_pin() {
    for formula in postcondition_formulas(&bool_conj_diamond(ensures_result_eq(range_conj()))) {
        let names = return_slot_names(&formula);
        assert_eq!(
            names.len(),
            1,
            "the clause's `_0` read must unify with the pin's version; \
             two spellings leave the clause free and false-refute a tautology: \
             {names:?}\nformula: {formula:?}"
        );
    }
}

/// The FALSE twin (`result == (x >= 0)` over the same body) must connect the
/// SAME way — to the genuine pinned value, from which the solver refutes it.
/// Unification must never work by disconnecting or crediting the clause.
#[test]
fn bool_conj_false_twin_connects_to_the_genuine_value() {
    let false_clause = ensures_result_eq(Formula::Ge(Box::new(x_var()), Box::new(Formula::Int(0))));
    for formula in postcondition_formulas(&bool_conj_diamond(false_clause)) {
        let names = return_slot_names(&formula);
        assert_eq!(
            names.len(),
            1,
            "the false twin must also unify onto the pin (and then refute from \
             the genuine value): {names:?}\nformula: {formula:?}"
        );
        // The negated clause must still be present — connection, not credit.
        let mut has_negated_clause = false;
        formula.visit(&mut |node| {
            if let Formula::Not(inner) = node
                && matches!(&**inner, Formula::Eq(lhs, _)
                    if matches!(&**lhs, Formula::Var(name, _) if name == "_0" || name.starts_with("_0#")))
            {
                has_negated_clause = true;
            }
        });
        assert!(
            has_negated_clause,
            "the negated postcondition must survive unification: {formula:?}"
        );
    }
}

/// Straightline single-write control: one block, one `_0` write, clause
/// `result == (x >= 0)`. Already-working shape (probe note: "a
/// single-comparison clause proves fine") — must keep exactly one spelling.
#[test]
fn straightline_eq_clause_stays_connected() {
    let f = VerifiableFunction {
        name: "nonneg".into(),
        def_path: "nonneg".into(),
        span: span(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Bool, name: None },
                LocalDecl { index: 1, ty: Ty::i64(), name: Some("x".into()) },
            ],
            blocks: vec![block(
                0,
                vec![assign(Place::local(0), cmp_x(BinOp::Ge, 0))],
                Terminator::Return,
            )],
            arg_count: 1,
            return_ty: Ty::Bool,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![ensures_result_eq(Formula::Ge(
            Box::new(x_var()),
            Box::new(Formula::Int(0)),
        ))],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    };
    let found: Vec<Formula> = generate_v2_contract_vcs_impl(&f, None)
        .into_iter()
        .filter(|vc| matches!(vc.kind, trust_types::VcKind::Postcondition))
        .map(|vc| vc.formula)
        .collect();
    assert_eq!(found.len(), 1, "straightline body has a single Postcondition VC");
    let names = return_slot_names(&found[0]);
    assert_eq!(names.len(), 1, "single-write body must stay connected: {names:?}");
}

// ───────────────── bounded semantic check (the verdicts themselves) ─────────────────
//
// The connection assertions above pin the STRUCTURAL fix; these pin what the
// solver will now answer. A tiny ground evaluator over exactly the node kinds
// these fixtures produce (And/Not/Eq/Ge/Le/Var/Int/Bool — anything else
// evaluates to `None` and fails the test loudly), exhaustively enumerated over
// every Bool free variable and an integer grid covering both branch boundaries.

#[derive(Clone, Copy, PartialEq)]
enum GroundValue {
    Int(i128),
    Bool(bool),
}

fn ground_eval(
    formula: &Formula,
    env: &std::collections::BTreeMap<String, GroundValue>,
) -> Option<GroundValue> {
    let as_int = |f: &Formula| match ground_eval(f, env)? {
        GroundValue::Int(v) => Some(v),
        GroundValue::Bool(_) => None,
    };
    let as_bool = |f: &Formula| match ground_eval(f, env)? {
        GroundValue::Bool(v) => Some(v),
        GroundValue::Int(_) => None,
    };
    match formula {
        Formula::Bool(v) => Some(GroundValue::Bool(*v)),
        Formula::Int(v) => Some(GroundValue::Int(*v)),
        Formula::Var(name, _) => env.get(name).copied(),
        Formula::Not(inner) => Some(GroundValue::Bool(!as_bool(inner)?)),
        Formula::And(conjuncts) => {
            let mut acc = true;
            for conjunct in conjuncts {
                acc &= as_bool(conjunct)?;
            }
            Some(GroundValue::Bool(acc))
        }
        Formula::Eq(l, r) => match (ground_eval(l, env)?, ground_eval(r, env)?) {
            (GroundValue::Int(a), GroundValue::Int(b)) => Some(GroundValue::Bool(a == b)),
            (GroundValue::Bool(a), GroundValue::Bool(b)) => Some(GroundValue::Bool(a == b)),
            _ => None,
        },
        Formula::Ge(l, r) => Some(GroundValue::Bool(as_int(l)? >= as_int(r)?)),
        Formula::Le(l, r) => Some(GroundValue::Bool(as_int(l)? <= as_int(r)?)),
        _ => None,
    }
}

/// Every satisfying assignment of `formula` over: all Bool free vars ×
/// `int_grid` for every Int free var. Panics if any node is outside the
/// evaluator's fragment (that means the fixture changed shape — extend it).
fn bounded_sat(formula: &Formula, int_grid: &[i128]) -> bool {
    let mut int_vars: Vec<String> = Vec::new();
    let mut bool_vars: Vec<String> = Vec::new();
    formula.visit(&mut |node| {
        if let Formula::Var(name, sort) = node {
            let bucket = match sort {
                Sort::Bool => &mut bool_vars,
                _ => &mut int_vars,
            };
            if !bucket.contains(name) {
                bucket.push(name.clone());
            }
        }
    });
    let bool_count = bool_vars.len();
    assert!(bool_count <= 8, "fixture grew too many bools: {bool_vars:?}");
    let mut int_indices = vec![0usize; int_vars.len()];
    loop {
        for mask in 0u32..(1u32 << bool_count) {
            let mut env = std::collections::BTreeMap::new();
            for (i, name) in int_vars.iter().enumerate() {
                env.insert(name.clone(), GroundValue::Int(int_grid[int_indices[i]]));
            }
            for (i, name) in bool_vars.iter().enumerate() {
                env.insert(name.clone(), GroundValue::Bool(mask & (1 << i) != 0));
            }
            match ground_eval(formula, &env) {
                Some(GroundValue::Bool(true)) => return true,
                Some(GroundValue::Bool(false)) => {}
                _ => panic!("fixture node outside the test evaluator's fragment: {formula:?}"),
            }
        }
        // advance the mixed-radix integer counter
        let mut k = 0;
        loop {
            if k == int_indices.len() {
                return false;
            }
            int_indices[k] += 1;
            if int_indices[k] < int_grid.len() {
                break;
            }
            int_indices[k] = 0;
            k += 1;
        }
    }
}

/// Both branch boundaries, their neighbours, zero, and far-out points — the
/// grid on which f53's false counterexample (`x = 0`, free `_0#s1_0_s2_0`)
/// lived pre-fix.
const X_GRID: &[i128] = &[-1000, -129, -128, -127, -1, 0, 1, 126, 127, 128, 1000];

/// THE VERDICT FLIP. Pre-fix, `x = 0` with the free join name set `false`
/// satisfied the per-path VC — the measured `verified_counterexample = true`.
/// Post-fix the TRUE clause's every per-path VC must be bounded-UNSAT (the
/// native lane proves it), and the FALSE twin must stay satisfiable (a genuine
/// refutation, from the genuinely pinned value).
#[test]
fn bool_conj_true_clause_is_unsat_and_false_twin_stays_sat() {
    for formula in postcondition_formulas(&bool_conj_diamond(ensures_result_eq(range_conj()))) {
        assert!(
            !bounded_sat(&formula, X_GRID),
            "a tautologically true postcondition's VC must admit NO counterexample: {formula:?}"
        );
    }
    let false_clause = ensures_result_eq(Formula::Ge(Box::new(x_var()), Box::new(Formula::Int(0))));
    let sat_rows = postcondition_formulas(&bool_conj_diamond(false_clause))
        .iter()
        .filter(|formula| bounded_sat(formula, X_GRID))
        .count();
    assert!(
        sat_rows > 0,
        "the false twin must remain refutable — unification must never credit a clause"
    );
}
