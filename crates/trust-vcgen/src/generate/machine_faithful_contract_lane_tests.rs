//! Machine{w} declared-width lane (ratified L1 rule 4): an
//! arithmetic-bearing `ensures` over one shared machine domain enters the
//! refutable body-aware lane, and the EMITTED VC is pure declared-width
//! QF_BV — the mathematical-`Int` spelling of machine arithmetic (the
//! confirmed `result + 1 > result` false-proof vector: an `Int` tautology,
//! false at `u64::MAX` under the wrap) must never survive into a solvable
//! row. Structural pins only; the solver-level pass/refute pins live in
//! `tests/ui/trust/` (s1c_arith_ensures_no_false_pass and the positive
//! s1c_arith_true_ensures_proves) where the full pipeline runs.

use trust_types::{
    BasicBlock, BinOp, BlockId, ConstValue, Contract, ContractKind, Formula, LocalDecl,
    Operand, Place, Rvalue, SourceSpan, Statement, Terminator, Ty, VcKind, VerifiableBody,
    VerifiableFunction,
};

use super::{contracts, generate_v2_contract_vcs_impl};

fn machine_fn(
    int_ty: Ty,
    ensures: &str,
    body_stmts: Vec<Statement>,
    extra_locals: Vec<LocalDecl>,
    preconditions: Vec<Formula>,
) -> VerifiableFunction {
    let mut locals = vec![
        LocalDecl { index: 0, ty: int_ty.clone(), name: None },
        LocalDecl { index: 1, ty: int_ty.clone(), name: Some("x".to_string()) },
    ];
    locals.extend(extra_locals);
    VerifiableFunction {
        name: "machine_fixture".to_string(),
        def_path: "test::machine_fixture".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: body_stmts,
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: int_ty,
        },
        contracts: vec![Contract {
            kind: ContractKind::Ensures,
            span: SourceSpan::default(),
            body: ensures.to_string(),
        }],
        preconditions,
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn u64_ty() -> Ty {
    Ty::Int { width: 64, signed: false }
}

fn i32_ty() -> Ty {
    Ty::Int { width: 32, signed: true }
}

fn assign_ret_from_x() -> Statement {
    Statement::Assign {
        place: Place::local(0),
        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
        span: SourceSpan::default(),
    }
}

fn count_nodes(formula: &Formula, pred: &dyn Fn(&Formula) -> bool) -> usize {
    let mut n = 0;
    formula.visit(&mut |f| {
        if pred(f) {
            n += 1;
        }
    });
    n
}

fn int_arith_nodes(formula: &Formula) -> usize {
    count_nodes(formula, &|f| {
        matches!(
            f,
            Formula::Add(..)
                | Formula::Sub(..)
                | Formula::Mul(..)
                | Formula::Div(..)
                | Formula::Rem(..)
                | Formula::Neg(..)
        )
    })
}

fn int_comparison_nodes(formula: &Formula) -> usize {
    count_nodes(formula, &|f| {
        matches!(f, Formula::Lt(..) | Formula::Le(..) | Formula::Gt(..) | Formula::Ge(..))
    })
}

fn postcondition_rows(func: &VerifiableFunction) -> Vec<trust_types::VerificationCondition> {
    generate_v2_contract_vcs_impl(func, None)
        .into_iter()
        .filter(|vc| matches!(vc.kind, VcKind::Postcondition))
        .collect()
}

fn unsupported_rows(func: &VerifiableFunction) -> Vec<trust_types::VerificationCondition> {
    generate_v2_contract_vcs_impl(func, None)
        .into_iter()
        .filter(|vc| matches!(vc.kind, VcKind::UnsupportedMir { .. }))
        .collect()
}

/// The headline containment pin at the vcgen seam: `result + 1 > result`
/// (an `Int` tautology, FALSE at `u64::MAX` under the machine wrap) is
/// admitted as a REFUTABLE row whose formula wraps at the declared width —
/// `bvadd`/`bvult` at 64, zero mathematical-integer arithmetic anywhere.
#[test]
fn arith_tautology_emits_declared_width_bv_row() {
    let func = machine_fn(
        u64_ty(),
        "result + 1 > result",
        vec![assign_ret_from_x()],
        vec![],
        vec![],
    );
    let rows = postcondition_rows(&func);
    assert_eq!(rows.len(), 1, "one body-aware row per Return block: {rows:#?}");
    let formula = &rows[0].formula;
    assert_eq!(int_arith_nodes(formula), 0, "Int arithmetic must not survive: {formula:?}");
    assert_eq!(int_comparison_nodes(formula), 0, "Int comparisons must not survive: {formula:?}");
    assert!(
        count_nodes(formula, &|f| matches!(f, Formula::BvAdd(_, _, 64))) >= 1,
        "the clause `+` must wrap at the DECLARED width 64: {formula:?}"
    );
    assert!(
        count_nodes(formula, &|f| matches!(f, Formula::BvULt(_, _, 64))) >= 1,
        "the unsigned clause `>` must be an unsigned 64-bit BV comparison: {formula:?}"
    );
    assert!(
        unsupported_rows(&func).is_empty(),
        "an admitted clause does not also keep a fail-closed row"
    );
}

/// The mission's positive pin at the vcgen seam: a TRUE arithmetic
/// contract (`ensures result == x + 1` with the wrap excluded by a
/// declared precondition) produces a pure-BV row whose body def (`_0 = x
/// + 1`) and hypothesis translate alongside the clause.
#[test]
fn true_arith_ensures_emits_pure_bv_row() {
    let func = machine_fn(
        u64_ty(),
        "result == x + 1",
        vec![Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::BinaryOp(
                BinOp::Add,
                Operand::Copy(Place::local(1)),
                Operand::Constant(ConstValue::Uint(1, 64)),
            ),
            span: SourceSpan::default(),
        }],
        vec![],
        vec![Formula::Lt(
            Box::new(Formula::Var("x".to_string(), trust_types::Sort::Int)),
            Box::new(Formula::Int(i128::from(u64::MAX))),
        )],
    );
    let rows = postcondition_rows(&func);
    assert_eq!(rows.len(), 1, "one body-aware row per Return block: {rows:#?}");
    let formula = &rows[0].formula;
    assert_eq!(int_arith_nodes(formula), 0, "Int arithmetic must not survive: {formula:?}");
    assert_eq!(int_comparison_nodes(formula), 0, "Int comparisons must not survive: {formula:?}");
    assert!(
        count_nodes(formula, &|f| matches!(f, Formula::BvAdd(_, _, 64))) >= 1,
        "clause and body-def `+` both wrap at width 64: {formula:?}"
    );
    assert!(unsupported_rows(&func).is_empty(), "nothing falls closed: {func:#?}");
}

/// Signed domains pick the SIGNED BV comparators — `bvult` over an `i32`
/// would misread every negative value.
#[test]
fn signed_domain_uses_signed_bv_comparisons() {
    let func = machine_fn(
        i32_ty(),
        "result + 0 >= x",
        vec![assign_ret_from_x()],
        vec![],
        vec![],
    );
    let rows = postcondition_rows(&func);
    assert_eq!(rows.len(), 1, "one body-aware row: {rows:#?}");
    let formula = &rows[0].formula;
    assert!(
        count_nodes(formula, &|f| matches!(f, Formula::BvSLe(_, _, 32))) >= 1,
        "signed `>=` must lower to a signed 32-bit comparison: {formula:?}"
    );
    assert_eq!(
        count_nodes(formula, &|f| matches!(f, Formula::BvULe(..) | Formula::BvULt(..))),
        0,
        "no unsigned comparator may appear in a signed domain: {formula:?}"
    );
}

/// A body fact over a DIFFERENT machine width poisons the whole-VC
/// translation: the row falls closed to the visible unsupported shape —
/// never emitted in the mathematical-`Int` spelling.
#[test]
fn mixed_width_body_falls_closed_visibly() {
    let func = machine_fn(
        u64_ty(),
        "result + 1 > result",
        vec![Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
            span: SourceSpan::default(),
        }],
        vec![LocalDecl {
            index: 2,
            ty: Ty::Int { width: 32, signed: false },
            name: Some("narrow".to_string()),
        }],
        vec![],
    );
    let rows = generate_v2_contract_vcs_impl(&func, None);
    assert!(
        !rows.iter().any(|vc| matches!(vc.kind, VcKind::Postcondition)),
        "a VC that cannot translate must not be emitted at all: {rows:#?}"
    );
    assert!(
        rows.iter().any(|vc| matches!(
            &vc.kind,
            VcKind::UnsupportedMir { kind, .. } if kind == contracts::SPEC_UNVERIFIABLE_KIND
        )),
        "the gap stays a visible fail-closed row: {rows:#?}"
    );
}

/// A literal outside the declared width (`256` over `u8`) refuses
/// ADMISSION: the clause keeps the pre-existing fail-closed lane.
#[test]
fn out_of_width_literal_is_not_admitted() {
    let func = machine_fn(
        Ty::Int { width: 8, signed: false },
        "result + 256 > result",
        vec![assign_ret_from_x()],
        vec![],
        vec![],
    );
    assert!(
        !contracts::machine_faithful_clause_admissible(
            &func,
            &trust_types::parse_spec_expr("result + 256 > result").expect("clause parses"),
        ),
        "256 has no u8 pattern"
    );
    let rows = generate_v2_contract_vcs_impl(&func, None);
    assert!(
        !rows.iter().any(|vc| matches!(vc.kind, VcKind::Postcondition)),
        "no refutable row for an inadmissible clause: {rows:#?}"
    );
}

/// Spec-level `/` keeps its visible `unsupported_machine_arithmetic` row:
/// SMT's total bvudiv assigns a zero divisor a value where the authored
/// Rust expression traps.
#[test]
fn spec_division_is_not_admitted() {
    let func =
        machine_fn(u64_ty(), "result / 2 == x", vec![assign_ret_from_x()], vec![], vec![]);
    assert!(
        !contracts::machine_faithful_clause_admissible(
            &func,
            &trust_types::parse_spec_expr("result / 2 == x").expect("clause parses"),
        ),
        "spec division needs a definedness premise lane"
    );
    let rows = generate_v2_contract_vcs_impl(&func, None);
    assert!(
        !rows.iter().any(|vc| matches!(vc.kind, VcKind::Postcondition)),
        "no refutable row for spec division: {rows:#?}"
    );
}

/// The mutated-param shortcut emits `Not(post)` with FREE parameters. For
/// a machine-admitted clause that spelling must ALSO be the declared-width
/// one: the `Int` spelling of `result + 1 > result` is an `Int` TAUTOLOGY
/// whose bare negation is UNSAT — a false proof minted by the shortcut
/// itself.
#[test]
fn machine_tautology_negation_translates_to_refutable_bv() {
    let func =
        machine_fn(u64_ty(), "result + 1 > result", vec![assign_ret_from_x()], vec![], vec![]);
    let post = trust_types::parse_spec_expr("result + 1 > result").expect("clause parses");
    let translated = contracts::machine_faithful_vc_formula(
        &func,
        &Formula::Not(Box::new(post)),
    )
    .expect("the tautology clause is inside the declared-width fragment");
    assert_eq!(int_arith_nodes(&translated), 0, "no Int arithmetic: {translated:?}");
    assert!(
        count_nodes(&translated, &|f| matches!(f, Formula::BvAdd(_, _, 64))) >= 1,
        "the negated clause still wraps at 64: {translated:?}"
    );
}
