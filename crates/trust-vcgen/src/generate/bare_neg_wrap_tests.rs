// Trust (2026-10-05, NEG-WRAP-OFF-1): the wrap-exact value model for a BARE
// integer `Rvalue::UnaryOp(Neg)` — the sibling of `wrapping_binop_defs_tests`
// (plain `Add`/`Sub`/`Mul`) and of SHIFT-1 (plain `Shl`/`Shr`).
//
// MIR reality: rustc defines the integer `Neg` as WRAPPING (`-MIN == MIN`). The
// overflow check is not part of the operation; it is a separate
// `Assert(OverflowNeg)` terminator (`cond = Eq(x, MIN)`, `expected: false`) that
// dominates the `Neg`. With `-Coverflow-checks=on` no `MIN` reaches the `Neg`;
// with checks off (honored by memory-safe and advisory) it does, and the machine
// result is `MIN`.
//
// THE BUG THESE TESTS PIN CLOSED (a false PROVE):
// `guards::extract_block_definitions` modelled the bare `Neg` as the mathematical
// `dest == -x`. The postcondition lane also pins the return slot through
// `chc::rvalue_to_formula_with_dest`, whose machine `Neg` arm is wrap-exact
// (`BvToInt(0 -w x)`). At `x == MIN` the two contradict each other, so the
// postcondition query was UNSAT exactly where the clause is false, and
//
//     fn abs_like(x: i32) -> i32 ensures result >= 0 { if x < 0 { -x } else { x } }
//
// PROVED under `-Ztrust-policy=memory-safe -Coverflow-checks=off` (and advisory),
// while the binary returns `-2147483648`. The interval lane
// (`abstract_interp::transfer`) and the value-set lane (`value_analysis`) had the
// same mathematical negation: `x ∈ [i32::MIN, -1] ⇒ -x ∈ [1, 2^31]`, excluding the
// machine's `i32::MIN`.
//
// `abs_like_checks_off_postcondition_is_refuted_by_ay` is the fails-before control
// (measured with the guards.rs hunk reverted: no row admits the real execution).
use trust_types::{
    AssertMessage, BasicBlock, BinOp, BlockId, ConstValue, Formula, LocalDecl, Operand, Place,
    Rvalue, Sort, SourceSpan, Statement, Terminator, Ty, UnOp, UnwindEdge, VcKind, VerifiableBody,
    VerifiableFunction, VerificationCondition, VerificationResult,
};

use super::ite::eliminate_term_ites;
use super::{
    ITE_ELIM_CASE_CAP, generate_v2_contract_vcs_impl, guards, wrapping_neg_call_dest_value,
};

// ---------------------------------------------------------------------------
// A tiny total evaluator for the Int fragment the defs use (the
// `wrapping_binop_defs_tests` one, which this module does not share: it is
// private there). `None` on anything it does not model.
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq)]
enum Val {
    I(i128),
    B(bool),
}

fn eval(f: &Formula, env: &dyn Fn(&str) -> Option<Val>) -> Option<Val> {
    let int = |f: &Formula| match eval(f, env)? {
        Val::I(v) => Some(v),
        Val::B(_) => None,
    };
    let boolean = |f: &Formula| match eval(f, env)? {
        Val::B(v) => Some(v),
        Val::I(_) => None,
    };
    Some(match f {
        Formula::Bool(b) => Val::B(*b),
        Formula::Int(v) => Val::I(*v),
        Formula::Var(name, _) => env(name.split('#').next().unwrap_or(name))?,
        Formula::Add(a, b) => Val::I(int(a)?.checked_add(int(b)?)?),
        Formula::Sub(a, b) => Val::I(int(a)?.checked_sub(int(b)?)?),
        Formula::Neg(a) => Val::I(int(a)?.checked_neg()?),
        Formula::Eq(a, b) => match (eval(a, env)?, eval(b, env)?) {
            (Val::I(x), Val::I(y)) => Val::B(x == y),
            (Val::B(x), Val::B(y)) => Val::B(x == y),
            _ => return None,
        },
        Formula::Lt(a, b) => Val::B(int(a)? < int(b)?),
        Formula::Le(a, b) => Val::B(int(a)? <= int(b)?),
        Formula::Gt(a, b) => Val::B(int(a)? > int(b)?),
        Formula::Ge(a, b) => Val::B(int(a)? >= int(b)?),
        Formula::Not(a) => Val::B(!boolean(a)?),
        Formula::Implies(a, b) => Val::B(!boolean(a)? || boolean(b)?),
        Formula::And(cs) => {
            let mut acc = true;
            for c in cs {
                acc &= boolean(c)?;
            }
            Val::B(acc)
        }
        Formula::Or(cs) => {
            let mut acc = false;
            for c in cs {
                acc |= boolean(c)?;
            }
            Val::B(acc)
        }
        Formula::Ite(c, t, e) => {
            if boolean(c)? {
                eval(t, env)?
            } else {
                eval(e, env)?
            }
        }
        // The chc return pin's bridge (`BvToInt(0 -w IntToBv(x))`): a bit-vector is
        // its unsigned pattern in `[0, 2^w)`; widths up to 64 only.
        Formula::BitVec { value, width } if *width <= 64 => {
            Val::I(value.rem_euclid(1i128 << *width))
        }
        Formula::IntToBv(a, w) if *w <= 64 => Val::I(int(a)?.rem_euclid(1i128 << *w)),
        Formula::BvSub(a, b, w) if *w <= 64 => {
            Val::I(int(a)?.checked_sub(int(b)?)?.rem_euclid(1i128 << *w))
        }
        Formula::BvToInt(a, w, signed) if *w <= 64 => {
            let pattern = int(a)?;
            if *signed && pattern >= 1i128 << (*w - 1) {
                Val::I(pattern - (1i128 << *w))
            } else {
                Val::I(pattern)
            }
        }
        _ => return None,
    })
}

// ---------------------------------------------------------------------------
// MIR builders
// ---------------------------------------------------------------------------

fn assign(local: usize, rvalue: Rvalue) -> Statement {
    Statement::Assign { place: Place::local(local), rvalue, span: SourceSpan::default() }
}

fn neg_of(local: usize) -> Rvalue {
    Rvalue::UnaryOp(UnOp::Neg, Operand::Copy(Place::local(local)))
}

fn local(index: usize, ty: Ty, name: &str) -> LocalDecl {
    LocalDecl { index, ty, name: Some(name.into()) }
}

fn func(
    locals: Vec<LocalDecl>,
    blocks: Vec<BasicBlock>,
    return_ty: Ty,
    postconditions: Vec<Formula>,
) -> VerifiableFunction {
    VerifiableFunction {
        name: "neg_fixture".into(),
        def_path: "test::neg_fixture".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks,
            arg_count: 1,
            return_ty,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions,
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// `fn f(x: T) { let d: T = -x; }` — one block, the bare `d = Neg(x)`.
fn single_neg(ty: Ty) -> VerifiableFunction {
    func(
        vec![local(0, Ty::Unit, "ret"), local(1, ty.clone(), "x"), local(2, ty, "d")],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![assign(2, neg_of(1))],
            terminator: Terminator::Return,
        }],
        Ty::Unit,
        vec![],
    )
}

fn def_of<'a>(defs: &'a [Formula], name: &str) -> Option<&'a Formula> {
    defs.iter().find_map(|d| match d {
        Formula::Eq(l, r) if l.var_name() == Some(name) => Some(r.as_ref()),
        _ => None,
    })
}

fn int(name: &str) -> Formula {
    Formula::Var(name.into(), Sort::Int)
}

// ---------------------------------------------------------------------------
// The block def
// ---------------------------------------------------------------------------

/// The exact wrap `ite(x == MIN, MIN, -x)` at `x`'s real width, with the operand's
/// type range beside it — at every signed width, pointer-width included. Off `MIN`
/// the value term is the old `Formula::Neg` node; at `MIN` it is the machine's `MIN`.
/// The mathematical `d == -x` is gone.
fn expected_wrap(width: u32) -> Formula {
    let min = crate::range::type_min_formula(width, true);
    Formula::Ite(
        Box::new(Formula::Eq(Box::new(int("x")), Box::new(min.clone()))),
        Box::new(min),
        Box::new(Formula::Neg(Box::new(int("x")))),
    )
}

#[test]
fn bare_neg_def_is_the_exact_wrap() {
    for (ty, width) in [
        (Ty::i8(), 8u32),
        (Ty::i32(), 32),
        (Ty::i64(), 64),
        (Ty::i128(), 128),
        (Ty::PtrSizedInt { signed: true }, 64),
    ] {
        let f = single_neg(ty.clone());
        let defs = guards::extract_block_definitions(&f, &f.body.blocks[0]);
        let def = def_of(&defs, "d").unwrap_or_else(|| panic!("{ty:?}: no def for d: {defs:?}"));
        assert_eq!(def, &expected_wrap(width), "{ty:?}: the bare Neg def must be the exact wrap");
        assert!(
            defs.contains(&crate::range::input_range_constraint(&int("x"), width, true)),
            "{ty:?}: the operand's type range must ride along: {defs:?}"
        );
        assert!(
            !defs.contains(&Formula::Eq(
                Box::new(int("d")),
                Box::new(Formula::Neg(Box::new(int("x"))))
            )),
            "{ty:?}: the mathematical `d == -x` def must be gone: {defs:?}"
        );
        let min = crate::range::signed_min(width);
        let at = |x: i128| move |name: &str| (name == "x").then_some(Val::I(x));
        assert_eq!(eval(def, &at(min)), Some(Val::I(min)), "{ty:?}: -MIN wraps to MIN");
        assert_eq!(eval(def, &at(-5)), Some(Val::I(5)), "{ty:?}: -(-5) == 5");
        assert_eq!(eval(def, &at(min + 1)), Some(Val::I(-(min + 1))), "{ty:?}: -(MIN+1) == MAX");
    }
}

/// AGREEMENT with the authenticated std `wrapping_neg` CALL model at every edge
/// point of the domain: the bare `Neg` and `x.wrapping_neg()` are the same machine
/// function, so their value terms must evaluate identically.
#[test]
fn bare_neg_def_agrees_with_the_wrapping_neg_call_model() {
    let call_func =
        func(vec![local(0, Ty::i32(), "d"), local(1, Ty::i32(), "x")], vec![], Ty::i32(), vec![]);
    let call = Terminator::Call {
        func: "core::num::<impl i32>::wrapping_neg".into(),
        args: vec![Operand::Copy(Place::local(1))],
        dest: Place::local(0),
        target: Some(BlockId(1)),
        span: SourceSpan::default(),
        atomic: None,
        is_unsafe_sig: false,
        is_foreign: false,
        callee_identity: None,
        callee_key: crate::sep_engine::tests::fixture_key("core::num::<impl i32>::wrapping_neg"),
        unwind: UnwindEdge::Terminate,
    };
    let (_, call_value) =
        wrapping_neg_call_dest_value(&call_func, &call).expect("the std call form must model");
    let f = single_neg(Ty::i32());
    let defs = guards::extract_block_definitions(&f, &f.body.blocks[0]);
    let def = def_of(&defs, "d").unwrap_or_else(|| panic!("no def for d: {defs:?}"));
    let min = i128::from(i32::MIN);
    let max = i128::from(i32::MAX);
    for x in [min, min + 1, -1, 0, 1, max - 1, max] {
        let env = move |name: &str| (name == "x").then_some(Val::I(x));
        let bare = eval(def, &env);
        assert!(bare.is_some(), "the bare def must evaluate at x = {x}: {def:?}");
        assert_eq!(bare, eval(&call_value, &env), "bare Neg vs wrapping_neg at x = {x}");
    }
}

/// The width comes from the DESTINATION. A width-less `ConstValue::Int(i32::MIN)`
/// operand reports `i64` from its VALUE (`operand_ty`'s convention); the constant
/// resolver declines `-(i32::MIN)` at `i32` (it leaves the type), so the def falls
/// to the bare-`Neg` arm, where a width-64 model would say `0 - i32::MIN == 2^31`.
/// The machine's `i32` result is `i32::MIN`.
#[test]
fn bare_neg_of_a_widthless_constant_uses_the_destination_width() {
    let operand = Operand::Constant(ConstValue::Int(i32::MIN.into()));
    let f = func(
        vec![local(0, Ty::Unit, "ret"), local(1, Ty::i32(), "x"), local(2, Ty::i32(), "d")],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![assign(2, Rvalue::UnaryOp(UnOp::Neg, operand.clone()))],
            terminator: Terminator::Return,
        }],
        Ty::Unit,
        vec![],
    );
    assert_eq!(
        crate::operand_ty(&f, &operand),
        Some(Ty::i64()),
        "the width-less literal reports a value-derived i64; that is what the \
         destination-width rule exists for"
    );
    let defs = guards::extract_block_definitions(&f, &f.body.blocks[0]);
    let def = def_of(&defs, "d").unwrap_or_else(|| panic!("no def for d: {defs:?}"));
    assert_eq!(
        eval(def, &|_: &str| None),
        Some(Val::I(i32::MIN.into())),
        "-(i32::MIN) at i32 wraps to i32::MIN, not the width-64 2^31: {def:?}"
    );
}

/// A place operand whose declared type disagrees with the destination, and a
/// destination that is not a machine integer, model NOTHING (fail-closed: an
/// exact-value def at a wrong width is wrong in both directions). `u128` has no
/// encoding (its modulus does not fit the `i128` carrier).
#[test]
fn bare_neg_with_a_disagreeing_or_unencodable_type_emits_no_def() {
    let mismatched = func(
        vec![local(0, Ty::Unit, "ret"), local(1, Ty::i32(), "x"), local(2, Ty::i64(), "d")],
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![assign(2, neg_of(1))],
            terminator: Terminator::Return,
        }],
        Ty::Unit,
        vec![],
    );
    let defs = guards::extract_block_definitions(&mismatched, &mismatched.body.blocks[0]);
    assert!(def_of(&defs, "d").is_none(), "i32 operand into i64 dest: no def: {defs:?}");

    let wide = single_neg(Ty::Int { width: 128, signed: false });
    let defs = guards::extract_block_definitions(&wide, &wide.body.blocks[0]);
    assert!(def_of(&defs, "d").is_none(), "u128 negation has no encoding: {defs:?}");
}

// ---------------------------------------------------------------------------
// The measured false proof, solver-backed
// ---------------------------------------------------------------------------

/// `fn abs_like(x: i32) -> i32 ensures result >= 0 { if x < 0 { -x } else { x } }`.
/// `checks_on` inserts rustc's `Assert(OverflowNeg)` (`_3 = Eq(x, i32::MIN);
/// assert(!_3)`) in front of the `Neg`, exactly as `-Coverflow-checks=on` lowers it.
fn abs_like(checks_on: bool, postcondition: Formula) -> VerifiableFunction {
    let neg_block = if checks_on { 4 } else { 1 };
    let mut blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![assign(
                2,
                Rvalue::BinaryOp(
                    BinOp::Lt,
                    Operand::Copy(Place::local(1)),
                    Operand::Constant(ConstValue::Int(0)),
                ),
            )],
            terminator: Terminator::SwitchInt {
                discr: Operand::Copy(Place::local(2)),
                targets: vec![(0, BlockId(2))],
                otherwise: BlockId(1),
                exhaustive_enum_unreachable: false,
                span: SourceSpan::default(),
            },
        },
        BasicBlock {
            id: BlockId(1),
            stmts: if checks_on {
                vec![assign(
                    3,
                    Rvalue::BinaryOp(
                        BinOp::Eq,
                        Operand::Copy(Place::local(1)),
                        Operand::Constant(ConstValue::Int(i32::MIN.into())),
                    ),
                )]
            } else {
                vec![assign(0, neg_of(1))]
            },
            terminator: if checks_on {
                Terminator::Assert {
                    cond: Operand::Copy(Place::local(3)),
                    expected: false,
                    msg: AssertMessage::OverflowNeg,
                    target: BlockId(neg_block),
                    span: SourceSpan::default(),
                    unwind: UnwindEdge::Unreachable,
                }
            } else {
                Terminator::Goto(BlockId(3))
            },
        },
        BasicBlock {
            id: BlockId(2),
            stmts: vec![assign(0, Rvalue::Use(Operand::Copy(Place::local(1))))],
            terminator: Terminator::Goto(BlockId(3)),
        },
        BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
    ];
    if checks_on {
        blocks.push(BasicBlock {
            id: BlockId(4),
            stmts: vec![assign(0, neg_of(1))],
            terminator: Terminator::Goto(BlockId(3)),
        });
    }
    func(
        vec![
            local(0, Ty::i32(), "_0"),
            local(1, Ty::i32(), "x"),
            local(2, Ty::Bool, "neg"),
            local(3, Ty::Bool, "is_min"),
        ],
        blocks,
        Ty::i32(),
        vec![postcondition],
    )
}

/// `fn negate_x(x: i32) -> i32 { -x }`, with rustc's `Assert(OverflowNeg)` in front
/// of the `Neg` when `checks_on`.
fn negate_x(checks_on: bool, postcondition: Formula) -> VerifiableFunction {
    let negate = |id: usize| BasicBlock {
        id: BlockId(id),
        stmts: vec![assign(0, neg_of(1))],
        terminator: Terminator::Return,
    };
    let blocks = if checks_on {
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![assign(
                    3,
                    Rvalue::BinaryOp(
                        BinOp::Eq,
                        Operand::Copy(Place::local(1)),
                        Operand::Constant(ConstValue::Int(i32::MIN.into())),
                    ),
                )],
                terminator: Terminator::Assert {
                    cond: Operand::Copy(Place::local(3)),
                    expected: false,
                    msg: AssertMessage::OverflowNeg,
                    target: BlockId(1),
                    span: SourceSpan::default(),
                    unwind: UnwindEdge::Unreachable,
                },
            },
            negate(1),
        ]
    } else {
        vec![negate(0)]
    };
    func(
        vec![
            local(0, Ty::i32(), "_0"),
            local(1, Ty::i32(), "x"),
            local(2, Ty::Bool, "unused"),
            local(3, Ty::Bool, "is_min"),
        ],
        blocks,
        Ty::i32(),
        vec![postcondition],
    )
}

/// `result >= 0`
fn result_non_negative() -> Formula {
    Formula::Ge(Box::new(int("_0")), Box::new(Formula::Int(0)))
}

/// `x >= 0 || result > 0` — true of the mathematical negation, false at `x == MIN`
/// for the wrapping one.
fn neg_of_negative_is_positive() -> Formula {
    Formula::Or(vec![
        Formula::Ge(Box::new(int("x")), Box::new(Formula::Int(0))),
        Formula::Gt(Box::new(int("_0")), Box::new(Formula::Int(0))),
    ])
}

/// `x >= -2147483647 || result == x` — the wrap itself (`x == MIN ==> result == MIN`),
/// which only the exact model proves (the true twin of the two liars above).
fn neg_of_min_is_min() -> Formula {
    Formula::Or(vec![
        Formula::Ge(Box::new(int("x")), Box::new(Formula::Int(-2_147_483_647))),
        Formula::Eq(Box::new(int("_0")), Box::new(int("x"))),
    ])
}

/// The contract lane's postcondition rows, with the production pipeline's general
/// term-`Ite` elimination applied (`entry.rs` runs it on every aggregated row).
fn postcondition_rows(f: &VerifiableFunction) -> Vec<VerificationCondition> {
    let rows: Vec<_> = generate_v2_contract_vcs_impl(f, None)
        .into_iter()
        .filter(|vc| matches!(vc.kind, VcKind::Postcondition))
        .map(|mut vc| {
            vc.formula = eliminate_term_ites(&vc.formula, ITE_ELIM_CASE_CAP);
            vc
        })
        .collect();
    assert!(!rows.is_empty(), "the clause must raise postcondition rows");
    rows
}

/// The row with every top-level conjunct that mentions the bit-vector bridge
/// (`IntToBv`/`BvToInt` — the chc return pin) replaced by `true`.
///
/// In-process ay answers the MIXED Int+bridge row `unknown` (model validation /
/// self-check), with or without this fix, so the rows are decided here in pure LIA
/// on what the BLOCK DEFINITION says. Dropping a hypothesis only WEAKENS the row:
/// UNSAT of the weakened row is UNSAT of the full row (a proof survives), and SAT
/// of it is checked against the full row separately, with a concrete witness.
fn without_bv_pins(f: &Formula) -> Formula {
    match f {
        Formula::And(conjuncts) => Formula::And(conjuncts.iter().map(without_bv_pins).collect()),
        leaf => {
            let rendered = format!("{leaf:?}");
            if rendered.contains("BvToInt") || rendered.contains("IntToBv") {
                Formula::Bool(true)
            } else {
                leaf.clone()
            }
        }
    }
}

fn lia_verdicts(f: &VerifiableFunction) -> Vec<(VerificationResult, String)> {
    use trust_router::{InProcessAyBackend, VerificationBackend};
    let backend = InProcessAyBackend::new();
    postcondition_rows(f)
        .into_iter()
        .map(|mut vc| {
            vc.formula = without_bv_pins(&vc.formula);
            assert!(backend.can_handle(&vc), "in-process ay must take the row: {:?}", vc.formula);
            (backend.verify(&vc), format!("{:?}", vc.formula))
        })
        .collect()
}

/// THE FALSE-PROVE CONTROL. Checks OFF, `abs_like(i32::MIN)` returns `i32::MIN`, so
/// `result >= 0` (and `x >= 0 || result > 0`) must be REFUTABLE on the negation path:
///   * the real execution `{x: MIN, _0: MIN}` must SATISFY a full postcondition row
///     (return pin included) — before the fix no row admitted it: the block def said
///     `_0 == -x == 2^31` while the pin said `_0 == MIN`, the contradiction that made
///     every row UNSAT;
///   * on what the block definition alone says, in-process ay must REFUTE a row —
///     before the fix it PROVED every one (`_0 == -x` excludes the wrap).
#[test]
fn abs_like_checks_off_postcondition_is_refuted_by_ay() {
    for clause in [result_non_negative(), neg_of_negative_is_positive()] {
        let f = abs_like(false, clause.clone());
        let witness = |name: &str| match name {
            "x" | "_0" => Some(Val::I(i32::MIN.into())),
            "neg" => Some(Val::B(true)),
            _ => None,
        };
        let rows = postcondition_rows(&f);
        assert!(
            rows.iter().any(|vc| eval(&vc.formula, &witness) == Some(Val::B(true))),
            "checks off: the real execution x = _0 = i32::MIN must satisfy a full row of \
             `{clause:?}` (excluding it is the false-PROVE mechanism): {rows:#?}"
        );
        let verdicts = lia_verdicts(&f);
        assert!(
            verdicts.iter().any(|(r, _)| matches!(r, VerificationResult::Failed { .. })),
            "checks off, -i32::MIN wraps to i32::MIN: `{clause:?}` must be refuted on the \
             negation path, got {verdicts:#?}"
        );
    }
}

/// THE TRUE TWIN, checks OFF: the wrap itself (`x < -2147483647 ==> result == x`, i.e.
/// `x == MIN ==> result == MIN`) proves from the block definition alone — the exact
/// model moves the false proofs to the true claims.
#[test]
fn abs_like_checks_off_true_wrap_claim_proves() {
    let verdicts = lia_verdicts(&abs_like(false, neg_of_min_is_min()));
    assert!(
        verdicts.iter().all(|(r, _)| r.is_proved()),
        "`x >= -2147483647 || result == x` holds of the wrapping negation: {verdicts:#?}"
    );
}

/// CHECKS ON IS UNTOUCHED. The `Assert(OverflowNeg)` path guard `x != MIN` selects
/// the `-x` branch of the exact def, so `result >= 0` keeps proving from the block
/// definition alone (and so from the full row): at `MIN` the function panics.
#[test]
fn abs_like_checks_on_postcondition_still_proves() {
    for clause in [result_non_negative(), neg_of_negative_is_positive()] {
        let verdicts = lia_verdicts(&abs_like(true, clause.clone()));
        assert!(
            verdicts.iter().all(|(r, _)| r.is_proved()),
            "checks on, -MIN panics before it returns: `{clause:?}` must stay proved, got \
             {verdicts:#?}"
        );
    }
}

// ---------------------------------------------------------------------------
// The interval and value-set lanes
// ---------------------------------------------------------------------------

/// The interval lane's `-x` for `x ∈ [i32::MIN, -1]` must contain the machine's
/// `i32::MIN` (it was `[1, 2^31]`); a negation that cannot wrap stays exact.
#[test]
fn interval_lane_bare_neg_keeps_the_wrapped_min() {
    use crate::abstract_interp::{AbstractDomain, Interval, IntervalDomain, transfer_function};
    let f = single_neg(Ty::i32());
    let stmt = assign(2, neg_of(1));
    let mut state = IntervalDomain::top();
    state.set("x".to_string(), Interval::new(i32::MIN.into(), -1));
    let d = transfer_function(&stmt, &f, &state).get("d");
    assert!(
        d.contains(i32::MIN.into()) && d.hi <= i32::MAX.into(),
        "-x over [MIN, -1] must hold the wrapped MIN and stay in i32: got [{}, {}]",
        d.lo,
        d.hi
    );
    state.set("x".to_string(), Interval::new(-5, -1));
    let d = transfer_function(&stmt, &f, &state).get("d");
    assert_eq!((d.lo, d.hi), (1, 5), "a negation that cannot wrap stays exact");
}

/// The value-set lane: a range over `MIN` and an exact set holding `i64::MIN` both
/// keep the machine's wrapped `MIN` (the exact set used to DROP it).
#[test]
fn value_set_lane_bare_neg_keeps_the_wrapped_min() {
    use crate::value_analysis::{ValueSet, ValueSetState, transfer_assign};
    let f = single_neg(Ty::i32());
    let rvalue = neg_of(1);
    let mut state = ValueSetState::top();
    state.set("x".to_string(), ValueSet::range(i32::MIN.into(), -1));
    let d = transfer_assign(&Place::local(2), &rvalue, &f, &state).get("d");
    assert!(
        d.is_top() || d.min_value() <= Some(i32::MIN.into()),
        "-x over [MIN, -1] must hold the wrapped MIN: {d:?}"
    );
    state.set("x".to_string(), ValueSet::range(-5, -1));
    let d = transfer_assign(&Place::local(2), &rvalue, &f, &state).get("d");
    assert_eq!(d, ValueSet::range(1, 5), "a negation that cannot wrap stays exact");

    let f = single_neg(Ty::i64());
    let mut exact = ValueSetState::top();
    exact.set("x".to_string(), ValueSet::Exact([i64::MIN, 5].into_iter().collect()));
    let d = transfer_assign(&Place::local(2), &rvalue, &f, &exact).get("d");
    assert!(
        d.is_top() || d.min_value() == Some(i64::MIN),
        "{{i64::MIN, 5}} negated must keep i64::MIN (it was dropped to {{-5}}): {d:?}"
    );
}

/// CHECKS ON KEEPS ITS PRECISION in the interval lane: the success edge of rustc's
/// `Assert(OverflowNeg)` (`_3 = Eq(x, i32::MIN); assert(!_3)`) excludes `MIN`, so
/// the `-x` behind it stays the exact `[1, i32::MAX]` instead of widening to the
/// whole type. An assert that is not that exact shape narrows nothing.
#[test]
fn interval_lane_overflow_neg_assert_edge_excludes_min() {
    use crate::abstract_interp::transfer::compute_successor_states;
    use crate::abstract_interp::{AbstractDomain, Interval, IntervalDomain, transfer_function};
    let f = abs_like(true, result_non_negative());
    let assert_block = &f.body.blocks[1];
    let mut state = IntervalDomain::top();
    state.set("x".to_string(), Interval::new(i32::MIN.into(), -1));
    let succs = compute_successor_states(&assert_block.terminator, &f, assert_block, &state);
    assert_eq!(succs.len(), 1, "the assert has one success edge: {succs:?}");
    let (target, edge) = &succs[0];
    assert_eq!(*target, BlockId(4));
    let x = edge.get("x");
    assert_eq!((x.lo, x.hi), (i128::from(i32::MIN) + 1, -1), "the edge excludes MIN");
    let d = transfer_function(&assign(0, neg_of(1)), &f, edge).get("_0");
    assert_eq!((d.lo, d.hi), (1, i128::from(i32::MAX)), "checks-on -x stays exact");

    // A non-negation assert on the same condition narrows nothing.
    let mut other = f.clone();
    if let Terminator::Assert { msg, .. } = &mut other.body.blocks[1].terminator {
        *msg = AssertMessage::Overflow(BinOp::Add);
    }
    let block = &other.body.blocks[1];
    let succs = compute_successor_states(&block.terminator, &other, block, &state);
    let x = succs[0].1.get("x");
    assert_eq!((x.lo, x.hi), (i128::from(i32::MIN), -1), "only OverflowNeg narrows");

    // Nor does a comparison against anything but the type's MIN.
    let mut other = f.clone();
    other.body.blocks[1].stmts = vec![assign(
        3,
        Rvalue::BinaryOp(
            BinOp::Eq,
            Operand::Copy(Place::local(1)),
            Operand::Constant(ConstValue::Int(i64::MIN.into())),
        ),
    )];
    let block = &other.body.blocks[1];
    let succs = compute_successor_states(&block.terminator, &other, block, &state);
    let x = succs[0].1.get("x");
    assert_eq!((x.lo, x.hi), (i128::from(i32::MIN), -1), "a non-MIN constant narrows nothing");

    // An `x` pinned to MIN cannot take the success edge.
    state.set("x".to_string(), Interval::constant(i32::MIN.into()));
    let succs = compute_successor_states(&assert_block.terminator, &f, assert_block, &state);
    assert!(succs[0].1.get("x").is_bottom(), "x == MIN makes the success edge unreachable");
}

// ---------------------------------------------------------------------------
// The Machine{w} postcondition lane
// ---------------------------------------------------------------------------

/// The Machine{w} lane translates the WHOLE assembled postcondition row into
/// declared-width QF_BV before the term-`Ite` elimination runs, and refuses the
/// row (`SpecUnverifiable`) on any node outside its fragment. The exact `Neg` def
/// is an `Ite`, so it must be recognized — by construction, as the bare `Neg` was —
/// or every arithmetic-bearing `ensures` over a body with `-x` would lose its proof.
#[test]
fn machine_lane_reads_the_exact_neg_def_as_bv_negation() {
    let f = single_neg(Ty::i32());
    let wrapped = guards::bare_neg_wrap_ite(&int("x"), 32).expect("i32 encodes");
    let def = Formula::Eq(Box::new(int("d")), Box::new(wrapped.clone()));
    let translated = crate::contracts::machine_faithful_vc_formula(&f, &def)
        .expect("the exact Neg def must stay inside the declared-width fragment");
    let bv = |name: &str| Formula::Var(name.into(), Sort::BitVec(32));
    assert_eq!(
        translated,
        Formula::Eq(
            Box::new(bv("d")),
            Box::new(Formula::BvSub(
                Box::new(Formula::BitVec { value: 0, width: 32 }),
                Box::new(bv("x")),
                32,
            )),
        ),
        "the exact Neg def reads as two's-complement `0 -w x`, as the bare Neg did"
    );
    // Any OTHER `Ite` over a negation stays outside the fragment.
    let Formula::Ite(cond, _, otherwise) = wrapped else { unreachable!() };
    let forged = Formula::Eq(
        Box::new(int("d")),
        Box::new(Formula::Ite(cond, Box::new(Formula::Int(0)), otherwise)),
    );
    assert!(
        crate::contracts::machine_faithful_vc_formula(&f, &forged).is_none(),
        "only the constructor's exact node may launder into the fragment"
    );
}

/// End to end on the contract lane: `ensures result + x == 0` (machine arithmetic in
/// the clause, so the Machine{w} lane) over `-x` keeps a translated, provable row
/// with checks on AND off — `-MIN + MIN` wraps to `0` too — and never falls to the
/// `SpecUnverifiable` refusal.
#[test]
fn machine_lane_neg_postcondition_still_translates_and_proves() {
    use trust_router::{InProcessAyBackend, VerificationBackend};
    let clause = Formula::Eq(
        Box::new(Formula::Add(Box::new(int("_0")), Box::new(int("x")))),
        Box::new(Formula::Int(0)),
    );
    let backend = InProcessAyBackend::new();
    for checks_on in [false, true] {
        let f = negate_x(checks_on, clause.clone());
        let vcs = generate_v2_contract_vcs_impl(&f, None);
        assert!(
            !vcs.iter().any(|vc| matches!(&vc.kind, VcKind::UnsupportedMir { detail, .. }
                if detail.contains("declared-width"))),
            "checks_on={checks_on}: the row must translate, not refuse: {vcs:#?}"
        );
        let rows: Vec<_> =
            vcs.iter().filter(|vc| matches!(vc.kind, VcKind::Postcondition)).collect();
        assert!(!rows.is_empty(), "checks_on={checks_on}: the clause must raise a row");
        for vc in rows {
            assert!(
                format!("{:?}", vc.formula).contains("BvSub"),
                "checks_on={checks_on}: the row is the declared-width reading: {:?}",
                vc.formula
            );
            let result = backend.verify(vc);
            assert!(
                result.is_proved(),
                "checks_on={checks_on}: `result + x == 0` holds of the wrapping negation: \
                 {result:?} for {:?}",
                vc.formula
            );
        }
    }
}
