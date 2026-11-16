// trust_vcgen/abstract_interp/statement_point_tests.rs: the whole-function interval
// environment bounds a name at every statement, not only at block entries.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0
//
// Trust (2026-10-09, trust-interval-drop-havoc, independent review). The discharge
// reads a versioned name (`b#s0_1`) through the environment's entry for the bare `b`,
// which is sound only if that entry bounds `b` wherever `b` is a value. The
// environment was the join of the fixpoint's block ENTRY states, and a value written
// and overwritten inside one block is no block's entry state. Measured as builds that
// passed while the program panicked on every run (review probes `e02`, `e03`: a swap
// of two constant-initialised locals in the entry block, then a division by zero or an
// add overflow). Pinned here on those probes' MIR:
//
// * the swap's intermediate values are in the environment, and the obligation behind
//   them is dispatched, not discharged (overflow and division);
// * the same shape in a NON-entry block, and with a parameter narrowed by a `requires`;
// * what the join must keep: a name written once keeps its exact interval, and an
//   obligation that follows from one is still discharged (anti-vacuity);
// * a first write that leaves a local at its whole type range is a write all the same;
// * a call that unwinds into a cleanup block wrote before it left, and the fixpoint
//   follows no unwind edge;
// * a value the negation check's success edge rules out is still the value the check
//   is about;
// * an empty interval, which is what such an edge leaves behind, discharges nothing.
// * a name an opaque store may write joins as unbounded even where the state never
//   tracked it;
// * a name a statement changes without writing it by name (a field a precondition
//   bounds, under a whole write of its local) joins as unbounded too;
// * a value unbounded on one side joins as its part within the local's type range,
//   and a value with a finite bound past the type as the whole range.
//
// Every environment these tests compute also runs
// `transfer::assert_environment_bounds_every_statement_point`, which re-derives the
// property from the formula path's write oracle.

use trust_types::*;

use super::{
    AbstractDomain, Interval, IntervalDomain, merged_interval_environment, try_discharge_vc,
};

const MAX: u128 = u32::MAX as u128;

fn u32_ty() -> Ty {
    Ty::Int { width: 32, signed: false }
}

fn assign(place: Place, rvalue: Rvalue) -> Statement {
    Statement::Assign { place, rvalue, span: SourceSpan::default() }
}

fn konst(n: u128) -> Rvalue {
    Rvalue::Use(Operand::Constant(ConstValue::Uint(n, 32)))
}

fn copy(local: usize) -> Rvalue {
    Rvalue::Use(Operand::Copy(Place::local(local)))
}

fn local(index: usize, ty: Ty, name: &str) -> LocalDecl {
    LocalDecl { index, ty, name: Some(name.to_string()) }
}

fn function(
    name: &str,
    locals: Vec<LocalDecl>,
    blocks: Vec<BasicBlock>,
    preconditions: Vec<Formula>,
) -> VerifiableFunction {
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("statement_point::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks,
            arg_count: 1,
            return_ty: u32_ty(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions,
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// `_k = CheckedAdd(copy lhs, rhs); Assert(!_k.1) -> target`.
fn checked_add(sum: usize, lhs: usize, rhs: u128) -> Statement {
    assign(
        Place::local(sum),
        Rvalue::CheckedBinaryOp(
            BinOp::Add,
            Operand::Copy(Place::local(lhs)),
            Operand::Constant(ConstValue::Uint(rhs, 32)),
        ),
    )
}

fn assert_no_overflow(sum: usize, target: usize) -> Terminator {
    Terminator::Assert {
        cond: Operand::Move(Place { local: sum, projections: vec![Projection::Field(1)] }),
        expected: false,
        msg: AssertMessage::Overflow(BinOp::Add),
        target: BlockId(target),
        span: SourceSpan::default(),
        unwind: UnwindEdge::Continue,
    }
}

fn return_field0(id: usize, of: usize) -> BasicBlock {
    BasicBlock {
        id: BlockId(id),
        stmts: vec![assign(
            Place::local(0),
            Rvalue::Use(Operand::Move(Place {
                local: of,
                projections: vec![Projection::Field(0)],
            })),
        )],
        terminator: Terminator::Return,
    }
}

/// (dispatched to the solver, discharged at generation) obligations of one kind.
fn rows(func: &VerifiableFunction, kind: impl Fn(&VcKind) -> bool) -> (usize, usize) {
    let (solver, discharged) = crate::generate_vcs_with_discharge(func);
    (
        solver.iter().filter(|vc| kind(&vc.kind)).count(),
        discharged.iter().filter(|(vc, _)| kind(&vc.kind)).count(),
    )
}

fn is_add_overflow(kind: &VcKind) -> bool {
    matches!(kind, VcKind::ArithmeticOverflow { op: BinOp::Add, .. })
}

/// The review probe `e03_entry_swap_overflow_bug`, with the two constants as
/// parameters of the fixture:
///
/// ```text
/// pub fn f(k: u32) -> u32 {
///     let mut a = A;
///     let mut b = B;
///     let t = a;
///     a = b;
///     b = t;
///     a + 1
/// }
/// ```
///
/// ```text
/// bb0: a = A; b = B; t = copy a; _5 = copy b; a = move _5; _6 = copy t; b = move _6;
///      _7 = copy a; _8 = CheckedAdd(copy _7, 1)        Assert(!_8.1) -> bb1
/// bb1: _0 = move _8.0                                   Return
/// ```
fn entry_swap_then_add(a: u128, b: u128) -> VerifiableFunction {
    let locals = vec![
        local(0, u32_ty(), "_0"),
        local(1, u32_ty(), "k"),
        local(2, u32_ty(), "a"),
        local(3, u32_ty(), "b"),
        local(4, u32_ty(), "t"),
        local(5, u32_ty(), "_5"),
        local(6, u32_ty(), "_6"),
        local(7, u32_ty(), "_7"),
        local(8, Ty::Tuple(vec![u32_ty(), Ty::Bool]), "_8"),
    ];
    let blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![
                assign(Place::local(2), konst(a)),
                assign(Place::local(3), konst(b)),
                assign(Place::local(4), copy(2)),
                assign(Place::local(5), copy(3)),
                assign(Place::local(2), copy(5)),
                assign(Place::local(6), copy(4)),
                assign(Place::local(3), copy(6)),
                assign(Place::local(7), copy(2)),
                checked_add(8, 7, 1),
            ],
            terminator: assert_no_overflow(8, 1),
        },
        return_field0(1, 8),
    ];
    function("entry_swap_then_add", locals, blocks, vec![])
}

/// The probe. After the swap `a` is `u32::MAX` and `a + 1` overflows on every run. The
/// environment used to say `a ∈ [MAX, MAX]` and `b ∈ [0, 0]` — the values at the END of
/// the entry block — so the obligation's own `Eq(_5, b#s0_1)` (the copy of `b` while it
/// was `MAX`) evaluated false and the overflow was discharged as unreachable.
#[test]
fn a_value_overwritten_inside_the_entry_block_is_in_the_environment() {
    let func = entry_swap_then_add(0, MAX);
    let env = merged_interval_environment(&func);
    let both = Interval::new(0, i128::from(u32::MAX));
    assert_eq!(env.get("a"), both, "`a` holds 0, then MAX");
    assert_eq!(env.get("b"), both, "`b` holds MAX, then 0");
    // What the join must NOT lose: a name written once keeps its exact interval.
    assert_eq!(env.get("t"), Interval::constant(0));
    assert_eq!(env.get("_5"), Interval::constant(i128::from(u32::MAX)));
    assert_eq!(env.get("_7"), Interval::constant(i128::from(u32::MAX)));
    let (dispatched, discharged) = rows(&func, is_add_overflow);
    assert_eq!(dispatched + discharged, 1, "ANTI-VACUITY: one Add-overflow obligation");
    assert_eq!(discharged, 0, "`MAX + 1` was discharged at generation");
}

/// The control: swapping 5 and 7 leaves `a == 7`, and `7 + 1` cannot overflow. The lane
/// still says so by itself, from `_7 ∈ [7, 7]` — a name written once.
#[test]
fn the_swap_s_safe_twin_is_still_discharged() {
    let func = entry_swap_then_add(5, 7);
    let env = merged_interval_environment(&func);
    assert_eq!(env.get("a"), Interval::new(5, 7));
    assert_eq!(env.get("b"), Interval::new(5, 7));
    assert_eq!(env.get("_7"), Interval::constant(7));
    let (dispatched, discharged) = rows(&func, is_add_overflow);
    assert_eq!(
        (dispatched, discharged),
        (0, 1),
        "ANTI-VACUITY: `7 + 1` is the lane's to discharge"
    );
}

/// The review probe `e02_entry_swap_div_bug`: the same swap of 1 and 0, then `k / a`.
///
/// ```text
/// bb0: a = 1; b = 0; t = copy a; _5 = copy b; a = move _5; _6 = copy t; b = move _6;
///      _7 = copy a; _8 = Eq(copy _7, 0)                 Assert(!_8, DivisionByZero) -> bb1
/// bb1: _0 = Div(copy k, move _7)                        Return
/// ```
#[test]
fn a_division_by_a_swapped_in_zero_is_not_discharged() {
    let locals = vec![
        local(0, u32_ty(), "_0"),
        local(1, u32_ty(), "k"),
        local(2, u32_ty(), "a"),
        local(3, u32_ty(), "b"),
        local(4, u32_ty(), "t"),
        local(5, u32_ty(), "_5"),
        local(6, u32_ty(), "_6"),
        local(7, u32_ty(), "_7"),
        local(8, Ty::Bool, "_8"),
    ];
    let blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![
                assign(Place::local(2), konst(1)),
                assign(Place::local(3), konst(0)),
                assign(Place::local(4), copy(2)),
                assign(Place::local(5), copy(3)),
                assign(Place::local(2), copy(5)),
                assign(Place::local(6), copy(4)),
                assign(Place::local(3), copy(6)),
                assign(Place::local(7), copy(2)),
                assign(
                    Place::local(8),
                    Rvalue::BinaryOp(
                        BinOp::Eq,
                        Operand::Copy(Place::local(7)),
                        Operand::Constant(ConstValue::Uint(0, 32)),
                    ),
                ),
            ],
            terminator: Terminator::Assert {
                cond: Operand::Move(Place::local(8)),
                expected: false,
                msg: AssertMessage::DivisionByZero,
                target: BlockId(1),
                span: SourceSpan::default(),
                unwind: UnwindEdge::Continue,
            },
        },
        BasicBlock {
            id: BlockId(1),
            stmts: vec![assign(
                Place::local(0),
                Rvalue::BinaryOp(
                    BinOp::Div,
                    Operand::Copy(Place::local(1)),
                    Operand::Move(Place::local(7)),
                ),
            )],
            terminator: Terminator::Return,
        },
    ];
    let func = function("entry_swap_then_div", locals, blocks, vec![]);
    let env = merged_interval_environment(&func);
    assert_eq!(env.get("a"), Interval::new(0, 1));
    assert_eq!(env.get("b"), Interval::new(0, 1));
    assert_eq!(env.get("_7"), Interval::constant(0), "the divisor is exactly 0");
    let (dispatched, discharged) = rows(&func, |kind| matches!(kind, VcKind::DivisionByZero));
    assert!(dispatched + discharged >= 1, "ANTI-VACUITY: no division-by-zero obligation");
    assert_eq!(discharged, 0, "`k / 0` was discharged at generation");
}

/// Not the entry block's privilege. Every name here is bounded by the environment
/// because the ENTRY block defines it; the value that goes missing lives inside bb1:
///
/// ```text
/// bb0: a = 1; t = 7; d = 1                              -> bb1
/// bb1: t = copy a; d = copy t; t = 7;
///      _5 = copy d; _6 = CheckedAdd(copy _5, u32::MAX)  Assert(!_6.1) -> bb2
/// bb2: _0 = move _6.0                                   Return
/// ```
///
/// `t` is 7 at the entry of bb1 and 7 at the entry of bb2, and 1 in between, where `d`
/// copies it. Entry states alone say `t ∈ [7, 7]` and `d ∈ [1, 1]`, so `Eq(d', t')` is
/// "false" and everything after it "unreachable" — `1 + u32::MAX` included.
#[test]
fn a_value_overwritten_inside_a_later_block_is_in_the_environment() {
    let locals = vec![
        local(0, u32_ty(), "_0"),
        local(1, u32_ty(), "k"),
        local(2, u32_ty(), "a"),
        local(3, u32_ty(), "t"),
        local(4, u32_ty(), "d"),
        local(5, u32_ty(), "_5"),
        local(6, Ty::Tuple(vec![u32_ty(), Ty::Bool]), "_6"),
    ];
    let blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![
                assign(Place::local(2), konst(1)),
                assign(Place::local(3), konst(7)),
                assign(Place::local(4), konst(1)),
            ],
            terminator: Terminator::Goto(BlockId(1)),
        },
        BasicBlock {
            id: BlockId(1),
            stmts: vec![
                assign(Place::local(3), copy(2)),
                assign(Place::local(4), copy(3)),
                assign(Place::local(3), konst(7)),
                assign(Place::local(5), copy(4)),
                checked_add(6, 5, MAX),
            ],
            terminator: assert_no_overflow(6, 2),
        },
        return_field0(2, 6),
    ];
    let func = function("later_block_overwrite", locals, blocks, vec![]);
    let env = merged_interval_environment(&func);
    assert_eq!(env.get("t"), Interval::new(1, 7), "`t` is 1 between two statements of bb1");
    assert_eq!(env.get("d"), Interval::constant(1));
    assert_eq!(env.get("a"), Interval::constant(1));
    let (dispatched, discharged) = rows(&func, is_add_overflow);
    assert_eq!(dispatched + discharged, 1, "ANTI-VACUITY: one Add-overflow obligation");
    assert_eq!(discharged, 0, "`1 + u32::MAX` was discharged at generation");
}

/// A parameter narrowed by a precondition, overwritten, copied and restored in the
/// entry block (`fn f(mut k: u32) requires k < 3`):
///
/// ```text
/// bb0: k = 4_000_000_000; t = copy k; k = 0;
///      _3 = CheckedAdd(copy t, 1_000_000_000)           Assert(!_3.1) -> bb1
/// bb1: _0 = move _3.0                                   Return
/// ```
///
/// The entry state bounds `k` by the precondition, every later state by 0, and the
/// read `t = k` sees four billion.
#[test]
fn an_overwritten_parameter_keeps_no_precondition_bound() {
    let locals = vec![
        local(0, u32_ty(), "_0"),
        local(1, u32_ty(), "k"),
        local(2, u32_ty(), "t"),
        local(3, Ty::Tuple(vec![u32_ty(), Ty::Bool]), "_3"),
    ];
    let blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![
                assign(Place::local(1), konst(4_000_000_000)),
                assign(Place::local(2), copy(1)),
                assign(Place::local(1), konst(0)),
                checked_add(3, 2, 1_000_000_000),
            ],
            terminator: assert_no_overflow(3, 1),
        },
        return_field0(1, 3),
    ];
    let requires =
        Formula::Lt(Box::new(Formula::Var("k".to_string(), Sort::Int)), Box::new(Formula::Int(3)));
    let func = function("overwritten_parameter", locals, blocks, vec![requires]);
    let env = merged_interval_environment(&func);
    assert_eq!(env.get("k"), Interval::new(0, 4_000_000_000));
    assert_eq!(env.get("t"), Interval::constant(4_000_000_000));
    let (dispatched, discharged) = rows(&func, is_add_overflow);
    assert_eq!(dispatched + discharged, 1, "ANTI-VACUITY: one Add-overflow obligation");
    assert_eq!(discharged, 0, "`4e9 + 1e9` was discharged at generation");
}

/// `requires p.0 <= 3`, with or without a whole write of `p` in front:
///
/// ```text
/// bb0: [p = copy q;] t = copy p.0; p.0 = 0              -> bb1
/// bb1: _0 = copy t                                      Return
/// ```
fn field_under_a_precondition(whole_write: bool) -> (VerifiableFunction, String) {
    field_under(whole_write, |p0| Formula::Le(Box::new(p0), Box::new(Formula::Int(3))))
}

/// [`field_under_a_precondition`] with the precondition on `p.0` given by `requires`.
fn field_under(
    whole_write: bool,
    requires: impl Fn(Formula) -> Formula,
) -> (VerifiableFunction, String) {
    let pair = Ty::Tuple(vec![u32_ty(), u32_ty()]);
    let p0 = Place { local: 1, projections: vec![Projection::Field(0)] };
    let locals = vec![
        local(0, u32_ty(), "_0"),
        local(1, pair.clone(), "p"),
        local(2, pair, "q"),
        local(3, u32_ty(), "t"),
    ];
    let mut stmts = Vec::new();
    if whole_write {
        stmts.push(assign(Place::local(1), copy(2)));
    }
    stmts.push(assign(Place::local(3), Rvalue::Use(Operand::Copy(p0.clone()))));
    stmts.push(assign(p0.clone(), konst(0)));
    let blocks = vec![
        BasicBlock { id: BlockId(0), stmts, terminator: Terminator::Goto(BlockId(1)) },
        BasicBlock {
            id: BlockId(1),
            stmts: vec![assign(Place::local(0), copy(3))],
            terminator: Terminator::Return,
        },
    ];
    let mut func = function("field_under_a_precondition", locals, blocks, vec![]);
    func.body.arg_count = 2;
    let name = crate::place_to_var_name(&func, &p0);
    func.preconditions = vec![requires(Formula::Var(name.clone(), Sort::Int))];
    (func, name)
}

/// A name that is neither a statement's destination nor one of its extra writes
/// changes all the same: a whole write of `p` leaves `p.0` holding a new value. The
/// state forgets `p.0` there (the destination rebinds it), and "the new value of every
/// other name whose interval the transfer changed" is the one step of the walk that
/// tells the environment.
///
/// The entry state bounds `p.0` by the precondition and every later state by 0, so
/// the block-entry join says `p.0 <= 3`; between `p = copy q` and `p.0 = 0` it is
/// `q.0`, whatever the caller passed. A projection name is in the environment only
/// when a precondition names it (the entry block's state is unbounded for every
/// other one), which is why no integer LOCAL reaches this step: nothing is below or
/// above one, so only its own assignment or an extra write changes it.
#[test]
fn a_whole_write_unbounds_the_field_a_precondition_bounded() {
    // ANTI-VACUITY: without the whole write the environment carries the bound, the
    // precondition's joined with the 0 the block stores.
    let (kept, name) = field_under_a_precondition(false);
    assert_eq!(merged_interval_environment(&kept).get(&name), Interval::new(i128::MIN, 3));
    let (func, name) = field_under_a_precondition(true);
    assert_eq!(
        merged_interval_environment(&func).get(&name),
        Interval::TOP,
        "`{name}` is `q.0` between the whole write and the store of 0"
    );
}

/// What the value a statement leaves says about a local of an integer TYPE
/// (`transfer::as_value_of_type`), on `t = copy p.0` with `t: u32` and three
/// preconditions on the field (a projection has no seeded type range, so the copy
/// carries the precondition's interval as it is):
///
/// * `p.0 <= 3` is unbounded below. The copy joins as `[0, 3]`, and the environment
///   keeps the bound every block entry has for `t`. It used to join as the whole `u32`
///   range, which unbounded `t` above: with `requires p.0 <= 3`, `let big = p.0 >= 10;
///   p.0 = 0; if big { .. }` then had its dead branch dispatched and REFUTED, a correct
///   program main builds (probe round `ep-r3`, controls `fc01` and `fc02`).
/// * `-5 <= p.0 <= 3` has a FINITE bound below the type. That is not a `u32`'s value on
///   either side, and the copy joins as the whole range.
/// * `p.0 <= -1` has nothing in common with the type. The whole range again: an empty
///   contribution would be no contribution, and the local does hold a value.
#[test]
fn a_one_sided_bound_survives_the_join_and_a_bound_past_the_type_does_not() {
    let u32_max = i128::from(u32::MAX);
    let le = |bound: i128| move |p0| Formula::Le(Box::new(p0), Box::new(Formula::Int(bound)));
    let (one_sided, _) = field_under(false, le(3));
    assert_eq!(merged_interval_environment(&one_sided).get("t"), Interval::new(i128::MIN, 3));
    let (finite, _) = field_under(false, |p0: Formula| {
        Formula::And(vec![
            Formula::Ge(Box::new(p0.clone()), Box::new(Formula::Int(-5))),
            Formula::Le(Box::new(p0), Box::new(Formula::Int(3))),
        ])
    });
    assert_eq!(merged_interval_environment(&finite).get("t"), Interval::new(-5, u32_max));
    let (disjoint, _) = field_under(false, le(-1));
    assert_eq!(merged_interval_environment(&disjoint).get("t"), Interval::new(i128::MIN, u32_max));
}

/// The probe control `fc01` (round `ep-r3`), which main builds and the first form of
/// the join refuted:
///
/// ```text
/// #[requires(p.0 <= 3)]
/// pub fn f(mut p: (u32, u32), q: (u32, u32)) -> u32 {
///     let big = p.0 >= 10;
///     p.0 = 0;
///     if big { q.1 + u32::MAX } else { p.0 }
/// }
/// ```
///
/// ```text
/// bb0: _4 = copy p.0; big = Ge(copy _4, 10); p.0 = 0    SwitchInt(big) -> [0: bb3, _: bb1]
/// bb1: _5 = copy q.1; _6 = CheckedAdd(copy _5, MAX)     Assert(!_6.1) -> bb2
/// bb2: _0 = move _6.0                                   Return
/// bb3: _0 = copy p.0                                    Return
/// ```
///
/// The branch is dead by the precondition, and only the interval lane can say so:
/// once `p.0` is stored to, the formula has no tie from `_4` to the field. `_4` is
/// written once and holds `[i128::MIN, 3]`, which must still decide the guard.
#[test]
fn a_branch_a_one_sided_field_precondition_makes_dead_is_still_discharged() {
    let pair = Ty::Tuple(vec![u32_ty(), u32_ty()]);
    let field =
        |local: usize, index: usize| Place { local, projections: vec![Projection::Field(index)] };
    let locals = vec![
        local(0, u32_ty(), "_0"),
        local(1, pair.clone(), "p"),
        local(2, pair, "q"),
        local(3, Ty::Bool, "big"),
        local(4, u32_ty(), "_4"),
        local(5, u32_ty(), "_5"),
        local(6, Ty::Tuple(vec![u32_ty(), Ty::Bool]), "_6"),
    ];
    let blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![
                assign(Place::local(4), Rvalue::Use(Operand::Copy(field(1, 0)))),
                assign(
                    Place::local(3),
                    Rvalue::BinaryOp(
                        BinOp::Ge,
                        Operand::Copy(Place::local(4)),
                        Operand::Constant(ConstValue::Uint(10, 32)),
                    ),
                ),
                assign(field(1, 0), konst(0)),
            ],
            terminator: Terminator::SwitchInt {
                discr: Operand::Move(Place::local(3)),
                targets: vec![(0, BlockId(3))],
                otherwise: BlockId(1),
                exhaustive_enum_unreachable: false,
                span: SourceSpan::default(),
            },
        },
        BasicBlock {
            id: BlockId(1),
            stmts: vec![
                assign(Place::local(5), Rvalue::Use(Operand::Copy(field(2, 1)))),
                checked_add(6, 5, MAX),
            ],
            terminator: assert_no_overflow(6, 2),
        },
        return_field0(2, 6),
        BasicBlock {
            id: BlockId(3),
            stmts: vec![assign(Place::local(0), Rvalue::Use(Operand::Copy(field(1, 0))))],
            terminator: Terminator::Return,
        },
    ];
    let mut func = function("field_precondition_dead_branch", locals, blocks, vec![]);
    func.body.arg_count = 2;
    let name = crate::place_to_var_name(&func, &field(1, 0));
    func.preconditions =
        vec![Formula::Le(Box::new(Formula::Var(name, Sort::Int)), Box::new(Formula::Int(3)))];
    assert_eq!(merged_interval_environment(&func).get("_4"), Interval::new(i128::MIN, 3));
    let (dispatched, discharged) = rows(&func, is_add_overflow);
    assert_eq!(dispatched + discharged, 1, "ANTI-VACUITY: one Add-overflow obligation");
    assert_eq!(dispatched, 0, "the dead branch's overflow was dispatched");
}

/// A name the state never tracked, written by a statement that is not its assignment.
/// `c` is an `i128` (its type range is the whole domain, so the state carries no bound
/// for it before its first write); `(*p) = copy k` through the raw-pointer PARAMETER `p`
/// is an opaque store, and `c` is borrowed, so the write oracle says the store may write
/// it:
///
/// ```text
/// bb0: q = &mut c; (*p) = copy k; c = 0                 -> bb1
/// bb1: _0 = const 0                                     Return
/// ```
///
/// Nothing changes in the state at the store (`c` is unbounded before and after), and
/// the later `c = 0` is all any block entry sees. The environment must not bound `c`:
/// between the store and the assignment it holds whatever the store wrote.
///
/// Merge 2026-10-14: `p` is a `*mut i128`. Upstream's fixture stored through a `&mut
/// i128` parameter, which is the one shape the round-112 exemption
/// (`store_spares_frame_storage`: a never-reseated `&mut` parameter reaches only caller
/// memory, never this frame's `c`) deliberately keeps, so it no longer tested the
/// lockstep forget. The `&mut` form is pinned below as that exemption.
#[test]
fn a_name_an_opaque_store_may_write_is_unbounded_even_if_untracked() {
    let i128_ty = Ty::Int { width: 128, signed: true };
    let mut_i128 = Ty::Ref { mutable: true, inner: Box::new(i128_ty.clone()) };
    let raw_mut_i128 = Ty::RawPtr { mutable: true, pointee: Box::new(i128_ty.clone()) };
    let through_p = Place { local: 1, projections: vec![Projection::Deref] };
    let body_with = |p_ty: &Ty, store: bool| {
        let locals = vec![
            local(0, u32_ty(), "_0"),
            local(1, p_ty.clone(), "p"),
            local(2, i128_ty.clone(), "c"),
            local(3, mut_i128.clone(), "q"),
            local(4, i128_ty.clone(), "k"),
        ];
        let blocks = vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    assign(Place::local(4), Rvalue::Use(Operand::Constant(ConstValue::Int(9)))),
                    assign(Place::local(3), Rvalue::Ref { mutable: true, place: Place::local(2) }),
                    if store { assign(through_p.clone(), copy(4)) } else { Statement::Nop },
                    assign(Place::local(2), Rvalue::Use(Operand::Constant(ConstValue::Int(0)))),
                ],
                terminator: Terminator::Goto(BlockId(1)),
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![assign(Place::local(0), konst(0))],
                terminator: Terminator::Return,
            },
        ];
        function("untracked_store_target", locals, blocks, vec![])
    };
    let control = body_with(&raw_mut_i128, false);
    assert_eq!(
        merged_interval_environment(&control).get("c"),
        Interval::constant(0),
        "ANTI-VACUITY: without the store the environment bounds `c`"
    );
    let func = body_with(&raw_mut_i128, true);
    let Statement::Assign { place, .. } = &func.body.blocks[0].stmts[2] else { unreachable!() };
    assert!(crate::deref_store_is_opaque(&func, place), "ANTI-VACUITY: a parameter's store");
    assert!(
        crate::generate::stmt_writes_name(&func, &func.body.blocks[0], 2, "c"),
        "ANTI-VACUITY: the oracle must say the store may write `c`"
    );
    assert_eq!(merged_interval_environment(&func).get("c"), Interval::TOP);

    // The round-112 exemption: the same store through a never-reseated `&mut i128`
    // parameter cannot reach this frame's `c`, so `c` keeps its interval although the
    // oracle still versions it (a superset of the store's real writes).
    let exempt = body_with(&mut_i128, true);
    let Statement::Assign { place, .. } = &exempt.body.blocks[0].stmts[2] else { unreachable!() };
    assert!(crate::deref_store_is_opaque(&exempt, place), "ANTI-VACUITY: an opaque store");
    assert!(crate::generate::stmt_writes_name(&exempt, &exempt.body.blocks[0], 2, "c"));
    assert_eq!(merged_interval_environment(&exempt).get("c"), Interval::constant(0));
}

/// A local's FIRST write may leave its interval exactly where the entry state seeded
/// it — its whole type range — and is a write all the same: from there on the local
/// is a value, and that value is anything of its type.
///
/// ```text
/// bb0: x = copy k; t = copy x; x = 5                    -> bb1
/// bb1: _0 = copy t                                      Return
/// ```
///
/// The state does not change at `x = copy k` (`x` was seeded `[0, u32::MAX]` and `k`
/// is `[0, u32::MAX]`), the entry block's own entry state is left out for `x` (not yet
/// a value there), and every later state says `x ∈ [5, 5]`. The environment must say
/// what `x` held when `t` copied it.
#[test]
fn a_first_write_that_leaves_the_type_range_is_joined() {
    let locals = vec![
        local(0, u32_ty(), "_0"),
        local(1, u32_ty(), "k"),
        local(2, u32_ty(), "x"),
        local(3, u32_ty(), "t"),
    ];
    let body = |first: Rvalue| {
        let blocks = vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    assign(Place::local(2), first),
                    assign(Place::local(3), copy(2)),
                    assign(Place::local(2), konst(5)),
                ],
                terminator: Terminator::Goto(BlockId(1)),
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![assign(Place::local(0), copy(3))],
                terminator: Terminator::Return,
            },
        ];
        function("first_write_type_range", locals.clone(), blocks, vec![])
    };
    // Anti-vacuity: a first write the state does see (`x = 9`) joins as that value.
    assert_eq!(merged_interval_environment(&body(konst(9))).get("x"), Interval::new(5, 9));
    let env = merged_interval_environment(&body(copy(1)));
    assert_eq!(env.get("x"), Interval::new(0, i128::from(u32::MAX)));
    assert_eq!(env.get("t"), Interval::new(0, i128::from(u32::MAX)));
}

/// A call that never returns but UNWINDS INTO A CLEANUP BLOCK has written before it
/// left, and the cleanup path runs after it. The fixpoint propagates along normal
/// successors only, so the call's havoc is the entry state of no block:
///
/// ```text
/// bb0: c = 0; p = &mut c; _4 = Gt(copy k, 3)   SwitchInt(move _4): 0 -> bb2, else -> bb1
/// bb1: _5 = store_then_panic(copy p)           no return; unwind -> bb3 (cleanup)
/// bb2: _0 = copy c                             Return
/// bb3: (cleanup)                               Resume
/// ```
///
/// With `unwind: Continue` (the function is left at once, no cleanup block) nothing
/// in it runs after the call, and `c` keeps its bound (anti-vacuity).
#[test]
fn a_call_that_unwinds_into_cleanup_has_written_what_it_borrowed() {
    let body = |unwind: UnwindEdge| {
        let locals = vec![
            local(0, u32_ty(), "_0"),
            local(1, u32_ty(), "k"),
            local(2, u32_ty(), "c"),
            local(3, Ty::Ref { mutable: true, inner: Box::new(u32_ty()) }, "p"),
            local(4, Ty::Bool, "_4"),
            local(5, u32_ty(), "_5"),
        ];
        let blocks = vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    assign(Place::local(2), konst(0)),
                    assign(Place::local(3), Rvalue::Ref { mutable: true, place: Place::local(2) }),
                    assign(
                        Place::local(4),
                        Rvalue::BinaryOp(
                            BinOp::Gt,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Uint(3, 32)),
                        ),
                    ),
                ],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Move(Place::local(4)),
                    targets: vec![(0, BlockId(2))],
                    otherwise: BlockId(1),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![],
                terminator: Terminator::Call {
                    unwind,
                    is_unsafe_sig: false,
                    callee_identity: None,
                    callee_key: None,
                    is_foreign: false,
                    func: "test::store_then_panic".to_string(),
                    args: vec![Operand::Copy(Place::local(3))],
                    dest: Place::local(5),
                    target: None,
                    span: SourceSpan::default(),
                    atomic: None,
                },
            },
            BasicBlock {
                id: BlockId(2),
                stmts: vec![assign(Place::local(0), copy(2))],
                terminator: Terminator::Return,
            },
            BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Resume },
        ];
        function("unwinding_call", locals, blocks, vec![])
    };
    let leaves = body(UnwindEdge::Continue);
    assert!(
        crate::generate::terminator_def_names(&leaves, &leaves.body.blocks[1])
            .iter()
            .any(|written| crate::generate::write_rebinds(written, "c")),
        "ANTI-VACUITY: the formula path must say the call may write `c`"
    );
    assert_eq!(
        merged_interval_environment(&leaves).get("c"),
        Interval::constant(0),
        "ANTI-VACUITY: nothing in the function runs after a call that leaves it"
    );
    let cleans_up = body(UnwindEdge::Cleanup(BlockId(3)));
    assert_eq!(
        merged_interval_environment(&cleans_up).get("c"),
        Interval::new(0, i128::from(u32::MAX)),
        "the cleanup path runs after the call wrote `c`"
    );
}

/// The value an edge narrows away is still a value the block held. rustc lowers a
/// checked `-y` as `_c = Eq(y, MIN); assert(!_c) -> bb1; bb1: Neg(y)`, and the fixpoint
/// reads the assert's success edge back onto `y` (`y != MIN`). With `y` pinned to `MIN`
/// that edge is infeasible: every later block holds no value for `y` at all.
///
/// ```text
/// bb0: [x = MIN; y = copy x; x = 0 |  y = MIN];
///      _4 = Eq(copy y, const MIN)                       Assert(!_4, OverflowNeg) -> bb1
/// bb1: _0 = Neg(copy y)                                 Return
/// ```
///
/// The entry block's own entry state is left out for `y` (not yet a value there), so
/// block entries alone gave the environment NO value for `y` — and the negation
/// obligation, which asks exactly whether `y` can be `MIN`, was answered from what
/// holds AFTER the check passed. `y` is `MIN` on every run.
#[test]
fn a_value_the_negation_check_rules_out_is_still_in_the_environment() {
    let i32_ty = Ty::Int { width: 32, signed: true };
    let min = i128::from(i32::MIN);
    let min_const = || Rvalue::Use(Operand::Constant(ConstValue::Int(min)));
    let body = |through_copy: bool| {
        let locals = vec![
            local(0, i32_ty.clone(), "_0"),
            local(1, i32_ty.clone(), "k"),
            local(2, i32_ty.clone(), "x"),
            local(3, i32_ty.clone(), "y"),
            local(4, Ty::Bool, "_4"),
        ];
        let mut stmts = if through_copy {
            vec![
                assign(Place::local(2), min_const()),
                assign(Place::local(3), copy(2)),
                assign(Place::local(2), Rvalue::Use(Operand::Constant(ConstValue::Int(0)))),
            ]
        } else {
            vec![assign(Place::local(3), min_const())]
        };
        stmts.push(assign(
            Place::local(4),
            Rvalue::BinaryOp(
                BinOp::Eq,
                Operand::Copy(Place::local(3)),
                Operand::Constant(ConstValue::Int(min)),
            ),
        ));
        let blocks = vec![
            BasicBlock {
                id: BlockId(0),
                stmts,
                terminator: Terminator::Assert {
                    cond: Operand::Move(Place::local(4)),
                    expected: false,
                    msg: AssertMessage::OverflowNeg,
                    target: BlockId(1),
                    span: SourceSpan::default(),
                    unwind: UnwindEdge::Continue,
                },
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![assign(
                    Place::local(0),
                    Rvalue::UnaryOp(UnOp::Neg, Operand::Copy(Place::local(3))),
                )],
                terminator: Terminator::Return,
            },
        ];
        let mut func = function("negation_of_min", locals, blocks, vec![]);
        func.body.return_ty = i32_ty.clone();
        func
    };
    for through_copy in [false, true] {
        let func = body(through_copy);
        let env = merged_interval_environment(&func);
        assert_eq!(
            env.get("y"),
            Interval::constant(min),
            "through_copy={through_copy}: `y` is MIN where the check reads it"
        );
        // The interval lane must not be what answers the check: nothing is discharged
        // at generation, and the negation obligation goes to the solver.
        let (solver, discharged) = crate::generate_vcs_with_discharge(&func);
        assert!(
            !solver.is_empty() || !discharged.is_empty(),
            "ANTI-VACUITY through_copy={through_copy}: the check generated no obligation"
        );
        assert!(
            !discharged.iter().any(|(vc, _)| matches!(
                &vc.kind,
                VcKind::UnsupportedMir { kind, .. } if kind == "MalformedTrustIr"
            )),
            "ANTI-VACUITY through_copy={through_copy}: the hand-written body is malformed"
        );
        for (vc, result) in &discharged {
            assert!(
                !matches!(result, VerificationResult::Proved { .. }),
                "through_copy={through_copy}: {:?} was discharged at generation: {:?}",
                vc.kind,
                vc.formula
            );
        }
        assert!(
            solver.iter().any(|vc| matches!(vc.kind, VcKind::NegationOverflow { .. })),
            "through_copy={through_copy}: the negation obligation was not dispatched: {:?}",
            solver.iter().map(|vc| &vc.kind).collect::<Vec<_>>()
        );
    }
}

/// An EMPTY interval is not evidence. It is the fixpoint's spelling of "no value on
/// this edge", and `contains(v)` is false of it for every `v`, so the division,
/// remainder and negation discharges read it as "excludes the bad value", and the
/// bounds discharge's two comparisons hold of its `lo > hi` for any positive length.
/// (The shift, cast and overflow discharges and the generic comparison already refused
/// it.) Each kind below is discharged from a real interval that excludes the bad
/// value, and from an empty one it is not.
#[test]
fn an_empty_interval_discharges_nothing() {
    let vc = |kind: VcKind, formula: Formula| VerificationCondition {
        kind,
        function: "f".into(),
        location: SourceSpan::default(),
        formula,
        contract_metadata: None,
        obligation: None,
    };
    let var = |name: &str| Box::new(Formula::Var(name.to_string(), Sort::Int));
    let env_with = |d: Interval| {
        let mut env = IntervalDomain::top();
        env.set("d".to_string(), d);
        env.set("len".to_string(), Interval::constant(3));
        env
    };
    let is_zero = || Formula::Eq(var("d"), Box::new(Formula::Int(0)));
    let cases: Vec<(&str, VcKind, Formula)> = vec![
        ("division", VcKind::DivisionByZero, is_zero()),
        ("remainder", VcKind::RemainderByZero, is_zero()),
        ("float division", VcKind::FloatDivisionByZero, is_zero()),
        (
            "negation",
            VcKind::NegationOverflow { ty: Ty::Int { width: 32, signed: true } },
            Formula::Eq(var("d"), Box::new(Formula::Int(i128::from(i32::MIN)))),
        ),
        ("bounds", VcKind::IndexOutOfBounds, Formula::Ge(var("d"), var("len"))),
    ];
    for (what, kind, formula) in cases {
        let real = env_with(Interval::constant(1));
        assert!(
            try_discharge_vc(&vc(kind.clone(), formula.clone()), &real).is_discharged(),
            "ANTI-VACUITY {what}: `d == 1` excludes the bad value and must discharge"
        );
        let empty = env_with(Interval::BOTTOM);
        assert!(
            !try_discharge_vc(&vc(kind, formula), &empty).is_discharged(),
            "{what}: discharged from an EMPTY interval"
        );
    }
}
