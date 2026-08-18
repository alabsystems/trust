// BMC reduction refutation — unit tests.
//
// Two kinds of test here, and both are soundness tests:
//
//  * POSITIVE: the two falsification `mutant/` fixtures' MIR shapes must produce
//    a candidate whose violation formula the in-process ay backend answers SAT
//    WITH A MODEL. That model is the counterexample, so these tests are what
//    substantiates "witness-backed" — not the recognizer returning `Some`.
//  * NEGATIVE: every gate is DROP-ONLY, so each negative test pins a way a FALSE
//    refutation could be minted (a const array instead of a free input, a body
//    with a user branch, a reset accumulator, a wrapping cast, a second add,
//    an over-cap trip count) and asserts no candidate is produced.
//
// The SAFE twin (`[u8; 16]` summed into a `u16` with `<< 4`, which genuinely
// cannot overflow) must be UNSAT — and UNSAT is DROPPED by the consumer, so the
// test asserts the backend does not return `Failed`, which is the property the
// refutation lane actually depends on.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{
    AssertMessage, BasicBlock, BinOp, BlockId, ConstValue, Contract, ContractKind, Formula,
    LocalDecl, Operand, Place, Projection, Rvalue, Sort, SourceSpan, Statement, Terminator, Ty,
    UnwindEdge, VcKind, VerifiableBody, VerifiableFunction,
};

use super::{BMC_MAX_UNROLL, generate_bounded_reduction_bmc_refutation_candidates, int_range};

const INTO_ITER: &str = "<&[u8; 64] as core::iter::traits::collect::IntoIterator>::into_iter";
const NEXT: &str = "<core::slice::Iter<u8> as core::iter::traits::iterator::Iterator>::next";

fn assign(place: Place, rvalue: Rvalue) -> Statement {
    Statement::Assign { place, rvalue, span: SourceSpan::default() }
}

/// The `t += ..` statement's span.
fn add_span() -> SourceSpan {
    SourceSpan {
        file: "reduction.rs".into(),
        line_start: 4,
        col_start: 9,
        line_end: 4,
        col_end: 25,
    }
}

fn deref(local: usize) -> Place {
    Place { local, projections: vec![Projection::Deref] }
}

fn field(local: usize, index: usize) -> Place {
    Place { local, projections: vec![Projection::Field(index)] }
}

fn some_payload(local: usize) -> Place {
    Place { local, projections: vec![Projection::Downcast(1), Projection::Field(0)] }
}

/// Iterator/reference locals whose type this module never inspects.
fn opaque_ty() -> Ty {
    Ty::Unit
}

/// How the addend is computed from the loop element.
#[derive(Clone, Copy)]
enum Addend {
    /// `t += x` (no cast at all).
    Direct,
    /// `t += x as ACC`.
    Cast,
    /// `t += (x as ACC) << k`.
    ShlAfterCast(i128),
}

/// How the iterator's `Option` `SwitchInt` is spelled. The default is the
/// simplified two-way shape; the rest exist because rustc's REAL for-each
/// desugar closes the switch with an `otherwise -> Unreachable` arm, and the
/// certificate that makes that arm dead must be trusted only under its own
/// conditions (see `bmc_terminator_succs`).
#[derive(Clone, Copy, PartialEq, Eq)]
enum OptionSwitch {
    /// `1 -> body`, `otherwise -> return`. No `Unreachable` block anywhere.
    NoneIsOtherwise,
    /// What rustc ACTUALLY emits: `0 -> return`, `1 -> body`,
    /// `otherwise -> bb6`, `bb6: Unreachable`, with rustc's exhaustiveness
    /// certificate set. The dead edge is pruned, so this must be RECOGNIZED.
    ExhaustiveUnreachable,
    /// Same CFG, certificate NOT set — a partial match closed with
    /// `unreachable_unchecked()`. The `Unreachable` is genuinely reachable UB
    /// and MUST keep being refused.
    UncertifiedUnreachable,
    /// Certificate set, but the `otherwise` block does NOT end in `Unreachable`
    /// — the local belt re-check must refuse to prune.
    CertificateWithoutUnreachable,
    /// Certificate set and `otherwise -> bb6: Unreachable`, but `bb6` is ALSO a
    /// live case target, so it is genuinely reached and must not be pruned.
    UnreachableAlsoACaseTarget,
}

struct ReductionSpec {
    elem_ty: Ty,
    acc_ty: Ty,
    len: u64,
    addend: Addend,
    /// `true` iterates a function PARAMETER; `false` iterates a body-local array
    /// (which must be refused — its elements are not free).
    array_is_param: bool,
    /// Inject a user `if`/`break` into the loop body (must be refused).
    extra_branch: bool,
    /// Re-initialize the accumulator INSIDE the loop (must be refused).
    init_inside_loop: bool,
    /// Add a second `CheckedAdd` (must be refused).
    second_add: bool,
    /// Add an unmodelled call into the loop body (must be refused).
    foreign_call: bool,
    /// How the `Option` switch and its dead arm are spelled.
    option_switch: OptionSwitch,
}

impl ReductionSpec {
    fn new(elem_ty: Ty, acc_ty: Ty, len: u64, addend: Addend) -> Self {
        Self {
            elem_ty,
            acc_ty,
            len,
            addend,
            array_is_param: true,
            extra_branch: false,
            init_inside_loop: false,
            second_add: false,
            foreign_call: false,
            option_switch: OptionSwitch::NoneIsOtherwise,
        }
    }
}

/// Build the MIR of
/// `fn f(a: &[ELEM; LEN]) -> ACC { let mut t: ACC = 0; for &x in a { t += <addend>; } t }`
/// in the shape rustc's for-each desugar produces.
///
/// Locals: 0 `_0` return, 1 `_1` the array parameter, 2 `_2` accumulator,
/// 3 `_3 = &(*_1)`, 4 `_4` iterator, 5 `_5` `next()` result, 6 `_6` discriminant,
/// 7 `_7` `&mut _4`, 8 `_8` Some payload, 9 `_9` element `x`, 10 `_10` cast,
/// 11 `_11` shifted, 12 `_12` the checked-add tuple, 13 `_13` a branch temp,
/// 14 `_14` the second-add tuple, 15 `_15` a local array (non-param variant).
fn reduction_fn(spec: &ReductionSpec) -> VerifiableFunction {
    let array_ty = Ty::Array { elem: Box::new(spec.elem_ty.clone()), len: spec.len };
    let locals = vec![
        LocalDecl { index: 0, ty: spec.acc_ty.clone(), name: Some("_0".into()) },
        LocalDecl {
            index: 1,
            ty: Ty::Ref { inner: Box::new(array_ty.clone()), mutable: false },
            name: Some("a".into()),
        },
        LocalDecl { index: 2, ty: spec.acc_ty.clone(), name: Some("t".into()) },
        LocalDecl {
            index: 3,
            ty: Ty::Ref { inner: Box::new(array_ty.clone()), mutable: false },
            name: None,
        },
        LocalDecl { index: 4, ty: opaque_ty(), name: None },
        LocalDecl { index: 5, ty: opaque_ty(), name: None },
        LocalDecl { index: 6, ty: Ty::Int { width: 64, signed: true }, name: None },
        LocalDecl { index: 7, ty: opaque_ty(), name: None },
        LocalDecl { index: 8, ty: opaque_ty(), name: None },
        LocalDecl { index: 9, ty: spec.elem_ty.clone(), name: Some("x".into()) },
        LocalDecl { index: 10, ty: spec.acc_ty.clone(), name: None },
        LocalDecl { index: 11, ty: spec.acc_ty.clone(), name: None },
        LocalDecl { index: 12, ty: Ty::Unit, name: None },
        LocalDecl { index: 13, ty: Ty::Bool, name: None },
        LocalDecl { index: 14, ty: Ty::Unit, name: None },
        LocalDecl { index: 15, ty: array_ty.clone(), name: None },
    ];

    // bb0 — init + iterator construction.
    let mut bb0_stmts =
        vec![assign(Place::local(2), Rvalue::Use(Operand::Constant(ConstValue::Int(0))))];
    let iter_source = if spec.array_is_param {
        bb0_stmts.push(assign(Place::local(3), Rvalue::Ref { mutable: false, place: deref(1) }));
        Operand::Move(Place::local(3))
    } else {
        // A body-LOCAL array: its elements are not free inputs.
        bb0_stmts.push(assign(
            Place::local(15),
            Rvalue::Repeat(
                Operand::Constant(ConstValue::Int(1)),
                usize::try_from(spec.len).expect("test array length fits usize"),
            ),
        ));
        Operand::Move(Place::local(15))
    };

    // bb3 — the loop body.
    let mut body_stmts = vec![
        assign(Place::local(8), Rvalue::Use(Operand::Copy(some_payload(5)))),
        assign(Place::local(9), Rvalue::Use(Operand::Copy(deref(8)))),
    ];
    let addend = match spec.addend {
        Addend::Direct => Operand::Copy(Place::local(9)),
        Addend::Cast => {
            body_stmts.push(assign(
                Place::local(10),
                Rvalue::Cast(Operand::Copy(Place::local(9)), spec.acc_ty.clone()),
            ));
            Operand::Copy(Place::local(10))
        }
        Addend::ShlAfterCast(k) => {
            body_stmts.push(assign(
                Place::local(10),
                Rvalue::Cast(Operand::Copy(Place::local(9)), spec.acc_ty.clone()),
            ));
            body_stmts.push(assign(
                Place::local(11),
                Rvalue::BinaryOp(
                    BinOp::Shl,
                    Operand::Copy(Place::local(10)),
                    Operand::Constant(ConstValue::Int(k)),
                ),
            ));
            Operand::Copy(Place::local(11))
        }
    };
    if spec.second_add {
        body_stmts.push(assign(
            Place::local(14),
            Rvalue::CheckedBinaryOp(
                BinOp::Add,
                Operand::Copy(Place::local(2)),
                Operand::Constant(ConstValue::Int(1)),
            ),
        ));
    }
    // The add carries a distinctive span so the refuted row is checked to point
    // at the statement, not at the function.
    body_stmts.push(Statement::Assign {
        place: Place::local(12),
        rvalue: Rvalue::CheckedBinaryOp(BinOp::Add, Operand::Copy(Place::local(2)), addend),
        span: add_span(),
    });

    // bb4 — write back and loop.
    let mut bb4_stmts = vec![assign(Place::local(2), Rvalue::Use(Operand::Copy(field(12, 0))))];
    if spec.init_inside_loop {
        bb4_stmts.push(assign(Place::local(2), Rvalue::Use(Operand::Constant(ConstValue::Int(0)))));
    }

    let mut blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: bb0_stmts,
            terminator: Terminator::Call {
                func: INTO_ITER.to_string(),
                args: vec![iter_source],
                dest: Place::local(4),
                target: Some(BlockId(1)),
                span: SourceSpan::default(),
                atomic: None,
                is_foreign: false,
                is_unsafe_sig: false,
                unwind: UnwindEdge::Unreachable,
            },
        },
        BasicBlock {
            id: BlockId(1),
            stmts: vec![assign(
                Place::local(7),
                Rvalue::Ref { mutable: true, place: Place::local(4) },
            )],
            terminator: Terminator::Call {
                func: NEXT.to_string(),
                args: vec![Operand::Move(Place::local(7))],
                dest: Place::local(5),
                target: Some(BlockId(2)),
                span: SourceSpan::default(),
                atomic: None,
                is_foreign: false,
                is_unsafe_sig: false,
                unwind: UnwindEdge::Unreachable,
            },
        },
        BasicBlock {
            id: BlockId(2),
            stmts: vec![assign(Place::local(6), Rvalue::Discriminant(Place::local(5)))],
            terminator: Terminator::SwitchInt {
                discr: Operand::Move(Place::local(6)),
                targets: vec![(1, BlockId(3))],
                otherwise: BlockId(5),
                exhaustive_enum_unreachable: false,
                span: SourceSpan::default(),
            },
        },
        BasicBlock {
            id: BlockId(3),
            stmts: body_stmts,
            terminator: Terminator::Assert {
                cond: Operand::Copy(field(12, 1)),
                expected: false,
                msg: AssertMessage::Overflow(BinOp::Add),
                target: BlockId(4),
                span: add_span(),
                unwind: UnwindEdge::Unreachable,
            },
        },
        BasicBlock { id: BlockId(4), stmts: bb4_stmts, terminator: Terminator::Goto(BlockId(1)) },
        BasicBlock {
            id: BlockId(5),
            stmts: vec![assign(Place::local(0), Rvalue::Use(Operand::Copy(Place::local(2))))],
            terminator: Terminator::Return,
        },
    ];

    if spec.extra_branch {
        // A user `if x == 0 { .. }` inside the body: bb3 branches on a value this
        // module does not model, so iteration `i` is no longer unconditionally
        // reached.
        blocks[3].stmts.push(assign(
            Place::local(13),
            Rvalue::BinaryOp(
                BinOp::Eq,
                Operand::Copy(Place::local(9)),
                Operand::Constant(ConstValue::Int(0)),
            ),
        ));
        blocks[3].terminator = Terminator::SwitchInt {
            discr: Operand::Move(Place::local(13)),
            targets: vec![(1, BlockId(4))],
            otherwise: BlockId(4),
            exhaustive_enum_unreachable: false,
            span: SourceSpan::default(),
        };
    }
    if spec.foreign_call {
        blocks[4].terminator = Terminator::Call {
            func: "test::side_effect".to_string(),
            args: vec![],
            dest: Place::local(13),
            target: Some(BlockId(1)),
            span: SourceSpan::default(),
            atomic: None,
            is_foreign: false,
            is_unsafe_sig: false,
            unwind: UnwindEdge::Unreachable,
        };
    }
    if spec.option_switch != OptionSwitch::NoneIsOtherwise {
        // Re-spell bb2's switch as the REAL desugar: an explicit `None` arm plus
        // a closing `otherwise` arm into a new bb6.
        let none_arm = if spec.option_switch == OptionSwitch::UnreachableAlsoACaseTarget {
            BlockId(6)
        } else {
            BlockId(5)
        };
        blocks[2].terminator = Terminator::SwitchInt {
            discr: Operand::Move(Place::local(6)),
            targets: vec![(0, none_arm), (1, BlockId(3))],
            otherwise: BlockId(6),
            exhaustive_enum_unreachable: spec.option_switch != OptionSwitch::UncertifiedUnreachable,
            span: SourceSpan::default(),
        };
        let bb6_terminator = if spec.option_switch == OptionSwitch::CertificateWithoutUnreachable {
            // A block the certificate CLAIMS is dead but which is not spelled
            // `Unreachable`: the belt must keep the edge and the allowlist must
            // then reject this call.
            Terminator::Call {
                func: "test::side_effect".to_string(),
                args: vec![],
                dest: Place::local(13),
                target: Some(BlockId(5)),
                span: SourceSpan::default(),
                atomic: None,
                is_foreign: false,
                is_unsafe_sig: false,
                unwind: UnwindEdge::Unreachable,
            }
        } else {
            Terminator::Unreachable
        };
        blocks.push(BasicBlock { id: BlockId(6), stmts: vec![], terminator: bb6_terminator });
    }

    VerifiableFunction {
        name: "f".to_string(),
        def_path: "test::f".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks,
            arg_count: 1,
            return_ty: spec.acc_ty.clone(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn u8_ty() -> Ty {
    Ty::Int { width: 8, signed: false }
}
fn u16_ty() -> Ty {
    Ty::Int { width: 16, signed: false }
}
fn i128_ty() -> Ty {
    Ty::Int { width: 128, signed: true }
}

/// `mutant/shift_reduction_overflow.rs`:
/// `pub fn f(a: &[u8; 64]) -> u8 { let mut t: u8 = 0; for &x in a { t += (x as u8) << 4; } t }`
fn shift_reduction_overflow_fixture() -> VerifiableFunction {
    reduction_fn(&ReductionSpec::new(u8_ty(), u8_ty(), 64, Addend::ShlAfterCast(4)))
}

/// `mutant/i128_shift_accumulator_overflow.rs`:
/// `pub fn f(a: &[i128; 4]) -> i128 { let mut t: i128 = 0; for &x in a { t += x; } t }`
fn i128_accumulator_overflow_fixture() -> VerifiableFunction {
    reduction_fn(&ReductionSpec::new(i128_ty(), i128_ty(), 4, Addend::Direct))
}

/// The SAFE twin `build_accumulator_bound_facts` already proves:
/// `[u8; 16]` shifted by 4 into a `u16` — `16 * (255 << 4) = 65280 <= u16::MAX`.
fn safe_widening_reduction() -> VerifiableFunction {
    reduction_fn(&ReductionSpec::new(u8_ty(), u16_ty(), 16, Addend::ShlAfterCast(4)))
}

// ── recognizer ──────────────────────────────────────────────────────────────

#[test]
fn int_range_refuses_unsigned_128_and_admits_signed_128() {
    // `2^128 - 1` has no `i128` spelling, so the unsigned-128 accumulator is
    // refused rather than encoded against a truncated ceiling.
    assert_eq!(int_range(128, false), None);
    assert_eq!(int_range(128, true), Some((i128::MIN, i128::MAX)));
    assert_eq!(int_range(8, false), Some((0, 255)));
    assert_eq!(int_range(8, true), Some((-128, 127)));
    assert_eq!(int_range(0, false), None);
    assert_eq!(int_range(129, true), None);
}

#[test]
fn shift_fixture_yields_one_overflow_candidate_at_the_add_span() {
    let candidates =
        generate_bounded_reduction_bmc_refutation_candidates(&shift_reduction_overflow_fixture());
    assert_eq!(candidates.len(), 1, "the shift-reduction mutant must yield one candidate");
    assert!(
        matches!(&candidates[0].kind, VcKind::ArithmeticOverflow { op: BinOp::Add, .. }),
        "the refuted obligation must carry the REAL L0 kind, got {:?}",
        candidates[0].kind
    );
    assert_eq!(
        candidates[0].location.line_start, 4,
        "the row must point at the add, not at the function"
    );
}

#[test]
fn i128_fixture_yields_one_overflow_candidate() {
    let candidates =
        generate_bounded_reduction_bmc_refutation_candidates(&i128_accumulator_overflow_fixture());
    assert_eq!(candidates.len(), 1, "the i128 reduction mutant must yield one candidate");
}

#[test]
fn safe_widening_reduction_still_yields_a_candidate_but_it_is_unsat() {
    // The producer is shape-driven, not outcome-driven: it emits a candidate for
    // the safe twin too. Soundness rests on the CONSUMER dropping UNSAT, which
    // `safe_widening_reduction_is_never_refuted` checks against the real backend.
    let candidates =
        generate_bounded_reduction_bmc_refutation_candidates(&safe_widening_reduction());
    assert_eq!(candidates.len(), 1);
}

// ── the drop-only gates (each pins a FALSE-refutation vector) ────────────────

#[test]
fn constant_local_array_is_refused() {
    let mut spec = ReductionSpec::new(u8_ty(), u8_ty(), 64, Addend::ShlAfterCast(4));
    spec.array_is_param = false;
    assert!(
        generate_bounded_reduction_bmc_refutation_candidates(&reduction_fn(&spec)).is_empty(),
        "a body-local array's elements are NOT free inputs; modelling them free \
         would be a false refutation"
    );
}

#[test]
fn user_branch_in_the_loop_body_is_refused() {
    let mut spec = ReductionSpec::new(u8_ty(), u8_ty(), 64, Addend::ShlAfterCast(4));
    spec.extra_branch = true;
    assert!(
        generate_bounded_reduction_bmc_refutation_candidates(&reduction_fn(&spec)).is_empty(),
        "an unmodelled branch can skip the add, so iteration i is not \
         unconditionally reached"
    );
}

#[test]
fn accumulator_reset_inside_the_loop_is_refused() {
    let mut spec = ReductionSpec::new(u8_ty(), u8_ty(), 64, Addend::ShlAfterCast(4));
    spec.init_inside_loop = true;
    assert!(
        generate_bounded_reduction_bmc_refutation_candidates(&reduction_fn(&spec)).is_empty(),
        "a per-iteration reset makes the unrolled running sum wrong"
    );
}

#[test]
fn a_second_checked_add_is_refused() {
    let mut spec = ReductionSpec::new(u8_ty(), u8_ty(), 64, Addend::ShlAfterCast(4));
    spec.second_add = true;
    assert!(
        generate_bounded_reduction_bmc_refutation_candidates(&reduction_fn(&spec)).is_empty(),
        "a second add is another obligation that could panic first"
    );
}

#[test]
fn an_unmodelled_call_in_the_loop_is_refused() {
    let mut spec = ReductionSpec::new(u8_ty(), u8_ty(), 64, Addend::ShlAfterCast(4));
    spec.foreign_call = true;
    assert!(
        generate_bounded_reduction_bmc_refutation_candidates(&reduction_fn(&spec)).is_empty(),
        "an arbitrary call can panic, diverge, or mutate the input"
    );
}

#[test]
fn narrowing_cast_is_refused() {
    // `[u16; 4]` elements cast down into a `u8` accumulator: the cast WRAPS, and
    // the linear encoding has no modular semantics for it.
    let spec = ReductionSpec::new(u16_ty(), u8_ty(), 4, Addend::Cast);
    assert!(generate_bounded_reduction_bmc_refutation_candidates(&reduction_fn(&spec)).is_empty());
}

#[test]
fn signed_accumulator_with_a_shift_is_refused() {
    // The `2^(W-k)` split describes an UNSIGNED bit pattern.
    let spec = ReductionSpec::new(
        u8_ty(),
        Ty::Int { width: 32, signed: true },
        4,
        Addend::ShlAfterCast(4),
    );
    assert!(generate_bounded_reduction_bmc_refutation_candidates(&reduction_fn(&spec)).is_empty());
}

#[test]
fn unsigned_128_accumulator_is_refused() {
    let spec = ReductionSpec::new(u8_ty(), Ty::Int { width: 128, signed: false }, 4, Addend::Cast);
    assert!(generate_bounded_reduction_bmc_refutation_candidates(&reduction_fn(&spec)).is_empty());
}

#[test]
fn trip_count_over_the_cap_is_refused_rather_than_partially_unrolled() {
    let len = u64::try_from(BMC_MAX_UNROLL).expect("cap fits u64") + 1;
    let spec = ReductionSpec::new(u8_ty(), u8_ty(), len, Addend::Cast);
    assert!(
        generate_bounded_reduction_bmc_refutation_candidates(&reduction_fn(&spec)).is_empty(),
        "over the cap the unroll would be PARTIAL; a partial unroll is not built"
    );
}

// ── P2's precondition channel ───────────────────────────────────────────────
//
// `preconditions` is the BODY-HYPOTHESIS channel, not the authored-contract one:
// the extractor extends it with type tautologies, and the `Option`-tag fact is
// present in EVERY real `for &x in <array>` body. The gate therefore refuses the
// AUTHORED channels outright and positively certifies what remains. These tests
// pin both directions.

/// The always-true `Option`-tag fact `enum_discriminant_range_preconditions`
/// mints for this body's discriminant temp (`_6 = Discriminant(_5)`), under the
/// given variable spelling.
fn tag_fact(var: &str, tags: [i128; 2]) -> Formula {
    Formula::Or(
        tags.iter()
            .map(|&t| {
                Formula::Eq(
                    Box::new(Formula::Var(var.into(), Sort::Int)),
                    Box::new(Formula::Int(t)),
                )
            })
            .collect(),
    )
}

/// The `MIN_T <= p <= MAX_T` fact `integer_param_range_preconditions` mints.
fn param_range_fact(var: &str, min: i128, max: i128) -> Formula {
    Formula::And(vec![
        Formula::Ge(Box::new(Formula::Var(var.into(), Sort::Int)), Box::new(Formula::Int(min))),
        Formula::Le(Box::new(Formula::Var(var.into(), Sort::Int)), Box::new(Formula::Int(max))),
    ])
}

#[test]
fn the_synthesized_option_tag_fact_does_not_block_recognition() {
    // The REGRESSION this whole seam exists for: a blanket
    // `!preconditions.is_empty()` refusal was dead on arrival against real MIR,
    // because every for-each body carries this tautology.
    let mut func = shift_reduction_overflow_fixture();
    func.preconditions.push(tag_fact("_6", [0, 1]));
    assert_eq!(
        generate_bounded_reduction_bmc_refutation_candidates(&func).len(),
        1,
        "the extractor's always-true `Option`-tag fact constrains no input and must \
         not suppress the candidate"
    );
}

#[test]
fn an_authored_contract_row_is_refused() {
    let mut func = shift_reduction_overflow_fixture();
    func.preconditions.push(tag_fact("_6", [0, 1]));
    func.contracts.push(Contract {
        kind: ContractKind::Requires,
        body: "a[0] == 0".to_string(),
        span: SourceSpan::default(),
    });
    assert!(
        generate_bounded_reduction_bmc_refutation_candidates(&func).is_empty(),
        "a `#[requires]` could constrain the input array, breaking the free-element premise"
    );
}

#[test]
fn an_authored_spec_requires_is_refused() {
    // The channel an UNPARSEABLE `#[requires]` lands in: no usable formula
    // reaches `preconditions`, but the declared caller obligation is real.
    let mut func = shift_reduction_overflow_fixture();
    func.preconditions.push(tag_fact("_6", [0, 1]));
    func.spec.requires.push("a[0] == 0".to_string());
    assert!(
        generate_bounded_reduction_bmc_refutation_candidates(&func).is_empty(),
        "a declared-but-unlowered `#[requires]` must still refuse the lane"
    );
}

#[test]
fn a_trait_impl_method_is_refused_because_an_inherited_contract_is_invisible() {
    // MEASURED on the real HEAD-matching stage2 trustc (`-Ztrust-dump=mir:`): a
    // `#[trust::requires]` DECLARED ON A TRAIT METHOD and inherited by an impl
    // appears in NONE of the three channels on the impl's `VerifiableFunction` —
    //   def_path "<tr::S as tr::R>::f", contracts [], spec.requires [],
    //   preconditions [ Or(Eq(_8,0), Eq(_8,1)) ]   (the Option tag fact ONLY)
    // — while Trust still ENFORCES that contract at call sites. So a witness
    // violating it is not a reachable execution, and a `Failed` row naming it
    // would be a FALSE REFUTATION. The contract cannot be seen, so the SHAPE is
    // refused. Refusal-only: a false positive costs completeness, never soundness.
    let mut func = shift_reduction_overflow_fixture();
    func.preconditions.push(tag_fact("_6", [0, 1]));
    func.def_path = "<tr::S as tr::R>::f".to_string();
    assert!(
        generate_bounded_reduction_bmc_refutation_candidates(&func).is_empty(),
        "a trait-impl method may carry an INVISIBLE inherited `#[requires]`; refuse the shape"
    );

    // The control: the same body as a free function is still admitted, so the gate
    // costs the two real fixtures nothing (measured def_path
    // `shift_reduction_overflow::f`).
    let mut plain = shift_reduction_overflow_fixture();
    plain.preconditions.push(tag_fact("_6", [0, 1]));
    assert_eq!(
        generate_bounded_reduction_bmc_refutation_candidates(&plain).len(),
        1,
        "a free function keeps the candidate"
    );
}

#[test]
fn an_uncertifiable_precondition_is_refused() {
    let mut func = shift_reduction_overflow_fixture();
    func.preconditions.push(Formula::Bool(true));
    assert!(
        generate_bounded_reduction_bmc_refutation_candidates(&func).is_empty(),
        "a body hypothesis this module cannot certify as a type tautology must DECLINE, \
         not be waved through"
    );
}

#[test]
fn a_tag_fact_about_a_local_that_is_not_the_next_result_is_refused() {
    // Same `v == 0 ∨ v == 1` shape, but about the loop ELEMENT rather than the
    // `next()` discriminant temp: that is a genuine constraint on the input.
    let mut func = shift_reduction_overflow_fixture();
    func.preconditions.push(tag_fact("x", [0, 1]));
    assert!(
        generate_bounded_reduction_bmc_refutation_candidates(&func).is_empty(),
        "a tag-shaped fact about a non-discriminant local constrains the input"
    );
}

#[test]
fn a_tag_fact_with_tags_other_than_the_option_pair_is_refused() {
    // `_6 ∈ {0, 2}` is NOT the `Option` tag set; the tautology argument (and with
    // it P2) does not carry, and this crate cannot consult the enum's real tags.
    let mut func = shift_reduction_overflow_fixture();
    func.preconditions.push(tag_fact("_6", [0, 2]));
    assert!(generate_bounded_reduction_bmc_refutation_candidates(&func).is_empty());
}

#[test]
fn an_integer_parameter_type_range_is_certified_but_a_narrower_range_is_refused() {
    // With `arg_count = 2` the accumulator local `t: u8` is also a parameter, so
    // the extractor would mint `0 <= t <= 255` for it. That is a tautology of
    // `t`'s OWN type and must not suppress the candidate; a NARROWER range is a
    // real constraint and must refuse.
    let mut certified = shift_reduction_overflow_fixture();
    certified.body.arg_count = 2;
    certified.preconditions.push(tag_fact("_6", [0, 1]));
    certified.preconditions.push(param_range_fact("t", 0, 255));
    assert_eq!(
        generate_bounded_reduction_bmc_refutation_candidates(&certified).len(),
        1,
        "`0 <= t <= 255` is exactly `u8`'s range — a tautology, so it constrains nothing"
    );

    let mut narrowed = shift_reduction_overflow_fixture();
    narrowed.body.arg_count = 2;
    narrowed.preconditions.push(tag_fact("_6", [0, 1]));
    narrowed.preconditions.push(param_range_fact("t", 0, 3));
    assert!(
        generate_bounded_reduction_bmc_refutation_candidates(&narrowed).is_empty(),
        "`0 <= t <= 3` is NOT `u8`'s range; it is a genuine input constraint"
    );
}

// ── the exhaustive-enum dead arm (rustc's real for-each desugar) ─────────────

#[test]
fn the_real_desugar_with_a_certified_dead_unreachable_is_recognized() {
    // The second seam: rustc closes the `Option` switch with
    // `otherwise -> bb6: Unreachable` and stamps its own exhaustiveness
    // certificate. That edge is statically dead, so it must not be walked into
    // the terminator allowlist.
    let mut spec = ReductionSpec::new(u8_ty(), u8_ty(), 64, Addend::ShlAfterCast(4));
    spec.option_switch = OptionSwitch::ExhaustiveUnreachable;
    let mut func = reduction_fn(&spec);
    func.preconditions.push(tag_fact("_6", [0, 1]));
    let candidates = generate_bounded_reduction_bmc_refutation_candidates(&func);
    assert_eq!(candidates.len(), 1, "the real desugar shape must be recognized");
    match solve(&candidates[0]) {
        trust_types::VerificationResult::Failed { counterexample: Some(cex), .. } => {
            assert!(!cex.assignments.is_empty(), "the refutation must carry a witness");
        }
        other => panic!("expected SAT with a model, got {other:?}"),
    }
}

#[test]
fn a_certificate_over_a_non_option_tag_set_is_refused() {
    // The certificate ALONE must not license pruning.
    // `mark_exhaustive_enum_unreachable_switches` has TWO lanes, and the COROUTINE
    // lane sets `exhaustive_enum_unreachable = true` with NO tag-set equality check
    // (computing the tag set needs the coroutine layout query, which cycles inside
    // that MIR pass — E0391; the extractor says so itself). Case-set exhaustiveness
    // is therefore exactly what the flag may not carry, and exactly what makes
    // pruning the `otherwise` edge safe. So this module re-derives it locally:
    // only the literal `Option` tag set {0, 1} is pruned.
    //
    // Here the certificate is set and `otherwise` really is `Unreachable`, but the
    // cases are {0, 2} — a gap at 1. The edge must be KEPT, and the terminator
    // allowlist must then refuse the function.
    let mut spec = ReductionSpec::new(u8_ty(), u8_ty(), 64, Addend::ShlAfterCast(4));
    spec.option_switch = OptionSwitch::ExhaustiveUnreachable;
    let mut func = reduction_fn(&spec);
    func.preconditions.push(tag_fact("_6", [0, 1]));
    for block in &mut func.body.blocks {
        if let Terminator::SwitchInt { targets, .. } = &mut block.terminator
            && targets.len() == 2
            && targets[0].0 == 0
            && targets[1].0 == 1
        {
            targets[1].0 = 2;
        }
    }
    assert!(
        generate_bounded_reduction_bmc_refutation_candidates(&func).is_empty(),
        "a certificate over a NON-exhaustive case set must not license pruning the \
         `otherwise` edge — the coroutine lane can stamp it without checking"
    );
}

#[test]
fn an_uncertified_reachable_unreachable_is_refused() {
    // A partial match closed with `unreachable_unchecked()`: the `Unreachable`
    // is GENUINELY reachable UB, so P3 fails and the lane must decline.
    let mut spec = ReductionSpec::new(u8_ty(), u8_ty(), 64, Addend::ShlAfterCast(4));
    spec.option_switch = OptionSwitch::UncertifiedUnreachable;
    let mut func = reduction_fn(&spec);
    func.preconditions.push(tag_fact("_6", [0, 1]));
    assert!(
        generate_bounded_reduction_bmc_refutation_candidates(&func).is_empty(),
        "without rustc's exhaustiveness certificate the dead arm is not dead"
    );
}

#[test]
fn a_certificate_whose_otherwise_block_is_not_unreachable_is_refused() {
    // The local belt: the certificate is taken only when the `otherwise` block
    // really ends in `Terminator::Unreachable`.
    let mut spec = ReductionSpec::new(u8_ty(), u8_ty(), 64, Addend::ShlAfterCast(4));
    spec.option_switch = OptionSwitch::CertificateWithoutUnreachable;
    let mut func = reduction_fn(&spec);
    func.preconditions.push(tag_fact("_6", [0, 1]));
    assert!(
        generate_bounded_reduction_bmc_refutation_candidates(&func).is_empty(),
        "the certificate is re-checked locally, not taken on trust"
    );
}

#[test]
fn an_unreachable_block_that_is_also_a_live_case_target_is_refused() {
    // Pruning the `otherwise` edge must not un-reach a block a LIVE case arm
    // still targets.
    let mut spec = ReductionSpec::new(u8_ty(), u8_ty(), 64, Addend::ShlAfterCast(4));
    spec.option_switch = OptionSwitch::UnreachableAlsoACaseTarget;
    let mut func = reduction_fn(&spec);
    func.preconditions.push(tag_fact("_6", [0, 1]));
    assert!(
        generate_bounded_reduction_bmc_refutation_candidates(&func).is_empty(),
        "a case arm reaches that block, so its `Unreachable` is live UB"
    );
}

#[test]
fn mismatched_array_length_and_trip_count_is_refused() {
    // The trip count comes from the iterated array, so a body whose element trace
    // reaches a DIFFERENT array must not be unrolled against this one. Simulate
    // by making the element read come from an untraceable place.
    let mut func = shift_reduction_overflow_fixture();
    // Break `x = *payload` into a plain copy of the (opaque) payload local, so
    // `for_each_array_source` can no longer prove `x` is an array element.
    func.body.blocks[3].stmts[1] =
        assign(Place::local(9), Rvalue::Use(Operand::Copy(Place::local(8))));
    assert!(generate_bounded_reduction_bmc_refutation_candidates(&func).is_empty());
}

// ── the witness (the point of the whole lane) ───────────────────────────────

/// Solve a candidate with the deterministic in-process ay backend.
fn solve(vc: &trust_types::VerificationCondition) -> trust_types::VerificationResult {
    use trust_router::VerificationBackend;
    let backend = trust_router::InProcessAyBackend::new();
    assert!(backend.can_handle(vc), "ArithmeticOverflow is in the ay backend's can_handle set");
    backend.verify(vc)
}

#[test]
fn shift_fixture_violation_is_sat_with_a_concrete_model() {
    let candidates =
        generate_bounded_reduction_bmc_refutation_candidates(&shift_reduction_overflow_fixture());
    let result = solve(&candidates[0]);
    match result {
        trust_types::VerificationResult::Failed { counterexample: Some(cex), .. } => {
            assert!(
                !cex.assignments.is_empty(),
                "a refutation must carry a CONCRETE witness, not an empty model"
            );
        }
        other => panic!(
            "`t: u8 += (x as u8) << 4` over [u8; 64] genuinely overflows; the unrolled \
             violation must be SAT with a model, got {other:?}"
        ),
    }
}

#[test]
fn i128_fixture_violation_is_sat_with_a_concrete_model() {
    let candidates =
        generate_bounded_reduction_bmc_refutation_candidates(&i128_accumulator_overflow_fixture());
    let result = solve(&candidates[0]);
    match result {
        trust_types::VerificationResult::Failed { counterexample: Some(cex), .. } => {
            assert!(!cex.assignments.is_empty(), "the i128 refutation must carry a witness");
        }
        other => panic!(
            "summing four i128 elements genuinely overflows; the unrolled violation must \
             be SAT with a model, got {other:?}"
        ),
    }
}

#[test]
fn safe_widening_reduction_is_never_refuted() {
    // The SOUNDNESS direction: a reduction that provably cannot overflow must not
    // produce a `Failed` verdict. (`Proved` or a fail-closed `Unknown` are both
    // fine — the consumer drops everything but `Failed`-with-model.)
    let candidates =
        generate_bounded_reduction_bmc_refutation_candidates(&safe_widening_reduction());
    let result = solve(&candidates[0]);
    assert!(
        !matches!(result, trust_types::VerificationResult::Failed { .. }),
        "16 * (255 << 4) = 65280 <= u16::MAX, so the violation is UNSAT; got {result:?}"
    );
}

// ── the alternative shift spelling (a CHECKED `Shl` with its own assert) ─────

/// `(x as u8) << 4` extracted as a CHECKED `Shl` tuple guarded by its own
/// `assert(!flag)` in a separate block — the spelling `reduction_shl_operands`
/// also accepts. The shift-amount assert is provably clear (`4 < 8`), so it
/// cannot cut the unrolled prefix short and the reduction stays refutable.
fn checked_shift_fixture() -> VerifiableFunction {
    let mut f = shift_reduction_overflow_fixture();
    f.body.blocks[3].stmts = vec![
        assign(Place::local(8), Rvalue::Use(Operand::Copy(some_payload(5)))),
        assign(Place::local(9), Rvalue::Use(Operand::Copy(deref(8)))),
        assign(Place::local(10), Rvalue::Cast(Operand::Copy(Place::local(9)), u8_ty())),
        assign(
            Place::local(14),
            Rvalue::CheckedBinaryOp(
                BinOp::Shl,
                Operand::Copy(Place::local(10)),
                Operand::Constant(ConstValue::Int(4)),
            ),
        ),
    ];
    f.body.blocks[3].terminator = Terminator::Assert {
        cond: Operand::Copy(field(14, 1)),
        expected: false,
        msg: AssertMessage::Overflow(BinOp::Shl),
        target: BlockId(6),
        span: SourceSpan::default(),
        unwind: UnwindEdge::Unreachable,
    };
    f.body.blocks.push(BasicBlock {
        id: BlockId(6),
        stmts: vec![
            assign(Place::local(11), Rvalue::Use(Operand::Copy(field(14, 0)))),
            Statement::Assign {
                place: Place::local(12),
                rvalue: Rvalue::CheckedBinaryOp(
                    BinOp::Add,
                    Operand::Copy(Place::local(2)),
                    Operand::Copy(Place::local(11)),
                ),
                span: add_span(),
            },
        ],
        terminator: Terminator::Assert {
            cond: Operand::Copy(field(12, 1)),
            expected: false,
            msg: AssertMessage::Overflow(BinOp::Add),
            target: BlockId(4),
            span: add_span(),
            unwind: UnwindEdge::Unreachable,
        },
    });
    f
}

#[test]
fn checked_shift_spelling_is_recognized_and_refuted_with_a_witness() {
    let candidates = generate_bounded_reduction_bmc_refutation_candidates(&checked_shift_fixture());
    assert_eq!(candidates.len(), 1, "the checked-`Shl` spelling must also be recognized");
    match solve(&candidates[0]) {
        trust_types::VerificationResult::Failed { counterexample: Some(cex), .. } => {
            assert!(!cex.assignments.is_empty());
        }
        other => panic!("expected SAT with a model, got {other:?}"),
    }
}

#[test]
fn an_unfoldable_assert_in_the_loop_is_refused() {
    // Same body, but the shift assert's condition is an opaque local: it CAN
    // fire, so iteration i is no longer unconditionally reached.
    let mut f = checked_shift_fixture();
    f.body.blocks[3].terminator = Terminator::Assert {
        cond: Operand::Copy(Place::local(13)),
        expected: true,
        msg: AssertMessage::Overflow(BinOp::Shl),
        target: BlockId(6),
        span: SourceSpan::default(),
        unwind: UnwindEdge::Unreachable,
    };
    assert!(
        generate_bounded_reduction_bmc_refutation_candidates(&f).is_empty(),
        "an assert that can fire must decline the whole unroll"
    );
}
