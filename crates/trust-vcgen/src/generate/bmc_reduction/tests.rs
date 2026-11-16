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
    AdtKind, AssertMessage, BasicBlock, BinOp, BlockId, ConstValue, Contract, ContractKind,
    Formula, LocalDecl, Operand, Place, Projection, Rvalue, Sort, SourceSpan, Statement,
    Terminator, Ty, UnwindEdge, VariantDef, VcKind, VerifiableBody, VerifiableFunction,
};

use super::{
    BMC_MAX_UNROLL, generate_bounded_reduction_bmc_refutation_candidates, int_range,
    is_integer_param_range_fact,
};

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

/// Spell the fixture's small integer literals with the exact Rust integer type
/// that supplies their MIR context. In particular, `ConstValue::Int` is signed
/// and carries no width, while an unsigned literal retains both facts in
/// `ConstValue::Uint`.
fn integer_const(ty: &Ty, value: i128) -> ConstValue {
    match ty {
        Ty::Int { signed: true, .. } => ConstValue::Int(value),
        Ty::Int { width, signed: false } => ConstValue::Uint(
            u128::try_from(value).expect("test fixture unsigned literal is nonnegative"),
            *width,
        ),
        other => panic!("test fixture expected an integer type, got {other:?}"),
    }
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
/// simplified two-way shape; the rest exercise rustc's real for-each shape and
/// adversarial variants of its public, caller-constructible exhaustiveness bit.
/// That bit never grants this refutation lane authority to prune a successor.
#[derive(Clone, Copy, PartialEq, Eq)]
enum OptionSwitch {
    /// `1 -> body`, `otherwise -> return`. No `Unreachable` block anywhere.
    NoneIsOtherwise,
    /// What rustc ACTUALLY emits: `0 -> return`, `1 -> body`,
    /// `otherwise -> bb6`, `bb6: Unreachable`, with the public exhaustiveness
    /// bit set. Without provenance-bound layout evidence this must be REFUSED.
    ExhaustiveUnreachable,
    /// Same CFG, certificate NOT set — a partial match closed with
    /// `unreachable_unchecked()`. The `Unreachable` is genuinely reachable UB
    /// and MUST keep being refused.
    UncertifiedUnreachable,
    /// Exhaustiveness bit set, but the `otherwise` block does NOT end in
    /// `Unreachable`; the successor remains live and must be refused.
    CertificateWithoutUnreachable,
    /// Exhaustiveness bit set and `otherwise -> bb6: Unreachable`, but `bb6` is
    /// ALSO a live case target, so it is genuinely reached and must be refused.
    UnreachableAlsoACaseTarget,
    /// Same CFG as `ExhaustiveUnreachable` but the switch cases are `{0, 1}` while
    /// the scrutinee's declared enum has THREE variants — the real
    /// `unreachable_unchecked()`-shaped partial match. The `otherwise` arm IS
    /// reachable (at discriminant 2) and must keep being refused even though the
    /// scrutinee now carries genuine datatype evidence.
    PartialMatchOverAThreeVariantEnum,
}

/// The DECLARED type of local `_5` (the `next()` result), which is the evidence
/// `bmc_terminator_succs` reads to decide whether a switch's `otherwise` edge is
/// dead. Nothing else in this module inspects it.
#[derive(Clone, Copy, PartialEq, Eq)]
enum ScrutineeTy {
    /// The historical spelling: no datatype evidence at all. A `Discriminant`
    /// read of it says nothing about the value set, so no edge may be pruned.
    Opaque,
    /// A real `Option`-shaped `enum` ADT: variants `None = 0`, `Some = 1`.
    OptionEnum,
    /// The same variant list spelled as a `struct`. A `Discriminant` read of a
    /// struct is not a sum tag, so this must prune nothing.
    OptionShapedStruct,
    /// A real three-variant `enum` (`A = 0`, `B = 1`, `C = 2`).
    ThreeVariantEnum,
}

fn option_variants() -> Vec<VariantDef> {
    vec![
        VariantDef { name: "None".into(), discriminant: 0, fields: vec![] },
        VariantDef { name: "Some".into(), discriminant: 1, fields: vec![] },
    ]
}

fn three_variants() -> Vec<VariantDef> {
    vec![
        VariantDef { name: "A".into(), discriminant: 0, fields: vec![] },
        VariantDef { name: "B".into(), discriminant: 1, fields: vec![] },
        VariantDef { name: "C".into(), discriminant: 2, fields: vec![] },
    ]
}

fn adt(name: &str, variants: Vec<VariantDef>, kind: AdtKind) -> Ty {
    Ty::Adt {
        name: name.into(),
        fields: vec![].into(),
        variants: variants.into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        layout: None,
        enum_layout: None,
        adt_kind: Some(kind),
        // Added upstream during the 1377-commit merge. `None` = no
        // arbitrary-precision authority claimed, which is what these
        // fixtures' ordinary fixed-width enums are; every other test
        // constructor in the crate spells it the same way.
        arbitrary_precision: None,
        validity_wrapper: None,
    }
}

fn scrutinee_ty(kind: ScrutineeTy) -> Ty {
    match kind {
        ScrutineeTy::Opaque => opaque_ty(),
        ScrutineeTy::OptionEnum => adt("core::option::Option", option_variants(), AdtKind::Enum),
        ScrutineeTy::OptionShapedStruct => {
            adt("core::option::Option", option_variants(), AdtKind::Struct)
        }
        ScrutineeTy::ThreeVariantEnum => adt("test::E3", three_variants(), AdtKind::Enum),
    }
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
    /// The declared type of the switched-on `next()` result.
    scrutinee: ScrutineeTy,
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
            scrutinee: ScrutineeTy::Opaque,
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
        LocalDecl { index: 5, ty: scrutinee_ty(spec.scrutinee), name: None },
        LocalDecl { index: 6, ty: Ty::Int { width: 64, signed: true }, name: None },
        LocalDecl { index: 7, ty: opaque_ty(), name: None },
        LocalDecl { index: 8, ty: opaque_ty(), name: None },
        LocalDecl { index: 9, ty: spec.elem_ty.clone(), name: Some("x".into()) },
        LocalDecl { index: 10, ty: spec.acc_ty.clone(), name: None },
        LocalDecl { index: 11, ty: spec.acc_ty.clone(), name: None },
        LocalDecl { index: 12, ty: Ty::Tuple(vec![spec.acc_ty.clone(), Ty::Bool]), name: None },
        LocalDecl { index: 13, ty: Ty::Bool, name: None },
        LocalDecl { index: 14, ty: Ty::Tuple(vec![spec.acc_ty.clone(), Ty::Bool]), name: None },
        LocalDecl { index: 15, ty: array_ty.clone(), name: None },
    ];

    // bb0 — init + iterator construction.
    let mut bb0_stmts = vec![assign(
        Place::local(2),
        Rvalue::Use(Operand::Constant(integer_const(&spec.acc_ty, 0))),
    )];
    let iter_source = if spec.array_is_param {
        bb0_stmts.push(assign(Place::local(3), Rvalue::Ref { mutable: false, place: deref(1) }));
        Operand::Move(Place::local(3))
    } else {
        // A body-LOCAL array: its elements are not free inputs.
        bb0_stmts.push(assign(
            Place::local(15),
            Rvalue::Repeat(
                Operand::Constant(integer_const(&spec.elem_ty, 1)),
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
                    Operand::Constant(ConstValue::Uint(
                        u128::try_from(k).expect("test fixture shift amount is nonnegative"),
                        32,
                    )),
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
                Operand::Constant(integer_const(&spec.acc_ty, 1)),
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
        bb4_stmts.push(assign(
            Place::local(2),
            Rvalue::Use(Operand::Constant(integer_const(&spec.acc_ty, 0))),
        ));
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
                callee_identity: None,
                callee_key: crate::sep_engine::tests::fixture_key(&INTO_ITER.to_string()),
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
                callee_identity: None,
                callee_key: crate::sep_engine::tests::fixture_key(&NEXT.to_string()),
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
                Operand::Constant(integer_const(&spec.elem_ty, 0)),
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
            callee_identity: None,
            callee_key: crate::sep_engine::tests::fixture_key("test::side_effect"),
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
            // A block the public bit CLAIMS is dead but which is not spelled
            // `Unreachable`: every successor stays live and the allowlist must
            // reject this call.
            Terminator::Call {
                func: "test::side_effect".to_string(),
                args: vec![],
                dest: Place::local(13),
                target: Some(BlockId(5)),
                span: SourceSpan::default(),
                atomic: None,
                is_foreign: false,
                is_unsafe_sig: false,
                callee_identity: None,
                callee_key: crate::sep_engine::tests::fixture_key("test::side_effect"),
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
        tuple_layouts: Default::default(),
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
fn a_tail_call_after_the_loop_is_refused() {
    let mut func = shift_reduction_overflow_fixture();
    let exit = func
        .body
        .blocks
        .iter_mut()
        .find(|block| block.id == BlockId(5))
        .expect("fixture exit block");
    exit.terminator = Terminator::TailCall {
        func: "some::tail_consumer".into(),
        args: vec![Operand::Copy(Place::local(2))],
        span: SourceSpan::default(),
        atomic: None,
        is_foreign: false,
        is_unsafe_sig: false,
        callee_identity: None,
        callee_key: crate::sep_engine::tests::fixture_key("some::tail_consumer"),
    };
    assert!(
        generate_bounded_reduction_bmc_refutation_candidates(&func).is_empty(),
        "an arbitrary tail callee may panic or diverge before the modeled execution completes"
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

/// INTRINSIC-RESIDUAL-1: the generator states a `u128` parameter's range as
/// `0 <= p <= UInt(u128::MAX)` (its MAX has no `Formula::Int` spelling). That exact
/// pair is the type's range and is certified; the `i128` range keeps its `Int`
/// spelling; anything narrower, or the `u128` pair on a narrower type, is refused.
#[test]
fn a_128_bit_parameter_type_range_is_certified_in_its_generator_spelling() {
    let with_param_ty = |ty: Ty| {
        let mut func = shift_reduction_overflow_fixture();
        func.body.arg_count = 2;
        func.body.locals[2].ty = ty;
        func
    };
    let fact = |min: Formula, max: Formula| {
        Formula::And(vec![
            Formula::Ge(Box::new(Formula::Var("t".into(), Sort::Int)), Box::new(min)),
            Formula::Le(Box::new(Formula::Var("t".into(), Sort::Int)), Box::new(max)),
        ])
    };
    let u128_func = with_param_ty(Ty::Int { width: 128, signed: false });
    assert!(is_integer_param_range_fact(
        &u128_func,
        &fact(Formula::Int(0), Formula::UInt(u128::MAX))
    ));
    assert!(!is_integer_param_range_fact(
        &u128_func,
        &fact(Formula::Int(0), Formula::UInt(u128::MAX - 1))
    ));
    assert!(!is_integer_param_range_fact(
        &u128_func,
        &fact(Formula::Int(0), Formula::Int(i128::MAX))
    ));
    let i128_func = with_param_ty(Ty::Int { width: 128, signed: true });
    assert!(is_integer_param_range_fact(
        &i128_func,
        &fact(Formula::Int(i128::MIN), Formula::Int(i128::MAX))
    ));
    assert!(!is_integer_param_range_fact(
        &i128_func,
        &fact(Formula::Int(0), Formula::Int(i128::MAX))
    ));
    let u64_func = with_param_ty(Ty::Int { width: 64, signed: false });
    assert!(!is_integer_param_range_fact(
        &u64_func,
        &fact(Formula::Int(0), Formula::UInt(u128::MAX))
    ));
}

// ── the caller-claimed exhaustive-enum arm ───────────────────────────────────

#[test]
fn the_public_exhaustiveness_bit_cannot_prune_an_unreachable_successor() {
    // Rustc closes the real `Option` switch with `otherwise -> bb6:
    // Unreachable`, but this test fixture is public TrustIR rather than a
    // provenance-bound compiler fact. A caller can set the same boolean on an
    // ordinary integer switch, so the BMC lane must follow the successor and
    // decline when it reaches `Unreachable`.
    let mut spec = ReductionSpec::new(u8_ty(), u8_ty(), 64, Addend::ShlAfterCast(4));
    spec.option_switch = OptionSwitch::ExhaustiveUnreachable;
    let mut func = reduction_fn(&spec);
    func.preconditions.push(tag_fact("_6", [0, 1]));
    assert!(
        crate::validate_function(&func).is_ok(),
        "the refusal must come from the BMC authority gate, not malformed TrustIR"
    );
    assert!(
        generate_bounded_reduction_bmc_refutation_candidates(&func).is_empty(),
        "a caller-constructible exhaustiveness bit cannot erase a reachable successor"
    );
}

/// The restoring half of the rule: with the SAME CFG and the SAME public bit,
/// but with the scrutinee's DECLARED type spelling a two-variant enum whose
/// discriminants are exactly the case set, the `otherwise` arm is dead by the
/// type and the lane fires.
///
/// This is what `4ca0cb0eac` asked for when it removed the hint-keyed override:
/// *"A future optimization may prune only from locally rederived, subject-bound
/// type/layout evidence."* The pair above/below is the whole rule: the bit alone
/// prunes nothing, the declared enum type does.
#[test]
fn a_declared_two_variant_enum_scrutinee_makes_the_dead_arm_prunable() {
    let mut spec = ReductionSpec::new(u8_ty(), u8_ty(), 64, Addend::ShlAfterCast(4));
    spec.option_switch = OptionSwitch::ExhaustiveUnreachable;
    spec.scrutinee = ScrutineeTy::OptionEnum;
    let mut func = reduction_fn(&spec);
    func.preconditions.push(tag_fact("_6", [0, 1]));
    assert!(crate::validate_function(&func).is_ok());
    assert_eq!(
        generate_bounded_reduction_bmc_refutation_candidates(&func).len(),
        1,
        "a `Discriminant` read of a place declared to be a two-variant enum, with \
         both discriminants cased, cannot reach the `otherwise` arm"
    );
}

/// The bit is not read AT ALL, in either direction: the same typed-enum body with
/// the exhaustiveness bit CLEARED still prunes, because the argument never used
/// the bit. (Nothing regresses: the pruning is licensed by the type.)
#[test]
fn the_public_bit_is_not_consulted_in_either_direction() {
    let mut spec = ReductionSpec::new(u8_ty(), u8_ty(), 64, Addend::ShlAfterCast(4));
    spec.option_switch = OptionSwitch::UncertifiedUnreachable;
    spec.scrutinee = ScrutineeTy::OptionEnum;
    let mut func = reduction_fn(&spec);
    func.preconditions.push(tag_fact("_6", [0, 1]));
    assert!(matches!(
        func.body.blocks[2].terminator,
        Terminator::SwitchInt { exhaustive_enum_unreachable: false, .. }
    ));
    assert_eq!(
        generate_bounded_reduction_bmc_refutation_candidates(&func).len(),
        1,
        "the verdict must depend on the declared type, never on the serialized bit"
    );
}

/// The `unreachable_unchecked()`-shaped partial match, now under genuine datatype
/// evidence: a THREE-variant enum with only `{0, 1}` cased. Discriminant 2 really
/// does reach the `otherwise` arm, so the case set must be required to be the
/// FULL declared discriminant set — a non-empty intersection is not enough.
#[test]
fn a_partial_match_over_a_three_variant_enum_is_still_refused() {
    let mut spec = ReductionSpec::new(u8_ty(), u8_ty(), 64, Addend::ShlAfterCast(4));
    spec.option_switch = OptionSwitch::PartialMatchOverAThreeVariantEnum;
    spec.scrutinee = ScrutineeTy::ThreeVariantEnum;
    let mut func = reduction_fn(&spec);
    func.preconditions.push(tag_fact("_6", [0, 1]));
    assert!(crate::validate_function(&func).is_ok());
    assert!(
        generate_bounded_reduction_bmc_refutation_candidates(&func).is_empty(),
        "discriminant 2 is unmatched, so the `Unreachable` arm is genuinely reachable UB"
    );
}

/// A `Discriminant` read of a STRUCT is not a sum tag, whatever variant list the
/// serialized type carries. The `adt_kind` discriminator is what separates the
/// two, and it must be required positively (`#[serde(default)]` makes it `None`
/// on every pre-classification body, which therefore prunes nothing).
#[test]
fn an_option_shaped_struct_scrutinee_prunes_nothing() {
    let mut spec = ReductionSpec::new(u8_ty(), u8_ty(), 64, Addend::ShlAfterCast(4));
    spec.option_switch = OptionSwitch::ExhaustiveUnreachable;
    spec.scrutinee = ScrutineeTy::OptionShapedStruct;
    let mut func = reduction_fn(&spec);
    func.preconditions.push(tag_fact("_6", [0, 1]));
    assert!(
        generate_bounded_reduction_bmc_refutation_candidates(&func).is_empty(),
        "an ADT declared a struct carries no sum-tag exhaustiveness argument"
    );
}

/// Belt (2) of the pruning rule, now with the type evidence present: an
/// `Unreachable` block that a NAMED case also targets is genuinely reached, and
/// dropping the `otherwise` edge would hide it.
#[test]
fn a_dead_arm_that_is_also_a_case_target_is_refused_even_with_type_evidence() {
    let mut spec = ReductionSpec::new(u8_ty(), u8_ty(), 64, Addend::ShlAfterCast(4));
    spec.option_switch = OptionSwitch::UnreachableAlsoACaseTarget;
    spec.scrutinee = ScrutineeTy::OptionEnum;
    let mut func = reduction_fn(&spec);
    func.preconditions.push(tag_fact("_6", [0, 1]));
    assert!(
        generate_bounded_reduction_bmc_refutation_candidates(&func).is_empty(),
        "case 0 reaches the `Unreachable` block directly; the lane must decline"
    );
}

/// Belt (1): the exhaustiveness argument licenses dropping an edge into an
/// `Unreachable` block and nothing else. When the `otherwise` block holds real
/// work, the edge stays and the terminator allowlist judges it.
#[test]
fn a_live_otherwise_block_keeps_its_edge_even_with_type_evidence() {
    let mut spec = ReductionSpec::new(u8_ty(), u8_ty(), 64, Addend::ShlAfterCast(4));
    spec.option_switch = OptionSwitch::CertificateWithoutUnreachable;
    spec.scrutinee = ScrutineeTy::OptionEnum;
    let mut func = reduction_fn(&spec);
    func.preconditions.push(tag_fact("_6", [0, 1]));
    assert!(
        generate_bounded_reduction_bmc_refutation_candidates(&func).is_empty(),
        "the `otherwise` block makes an unmodelled call; pruning must not reach it"
    );
}

#[test]
fn a_certificate_over_a_non_option_tag_set_is_refused() {
    // The public bit cannot license pruning even for the familiar `Option`
    // case spelling. This malformed case set makes the danger concrete: cases
    // {0, 2} leave a live gap at 1, so following the default successor must
    // expose `Unreachable` and refuse the function.
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
        "a caller-constructible bit over a non-exhaustive case set must not prune \
         the otherwise edge"
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
        "a reachable Unreachable successor must make the optional refutation lane decline"
    );
}

#[test]
fn a_certificate_whose_otherwise_block_is_not_unreachable_is_refused() {
    // The public bit does not hide even an ordinary otherwise successor. This
    // one contains a call that the straight-line reduction allowlist refuses.
    let mut spec = ReductionSpec::new(u8_ty(), u8_ty(), 64, Addend::ShlAfterCast(4));
    spec.option_switch = OptionSwitch::CertificateWithoutUnreachable;
    let mut func = reduction_fn(&spec);
    func.preconditions.push(tag_fact("_6", [0, 1]));
    assert!(
        generate_bounded_reduction_bmc_refutation_candidates(&func).is_empty(),
        "the caller-constructible bit cannot hide an otherwise-block call"
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

// ── a forged checked-shift carrier ───────────────────────────────────────────

/// A stale/public fixture that spells a shift as `CheckedBinaryOp(Shl)`.
/// Rustc's audited checked tuple carrier is only Add/Sub/Mul-WithOverflow, so
/// this body must fail structural admission before the optional BMC lane runs.
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
                Operand::Constant(ConstValue::Uint(4, 32)),
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
fn checked_shift_spelling_is_malformed_and_cannot_mint_a_candidate() {
    let func = checked_shift_fixture();
    assert!(
        matches!(
            crate::validate_function(&func),
            Err(crate::VcgenError::MalformedMir { detail, .. })
                if detail.contains("CheckedBinaryOp(Shl)")
                    && detail.contains("only Add, Sub, and Mul")
        ),
        "the forged checked-shift carrier must fail the exact structural admission rule"
    );
    assert!(
        generate_bounded_reduction_bmc_refutation_candidates(&func).is_empty(),
        "malformed checked-shift TrustIR cannot reach the refutation lane"
    );
}

#[test]
fn an_unfoldable_assert_in_the_loop_is_refused() {
    // Keep an otherwise valid ordinary-shift reduction, but replace the add's
    // assert with an opaque loop guard. It CAN fire, so iteration i is no
    // longer unconditionally reached.
    let mut f = shift_reduction_overflow_fixture();
    f.body.blocks[3].terminator = Terminator::Assert {
        cond: Operand::Copy(Place::local(13)),
        expected: true,
        msg: AssertMessage::Custom("opaque loop guard".into()),
        target: BlockId(4),
        span: SourceSpan::default(),
        unwind: UnwindEdge::Unreachable,
    };
    assert!(
        crate::validate_function(&f).is_ok(),
        "the assert refusal test must not collapse to malformed TrustIR"
    );
    assert!(
        generate_bounded_reduction_bmc_refutation_candidates(&f).is_empty(),
        "an assert that can fire must decline the whole unroll"
    );
}

/// T3 C07p: the lane writes its candidate into the caller's context through the row
/// oracle, and returns the candidate the tree-only lane returns.
#[test]
fn bmc_candidates_go_through_the_row_oracle() {
    use trust_types::vc_context::{Oracle, ParityCount, VcContext, same_row};

    let mut rows = VcContext::new();
    let interned = super::generate_bounded_reduction_bmc_refutation_candidates_rows(
        &shift_reduction_overflow_fixture(),
        &mut rows,
    );
    let tree =
        generate_bounded_reduction_bmc_refutation_candidates(&shift_reduction_overflow_fixture());
    assert_eq!(interned.len(), 1);
    assert_eq!(tree.len(), 1);
    assert!(same_row(&interned[0], &tree[0]));
    assert_eq!(rows.parity(Oracle::Row), ParityCount { rows: 1, mismatches: 0 });
}
