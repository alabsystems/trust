//! NEW-READER PINS for the E6 import — increment P of the E6 admission
//! expansion (`docs/design-notes/2026-09-28-e6-admission-expansion.md` §6,
//! review H3).
//!
//! The standing provenance pins (`binop_provenance_pins_never_admit` in
//! `trust-types/src/admissible_body.rs`, `l3_p2`, `l7_p5`, `control_23`/
//! `control_27` `half_7`, `control_3`) call `recognize_admissible_body`. Every
//! E6 widening lands BESIDE that function — an E6-only reader the importer
//! consults after it answers `None` — so those pins stay green while measuring
//! nothing about the new reader. These are their twins, taken END TO END
//! through the production entry point [`admit_function_into`], with every
//! facet certified so that only the readers and the mints stand between each
//! body and an import:
//!
//! * `UncheckedBinaryOp` (undefined behaviour on overflow) is never imported,
//!   at any operator or carrier;
//! * a `CheckedBinaryOp` pair never reaches `_0` as arithmetic — neither as
//!   the returned value nor through its `.0` projection behind the overflow
//!   `Assert`;
//! * a raw `BinaryOp(Add|Sub|Mul)` stays outside the fragment (today's
//!   boundary: the confined D-a lane is the only route that may ever read it);
//! * a call to a callee that has no import of its own — unadmitted, opaque,
//!   generic, or merely NAMED like an admitted function — is never imported.
//!
//! Since E6 expansion I3′/I4′ the E6-only TREE reader walks every arm of a
//! decision — the right operand of a short-circuit `&&`/`||`, both arms of an
//! `if`, every arm of a `match` — so each family above is ALSO pinned in each
//! of those ARM positions (`*_in_every_arm_position`), beside a control that
//! puts a plain parameter in the same slot and must import.
//!
//! A red here after a widening is a soundness incident, not a test update:
//! the widened reader has armed a false definitional import.

use clean_kernel::Environment;
use trust_certify::clean_island::admit_function_into;
use trust_spec_elab::FacetTable;
use trust_types::{
    BasicBlock, BinOp, BlockId, LocalDecl, Operand, Place, Projection, Rvalue, SourceSpan,
    Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
};

fn func(params: &[Ty], ret: Ty, temps: &[Ty], blocks: Vec<BasicBlock>) -> VerifiableFunction {
    let mut locals = vec![LocalDecl { index: 0, ty: ret.clone(), name: None }];
    for ty in params.iter().chain(temps) {
        locals.push(LocalDecl { index: locals.len(), ty: ty.clone(), name: None });
    }
    VerifiableFunction {
        name: "f".into(),
        def_path: "pins::f".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks,
            arg_count: params.len(),
            return_ty: ret,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn asn(local: usize, rvalue: Rvalue) -> Statement {
    Statement::Assign { place: Place::local(local), rvalue, span: SourceSpan::default() }
}

fn cp(local: usize) -> Operand {
    Operand::Copy(Place::local(local))
}

fn ret_block(id: usize, stmts: Vec<Statement>) -> BasicBlock {
    BasicBlock { id: BlockId(id), stmts, terminator: Terminator::Return }
}

/// Whether the production importer mints `f` with all four facets certified.
fn imports(f: &VerifiableFunction) -> bool {
    let table = FacetTable::from_structural_facets([(f.def_path.clone(), true, true, true, true)]);
    admit_function_into(&mut Environment::with_prelude(), f, &table).is_some()
}

const OPS: [BinOp; 10] = [
    BinOp::Add,
    BinOp::Sub,
    BinOp::Mul,
    BinOp::Shl,
    BinOp::Shr,
    BinOp::BitAnd,
    BinOp::BitOr,
    BinOp::BitXor,
    BinOp::Eq,
    BinOp::Ne,
];

fn carriers() -> [Ty; 3] {
    [Ty::u64(), Ty::Int { width: 8, signed: false }, Ty::Bool]
}

#[test]
fn unchecked_binary_ops_are_never_imported() {
    for ty in carriers() {
        for op in OPS {
            let ret = if matches!(op, BinOp::Eq | BinOp::Ne) { Ty::Bool } else { ty.clone() };
            let f = func(
                &[ty.clone(), ty.clone()],
                ret,
                &[],
                vec![ret_block(0, vec![asn(0, Rvalue::UncheckedBinaryOp(op, cp(1), cp(2)))])],
            );
            assert!(!imports(&f), "UncheckedBinaryOp({op:?}) on {ty:?} was imported");
        }
    }
}

#[test]
fn a_checked_pair_never_reaches_the_return_place_as_arithmetic() {
    for ty in carriers() {
        for op in [BinOp::Add, BinOp::Sub, BinOp::Mul] {
            // `_0 = CheckedBinaryOp(..)` — the pair itself.
            let pair = func(
                &[ty.clone(), ty.clone()],
                ty.clone(),
                &[],
                vec![ret_block(0, vec![asn(0, Rvalue::CheckedBinaryOp(op, cp(1), cp(2)))])],
            );
            assert!(!imports(&pair), "CheckedBinaryOp({op:?}) on {ty:?} was imported");
            // `_3 = CheckedBinaryOp(..); assert(!_3.1); _0 = _3.0` — rustc's
            // overflow-checked `a + b`.
            let tuple = Ty::Tuple(vec![ty.clone(), Ty::Bool]);
            let field = |i: usize| {
                Operand::Move(Place { local: 3, projections: vec![Projection::Field(i)] })
            };
            let guarded = func(
                &[ty.clone(), ty.clone()],
                ty.clone(),
                &[tuple],
                vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![asn(3, Rvalue::CheckedBinaryOp(op, cp(1), cp(2)))],
                        terminator: Terminator::Assert {
                            cond: field(1),
                            expected: false,
                            msg: trust_types::AssertMessage::Overflow(op),
                            target: BlockId(1),
                            span: SourceSpan::default(),
                            unwind: Default::default(),
                        },
                    },
                    ret_block(1, vec![asn(0, Rvalue::Use(field(0)))]),
                ],
            );
            assert!(!imports(&guarded), "the `.0` of a checked {op:?} on {ty:?} was imported");
        }
    }
}

#[test]
fn raw_arithmetic_stays_outside_the_fragment() {
    for ty in [Ty::u64(), Ty::Int { width: 8, signed: false }] {
        for op in [BinOp::Add, BinOp::Sub, BinOp::Mul] {
            let f = func(
                &[ty.clone(), ty.clone()],
                ty.clone(),
                &[],
                vec![ret_block(0, vec![asn(0, Rvalue::BinaryOp(op, cp(1), cp(2)))])],
            );
            assert!(!imports(&f), "raw BinaryOp({op:?}) on {ty:?} was imported");
        }
    }
}

#[test]
fn a_call_to_a_callee_without_its_own_import_is_never_imported() {
    let u = Ty::u64();
    for callee in [
        // an ordinary local function with no admission in the table
        "pins::g",
        // a generic instantiation
        "pins::g::<u64>",
        // an opaque / foreign symbol
        "extern_symbol",
        // a spelling that LOOKS like a marked primitive but is not one
        "core::num::<impl u64>::wrapping_add",
        "pins::wrapping_add",
        // the importer's own constant namespace, named as a callee
        "trust_import_pins__g",
    ] {
        let f = func(
            &[u.clone(), u.clone()],
            u.clone(),
            &[],
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        func: callee.into(),
                        args: vec![cp(1), cp(2)],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_foreign: callee == "extern_symbol",
                        is_unsafe_sig: false,
                        unwind: Default::default(),
                        callee_identity: None,
                        callee_key: None,
                    },
                },
                ret_block(1, vec![]),
            ],
        );
        assert!(!imports(&f), "a call to `{callee}` was imported");
    }
}

// ---------------------------------------------------------------------------
// ARM positions (E6 expansion I3′/I4′, review P1-3)
// ---------------------------------------------------------------------------

/// Where a construct sits in a decision the tree reader walks. Every body has
/// the parameters `(c: bool, x: u8, a: T, b: T)` = `_1.._4`; the arm under
/// test computes into `_0` (or, for [`ArmAt::AndRight`], into the temporary
/// `_6` that the `&&`'s right operand compares).
#[derive(Clone, Copy, Debug)]
enum ArmAt {
    /// `if c { a } else { ⟨arm⟩ }`.
    Else,
    /// `if c { ⟨arm⟩ } else { a }`.
    Then,
    /// `match x { 0 => a, 1 => ⟨arm⟩, _ => a }` — a NON-FIRST arm.
    MatchArm,
    /// `c && ⟨arm⟩ == a` — the short-circuited right operand, returning `bool`.
    AndRight,
}

const ARM_POSITIONS: [ArmAt; 4] = [ArmAt::Else, ArmAt::Then, ArmAt::MatchArm, ArmAt::AndRight];

/// What the arm under test computes, from `a` and `b`.
#[derive(Clone, Debug)]
enum ArmFamily {
    /// `a`/`b` copied — the CONTROL, which must import.
    Plain,
    /// `UncheckedBinaryOp(op, a, b)`.
    Unchecked(BinOp),
    /// `_5 = CheckedBinaryOp(op, a, b); assert(!_5.1); … _5.0`.
    CheckedPair(BinOp),
    /// A raw `BinaryOp(op, a, b)`.
    Raw(BinOp),
    /// A call `callee(a, b)`.
    Callee(&'static str),
}

const JOIN: usize = 4;

fn goto(id: usize, stmts: Vec<Statement>, to: usize) -> BasicBlock {
    BasicBlock { id: BlockId(id), stmts, terminator: Terminator::Goto(BlockId(to)) }
}

fn switch(id: usize, discr: usize, targets: Vec<(u128, usize)>, otherwise: usize) -> BasicBlock {
    BasicBlock {
        id: BlockId(id),
        stmts: vec![],
        terminator: Terminator::SwitchInt {
            discr: cp(discr),
            targets: targets.into_iter().map(|(v, t)| (v, BlockId(t))).collect(),
            otherwise: BlockId(otherwise),
            exhaustive_enum_unreachable: false,
            span: SourceSpan::default(),
        },
    }
}

/// The arm's blocks, starting at `bb2` (and `bb3` when it needs a second
/// block), computing `family(a, b)` into `into` and then running `after`
/// before jumping to the join.
fn arm_blocks(family: &ArmFamily, into: usize, after: Vec<Statement>) -> Vec<BasicBlock> {
    let then_after = |mut stmts: Vec<Statement>| {
        stmts.extend(after.clone());
        stmts
    };
    match family {
        ArmFamily::Plain => vec![goto(2, then_after(vec![asn(into, Rvalue::Use(cp(4)))]), JOIN)],
        ArmFamily::Unchecked(op) => vec![goto(
            2,
            then_after(vec![asn(into, Rvalue::UncheckedBinaryOp(*op, cp(3), cp(4)))]),
            JOIN,
        )],
        ArmFamily::Raw(op) => {
            vec![goto(2, then_after(vec![asn(into, Rvalue::BinaryOp(*op, cp(3), cp(4)))]), JOIN)]
        }
        ArmFamily::CheckedPair(op) => {
            let field = |i: usize| {
                Operand::Move(Place { local: 5, projections: vec![Projection::Field(i)] })
            };
            vec![
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![asn(5, Rvalue::CheckedBinaryOp(*op, cp(3), cp(4)))],
                    terminator: Terminator::Assert {
                        cond: field(1),
                        expected: false,
                        msg: trust_types::AssertMessage::Overflow(*op),
                        target: BlockId(3),
                        span: SourceSpan::default(),
                        unwind: Default::default(),
                    },
                },
                goto(3, then_after(vec![asn(into, Rvalue::Use(field(0)))]), JOIN),
            ]
        }
        ArmFamily::Callee(callee) => vec![
            BasicBlock {
                id: BlockId(2),
                stmts: vec![],
                terminator: Terminator::Call {
                    func: (*callee).into(),
                    args: vec![cp(3), cp(4)],
                    dest: Place::local(into),
                    target: Some(BlockId(3)),
                    span: SourceSpan::default(),
                    atomic: None,
                    is_foreign: *callee == "extern_symbol",
                    is_unsafe_sig: false,
                    unwind: Default::default(),
                    callee_identity: None,
                    callee_key: None,
                },
            },
            goto(3, then_after(vec![]), JOIN),
        ],
    }
}

/// The body with `family` at `at`, over the carrier `ty`.
fn in_arm(at: ArmAt, family: &ArmFamily, ty: &Ty) -> VerifiableFunction {
    let params = [Ty::Bool, Ty::Int { width: 8, signed: false }, ty.clone(), ty.clone()];
    // `_5` holds a checked pair, `_6` the `&&` operand's value.
    let temps = [Ty::Tuple(vec![ty.clone(), Ty::Bool]), ty.clone()];
    let plain_a = |id: usize| goto(id, vec![asn(0, Rvalue::Use(cp(3)))], JOIN);
    let mut blocks = match at {
        ArmAt::Else => vec![switch(0, 1, vec![(0, 2)], 1), plain_a(1)],
        ArmAt::Then => vec![switch(0, 1, vec![(0, 1)], 2), plain_a(1)],
        ArmAt::MatchArm => vec![switch(0, 2, vec![(0, 1), (1, 2)], 5), plain_a(1), plain_a(5)],
        ArmAt::AndRight => vec![
            switch(0, 1, vec![(0, 1)], 2),
            goto(
                1,
                vec![asn(0, Rvalue::Use(Operand::Constant(trust_types::ConstValue::Bool(false))))],
                JOIN,
            ),
        ],
    };
    let (into, after, ret) = match at {
        ArmAt::AndRight => (6, vec![asn(0, Rvalue::BinaryOp(BinOp::Eq, cp(6), cp(3)))], Ty::Bool),
        _ => (0, vec![], ty.clone()),
    };
    blocks.extend(arm_blocks(family, into, after));
    blocks.push(ret_block(JOIN, vec![]));
    blocks.sort_by_key(|b| b.id.0);
    func(&params, ret, &temps, blocks)
}

/// The families, each at every arm position, over `u64` and `u8`.
fn assert_never_imported_in_any_arm(families: &[ArmFamily]) {
    for ty in [Ty::u64(), Ty::Int { width: 8, signed: false }] {
        for at in ARM_POSITIONS {
            // The control first: the same position with a parameter in the
            // slot DOES import, so every refusal below is the family's.
            assert!(
                imports(&in_arm(at, &ArmFamily::Plain, &ty)),
                "the {at:?} control over {ty:?} must import"
            );
            for family in families {
                assert!(
                    !imports(&in_arm(at, family, &ty)),
                    "{family:?} in the {at:?} arm over {ty:?} was imported"
                );
            }
        }
    }
}

#[test]
fn unchecked_binary_ops_in_every_arm_position() {
    let arith = [BinOp::Add, BinOp::Sub, BinOp::Mul, BinOp::Shl, BinOp::Shr];
    assert_never_imported_in_any_arm(&arith.map(ArmFamily::Unchecked));
}

#[test]
fn a_checked_pair_in_every_arm_position() {
    let arith = [BinOp::Add, BinOp::Sub, BinOp::Mul];
    assert_never_imported_in_any_arm(&arith.map(ArmFamily::CheckedPair));
}

#[test]
fn raw_arithmetic_in_every_arm_position() {
    let ops = [
        BinOp::Add,
        BinOp::Sub,
        BinOp::Mul,
        BinOp::Div,
        BinOp::Rem,
        BinOp::Shl,
        BinOp::Shr,
        BinOp::BitAnd,
        BinOp::BitOr,
        BinOp::BitXor,
    ];
    assert_never_imported_in_any_arm(&ops.map(ArmFamily::Raw));
}

#[test]
fn a_callee_without_its_own_import_in_every_arm_position() {
    let callees = [
        "pins::g",
        "pins::g::<u64>",
        "extern_symbol",
        "core::num::<impl u64>::wrapping_add",
        "core::num::<impl u8>::wrapping_add",
        "pins::wrapping_add",
        "trust_import_pins__g",
    ];
    assert_never_imported_in_any_arm(&callees.map(ArmFamily::Callee));
}

/// The controls: the same harness DOES import the admitted neighbours of the
/// pinned shapes, so every refusal above is a refusal of the shape and not of
/// the harness.
#[test]
fn the_pins_harness_imports_the_admitted_neighbours() {
    let u = Ty::u64();
    let lt = func(
        &[u.clone(), u.clone()],
        Ty::Bool,
        &[],
        vec![ret_block(0, vec![asn(0, Rvalue::BinaryOp(BinOp::Lt, cp(1), cp(2)))])],
    );
    assert!(imports(&lt), "the comparison control must import");
    let proj = func(
        &[u.clone(), u.clone()],
        u.clone(),
        &[],
        vec![ret_block(0, vec![asn(0, Rvalue::Use(cp(2)))])],
    );
    assert!(imports(&proj), "the projection control must import");
}
