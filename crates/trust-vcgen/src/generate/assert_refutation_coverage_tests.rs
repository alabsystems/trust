// trust_vcgen/generate/assert_refutation_coverage_tests.rs
//
// Trust (NEW-EXEMPT-SPLIT, 2026-09-27): the pins for
// `assert_refutation::AssertRefutationCoverage` — which refutation-target block
// each candidate of the `-full` assert-refutation lane belongs to, and which
// target blocks the lane declined.
//
// THE FALSE PROOF THESE TESTS PIN (measured on stage 1 built from
// `1505108872`, docs/KNOWN_HAZARDS.md, "the panic-callee exemption counted
// candidates, not blocks"): the compiler's panic-callee exemption compared
// `#proved candidates == #target blocks`. The lane emits one candidate per
// PATH of a block's panic-path feasibility formula and none for a block whose
// guard it cannot ground, so two proved paths of one block balanced a second,
// declined block, whose panic call was then exempted. The fixture below is
// that shape in miniature: block 3 is reached by two paths, block 6 asserts on
// an opaque call result and is declined.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{
    BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan,
    Statement, Terminator, Ty, UnwindEdge, VerifiableBody, VerifiableFunction,
};

use crate::{
    AssertRefutationCandidates, AssertRefutationCoverage, VcgenContext,
    generate_full_assert_refutation_candidates_with_context,
    generate_full_assert_refutation_vcs_with_context, is_assert_refutation_target_block,
};

/// The two-path target block.
const TWO_PATH: BlockId = BlockId(3);
/// The declined target block (its assert reads an opaque call result).
const DECLINED: BlockId = BlockId(6);

fn assign(local: usize, rvalue: Rvalue) -> Statement {
    Statement::Assign { place: Place::local(local), rvalue, span: SourceSpan::default() }
}

fn cmp(op: BinOp, local: usize, constant: u128) -> Rvalue {
    Rvalue::BinaryOp(
        op,
        Operand::Copy(Place::local(local)),
        Operand::Constant(ConstValue::Uint(constant, 64)),
    )
}

/// `if b { goto on_true } else { goto on_false }` on the Bool local `b`.
fn branch(b: usize, on_false: BlockId, on_true: BlockId) -> Terminator {
    Terminator::SwitchInt {
        discr: Operand::Copy(Place::local(b)),
        targets: vec![(0, on_false)],
        otherwise: on_true,
        exhaustive_enum_unreachable: false,
        span: SourceSpan::default(),
    }
}

fn call(callee: &str, dest: usize, target: Option<BlockId>) -> Terminator {
    Terminator::Call {
        func: callee.into(),
        args: Vec::new(),
        dest: Place::local(dest),
        target,
        span: SourceSpan::default(),
        atomic: None,
        is_foreign: false,
        is_unsafe_sig: false,
        callee_identity: None,
        callee_key: crate::sep_engine::tests::fixture_key(callee),
        unwind: UnwindEdge::Unreachable,
    }
}

fn block(id: usize, stmts: Vec<Statement>, terminator: Terminator) -> BasicBlock {
    BasicBlock { id: BlockId(id), stmts, terminator }
}

/// ```text
/// fn split(x: u64) -> u64 {
///     if x < 3 || x > 100 { assert!(x != 50); }   // bb3: two paths, both infeasible
///     let v = external::opaque_u64();
///     assert!(v == 10);                            // bb6: declined when `declined`
///     x
/// }
/// ```
///
/// With `declined == false` bb4 is a plain `goto` and bb6's panic call is
/// replaced by `Unreachable`, leaving bb3 the only target block.
fn split_fixture(declined: bool) -> VerifiableFunction {
    let locals = vec![
        LocalDecl { index: 0, ty: Ty::u64(), name: None },
        LocalDecl { index: 1, ty: Ty::u64(), name: Some("x".into()) },
        LocalDecl { index: 2, ty: Ty::Bool, name: Some("lt3".into()) },
        LocalDecl { index: 3, ty: Ty::Bool, name: Some("gt100".into()) },
        LocalDecl { index: 4, ty: Ty::Bool, name: Some("ne50".into()) },
        LocalDecl { index: 5, ty: Ty::Unit, name: None },
        LocalDecl { index: 6, ty: Ty::u64(), name: Some("v".into()) },
        LocalDecl { index: 7, ty: Ty::Bool, name: Some("eq10".into()) },
        LocalDecl { index: 8, ty: Ty::Unit, name: None },
    ];
    let blocks = vec![
        block(0, vec![assign(2, cmp(BinOp::Lt, 1, 3))], branch(2, BlockId(1), BlockId(2))),
        block(1, vec![assign(3, cmp(BinOp::Gt, 1, 100))], branch(3, BlockId(4), BlockId(2))),
        block(2, vec![assign(4, cmp(BinOp::Ne, 1, 50))], branch(4, TWO_PATH, BlockId(4))),
        block(3, Vec::new(), call("core::panicking::panic", 5, None)),
        block(
            4,
            Vec::new(),
            if declined {
                call("external::opaque_u64", 6, Some(BlockId(5)))
            } else {
                Terminator::Goto(BlockId(7))
            },
        ),
        block(5, vec![assign(7, cmp(BinOp::Eq, 6, 10))], branch(7, DECLINED, BlockId(7))),
        block(
            6,
            Vec::new(),
            if declined {
                call("core::panicking::assert_failed::<u64, u64>", 8, None)
            } else {
                Terminator::Unreachable
            },
        ),
        block(7, vec![assign(0, Rvalue::Use(Operand::Copy(Place::local(1))))], Terminator::Return),
    ];
    VerifiableFunction {
        name: "split".into(),
        def_path: "test::split".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks,
            arg_count: 1,
            return_ty: Ty::u64(),
            datatype_defs: Default::default(),
        },
        contracts: Vec::new(),
        preconditions: Vec::new(),
        postconditions: Vec::new(),
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn candidates(func: &VerifiableFunction) -> AssertRefutationCandidates {
    let context = VcgenContext::for_function(func.def_path.clone());
    generate_full_assert_refutation_candidates_with_context(func, &context)
}

fn parts_of(candidates: &AssertRefutationCandidates, block: BlockId) -> Vec<usize> {
    (0..candidates.vcs().len())
        .filter(|&index| candidates.coverage().candidate_target_block(index) == Some(block))
        .collect()
}

/// THE REGRESSION. Every candidate proved, the retired count balanced, and the
/// declined block is still not proved — so the exemption is refused.
///
/// MUTANT WITNESS: `every_target_block_proved` answering the retired rule
/// (`#proved candidates == #target blocks`) fails the last assertion — the
/// count holds on this fixture.
#[test]
fn two_proved_paths_of_one_block_do_not_cover_a_declined_block() {
    let func = split_fixture(true);
    let found = candidates(&func);
    let coverage = found.coverage();

    // The premise, as measured on real MIR: the two-path block splits into two
    // candidates and the declined block has none.
    assert_eq!(parts_of(&found, TWO_PATH).len(), 2, "one candidate per path");
    assert!(parts_of(&found, DECLINED).is_empty(), "the opaque assert is declined");
    assert_eq!(found.vcs().len(), 2);
    assert_eq!(coverage.target_blocks().collect::<Vec<_>>(), vec![TWO_PATH, DECLINED]);
    assert_eq!(coverage.declined_target_blocks(), vec![DECLINED]);
    // ... which is exactly what satisfied the retired count rule.
    let target_count =
        func.body.blocks.iter().filter(|b| is_assert_refutation_target_block(b)).count();
    assert_eq!(found.vcs().len(), target_count);

    assert!(coverage.target_block_proved(TWO_PATH, |_| true));
    assert!(!coverage.target_block_proved(DECLINED, |_| true));
    assert!(
        !coverage.every_target_block_proved(|_| true),
        "block 6 was never a candidate, so no proof covers it: the exemption must be refused \
         however many paths of block 3 were proved"
    );
}

/// CONTROL: the same two-path block with nothing declined is proved once BOTH
/// of its paths are proved — and only then.
///
/// The retired count REFUSED this body (two proved candidates, one target
/// block): the per-block rule is also what lets a multi-path block be exempted.
#[test]
fn a_block_is_proved_only_when_every_one_of_its_paths_is() {
    let func = split_fixture(false);
    let found = candidates(&func);
    let coverage = found.coverage();
    let parts = parts_of(&found, TWO_PATH);
    assert_eq!(parts.len(), 2, "one candidate per path");
    assert_eq!(found.vcs().len(), 2);
    assert_eq!(coverage.target_blocks().collect::<Vec<_>>(), vec![TWO_PATH]);
    assert!(coverage.declined_target_blocks().is_empty());

    assert!(coverage.every_target_block_proved(|_| true));
    for unproved in &parts {
        assert!(
            !coverage.every_target_block_proved(|index| index != *unproved),
            "a block with one unproved path is not unreachable"
        );
        assert!(!coverage.target_block_proved(TWO_PATH, |index| index != *unproved));
    }
}

/// A candidate the CALLER appends after the generator's own (the compiler's
/// coroutine-sentinel rows) belongs to no target block, proved or not — the
/// second way into the retired count.
#[test]
fn appended_candidates_cover_no_target_block() {
    let func = split_fixture(true);
    let found = candidates(&func);
    let coverage = found.coverage();
    let len = found.vcs().len();
    assert_eq!(coverage.candidate_count(), len);
    assert_eq!(coverage.candidate_target_block(len), None);
    assert_eq!(coverage.candidate_target_block(len + 7), None);
    // Only appended rows proved: nothing is covered, not even the emitted block.
    assert!(!coverage.target_block_proved(TWO_PATH, |index| index >= len));
    assert!(!coverage.every_target_block_proved(|index| index >= len));
}

/// A block whose emitted parts are not all still present is not proved: the
/// record carries the number of parts each block emitted, so a part lost
/// between the generator and the verdicts cannot make a block look decided.
#[test]
fn a_block_missing_one_of_its_parts_is_not_proved() {
    let coverage = AssertRefutationCoverage::for_test(vec![Some(TWO_PATH)], vec![(TWO_PATH, 2)]);
    assert!(!coverage.target_block_proved(TWO_PATH, |_| true));
    assert!(!coverage.every_target_block_proved(|_| true));
    // The same record with both parts present is proved.
    let whole = AssertRefutationCoverage::for_test(
        vec![Some(TWO_PATH), Some(TWO_PATH)],
        vec![(TWO_PATH, 2)],
    );
    assert!(whole.every_target_block_proved(|_| true));
    // A block the record does not list as a target is never proved.
    assert!(!whole.target_block_proved(DECLINED, |_| true));
}

/// A malformed body yields one row that belongs to no block, and every target
/// block is recorded as declined — so even a proof of that row licenses no
/// exemption.
#[test]
fn the_malformed_body_row_covers_no_target_block() {
    let mut func = split_fixture(true);
    // A non-positional block identity fails `validate_function`.
    func.body.blocks[7].id = BlockId(70);
    let found = candidates(&func);
    assert_eq!(found.vcs().len(), 1, "the malformed-body row");
    let coverage = found.coverage();
    assert_eq!(coverage.candidate_target_block(0), None);
    assert_eq!(coverage.declined_target_blocks(), vec![TWO_PATH, DECLINED]);
    assert!(!coverage.every_target_block_proved(|_| true));
}

/// A body with no target block is vacuously covered — there is nothing to
/// exempt — and the recognizer and the coverage agree on what a target is.
#[test]
fn no_target_block_is_vacuously_covered() {
    let mut func = split_fixture(false);
    func.body.blocks[3].terminator = Terminator::Unreachable;
    func.body.blocks[6].terminator = Terminator::Unreachable;
    assert!(!func.body.blocks.iter().any(is_assert_refutation_target_block));
    let found = candidates(&func);
    assert!(found.vcs().is_empty());
    assert_eq!(found.coverage().target_blocks().count(), 0);
    assert!(found.coverage().every_target_block_proved(|_| false));
}

/// The coverage describes exactly the candidates the plain API returns.
#[test]
fn candidates_api_returns_the_plain_api_candidates() {
    let func = split_fixture(true);
    let context = VcgenContext::for_function(func.def_path.clone());
    let plain = generate_full_assert_refutation_vcs_with_context(&func, &context);
    let (vcs, coverage) = candidates(&func).into_parts();
    assert_eq!(plain.len(), vcs.len());
    assert_eq!(coverage.candidate_count(), vcs.len());
    for (a, b) in plain.iter().zip(&vcs) {
        assert_eq!(a.formula, b.formula);
        assert_eq!(a.location, b.location);
    }
}

/// T3 C07p: the lane writes its candidates into the caller's context through the row
/// oracle, and returns the candidates and the coverage the tree-only lane returns.
#[test]
fn refutation_candidates_go_through_the_row_oracle() {
    use trust_types::vc_context::{Oracle, ParityCount, VcContext, same_row};

    let func = split_fixture(true);
    let context = VcgenContext::for_function(func.def_path.clone());
    let mut rows = VcContext::new();
    let interned = crate::generate_full_assert_refutation_candidates_with_context_rows(
        &func, &context, &mut rows,
    );
    let tree = candidates(&func);
    assert_eq!(interned.vcs().len(), 2);
    assert_eq!(tree.vcs().len(), 2);
    assert!(interned.vcs().iter().zip(tree.vcs()).all(|(a, b)| same_row(a, b)));
    assert_eq!(
        interned.coverage().declined_target_blocks(),
        tree.coverage().declined_target_blocks()
    );
    assert_eq!(rows.parity(Oracle::Row), ParityCount { rows: 2, mismatches: 0 });
}
