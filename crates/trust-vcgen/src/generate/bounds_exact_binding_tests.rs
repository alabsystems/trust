//! The native-`BoundsCheck` suppression in the rvalue lane is EXACT-BINDING,
//! never bare target identity.
//!
//! `generate_v2_rvalue_safety_vcs_impl` used to skip every per-statement
//! index-bounds row in any block some `BoundsCheck` assert targeted
//! (`v2_bounds_guard_targets`, now deleted) — no cond binding, no `expected`
//! check. That is precisely the identity weakness this campaign removed for
//! Overflow/OverflowNeg and Div/Rem ("an assert targeting this block is not
//! sufficient authority to suppress the row"): a `Lt(_i, len_A)` assert whose
//! success edge enters a block that also indexes a DIFFERENT array `B`
//! suppressed B's rows on A's authority. The tests below pin the replacement
//! (`v2_bounds_assert_exactly_covers_place`): only a canonical
//! `Lt(index, bound)` binding whose index IS the row's index local and whose
//! bound IS the row's collection length may suppress — and only through the
//! assert's sole-entry success edge. Everything short of that emits the row
//! (over-report is the fail-closed direction; path guards can still discharge
//! the emitted row downstream).

use trust_types::{
    AssertMessage, BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place, Projection,
    Rvalue, SourceSpan, Statement, Terminator, Ty, VcKind, VerifiableBody, VerifiableFunction,
    VerificationCondition,
};

use super::generate_v2_rvalue_safety_vcs_impl;

const ASSERT_ADDR: u64 = 0x90;
const LOAD_A_ADDR: u64 = 0xA0;
const LOAD_B_ADDR: u64 = 0xB0;
const STORE_A_ADDR: u64 = 0xC0;
const STORE_B_ADDR: u64 = 0xD0;

fn assign_at(place: Place, rvalue: Rvalue, addr: u64) -> Statement {
    Statement::Assign { place, rvalue, span: SourceSpan::binary_address(addr) }
}

/// `_dest = _arr[_index]` at `addr`.
fn load(dest: usize, arr: usize, index: usize, addr: u64) -> Statement {
    assign_at(
        Place::local(dest),
        Rvalue::Use(Operand::Copy(Place {
            local: arr,
            projections: vec![Projection::Index(index)],
        })),
        addr,
    )
}

/// `_arr[_index] = const` at `addr`.
fn store(arr: usize, index: usize, addr: u64) -> Statement {
    assign_at(
        Place { local: arr, projections: vec![Projection::Index(index)] },
        Rvalue::Use(Operand::Constant(ConstValue::Float(1.0))),
        addr,
    )
}

/// `fn guarded(a: [f64; 4], b: [f64; 8], i: usize, j: usize)` with the exact
/// MIR bounds-assert shape rustc emits for `a[i]`:
///
///   bb0: _5 = Len(_1); _6 = Lt(copy _3, copy _5);
///        Assert(move _6, expected, BoundsCheck) -> bb1
///   bb1: <bb1_stmts>; return
///
/// The assert's cond binds index `_3` (`i`) against `Len(a)` — and NOTHING
/// else. `b` (`_2`) and `j` (`_4`) exist so a statement in bb1 can index a
/// collection/index the assert never checked.
fn guarded_fn(expected: bool, bb1_stmts: Vec<Statement>) -> VerifiableFunction {
    VerifiableFunction {
        name: "guarded".to_string(),
        def_path: "test::guarded".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::f64_ty(), name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Array { elem: Box::new(Ty::f64_ty()), len: 4 },
                    name: Some("a".into()),
                },
                LocalDecl {
                    index: 2,
                    ty: Ty::Array { elem: Box::new(Ty::f64_ty()), len: 8 },
                    name: Some("b".into()),
                },
                LocalDecl { index: 3, ty: Ty::usize(), name: Some("i".into()) },
                LocalDecl { index: 4, ty: Ty::usize(), name: Some("j".into()) },
                LocalDecl { index: 5, ty: Ty::usize(), name: None },
                LocalDecl { index: 6, ty: Ty::Bool, name: None },
                LocalDecl { index: 7, ty: Ty::f64_ty(), name: None },
                LocalDecl { index: 8, ty: Ty::f64_ty(), name: None },
                LocalDecl { index: 9, ty: Ty::usize(), name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        assign_at(Place::local(5), Rvalue::Len(Place::local(1)), 0x80),
                        assign_at(
                            Place::local(6),
                            Rvalue::BinaryOp(
                                BinOp::Lt,
                                Operand::Copy(Place::local(3)),
                                Operand::Copy(Place::local(5)),
                            ),
                            0x81,
                        ),
                    ],
                    terminator: Terminator::Assert {
                        unwind: trust_types::UnwindEdge::Unreachable,
                        cond: Operand::Move(Place::local(6)),
                        expected,
                        msg: AssertMessage::BoundsCheck,
                        target: BlockId(1),
                        span: SourceSpan::binary_address(ASSERT_ADDR),
                    },
                },
                BasicBlock { id: BlockId(1), stmts: bb1_stmts, terminator: Terminator::Return },
            ],
            arg_count: 4,
            return_ty: Ty::f64_ty(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn rvalue_lane_vcs(func: &VerifiableFunction) -> Vec<VerificationCondition> {
    generate_v2_rvalue_safety_vcs_impl(func, None)
}

fn bounds_rows_at(vcs: &[VerificationCondition], addr: u64) -> usize {
    let at = SourceSpan::binary_address(addr);
    vcs.iter()
        .filter(|vc| {
            matches!(vc.kind, VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck)
                && vc.location == at
        })
        .count()
}

#[test]
fn canonical_guarded_load_stays_suppressed() {
    // The exactly-bound row: `a[i]` under `assert(Lt(i, Len(a)), true)` through
    // the assert's sole success edge. The assert lane owns this obligation; the
    // per-statement duplicate stays suppressed (no over-reporting regression).
    let func = guarded_fn(true, vec![load(7, 1, 3, LOAD_A_ADDR)]);
    let vcs = rvalue_lane_vcs(&func);
    assert_eq!(
        bounds_rows_at(&vcs, LOAD_A_ADDR),
        0,
        "the canonical exactly-bound `a[i]` row must stay suppressed: {vcs:#?}"
    );
}

#[test]
fn unrelated_collection_row_cannot_borrow_the_asserts_authority() {
    // The soundness scenario the bare-target set walked into: bb1 also indexes
    // `b[j]`, which the assert's cond (`i < Len(a)`) never checked. Under
    // block-identity suppression B's row vanished on A's authority; under exact
    // binding it must EMIT, while the genuinely bound `a[i]` row stays
    // suppressed.
    let func = guarded_fn(true, vec![load(7, 1, 3, LOAD_A_ADDR), load(8, 2, 4, LOAD_B_ADDR)]);
    let vcs = rvalue_lane_vcs(&func);
    assert_eq!(
        bounds_rows_at(&vcs, LOAD_A_ADDR),
        0,
        "the exactly-bound `a[i]` row stays suppressed alongside the unrelated one"
    );
    assert_eq!(
        bounds_rows_at(&vcs, LOAD_B_ADDR),
        1,
        "`b[j]` must EMIT its row — the `Lt(i, Len(a))` assert is no authority over it: {vcs:#?}"
    );
    // End-to-end: the emitted row survives the full pipeline (path guards may
    // wrap its formula, but the obligation itself must reach the router).
    let full = crate::generate_vcs(&func);
    assert_eq!(
        bounds_rows_at(&full, LOAD_B_ADDR),
        1,
        "the unguarded `b[j]` row must survive `generate_vcs`"
    );
}

#[test]
fn same_index_against_a_different_collection_keeps_the_row() {
    // Sharper variant: SAME index `i`, DIFFERENT collection (`b[i]`, len 8).
    // The index half of the binding matches; the length half must refuse —
    // `i < Len(a)` proves nothing about `b`'s bound.
    let func = guarded_fn(true, vec![load(8, 2, 3, LOAD_B_ADDR)]);
    let vcs = rvalue_lane_vcs(&func);
    assert_eq!(
        bounds_rows_at(&vcs, LOAD_B_ADDR),
        1,
        "`b[i]` must keep its row: the assert's bound is `Len(a)`, not `Len(b)`: {vcs:#?}"
    );
}

#[test]
fn expected_false_bounds_assert_never_suppresses() {
    // An `expected: false` BoundsCheck succeeds when its condition is FALSE —
    // its success edge carries no `index < len` evidence at all, so the row in
    // its target block must emit.
    let func = guarded_fn(false, vec![load(7, 1, 3, LOAD_A_ADDR)]);
    let vcs = rvalue_lane_vcs(&func);
    assert_eq!(
        bounds_rows_at(&vcs, LOAD_A_ADDR),
        1,
        "`expected: false` is non-canonical polarity and must never suppress: {vcs:#?}"
    );
}

#[test]
fn store_side_binding_is_per_row_too() {
    // The destination-side lane (`arr[i] = v`, `check_place_index_bounds`) had
    // the same bare-target skip. Exact binding applies per row there as well:
    // the bound `a[i] = v` store stays suppressed, the unrelated `b[j] = v`
    // store emits.
    let func = guarded_fn(true, vec![store(1, 3, STORE_A_ADDR), store(2, 4, STORE_B_ADDR)]);
    let vcs = rvalue_lane_vcs(&func);
    assert_eq!(
        bounds_rows_at(&vcs, STORE_A_ADDR),
        0,
        "the exactly-bound `a[i] = v` store row stays suppressed"
    );
    assert_eq!(
        bounds_rows_at(&vcs, STORE_B_ADDR),
        1,
        "the unrelated `b[j] = v` store row must EMIT: {vcs:#?}"
    );
}

#[test]
fn index_rewritten_before_the_read_keeps_the_row() {
    // The compared value must BE the value the row reads. `_9` has exactly ONE
    // static store, so the whole-function staleness oracle
    // (`value_local_is_unstable`) calls it stable — only the use-block prefix
    // scan can see that the store sits BETWEEN the comparison and the read,
    // decoupling the assert from the operation it nominally guards.
    let mut func = guarded_fn(
        true,
        vec![
            assign_at(
                Place::local(9),
                Rvalue::Use(Operand::Constant(ConstValue::Uint(7, 64))),
                0x82,
            ),
            load(7, 1, 9, LOAD_A_ADDR),
        ],
    );
    // Re-point the comparison at `_9` so the index halves match structurally.
    let Some(Statement::Assign { rvalue: Rvalue::BinaryOp(_, lhs, _), .. }) =
        func.body.blocks[0].stmts.get_mut(1)
    else {
        panic!("fixture shape: bb0 stmt 1 is the Lt comparison");
    };
    *lhs = Operand::Copy(Place::local(9));
    let vcs = rvalue_lane_vcs(&func);
    assert_eq!(
        bounds_rows_at(&vcs, LOAD_A_ADDR),
        1,
        "an index rewritten between the comparison and the read must keep its row: {vcs:#?}"
    );
}

#[test]
fn bypass_edge_into_the_guarded_block_keeps_the_row() {
    // Sole entry is part of the binding: a second edge into the guarded block
    // reaches the indexed read WITHOUT the assert having run, so the assert
    // does not cover every execution of the row.
    let mut func = guarded_fn(true, vec![load(7, 1, 3, LOAD_A_ADDR)]);
    func.body.blocks.push(BasicBlock {
        id: BlockId(2),
        stmts: vec![],
        terminator: Terminator::Goto(BlockId(1)),
    });
    let vcs = rvalue_lane_vcs(&func);
    assert_eq!(
        bounds_rows_at(&vcs, LOAD_A_ADDR),
        1,
        "a row reachable around the assert must keep its obligation: {vcs:#?}"
    );
}

#[test]
fn two_candidate_asserts_are_ambiguous_and_never_suppress() {
    // Among multiple `BoundsCheck` asserts targeting one block, target identity
    // cannot say which (if either) guarded a given row — ambiguity keeps it.
    let mut func = guarded_fn(true, vec![load(7, 1, 3, LOAD_A_ADDR)]);
    func.body.blocks.push(BasicBlock {
        id: BlockId(2),
        stmts: vec![],
        terminator: Terminator::Assert {
            unwind: trust_types::UnwindEdge::Unreachable,
            cond: Operand::Copy(Place::local(6)),
            expected: true,
            msg: AssertMessage::BoundsCheck,
            target: BlockId(1),
            span: SourceSpan::binary_address(0x91),
        },
    });
    let vcs = rvalue_lane_vcs(&func);
    assert_eq!(
        bounds_rows_at(&vcs, LOAD_A_ADDR),
        1,
        "multiple candidate asserts are never suppression authority: {vcs:#?}"
    );
}
