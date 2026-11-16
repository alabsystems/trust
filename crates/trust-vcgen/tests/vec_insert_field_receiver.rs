// Regression (VEC-INSERT-FIELD, 2026-10-07): a `Vec` index mutator whose receiver is
// a struct FIELD (`m.rows.insert(0, x)`, trust-ir-conformance `tests/generate/
// refuse.rs:619`) was never charged its index precondition. The region model
// (`generate/vec_region.rs`) resolved only a WHOLE-local base — `&mut v` for a `Vec`
// by value, `&mut (*v)` / `copy v` for a `&mut Vec` parameter — so the receiver
// `_3 = &mut ((*_1).0)` matched no base, the call kept the fail-honest
// `vec-panic-method-index-unmodeled` row, and Level 0 reclassified it to a FAILED
// `Call::insert::panic-freedom-unverified` row. The same call on a local, owned, or
// `&mut Vec` receiver was a proved `SliceBoundsCheck` row.
//
// Measured before the fix (stage 1 snapshot of 7be75e9a80, `vec_insert_front.rs`):
// `0 proved, 1 failed, 1 unknown` for `f(m: &mut M, x) { m.rows.insert(0, x) }`;
// `1 proved` for `g(v: &mut Vec<u32>, x) { v.insert(0, x) }`.
//
// The base is now the field PLACE; the region is still the ROOT's (any write, move,
// drop or `&mut`/raw borrow of any part of the root ends it), and each field path
// names its own length symbol. These rows pin the precision gained AND the
// soundness edges: an unguarded `insert(i)` is refuted, a guard over a SIBLING
// field's length discharges nothing, a mutation of the root before the call keeps the
// fail-honest row, and a path through a `core::cell` type is never charged.
use trust_types::*;
use trust_vcgen::generate_vcs;

#[path = "support/test_router.rs"]
mod test_router;

const INSERT: &str = "alloc::vec::Vec::<u32>::insert";
const LEN: &str = "alloc::vec::Vec::<u32>::len";
const CLEAR: &str = "alloc::vec::Vec::<u32>::clear";
const MK: &str = "t::mk";

fn usize_ty() -> Ty {
    Ty::Int { width: 64, signed: false }
}
fn vec_u32() -> Ty {
    Ty::adt("alloc::vec::Vec<u32>", vec![])
}
fn m_ty() -> Ty {
    Ty::adt("t::M", vec![("rows".into(), vec_u32()), ("cols".into(), vec_u32())])
}
fn cell_m_ty() -> Ty {
    let cell =
        Ty::adt("core::cell::UnsafeCell<alloc::vec::Vec<u32>>", vec![("value".into(), vec_u32())]);
    Ty::adt("t::C", vec![("rows".into(), cell)])
}
fn mut_ref(inner: Ty) -> Ty {
    Ty::Ref { mutable: true, inner: Box::new(inner) }
}
fn shared_ref(inner: Ty) -> Ty {
    Ty::Ref { mutable: false, inner: Box::new(inner) }
}

fn call(callee: &str, args: Vec<Operand>, dest: usize, target: usize, col: usize) -> Terminator {
    Terminator::Call {
        func: callee.to_string(),
        args,
        dest: Place::local(dest),
        target: Some(BlockId(target)),
        span: SourceSpan { col_start: col as u32, ..SourceSpan::default() },
        atomic: None,
        is_unsafe_sig: false,
        callee_identity: None,
        callee_key: None,
        is_foreign: false,
        unwind: UnwindEdge::Unreachable,
    }
}
fn block(id: usize, stmts: Vec<Statement>, terminator: Terminator) -> BasicBlock {
    BasicBlock { id: BlockId(id), stmts, terminator }
}
fn assign(dest: usize, rvalue: Rvalue) -> Statement {
    Statement::Assign { place: Place::local(dest), rvalue, span: SourceSpan::default() }
}
fn field_place(root: usize, deref: bool, fields: &[usize]) -> Place {
    let mut projections = Vec::new();
    if deref {
        projections.push(Projection::Deref);
    }
    projections.extend(fields.iter().map(|&f| Projection::Field(f)));
    Place { local: root, projections }
}
fn borrow_place(dest: usize, place: Place, mutable: bool) -> Statement {
    assign(dest, Rvalue::Ref { mutable, place })
}
fn usize_const(n: u128) -> Operand {
    Operand::Constant(ConstValue::Uint(n, 64))
}
fn copy(l: usize) -> Operand {
    Operand::Copy(Place::local(l))
}
fn mv(l: usize) -> Operand {
    Operand::Move(Place::local(l))
}

/// Locals: 0 ret ()  1 m (`root_ty`)  2 i: usize  3 x: u32  4 &mut Vec (insert recv)
///         5 () (insert result)  6 &Vec (len recv)  7 usize (len)  8 bool (guard)
///         9 &mut Vec (clear recv)  10 () (clear result)  11 u32 (`mk` result)
///         12 Vec (a replacement value)  13 &mut Vec (a reborrow of 4)
fn func(root_ty: Ty, blocks: Vec<BasicBlock>) -> VerifiableFunction {
    let tys = [
        Ty::Unit,
        root_ty,
        usize_ty(),
        Ty::u32(),
        mut_ref(vec_u32()),
        Ty::Unit,
        shared_ref(vec_u32()),
        usize_ty(),
        Ty::Bool,
        mut_ref(vec_u32()),
        Ty::Unit,
        Ty::u32(),
        vec_u32(),
        mut_ref(vec_u32()),
    ];
    VerifiableFunction {
        name: "f".into(),
        def_path: "t::f".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: tys
                .into_iter()
                .enumerate()
                .map(|(index, ty)| LocalDecl { index, ty, name: None })
                .collect(),
            blocks,
            arg_count: 3,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        },
        contracts: Vec::new(),
        preconditions: Vec::new(),
        postconditions: Vec::new(),
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// `m.<fields>.insert(idx, x)` as block `id`, returning at `id + 1`.
fn insert_at(id: usize, deref: bool, fields: &[usize], idx: Operand, col: usize) -> BasicBlock {
    block(
        id,
        vec![borrow_place(4, field_place(1, deref, fields), true)],
        call(INSERT, vec![mv(4), idx, copy(3)], 5, id + 1, col),
    )
}

/// `if i <= m.<len_fields>.len() { m.<ins_fields>.insert(i, x) }` over an `&mut M`.
fn guarded_insert(len_fields: &[usize], ins_fields: &[usize]) -> VerifiableFunction {
    func(
        mut_ref(m_ty()),
        vec![
            block(
                0,
                vec![borrow_place(6, field_place(1, true, len_fields), false)],
                call(LEN, vec![mv(6)], 7, 1, 1),
            ),
            block(
                1,
                vec![assign(8, Rvalue::BinaryOp(BinOp::Le, copy(2), copy(7)))],
                Terminator::SwitchInt {
                    discr: mv(8),
                    targets: vec![(0, BlockId(3))],
                    otherwise: BlockId(2),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            ),
            insert_at(2, true, ins_fields, copy(2), 40),
            block(3, vec![], Terminator::Return),
        ],
    )
}

fn vec_panic_unknowns(vcs: &[VerificationCondition]) -> usize {
    vcs.iter()
        .filter(|vc| {
            matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. }
                if kind == "vec-panic-method-index-unmodeled")
        })
        .count()
}

/// The solver verdict of every `SliceBoundsCheck` row.
fn slice_bounds_verdicts(f: VerifiableFunction) -> Vec<VerificationResult> {
    std::thread::Builder::new()
        .stack_size(32 * 1024 * 1024)
        .spawn(move || {
            let rows: Vec<VerificationCondition> = generate_vcs(&f)
                .into_iter()
                .filter(|vc| matches!(vc.kind, VcKind::SliceBoundsCheck))
                .collect();
            let router = test_router::deterministic_test_router();
            router.verify_all(&rows).into_iter().map(|(_, verdict)| verdict).collect()
        })
        .expect("spawn solver thread")
        .join()
        .expect("solver thread must not panic")
}

fn charged(f: &VerifiableFunction) -> Vec<BlockId> {
    trust_vcgen::vec_mutator_charged_blocks(f)
}

#[test]
fn field_of_mut_param_insert_front_is_charged_and_proved() {
    // `fn f(m: &mut M, x: u32) { m.rows.insert(0, x) }` — the reproducer, MIR verbatim
    // in shape: `_4 = &mut ((*_1).0); insert(move _4, const 0, copy _3)`.
    let f = func(
        mut_ref(m_ty()),
        vec![insert_at(0, true, &[0], usize_const(0), 5), block(1, vec![], Terminator::Return)],
    );
    assert_eq!(charged(&f), vec![BlockId(0)], "a field receiver is a region base");
    assert_eq!(vec_panic_unknowns(&generate_vcs(&f)), 0, "no fail-honest row once charged");
    let verdicts = slice_bounds_verdicts(f);
    assert_eq!(verdicts.len(), 1, "exactly one charged row: {verdicts:?}");
    assert!(
        matches!(verdicts[0], VerificationResult::Proved { .. }),
        "`0 > L0` is UNSAT for every length; got {:?}",
        verdicts[0]
    );
}

#[test]
fn field_of_owned_struct_insert_front_is_charged_and_proved() {
    // `fn h(mut m: M, x: u32) { m.rows.insert(0, x) }`: `_4 = &mut (_1.0)`.
    let f = func(
        m_ty(),
        vec![insert_at(0, false, &[0], usize_const(0), 5), block(1, vec![], Terminator::Return)],
    );
    assert_eq!(charged(&f), vec![BlockId(0)]);
    let verdicts = slice_bounds_verdicts(f);
    assert!(
        matches!(verdicts.as_slice(), [VerificationResult::Proved { .. }]),
        "owned-struct field insert(0) must prove; got {verdicts:?}"
    );
}

#[test]
fn unguarded_field_insert_is_refuted_never_proved() {
    let f = func(
        mut_ref(m_ty()),
        vec![insert_at(0, true, &[0], copy(2), 5), block(1, vec![], Terminator::Return)],
    );
    assert_eq!(charged(&f), vec![BlockId(0)]);
    let verdicts = slice_bounds_verdicts(f);
    assert!(
        matches!(verdicts.as_slice(), [VerificationResult::Failed { .. }]),
        "an unguarded `m.rows.insert(i, x)` must be REFUTED (`i > L0` is satisfiable); got \
         {verdicts:?}"
    );
}

#[test]
fn same_field_len_guard_discharges_the_field_insert() {
    let f = guarded_insert(&[0], &[0]);
    assert_eq!(charged(&f), vec![BlockId(2)]);
    let verdicts = slice_bounds_verdicts(f);
    assert!(
        matches!(verdicts.as_slice(), [VerificationResult::Proved { .. }]),
        "`if i <= m.rows.len() {{ m.rows.insert(i, x) }}` is in bounds; got {verdicts:?}"
    );
}

#[test]
fn sibling_field_len_guard_never_discharges_the_field_insert() {
    // SOUNDNESS: `if i <= m.cols.len() { m.rows.insert(i, x) }` panics when `rows` is
    // shorter than `cols`. The two fields must not share a length symbol.
    let f = guarded_insert(&[1], &[0]);
    assert_eq!(charged(&f), vec![BlockId(2)]);
    let verdicts = slice_bounds_verdicts(f);
    assert!(
        matches!(verdicts.as_slice(), [VerificationResult::Failed { .. }]),
        "a guard over a SIBLING field's length must not prove the insert; got {verdicts:?}"
    );
}

#[test]
fn a_mutation_of_the_root_before_the_insert_keeps_the_fail_honest_row() {
    // `m.cols.clear(); m.rows.insert(0, x)` — the region is the ROOT's, so a `&mut`
    // borrow of ANY part of `*m` ends it (conservative: a sibling cannot resize `rows`,
    // but the region does not distinguish them).
    let f = func(
        mut_ref(m_ty()),
        vec![
            block(
                0,
                vec![borrow_place(9, field_place(1, true, &[1]), true)],
                call(CLEAR, vec![mv(9)], 10, 1, 1),
            ),
            insert_at(1, true, &[0], usize_const(0), 5),
            block(2, vec![], Terminator::Return),
        ],
    );
    assert!(charged(&f).is_empty(), "the insert follows a mutation of its root");
    assert_eq!(vec_panic_unknowns(&generate_vcs(&f)), 1, "it keeps the fail-honest row");
}

#[test]
fn a_field_path_through_a_cell_is_never_charged() {
    // `m.rows.get_mut().insert(0, x)` spelled as the place `(*_1).0.0` through an
    // `UnsafeCell`: a SHARED borrow of the root could resize this `Vec`, and the region
    // does not count shared borrows, so the path is refused outright.
    let f = func(
        mut_ref(cell_m_ty()),
        vec![insert_at(0, true, &[0, 0], usize_const(0), 5), block(1, vec![], Terminator::Return)],
    );
    assert!(charged(&f).is_empty(), "a path through core::cell is no region base");
    assert_eq!(vec_panic_unknowns(&generate_vcs(&f)), 1);
}

#[test]
fn a_field_of_a_shared_ref_param_is_never_charged() {
    // A `&M` root is not a region root (no `&mut` path can be borrowed from it in safe
    // code; this pins that the eligibility gate still refuses it).
    let f = func(
        shared_ref(m_ty()),
        vec![insert_at(0, true, &[0], usize_const(0), 5), block(1, vec![], Terminator::Return)],
    );
    assert!(charged(&f).is_empty());
}

// ---------------------------------------------------------------------------------
// VEC-INSERT-FIELD-2: the receiver borrow RESERVED in an earlier block. When the
// inserted value is computed by a call (`m.rows.insert(0, mk(k))`, the real
// `refuse.rs:619` site), MIR takes the two-phase borrow before that call and
// activates it a block later:
//   bb0: { _4 = &mut ((*_1).0); _11 = mk(copy _3) -> bb1 }
//   bb1: { _5 = Vec::insert(move _4, idx, move _11) -> bb2 }
// Measured before (branch stage1 at e4adfeb86f): `0 proved, 1 failed, 1 unknown` for
// `m.drop_glue.insert(0, mk(k))`, `module.drop_glue.insert(0, mk(k))` (owned) and
// `v.insert(0, mk(k))` with `mut v: Vec<E>` alike.

/// `root.<fields>.insert(idx, mk(x))`: the reservation in bb0, the call in bb1.
fn reserved_insert(root_ty: Ty, deref: bool, fields: &[usize], idx: Operand) -> VerifiableFunction {
    func(
        root_ty,
        vec![
            block(
                0,
                vec![borrow_place(4, field_place(1, deref, fields), true)],
                call(MK, vec![copy(3)], 11, 1, 1),
            ),
            block(1, vec![], call(INSERT, vec![mv(4), idx, mv(11)], 5, 2, 40)),
            block(2, vec![], Terminator::Return),
        ],
    )
}

#[test]
fn reserved_field_receiver_of_mut_param_is_charged_and_proved() {
    let f = reserved_insert(mut_ref(m_ty()), true, &[0], usize_const(0));
    assert_eq!(charged(&f), vec![BlockId(1)], "the reservation is taken at its activation");
    assert_eq!(vec_panic_unknowns(&generate_vcs(&f)), 0);
    let verdicts = slice_bounds_verdicts(f);
    assert!(
        matches!(verdicts.as_slice(), [VerificationResult::Proved { .. }]),
        "`m.rows.insert(0, mk(k))` must prove; got {verdicts:?}"
    );
}

#[test]
fn reserved_field_receiver_of_owned_struct_is_charged_and_proved() {
    let f = reserved_insert(m_ty(), false, &[0], usize_const(0));
    assert_eq!(charged(&f), vec![BlockId(1)]);
    let verdicts = slice_bounds_verdicts(f);
    assert!(
        matches!(verdicts.as_slice(), [VerificationResult::Proved { .. }]),
        "`module.rows.insert(0, mk(k))` must prove; got {verdicts:?}"
    );
}

#[test]
fn reserved_whole_owned_vec_receiver_is_charged_and_proved() {
    // `fn g(mut v: Vec<u32>, k) { v.insert(0, mk(k)) }`: `_4 = &mut _1` in bb0.
    let f = reserved_insert(vec_u32(), false, &[], usize_const(0));
    assert_eq!(charged(&f), vec![BlockId(1)]);
    let verdicts = slice_bounds_verdicts(f);
    assert!(
        matches!(verdicts.as_slice(), [VerificationResult::Proved { .. }]),
        "`v.insert(0, mk(k))` on an owned Vec must prove; got {verdicts:?}"
    );
}

#[test]
fn reserved_unguarded_insert_is_refuted_never_proved() {
    let f = reserved_insert(mut_ref(m_ty()), true, &[0], copy(2));
    assert_eq!(charged(&f), vec![BlockId(1)]);
    let verdicts = slice_bounds_verdicts(f);
    assert!(
        matches!(verdicts.as_slice(), [VerificationResult::Failed { .. }]),
        "`m.rows.insert(i, mk(k))` must be REFUTED; got {verdicts:?}"
    );
}

#[test]
fn a_reservation_used_before_its_activation_is_never_charged() {
    // SOUNDNESS: `_13 = &mut (*_4); clear(move _13)` in the reservation block empties
    // the Vec through the reserved borrow before the insert; the length at the call is
    // no longer the region's. The receiver is mentioned outside the call: refused.
    let f = func(
        mut_ref(m_ty()),
        vec![
            block(
                0,
                vec![
                    borrow_place(4, field_place(1, true, &[0]), true),
                    borrow_place(13, field_place(4, true, &[]), true),
                ],
                call(CLEAR, vec![mv(13)], 10, 1, 1),
            ),
            block(1, vec![], call(INSERT, vec![mv(4), copy(2), copy(3)], 5, 2, 40)),
            block(2, vec![], Terminator::Return),
        ],
    );
    assert!(charged(&f).is_empty(), "the reserved borrow is used before the insert");
    assert_eq!(vec_panic_unknowns(&generate_vcs(&f)), 1);
}

#[test]
fn a_root_mutation_between_reservation_and_activation_is_never_charged() {
    // bb0 reserves `rows`; bb1 `clear`s `cols` (a disjoint field, borrowck accepts it);
    // bb2 activates. bb1 is in `Mut(root)` and reaches the call: not in the region.
    let f = func(
        mut_ref(m_ty()),
        vec![
            block(
                0,
                vec![borrow_place(4, field_place(1, true, &[0]), true)],
                call(MK, vec![copy(3)], 11, 1, 1),
            ),
            block(
                1,
                vec![borrow_place(9, field_place(1, true, &[1]), true)],
                call(CLEAR, vec![mv(9)], 10, 2, 2),
            ),
            block(2, vec![], call(INSERT, vec![mv(4), usize_const(0), mv(11)], 5, 3, 40)),
            block(3, vec![], Terminator::Return),
        ],
    );
    assert!(charged(&f).is_empty());
}

#[test]
fn a_reservation_block_that_also_mutates_the_root_is_never_charged() {
    // bb0 both reserves `rows` AND writes `(*_1).0` (after the borrow, as a
    // reservation-block mutation the move to the call would hide): refused.
    let f = func(
        mut_ref(m_ty()),
        vec![
            block(
                0,
                vec![
                    borrow_place(4, field_place(1, true, &[0]), true),
                    Statement::Assign {
                        place: field_place(1, true, &[0]),
                        rvalue: Rvalue::Use(mv(12)),
                        span: SourceSpan::default(),
                    },
                ],
                call(MK, vec![copy(3)], 11, 1, 1),
            ),
            block(1, vec![], call(INSERT, vec![mv(4), copy(2), mv(11)], 5, 2, 40)),
            block(2, vec![], Terminator::Return),
        ],
    );
    assert!(charged(&f).is_empty());
}

#[test]
fn a_reserved_insert_on_a_cycle_is_never_charged() {
    // bb1 loops back to bb0: the second activation sees the first insert's length.
    let f = func(
        mut_ref(m_ty()),
        vec![
            block(
                0,
                vec![borrow_place(4, field_place(1, true, &[0]), true)],
                call(MK, vec![copy(3)], 11, 1, 1),
            ),
            block(1, vec![], call(INSERT, vec![mv(4), copy(2), mv(11)], 5, 0, 40)),
        ],
    );
    assert!(charged(&f).is_empty());
}

#[test]
fn sibling_field_len_guard_never_discharges_when_both_fields_are_charged() {
    // SOUNDNESS (per-path `L0`): `n = m.cols.len(); if i <= n { m.rows.insert(i, x) }
    // else { m.cols.insert(0, x) }`. Both fields are charged bases, so BOTH get region
    // facts; were the two paths to share one length symbol, `n == L0(cols) == L0(rows)`
    // would prove the rows insert, which panics when `rows` is shorter than `cols`.
    // (The single-charge sibling test above cannot see that: `cols` gets no fact there.)
    let f = func(
        mut_ref(m_ty()),
        vec![
            block(
                0,
                vec![borrow_place(6, field_place(1, true, &[1]), false)],
                call(LEN, vec![mv(6)], 7, 1, 1),
            ),
            block(
                1,
                vec![assign(8, Rvalue::BinaryOp(BinOp::Le, copy(2), copy(7)))],
                Terminator::SwitchInt {
                    discr: mv(8),
                    targets: vec![(0, BlockId(3))],
                    otherwise: BlockId(2),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            ),
            block(
                2,
                vec![borrow_place(4, field_place(1, true, &[0]), true)],
                call(INSERT, vec![mv(4), copy(2), copy(3)], 5, 4, 40),
            ),
            block(
                3,
                vec![borrow_place(9, field_place(1, true, &[1]), true)],
                call(INSERT, vec![mv(9), usize_const(0), copy(3)], 10, 4, 60),
            ),
            block(4, vec![], Terminator::Return),
        ],
    );
    assert_eq!(charged(&f), vec![BlockId(2), BlockId(3)], "both field inserts are charged");
    let rows: Vec<VerificationCondition> = generate_vcs(&f)
        .into_iter()
        .filter(|vc| matches!(vc.kind, VcKind::SliceBoundsCheck))
        .collect();
    assert_eq!(rows.len(), 2, "{rows:?}");
    let verdicts = slice_bounds_verdicts(f);
    // The rows insert (col 40) must be refuted; the cols insert(0) proves.
    let failed = verdicts.iter().filter(|v| matches!(v, VerificationResult::Failed { .. })).count();
    let proved = verdicts.iter().filter(|v| matches!(v, VerificationResult::Proved { .. })).count();
    assert_eq!(
        (failed, proved),
        (1, 1),
        "the rows insert guarded by `cols.len()` must be REFUTED; got {verdicts:?}"
    );
}

#[test]
fn a_root_write_in_the_call_block_before_the_insert_is_never_charged() {
    // `(*_1).0 = move _12; _4 = &mut ((*_1).0); insert(move _4, i, x)` in ONE block,
    // after a `len()` read of the old `rows`: the call block is in the region (only its
    // successors are tainted), so the same-block pre-call root-write check is the only
    // thing that keeps `i <= old_len` from discharging the insert into the NEW Vec.
    let f = func(
        mut_ref(m_ty()),
        vec![
            block(
                0,
                vec![borrow_place(6, field_place(1, true, &[0]), false)],
                call(LEN, vec![mv(6)], 7, 1, 1),
            ),
            block(
                1,
                vec![assign(8, Rvalue::BinaryOp(BinOp::Le, copy(2), copy(7)))],
                Terminator::SwitchInt {
                    discr: mv(8),
                    targets: vec![(0, BlockId(3))],
                    otherwise: BlockId(2),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            ),
            block(
                2,
                vec![
                    Statement::Assign {
                        place: field_place(1, true, &[0]),
                        rvalue: Rvalue::Use(mv(12)),
                        span: SourceSpan::default(),
                    },
                    borrow_place(4, field_place(1, true, &[0]), true),
                ],
                call(INSERT, vec![mv(4), copy(2), copy(3)], 5, 3, 40),
            ),
            block(3, vec![], Terminator::Return),
        ],
    );
    assert!(charged(&f).is_empty(), "the root is written in the call block before the call");
    assert_eq!(vec_panic_unknowns(&generate_vcs(&f)), 1);
}
