// Trust (W4 fix round 3, 2026-09-29): the `Vec` region's definition-block exemption
// covers the DEFINITION, not a `&mut`/raw borrow of the base that the same block leaves
// open for a later block (`vec_region::def_block_borrows`).
//
// THE DEFECT (round-r2 adversarial probe v2p01, and thirteen siblings). In
//     let mut v = w; let k;
//     v.truncate({ std::hint::black_box(0u8); k = v.len(); 0 });
//     if i < k { v.remove(i) } else { 0 }
// the two-phase autoref reservation `_5 = &mut v` sits in `v`'s definition block,
// which was exempt from the taint starts as a WHOLE block. The call that activates it,
// `truncate(move _5, 0)`, mentions only `_5`, so it was in no mutation block; the
// `v.len()` read between the two minted `k == L0` at the PRE-truncate length, and
// `v.remove(i)` was charged against that stale `L0` — `proved SliceBoundsCheck`,
// kernel-certified, on `0.10.0+g81274d5b9`; `f(vec![1, 2, 3], 1)` panics "removal
// index (is 1) should be < len (is 0)".
//
// These rows drive the region on the hand-built MIR of that shape and its neighbours,
// by the public producers (`vec_region_definitions`, `vec_mutator_charged_blocks`):
//   * the reservation's window mints NO length fact (the hole);
//   * a single activation off every cycle keeps the region AFTER it (`v.push(v.len())`
//     then a guarded remove, probe v2p17 — the widening this lane exists for);
//   * a reservation used by two blocks, or by one on a cycle, ends the region at each;
//   * a raw pointer taken in the definition block leaves no region at all;
//   * a reservation the definition block's own terminator consumes is unchanged.
//
// The second half (VEC-REGION-DEF-BLOCK-STASH-1, 2026-10-13) drives the same producers on
// REAL extracted MIR: a definition-block borrow handed to a callee that could keep it
// leaves no region (see the section header below).

use trust_types::{
    BasicBlock, BinOp, BlockId, CalleeKey, ConstValue, Formula, LocalDecl, Operand, Place,
    Projection, Rvalue, SourceSpan, Statement, Terminator, Ty, UnwindEdge, VerifiableBody,
    VerifiableFunction,
};

use super::vec_region_no_mutator_tests::sub_rows;
use super::{VecRegion, vec_mutator_charged_blocks, vec_region_definitions};

const LEN: &str = "alloc::vec::Vec::<u32>::len";
const REMOVE: &str = "alloc::vec::Vec::<u32>::remove";
const TRUNCATE: &str = "alloc::vec::Vec::<u32>::truncate";
const PUSH: &str = "alloc::vec::Vec::<u32>::push";
const BLACK_BOX: &str = "core::hint::black_box::<u8>";

fn usize_ty() -> Ty {
    Ty::Int { width: 64, signed: false }
}
fn vec_u32() -> Ty {
    Ty::adt("alloc::vec::Vec<u32>", vec![])
}
fn mut_vec() -> Ty {
    Ty::Ref { mutable: true, inner: Box::new(vec_u32()) }
}
fn shared_vec() -> Ty {
    Ty::Ref { mutable: false, inner: Box::new(vec_u32()) }
}

/// The key the extractor mints for `callee`. `fixture_key` marks a callee resident in a
/// real sysroot crate only when its tagged vocabulary names it, but the extractor's
/// residency verdict is per CRATE: every `alloc::`/`core::` callee of these bodies carries
/// `krate_is_real_sysroot: true` (measured on the real dumps below: `push_then_len.json`'s
/// `alloc::vec::Vec::<u8>::push` has it, with no tag). VEC-REGION-DEF-BLOCK-STASH-1
/// credits a callee handed a definition-block borrow on that verdict only, so a `push`
/// or `truncate` keyed by `fixture_key` alone would read as a dependency callee.
fn extracted_key(callee: &str) -> Option<CalleeKey> {
    let mut key = crate::sep_engine::tests::fixture_key(callee)?;
    if callee.starts_with("alloc::") || callee.starts_with("core::") {
        key.krate_is_real_sysroot = true;
    }
    Some(key)
}

fn call(callee: &str, args: Vec<Operand>, dest: usize, target: usize) -> Terminator {
    Terminator::Call {
        func: callee.to_string(),
        args,
        dest: Place::local(dest),
        target: Some(BlockId(target)),
        span: SourceSpan::default(),
        atomic: None,
        is_unsafe_sig: false,
        callee_identity: None,
        callee_key: extracted_key(callee),
        is_foreign: false,
        unwind: UnwindEdge::Unreachable,
    }
}

fn assign(dest: usize, rvalue: Rvalue) -> Statement {
    Statement::Assign { place: Place::local(dest), rvalue, span: SourceSpan::default() }
}
fn borrow(dest: usize, of: usize, mutable: bool) -> Statement {
    assign(dest, Rvalue::Ref { mutable, place: Place::local(of) })
}
fn usize_const(n: u128) -> Operand {
    Operand::Constant(ConstValue::Uint(n, 64))
}
fn block(id: usize, stmts: Vec<Statement>, terminator: Terminator) -> BasicBlock {
    BasicBlock { id: BlockId(id), stmts, terminator }
}

/// Locals shared by every body below.
///   0 ret: u32   1 w: Vec<u32>   2 i: usize   3 v: Vec<u32>   4 (): ()
///   5 reservation: &mut Vec     6 black_box result: u8        7 k: usize
///   8 &Vec (window len)         9 bool                        10 &mut Vec (remove)
///   11 &Vec (post len)          12 usize (post len)           13 &mut Vec (2nd use)
///   14 *mut Vec                 15 u32 (pushed value)
fn locals() -> Vec<LocalDecl> {
    let tys = [
        Ty::u32(),
        vec_u32(),
        usize_ty(),
        vec_u32(),
        Ty::Unit,
        mut_vec(),
        Ty::Int { width: 8, signed: false },
        usize_ty(),
        shared_vec(),
        Ty::Bool,
        mut_vec(),
        shared_vec(),
        usize_ty(),
        mut_vec(),
        Ty::RawPtr { mutable: true, pointee: Box::new(vec_u32()) },
        Ty::u32(),
    ];
    tys.into_iter().enumerate().map(|(index, ty)| LocalDecl { index, ty, name: None }).collect()
}

fn func(blocks: Vec<BasicBlock>) -> VerifiableFunction {
    VerifiableFunction {
        name: "f".into(),
        def_path: "test::vec_region_twophase".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: locals(),
            blocks,
            arg_count: 2,
            return_ty: Ty::u32(),
            datatype_defs: Default::default(),
        },
        contracts: Vec::new(),
        preconditions: Vec::new(),
        postconditions: Vec::new(),
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// `if i < <cond> { v.remove(i) } else { 0 }` from block `at`, returning at `at + 3`.
fn guarded_remove(at: usize, cond: usize) -> Vec<BasicBlock> {
    vec![
        block(
            at,
            vec![assign(
                9,
                Rvalue::BinaryOp(
                    BinOp::Lt,
                    Operand::Copy(Place::local(2)),
                    Operand::Copy(Place::local(cond)),
                ),
            )],
            Terminator::SwitchInt {
                discr: Operand::Move(Place::local(9)),
                targets: vec![(0, BlockId(at + 2))],
                otherwise: BlockId(at + 1),
                exhaustive_enum_unreachable: false,
                span: SourceSpan::default(),
            },
        ),
        block(
            at + 1,
            vec![borrow(10, 3, true)],
            call(
                REMOVE,
                vec![Operand::Move(Place::local(10)), Operand::Copy(Place::local(2))],
                0,
                at + 3,
            ),
        ),
        block(
            at + 2,
            vec![assign(0, Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 32))))],
            Terminator::Goto(BlockId(at + 3)),
        ),
        block(at + 3, vec![], Terminator::Return),
    ]
}

/// The probe's MIR, verbatim in shape (`-Zunpretty=mir` of v2p01):
///   bb0: v = move w; _5 = &mut v; _6 = black_box(0) -> bb1
///   bb1: _8 = &v; k = len(move _8) -> bb2
///   bb2: _4 = truncate(move _5, 0) -> bb3
///   bb3..: if i < k { v.remove(i) } else { 0 }
fn twophase_truncate() -> VerifiableFunction {
    let mut blocks = vec![
        block(
            0,
            vec![assign(3, Rvalue::Use(Operand::Move(Place::local(1)))), borrow(5, 3, true)],
            call(BLACK_BOX, vec![Operand::Constant(ConstValue::Uint(0, 8))], 6, 1),
        ),
        block(1, vec![borrow(8, 3, false)], call(LEN, vec![Operand::Move(Place::local(8))], 7, 2)),
        block(
            2,
            vec![],
            call(TRUNCATE, vec![Operand::Move(Place::local(5)), usize_const(0)], 4, 3),
        ),
    ];
    blocks.extend(guarded_remove(3, 7));
    func(blocks)
}

fn mentions_local(f: &Formula, name_fragment: &str) -> bool {
    format!("{f:?}").contains(name_fragment)
}

#[test]
fn a_twophase_reservation_window_mints_no_stale_length_fact() {
    let f = twophase_truncate();
    let facts = vec_region_definitions(&f);
    // BEFORE: `{bb2: [k == __trust_vec_region_len_3]}` — the pre-truncate length.
    assert!(
        facts.values().flatten().all(|fact| !mentions_local(fact, "__trust_vec_region_len_3")),
        "a length read between the reservation and its activation must not state L0: {facts:?}"
    );
    assert!(facts.is_empty(), "no region fact site exists after the truncate: {facts:?}");
    let region = VecRegion::build(&f, 3).expect("a Vec local with one definition");
    assert!(!region.is_clean(1), "the reservation window (the len block) is outside the region");
    assert!(!region.is_clean(2), "the activating truncate block is outside the region");
}

#[test]
fn a_single_activation_keeps_the_region_after_it() {
    // `v.push(v.len() as u32); if i < v.len() { v.remove(i) }` (probe v2p17):
    //   bb0: v = move w; _5 = &mut v; _8 = &v; k = len(move _8) -> bb1
    //   bb1: _15 = k as u32; _4 = push(move _5, move _15) -> bb2
    //   bb2: _11 = &v; _12 = len(move _11) -> bb3
    //   bb3..: if i < _12 { v.remove(i) } else { 0 }
    let mut blocks = vec![
        block(
            0,
            vec![
                assign(3, Rvalue::Use(Operand::Move(Place::local(1)))),
                borrow(5, 3, true),
                borrow(8, 3, false),
            ],
            call(LEN, vec![Operand::Move(Place::local(8))], 7, 1),
        ),
        block(
            1,
            vec![assign(15, Rvalue::Cast(Operand::Move(Place::local(7)), Ty::u32()))],
            call(PUSH, vec![Operand::Move(Place::local(5)), Operand::Move(Place::local(15))], 4, 2),
        ),
        block(
            2,
            vec![borrow(11, 3, false)],
            call(LEN, vec![Operand::Move(Place::local(11))], 12, 3),
        ),
    ];
    blocks.extend(guarded_remove(3, 12));
    let f = func(blocks);
    assert_eq!(vec_mutator_charged_blocks(&f), vec![BlockId(4)], "the remove stays charged");
    let facts = vec_region_definitions(&f);
    let post = facts.get(&BlockId(3)).expect("the post-push len fact");
    assert!(post.iter().any(|fact| mentions_local(fact, "__trust_vec_region_len_3")), "{facts:?}");
    assert!(!facts.contains_key(&BlockId(1)), "the definition block's own len read states nothing");
}

#[test]
fn a_reservation_used_by_two_blocks_ends_the_region_at_each() {
    // As the probe, but the reservation is reborrowed in bb2 and the truncate is its
    // own block (bb2 -> bb6 -> bb3): two uses, so each is an ordinary mutation block.
    let mut f = twophase_truncate();
    f.body.blocks[2] = block(
        2,
        vec![assign(
            13,
            Rvalue::Ref {
                mutable: true,
                place: Place { local: 5, projections: vec![Projection::Deref] },
            },
        )],
        Terminator::Goto(BlockId(7)),
    );
    f.body.blocks.push(block(
        7,
        vec![],
        call(TRUNCATE, vec![Operand::Move(Place::local(13)), usize_const(0)], 4, 3),
    ));
    assert!(
        vec_mutator_charged_blocks(&f).is_empty(),
        "the remove after the truncate is uncharged"
    );
    let region = VecRegion::build(&f, 3).expect("a Vec local with one definition");
    assert!(!region.is_clean(4), "the remove block is outside the region");
}

#[test]
fn an_activation_on_a_cycle_ends_the_region() {
    // bb2 (the truncate) -> bb7 -> back to bb1: the activation re-reaches itself.
    let mut f = twophase_truncate();
    f.body.blocks[2].terminator =
        call(TRUNCATE, vec![Operand::Move(Place::local(5)), usize_const(0)], 4, 7);
    f.body.blocks.push(block(
        7,
        vec![],
        Terminator::SwitchInt {
            discr: Operand::Copy(Place::local(9)),
            targets: vec![(0, BlockId(1))],
            otherwise: BlockId(3),
            exhaustive_enum_unreachable: false,
            span: SourceSpan::default(),
        },
    ));
    assert!(
        vec_mutator_charged_blocks(&f).is_empty(),
        "the remove after a looping truncate is uncharged"
    );
}

#[test]
fn a_raw_pointer_taken_in_the_definition_block_leaves_no_region() {
    // `let p: *mut Vec<u32> = &mut v;` in the definition block (probe v2p16).
    let mut f = twophase_truncate();
    f.body.blocks[0].stmts.push(assign(
        14,
        Rvalue::AddressOf(true, Place { local: 5, projections: vec![Projection::Deref] }),
    ));
    assert!(VecRegion::build(&f, 3).is_none());
    assert!(vec_mutator_charged_blocks(&f).is_empty());
    assert!(vec_region_definitions(&f).is_empty());
}

#[test]
fn a_reservation_the_definition_block_consumes_is_unchanged() {
    // `let mut v = w; v.push(1); if i < v.len() { v.remove(i) }`: the push is the
    // definition block's own terminator, so the region starts after it, as before.
    let mut blocks = vec![
        block(
            0,
            vec![assign(3, Rvalue::Use(Operand::Move(Place::local(1)))), borrow(5, 3, true)],
            call(
                PUSH,
                vec![Operand::Move(Place::local(5)), Operand::Constant(ConstValue::Uint(1, 32))],
                4,
                1,
            ),
        ),
        block(
            1,
            vec![borrow(11, 3, false)],
            call(LEN, vec![Operand::Move(Place::local(11))], 12, 2),
        ),
        block(2, vec![], Terminator::Goto(BlockId(3))),
    ];
    blocks.extend(guarded_remove(3, 12));
    let f = func(blocks);
    assert_eq!(vec_mutator_charged_blocks(&f), vec![BlockId(4)]);
    assert!(vec_region_definitions(&f).contains_key(&BlockId(2)));
}

// ---------------------------------------------------------------------------------
// VEC-REGION-DEF-BLOCK-STASH-1 (2026-10-13): a definition-block `&mut v` handed to a
// callee that could keep it leaves NO region for `v`.
//
// THE MISCOMPILE. With a verify-off dependency
//
// ```text
// static mut P: *mut Vec<u8> = std::ptr::null_mut();
// pub fn stash(v: &mut Vec<u8>) { unsafe { P = v as *mut Vec<u8>; } }
// pub fn clear_it() { unsafe { (*P).clear(); } }
// ```
//
// `f1` below has no `unsafe` of its own and no UB under Stacked or Tree Borrows (the
// scout's argument; not run under Miri). Its
// definition block `bb0: { _2 = move _1; _4 = &mut _2; _3 = stash(copy _4) -> bb1 }` was
// `Closed` (a `()` result, the terminator the only use), so the region started at bb1;
// `clear_it()` names neither `v` nor `_4`, so both `len` reads got `_n == L0` and
// `v.len() - 1` was proved, clean-kernel Certified, and its overflow check ELIDED by the
// advisory build: `f1(vec![1, 2, 3])` returned 18446744073709551615 where rustc panics
// (stage 1 of wave 25, `scratchpad/stage1-w25f`, `TRUST_ELIDE: elided 1`). `f1b` adds a
// charged `v.remove(0)` and reached the same false proof before wave 25.
//
// The four `stash_*` siblings reach the same stash through a SYSROOT callee, so a
// callee-identity gate alone leaves them open; each also built `elided 1` and printed
// 18446744073709551615 on `stage1-w25f` (stock rustc: "attempt to subtract with
// overflow", exit 101), with a dependency adding
// `pub fn stash_first(vv: &mut Vec<&mut Vec<u8>>)` (stash `vv[0]`):
//   * `stash_vv_push`: `vv.push(&mut v); stash_first(&mut vv)` (`Vec::push` stores the
//     borrow in another argument's referent);
//   * `stash_option_map`: `Some(&mut v).map(stash)` (`Option::map` hands it to a fn item);
//   * `stash_drop_wrapper`: `drop(W(&mut v))`, `W`'s user `Drop` calls `stash(self.0)`;
//   * `stash_scope_wrapper`: `{ let _w = W(&mut v); }`, the same glue run by a MIR `Drop`.
//
// The MIR under `tests/fixtures/vec_region_no_mutator/` (`stash_*`, `push_*`,
// `truncate_then_fresh_remove`) is `-Ztrust-dump=mir-only:<dir>` output of
// `scratchpad/stage1-w25f` (`--edition 2021 -Ztrust-verify=on -Ztrust-policy=advisory
// -Coverflow-checks=on`, the dependencies built `-Ztrust-verify=off`), re-serialized
// without whitespace; spans name the probe files `stash_body.rs` and `extra.rs`:
//
// ```text
// // stash_body.rs (--crate-type lib)
// pub fn f1(w: Vec<u8>) -> usize { let mut v = w; stdep::stash(&mut v);
//     if v.len() == 0 { return 0; } stdep::clear_it(); v.len() - 1 }
// pub fn f1b(w: Vec<u8>) -> usize { let mut v = w; stdep::stash(&mut v);
//     if v.len() == 0 { return 0; } stdep::clear_it(); let r = v.len() - 1;
//     if r > 1000 { v.remove(0); } r }
// pub fn push_then_len(w: Vec<u8>) -> usize { let mut v = w; v.push(1);
//     if !v.is_empty() { v.len() - 1 } else { 0 } }
// pub fn push_len_then_remove(w: Vec<u32>, i: usize) -> u32 { let mut v = w;
//     v.push(v.len() as u32); if i < v.len() { v.remove(i) } else { 0 } }
// pub fn truncate_then_fresh_remove(w: Vec<u32>, i: usize) -> u32 { let mut v = w; let k;
//     v.truncate({ std::hint::black_box(0u8); k = v.len(); 0 });
//     if i < v.len() { v.remove(i) } else { k as u32 } }
// // extra.rs (bin)
// pub struct W<'a>(pub &'a mut Vec<u8>);
// impl Drop for W<'_> { fn drop(&mut self) { lane1dep::stash(self.0) } }
// pub fn vv_push(w: Vec<u8>) -> usize { let mut vv: Vec<&mut Vec<u8>> = Vec::new();
//     let mut v = w; vv.push(&mut v); lane1dep::stash_first(&mut vv);
//     if v.len() == 0 { return 0; } lane1dep::clear_it(); v.len() - 1 }
// pub fn drop_wrapper(..)  { let mut v = w; drop(W(&mut v)); <same tail> }
// pub fn scope_wrapper(..) { let mut v = w; { let _w = W(&mut v); } <same tail> }
// pub fn option_map(..)    { let mut v = w; Some(&mut v).map(lane1dep::stash); <same tail> }
// ```
//
// (one function per line here; the dumped spans index the multi-line originals).
//
// BEFORE (this fix reverted): every `stash_*` body has a region, facts at both `len`
// targets, and its `- 1` row PROVED by the in-process ay; `f1b`'s remove is charged.

const STASH_F1: &str = include_str!("../../tests/fixtures/vec_region_no_mutator/stash_f1.json");
const STASH_F1B: &str = include_str!("../../tests/fixtures/vec_region_no_mutator/stash_f1b.json");
const STASH_VV_PUSH: &str =
    include_str!("../../tests/fixtures/vec_region_no_mutator/stash_vv_push.json");
const STASH_OPTION_MAP: &str =
    include_str!("../../tests/fixtures/vec_region_no_mutator/stash_option_map.json");
const STASH_DROP_WRAPPER: &str =
    include_str!("../../tests/fixtures/vec_region_no_mutator/stash_drop_wrapper.json");
const STASH_SCOPE_WRAPPER: &str =
    include_str!("../../tests/fixtures/vec_region_no_mutator/stash_scope_wrapper.json");
const PUSH_THEN_LEN: &str =
    include_str!("../../tests/fixtures/vec_region_no_mutator/push_then_len.json");
const PUSH_LEN_THEN_REMOVE: &str =
    include_str!("../../tests/fixtures/vec_region_no_mutator/push_len_then_remove.json");
const TRUNCATE_THEN_FRESH_REMOVE: &str =
    include_str!("../../tests/fixtures/vec_region_no_mutator/truncate_then_fresh_remove.json");

fn parse(mir: &str) -> VerifiableFunction {
    serde_json::from_str(mir).expect("the captured MIR fixture must deserialize")
}

/// `f1`'s `v`, the region root of every `stash_body.rs` body with one parameter.
const F1_V: usize = 2;

/// The callee and key of the call terminating `block`.
fn call_site(f: &mut VerifiableFunction, block: usize) -> (&mut String, &mut Option<CalleeKey>) {
    let Terminator::Call { func, callee_key, .. } = &mut f.body.blocks[block].terminator else {
        panic!("bb{block} of {} is a call in the fixture", f.name)
    };
    (func, callee_key)
}

/// A key the extractor minted for a real `alloc` item (`f1`'s `Vec::len`), its tag
/// dropped: real sysroot residency and nothing else.
fn real_alloc_key(f: &mut VerifiableFunction) -> CalleeKey {
    let (_, key) = call_site(f, 1);
    let mut key = key.clone().expect("the fixture's `Vec::len` carries its extracted key");
    assert!(key.krate_is_real_sysroot, "the fixture's `Vec::len` is resident in alloc");
    key.sysroot_item = None;
    key
}

/// `f1` with its `stash(copy _4)` callee replaced by `callee` keyed `key`.
fn f1_with_callee(
    callee: &str,
    key: impl FnOnce(&mut VerifiableFunction) -> Option<CalleeKey>,
) -> VerifiableFunction {
    let mut f = parse(STASH_F1);
    let key = key(&mut f);
    let (func, callee_key) = call_site(&mut f, 0);
    *func = callee.to_string();
    *callee_key = key;
    f
}

/// No region for `root`, no fact anywhere, and the `- 1` row not proved by ay.
fn assert_no_region_and_not_proved(name: &str, f: VerifiableFunction, root: usize) {
    assert!(VecRegion::build(&f, root).is_none(), "{name}: the base must get no region");
    let facts = vec_region_definitions(&f);
    assert!(facts.is_empty(), "{name}: no region fact may be minted: {facts:?}");
    assert!(vec_mutator_charged_blocks(&f).is_empty(), "{name}: no mutator may be charged");
    let rows = sub_rows(f);
    assert!(rows.not_proved(), "{name}: `v.len() - 1` must not be proved; {rows:?}");
}

/// THE MISCOMPILE: a dependency callee handed the definition block's `&mut v`. BEFORE:
/// `{bb2: [_6 == L0], bb6: [_9 == L0]}` and the row PROVED.
#[test]
fn a_dependency_callee_handed_the_definition_borrow_leaves_no_region() {
    let mut f = parse(STASH_F1);
    let (callee, key) = call_site(&mut f, 0);
    assert_eq!(callee, "stdep::stash");
    assert!(!CalleeKey::opt_is_real_sysroot(key.as_ref()), "a dependency is not the sysroot");
    assert_no_region_and_not_proved("f1", f, F1_V);
}

/// The pre-wave-25 reach: a charged `v.remove(0)` used to switch the facts on. BEFORE:
/// the remove (bb8) charged, facts at both `len` targets, the `- 1` row PROVED.
#[test]
fn a_dependency_callee_before_a_charged_mutator_leaves_no_region() {
    assert_no_region_and_not_proved("f1b", parse(STASH_F1B), F1_V);
}

/// The identity gate reads the extractor's residency verdict and the rendering together.
/// A std `Vec` spelling with no key, a REAL sysroot key on a trait-qualified rendering
/// (a user impl's body runs under core's trait-method `DefId`), and a real key on a
/// stamped rendering are all refused. BEFORE: each kept the region.
#[test]
fn a_forged_std_spelling_does_not_credit_the_callee() {
    let reserve = "alloc::vec::Vec::<u8>::reserve";
    for (name, f) in [
        ("no key", f1_with_callee(reserve, |_| None)),
        (
            "trait-qualified",
            f1_with_callee(
                "<alloc::vec::Vec<u8> as core::ops::AddAssign<stash_body::Local>>::add_assign",
                |f| Some(real_alloc_key(f)),
            ),
        ),
        (
            "stamped",
            f1_with_callee("__trust_crate@1973d11b2baa21fa::alloc::vec::Vec::<u8>::reserve", |f| {
                Some(real_alloc_key(f))
            }),
        ),
    ] {
        assert!(VecRegion::build(&f, F1_V).is_none(), "{name}: no region");
        assert!(vec_region_definitions(&f).is_empty(), "{name}: no fact");
    }
    // The same MIR with the callee a credited std inherent method keeps both facts: the
    // gate, not some other shape of `f1`, is what removes them.
    let f = f1_with_callee(reserve, |f| Some(real_alloc_key(f)));
    let facts = vec_region_definitions(&f);
    assert!(facts.contains_key(&BlockId(2)) && facts.contains_key(&BlockId(6)), "{facts:?}");
}

/// A tail call handed a member is never credited (the walk used to skip `TailCall`).
/// BEFORE: `Closed`, a region.
#[test]
fn a_tail_call_handed_the_definition_borrow_leaves_no_region() {
    let mut f = f1_with_callee("alloc::vec::Vec::<u8>::reserve", |f| Some(real_alloc_key(f)));
    let Terminator::Call { func, args, span, callee_key, .. } = f.body.blocks[0].terminator.clone()
    else {
        unreachable!()
    };
    f.body.blocks[0].terminator = Terminator::TailCall {
        func,
        args,
        span,
        atomic: None,
        is_foreign: false,
        is_unsafe_sig: false,
        callee_identity: None,
        callee_key,
    };
    assert!(VecRegion::build(&f, F1_V).is_none());
}

// A SYSROOT callee that can still keep the borrow, so the identity gate alone does not
// close these. BEFORE: each `- 1` row PROVED (and elided by the advisory build).

/// `Vec::push(&mut vv, &mut v)` stores the borrow in ANOTHER argument's referent; a later
/// dependency call handed `&mut vv` stashes it (`call_args_admit_no_alias`: the other
/// argument is a reference to memory that can hold a pointer).
#[test]
fn a_std_callee_storing_the_borrow_in_another_argument_leaves_no_region() {
    assert_no_region_and_not_proved("vv_push", parse(STASH_VV_PUSH), 3);
}

/// `Option::map(Some(&mut v), stash)` hands a NON-REFERENCE member (the `Option`) beside a
/// fn item, and std passes the payload to it (`call_args_admit_no_alias`).
#[test]
fn a_std_callee_handed_a_wrapped_borrow_and_a_fn_item_leaves_no_region() {
    assert_no_region_and_not_proved("option_map", parse(STASH_OPTION_MAP), F1_V);
}

/// `core::mem::drop(W(&mut v))` runs `W`'s user `Drop`, which stashes `self.0`
/// (`call_args_admit_no_alias`: the member handed is not a plain reference).
#[test]
fn a_std_drop_of_a_wrapper_holding_the_borrow_leaves_no_region() {
    assert_no_region_and_not_proved("drop_wrapper", parse(STASH_DROP_WRAPPER), F1_V);
}

/// `{ let _w = W(&mut v); }`: the same user `Drop`, run by a MIR `Drop` terminator, not a
/// call (`close_borrow_chain`'s `Drop` arm).
#[test]
fn a_scope_drop_of_a_wrapper_holding_the_borrow_leaves_no_region() {
    assert_no_region_and_not_proved("scope_wrapper", parse(STASH_SCOPE_WRAPPER), F1_V);
}

/// An `Opaque` terminator (inline asm, an indirect call) records no operands, so nothing
/// could say it is not handed a definition-block borrow. The borrow-chain walk does not
/// look for one because it never sees one: such a terminator is an `Unlocatable` write
/// of every local, so `has_one_explicit_def` refuses every local base of the body. This
/// pins that the walk may rely on it (it passed before VEC-REGION-DEF-BLOCK-STASH-1 too).
#[test]
fn an_opaque_terminator_leaves_no_region_for_a_borrowed_definition() {
    let mut f = parse(PUSH_THEN_LEN);
    // bb3: `_0 = 0; goto bb7` becomes an inline-asm-like opaque edge to bb7.
    f.body.blocks[3].terminator = Terminator::Opaque {
        kind: "InlineAsm".into(),
        targets: vec![BlockId(7)],
        span: SourceSpan::default(),
    };
    assert!(VecRegion::build(&f, F1_V).is_none());
}

/// CONTROLS (wave 25's precision where it is sound; these pass before and after): a std
/// inherent method handed the definition borrow with scalar arguments keeps the region,
/// its facts and its proof; a two-phase `truncate` still opens the region after its
/// activation and mints nothing in the window.
#[test]
fn a_std_inherent_callee_keeps_the_region() {
    // bb0: `push(move _4, 1) -> bb1`; bb1: `_5 = is_empty(&v) -> bb2`; bb4: `_7 = len(&v) -> bb5`.
    let f = parse(PUSH_THEN_LEN);
    assert!(VecRegion::build(&f, F1_V).is_some());
    let facts = vec_region_definitions(&f);
    assert!(facts.contains_key(&BlockId(2)) && facts.contains_key(&BlockId(5)), "{facts:?}");
    let rows = sub_rows(f);
    assert!(rows.proved(), "push_then_len: the guarded `- 1` stays proved; {rows:?}");

    // bb1: `push(move _5, move _6) -> bb2` activates the reservation; bb4: the remove.
    let f = parse(PUSH_LEN_THEN_REMOVE);
    assert_eq!(vec_mutator_charged_blocks(&f), vec![BlockId(4)]);

    // bb1's `len` is in the window (its target bb2 states nothing); bb3's is after the
    // activation (bb2's `truncate`), so bb4 states `_10 == L0` and the remove is charged.
    let f = parse(TRUNCATE_THEN_FRESH_REMOVE);
    let facts = vec_region_definitions(&f);
    assert!(!facts.contains_key(&BlockId(2)), "the window states nothing: {facts:?}");
    assert!(facts.contains_key(&BlockId(4)), "{facts:?}");
    assert_eq!(vec_mutator_charged_blocks(&f), vec![BlockId(5)]);
}

/// The control's fail-closed half: the same `push` with its key removed (as for an
/// indirect call or a pre-carrier producer) is not credited, so the body gets no region.
/// BEFORE: the region was kept.
#[test]
fn an_unkeyed_std_callee_is_not_credited() {
    let mut f = parse(PUSH_THEN_LEN);
    *call_site(&mut f, 0).1 = None;
    assert!(VecRegion::build(&f, F1_V).is_none(), "an unkeyed `push` is not credited");
    assert!(vec_region_definitions(&f).is_empty());
}
