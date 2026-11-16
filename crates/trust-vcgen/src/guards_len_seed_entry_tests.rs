//! Trust (LEN-TIE-JOIN-SEED-1 and LAST-SOME-ARM-SEED-1, 2026-10-12): every fact
//! `slice_last_some_nonempty_definitions` mints holds on ONE edge and is seeded as an
//! entry fact of a block, so it is read on every edge into that block. Pinned on REAL
//! extracted MIR.
//!
//! Found while widening the `Vec` region facts (MUTREF-VEC-LEN-GUARD-REFUTE-1), whose
//! return-target seed had the same hole (VEC-REGION-JOIN-SEED-1). Measured on the stage
//! 1 of `46e9afaf95` (`scratchpad/stage1-w25probe`), default policy unless noted:
//!
//!  * `join_shared`: `let n = if c { v.len() } else { 100 }; v.len() - n` over `&Vec`.
//!    rustc's `SimplifyCfg` returns the first `len` straight into the join, which the
//!    `else` arm enters with `n == 100`; the `n == coll_len(v)` tie was seeded there and
//!    `overflow:sub` was PROVED (rc=0). It panics for `c == false`, `v.len() < 100`
//!    (the check was kept: the row was not kernel-certified).
//!  * `last_dup`: `match v.last() { Some(_) => {}, None => {} }; v.len() - 1`. rustc -O0
//!    spells the match `switchInt(d) -> [0: bbJ, 1: bbJ, ..]`, so the `Some` target is
//!    the join `None` also enters; `coll_len(v) >= 1` was seeded there, the row was
//!    kernel-certified, its overflow check ELIDED, and the binary returned `usize::MAX`
//!    for an empty `v` where verify-off panics (exit 1 vs 101).
//!  * `last_redef`: `let mut o = v.last(); if c { o = Some(&5); } match o { Some(_) =>
//!    v.len() - 1, .. }`. The `Some` arm says nothing about `v` once `o` is reassigned;
//!    the row was PROVED (advisory).
//!
//! The MIR under `tests/fixtures/len_seed_entry/` is `-Ztrust-dump=mir:<dir>` output from
//! that stage 1 (`--edition 2021 -Ztrust-verify=on -Ztrust-policy=advisory
//! -Coverflow-checks=on --crate-type lib`), re-serialized without whitespace, of
//! `body.rs` (one function per line here; the dumped spans index the multi-line
//! original):
//!
//! ```text
//! pub fn last_dup(v: &Vec<u8>) -> usize {
//!     match v.last() { Some(_) => {} None => {} } v.len() - 1 }
//! pub fn last_redef(v: &Vec<u8>, c: bool) -> usize {
//!     let mut o = v.last(); if c { o = Some(&5); }
//!     match o { Some(_) => v.len() - 1, None => 0 } }
//! pub fn join_shared(v: &Vec<u8>, c: bool) -> usize {
//!     let n = if c { v.len() } else { 100 }; v.len() - n }
//! pub fn last_ok(v: &Vec<u8>) -> usize { match v.last() { Some(_) => v.len() - 1, None => 0 } }
//! pub fn last_iflet(v: &Vec<u8>) -> usize { if let Some(_) = v.last() { v.len() - 1 } else { 0 } }
//! pub fn len_guard_shared(v: &Vec<u8>) -> usize { if v.len() > 0 { v.len() - 1 } else { 0 } }
//! ```
//!
//! The three controls keep their proof.

use trust_types::{VcKind, VerificationResult};

use super::*;

const LAST_DUP: &str = include_str!("../tests/fixtures/len_seed_entry/last_dup.json");
const LAST_REDEF: &str = include_str!("../tests/fixtures/len_seed_entry/last_redef.json");
const JOIN_SHARED: &str = include_str!("../tests/fixtures/len_seed_entry/join_shared.json");
const LAST_OK: &str = include_str!("../tests/fixtures/len_seed_entry/last_ok.json");
const LAST_IFLET: &str = include_str!("../tests/fixtures/len_seed_entry/last_iflet.json");
const LEN_GUARD_SHARED: &str =
    include_str!("../tests/fixtures/len_seed_entry/len_guard_shared.json");

fn parse(mir: &str) -> VerifiableFunction {
    serde_json::from_str(mir).expect("the captured MIR fixture must deserialize")
}

/// `coll_len(v)` of the `&Vec` parameter `_1`.
fn coll_len_v(func: &VerifiableFunction) -> Formula {
    coll_len_var_place(func, &trust_types::Place::local(1))
}

/// The facts seeded at `block`, empty when none.
fn facts_at(func: &VerifiableFunction, block: usize) -> Vec<Formula> {
    slice_last_some_nonempty_definitions(func).remove(&BlockId(block)).unwrap_or_default()
}

/// Does any fact seeded at `block` mention `coll_len(v)`?
fn states_coll_len_at(func: &VerifiableFunction, block: usize) -> bool {
    let len = coll_len_v(func);
    facts_at(func, block).iter().any(|fact| format!("{fact:?}").contains(&format!("{len:?}")))
}

/// The `Sub` overflow rows of a fixture: ay's verdict on each routed row, how many the
/// interval lane discharged, and how many `havoc_decline` reclassified
/// (`UnsupportedMir` `UnmodeledCalleeReturn`, Unknown).
#[derive(Debug)]
struct SubRows {
    routed: Vec<VerificationResult>,
    discharged: usize,
    declined: usize,
}

fn sub_rows(func: VerifiableFunction) -> SubRows {
    std::thread::Builder::new()
        .stack_size(32 * 1024 * 1024)
        .spawn(move || {
            let is_sub =
                |kind: &VcKind| matches!(kind, VcKind::ArithmeticOverflow { op: BinOp::Sub, .. });
            let is_decline = |kind: &VcKind| {
                let VcKind::UnsupportedMir { kind, .. } = kind else { return false };
                kind == "UnmodeledCalleeReturn"
            };
            let (solver, discharged) = crate::generate_vcs_with_discharge(&func);
            let routed: Vec<_> = solver.iter().filter(|vc| is_sub(&vc.kind)).cloned().collect();
            let router = crate::test_router::deterministic_test_router();
            SubRows {
                routed: router.verify_all(&routed).into_iter().map(|(_, r)| r).collect(),
                discharged: discharged.iter().filter(|(vc, _)| is_sub(&vc.kind)).count(),
                declined: solver.iter().filter(|vc| is_decline(&vc.kind)).count()
                    + discharged.iter().filter(|(vc, _)| is_decline(&vc.kind)).count(),
            }
        })
        .expect("spawn solver thread")
        .join()
        .expect("solver thread must not panic")
}

/// The row exists and is proved, by ay or the interval lane, and never declined.
fn proved(rows: &SubRows) -> bool {
    rows.declined == 0
        && rows.discharged + rows.routed.len() >= 1
        && rows.routed.iter().all(|r| matches!(r, VerificationResult::Proved { .. }))
}

/// The row exists (as `Sub` or as the decline) and no lane proved it.
fn not_proved(rows: &SubRows) -> bool {
    rows.discharged == 0
        && rows.routed.len() + rows.declined >= 1
        && rows.routed.iter().all(|r| !matches!(r, VerificationResult::Proved { .. }))
}

/// LEN-TIE-JOIN-SEED-1: the first `len` returns into the join (bb3), which the `else` arm
/// (bb2, `_3 = 100`) also enters. BEFORE: `{bb3: [_3 == coll_len(v)], bb4: [..]}` and the
/// row PROVED.
#[test]
fn a_len_returning_into_a_join_is_not_tied_there() {
    let f = parse(JOIN_SHARED);
    let preds = block_predecessor_edges(&f);
    assert!(!sole_predecessor_is(&preds, BlockId(3), BlockId(1)), "bb3 is the join");
    assert!(!states_coll_len_at(&f, 3), "no `n == coll_len(v)` at the join: {:?}", facts_at(&f, 3));
    assert!(states_coll_len_at(&f, 4), "the second `len` returns solely into bb4");
    let rows = sub_rows(f);
    assert!(not_proved(&rows), "`v.len() - n` with `n == 100` must not be proved: {rows:?}");
}

/// LAST-SOME-ARM-SEED-1, the duplicated label: `switchInt(_4) -> [0: bb4, 1: bb4, ..]`.
/// BEFORE: `{bb4: [coll_len(v) >= 1], ..}`, kernel-certified, check elided.
#[test]
fn a_some_label_sharing_its_target_with_none_states_no_non_emptiness() {
    let f = parse(LAST_DUP);
    let Terminator::SwitchInt { targets, otherwise, .. } = &f.body.blocks[2].terminator else {
        panic!("bb2 switches on the `last()` discriminant in the fixture")
    };
    assert_eq!(switch_edges_into(targets, *otherwise, BlockId(4)), 2, "both labels enter bb4");
    let nonempty = Formula::Ge(Box::new(coll_len_v(&f)), Box::new(Formula::Int(1)));
    assert!(!facts_at(&f, 4).contains(&nonempty), "{:?}", facts_at(&f, 4));
    let rows = sub_rows(f);
    assert!(not_proved(&rows), "`v.len() - 1` after the match must not be proved: {rows:?}");
}

/// LAST-SOME-ARM-SEED-1, the reassigned `Option`: `_3` is written by `last()` (bb1) and
/// by `_3 = move _5` (bb3). BEFORE: `{bb7: [coll_len(v) >= 1], ..}` and the row PROVED.
#[test]
fn a_reassigned_option_local_states_no_non_emptiness() {
    let f = parse(LAST_REDEF);
    assert_eq!(crate::local_defs::body_unique_defining_block(&f.body, 3), None);
    let nonempty = Formula::Ge(Box::new(coll_len_v(&f)), Box::new(Formula::Int(1)));
    assert!(!facts_at(&f, 7).contains(&nonempty), "{:?}", facts_at(&f, 7));
    let rows = sub_rows(f);
    assert!(not_proved(&rows), "`v.len() - 1` in the `Some` arm must not be proved: {rows:?}");
}

/// CONTROLS: the shapes these facts exist for keep their proof.
#[test]
fn the_solely_entered_shapes_keep_their_proof() {
    // `match v.last() { Some(_) => v.len() - 1, .. }`: `Some` -> bb5, one edge.
    let f = parse(LAST_OK);
    let nonempty = Formula::Ge(Box::new(coll_len_v(&f)), Box::new(Formula::Int(1)));
    assert!(facts_at(&f, 5).contains(&nonempty), "{:?}", facts_at(&f, 5));
    for (name, mir) in
        [("last_ok", LAST_OK), ("last_iflet", LAST_IFLET), ("len_guard_shared", LEN_GUARD_SHARED)]
    {
        let rows = sub_rows(parse(mir));
        assert!(proved(&rows), "{name}: the guarded `- 1` must stay proved: {rows:?}");
    }
}
