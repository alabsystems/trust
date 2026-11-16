// Trust (2026-10-15, DECISION_QUEUE D101): an `&mut Vec` PARAMETER is a `Vec` region root
// only when no OTHER parameter could reach its pointee.
//
// THE DEFECT. `Mut(b)` counts the writes, borrows, moves and drops that NAME the base. A
// second argument that aliased `*b` could resize it without naming it, so a region over an
// `&mut` root silently assumed the two arguments disjoint: Rust's `noalias`, which D96
// adopts only DISCLOSED and DEMOTED (R1) through the compiler-installed
// `NOALIAS_MUT_ARGS` premise. After the 2026-10-14 merge the region facts are minted at
// every `len`/`is_empty` call (790f9f50fdb), so `for i in 0..v.len() { w.clear(); v[i] = 0 }`
// over `v, w: &mut Vec<u32>` was PROVED with both rows kernel-certified and nothing
// disclosed (`tests/ui/trust/vec_param_length_invariant_loop_refused.rs`, whose pin says
// "a green here means that premise was adopted without the decision").
//
// The MIR under `tests/fixtures/vec_region_param_alias/` is `-Ztrust-dump=mir:<dir>` output
// from the stage 1 of the merged tree (`5184affbb97` plus its working tree, 2026-10-15),
// `--edition 2021 -Ztrust-verify=on -Ztrust-policy=advisory -Coverflow-checks=on
// --crate-type lib`, re-serialized without whitespace, of `body.rs`:
//
// ```text
// pub fn two_mut_last(v: &mut Vec<u8>, w: &mut Vec<u8>) -> usize {
//     if !v.is_empty() { w.clear(); v.len() - 1 } else { 0 } }
// pub fn mut_scalar_last(v: &mut Vec<u8>, n: &mut usize) -> usize {
//     if !v.is_empty() { *n = 0; v.len() - 1 } else { 0 } }
// pub fn shared_scalar_last(v: &mut Vec<u8>, k: &u32) -> usize {
//     if !v.is_empty() { let _x = *k; v.len() - 1 } else { 0 } }
// pub fn two_mut_remove(v: &mut Vec<u8>, w: &mut Vec<u8>) -> u8 {
//     if !v.is_empty() { w.clear(); v.remove(0) } else { 0 } }
// ```
//
// BEFORE (that stage 1, measured): each of the four built `1 proved` out of 1 — the
// `- 1` rows from `_n == L0` at the `len` call, `two_mut_remove`'s index row from `L0`.
// AFTER: only `shared_scalar_last` (a shared reference to a pure value cannot write
// anything) keeps its region.
//
// THE SECOND LANE. Main's abstract-length symbol `coll_len(v)` is ONE unversioned name
// for the whole body; its ties (`_n == coll_len(v)` at `v.len()`) and the scalar-index
// recovery (`v[i]` against `coll_len(v)`) are gated on `guards::local_mut_borrows_may_resize`,
// which saw only the borrows that name `v`. With the region gone, the loop shape
// `two_mut_loop` (`for i in 0..v.len() { w.clear(); v[i] = 0 }`, the UI pin's own) still
// proved its `[slice]` row from `_5 == v` and `i < _5` on the stage 1 of the region fix.
// The gate now asks the same predicate (`shared_scalar_loop` is its control):
//
// ```text
// pub fn two_mut_loop(v: &mut Vec<u32>, w: &mut Vec<u32>) {
//     for i in 0..v.len() { w.clear(); v[i] = 0; } }
// pub fn shared_scalar_loop(v: &mut Vec<u32>, k: &u32) {
//     for i in 0..v.len() { let _x = *k; v[i] = 0; } }
// pub fn two_shared_index(a: &Vec<u32>, b: &Vec<u32>, i: usize) -> u32 {
//     if i < b.len() { b[i] + a.len() as u32 * 0 } else { 0 } }
// ```
//
// The gate asks the predicate of an `&mut` base only: two SHARED `&Vec` parameters keep
// their tie (`two_shared_index`), since D96 is the question of two `&mut` arguments.

use trust_types::{BlockId, VcKind, VerifiableFunction, VerificationResult};

use super::vec_region_definitions;
use super::vec_region_no_mutator_tests::sub_rows;

const TWO_MUT_LAST: &str =
    include_str!("../../tests/fixtures/vec_region_param_alias/two_mut_last.json");
const MUT_SCALAR_LAST: &str =
    include_str!("../../tests/fixtures/vec_region_param_alias/mut_scalar_last.json");
const SHARED_SCALAR_LAST: &str =
    include_str!("../../tests/fixtures/vec_region_param_alias/shared_scalar_last.json");
const TWO_MUT_REMOVE: &str =
    include_str!("../../tests/fixtures/vec_region_param_alias/two_mut_remove.json");
const TWO_MUT_LOOP: &str =
    include_str!("../../tests/fixtures/vec_region_param_alias/two_mut_loop.json");
const SHARED_SCALAR_LOOP: &str =
    include_str!("../../tests/fixtures/vec_region_param_alias/shared_scalar_loop.json");
const TWO_SHARED_INDEX: &str =
    include_str!("../../tests/fixtures/vec_region_param_alias/two_shared_index.json");

fn parse(mir: &str) -> VerifiableFunction {
    serde_json::from_str(mir).expect("the captured MIR fixture must deserialize")
}

/// A second parameter that can WRITE — another `&mut Vec`, or an `&mut usize` that could
/// overlap the header if the arguments aliased — leaves the `&mut` root no region: no
/// `L0` fact is minted anywhere, and the guarded `- 1` is not proved.
#[test]
fn a_mut_vec_param_beside_a_writing_param_gets_no_region() {
    for (name, mir) in [("two_mut_last", TWO_MUT_LAST), ("mut_scalar_last", MUT_SCALAR_LAST)] {
        let f = parse(mir);
        assert!(
            vec_region_definitions(&f).is_empty(),
            "{name}: no region fact may rest on the arguments being disjoint"
        );
        let rows = sub_rows(f);
        assert!(rows.not_proved(), "{name}: the `- 1` must stay unproved; {rows:?}");
    }
}

/// The index mutator's precondition is not stated over `L0` either: `two_mut_remove`'s
/// `v.remove(0)` keeps the fail-honest row instead of the region's charge.
#[test]
fn a_mut_vec_param_beside_another_mut_vec_charges_no_region_mutator_row() {
    let f = parse(TWO_MUT_REMOVE);
    assert!(vec_region_definitions(&f).is_empty());
    assert!(
        super::vec_mutator_charged_blocks(&f).is_empty(),
        "the remove must not be charged inside a region the second `&mut` could break"
    );
}

/// CONTROL: a shared reference to a pure value cannot write anything, so the root keeps
/// its region, the guard and the later `len` get their facts, and the row is proved.
#[test]
fn a_mut_vec_param_beside_a_shared_pure_reference_keeps_its_region() {
    let f = parse(SHARED_SCALAR_LAST);
    let facts = vec_region_definitions(&f);
    assert!(
        facts.len() >= 2,
        "the guard's and the later `len`'s facts must both be minted; {facts:?}"
    );
    assert!(facts.keys().all(|b| *b != BlockId(0)), "never seeded at the entry block");
    let rows = sub_rows(f);
    assert!(rows.proved(), "the guarded `- 1` must be proved; {rows:?}");
}

/// The `v[i]` index rows of `func`: how many `[slice]` bounds rows there are, how many of
/// them the real in-process ay (or a discharging lane) proves, and how many fail-honest
/// `container-index-unstable-len` Unknown rows the recovery left instead. Run on a big
/// stack, as `sub_rows` is.
fn index_rows(func: VerifiableFunction) -> (usize, usize, usize) {
    std::thread::Builder::new()
        .stack_size(32 * 1024 * 1024)
        .spawn(move || {
            let is_slice = |kind: &VcKind| matches!(kind, VcKind::SliceBoundsCheck);
            let is_unstable = |kind: &VcKind| {
                matches!(kind, VcKind::UnsupportedMir { kind, .. } if kind == "container-index-unstable-len")
            };
            let (solver, discharged) = crate::generate_vcs_with_discharge(&func);
            let routed: Vec<_> = solver.iter().filter(|vc| is_slice(&vc.kind)).cloned().collect();
            let router = crate::test_router::deterministic_test_router();
            let proved_routed = router
                .verify_all(&routed)
                .into_iter()
                .filter(|(_, r)| matches!(r, VerificationResult::Proved { .. }))
                .count();
            let lane = discharged.iter().filter(|(vc, _)| is_slice(&vc.kind)).count();
            let unstable = solver.iter().filter(|vc| is_unstable(&vc.kind)).count()
                + discharged.iter().filter(|(vc, _)| is_unstable(&vc.kind)).count();
            (routed.len() + lane, proved_routed + lane, unstable)
        })
        .expect("spawn solver thread")
        .join()
        .expect("solver thread must not panic")
}

/// The `coll_len` lane: beside a second `&mut Vec`, `v[i]` after `w.clear()` is not proved
/// from the pre-loop `v.len()` — the recovery declines and the row is the fail-honest
/// `container-index-unstable-len` Unknown (BEFORE: a `[slice]` row, proved). Beside a
/// shared reference to a pure value the `[slice]` row is still proved.
#[test]
fn a_coll_len_tie_does_not_survive_a_call_through_another_mut_param() {
    let (slice, proved, unstable) = index_rows(parse(TWO_MUT_LOOP));
    assert_eq!(proved, 0, "no `v[i]` row may rest on `v` and `w` being disjoint ({slice} rows)");
    assert!(unstable >= 1, "the declined index must keep its Unknown row");
    let (slice, proved, unstable) = index_rows(parse(SHARED_SCALAR_LOOP));
    assert!(
        slice >= 1 && proved == slice && unstable == 0,
        "the control's `v[i]` row stays proved: {proved}/{slice}, {unstable} unstable"
    );
}

/// CONTROL for the `&mut`-only scope: two SHARED `&Vec` parameters keep the `coll_len` tie,
/// so `b[i]` under `i < b.len()` is proved beside another `&Vec`.
#[test]
fn two_shared_vec_params_keep_their_coll_len_tie() {
    let (slice, proved, unstable) = index_rows(parse(TWO_SHARED_INDEX));
    assert!(
        slice >= 1 && proved == slice && unstable == 0,
        "the guarded `b[i]` row stays proved: {proved}/{slice}, {unstable} unstable"
    );
}
