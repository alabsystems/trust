// Trust (MUTREF-VEC-LEN-GUARD-REFUTE-1 and VEC-REGION-JOIN-SEED-1, 2026-10-12): the `Vec`
// region facts are minted wherever a region-eligible base has a fact site, not only for a
// base a charged index mutator uses, and only at a return target the call solely enters.
//
// THE REFUTATION. `pub fn last_index(v: &mut Vec<u8>) -> usize { if !v.is_empty() {
// v.len() - 1 } else { 0 } }` was `[overflow:sub] FAILED (ay-in-process)` under every
// policy, with the counterexample `_2 = false .. v = 0`, which breaks its own guard. The
// `&mut`-parameter havoc at the second `Vec::len(&*v)` call severs every tie to the guard,
// and `guards::owned_container_len_var` declines a `&mut` receiver by design. The region
// facts (`_e <=> L0 == 0`, `_n == L0` over the fresh constant `__trust_vec_region_len_1`)
// were the one mechanism that survives the havoc, and `vec_region_definitions` minted
// them only when a region-reached `v.remove(r)` also used `v` (scout probe `reg.rs`
// `b_with_remove` proved; `a_plain` failed).
//
// THE JOIN. Each fact is seeded as an ENTRY fact of the call's return target. In
// `let n = if c { v.len() } else { 100 }` that target is the join, which the `else` arm
// enters with `n == 100`, so `n == L0` was read there too: `join_remove` (a later
// `v.remove(r)` switching the facts on) proved `v.len() - n` on the stage 1 of
// `46e9afaf95`, and it panics for `c == false` and `v.len() < 100`. Without the
// sole-entry gate, minting without a mutator would have spread that to `join_len`.
//
// The MIR under `tests/fixtures/vec_region_no_mutator/` is `-Ztrust-dump=mir:<dir>` output
// from that stage 1 (`scratchpad/stage1-w25probe`, `--edition 2021 -Ztrust-verify=on
// -Ztrust-policy=advisory -Coverflow-checks=on --crate-type lib`), re-serialized without
// whitespace, of `body.rs`:
//
// ```text
// #[inline(never)] pub fn f(v: &mut Vec<u8>) { v.clear() }
// #[inline(never)] pub fn g() { std::hint::black_box(0u8); }
// pub fn last_index(v: &mut Vec<u8>) -> usize { if !v.is_empty() { v.len() - 1 } else { 0 } }
// pub fn last_index_gt(v: &mut Vec<u8>) -> usize { if v.len() > 0 { v.len() - 1 } else { 0 } }
// pub fn ge2(v: &mut Vec<u8>) -> usize { if v.len() >= 2 { v.len() - 2 } else { 7 } }
// pub fn last_elem(v: &mut Vec<u8>) -> u8 { if !v.is_empty() { v[v.len() - 1] } else { 0 } }
// pub fn t_unrelated_nomut(v: &mut Vec<u8>) -> usize {
//     if !v.is_empty() { g(); v.len() - 1 } else { 0 } }
// pub fn cleared(v: &mut Vec<u8>) -> usize {
//     if !v.is_empty() { v.clear(); v.len() - 1 } else { 0 } }
// pub fn truncated(v: &mut Vec<u8>) -> usize {
//     if !v.is_empty() { v.truncate(0); v.len() - 1 } else { 0 } }
// pub fn t_opaque_v(v: &mut Vec<u8>) -> usize {
//     if !v.is_empty() { f(v); v.len() - 1 } else { 0 } }
// pub fn join_len(v: &mut Vec<u8>, c: bool) -> usize {
//     let n = if c { v.len() } else { 100 }; v.len() - n }
// pub fn join_remove(v: &mut Vec<u8>, c: bool) -> usize {
//     let n = if c { v.len() } else { 100 }; let r = v.len() - n;
//     if r < v.len() { v.remove(r); } r }
// ```
//
// (one function per line here; the dumped spans index the multi-line original).
//
// BEFORE (the fix reverted): `vec_region_definitions` is EMPTY for every mutator-free
// body, so the `- 1`/`- 2` row is refuted by ay on `last_index`, `last_index_gt`, `ge2`,
// `last_elem` and `t_unrelated_nomut`; on `join_remove` it holds `n == L0` at the join
// and the row is PROVED. The clear/truncate/opaque-call twins and `join_len` are not
// proved before or after.

use trust_types::{
    BinOp, BlockId, Formula, Operand, Place, Ty, VcKind, VerifiableFunction, VerificationResult,
};

use super::{VecBase, vec_region_definitions, vec_region_len_var};

const LAST_INDEX: &str = include_str!("../../tests/fixtures/vec_region_no_mutator/last_index.json");
const LAST_INDEX_GT: &str =
    include_str!("../../tests/fixtures/vec_region_no_mutator/last_index_gt.json");
const GE2: &str = include_str!("../../tests/fixtures/vec_region_no_mutator/ge2.json");
const LAST_ELEM: &str = include_str!("../../tests/fixtures/vec_region_no_mutator/last_elem.json");
const T_UNRELATED_NOMUT: &str =
    include_str!("../../tests/fixtures/vec_region_no_mutator/t_unrelated_nomut.json");
const CLEARED: &str = include_str!("../../tests/fixtures/vec_region_no_mutator/cleared.json");
const TRUNCATED: &str = include_str!("../../tests/fixtures/vec_region_no_mutator/truncated.json");
const T_OPAQUE_V: &str = include_str!("../../tests/fixtures/vec_region_no_mutator/t_opaque_v.json");
const JOIN_LEN: &str = include_str!("../../tests/fixtures/vec_region_no_mutator/join_len.json");
const JOIN_REMOVE: &str =
    include_str!("../../tests/fixtures/vec_region_no_mutator/join_remove.json");

fn parse(mir: &str) -> VerifiableFunction {
    serde_json::from_str(mir).expect("the captured MIR fixture must deserialize")
}

/// `L0` of the whole `&mut Vec` parameter `_1`.
fn l0() -> Formula {
    vec_region_len_var(&VecBase { root: 1, fields: Vec::new() })
}

fn int_local(func: &VerifiableFunction, local: usize) -> Formula {
    crate::operand_to_formula(func, &Operand::Copy(Place::local(local)))
}

/// `_n == L0`.
fn len_fact(func: &VerifiableFunction, n: usize) -> Formula {
    Formula::Eq(Box::new(int_local(func, n)), Box::new(l0()))
}

/// `(_e && L0 == 0) || (!_e && !(L0 == 0))`.
fn is_empty_fact(func: &VerifiableFunction, e: usize) -> Formula {
    let empty = int_local(func, e);
    let zero = Formula::Eq(Box::new(l0()), Box::new(Formula::Int(0)));
    Formula::Or(vec![
        Formula::And(vec![empty.clone(), zero.clone()]),
        Formula::And(vec![Formula::Not(Box::new(empty)), Formula::Not(Box::new(zero))]),
    ])
}

/// The facts minted at `block`, empty when none.
fn facts_at(func: &VerifiableFunction, block: usize) -> Vec<Formula> {
    vec_region_definitions(func).remove(&BlockId(block)).unwrap_or_default()
}

/// The `Sub` overflow rows of a fixture, as the production split leaves them (also read by
/// `vec_region_twophase_tests`, VEC-REGION-DEF-BLOCK-STASH-1).
pub(super) struct SubRows {
    /// The in-process ay's verdict on each `Sub` overflow row handed to a solver.
    routed: Vec<VerificationResult>,
    /// `Sub` overflow rows the interval lane discharged without a solver.
    discharged: usize,
    /// Rows `havoc_decline` reclassified because their verdict rests on an
    /// unconstrained call result (`UnsupportedMir` `UnmodeledCalleeReturn`, Unknown):
    /// the `len` read after `clear(copy _1)` is one.
    declined: usize,
}

impl std::fmt::Debug for SubRows {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "routed {:?}, discharged {}, declined {}",
            self.routed, self.discharged, self.declined
        )
    }
}

impl SubRows {
    /// The row exists and is proved, by ay or the interval lane, and never declined.
    pub(super) fn proved(&self) -> bool {
        self.declined == 0
            && self.discharged + self.routed.len() >= 1
            && self.routed.iter().all(|r| matches!(r, VerificationResult::Proved { .. }))
    }

    /// The row exists (as `Sub` or as the decline) and no lane proved it.
    pub(super) fn not_proved(&self) -> bool {
        self.discharged == 0
            && self.routed.len() + self.declined >= 1
            && self.routed.iter().all(|r| !matches!(r, VerificationResult::Proved { .. }))
    }
}

/// The `Sub` rows' verdicts from the real in-process ay, on a big stack (VC generation
/// and the solver search overflow libtest's default stack).
pub(super) fn sub_rows(func: VerifiableFunction) -> SubRows {
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

/// THE FIX, fact half: a mutator-free `&mut Vec` parameter's guard and later `len` get the
/// region facts. BEFORE: `vec_region_definitions` returned an empty map.
#[test]
fn a_mutator_free_mut_vec_param_gets_the_region_facts() {
    // bb0: `_2 = is_empty(&*v) -> bb1`; bb3: `_4 = len(&*v) -> bb4`.
    let f = parse(LAST_INDEX);
    assert_eq!(facts_at(&f, 1), vec![is_empty_fact(&f, 2)]);
    assert_eq!(facts_at(&f, 4), vec![len_fact(&f, 4)]);
    assert_eq!(vec_region_definitions(&f).len(), 2, "only the two call targets");
    // bb0: `_3 = len(&*v) -> bb1`; bb2: `_5 = len(&*v) -> bb3`.
    let f = parse(LAST_INDEX_GT);
    assert_eq!(facts_at(&f, 1), vec![len_fact(&f, 3)]);
    assert_eq!(facts_at(&f, 3), vec![len_fact(&f, 5)]);
    // A nullary call between the guard and the `len` mutates nothing of `v`.
    let f = parse(T_UNRELATED_NOMUT);
    assert_eq!(facts_at(&f, 1), vec![is_empty_fact(&f, 2)]);
    assert_eq!(facts_at(&f, 5), vec![len_fact(&f, 5)]);
}

/// THE FIX, verdict half: the guarded subtraction is proved. BEFORE: refuted by ay with a
/// model that breaks the guard (`last_index`: `_2 = false .. v = 0`).
#[test]
fn a_len_guarded_subtraction_on_a_mut_vec_param_is_proved() {
    for (name, mir) in [
        ("last_index", LAST_INDEX),
        ("last_index_gt", LAST_INDEX_GT),
        ("ge2", GE2),
        ("last_elem", LAST_ELEM),
        ("t_unrelated_nomut", T_UNRELATED_NOMUT),
    ] {
        let rows = sub_rows(parse(mir));
        assert!(rows.proved(), "{name}: the guarded `- k` must be proved; {rows:?}");
    }
}

/// FAIL-CLOSED: a `clear()`, a `truncate(0)` or an opaque `f(v)` between the guard and the
/// `len` puts the `len` outside the region (each is handed `copy _1`, a mention of the
/// base). The guard's own fact is minted; the later `len` gets none, and the row stays
/// unproved.
#[test]
fn a_resize_between_the_guard_and_the_len_leaves_the_len_outside_the_region() {
    for (name, mir) in [("cleared", CLEARED), ("truncated", TRUNCATED), ("t_opaque_v", T_OPAQUE_V)]
    {
        let f = parse(mir);
        // bb0: `_2 = is_empty(&*v) -> bb1`; bb3: the resize; bb4: `_5 = len(&*v) -> bb5`.
        assert_eq!(facts_at(&f, 1), vec![is_empty_fact(&f, 2)], "{name}");
        assert!(facts_at(&f, 5).is_empty(), "{name}: the post-resize `len` states no `L0`");
        let rows = sub_rows(f);
        assert!(
            rows.not_proved(),
            "{name}: the `- 1` after the resize must stay unproved; {rows:?}"
        );
    }
}

/// The join shape's checks: bb1 `_3 = len(&*v) -> bb3`; bb2 `_3 = 100; goto bb3`; bb3
/// `_5 = len(&*v) -> bb4`. No fact at the join, the solely-entered target keeps its own,
/// and `v.len() - n` (`n == 100` on the `else` edge) is not proved.
fn assert_no_fact_at_the_join(name: &str, f: VerifiableFunction) {
    assert!(
        !super::call_facts::sole_predecessor_is(&f, BlockId(3), BlockId(1)),
        "{name}: the fixture's first `len` returns into the join"
    );
    assert!(facts_at(&f, 3).is_empty(), "{name}: `n == L0` must not be seeded at the join");
    assert_eq!(facts_at(&f, 4), vec![len_fact(&f, 5)], "{name}: the solely-entered target");
    let rows = sub_rows(f);
    assert!(
        rows.not_proved(),
        "{name}: `v.len() - n` with `n == 100` on the `else` arm must not be proved; {rows:?}"
    );
}

/// VEC-REGION-JOIN-SEED-1, the pre-existing false proof: `join_remove`'s later
/// `v.remove(r)` switched the facts on before this change. BEFORE: `{bb3: [n == L0], ..}`
/// and the `- n` row PROVED.
#[test]
fn a_len_returning_into_a_join_states_no_fact_there_with_a_mutator() {
    assert_no_fact_at_the_join("join_remove", parse(JOIN_REMOVE));
}

/// VEC-REGION-JOIN-SEED-1 against the widening: without the gate, minting without a
/// mutator would seed `n == L0` at `join_len`'s join too. BEFORE: no facts at all, the
/// row refuted.
#[test]
fn a_len_returning_into_a_join_states_no_fact_there_without_a_mutator() {
    assert_no_fact_at_the_join("join_len", parse(JOIN_LEN));
}

/// The root must still be region-eligible: the same body over a `&mut Vec` LOCAL (not a
/// parameter: a borrow of something whose mutations the walk does not see) or a raw
/// pointer root mints nothing.
#[test]
fn a_mut_vec_local_or_raw_pointer_root_gets_no_region_facts() {
    let mut local_root = parse(LAST_INDEX);
    local_root.body.arg_count = 0;
    assert!(vec_region_definitions(&local_root).is_empty(), "a `&mut Vec` local root");

    let mut raw_root = parse(LAST_INDEX);
    let Ty::Ref { inner, .. } = raw_root.body.locals[1].ty.clone() else {
        panic!("`v` is a reference in the fixture")
    };
    raw_root.body.locals[1].ty = Ty::RawPtr { mutable: true, pointee: inner };
    assert!(vec_region_definitions(&raw_root).is_empty(), "a `*mut Vec` root");
}
