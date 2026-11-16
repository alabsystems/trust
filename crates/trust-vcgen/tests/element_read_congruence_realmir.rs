//! VGAPS-G1 (the verifier-gaps design, trust-ir
//! `reports/2026-10-08-session-4b77663c/designs/trust-verifier-gaps-final.md` §2): the
//! ELEMENT-READ CONGRUENCE on real MIR. rustc mints a fresh index temp per `a[i]`, and an
//! element name keys on the index LOCAL, so the guard's read and the use's read of one
//! element were two unrelated SMT variables, and `if a[i] > 0 { a[i] - 1 }` over a
//! `&mut` slice was refuted with `_9 = _13`, `a*[_9] = 1`, `a*[_13] = 0`.
//! `value_facts::build_element_read_congruence_facts` now ties two reads of one
//! canonical base whenever their indices agree, for any root type.
//!
//! # Fixtures
//!
//! `tests/fixtures/element_read_congruence_*_mir.json` are the compiler's own extraction
//! of [`tests/data/element_read_congruence.rs`] (the design's Appendix A.1-A.5), captured
//! from the repository root, so `span.file` is repo-relative, with
//!
//! ```text
//! rustc --edition 2024 --crate-type lib -Ztrust-verify-profile=unix_hardened \
//!       -Ztrust-policy=advisory -Ztrust-dump=mir:<dir> \
//!       crates/trust-vcgen/tests/data/element_read_congruence.rs
//! ```
//!
//! by the stage 1 of `ca1f3317eb` (2026-10-20), and renamed
//! `element_read_congruence_<fn>_mir.json`; nothing else was edited. (An earlier dump by
//! a stage 1 of a parent tree was byte-identical for 26 of the 29 bodies; the other three
//! differed only in the `def_index`/`stable_crate_id` of std callees, a rebuilt sysroot's
//! crate identity.) Every `must_refute_*` body is written as a real defect on the input
//! in its comment (the design's B.2 ran its six challenge counters natively at `-O0` and
//! `-O3`; this landing ran none natively); every other body is correct.
//!
//! Every row is produced through the entry the compiler calls (hardened profile ON)
//! and decided by the deterministic in-process `ay` router (`support/realmir_rows.rs`).
//!
//! # Measured (2026-10-20, every `Sub` row and its hardened twin of these fixtures and of
//! # `false_refutation_dec_*`, 256 rows in all)
//!
//! | Body | Before the congruence | After |
//! |---|---|---|
//! | `dec_first_nonzero` (here, and `false_refutation_dec_first_nonzero` line 32) | FAILED, FAILED | PROVED, PROVED |
//! | `mut_guard_then_use`, `mut_equal_by_guard`, `reseated_root_then_guard_then_use` | FAILED, FAILED | PROVED, PROVED |
//! | `guard_then_use`, `equal_by_guard`, `imm_guard_then_use`, `imm_first_nonzero_pred` | PROVED, PROVED | unchanged |
//! | every `must_refute_*`, `dec_every`, `dec_neighbour` | FAILED, FAILED | unchanged |
//!
//! No other row of the 256 changed. The mutants of the design's §2.5 are recorded in
//! `docs/DECISION_QUEUE.md` (VGAPS-G1).
#[path = "support/realmir_rows.rs"]
mod realmir_rows;

use realmir_rows::{PRIMARY_SUB, TWIN_SUB, Verdict, expect, expect_certified};

/// The fixtures' file-name prefix.
const FIXTURE_PREFIX: &str = "element_read_congruence_";

fn rows(name: &str) -> Vec<realmir_rows::Row> {
    realmir_rows::rows(FIXTURE_PREFIX, name, &[])
}

/// Both `Sub` rows (the per-statement row and its hardened twin) of `name` at `line`.
fn sub_rows(name: &str, line: u32, want: Verdict, why: &str) {
    let rows = rows(name);
    expect(&rows, line, PRIMARY_SUB, 1, want, why);
    expect(&rows, line, TWIN_SUB, 1, want, why);
}

/// FAILING FIRST: the guarded re-read through fresh index temps of a `&mut` slice, a
/// mutable index local, a reseated root, and an index equality the guard states. Each
/// was refuted before the congruence, each is a correct program, and each now proves.
#[test]
fn a_guarded_reread_through_fresh_index_temps_proves() {
    sub_rows("dec_first_nonzero", 13, Verdict::Proved, "`digits[i] -= 1` under `digits[i] > 0`");
    sub_rows("mut_guard_then_use", 57, Verdict::Proved, "`a[i] - 1` under `a[i] > 0`");
    sub_rows(
        "reseated_root_then_guard_then_use",
        242,
        Verdict::Proved,
        "the guard and the use read the reseated `a`",
    );
    sub_rows("mut_equal_by_guard", 246, Verdict::Proved, "`a[j] - 1` under `i == j && a[i] > 0`");
}

/// The shared-slice twins and the parameter-index controls proved before the
/// congruence and still prove.
#[test]
fn the_shared_slice_twins_still_prove() {
    sub_rows("guard_then_use", 21, Verdict::Proved, "a parameter index");
    sub_rows("equal_by_guard", 24, Verdict::Proved, "`i == j` under a shared slice");
    sub_rows("imm_guard_then_use", 201, Verdict::Proved, "a shared slice, a mutable index");
    sub_rows("imm_first_nonzero_pred", 207, Verdict::Proved, "a shared slice in a loop");
}

/// Two reads that are NOT one element: another index, another base, a moved index, a
/// copy of the base taken before a reseat. The congruence's disequality disjunct holds
/// for each, so no tie follows, and each still refutes.
#[test]
fn reads_of_different_elements_still_refute() {
    for (name, line, why) in [
        ("must_refute_other_index", 28, "`a[j]` under a guard on `a[i]`"),
        ("must_refute_other_base", 32, "`b[i]` under a guard on `a[i]`"),
        ("must_refute_other_base_temps", 166, "`b[i]` under a guard on `a[i]`, index temps"),
        ("must_refute_index_moved_temps", 118, "`i = j` between the reads"),
        ("must_refute_copy_then_reseat", 256, "`r1 = a; a = b`: two bases"),
        ("must_refute_two_reborrows_across_reseat", 229, "a reborrow on each side of `a = b`"),
        ("must_refute_reseat_temps", 176, "`a = b` between the reads"),
    ] {
        sub_rows(name, line, Verdict::Failed, why);
    }
}

/// A WRITE between the two reads: a store, a call that writes through `&mut`, a raw
/// alias, a nested store, the previous iteration's store, a reborrow's store, an element
/// reference's store, `ptr::write`, a store through a field's slice and its reborrow,
/// and the loop shapes whose reaching-set token collides across iterations. Each is a
/// real defect on the input in its comment and still refutes. Mutant G1-M7 (an element
/// definition survives every outflow kill of `path_defs::block_base_outflow`) turned the
/// call, raw-alias, `ptr::write` and both field-slice rows PROVED, so the kill is what
/// keeps those refuted; it left the loop shapes, the store and the element reference's
/// store refuted, so something besides that kill also ends those reads' tie (measured,
/// not attributed; `docs/DECISION_QUEUE.md` VGAPS-G1).
#[test]
fn every_write_between_the_reads_still_refutes() {
    for (name, line, why) in [
        ("must_refute_store_between_temps", 89, "`a[k] = 0` between the reads"),
        ("must_refute_call_between_temps", 102, "`zero_all2(a)` between the reads"),
        ("must_refute_raw_alias_temps", 155, "`*p.add(k) = 0` between the reads"),
        ("must_refute_nested_temps", 189, "`a[k][1] = 0` between the reads"),
        ("must_refute_prev_iteration_temps", 135, "the previous iteration's `a[i] = 0`"),
        ("must_refute_reborrow_store_temps", 269, "`r[k] = 0` through `r = &mut *a`"),
        ("must_refute_elem_ref_store_temps", 283, "`*r = 0` through `r = &mut a[k]`"),
        ("must_refute_ptr_write_temps", 296, "`ptr::write(a.as_mut_ptr().add(k), 0)`"),
        ("must_refute_field_slice_store", 335, "`h.s[k] = 0` between the reads"),
        ("must_refute_field_slice_reborrow_store", 349, "`r[k] = 0` through `r = &mut *h.s`"),
        ("must_refute_loop_collision_temps", 71, "a conditional `a[k] = 0` in the loop"),
        ("must_refute_loop_elem_ref_collision", 314, "a conditional `*r = 0` in the loop"),
        ("must_refute_loop_conditional_store_ptr", 44, "a conditional `*p = 0` in the loop"),
    ] {
        sub_rows(name, line, Verdict::Failed, why);
    }
}

/// VGAPS-G1C: every row the congruence proves, its `Sub` row and its hardened twin, is
/// also re-checked by the Clean kernel (`trust_certify::certify_vc`, the congruence lane:
/// the index disequality closed by `Int.le_antisymm`, the twin's overflow core under the
/// tie's branch). Before that lane only `guard_then_use`'s two rows certified.
#[test]
fn every_congruence_row_kernel_certifies() {
    for (prefix, name, line) in [
        (FIXTURE_PREFIX, "dec_first_nonzero", 13),
        ("false_refutation_", "dec_first_nonzero", 32),
        (FIXTURE_PREFIX, "guard_then_use", 21),
        (FIXTURE_PREFIX, "equal_by_guard", 24),
        (FIXTURE_PREFIX, "mut_guard_then_use", 57),
        (FIXTURE_PREFIX, "imm_guard_then_use", 201),
        (FIXTURE_PREFIX, "imm_first_nonzero_pred", 207),
        (FIXTURE_PREFIX, "reseated_root_then_guard_then_use", 242),
        (FIXTURE_PREFIX, "mut_equal_by_guard", 246),
    ] {
        let rows = realmir_rows::rows(prefix, name, &[]);
        let why = format!("{prefix}{name}");
        expect_certified(&rows, line, PRIMARY_SUB, 1, true, &why);
        expect_certified(&rows, line, TWIN_SUB, 1, true, &why);
    }
}

/// The element-read congruences among `formula`'s conjuncts and disjunctions
/// (`Or([.., Eq(read_a, read_b)])` with both reads element names `base*[index]`).
fn congruences(formula: &trust_types::Formula) -> usize {
    use trust_types::Formula;
    let element = |f: &Formula| matches!(f, Formula::Var(name, _) if name.contains("*["));
    match formula {
        Formula::And(conjuncts) => conjuncts.iter().map(congruences).sum(),
        Formula::Or(disjuncts) => match disjuncts.last() {
            Some(Formula::Eq(a, b)) if disjuncts.len() > 1 && element(a) && element(b) => 1,
            _ => disjuncts.iter().map(congruences).sum(),
        },
        _ => 0,
    }
}

/// VGAPS-G2-FOLLOWUP (2) (2026-10-22, `docs/DECISION_QUEUE.md`): a congruence reaches only
/// a row that names both of its reads (`value_facts::RowGlobalFacts`). The whole-corpus
/// parity sweep found one correct row G1 had cost its proof: `argument_premise_clip`'s
/// `[unreach]` row at line 21 (aterm-gpu's `clip_textured_quad_x`), PROVED and
/// kernel-certified before G1 and Unknown from G1 (`5600bf48aa`) on, with the body's six
/// `f32` congruences over `rect[_]` and `uv[_]` conjoined onto a row that reads neither.
/// It carries none of them now and proves and certifies again. The control: the rows
/// that do read two of those elements (the float rows of lines 35-41) still carry theirs.
#[test]
fn a_congruence_reaches_only_the_rows_that_read_both_its_elements() {
    let rows = realmir_rows::rows("argument_premise_", "clip", &[]);
    let unreach = realmir_rows::at(&rows, 21, "Unreachable");
    assert_eq!(unreach.len(), 1, "one `[unreach]` row at line 21");
    assert_eq!(
        congruences(&unreach[0].vc.formula),
        0,
        "the row reads no `rect`/`uv` element: {:?}",
        unreach[0].vc.formula
    );
    expect_certified(&rows, 21, "Unreachable", 1, true, "the discriminant is 0 or 1");
    let carried: usize = rows
        .iter()
        .filter(|r| r.kind.contains("FloatOverflowToInfinity"))
        .map(|r| congruences(&r.vc.formula))
        .sum();
    assert!(carried > 0, "control: the rows reading `rect`/`uv` elements keep their congruences");
}

/// Review of `95449037cd` (2026-10-22, `docs/DECISION_QUEUE.md` VGAPS-G2-FOLLOWUP): a read
/// that only a LATER conjunct names keeps its congruence. `mut_match_then_use` switches
/// on the element itself (`switchInt(copy (*a)[_12])`), so the `Sub` row's path guard
/// `a*[_12] != 0` is the one conjunct naming the guard's read, and the safety and
/// hardened lanes conjoin it after the global facts. Counting only the row and the other
/// global facts dropped the congruence and refuted this correct program
/// (`value_facts::late_conjunct_names` now counts the guard). Its two counters, a store
/// between the reads and another index, panic natively on the inputs in their comments
/// (`-O0` and `-O3`) and still refute. Both `Sub` rows are PROVED and not kernel-certified,
/// as they are with every congruence kept, so this pin asks for no certificate.
/// The three fixtures were dumped by the installed `trustc 0.11.0+g20565c325` with the
/// command above, from the repository root (its other dumps of this file differ from the
/// committed ones only in std callees' crate identity, as noted above).
#[test]
fn a_read_only_a_path_guard_names_keeps_its_congruence() {
    sub_rows("mut_match_then_use", 367, Verdict::Proved, "`a[i] - 1` under `match a[i]`");
    sub_rows("must_refute_match_store_between", 384, Verdict::Failed, "`a[k] = 0` between");
    sub_rows("must_refute_match_other_index", 396, Verdict::Failed, "`a[j]` under `match a[i]`");
}
