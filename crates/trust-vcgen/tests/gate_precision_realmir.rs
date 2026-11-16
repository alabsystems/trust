//! Trust: 2026-10-17 (gate RCA, precision) — rows the candidate gate of 2026-10-16
//! (trust 7f3690ed73 against the seal 321aaeda75) lost on CORRECT programs, each beside
//! a negative control that must stay unproved.
//!
//!  * T5 — a PROJECTED slice-range bound read in the index call's own block
//!    (`self.buf[self.len..64]`, `self.buf[self.buf_len..]`, `&mut buf[*filled..]`) is
//!    stated, not declined to `slice-range-bounds-unresolved`
//!    (`panic_calls::projected_bound_read_in_call_block`). Controls: an unguarded bound
//!    is REFUTED on a realised value; a bound whose field is overwritten in the same
//!    block before the call stays declined (naming the field at the call would prove a
//!    program that panics at `n = 65`).
//!  * T6 — a `BoundsCheck` assert a loop-yield fact proves in range keeps its hardened
//!    twin (`hardened::append_assert_panic_vcs`), which proves. Control: an
//!    `enumerate` over three items indexing a two-slot array keeps its twin REFUTED.
//!  * T4 — a slice of a RECURSIVE enum (a bare datatype marker resolved through
//!    `body.datatype_defs`) takes the `len <= isize::MAX` ceiling, so `i += 2` under
//!    `i < p.len()` proves (`type_ranges::slice_elem_is_definitely_non_zst`). Control: a
//!    zero-sized element keeps no ceiling and the add is refuted.
//!  * T7 — an f32 add of a tiny constant (`self.quiet + 4.0`) keeps its
//!    `FloatOverflowToInfinity` row, whose witness is false on a ground conjunct
//!    (`float_overflow::float_add_witness_refutes_by_constant`). Control: `+ 3.0e38`
//!    keeps a witness with no ground-false conjunct.
//!  * T1 — a closure's by-reference capture `(*_1).k` whose every value the COMPILER
//!    certified a fresh shared borrow (`VcgenContext::with_fresh_shared_capture_fields`,
//!    FRESH-CAPTURE-1) keeps its pointee across a call, so `p % w` after `p / w` and a
//!    call proves (`path_defs::premised_capture_fields`). Controls: the same body with no
//!    premise, a premise on the other capture only, a premise on a field that is not a
//!    reference, a premise owned by another function, and a body that writes under `_1`
//!    all keep the remainder REFUTED.
//!  * T8 — a `for i in 0..self.len` whose field the body writes after the loop yields
//!    `i < _end` on the end temp (`iterator_yield::end_projected_copy_temp`), so `i + 1`
//!    proves instead of being declined `UnmodeledCalleeReturn`. Control: `i + 2`
//!    overflows at `len = usize::MAX` and is refuted.
//!
//!  * D2 — `t.col + 1` under `t.col >= cols => continue` and a call, where `t` comes out
//!    of `Iterator::next`'s `Option<&T>` (`for t in &v`, and `enumerate`'s
//!    `Option<(usize, &T)>`): the call-return retag covers the payload, so the guard on
//!    `*t` survives the call and the add PROVES (`path_defs::call_return_enum_root`,
//!    RETURN-PAYLOAD-RETAG-1; and, since the element is named `TrailCell` like aterm's,
//!    CELL-NAME-TAIL-1: a user type named like a cell is decided by its fields). Controls: an `Option<&T>` LOADED FROM MEMORY keeps its
//!    call havoc, and an unguarded `t.col + 1` is refuted.
//!
//! THE FIXTURES (`tests/fixtures/gate_precision/o0_<fn>.json`) are
//! `-Ztrust-dump=mir-only` captures of `gate_precision.rs` beside them:
//!
//! ```text
//! trustc --edition 2024 --crate-type lib --emit=metadata -Copt-level=0 \
//!        -Ztrust-verify=on -Ztrust-verify-profile=unix_hardened -Ztrust-policy=advisory \
//!        -Ztrust-dump=mir-only:<dir> gate_precision.rs
//! ```
//!
//! on the candidate toolchain stage-trust-7f3690ed (2026-10-17), written compact, span
//! files rewritten to `<dump-root>/`. Verdicts are this crate's, through the compiler's
//! configured generation entry (hardened lane on) and the deterministic in-process `ay`
//! router; certification is `trust_certify::certify_vc`.

use std::collections::HashSet;

use trust_types::{
    BlockId, Formula, VcKind, VerifiableFunction, VerificationCondition, VerificationResult,
};

#[path = "support/test_router.rs"]
mod test_router;

const SOLVER_STACK_BYTES: usize = 256 * 1024 * 1024;

fn load(name: &str) -> VerifiableFunction {
    let path =
        format!("{}/tests/fixtures/gate_precision/o0_{name}.json", env!("CARGO_MANIFEST_DIR"));
    let text = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    serde_json::from_str(&text).unwrap_or_else(|e| panic!("fixture `{name}` must deserialize: {e}"))
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Verdict {
    Proved,
    Failed,
    Other,
}

#[derive(Debug)]
struct Row {
    vc: VerificationCondition,
    verdict: Verdict,
    certified: bool,
    result: String,
}

fn verdicts(name: &str) -> Vec<Row> {
    verdicts_of(load(name), None)
}

/// [`verdicts`] of `func` under a context owned by `owner` (default: `func`'s own def
/// path) carrying the FRESH-CAPTURE-1 capture fields `fields`, as the compiler installs
/// them for a certified closure body.
fn verdicts_of(
    func: VerifiableFunction,
    premise: Option<(Option<String>, Vec<usize>)>,
) -> Vec<Row> {
    std::thread::Builder::new()
        .stack_size(SOLVER_STACK_BYTES)
        .spawn(move || {
            let context = match premise {
                None => trust_vcgen::VcgenContext::for_function(func.def_path.clone()),
                Some((owner, fields)) => trust_vcgen::VcgenContext::for_function(
                    owner.unwrap_or_else(|| func.def_path.clone()),
                )
                .with_fresh_shared_capture_fields(fields),
            };
            let db = trust_vcgen::SummaryDatabase::new();
            let ops: HashSet<(BlockId, usize)> = HashSet::new();
            let (solver_vcs, preclassified) =
                trust_vcgen::generate_vcs_with_discharge_and_summaries_configured_with_context_and_box_deref_ops(
                    &func, &db, true, &context, &ops,
                );
            let router = test_router::deterministic_test_router();
            let decided = solver_vcs.into_iter().map(|vc| {
                let (_, result) = router
                    .verify_all(std::slice::from_ref(&vc))
                    .into_iter()
                    .next()
                    .expect("one verdict per VC");
                (vc, result)
            });
            preclassified
                .into_iter()
                .chain(decided)
                .map(|(vc, result)| {
                    let certified = trust_certify::certify_vc(&vc).is_some();
                    let verdict = match result {
                        VerificationResult::Proved { .. } => Verdict::Proved,
                        VerificationResult::Failed { .. } => Verdict::Failed,
                        _ => Verdict::Other,
                    };
                    Row { vc, verdict, certified, result: format!("{result:?}") }
                })
                .collect()
        })
        .expect("spawn")
        .join()
        .expect("generation thread")
}

fn kind_text(vc: &VerificationCondition) -> String {
    format!("{:?}", vc.kind)
}

/// The rows at `line:col` whose kind's debug spelling contains `needle`.
fn at<'r>(rows: &'r [Row], line: u32, col: u32, needle: &str) -> Vec<&'r Row> {
    rows.iter()
        .filter(|r| {
            r.vc.location.line_start == line
                && r.vc.location.col_start == col
                && kind_text(&r.vc).contains(needle)
        })
        .collect()
}

/// Exactly one row at `line:col` matches `needle`; it is returned.
fn one<'r>(rows: &'r [Row], line: u32, col: u32, needle: &str) -> &'r Row {
    let hits = at(rows, line, col, needle);
    assert_eq!(
        hits.len(),
        1,
        "{line}:{col}: expected exactly one `{needle}` row; all rows: {:#?}",
        rows.iter()
            .map(|r| (
                r.vc.location.line_start,
                r.vc.location.col_start,
                kind_text(&r.vc),
                r.verdict
            ))
            .collect::<Vec<_>>()
    );
    hits[0]
}

fn declined_range(row: &Row) -> bool {
    matches!(&row.vc.kind, VcKind::UnsupportedMir { kind, .. } if kind == "slice-range-bounds-unresolved")
}

// ─── T5 ───────────────────────────────────────────────────────────────────────

/// `push_bytes` (aterm-core `stack_response.rs:46`), `finalize` (aterm-digest
/// `sha256.rs:150`) and `fill` (astream-aead `stream.rs:468`): every projected range
/// bound read in the call's block states its `SliceBoundsCheck` row and it PROVES.
/// Before the fix each was the declined `slice-range-bounds-unresolved` row.
#[test]
fn a_projected_range_bound_read_in_the_call_block_is_stated_and_proves() {
    for (name, line, col) in
        [("push_bytes", 19, 20), ("push_bytes", 23, 16), ("finalize", 54, 20), ("fill", 68, 29)]
    {
        let rows = verdicts(name);
        assert!(
            at(&rows, line, col, "UnsupportedMir").iter().all(|r| !declined_range(r)),
            "{name} {line}:{col}: the bound must not be declined"
        );
        let row = one(&rows, line, col, "SliceBoundsCheck");
        assert_eq!(row.verdict, Verdict::Proved, "{name} {line}:{col}: {}", row.result);
    }
    // The two the kernel certifies on this entry (`push_bytes`' rows prove under ay
    // without a kernel certificate, as the seal's did on the same entry).
    for (name, line, col) in [("finalize", 54, 20), ("fill", 68, 29)] {
        let rows = verdicts(name);
        assert!(one(&rows, line, col, "SliceBoundsCheck").certified, "{name} {line}:{col}");
    }
}

/// Negative controls. `unguarded` (`self.buf[self.len..]`, no guard) is REFUTED on a
/// realised `len > 64`. `stale_store` reads `self.len` into the range, then overwrites
/// the field IN THE SAME BLOCK before the call: the field at the call (0) is not the
/// bound (`n`), so the row stays declined — never proved (it panics at `n = 65`).
#[test]
fn an_unguarded_bound_refutes_and_a_same_block_store_declines() {
    let rows = verdicts("unguarded");
    let row = one(&rows, 28, 16, "SliceBoundsCheck");
    assert_eq!(row.verdict, Verdict::Failed, "{}", row.result);

    let rows = verdicts("stale_store");
    let declined: Vec<&Row> = rows.iter().filter(|r| declined_range(r)).collect();
    assert_eq!(declined.len(), 1, "stale_store keeps its declined range row: {rows:#?}");
    assert!(
        rows.iter().all(|r| !(r.vc.location.line_start == 37
            && matches!(r.vc.kind, VcKind::SliceBoundsCheck)
            && r.verdict == Verdict::Proved
            && r.vc.location.col_start == 16)),
        "the stale range must never be proved"
    );
}

// ─── T6 ───────────────────────────────────────────────────────────────────────

/// `map_builder_new` (aterm-font `shape/map.rs:233`): both `chosen[i]` / `index[i]`
/// asserts keep their hardened `BoundsCheck` twin, and it PROVES with its sibling.
/// Before the fix the loop-yield skip removed both twins (the enumerate fact now reads
/// the array length through the unsize cast). Control: `map_builder_short` (three items,
/// two slots) keeps its twin REFUTED.
#[test]
fn a_loop_yielded_index_keeps_its_hardened_twin() {
    let rows = verdicts("map_builder_new");
    for line in [89, 90] {
        let twin = one(&rows, line, 8, "mir_assert::BoundsCheck");
        assert_eq!(twin.verdict, Verdict::Proved, "{line}: {}", twin.result);
        let l0 = one(&rows, line, 8, "IndexOutOfBounds");
        assert_eq!(l0.verdict, Verdict::Proved, "{line}: {}", l0.result);
    }
    let rows = verdicts("map_builder_short");
    let twin = one(&rows, 101, 8, "mir_assert::BoundsCheck");
    assert_eq!(twin.verdict, Verdict::Failed, "{}", twin.result);
}

// ─── T4 ───────────────────────────────────────────────────────────────────────

/// `without_lifetime` (aterm-wasm-abi-macros `parse.rs:373`): `i += 2` under
/// `i < p.len()` over `&[Tt]`, `Tt` recursive (`Group(Delim, Vec<Tt>)`), PROVES and is
/// certified. Control: `skip_zst` over a zero-sized element keeps no ceiling, so the
/// same add is REFUTED.
#[test]
fn a_recursive_enum_slice_takes_the_isize_ceiling_and_a_zst_slice_does_not() {
    let rows = verdicts("without_lifetime");
    let row = one(&rows, 127, 12, "ArithmeticOverflow { op: Add");
    assert_eq!(row.verdict, Verdict::Proved, "{}", row.result);
    assert!(row.certified);

    let rows = verdicts("skip_zst");
    let row = one(&rows, 143, 8, "ArithmeticOverflow { op: Add");
    assert_eq!(row.verdict, Verdict::Failed, "{}", row.result);
}

// ─── T7 ───────────────────────────────────────────────────────────────────────

/// Ground evaluation of the bit-vector terms the float witness compares: a constant,
/// or an extract of a constant. `None` for anything with a free variable.
fn ground_bv(f: &Formula) -> Option<u128> {
    match f {
        Formula::BitVec { value, .. } => u128::try_from(*value).ok(),
        Formula::BvExtract { inner, high, low } => {
            let v = ground_bv(inner)?;
            let width = high - low + 1;
            let mask = if width >= 128 { u128::MAX } else { (1u128 << width) - 1 };
            Some((v >> low) & mask)
        }
        _ => None,
    }
}

/// Whether some top-level conjunct of `f` is a ground comparison that is FALSE.
fn has_ground_false_conjunct(f: &Formula) -> bool {
    match f {
        Formula::And(conjuncts) => conjuncts.iter().any(has_ground_false_conjunct),
        Formula::BvULe(a, b, _) => {
            matches!((ground_bv(a), ground_bv(b)), (Some(x), Some(y)) if x > y)
        }
        Formula::BvULt(a, b, _) => {
            matches!((ground_bv(a), ground_bv(b)), (Some(x), Some(y)) if x >= y)
        }
        Formula::Bool(false) => true,
        _ => false,
    }
}

/// `perform_trick` (aterm-effects `kitty_pet.rs:7601`): `self.quiet + 4.0` (f32) keeps
/// its `FloatOverflowToInfinity` row, and the row's witness is false on a ground
/// conjunct (`T <= |4.0|` with `T = 2^103`), so no model of it exists. Before the fix the
/// interval discharge dropped the row. Control: `+ 3.0e38` (above `T`) keeps a row whose
/// witness has no ground-false conjunct.
#[test]
fn an_add_of_a_tiny_constant_keeps_a_row_its_witness_refutes() {
    let rows = verdicts("perform_trick");
    let row = one(&rows, 157, 8, "FloatOverflowToInfinity");
    assert!(
        has_ground_false_conjunct(&row.vc.formula),
        "the witness must be refuted by its own constant: {:?}",
        row.vc.formula
    );
    let rows = verdicts("huge");
    let row = one(&rows, 162, 8, "FloatOverflowToInfinity");
    assert!(
        !has_ground_false_conjunct(&row.vc.formula),
        "a near-MAX constant must leave the witness satisfiable: {:?}",
        row.vc.formula
    );
}

// ─── T8 ───────────────────────────────────────────────────────────────────────

/// `delete` (aterm-font `shape/buffer.rs:550`): `for i in 0..self.len { if i + 1 <
/// self.len { self.merge(i, i + 2) } } self.len = j` — the `i + 1` row keeps its kind
/// and PROVES (certified), where it was declined `UnmodeledCalleeReturn`. Control:
/// `delete_two`'s `i + 2` is REFUTED.
#[test]
fn a_range_end_temp_bounds_the_payload_after_a_field_write() {
    let rows = verdicts("delete");
    assert!(
        at(&rows, 186, 15, "UnsupportedMir").is_empty(),
        "`i + 1` must not be declined: {rows:#?}"
    );
    let row = one(&rows, 186, 15, "ArithmeticOverflow { op: Add");
    assert_eq!(row.verdict, Verdict::Proved, "{}", row.result);
    assert!(row.certified);

    let rows = verdicts("delete_two");
    let row = one(&rows, 198, 15, "ArithmeticOverflow { op: Add");
    assert_eq!(row.verdict, Verdict::Failed, "{}", row.result);
}

// ─── T2 ───────────────────────────────────────────────────────────────────────

/// `relay` (aterm-ctl `redial.rs:1142/1144`): `n = a.min(s.len())` in a loop that
/// reseats `s`; both `&s[..n]` and `&s[n..]` PROVE through the global `n <= _len` fact
/// on the single-assignment length temp (`value_facts::single_assignment_length_temp`).
/// Control: `min_then_reseat` (the round-A8 shape, `s = b` between the `min` and the
/// index) is REFUTED — the temp still holds the OLD length.
#[test]
fn a_min_over_a_loop_rebound_slice_bounds_its_index() {
    let rows = verdicts("relay");
    for (line, col) in [(212, 32), (213, 14)] {
        let row = one(&rows, line, col, "SliceBoundsCheck");
        assert_eq!(row.verdict, Verdict::Proved, "{line}:{col}: {}", row.result);
    }
    let rows = verdicts("min_then_reseat");
    let row = one(&rows, 222, 5, "SliceBoundsCheck");
    assert_eq!(row.verdict, Verdict::Failed, "{}", row.result);
}

// ─── T3 ───────────────────────────────────────────────────────────────────────

/// `caret_col` (aterm-phase `phase.rs:1342` composer_index): `b[k]` under the inner
/// `while k < b.len()`, `b`'s length read through the `&String` it came from (a read
/// two tracked names rebind), PROVES, and so does its hardened twin: the group's value
/// identity (`version_ssa::ValueId::GroupOut`, asked through
/// `StmtVersionCtx::value_id_at_grouped`) keeps the guard's token. The controls are
/// PATH-GUARD-VALUE-1's own (`path_guard_value_identity_realmir.rs`: a write between
/// the guard and the row stays refuted).
#[test]
fn a_guard_on_a_group_read_keeps_its_token_when_nothing_writes_it() {
    let rows = verdicts("caret_col");
    let row = one(&rows, 233, 29, "SliceBoundsCheck");
    assert_eq!(row.verdict, Verdict::Proved, "{}", row.result);
    let twin = one(&rows, 233, 29, "mir_assert::BoundsCheck");
    assert_eq!(twin.verdict, Verdict::Proved, "the hardened twin: {}", twin.result);
}

// ─── T1 ───────────────────────────────────────────────────────────────────────

/// The `RemainderByZero` rows (the L0 row and any hardened twin) at `line:col`.
fn remainder_rows(rows: &[Row], line: u32, col: u32) -> Vec<&Row> {
    let hits = at(rows, line, col, "RemainderByZero");
    assert!(!hits.is_empty(), "{line}:{col}: no remainder row; rows: {rows:#?}");
    hits
}

/// `capture_ref_div_rem::{closure#0}` (the aterm-conformance `scan.rs:1460` shape) and
/// `word_cells::{closure#0}` (aterm-control `selection.rs:357`): `w` / `cols` is captured
/// by reference, `p / w` asserts it nonzero, a call runs, and `p % w` reads it again. With
/// the compiler's FRESH-CAPTURE-1 fields installed the capture's pointee survives the
/// call and every remainder row PROVES; CALL-HAVOC-ESCAPE-2 refuted it with `w = 0`.
#[test]
fn a_fresh_shared_capture_keeps_its_pointee_across_a_call() {
    let rows = verdicts_of(load("capture_ref_div_rem_closure"), Some((None, vec![0])));
    for row in remainder_rows(&rows, 255, 8) {
        assert_eq!(row.verdict, Verdict::Proved, "{}", row.result);
    }
    let rows = verdicts_of(load("word_cells_closure"), Some((None, vec![0, 1])));
    for row in remainder_rows(&rows, 263, 30) {
        assert_eq!(row.verdict, Verdict::Proved, "{}", row.result);
    }
}

/// Negative controls: the remainder stays REFUTED (a value a callee could have written)
/// when the premise is absent, names only the OTHER capture (`first_row`, field 1 of
/// `word_cells`' closure), names a field that is no capture, is owned by another
/// function, or when the body writes a place under `_1` (the re-gate declines it).
#[test]
fn a_capture_without_a_certified_premise_keeps_its_call_havoc() {
    let refuted = |rows: &[Row], line: u32, col: u32, what: &str| {
        assert!(
            remainder_rows(rows, line, col).iter().any(|r| r.verdict == Verdict::Failed),
            "{what}: the remainder must stay refuted: {rows:#?}"
        );
    };
    refuted(&verdicts("capture_ref_div_rem_closure"), 255, 8, "no premise");
    refuted(&verdicts("word_cells_closure"), 263, 30, "no premise");
    refuted(
        &verdicts_of(load("word_cells_closure"), Some((None, vec![1]))),
        263,
        30,
        "premise on the other capture",
    );
    refuted(
        &verdicts_of(load("capture_ref_div_rem_closure"), Some((None, vec![7]))),
        255,
        8,
        "premise on no capture",
    );
    refuted(
        &verdicts_of(
            load("capture_ref_div_rem_closure"),
            Some((Some("gate_precision::capture_ref_div_rem".to_string()), vec![0])),
        ),
        255,
        8,
        "premise owned by the parent",
    );
    // `(*_1).0 = copy _9` in the call's block: a body that writes under its
    // environment parameter gets no premise.
    let mut func = load("capture_ref_div_rem_closure");
    let span = func.span.clone();
    let block = func
        .body
        .blocks
        .iter_mut()
        .find(|b| matches!(b.terminator, trust_types::Terminator::Call { .. }))
        .expect("the call block");
    block.stmts.push(trust_types::Statement::Assign {
        place: trust_types::Place {
            local: 1,
            projections: vec![trust_types::Projection::Deref, trust_types::Projection::Field(0)],
        },
        rvalue: trust_types::Rvalue::Use(trust_types::Operand::Copy(trust_types::Place::local(9))),
        span,
    });
    refuted(&verdicts_of(func, Some((None, vec![0]))), 255, 8, "a write under `_1`");
}

// ─── D2 ───────────────────────────────────────────────────────────────────────

/// `draw_trail` (aterm-render `lib.rs:17913`) and its `enumerate` twin: the guard
/// `t.col >= cols => continue` on the reference `next()` returned survives the call
/// `row_is_uniform(..)`, so `t.col + 1` and its hardened twin PROVE. CALL-HAVOC-ESCAPE-2
/// havocked `*t` there (a reference read out of a local's payload), and the compiler
/// withheld the spurious counterexample.
#[test]
fn a_reference_out_of_a_call_returned_option_keeps_its_guard_across_a_call() {
    for (name, line) in [("draw_trail", 295), ("draw_trail_enumerate", 308)] {
        let rows = verdicts(name);
        let row = one(&rows, line, 19, "ArithmeticOverflow { op: Add");
        assert_eq!(row.verdict, Verdict::Proved, "{name}: {}", row.result);
        let twin = one(&rows, line, 19, "mir_assert::Overflow(Add)");
        assert_eq!(twin.verdict, Verdict::Proved, "{name} twin: {}", twin.result);
    }
}

/// Negative controls: `cached_trail` reads the `Option<&TrailCell>` out of
/// `input.cached` (stored in memory, never retagged: a callee may write `*t` through a
/// raw pointer it holds), and `unguarded_trail` has no guard on `t.col`. Both adds are
/// REFUTED.
#[test]
fn a_loaded_or_unguarded_trail_reference_stays_refuted() {
    for (name, line) in [("cached_trail", 321), ("unguarded_trail", 331)] {
        let rows = verdicts(name);
        let row = one(&rows, line, 19, "ArithmeticOverflow { op: Add");
        assert_eq!(row.verdict, Verdict::Failed, "{name}: {}", row.result);
    }
}
