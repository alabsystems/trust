//! TRUST-KI-1015-1, the sub-slice shape: a correct program's `rest.len() - 4` under its
//! parent's guard was FAILED (refuted with a counterexample no execution reaches).
//!
//! # The defect (measured on the channel seal `b58a105dde`, raw `trustc`)
//!
//! `if input.len() < 6 { return None } let rest = &input[2..]; rest.len() - 4`: the
//! plain `[overflow:sub]` row and its hardened `mir_assert::Overflow(Sub)` twin were
//! FAILED by the in-process `ay` lane (`solver: ay-in-process`; the trust-mc typed-CHC
//! evidence on both rows was demoted to unknown and did not refute) with the model
//! `input__slice_len = 6, rest__slice_len#s4_t = 0`. `&input[2..]` is the call
//! `<[u8] as Index<RangeFrom<usize>>>::index(copy input, move _13)`, whose destination's
//! length name was a fresh version bounded only by `0 <= len <= isize::MAX`. Every SAFE
//! function below was FAILED the same way on the channel (`&s[a..b]`, `&s[..b]`, a
//! symbolic start, `&mut s[2..]`, an array or `str` receiver, a sub-slice of a
//! sub-slice, `s = &s[2..]` in place and in a loop, `split_at`), except `b7`/`b7y`
//! (`chunks_exact`/`chunks` items, proved by the adapter-yield lanes), `b8` (the guard
//! is on the sub-slice itself) and `b21` (the loop guard's own length, no sub-slice
//! before the subtraction), which are controls.
//!
//! # The fix
//!
//! `generate/range_index_len.rs`: on the normal return of core's range index of a
//! built-in slice, array or `str`, the result's length is `len - a`, `b - a` or `b`
//! (`RangeFrom`, `Range`, `RangeTo`), and `split_at(mid)`'s halves are `mid` and
//! `len - mid` — post-return definitions of the call in the path-definition fixpoint,
//! read from the same range resolution the `RangeIndex` row uses. See that module for
//! the gates.
//!
//! # What these tests pin
//!
//! * every SAFE function's two `Sub` rows are PROVED;
//! * every UNSAFE twin (guard off by one, guard removed, wrong offset, wrong width,
//!   wrong range end, a sub-slice of the wrong slice, a too-deep nested cut, a loop
//!   that can leave the slice empty; three starts spelled by an `OpaqueScalar`) keeps
//!   both rows FAILED: the fact never makes a real underflow unsatisfiable, and a model
//!   that satisfies it is an execution;
//! * the gates: the same body with the index callee renamed to a user trait's
//!   `index`, with its `callee_key` not from the real sysroot, or with an `Index` impl
//!   whose self type is not a built-in slice gets no fact (the SAFE row is then NOT
//!   proved), and a call whose destination is its own receiver gets none (a real
//!   underflow stays refuted; without the gate it read PROVED);
//! * the inlined `SliceIndex::index(range, slice)` spelling gets the fact too;
//! * two correct shapes whose per-statement row is still FAILED for other causes have
//!   their hardened twin PROVED (`SAFE_TWIN_ONLY`; docs/KNOWN_HAZARDS.md).
//!
//! The four gates no program-level test reaches alone (the left-side kill, the
//! receiver's MIR type, `split_at`'s unsigned `mid`, the `OpaqueScalar` gate) are pinned
//! by the unit tests in `generate/range_index_len.rs` (`gate_tests`).
//!
//! # Falsification (2026-10-15, re-run at the review's polish; each mutant one edit of
//! `range_index_len.rs`)
//!
//! ```text
//! mutant                                         tests that go red
//! the fact off (no definitions at all)           a_sub_slice_length_under_its_parents_guard_is_proved,
//!                                                the_slice_index_spelling_carries_the_length_too,
//!                                                the_twin_of_a_sub_slice_length_is_proved_where_its_primary_is_not_yet
//! no real-sysroot callee_key required            an_index_callee_not_from_the_real_sysroot_mints_no_length
//! any indexed self type admitted                 an_index_of_a_non_builtin_self_type_mints_no_length
//! right side not checked against the call's kill a_call_whose_destination_is_its_own_receiver_mints_no_length
//! `RangeFrom` length `len - a + 1`               a_real_underflow_of_a_sub_slice_length_stays_refuted
//! `split_at` tail `len - mid + 1`                a_real_underflow_of_a_sub_slice_length_stays_refuted
//! left side need not be written by the call      gate_tests::a_definition_whose_left_side_the_call_does_not_write_is_refused
//! no `OpaqueScalar` gate                         gate_tests::a_body_that_mentions_an_opaque_scalar_gets_no_definition
//!                                                (the three opaque-start underflows here stay refuted)
//! no receiver MIR-type gate                      gate_tests::a_receiver_whose_mir_type_is_not_a_builtin_reference_gets_no_fact
//! no unsigned-`mid` gate                         gate_tests::a_split_at_whose_mid_is_not_unsigned_gets_no_fact
//! ```
//!
//! # Fixtures
//!
//! `tests/fixtures/subslice_len/<fn>.json` are the compiler's own extraction of
//! `tests/data/subslice_len.rs`, captured with the channel seal's raw `trustc`
//! (`b58a105dde`):
//!
//! ```text
//! trustc --crate-type lib --edition 2024 --crate-name repro --emit=metadata \
//!        -Ztrust-verify=on -Ztrust-policy=advisory -Ztrust-dump=mir-only:<dir> subslice_len.rs
//! ```
//!
//! with only the `span.file` fields rewritten to the repo-relative source path. Every
//! row is produced through the entry the compiler calls (hardened profile ON) and
//! decided by the deterministic in-process `ay` router, as in
//! `false_refutation_shapes_realmir.rs`.
use std::collections::HashSet;

use trust_types::{BlockId, Terminator, VerifiableFunction, VerificationResult};

#[path = "support/test_router.rs"]
mod test_router;

/// Real extracted MIR carries deep recursive `Formula` walks.
const SOLVER_STACK_BYTES: usize = 256 * 1024 * 1024;

fn load(name: &str) -> VerifiableFunction {
    let path = format!("{}/tests/fixtures/subslice_len/{name}.json", env!("CARGO_MANIFEST_DIR"));
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("fixture `{name}` must be readable: {e}"));
    serde_json::from_str(&text).unwrap_or_else(|e| panic!("fixture `{name}` must deserialize: {e}"))
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Verdict {
    Proved,
    Failed,
    Other,
}

#[derive(Debug, Clone)]
struct Row {
    kind: String,
    line: u32,
    verdict: Verdict,
    result: String,
}

/// Every row of `func`, hardened profile ON.
fn rows_of(func: VerifiableFunction) -> Vec<Row> {
    let ops: HashSet<(BlockId, usize)> = HashSet::new();
    std::thread::Builder::new()
        .stack_size(SOLVER_STACK_BYTES)
        .spawn(move || {
            let context = trust_vcgen::VcgenContext::for_function(func.def_path.clone());
            let db = trust_vcgen::SummaryDatabase::new();
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
                .map(|(vc, result)| Row {
                    kind: format!("{:?}", vc.kind),
                    line: vc.location.line_start,
                    verdict: match result {
                        VerificationResult::Proved { .. } => Verdict::Proved,
                        VerificationResult::Failed { .. } => Verdict::Failed,
                        _ => Verdict::Other,
                    },
                    result: format!("{result:?}"),
                })
                .collect()
        })
        .expect("spawn")
        .join()
        .expect("generation thread")
}

const PRIMARY_SUB: &str = "ArithmeticOverflow { op: Sub";
const TWIN_SUB: &str = "mir_assert::Overflow(Sub)";

/// The plain `[overflow:sub]` row and its hardened twin at `line`: exactly one of each.
fn sub_pair(name: &str, rows: &[Row], line: u32) -> [Row; 2] {
    let pick = |needle: &str| {
        let hits: Vec<&Row> =
            rows.iter().filter(|r| r.line == line && r.kind.contains(needle)).collect();
        assert_eq!(hits.len(), 1, "{name}:{line}: expected one `{needle}` row; rows: {rows:#?}");
        hits[0].clone()
    };
    [pick(PRIMARY_SUB), pick(TWIN_SUB)]
}

/// SAFE: `(fixture, line of the subtraction)`. Each was FAILED on the channel except
/// where noted in the module doc; each must be PROVED on both rows.
const SAFE: &[(&str, u32)] = &[
    ("a15_subslice_ok", 14),
    ("b1_from_ok", 34),
    ("b2_range_ok", 67),
    ("b3_range_sym_ok", 85),
    ("b4_to_ok", 103),
    ("b5_split_at_ok", 121),
    ("b6_nested_ok", 140),
    ("b7_chunks_exact_ok", 157),
    ("b8_guard_on_rest", 180),
    ("b10_from_sym_ok", 198),
    ("b7y_chunks_nonempty_ok", 214),
    ("b12_reslice_ok", 246),
    ("b14_array_ok", 263),
    ("b15_str_ok", 279),
    ("b20_range_two_sym_ok", 318),
    ("b11b_index_mut_no_store_ok", 336),
    ("b21_loop_guard_len_ok", 344),
];

/// SAFE, and PROVED on the hardened twin only. The fact reaches both rows; on the
/// per-statement row it does not decide the subtraction, for causes outside the
/// sub-slice relation (docs/KNOWN_HAZARDS.md, TRUST-KI-1015-1), and that row is not
/// asserted here:
///  * `b11` (`let rest = &mut input[2..]; rest[0] = 1; rest.len() - 4`): the element
///    store before the subtraction drops the fact at that row's use point (the twin's
///    kill keeps it); with no store (`b11b`) both rows are proved;
///  * `b18` (`while s.len() >= 6 { s = &s[2..]; .. s.len() - 4 }`): the row's own
///    in-block kill of the re-sliced `s` drops the tie between the loop guard's length
///    and the receiver's (the twin keeps it existentially); the guard's own length read
///    in the body (`b21`) is proved on both rows.
const SAFE_TWIN_ONLY: &[(&str, u32)] = &[("b11_index_mut_ok", 226), ("b18_loop_cut_ok", 297)];

/// UNSAFE: each subtraction underflows on some input; both rows must stay FAILED.
const UNSAFE: &[(&str, u32)] = &[
    ("a14_subslice", 25),
    ("b1x_from_offby1", 43),
    ("b1y_from_noguard", 49),
    ("b1z_from_wrong_offset", 58),
    ("b2x_range_wrong", 76),
    ("b3x_range_sym_offby1", 94),
    ("b4x_to_wrong", 112),
    ("b5x_split_at_wrong", 130),
    ("b6x_nested_wrong", 150),
    ("b7x_chunks_wrong", 166),
    ("b9_other_parent", 189),
    ("b10x_from_sym_offby1", 207),
    ("b11x_index_mut_wrong", 236),
    ("b12x_reslice_twice_wrong", 257),
    ("b14x_array_wrong", 269),
    ("b17_loop_cut_wrong", 288),
    ("b19_nested_deep_wrong", 309),
    ("b20x_range_two_sym_offby1", 327),
    // The `OpaqueScalar` gate's probes (2026-10-15; `g1_opaque_start_ok`, their correct
    // twin, is the gate's unit test in `generate/range_index_len.rs`): an associated-constant
    // start one wide, a guard on ANOTHER associated constant, and a runtime start
    // (`ptr as usize`) re-read in a loop against the previous iteration's cut. Each stays
    // FAILED with the gate switched off too (DECISION_QUEUE RANGE-INDEX-RESULT-LEN-1).
    ("g1x_opaque_start_offby1", 375),
    ("g1y_opaque_other_const", 384),
    ("g3x_opaque_site_loop_wrong", 403),
];

#[test]
fn a_sub_slice_length_under_its_parents_guard_is_proved() {
    let mut bad = Vec::new();
    for &(name, line) in SAFE {
        for row in sub_pair(name, &rows_of(load(name)), line) {
            if row.verdict != Verdict::Proved {
                bad.push(format!(
                    "{name}:{line} {} -> {:?}: {}",
                    row.kind, row.verdict, row.result
                ));
            }
        }
    }
    assert!(bad.is_empty(), "SAFE rows not proved:\n{}", bad.join("\n"));
}

#[test]
fn the_twin_of_a_sub_slice_length_is_proved_where_its_primary_is_not_yet() {
    let mut bad = Vec::new();
    for &(name, line) in SAFE_TWIN_ONLY {
        let [_, twin] = sub_pair(name, &rows_of(load(name)), line);
        if twin.verdict != Verdict::Proved {
            bad.push(format!("{name}:{line} {} -> {:?}: {}", twin.kind, twin.verdict, twin.result));
        }
    }
    assert!(bad.is_empty(), "SAFE twins not proved:\n{}", bad.join("\n"));
}

#[test]
fn a_real_underflow_of_a_sub_slice_length_stays_refuted() {
    let mut bad = Vec::new();
    for &(name, line) in UNSAFE {
        for row in sub_pair(name, &rows_of(load(name)), line) {
            if row.verdict != Verdict::Failed {
                bad.push(format!(
                    "{name}:{line} {} -> {:?}: {}",
                    row.kind, row.verdict, row.result
                ));
            }
        }
    }
    assert!(bad.is_empty(), "UNSAFE rows not refuted:\n{}", bad.join("\n"));
}

/// `a15_subslice_ok` with its one range-index call rewritten by `edit`: the SAFE row
/// must then NOT be proved (no fact was minted, and nothing else bounds the length).
fn a15_with_index_call(
    edit: impl Fn(&mut String, &mut Option<trust_types::CalleeKey>),
) -> [Row; 2] {
    let mut func = load("a15_subslice_ok");
    let mut edited = 0;
    for block in &mut func.body.blocks {
        if let Terminator::Call { func: callee, callee_key, .. } = &mut block.terminator
            && callee.contains("Index<core::ops::range::RangeFrom")
        {
            edit(callee, callee_key);
            edited += 1;
        }
    }
    assert_eq!(edited, 1, "a15 has exactly one range-index call");
    sub_pair("a15_subslice_ok(edited)", &rows_of(func), 14)
}

/// The inlined spelling of the same index, `<RangeFrom<usize> as SliceIndex<[u8]>>::index(range,
/// slice)` (range first), as the MIR inliner leaves it: the fact is minted for it too.
#[test]
fn the_slice_index_spelling_carries_the_length_too() {
    let mut func = load("a15_subslice_ok");
    let mut edited = 0;
    for block in &mut func.body.blocks {
        if let Terminator::Call { func: callee, args, .. } = &mut block.terminator
            && callee.contains("Index<core::ops::range::RangeFrom")
        {
            *callee =
                "<core::ops::range::RangeFrom<usize> as core::slice::index::SliceIndex<[u8]>>::index"
                    .into();
            args.swap(0, 1);
            edited += 1;
        }
    }
    assert_eq!(edited, 1, "a15 has exactly one range-index call");
    for row in sub_pair("a15_subslice_ok(SliceIndex)", &rows_of(func), 14) {
        assert_eq!(row.verdict, Verdict::Proved, "the SliceIndex spelling: {row:#?}");
    }
}

#[test]
fn a_user_trait_method_named_index_mints_no_length() {
    for row in a15_with_index_call(|callee, _| {
        *callee = "<[u8] as repro::MyIndex<core::ops::range::RangeFrom<usize>>>::index".into();
    }) {
        assert_ne!(row.verdict, Verdict::Proved, "a user `index` is not core's: {row:#?}");
    }
}

#[test]
fn an_index_callee_not_from_the_real_sysroot_mints_no_length() {
    for row in a15_with_index_call(|_, key| {
        let key = key.as_mut().expect("the fixture carries a callee_key");
        key.krate_is_real_sysroot = false;
    }) {
        assert_ne!(row.verdict, Verdict::Proved, "an unauthenticated callee: {row:#?}");
    }
}

#[test]
fn an_index_of_a_non_builtin_self_type_mints_no_length() {
    for row in a15_with_index_call(|callee, _| {
        *callee =
            "<repro::Wrapper as core::ops::index::Index<core::ops::range::RangeFrom<usize>>>::index"
                .into();
    }) {
        assert_ne!(row.verdict, Verdict::Proved, "a user `Index` impl: {row:#?}");
    }
}

/// The terminator-kill gate: a call whose destination is its own receiver
/// (`s = <[u8] as Index<RangeFrom<usize>>>::index(copy s, 2..)`, the in-place re-slice
/// with the copy temp folded away) must mint nothing. The bare definition would read
/// `s.len() == s.len() - 2` on the return edge, an unsatisfiable hypothesis that proves
/// every row after it. `b12x` (two cuts under a one-cut guard, a real underflow) is
/// rewritten into that shape and must stay refuted.
#[test]
fn a_call_whose_destination_is_its_own_receiver_mints_no_length() {
    let mut func = load("b12x_reslice_twice_wrong");
    let s_local = func
        .body
        .locals
        .iter()
        .find(|l| l.name.as_deref() == Some("s"))
        .map(|l| l.index)
        .expect("the fixture names `s`");
    let mut temps = Vec::new();
    for block in &mut func.body.blocks {
        if let Terminator::Call { func: callee, args, dest, .. } = &mut block.terminator
            && callee.contains("Index<core::ops::range::RangeFrom")
        {
            temps.push(dest.local);
            args[0] = trust_types::Operand::Copy(trust_types::Place::local(s_local));
            *dest = trust_types::Place::local(s_local);
        }
    }
    assert_eq!(temps.len(), 2, "b12x has two range-index calls");
    // Drop the `s = copy <call temp>` statements the original MIR re-seated `s` with.
    for block in &mut func.body.blocks {
        for stmt in &mut block.stmts {
            if let trust_types::Statement::Assign {
                place,
                rvalue: trust_types::Rvalue::Use(trust_types::Operand::Copy(src)),
                ..
            } = stmt
                && place.local == s_local
                && place.projections.is_empty()
                && temps.contains(&src.local)
            {
                *stmt = trust_types::Statement::Nop;
            }
        }
    }
    for row in sub_pair("b12x(dest = receiver)", &rows_of(func), 257) {
        assert_eq!(row.verdict, Verdict::Failed, "a real underflow must stay refuted: {row:#?}");
    }
}
