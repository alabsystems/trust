//! REAL-MIR pins for CHECKED-OP-TRAILING-COPY-1: a checked op's assert-passed
//! facts survive a statement rustc places between the op and its `Assert` when
//! that statement changes nothing the facts are stated over.
//!
//! # The defect (measured on Trust `main` a7ebff4816 and stage 1 `35a39d5c74`)
//!
//! trust-ir-conformance `CharCarriers::of` numbers its tables with
//! `let mut number = |rows| rows.keys().map(|&id| { count += 1; (id, count - 1) })`
//! (`subset.rs:573-578` at trust-ir `8cdf2b6917ec`). The closure reaches `count`
//! through its captured `&mut usize`, and rustc copies that pointer out of the
//! closure environment into a FRESH temporary for every use:
//!
//! ```text
//! bb0: _5 = copy ((*_1).0); _2 = CheckedAdd(copy (*_5), 1); _6 = copy ((*_1).0);
//!      assert(!move (_2.1), Overflow(Add)) -> bb1
//! bb1: _7 = copy ((*_1).0); (*_7) = move (_2.0); _8 = copy ((*_1).0); _3 = copy (*_8);
//!      _4 = CheckedSub(copy _3, 1); assert(!move (_4.1), Overflow(Sub)) -> bb2
//! ```
//!
//! `exact_asserted_checked_binary_op` admitted only INERT statements after the op,
//! so `_6 = copy ((*_1).0)` withheld every assert-passed fact of bb0 (`_2.0 ==
//! _1*.0* + 1` and the operand range), the value bb1 stores and rereads floated
//! free, and the `[overflow:sub]` row AND its hardened twin were refuted at
//! `_2.0 = 0`. KILLED-ENTRY-EXISTS-1 (`deref_store_reload_realmir.rs`) renames a
//! killed entry fact; its fixture passes `count: &mut usize` as a PARAMETER, so
//! bb0 has no trailing copy, and here there was no fact to rename. That is why it
//! moved none of the CharCarriers rows in preview4's control run.
//!
//! The `count += 1` row itself stays refuted, correctly: the closure body is
//! verified on its own, and the captured counter may be `usize::MAX` there.
//!
//! # Fixtures
//!
//! `tests/fixtures/closure_capture_reload_*_mir.json` are the compiler's own
//! extraction of the closure bodies in [`tests/data/closure_capture_reload.rs`],
//! captured with
//!
//! ```text
//! trustc --edition 2021 --crate-type lib -Ztrust-verify=on \
//!        -Ztrust-verify-profile=unix_hardened -Ztrust-verify-level=2 \
//!        -Ztrust-policy=advisory -Ztrust-verify-output=json \
//!        -Ztrust-dump=mir:<dir> closure_capture_reload.rs
//! ```
//!
//! on Trust stage 1 `35a39d5c74` (preview4, 2026-10-12); only the `span.file`
//! fields were rewritten to the crate-relative source path. That compiler
//! reported all four rows of every closure `failed`.
//!
//! `closure_capture_reload_char_carriers_of_mir.json` is the measured site itself:
//! `trust_ir_conformance::subset::CharCarriers::of::{closure#3}::{closure#0}`,
//! dumped unedited (`-Ztrust-dump=mir-only:<dir>`, the same verify flags) by the
//! same stage 1 from trust-ir `8cdf2b6917ec`, the preview4 control source. Its
//! `span.file` is the trust-ir repo's own relative path.
//!
//! # Mutation ledger (2026-10-12)
//!
//! ```text
//! mutant                                                tests that go red
//! trailing rule reverted (inert statements only)        the_char_carriers_reload_proves, the_measured_char_carriers_site_proves
//! trailing rule admits EVERY whole-local assign         a_trailing_write_of_the_operand_still_refutes
//!   (no operand-mention / borrow / write-oracle check)
//! ```
use std::collections::HashSet;

use trust_types::{
    BlockId, Counterexample, CounterexampleValue, Rvalue, Statement, VerifiableFunction,
    VerificationResult,
};

#[path = "support/test_router.rs"]
mod test_router;

/// Real extracted MIR carries deep recursive `Formula` walks.
const SOLVER_STACK_BYTES: usize = 256 * 1024 * 1024;

const PRIMARY_ADD: &str = "ArithmeticOverflow { op: Add";
const PRIMARY_SUB: &str = "ArithmeticOverflow { op: Sub";
const TWIN_ADD: &str = "mir_assert::Overflow(Add)";
const TWIN_SUB: &str = "mir_assert::Overflow(Sub)";

fn load(name: &str) -> VerifiableFunction {
    let path = format!(
        "{}/tests/fixtures/closure_capture_reload_{name}_mir.json",
        env!("CARGO_MANIFEST_DIR")
    );
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("fixture `{name}` must be readable: {e}"));
    serde_json::from_str(&text).unwrap_or_else(|e| panic!("fixture `{name}` must deserialize: {e}"))
}

#[derive(Debug, Clone)]
struct Row {
    kind: String,
    line: u32,
    formula: String,
    result: VerificationResult,
}

/// Every row of `func`, hardened profile ON, through the entry the compiler
/// calls, decided by the deterministic in-process `ay` router.
fn rows_of(func: VerifiableFunction) -> Vec<Row> {
    std::thread::Builder::new()
        .stack_size(SOLVER_STACK_BYTES)
        .spawn(move || {
            let context = trust_vcgen::VcgenContext::for_function(func.def_path.clone());
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
                .map(|(vc, result)| Row {
                    kind: format!("{:?}", vc.kind),
                    line: vc.location.line_start,
                    formula: format!("{:?}", vc.formula),
                    result,
                })
                .collect()
        })
        .expect("spawn")
        .join()
        .expect("generation thread")
}

fn rows(name: &str) -> Vec<Row> {
    rows_of(load(name))
}

/// The single row at `line` whose kind contains `needle`.
fn one<'a>(rows: &'a [Row], line: u32, needle: &str) -> &'a Row {
    let hits: Vec<&Row> =
        rows.iter().filter(|r| r.line == line && r.kind.contains(needle)).collect();
    assert_eq!(hits.len(), 1, "line {line}: expected one `{needle}` row; all rows: {rows:#?}");
    hits[0]
}

fn int_named(cex: &Counterexample, name: &str) -> Option<i128> {
    cex.assignments.iter().find_map(|(n, value)| match value {
        CounterexampleValue::Int(v) if n == name => Some(*v),
        CounterexampleValue::Uint(v) if n == name => i128::try_from(*v).ok(),
        _ => None,
    })
}

/// `row` is refuted, and `real` accepts its model as an execution that overflows.
fn assert_refuted(row: &Row, real: impl Fn(&Counterexample) -> bool, why: &str) {
    match &row.result {
        VerificationResult::Failed { counterexample, .. } => {
            let cex = counterexample.as_ref().expect("a refutation must carry its model");
            assert!(
                real(cex),
                "{why}: the model must be a real overflow; got {cex:?}\nrow: {row:#?}"
            );
        }
        other => panic!("{why}: must stay REFUTED; got {other:?}\nrow: {row:#?}"),
    }
}

/// The model names the Sub's minuend local `reload` below `bound`.
fn reload_below(reload: &'static str, bound: i128) -> impl Fn(&Counterexample) -> bool {
    move |cex| int_named(cex, reload).is_some_and(|v| v < bound)
}

/// The model puts the captured counter at `usize::MAX`: `count += 1` really overflows.
fn counter_at_max(cex: &Counterexample) -> bool {
    int_named(cex, "_1*.0*") == Some(i128::from(u64::MAX))
}

/// VACUITY GUARD: the fixture has the shape the rule is about. bb0's
/// `CheckedAdd` is followed, before the `Assert`, by a whole-local copy of the
/// captured pointer. Without it these tests would pin nothing.
fn assert_trailing_pointer_copy(func: &VerifiableFunction) {
    let bb0 = &func.body.blocks[0];
    let k = bb0
        .stmts
        .iter()
        .position(|s| matches!(s, Statement::Assign { rvalue: Rvalue::CheckedBinaryOp(..), .. }))
        .expect("bb0 holds the counter's CheckedAdd");
    assert!(
        bb0.stmts[k + 1..].iter().any(|s| matches!(s,
            Statement::Assign { place, rvalue: Rvalue::Use(_), .. } if place.projections.is_empty())),
        "{}: bb0 must copy the captured pointer AFTER the CheckedAdd: {bb0:#?}",
        func.def_path
    );
}

#[test]
fn the_char_carriers_reload_proves() {
    for (name, add_line, sub_line) in [("bump_reload", 15, 16), ("number_rows", 28, 29)] {
        assert_trailing_pointer_copy(&load(name));
        let rows = rows(name);
        for needle in [PRIMARY_SUB, TWIN_SUB] {
            let row = one(&rows, sub_line, needle);
            assert!(
                matches!(row.result, VerificationResult::Proved { .. }),
                "{name}: `count += 1; count - 1` rereads `old + 1 >= 1`; `{needle}` must \
                 prove: {row:#?}"
            );
        }
        // The fact that does the work is bb0's assert-passed definition of the
        // value bb1 stores, over the captured counter's pre-store value.
        let twin = one(&rows, sub_line, TWIN_SUB);
        assert!(
            twin.formula.contains("Var(\"_2.0#s0_1\"")
                || twin.formula.contains("Var(\"_4.0#s0_2\""),
            "{name}: the twin must carry bb0's stored-value definition: {}",
            twin.formula
        );
        // The bump itself is a real overflow in the closure verified alone.
        for needle in [PRIMARY_ADD, TWIN_ADD] {
            assert_refuted(
                one(&rows, add_line, needle),
                counter_at_max,
                "the captured counter may be usize::MAX",
            );
        }
    }
}

/// The measured row: preview4's control run reported `subset.rs:578`
/// `[overflow:sub]` and its hardened twin `failed` here.
#[test]
fn the_measured_char_carriers_site_proves() {
    let func = load("char_carriers_of");
    assert_eq!(
        func.def_path,
        "trust_ir_conformance::subset::CharCarriers::of::{closure#3}::{closure#0}"
    );
    assert_trailing_pointer_copy(&func);
    let rows = rows_of(func);
    for needle in [PRIMARY_SUB, TWIN_SUB] {
        let row = one(&rows, 578, needle);
        assert!(
            matches!(row.result, VerificationResult::Proved { .. }),
            "`(id, count - 1)` after `count += 1`: `{needle}` must prove: {row:#?}"
        );
    }
    for needle in [PRIMARY_ADD, TWIN_ADD] {
        assert_refuted(
            one(&rows, 577, needle),
            counter_at_max,
            "the captured counter may be usize::MAX",
        );
    }
}

#[test]
fn bump_reload_sub_two_still_refutes() {
    let rows = rows("bump_reload_sub_two");
    for needle in [PRIMARY_SUB, TWIN_SUB] {
        assert_refuted(one(&rows, 41, needle), reload_below("_3", 2), "`old + 1 - 2` at old = 0");
    }
}

#[test]
fn bump_overwrite_reload_still_refutes() {
    let rows = rows("bump_overwrite_reload");
    for needle in [PRIMARY_SUB, TWIN_SUB] {
        assert_refuted(
            one(&rows, 53, needle),
            reload_below("_4", 1),
            "the reload reads the second store `v`, which may be 0",
        );
    }
}

#[test]
fn bump_other_reload_still_refutes() {
    let rows = rows("bump_other_reload");
    for needle in [PRIMARY_SUB, TWIN_SUB] {
        assert_refuted(
            one(&rows, 65, needle),
            reload_below("_3", 1),
            "the reload reads the OTHER captured counter, which may be 0",
        );
    }
}

/// A synthetic counter-program for the rule's own boundary: a trailing statement
/// that DOES rewrite the op's operand. `x - 1` passes (so `x >= 1` at the op), then
/// `x = 0` before the `Assert`, then `x - 1` again, which underflows on every
/// execution. The first op's facts (`0 <= x - 1`) are about the PRE-write `x`; if
/// they reached bb1 they would contradict `x == 0` and vacuously prove the second
/// Sub. Both rows of the second Sub must stay refuted.
#[test]
fn a_trailing_write_of_the_operand_still_refutes() {
    let u64_ty = serde_json::json!({"Int": {"width": 64, "signed": false}});
    let span = |line: u32| {
        serde_json::json!({"file": "tests/data/closure_capture_reload.rs",
            "line_start": line, "col_start": 1, "line_end": line, "col_end": 2})
    };
    let place = |local: usize, proj: serde_json::Value| serde_json::json!({"local": local, "projections": proj});
    let checked_sub = |dest: usize, line: u32| {
        serde_json::json!({"Assign": {"place": place(dest, serde_json::json!([])),
            "rvalue": {"CheckedBinaryOp": ["Sub", {"Copy": place(1, serde_json::json!([]))},
                {"Constant": {"Uint": [1, 64]}}]},
            "span": span(line)}})
    };
    let assert_to = |tuple: usize, target: usize, line: u32| {
        serde_json::json!({"Assert": {"cond": {"Move": place(tuple, serde_json::json!([{"Field": 1}]))},
            "expected": false, "msg": {"Overflow": "Sub"}, "target": target,
            "span": span(line), "unwind": "Continue"}})
    };
    let func = serde_json::json!({
        "name": "trailing_operand_write",
        "def_path": "closure_capture_reload::trailing_operand_write",
        "span": span(900),
        "body": {
            "locals": [
                {"index": 0, "ty": u64_ty, "name": null},
                {"index": 1, "ty": u64_ty, "name": null},
                {"index": 2, "ty": {"Tuple": [u64_ty, "Bool"]}, "name": null},
                {"index": 3, "ty": {"Tuple": [u64_ty, "Bool"]}, "name": null}
            ],
            "blocks": [
                {"id": 0, "stmts": [
                    checked_sub(2, 901),
                    {"Assign": {"place": place(1, serde_json::json!([])),
                        "rvalue": {"Use": {"Constant": {"Uint": [0, 64]}}}, "span": span(902)}}
                 ], "terminator": assert_to(2, 1, 901)},
                {"id": 1, "stmts": [checked_sub(3, 903)], "terminator": assert_to(3, 2, 903)},
                {"id": 2, "stmts": [
                    {"Assign": {"place": place(0, serde_json::json!([])),
                        "rvalue": {"Use": {"Move": place(3, serde_json::json!([{"Field": 0}]))}},
                        "span": span(904)}}
                 ], "terminator": "Return"}
            ],
            "arg_count": 1,
            "return_ty": u64_ty
        },
        "contracts": [], "preconditions": [], "postconditions": [],
        "spec": {"requires": [], "ensures": [], "invariants": []}
    });
    let func: VerifiableFunction =
        serde_json::from_value(func).expect("the synthetic body must deserialize");
    let rows = rows_of(func);
    for needle in [PRIMARY_SUB, TWIN_SUB] {
        let row = one(&rows, 903, needle);
        assert!(
            matches!(row.result, VerificationResult::Failed { .. }),
            "`x = 0; x - 1` underflows on every execution; `{needle}` must stay refuted: {row:#?}"
        );
    }
}

/// REVIEW PROBE (adversarial): the trailing statement writes a local the operand
/// reads THROUGH A POINTER, not by name. `p = &raw const y; y - 1` passes, then
/// `y = 0` before the `Assert`, then `*p - 1` again, which underflows on every
/// execution. The operand's place is `*_4`, so the name check alone does not see
/// `_5`; the alias check (and the write oracle over the operand's canonical name)
/// must keep the first op's facts out. Both rows of the second Sub stay refuted.
#[test]
fn a_trailing_write_through_an_alias_still_refutes() {
    let u64_ty = serde_json::json!({"Int": {"width": 64, "signed": false}});
    let ptr_ty = serde_json::json!({"RawPtr": {"mutable": false, "pointee": u64_ty}});
    let span = |line: u32| {
        serde_json::json!({"file": "tests/data/closure_capture_reload.rs",
            "line_start": line, "col_start": 1, "line_end": line, "col_end": 2})
    };
    let place = |local: usize, proj: serde_json::Value| serde_json::json!({"local": local, "projections": proj});
    let checked_sub = |dest: usize, line: u32| {
        serde_json::json!({"Assign": {"place": place(dest, serde_json::json!([])),
            "rvalue": {"CheckedBinaryOp": ["Sub", {"Copy": place(4, serde_json::json!(["Deref"]))},
                {"Constant": {"Uint": [1, 64]}}]},
            "span": span(line)}})
    };
    let assert_to = |tuple: usize, target: usize, line: u32| {
        serde_json::json!({"Assert": {"cond": {"Move": place(tuple, serde_json::json!([{"Field": 1}]))},
            "expected": false, "msg": {"Overflow": "Sub"}, "target": target,
            "span": span(line), "unwind": "Continue"}})
    };
    let func = serde_json::json!({
        "name": "trailing_alias_write",
        "def_path": "closure_capture_reload::trailing_alias_write",
        "span": span(910),
        "body": {
            "locals": [
                {"index": 0, "ty": u64_ty, "name": null},
                {"index": 1, "ty": u64_ty, "name": null},
                {"index": 2, "ty": {"Tuple": [u64_ty, "Bool"]}, "name": null},
                {"index": 3, "ty": {"Tuple": [u64_ty, "Bool"]}, "name": null},
                {"index": 4, "ty": ptr_ty, "name": null},
                {"index": 5, "ty": u64_ty, "name": null}
            ],
            "blocks": [
                {"id": 0, "stmts": [
                    {"Assign": {"place": place(5, serde_json::json!([])),
                        "rvalue": {"Use": {"Copy": place(1, serde_json::json!([]))}}, "span": span(911)}},
                    {"Assign": {"place": place(4, serde_json::json!([])),
                        "rvalue": {"AddressOf": [false, place(5, serde_json::json!([]))]}, "span": span(911)}},
                    checked_sub(2, 912),
                    {"Assign": {"place": place(5, serde_json::json!([])),
                        "rvalue": {"Use": {"Constant": {"Uint": [0, 64]}}}, "span": span(913)}}
                 ], "terminator": assert_to(2, 1, 912)},
                {"id": 1, "stmts": [checked_sub(3, 914)], "terminator": assert_to(3, 2, 914)},
                {"id": 2, "stmts": [
                    {"Assign": {"place": place(0, serde_json::json!([])),
                        "rvalue": {"Use": {"Move": place(3, serde_json::json!([{"Field": 0}]))}},
                        "span": span(915)}}
                 ], "terminator": "Return"}
            ],
            "arg_count": 1,
            "return_ty": u64_ty
        },
        "contracts": [], "preconditions": [], "postconditions": [],
        "spec": {"requires": [], "ensures": [], "invariants": []}
    });
    let func: VerifiableFunction =
        serde_json::from_value(func).expect("the synthetic body must deserialize");
    let rows = rows_of(func);
    for needle in [PRIMARY_SUB, TWIN_SUB] {
        let row = one(&rows, 914, needle);
        assert!(
            matches!(row.result, VerificationResult::Failed { .. }),
            "`y = 0; *p - 1` underflows on every execution; `{needle}` must stay refuted: {row:#?}"
        );
    }
}
