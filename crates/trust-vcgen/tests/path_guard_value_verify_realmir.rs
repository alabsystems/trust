// Real-MIR cover from the adversarial verification of PATH-GUARD-VALUE-1
// (`generate::guard_value_spelling`, branch `fix/path-guard-value-naming` 0cd1f3ee79).
//
// 1. MORE CLASS-A FALSE PROOFS that the fix closes. Each is PROVED and `certify_vc`
//    certified on origin/main 3164de659d (scalar rows) or on the range-bound merge
//    without the fix (the `r*` range rows), and panics on the input in its source
//    comment (`pv.rs`, `pv2.rs`, `pv3.rs`, run at -O0 and -O1):
//      v01  the write sits in an INNER loop between the outer-head guard and the read;
//      v10  the guard subject is a LOCAL struct field (`s.a`);
//      v16  the guard is `let Some(3) = o`, the read is the payload after a write;
//      v26  the write is in a three-arm `match` (a 3-way join);
//      r01, r26  the `buf[..len]` slice-range twins of v01 and v26.
//
// 2. A KNOWN PRECISION HOLE (false refutations of correct programs; proof loss, never a
//    false proof), recorded as PATH-GUARD-VALUE-1's residual in docs/KNOWN_HAZARDS.md.
//    `guard_var_spelling` keeps a guard read's token only when `value_id_at` names an
//    Entry/Def, or the same Phi the row block's entry reads. `value_id_at` is `None`
//    whenever two or more tracked names rebind the read (a field of a local aggregate
//    that is also written whole; a field behind `&mut` whose base a call havocs), and
//    `None` is spelled guard-local (`x#gv_b{S}`) UNCONDITIONALLY, even when nothing
//    writes the subject between the guard and the row. So a guard and a read of the
//    SAME value lose their tie. c01, c02 and c14 are correct (guard `== 3` / `0..=7`,
//    then the read, then the write); origin/main PROVES and certifies their bounds row
//    at -O0 and -O1; the fix reports FAILED with a counterexample that is not an
//    execution (`st*.0#gv_b5 = 3`, `st*.0#e_s10_0_s2_t = 8`).
//    `projected_guard_read_before_write_still_proves` pinned that loss, `#[ignore]`d.
//    CLOSED 2026-10-17 (gate RCA precision T3): the path-guard spelling asks
//    `StmtVersionCtx::value_id_at_grouped`, which names such a read through its
//    group's own site resolution (`ValueId::GroupOut` at a def site, `Phi` at a join),
//    so the guard keeps its token when nothing writes the subject in between; the
//    test runs, and the class-A false proofs above stay closed.
//
// Fixtures: `tests/fixtures/path_guard_value_verify/{name}_o{0,1}.json`, extracted by
// the d36c551fa stage2 compiler
//
//   rustc -Ztrust-verify=on -Ztrust-policy=advisory -Ztrust-dump=mir-only:<dir> \
//         --edition 2024 --crate-type lib -Copt-level={0,1} --emit metadata <src>
//
// from `pv.rs`, `pv2.rs`, `pv3.rs` beside them (span paths made relative).
use trust_types::{VcKind, VerifiableFunction, VerificationCondition, VerificationResult};

#[path = "support/test_router.rs"]
mod test_router;

const LEVELS: [&str; 2] = ["o0", "o1"];

fn load(name: &str, level: &str) -> VerifiableFunction {
    let path = format!(
        "{}/tests/fixtures/path_guard_value_verify/{name}_{level}.json",
        env!("CARGO_MANIFEST_DIR")
    );
    let json = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    serde_json::from_str(&json)
        .unwrap_or_else(|e| panic!("{path}: fixture MIR must deserialize: {e}"))
}

fn index_row(kind: &VcKind) -> bool {
    matches!(kind, VcKind::IndexOutOfBounds)
}

fn slice_row(kind: &VcKind) -> bool {
    matches!(kind, VcKind::SliceBoundsCheck)
}

struct Row {
    name: &'static str,
    line: u32,
    col: u32,
    kind: fn(&VcKind) -> bool,
}

const fn row(name: &'static str, line: u32, col: u32, kind: fn(&VcKind) -> bool) -> Row {
    Row { name, line, col, kind }
}

/// PROVED and certified on origin/main 3164de659d (v*) or on the range-bound merge
/// without the fix (r*); every one panics.
const CLOSED: &[Row] = &[
    row("v01_nested_inner_write_bug", 41, 15, index_row),
    row("v10_local_field_bug", 194, 15, index_row),
    row("v16_option_payload_bug", 302, 19, index_row),
    row("v26_three_way_join_bug", 164, 15, index_row),
    row("r01_nested_inner_write_bug", 26, 18, slice_row),
    row("r26_three_way_join_bug", 79, 18, slice_row),
];

/// Sibling write channels (a `&mut` call write, a bool/copy guard, a swap): refuted on
/// main and on the fix; every one panics.
const SIBLINGS: &[Row] = &[
    row("v02_call_mut_write_bug", 58, 15, index_row),
    row("v20_bool_guard_call_write_bug", 47, 15, index_row),
    row("v22_copy_guard_call_write_bug", 84, 15, index_row),
    row("v24_swap_bug", 120, 15, index_row),
];

/// Correct programs on a plain local that main and the fix both PROVE and certify.
const KEPT: &[Row] = &[
    row("c04_continue_after_write_ctl", 367, 15, index_row),
    row("c05_nested_no_write_ctl", 386, 15, index_row),
];

/// Correct programs, guard then read BEFORE the write, the subject a projected place:
/// PROVED and certified on origin/main; FAILED on 0cd1f3ee79.
const PROJECTED: &[Row] = &[
    row("c01_field_read_before_write_ctl", 318, 15, index_row),
    row("c02_local_field_read_before_write_ctl", 335, 15, index_row),
    row("c14_tuple_field_ctl", 221, 15, index_row),
];

fn router() -> trust_router::Router {
    test_router::deterministic_test_router()
}

fn verdict(r: &Row, level: &str) -> (VerificationCondition, VerificationResult, bool) {
    let func = load(r.name, level);
    let (line, col, kind) = (r.line, r.col, r.kind);
    let (name, level) = (r.name, level.to_string());
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let vcs: Vec<VerificationCondition> = trust_vcgen::generate_vcs(&func)
                .into_iter()
                .filter(|vc| {
                    kind(&vc.kind) && vc.location.line_start == line && vc.location.col_start == col
                })
                .collect();
            assert_eq!(vcs.len(), 1, "{name} {level}: exactly one row at {line}:{col}");
            let (vc, result) = router().verify_all(&vcs).into_iter().next().expect("one verdict");
            let certified = trust_certify::certify_vc(&vc).is_some();
            (vc, result, certified)
        })
        .expect("spawn")
        .join()
        .expect("generation and verification must not panic")
}

#[test]
fn new_loop_head_false_proofs_stay_closed() {
    for r in CLOSED.iter().chain(SIBLINGS) {
        for level in LEVELS {
            let (vc, result, certified) = verdict(r, level);
            assert!(
                !matches!(result, VerificationResult::Proved { .. }) && !certified,
                "{} {level} {}:{}: a panicking program's row proved or certified: {:?}",
                r.name,
                r.line,
                r.col,
                vc.formula
            );
        }
    }
}

#[test]
fn plain_local_controls_still_prove() {
    for r in KEPT {
        for level in LEVELS {
            let (_, result, certified) = verdict(r, level);
            assert!(
                matches!(result, VerificationResult::Proved { .. }) && certified,
                "{} {level} {}:{}: a correct program lost its proof: {result:?}",
                r.name,
                r.line,
                r.col
            );
        }
    }
}

/// The loss PATH-GUARD-VALUE-1 left (failed on 0cd1f3ee79 and on main after it, ignored
/// until 2026-10-17): a guard on a projected place and a read of the SAME value (no
/// write between) were respelled apart because `value_id_at` is `None` there. Closed by
/// gate RCA precision T3 (`value_id_at_grouped`); every row PROVED and certified again.
#[test]
fn projected_guard_read_before_write_still_proves() {
    let mut lost = Vec::new();
    for r in PROJECTED {
        for level in LEVELS {
            let (vc, result, certified) = verdict(r, level);
            if !(matches!(result, VerificationResult::Proved { .. }) && certified) {
                let gv = vc.formula.free_variables().into_iter().filter(|v| {
                    v.split_once('#').is_some_and(|(_, token)| token.starts_with("gv_"))
                });
                lost.push(format!(
                    "{} {level} {}:{} -> {} (guard-local names: {:?})",
                    r.name,
                    r.line,
                    r.col,
                    if matches!(result, VerificationResult::Failed { .. }) {
                        "FAILED"
                    } else {
                        "not proved"
                    },
                    gv.collect::<Vec<_>>()
                ));
            }
        }
    }
    assert!(lost.is_empty(), "correct programs lost their proof:\n{}", lost.join("\n"));
}
