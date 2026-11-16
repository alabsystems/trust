// Cover for ARM-VALUE-SELF-READ-1: a branch-merge arm value that reads the place
// its own statement writes.
//
// THE DEFECT (`guards::arm_definition_map`). The single-switch merge, its PARTIAL
// merge (MATCH-ARM-CALL-CHAIN) and the nested lane spell each arm's value
// UNVERSIONED and claim it at the join, i.e. they read every free variable of the
// value at the arm's EXIT. Block-definition extraction drops a def whose operand a
// LATER statement rewrites, but not one whose operand its OWN statement rewrites,
// and such an rvalue reads the PRE-statement value:
//
//   * `acc ^= 1` gives the arm value `acc ^ 1` for `acc`, so the join claims
//     `acc == ite(.., acc ^ 1, ..)`: a recurrence, UNSAT on that arm. Every row
//     the join reaches would be vacuously discharged; the last-line
//     `SelfReferentialDefinition` net in `generate::entry` catches the single-
//     equation form and replaces the row with an `UnsupportedMir` refusal. That is
//     how `path_guard_value_identity_realmir`'s `diamond_nowrite_ctl` lost its
//     bounds row on the land/batch-1007 merge: MATCH-ARM-CALL-CHAIN admitted its
//     `wrapping_add` Call-hop arm, so the merge fired on that join for the first
//     time. The same refusal is on origin/main 85c8c21eeb for a plain two-arm
//     diamond (`self_update_ctl` below).
//   * the tuple swap `t = (t.1, t.0)` gives `t.0 == t.1` and `t.1 == t.0` — no
//     single equation is self-referential, so the net does not see it, and the
//     join claims the swapped components equal. On origin/main 85c8c21eeb
//     `tuple_swap_selfread_handbuilt` PROVED its index row although the program
//     reads `buf[100]` at `c = true, y0 = 100`.
//
// THE FIX. `arm_definition_map` drops a def whose value reads a name its own
// statement writes (`stmt_direct_write_names` under `dest_write_rebinds`). The
// subject then has no value on that arm, the total merge declines it, and fewer
// hypotheses can only lose proofs.
//
// Fixtures: `tests/fixtures/arm_value_self_read/`.
//   * `{self_update_ctl,merge_const_ctl}_o{0,1}.json` — REAL MIR, extracted from
//     `avsr.rs` beside them by the installed trustc 1.99.0-dev (321aaeda7):
//
//       trustc -Ztrust-verify=on -Ztrust-policy=advisory -Ztrust-dump=mir-only:<dir> \
//              --edition 2024 --crate-type lib -Copt-level={0,1} --emit metadata avsr.rs
//
//     (span files prefixed with `arm_value_self_read/`).
//   * `tuple_swap_selfread_handbuilt.json` — HAND-BUILT MIR. rustc lowers the
//     source swap (`tuple_swap_bug` in `avsr.rs`) through temporaries, at -O0 and
//     -O1 alike, and that real MIR is refuted on both trees; the hand-built body
//     writes the aggregate straight from the place it overwrites, the shape the
//     merge has to be sound for whatever produces it. Its shape:
//
//       bb0: t = (0, y0); switchInt(c) -> [0: bb2, otherwise: bb1]
//       bb1: t = (copy t.1, copy t.0); goto bb3
//       bb2: t = (0, 0); goto bb3
//       bb3: _5 = Lt(copy t.1, 8); assert(copy _5) -> bb7      (line 6)
//       bb7: assert(copy c) -> bb4                              (line 5)
//       bb4: _6 = copy t.0; _7 = Lt(copy _6, 8); assert(move _7) -> bb5   (7:15)
//       bb5: _0 = copy (*buf)[_6]; return
//
//     It carries the `y0` range precondition the extractor emits; a missing
//     extractor fact can only weaken it, so its false proof was not an artifact.
use trust_types::{VcKind, VerifiableFunction, VerificationCondition, VerificationResult};

#[path = "support/test_router.rs"]
mod test_router;

const LEVELS: [&str; 2] = ["o0", "o1"];

fn load(file: &str) -> VerifiableFunction {
    let path =
        format!("{}/tests/fixtures/arm_value_self_read/{file}.json", env!("CARGO_MANIFEST_DIR"));
    let json = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    serde_json::from_str(&json)
        .unwrap_or_else(|e| panic!("{path}: fixture MIR must deserialize: {e}"))
}

fn router() -> trust_router::Router {
    test_router::deterministic_test_router()
}

/// Every row of `file`, generated on a big stack, with its verdict and whether the
/// kernel certifies it.
fn rows(file: &str) -> Vec<(VerificationCondition, VerificationResult, bool)> {
    let func = load(file);
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let vcs = trust_vcgen::generate_vcs(&func);
            router()
                .verify_all(&vcs)
                .into_iter()
                .map(|(vc, result)| {
                    let certified = trust_certify::certify_vc(&vc).is_some();
                    (vc, result, certified)
                })
                .collect()
        })
        .expect("spawn")
        .join()
        .expect("generation and verification must not panic")
}

fn is_self_referential_refusal(kind: &VcKind) -> bool {
    matches!(kind, VcKind::UnsupportedMir { kind, .. } if kind == "SelfReferentialDefinition")
}

fn index_rows_at(
    rows: &[(VerificationCondition, VerificationResult, bool)],
    line: u32,
    col: u32,
) -> Vec<&(VerificationCondition, VerificationResult, bool)> {
    rows.iter()
        .filter(|(vc, _, _)| {
            matches!(vc.kind, VcKind::IndexOutOfBounds)
                && vc.location.line_start == line
                && vc.location.col_start == col
        })
        .collect()
}

/// THE FALSE PROOF, closed: the hand-built swap's index row is neither proved nor
/// certified; it is refuted.
#[test]
fn a_swap_arm_does_not_equate_the_components_it_swaps() {
    let rows = rows("tuple_swap_selfread_handbuilt");
    let index = index_rows_at(&rows, 7, 15);
    assert_eq!(index.len(), 1, "exactly one index row at 7:15");
    let (vc, result, certified) = index[0];
    assert!(
        !matches!(result, VerificationResult::Proved { .. }) && !certified,
        "a panicking program's index row proved or certified: {result:?} {:?}",
        vc.formula
    );
    assert!(
        matches!(result, VerificationResult::Failed { .. }),
        "the index row is refuted (c = true, y0 >= 8): {result:?}"
    );
}

/// The recurrence is no longer minted: the plain self-updating diamond yields its
/// ordinary bounds row instead of a `SelfReferentialDefinition` refusal, at -O0 and
/// -O1. (On origin/main 85c8c21eeb the only row at 21:10 was that refusal.)
#[test]
fn a_self_update_arm_mints_no_recurrence() {
    for level in LEVELS {
        let rows = rows(&format!("self_update_ctl_{level}"));
        assert!(
            !rows.iter().any(|(vc, _, _)| is_self_referential_refusal(&vc.kind)),
            "self_update_ctl {level}: a SelfReferentialDefinition refusal is back"
        );
        assert_eq!(
            index_rows_at(&rows, 21, 10).len(),
            1,
            "self_update_ctl {level}: exactly one ordinary bounds row at 21:10"
        );
    }
}

/// THE PRECISION KEPT: a merge whose arm values read nothing their own statement
/// writes still proves the row the join feeds.
#[test]
fn a_constant_arm_merge_still_proves() {
    for level in LEVELS {
        let rows = rows(&format!("merge_const_ctl_{level}"));
        let index = index_rows_at(&rows, 31, 4);
        assert!(!index.is_empty(), "merge_const_ctl {level}: no bounds row at 31:4");
        for (vc, result, _) in &index {
            assert!(
                matches!(result, VerificationResult::Proved { .. }),
                "merge_const_ctl {level}: the merged row lost its proof: {result:?} {:?}",
                vc.formula
            );
        }
    }
}
