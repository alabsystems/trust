// Real-MIR cover for PATH-GUARD-VALUE-1: a FALSE PROOF, kernel-certified, in the
// ordinary path-guard splice, and the precision its fix keeps.
//
//   pub fn gs_one_arm_scalar_bug(xs: &[bool], buf: &[u8; 8], m: usize, n: usize) -> u8 {
//       let mut len = m;
//       let mut acc = 0;
//       for &c in xs {
//           match len { 3 => {} _ => return acc }
//           if c { len = n; }
//           acc ^= buf[len];          // xs = [true], m = 3, n = 100: index 100, panics
//       }
//       acc
//   }
//
// THE DEFECT. Every path guard was renamed at its SOURCE block's terminal with
// `version_rename_at`, which spells a name by its reaching-definition SET. `len` reaches
// the loop header (the guard) as `{m, len = n}` through the back edge and reaches the
// index as `{m, len = n}` through the join after `if c` — one spelling, two values. So
// `len == 3` pinned the value the index reads, the bounds row was PROVED, `certify_vc`
// certified it, and the compiler's strict build accepted the program (measured on
// origin/main 3164de659d, 2026-10-07, and on 2b946b5458 / 58c7e89a2a before it). The
// same false proof: the write as a call result (`a4`), a multi-arm guard (`st`, `f02`),
// `split_at` (`f08`), and the subject a field behind `&mut` (`field_switch_bug`).
//
// THE FIX (`generate::guard_value_spelling`). A guard read keeps its token only where
// the token names, at the row's block, the SSA value the guard tested
// (`StmtVersionCtx::value_id_at`); elsewhere it gets a guard-local name
// (`crate::GUARD_VALUE_TOKEN_PREFIX`) no body read shares.
//
// THE RANGE TWINS (`g01`..`g03`, `f01`, `f03`..`f05`, `st1`) are the same shapes over a
// slice range. On this tree the range lane says nothing about them (`Bool(true)`, FAILED);
// the range-bound branch that gives that lane a real violation condition splices it
// through the same path guards, so these pin that it cannot inherit the false proof.
//
// Fixtures: `tests/fixtures/path_guard_value/{name}_o{0,1}.json`, extracted by the
// d36c551fa stage2 compiler
//
//   rustc -Ztrust-verify=on -Ztrust-policy=advisory -Ztrust-dump=mir-only:<dir> \
//         --edition 2024 --crate-type lib -Copt-level={0,1} --emit metadata <src>
//
// from `cf.rs`, `st.rs`, `a2.rs` and `pg.rs` beside them (span paths made relative).
// Every `_bug` function panics on the input its source comment names (run at -O0 and
// -O1); every `_ctl` function is correct.
use trust_types::{VcKind, VerifiableFunction, VerificationCondition, VerificationResult};

#[path = "support/test_router.rs"]
mod test_router;

const LEVELS: [&str; 2] = ["o0", "o1"];

fn load(name: &str, level: &str) -> VerifiableFunction {
    let path = format!(
        "{}/tests/fixtures/path_guard_value/{name}_{level}.json",
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

/// One row under test: the function, the row's source position, and its kind.
struct Row {
    name: &'static str,
    line: u32,
    col: u32,
    kind: fn(&VcKind) -> bool,
}

const fn row(name: &'static str, line: u32, col: u32, kind: fn(&VcKind) -> bool) -> Row {
    Row { name, line, col, kind }
}

/// The false proofs this fix closes: PROVED on origin/main 3164de659d (`gs`, `a4` and
/// `field_switch_bug` certified, `st`, `f02`, `f08` uncertified).
const FALSE_PROOFS: &[Row] = &[
    row("gs_one_arm_scalar_bug", 49, 15, index_row),
    row("a4_switch_call_bug", 53, 15, index_row),
    row("field_switch_bug", 13, 15, index_row),
    row("st_switch_scalar_bug", 7, 15, index_row),
    row("f02_switch_scalar_bug", 73, 15, index_row),
    row("f08_switch_split_at_bug", 136, 15, slice_row),
];

/// The range-lane twins and the sibling shapes that were already refuted on main; a
/// change that proves any of them reintroduces the defect.
const STAY_REFUTED: &[Row] = &[
    row("g01_one_arm_bug", 10, 18, slice_row),
    row("g02_iflet_lit_bug", 22, 18, slice_row),
    row("g03_loop_bug", 36, 18, slice_row),
    row("f01_switch_range_to_bug", 61, 18, slice_row),
    row("f03_switch_range_from_bug", 86, 18, slice_row),
    row("f04_switch_range_pair_bug", 98, 18, slice_row),
    row("f05_switch_while_bug", 111, 18, slice_row),
    row("st1_switch_range_bug", 17, 18, slice_row),
    row("a2_copy_def_bug", 14, 15, index_row),
    row("a3_semfact_call_bug", 41, 15, index_row),
    row("bool_guard_bug", 26, 15, index_row),
    row("while_lt_bug", 39, 15, index_row),
];

/// Correct programs whose bounds row main PROVES and certifies, and the fix keeps.
const CONTROLS: &[Row] = &[
    row("gs_read_before_write_ctl", 64, 15, index_row),
    row("a2_copy_def_ctl", 26, 15, index_row),
    row("diamond_nowrite_ctl", 60, 15, index_row),
    row("loop_index_ctl", 71, 26, index_row),
    row("while_lt_read_first_ctl", 83, 15, index_row),
];

/// The deterministic in-process ay router the reproducers were measured with.
fn router() -> trust_router::Router {
    test_router::deterministic_test_router()
}

/// The row of `r` in `func`, generated on a big stack (debug builds of the generator
/// recurse deeply), with its verdict and whether the kernel certifies it.
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

/// THE FALSE PROOFS, closed: each row of a program that panics is neither proved nor
/// kernel-certified, at -O0 and -O1.
#[test]
fn loop_head_guard_no_longer_proves_a_value_written_after_it() {
    for r in FALSE_PROOFS {
        for level in LEVELS {
            let (vc, result, certified) = verdict(r, level);
            assert!(
                !matches!(result, VerificationResult::Proved { .. }),
                "{} {level} {}:{}: a panicking program's row PROVED: {:?}",
                r.name,
                r.line,
                r.col,
                vc.formula
            );
            assert!(!certified, "{} {level}: a panicking program's row was certified", r.name);
        }
    }
}

/// The guard-local spelling is what closes them: every false-proof row's formula names
/// the guarded subject by a guard-value token (the tie to the read is cut, not hidden
/// behind some other change).
#[test]
fn closed_rows_carry_a_guard_local_spelling() {
    for r in FALSE_PROOFS {
        for level in LEVELS {
            let (vc, _, _) = verdict(r, level);
            assert!(
                vc.formula.free_variables().iter().any(|v| {
                    v.split_once('#').is_some_and(|(_, token)| token.starts_with("gv_"))
                }),
                "{} {level}: no guard-local spelling in {:?}",
                r.name,
                vc.formula
            );
        }
    }
}

/// The twins and siblings stay unproved and uncertified.
#[test]
fn range_twins_and_sibling_shapes_stay_unproved() {
    for r in STAY_REFUTED {
        for level in LEVELS {
            let (_, result, certified) = verdict(r, level);
            assert!(
                !matches!(result, VerificationResult::Proved { .. }) && !certified,
                "{} {level} {}:{}: a panicking program's row proved or certified: {result:?}",
                r.name,
                r.line,
                r.col
            );
        }
    }
}

/// THE PRECISION KEPT: a guard that tests the very value the row reads still proves
/// the row, and the kernel still certifies it.
#[test]
fn guards_on_the_rows_own_value_still_prove_and_certify() {
    for r in CONTROLS {
        for level in LEVELS {
            let (vc, result, certified) = verdict(r, level);
            assert!(
                matches!(result, VerificationResult::Proved { .. }),
                "{} {level} {}:{}: a correct program's row lost its proof: {result:?} {:?}",
                r.name,
                r.line,
                r.col,
                vc.formula
            );
            assert!(certified, "{} {level}: the kernel no longer certifies the row", r.name);
        }
    }
}

/// THE KNOWN PROOF LOSS, pinned so it stays visible. `gs_safe_write_ctl` is correct
/// (`if c { len = 2 }` under a `len == 3` loop-head guard: the read sees 2 or 3), and
/// main proved it ONLY through the defective tie — the guard pinned the written value
/// to 3. A guard does not constrain a value written after it, so the row is now
/// unproved; recovering it needs path-sensitive join resolution. When that lands, flip
/// this to the control list.
#[test]
fn a_write_after_the_guard_is_not_constrained_by_it() {
    for level in LEVELS {
        let (_, result, certified) = verdict(&row("gs_safe_write_ctl", 78, 15, index_row), level);
        assert!(
            !matches!(result, VerificationResult::Proved { .. }) && !certified,
            "gs_safe_write_ctl {level}: proved again — move it to CONTROLS: {result:?}"
        );
    }
}
