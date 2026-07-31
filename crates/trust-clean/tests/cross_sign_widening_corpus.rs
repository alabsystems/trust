// End-to-end production-gate pin for GAP-CROSS-SIGN-WIDEN.
//
// Diagnose every cast 0.3.0 corpus body in the same callees-first order and
// with the same sibling-body registry as production, then compare every field
// recorded by the checked pre-change census. Exactly fourteen
// unsigned-to-signed strict widenings may move, plus the two independently
// certified fieldless-`Error` methods added after that census, plus the three
// rows HEAD deliberately closed; every other recorded row must be
// byte-semantically stable. Each allowed target pins its full diagnosis,
// keeping the feature deltas explicit and disjoint.
//
// ===========================================================================
// Trust: RE-KEYED AND RE-DERIVED after the 2026-07-29 ladder fixture re-freeze
// (`reports/2026-07-29-ladder-fixture-refreeze.md`). Read this before touching
// a number below.
//
// TWO things moved, and they are different things:
//
// (1) SPELLING. The re-freeze re-dumped `census-rung2-2026-07-07/cast` from the
//     SAME unmodified cast 0.3.0 sources at the current stage2. The producer now
//     crate-root-qualifies `def_path` — a crate compiled straight from `lib.rs`
//     is named `lib` — so `_64::<impl From<i16> for i8>::cast` is now spelled
//     `lib::_64::<impl lib::From<i16> for i8>::cast`. The corpus is otherwise
//     IDENTICAL: 202 functions before, 202 after, none added, none dropped.
//     `strip_crate_root` below undoes exactly that qualification and is asserted
//     to be a BIJECTION onto the baseline's 202 keys, so the historical
//     `crate-ladder-recensus-2026-07-11` TSV stays usable and untouched (it is a
//     record of its own date and must not be rewritten).
//
// (2) COUNT: the current FF total moved 148 -> 145, and the reason is NOT this
//     test's feature. It is SCHEMA, not capability, on the gain side and
//     DELIBERATE CLOSURE on the loss side:
//
//       * gains: the pre-re-freeze committed dumps predated first-class enum
//         variant metadata, so their `Result` `Ty::Adt` decoded as
//         `variants: []`. Since `938f11049ad` (2026-07-17)
//         `aggregate_variant_discriminant` is first-class-metadata-only
//         (`mirsem/adt_shapes.rs:131`) — it will not guess a declaration-order
//         index for a missing array — so the whole fallible-`Result` narrowing
//         family declined. The re-freeze restores the array and the family
//         certifies again. This is the +85 the re-freeze report's §2 measures on
//         THIS directory (cast 60 -> 145 FF, ff-gate-diagnose-2026-07-10,
//         no budget). It is repaid staleness, not new prover power: §4 of that
//         report grafts the `variants` array onto the OLD committed bytes and
//         they certify, and deletes it from the FRESH bytes and they decline.
//
//       * losses: measured against THIS test's 2026-07-11 baseline the net is
//         +13, not +85, because the baseline is a different (earlier, healthy)
//         scoring — 132 FF. 132 + 16 gained - 3 lost = 145. The 3 lost are
//         `_64::<impl From<f32> for f32>::cast`,
//         `_64::<impl From<f64> for f64>::cast` and
//         `_x128::<impl From<u128> for i128>::cast`: HEAD closed them on
//         purpose (`prove.rs`'s non-`Int` return-type blanket, and the >64-bit
//         witness scope that had been a genuine FALSE ACCEPT — see the
//         re-freeze report §6, "the rows that must NOT come back"). They are
//         pinned as REQUIRED regressions here so re-blessing one is a test
//         failure, not a quiet green.
//
// The 16 gained rows are still EXACTLY the fourteen widenings plus the two
// fieldless-`Error` methods this test was written to pin — measured, not
// assumed. That is why this file keeps its name and its purpose.
// ===========================================================================

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::path::{Path, PathBuf};

use trust_clean::FullyFaithfulDiagnosis;
use trust_clean::mirsem::CalleeFact;
use trust_clean::prove::diagnose_fully_faithful_gate_with_bodies;
use trust_clean::trustir_fold::DumpBodies;
use trust_types::VerifiableFunction;

#[derive(Debug, Clone, PartialEq, Eq)]
struct GateRow {
    cluster: String,
    via_ir_shape: bool,
    via_ir_safety: bool,
    via_mirsem_shape: bool,
    via_mirsem_sl_safety_discharged: bool,
    via_mirsem_call_requires: bool,
    via_mirsem_loop_full: bool,
    fully_faithful: bool,
}

impl GateRow {
    fn from_diagnosis(diag: &FullyFaithfulDiagnosis) -> Self {
        Self {
            cluster: diag.cluster_tag().to_string(),
            via_ir_shape: diag.via_ir_shape,
            via_ir_safety: diag.via_ir_safety,
            via_mirsem_shape: diag.via_mirsem_shape,
            via_mirsem_sl_safety_discharged: diag.via_mirsem_straight_line_safety_discharged,
            via_mirsem_call_requires: diag.via_mirsem_call_requires,
            via_mirsem_loop_full: diag.via_mirsem_loop_full,
            fully_faithful: diag.fully_faithful,
        }
    }
}

fn parse_bool(value: &str, path: &Path, line: usize) -> bool {
    match value {
        "true" => true,
        "false" => false,
        _ => panic!("{}:{line}: invalid bool {value:?}", path.display()),
    }
}

fn read_baseline(path: &Path) -> BTreeMap<String, GateRow> {
    let text = std::fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("read required baseline {}: {e}", path.display()));
    let mut lines = text.lines();
    assert_eq!(
        lines.next(),
        Some(
            "def_path\tcluster_tag\tvia_ir_shape\tvia_ir_safety\tvia_mirsem_shape\t\
             via_mirsem_sl_safety_discharged\tvia_mirsem_call_requires\t\
             via_mirsem_loop_full\tfully_faithful"
        ),
        "baseline schema drifted"
    );
    let mut rows = BTreeMap::new();
    for (offset, line) in lines.enumerate() {
        let line_no = offset + 2;
        let fields: Vec<_> = line.split('\t').collect();
        assert_eq!(fields.len(), 9, "{}:{line_no}: malformed row", path.display());
        let row = GateRow {
            cluster: fields[1].to_string(),
            via_ir_shape: parse_bool(fields[2], path, line_no),
            via_ir_safety: parse_bool(fields[3], path, line_no),
            via_mirsem_shape: parse_bool(fields[4], path, line_no),
            via_mirsem_sl_safety_discharged: parse_bool(fields[5], path, line_no),
            via_mirsem_call_requires: parse_bool(fields[6], path, line_no),
            via_mirsem_loop_full: parse_bool(fields[7], path, line_no),
            fully_faithful: parse_bool(fields[8], path, line_no),
        };
        assert!(rows.insert(fields[0].to_string(), row).is_none(), "duplicate baseline row");
    }
    rows
}

/// Undo the crate-root qualification the producer added in the 2026-07-29
/// re-freeze, so a fresh dump keys against the historical baseline TSV without
/// rewriting that record. Asserted to be a bijection at the call site — if it
/// ever stops being one, the inventory assertions below fail loudly rather than
/// silently dropping rows.
fn strip_crate_root(def_path: &str) -> String {
    def_path.replace("lib::", "")
}

fn read_all_functions(dir: &Path) -> Vec<VerifiableFunction> {
    assert!(
        dir.is_dir(),
        "required fixture corpus {} is missing; it is checked in, so this is a defect, \
         not a checkout that may be skipped",
        dir.display(),
    );
    let mut paths: Vec<_> = std::fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("read required corpus {}: {e}", dir.display()))
        .map(|entry| entry.unwrap_or_else(|e| panic!("read corpus entry: {e}")).path())
        .filter(|path| path.extension().and_then(|ext| ext.to_str()) == Some("json"))
        .collect();
    paths.sort();
    paths
        .into_iter()
        .map(|path| {
            let bytes = std::fs::read(&path)
                .unwrap_or_else(|e| panic!("read required fixture {}: {e}", path.display()));
            serde_json::from_slice(&bytes)
                .unwrap_or_else(|e| panic!("parse required fixture {}: {e}", path.display()))
        })
        .collect()
}

fn production_diagnoses(funcs: &[VerifiableFunction]) -> BTreeMap<String, FullyFaithfulDiagnosis> {
    let order = trust_vcgen::compute_verification_order(&trust_vcgen::build_call_graph(funcs));
    let mut by_path: BTreeMap<&str, VecDeque<usize>> = BTreeMap::new();
    for (index, func) in funcs.iter().enumerate() {
        by_path.entry(func.def_path.as_str()).or_default().push_back(index);
    }
    let mut sequence = Vec::with_capacity(funcs.len());
    for def_path in &order {
        if let Some(index) = by_path.get_mut(def_path.as_str()).and_then(VecDeque::pop_front) {
            sequence.push(index);
        }
    }
    for index in 0..funcs.len() {
        if !sequence.contains(&index) {
            sequence.push(index);
        }
    }

    let bodies: DumpBodies =
        funcs.iter().map(|func| (func.def_path.clone(), func.clone())).collect();
    let mut certified: BTreeMap<String, CalleeFact> = BTreeMap::new();
    let mut rows = BTreeMap::new();
    for index in sequence {
        let func = &funcs[index];
        let diag = diagnose_fully_faithful_gate_with_bodies(func, &certified, &bodies);
        if diag.fully_faithful {
            certified.insert(func.def_path.clone(), CalleeFact::of_certified(func));
        }
        assert!(
            rows.insert(func.def_path.clone(), diag).is_none(),
            "duplicate current row for {}",
            func.def_path
        );
    }
    rows
}

#[test]
fn strict_unsigned_to_signed_widening_is_the_exact_production_corpus_delta() {
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let corpus = manifest.join("fixtures/census-rung2-2026-07-07/cast");
    let baseline_path =
        manifest.join("fixtures/crate-ladder-recensus-2026-07-11/results/cast.ff-gate.tsv");
    let baseline = read_baseline(&baseline_path);
    let funcs = read_all_functions(&corpus);
    let raw_diagnoses = production_diagnoses(&funcs);

    // Re-key onto the baseline's spelling. Injectivity is checked, not assumed:
    // a collision here would silently merge two rows and shrink the inventory.
    let mut diagnoses: BTreeMap<String, FullyFaithfulDiagnosis> = BTreeMap::new();
    for (path, diag) in &raw_diagnoses {
        assert!(
            diagnoses.insert(strip_crate_root(path), diag.clone()).is_none(),
            "crate-root stripping is not injective: two rows collide on {}",
            strip_crate_root(path),
        );
    }
    let current: BTreeMap<_, _> = diagnoses
        .iter()
        .map(|(path, diag)| (path.clone(), GateRow::from_diagnosis(diag)))
        .collect();

    let expected_widenings: BTreeSet<String> = [
        "_64::<impl From<u8> for i16>::cast",
        "_64::<impl From<u8> for i32>::cast",
        "_64::<impl From<u8> for i64>::cast",
        "_64::<impl From<u8> for isize>::cast",
        "_x128::<impl From<u8> for i128>::cast",
        "_64::<impl From<u16> for i32>::cast",
        "_64::<impl From<u16> for i64>::cast",
        "_64::<impl From<u16> for isize>::cast",
        "_x128::<impl From<u16> for i128>::cast",
        "_64::<impl From<u32> for i64>::cast",
        "_64::<impl From<u32> for isize>::cast",
        "_x128::<impl From<u32> for i128>::cast",
        "_x128::<impl From<u64> for i128>::cast",
        "_x128::<impl From<usize> for i128>::cast",
    ]
    .into_iter()
    .map(str::to_string)
    .collect();
    let expected_fieldless_error: BTreeSet<String> =
        ["<Error as core::clone::Clone>::clone", "<Error as core::cmp::PartialEq>::eq"]
            .into_iter()
            .map(str::to_string)
            .collect();
    let expected_changes: BTreeSet<String> =
        expected_widenings.union(&expected_fieldless_error).cloned().collect();
    // REQUIRED regressions vs the 2026-07-11 baseline: the three rows HEAD
    // closed on purpose (re-freeze report §6). Two are the non-`Int` return-type
    // blanket over float→float identity casts; the third was a genuine FALSE
    // ACCEPT at >64-bit witness width. Pinned so that re-blessing one is a
    // failure here, and so that "lost_faithful is empty" can no longer be
    // written as an unconditional assertion that quietly stops being true.
    let expected_regressions: BTreeSet<String> = [
        "_64::<impl From<f32> for f32>::cast",
        "_64::<impl From<f64> for f64>::cast",
        "_x128::<impl From<u128> for i128>::cast",
    ]
    .into_iter()
    .map(str::to_string)
    .collect();

    assert_eq!(funcs.len(), 202, "cast corpus inventory drifted");
    assert_eq!(baseline.len(), 202, "baseline inventory drifted");
    assert_eq!(current.len(), 202, "current diagnosis inventory drifted");
    assert_eq!(
        baseline.keys().collect::<Vec<_>>(),
        current.keys().collect::<Vec<_>>(),
        "baseline/current def-path inventories differ after crate-root stripping — \
         the corpus identity moved, not just its spelling"
    );

    let changed: BTreeSet<String> = baseline
        .iter()
        .filter_map(|(path, old)| (current.get(path) != Some(old)).then_some(path.clone()))
        .collect();
    let newly_faithful: BTreeSet<String> = baseline
        .iter()
        .filter_map(|(path, old)| {
            let new = current.get(path).expect("inventory equality checked");
            (!old.fully_faithful && new.fully_faithful).then_some(path.clone())
        })
        .collect();
    let lost_faithful: BTreeSet<String> = baseline
        .iter()
        .filter_map(|(path, old)| {
            let new = current.get(path).expect("inventory equality checked");
            (old.fully_faithful && !new.fully_faithful).then_some(path.clone())
        })
        .collect();

    let expected_changed: BTreeSet<String> =
        expected_changes.union(&expected_regressions).cloned().collect();
    assert_eq!(changed, expected_changed, "a non-target diagnostic row changed");
    assert_eq!(
        newly_faithful, expected_changes,
        "the false→true delta is not exactly the fourteen widenings plus two fieldless enums"
    );
    assert_eq!(
        lost_faithful, expected_regressions,
        "the true→false delta is not exactly the three deliberately closed rows"
    );
    // 132 + 16 gained - 3 lost = 145. See the header: 148 was this test's number
    // before the re-freeze made the three §6 closures visible on this corpus.
    assert_eq!(baseline.values().filter(|row| row.fully_faithful).count(), 132);
    assert_eq!(current.values().filter(|row| row.fully_faithful).count(), 145);
    assert_eq!(expected_widenings.len(), 14);
    assert_eq!(newly_faithful.len(), 16);
    assert_eq!(lost_faithful.len(), 3);

    let expected_target_diagnosis = FullyFaithfulDiagnosis {
        via_ir_shape: true,
        via_ir_safety: true,
        via_ir: true,
        expr_fold_decline: None,
        via_mirsem_straight_line_shape: true,
        via_mirsem_loop_shape: false,
        via_mirsem_shape: true,
        via_mirsem_straight_line_safety_discharged: true,
        via_mirsem_call_requires: true,
        via_mirsem_loop_full: false,
        via_mirsem: true,
        fully_faithful: true,
    };
    for path in &expected_widenings {
        assert_eq!(
            diagnoses.get(path),
            Some(&expected_target_diagnosis),
            "{path}: both semantic lanes must independently certify the widening"
        );
    }

    // `Error::clone` is TrustIR-ONLY. `Error::eq` also inhabits the
    // independently checked typed straight-line Bool-equality MirSem lane — the
    // same sound overlap `trustir_fieldless.rs`'s metadata gate already records.
    // Measured on the re-frozen corpus, not assumed: pinning both rows to the
    // TrustIR-only vector would be asserting the overlap away.
    let expected_fieldless_clone = FullyFaithfulDiagnosis {
        via_ir_shape: true,
        via_ir_safety: true,
        via_ir: true,
        expr_fold_decline: None,
        via_mirsem_straight_line_shape: false,
        via_mirsem_loop_shape: false,
        via_mirsem_shape: false,
        via_mirsem_straight_line_safety_discharged: false,
        via_mirsem_call_requires: false,
        via_mirsem_loop_full: false,
        via_mirsem: false,
        fully_faithful: true,
    };
    assert_eq!(
        diagnoses.get("<Error as core::clone::Clone>::clone"),
        Some(&expected_fieldless_clone),
        "the fieldless enum clone must certify TrustIR-only"
    );
    assert_eq!(
        diagnoses.get("<Error as core::cmp::PartialEq>::eq"),
        Some(&expected_target_diagnosis),
        "the fieldless enum eq must certify through TrustIR AND the overlapping \
         straight-line MirSem Bool-equality lane"
    );
    assert_eq!(expected_fieldless_error.len(), 2);

    // The three deliberately closed rows must be SHAPE declines on BOTH lanes —
    // fail-closed, not a softened variant of certification.
    for path in &expected_regressions {
        let diag = diagnoses.get(path).unwrap_or_else(|| panic!("{path}: missing from corpus"));
        assert!(
            !diag.fully_faithful && !diag.via_ir_shape && !diag.via_mirsem_shape,
            "{path} must stay declined on both lanes (re-freeze report §6), got {diag:?}"
        );
    }
}
