// End-to-end production-gate pin for GAP-CROSS-SIGN-WIDEN.
//
// Diagnose every cast 0.3.0 corpus body in the same callees-first order and
// with the same sibling-body registry as production, then compare every field
// recorded by the checked pre-change census. Exactly fourteen
// unsigned-to-signed strict widenings may move, plus the two independently
// certified fieldless-`Error` methods added after that census; every other
// recorded row must be byte-semantically stable. Each allowed target pins its
// full diagnosis, keeping the two feature deltas explicit and disjoint.

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

fn read_all_functions(dir: &Path) -> Vec<VerifiableFunction> {
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
    let diagnoses = production_diagnoses(&funcs);
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

    assert_eq!(funcs.len(), 202, "cast corpus inventory drifted");
    assert_eq!(baseline.len(), 202, "baseline inventory drifted");
    assert_eq!(current.len(), 202, "current diagnosis inventory drifted");
    assert_eq!(
        baseline.keys().collect::<Vec<_>>(),
        current.keys().collect::<Vec<_>>(),
        "baseline/current def-path inventories differ"
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

    assert_eq!(changed, expected_changes, "a non-target diagnostic row changed");
    assert_eq!(
        newly_faithful, expected_changes,
        "the false→true delta is not exactly the fourteen widenings plus two fieldless enums"
    );
    assert!(lost_faithful.is_empty(), "previously faithful rows regressed: {lost_faithful:?}");
    assert_eq!(baseline.values().filter(|row| row.fully_faithful).count(), 132);
    assert_eq!(current.values().filter(|row| row.fully_faithful).count(), 148);

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

    let expected_fieldless_diagnosis = FullyFaithfulDiagnosis {
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
    for path in &expected_fieldless_error {
        assert_eq!(
            diagnoses.get(path),
            Some(&expected_fieldless_diagnosis),
            "{path}: fieldless enum certification must remain TrustIR-only"
        );
    }
}
