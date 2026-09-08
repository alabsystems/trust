//! Trust — STEP 4 (verified-sysroot scoping) COVERAGE RATCHET for `core::num`.
//!
//! Plan of record: `docs/design/2026-08-19-verified-sysroot-scoping.md`, §5
//! step 4, third bullet, implemented verbatim:
//!
//! > "a coverage ratchet so the number can only go up."
//!
//! The number it holds is the step's deliverable:
//!
//! > "N functions in `library/core` carry a discharged L0 obligation set,
//! > verified by `trustc`, gate-checked."
//!
//! # What this ratchet reads — the measurement artifact, defined here
//!
//! Two committed files under `fixtures/std-coverage/`:
//!
//! * **`core_num_l0_coverage.snapshot.json`** — the MEASUREMENT. Schema
//!   `trust-std-coverage-v1`, lane `std-core-num-l0`: a list of
//!   `{def_path, discharged_l0_obligations}` rows for every `core::num`
//!   function the Mode::Std verification lane verified, plus the two totals
//!   `verified_function_count` and `discharged_l0_obligation_count`, plus a
//!   required `assumption_records_excluded: true` attestation. This is the
//!   exact artifact the step-4 lane's build is expected to emit; until that
//!   build has run, the committed file is a 0-row placeholder that the main
//!   session's reserved std-build step regenerates (this test never builds
//!   std and never invents a number — it only reads what is committed).
//! * **`core_num_l0_floor.txt`** — the FLOOR, hand-edited and reviewed. Its
//!   header carries the full update procedure.
//!
//! The gate goes red on ANY disagreement between the two, in BOTH directions:
//! a snapshot below the floor is a REGRESSION (verified coverage was
//! retired); a snapshot above the floor is an UNBANKED GAIN (raise the floor
//! in the same commit, or the gain is held by no gate). Exact agreement
//! rather than `floor <= snapshot`-with-slack is the measured lesson of this
//! crate's prior ratchet (`flip.rs`, Trust #63): a slack bound cannot see a
//! regression inside the slack. The letter of the step-4 fallback contract —
//! "the test validates floor <= snapshot" — is strictly implied by the
//! stronger check.
//!
//! # Why the attestation field is load-bearing (§1.4 of the plan)
//!
//! `PolicyBucket::UpstreamRustModified` turns unsupported obligations into
//! assumption records, and §1.4 is explicit that counting those would be the
//! failure mode: "an assumption record is still an assumption. Reaching real
//! coverage means graduating modules out of that bucket into
//! `TrustOwnedDefault`." A snapshot whose emitter cannot attest
//! `assumption_records_excluded: true` — i.e. that every counted obligation
//! was DISCHARGED, with assumption records counted by nobody — is refused
//! outright, so the ratchet can never be fed the number the plan warns about.
//!
//! # What this ratchet is NOT (§1.2 of the plan)
//!
//! §1.2: "Bootstrap is deliberately not self-proof", and the plan requires
//! the std lane be "separately named ... so
//! `rustflags_request_bootstrap_verification`'s panic ... is not weakened".
//! This module is measurement-side only: it changes no build, sets no flag,
//! and grants no verification authority — a snapshot row is a COVERAGE COUNT,
//! never a proof claim, and nothing here lets any std artifact claim
//! self-proof. Absence or emptiness of the snapshot blocks no build; the
//! fail-closed defaults and the explicit opt-in of the lane are untouched.
//!
//! # Scope
//!
//! Rows must belong to `core::num` (accepted def_path spellings: the external
//! `core::num::...` and the crate-local `num::...` that library-internal
//! extraction produces — both occur in this repo's committed dumps). Anything
//! else is refused: an out-of-scope row would inflate N with functions the
//! step-4 claim does not cover. Widening the scope (e.g. to `core::slice`)
//! is a deliberate, reviewed edit to `SCOPE_PREFIXES` with the plan section
//! that authorizes it.

/// Accepted def_path prefixes for the `std-core-num-l0` lane. See module doc.
const SCOPE_PREFIXES: &[&str] = &["core::num::", "num::"];

/// The schema identity the snapshot must declare. Anything else is refused
/// with the fix named (regenerate with the current lane, or update this
/// ratchet in the same commit as a deliberate schema migration).
const SNAPSHOT_SCHEMA: &str = "trust-std-coverage-v1";

/// The lane identity. One ratchet per lane; a snapshot from a different lane
/// must not be able to satisfy this one.
const SNAPSHOT_LANE: &str = "std-core-num-l0";

/// The banked floor — parsed from `core_num_l0_floor.txt`.
#[derive(Debug, PartialEq, Eq)]
pub(crate) struct CoverageFloor {
    pub(crate) verified_function_count_floor: usize,
    pub(crate) discharged_l0_obligation_count_floor: usize,
}

/// One verified function in the snapshot.
#[derive(Debug, PartialEq, Eq)]
pub(crate) struct SnapshotRow {
    pub(crate) def_path: String,
    pub(crate) discharged_l0_obligations: usize,
}

/// The measured snapshot — parsed (fail-closed) from
/// `core_num_l0_coverage.snapshot.json`.
#[derive(Debug, PartialEq, Eq)]
pub(crate) struct CoverageSnapshot {
    pub(crate) verified_function_count: usize,
    pub(crate) discharged_l0_obligation_count: usize,
    pub(crate) rows: Vec<SnapshotRow>,
}

/// Parse the floor file. FAIL-CLOSED: exactly the two known keys, once each;
/// `#` comments and blank lines only otherwise. Unknown keys, duplicates,
/// missing keys and non-integer values are errors, never defaults — a floor
/// that silently read as 0 would be a ratchet that holds nothing.
pub(crate) fn parse_floor(text: &str) -> Result<CoverageFloor, String> {
    let mut verified: Option<usize> = None;
    let mut discharged: Option<usize> = None;
    for (idx, raw) in text.lines().enumerate() {
        let line = raw.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let Some((key, value)) = line.split_once('=') else {
            return Err(format!(
                "floor line {} is neither a comment nor `key = value`: `{raw}`",
                idx + 1
            ));
        };
        let (key, value) = (key.trim(), value.trim());
        let parsed: usize = value.parse().map_err(|e| {
            format!("floor key `{key}` has a non-integer value `{value}` (line {}): {e}", idx + 1)
        })?;
        let slot = match key {
            "verified_function_count_floor" => &mut verified,
            "discharged_l0_obligation_count_floor" => &mut discharged,
            other => {
                return Err(format!(
                    "floor key `{other}` (line {}) is not part of the schema; the two known \
                     keys are `verified_function_count_floor` and \
                     `discharged_l0_obligation_count_floor`. A new metric is a deliberate \
                     ratchet change, not a floor-file edit alone",
                    idx + 1
                ));
            }
        };
        if slot.is_some() {
            return Err(format!("floor key `{key}` appears more than once (line {})", idx + 1));
        }
        *slot = Some(parsed);
    }
    match (verified, discharged) {
        (Some(v), Some(d)) => Ok(CoverageFloor {
            verified_function_count_floor: v,
            discharged_l0_obligation_count_floor: d,
        }),
        (v, d) => {
            let mut missing = Vec::new();
            if v.is_none() {
                missing.push("verified_function_count_floor");
            }
            if d.is_none() {
                missing.push("discharged_l0_obligation_count_floor");
            }
            Err(format!(
                "floor file is missing required key(s): {} — a missing floor is not zero, \
                 it is unreadable",
                missing.join(", ")
            ))
        }
    }
}

fn usize_field(obj: &serde_json::Map<String, serde_json::Value>, key: &str) -> Result<usize, String> {
    let v = obj
        .get(key)
        .ok_or_else(|| format!("snapshot is missing required key `{key}`"))?;
    let n = v
        .as_u64()
        .ok_or_else(|| format!("snapshot key `{key}` must be a non-negative integer, got {v}"))?;
    usize::try_from(n).map_err(|_| format!("snapshot key `{key}` value {n} overflows usize"))
}

fn str_field<'a>(
    obj: &'a serde_json::Map<String, serde_json::Value>,
    key: &str,
) -> Result<&'a str, String> {
    obj.get(key)
        .ok_or_else(|| format!("snapshot is missing required key `{key}`"))?
        .as_str()
        .ok_or_else(|| format!("snapshot key `{key}` must be a string"))
}

/// Parse and internally validate the snapshot. FAIL-CLOSED on: unknown or
/// missing keys (top-level and per-row), a wrong `schema` or `lane`, a
/// missing/false `assumption_records_excluded` attestation, an out-of-scope
/// or duplicate `def_path`, a total that does not equal what its own rows
/// sum to, and arithmetic overflow. A snapshot that cannot state its own
/// numbers consistently is not a measurement.
pub(crate) fn parse_snapshot(text: &str) -> Result<CoverageSnapshot, String> {
    let value: serde_json::Value =
        serde_json::from_str(text).map_err(|e| format!("snapshot is not valid JSON: {e}"))?;
    let obj = value.as_object().ok_or("snapshot top level must be a JSON object")?;

    const TOP_KEYS: &[&str] = &[
        "schema",
        "lane",
        "generated_by",
        "assumption_records_excluded",
        "verified_functions",
        "verified_function_count",
        "discharged_l0_obligation_count",
    ];
    for key in obj.keys() {
        if !TOP_KEYS.contains(&key.as_str()) {
            return Err(format!(
                "snapshot carries unknown top-level key `{key}`; the {SNAPSHOT_SCHEMA} schema \
                 keys are exactly {TOP_KEYS:?}. A schema extension is a deliberate ratchet \
                 change, not a snapshot edit alone"
            ));
        }
    }
    for key in TOP_KEYS {
        if !obj.contains_key(*key) {
            return Err(format!("snapshot is missing required key `{key}`"));
        }
    }

    let schema = str_field(obj, "schema")?;
    if schema != SNAPSHOT_SCHEMA {
        return Err(format!(
            "snapshot declares schema `{schema}`, this ratchet reads `{SNAPSHOT_SCHEMA}`. \
             Fix: regenerate the snapshot with the current lane, or migrate this ratchet's \
             parser in the same commit as the schema change"
        ));
    }
    let lane = str_field(obj, "lane")?;
    if lane != SNAPSHOT_LANE {
        return Err(format!(
            "snapshot declares lane `{lane}`, this ratchet gates `{SNAPSHOT_LANE}`; a \
             different lane's coverage cannot satisfy this gate"
        ));
    }
    let generated_by = str_field(obj, "generated_by")?;
    if generated_by.trim().is_empty() {
        return Err("snapshot `generated_by` must name its producing measurement (or the \
                    placeholder state); an unattributed measurement is not evidence"
            .to_string());
    }
    match obj.get("assumption_records_excluded").and_then(serde_json::Value::as_bool) {
        Some(true) => {}
        Some(false) => {
            return Err(
                "snapshot attests `assumption_records_excluded: false` — refused. Plan §1.4: \
                 an assumption record is still an assumption; this lane's numbers may count \
                 only DISCHARGED obligations. Fix: narrow the targeted modules to \
                 `TrustOwnedDefault` (plan §5 step 4) so the lane emits proofs, then \
                 regenerate"
                    .to_string(),
            );
        }
        None => {
            return Err(
                "snapshot key `assumption_records_excluded` must be a boolean".to_string()
            );
        }
    }

    let rows_value = obj
        .get("verified_functions")
        .and_then(serde_json::Value::as_array)
        .ok_or("snapshot key `verified_functions` must be an array")?;
    let mut rows = Vec::with_capacity(rows_value.len());
    let mut seen = std::collections::BTreeSet::new();
    let mut sum: usize = 0;
    for (idx, row_value) in rows_value.iter().enumerate() {
        let row = row_value
            .as_object()
            .ok_or_else(|| format!("verified_functions[{idx}] must be an object"))?;
        const ROW_KEYS: &[&str] = &["def_path", "discharged_l0_obligations"];
        for key in row.keys() {
            if !ROW_KEYS.contains(&key.as_str()) {
                return Err(format!(
                    "verified_functions[{idx}] carries unknown key `{key}`; row keys are \
                     exactly {ROW_KEYS:?}"
                ));
            }
        }
        let def_path = str_field(row, "def_path")
            .map_err(|e| format!("verified_functions[{idx}]: {e}"))?;
        if def_path.trim().is_empty() {
            return Err(format!("verified_functions[{idx}] has an empty def_path"));
        }
        if !SCOPE_PREFIXES.iter().any(|p| def_path.starts_with(p)) {
            return Err(format!(
                "verified_functions[{idx}] def_path `{def_path}` is outside the \
                 {SNAPSHOT_LANE} scope (accepted prefixes: {SCOPE_PREFIXES:?}). An \
                 out-of-scope row would inflate N with a function the step-4 claim does \
                 not cover; widening the scope is a reviewed edit to SCOPE_PREFIXES with \
                 the plan section that authorizes it"
            ));
        }
        if !seen.insert(def_path.to_string()) {
            return Err(format!(
                "verified_functions[{idx}] def_path `{def_path}` appears more than once — \
                 a duplicate row double-counts N"
            ));
        }
        let discharged = usize_field(row, "discharged_l0_obligations")
            .map_err(|e| format!("verified_functions[{idx}]: {e}"))?;
        sum = sum.checked_add(discharged).ok_or_else(|| {
            format!("verified_functions[{idx}]: obligation total overflows usize")
        })?;
        rows.push(SnapshotRow { def_path: def_path.to_string(), discharged_l0_obligations: discharged });
    }

    let verified_function_count = usize_field(obj, "verified_function_count")?;
    if verified_function_count != rows.len() {
        return Err(format!(
            "snapshot claims verified_function_count={verified_function_count} but carries \
             {} row(s) — a count its own rows do not back is not a measurement",
            rows.len()
        ));
    }
    let discharged_l0_obligation_count = usize_field(obj, "discharged_l0_obligation_count")?;
    if discharged_l0_obligation_count != sum {
        return Err(format!(
            "snapshot claims discharged_l0_obligation_count={discharged_l0_obligation_count} \
             but its rows sum to {sum} — a total its own rows do not back is not a \
             measurement"
        ));
    }

    Ok(CoverageSnapshot { verified_function_count, discharged_l0_obligation_count, rows })
}

/// The ratchet comparison. Returns EVERY finding rather than aborting at the
/// first (`flip.rs` Trust #63: a gate that fires first and aborts hides every
/// gate behind it). Empty result = green.
pub(crate) fn evaluate_ratchet(floor: &CoverageFloor, snap: &CoverageSnapshot) -> Vec<String> {
    let mut findings = Vec::new();
    let metrics: &[(&str, usize, usize)] = &[
        (
            "verified core::num function count N",
            snap.verified_function_count,
            floor.verified_function_count_floor,
        ),
        (
            "discharged L0 obligation count",
            snap.discharged_l0_obligation_count,
            floor.discharged_l0_obligation_count_floor,
        ),
    ];
    for (name, measured, floor_value) in metrics {
        if measured < floor_value {
            findings.push(format!(
                "REGRESSION: {name} fell to {measured} (floor {floor_value}). Verified \
                 coverage was retired; the number may only go up. Either restore the \
                 coverage, or — for a deliberate retirement — lower the floor with an \
                 attribution in core_num_l0_floor.txt naming which functions stopped \
                 verifying and why"
            ));
        } else if measured > floor_value {
            findings.push(format!(
                "UNBANKED GAIN: {name} measured {measured} against floor {floor_value}. \
                 Raise the floor to {measured} in core_num_l0_floor.txt in the SAME \
                 commit that regenerated the snapshot — an unbanked gain is held by no \
                 gate, and the next regression back to {floor_value} would read green"
            ));
        }
    }
    findings
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::Path;

    fn committed(file: &str) -> String {
        let path =
            Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures/std-coverage").join(file);
        std::fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("cannot read committed ratchet input {path:?}: {e}"))
    }

    /// THE GATE. Reads the two committed files, refuses to run on unreadable
    /// input (an unparseable floor or snapshot makes every comparison below
    /// vacuous, so those stay hard failures), then reports every ratchet
    /// finding at once.
    #[test]
    fn core_num_l0_coverage_ratchet_holds() {
        let floor = parse_floor(&committed("core_num_l0_floor.txt"))
            .unwrap_or_else(|e| panic!("committed floor file is unreadable — {e}"));
        let snap = parse_snapshot(&committed("core_num_l0_coverage.snapshot.json"))
            .unwrap_or_else(|e| panic!("committed snapshot is unreadable — {e}"));
        let findings = evaluate_ratchet(&floor, &snap);
        assert!(
            findings.is_empty(),
            "{} step-4 ratchet finding(s), ALL of them:\n\n{}",
            findings.len(),
            findings
                .iter()
                .enumerate()
                .map(|(i, f)| format!("[{}/{}] {f}", i + 1, findings.len()))
                .collect::<Vec<_>>()
                .join("\n\n"),
        );
        eprintln!(
            "std-core-num-l0 ratchet: N={} verified core::num function(s) (floor {}), \
             {} discharged L0 obligation(s) (floor {})",
            snap.verified_function_count,
            floor.verified_function_count_floor,
            snap.discharged_l0_obligation_count,
            floor.discharged_l0_obligation_count_floor,
        );
    }

    /// A machine-readable statement of the current committed state, so the
    /// main session's first measured build has an unambiguous baseline: the
    /// placeholder is 0-row, 0-count, floor 0/0. This test EXPIRES the moment
    /// the first real measurement lands — delete it in that commit; its only
    /// job is to make "nobody has measured yet" a checked fact rather than a
    /// prose claim.
    #[test]
    fn committed_state_is_the_unmeasured_placeholder() {
        let floor = parse_floor(&committed("core_num_l0_floor.txt")).expect("floor parses");
        let snap = parse_snapshot(&committed("core_num_l0_coverage.snapshot.json"))
            .expect("snapshot parses");
        assert_eq!(
            (floor.verified_function_count_floor, floor.discharged_l0_obligation_count_floor),
            (0, 0),
            "floor moved off 0/0 — the first measured build has landed; delete this test \
             in the same commit"
        );
        assert_eq!(snap.rows.len(), 0, "snapshot has rows — delete this test in that commit");
    }
}

/// Trust — the ratchet's negative controls, on the `flip.rs` discipline: "a
/// gate that cannot go red is not a gate", so every refusal direction is
/// driven directly with synthetic inputs rather than through the committed
/// files.
#[cfg(test)]
mod controls {
    use super::*;

    fn floor(v: usize, d: usize) -> CoverageFloor {
        CoverageFloor { verified_function_count_floor: v, discharged_l0_obligation_count_floor: d }
    }

    fn snapshot_json(rows: &[(&str, usize)], count: usize, total: usize) -> String {
        let rendered: Vec<String> = rows
            .iter()
            .map(|(p, n)| {
                format!("{{\"def_path\": \"{p}\", \"discharged_l0_obligations\": {n}}}")
            })
            .collect();
        format!(
            "{{\"schema\": \"trust-std-coverage-v1\", \"lane\": \"std-core-num-l0\", \
             \"generated_by\": \"controls\", \"assumption_records_excluded\": true, \
             \"verified_functions\": [{}], \"verified_function_count\": {count}, \
             \"discharged_l0_obligation_count\": {total}}}",
            rendered.join(", ")
        )
    }

    fn parsed_snapshot(rows: &[(&str, usize)], count: usize, total: usize) -> CoverageSnapshot {
        parse_snapshot(&snapshot_json(rows, count, total)).expect("control snapshot parses")
    }

    /// THE FALSIFYING TEST the lane contract demands: a synthetic snapshot
    /// BELOW the floor must fail the ratchet. Both metrics, independently.
    #[test]
    fn snapshot_below_function_floor_is_red() {
        let snap =
            parsed_snapshot(&[("core::num::<impl u32>::checked_add", 3)], 1, 3);
        let findings = evaluate_ratchet(&floor(2, 3), &snap);
        assert_eq!(findings.len(), 1, "exactly the function-count regression: {findings:?}");
        assert!(
            findings[0].contains("REGRESSION") && findings[0].contains("function count N"),
            "finding must name the regressed metric: {findings:?}"
        );
    }

    #[test]
    fn snapshot_below_obligation_floor_is_red() {
        let snap =
            parsed_snapshot(&[("core::num::<impl u32>::checked_add", 3)], 1, 3);
        let findings = evaluate_ratchet(&floor(1, 5), &snap);
        assert_eq!(findings.len(), 1, "exactly the obligation-count regression: {findings:?}");
        assert!(
            findings[0].contains("REGRESSION")
                && findings[0].contains("discharged L0 obligation count"),
            "finding must name the regressed metric: {findings:?}"
        );
    }

    /// BOTH metrics regressing must produce BOTH findings — the instrument
    /// reports everything, aborting at nothing (flip.rs Trust #63).
    #[test]
    fn double_regression_reports_both_findings() {
        let snap = parsed_snapshot(&[], 0, 0);
        let findings = evaluate_ratchet(&floor(4, 9), &snap);
        assert_eq!(findings.len(), 2, "both regressions, one run: {findings:?}");
    }

    /// The anti-rot direction: a measured gain the floor does not bank is red,
    /// with the one-line fix in the message. Without this, the floor rots at 0
    /// and the ratchet holds nothing.
    #[test]
    fn unbanked_gain_is_red() {
        let snap = parsed_snapshot(
            &[
                ("core::num::<impl u32>::checked_add", 3),
                ("core::num::<impl u8>::count_ones", 1),
            ],
            2,
            4,
        );
        let findings = evaluate_ratchet(&floor(0, 0), &snap);
        assert_eq!(findings.len(), 2, "both unbanked metrics: {findings:?}");
        assert!(
            findings.iter().all(|f| f.contains("UNBANKED GAIN") && f.contains("Raise the floor")),
            "findings must carry the fix: {findings:?}"
        );
    }

    #[test]
    fn exact_agreement_is_green() {
        let snap =
            parsed_snapshot(&[("num::<impl i32>::wrapping_mul", 2)], 1, 2);
        assert!(evaluate_ratchet(&floor(1, 2), &snap).is_empty());
    }

    // ---- fail-closed parsing: the floor file ----

    #[test]
    fn floor_missing_key_is_refused() {
        let err = parse_floor("verified_function_count_floor = 3\n").unwrap_err();
        assert!(err.contains("missing required key"), "{err}");
    }

    #[test]
    fn floor_duplicate_key_is_refused() {
        let err = parse_floor(
            "verified_function_count_floor = 3\n\
             discharged_l0_obligation_count_floor = 1\n\
             verified_function_count_floor = 4\n",
        )
        .unwrap_err();
        assert!(err.contains("more than once"), "{err}");
    }

    #[test]
    fn floor_unknown_key_is_refused() {
        let err = parse_floor(
            "verified_function_count_floor = 3\n\
             discharged_l0_obligation_count_floor = 1\n\
             bonus_metric = 7\n",
        )
        .unwrap_err();
        assert!(err.contains("not part of the schema"), "{err}");
    }

    #[test]
    fn floor_negative_or_non_integer_value_is_refused() {
        for bad in ["-1", "3.5", "three"] {
            let err = parse_floor(&format!(
                "verified_function_count_floor = {bad}\n\
                 discharged_l0_obligation_count_floor = 0\n"
            ))
            .unwrap_err();
            assert!(err.contains("non-integer value"), "{bad}: {err}");
        }
    }

    #[test]
    fn floor_stray_line_is_refused() {
        let err = parse_floor("just some prose\n").unwrap_err();
        assert!(err.contains("neither a comment nor"), "{err}");
    }

    // ---- fail-closed parsing: the snapshot ----

    #[test]
    fn snapshot_wrong_schema_is_refused() {
        let text = snapshot_json(&[], 0, 0).replace("trust-std-coverage-v1", "v0");
        let err = parse_snapshot(&text).unwrap_err();
        assert!(err.contains("declares schema"), "{err}");
    }

    #[test]
    fn snapshot_wrong_lane_is_refused() {
        let text = snapshot_json(&[], 0, 0).replace("std-core-num-l0", "std-slice-l0");
        let err = parse_snapshot(&text).unwrap_err();
        assert!(err.contains("different lane"), "{err}");
    }

    /// §1.4's failure mode, refused at the parser: a snapshot that counts
    /// assumption records (or will not attest that it does not) is not
    /// coverage.
    #[test]
    fn snapshot_without_discharge_attestation_is_refused() {
        let text = snapshot_json(&[], 0, 0)
            .replace("\"assumption_records_excluded\": true", "\"assumption_records_excluded\": false");
        let err = parse_snapshot(&text).unwrap_err();
        assert!(err.contains("assumption record is still an assumption"), "{err}");
    }

    #[test]
    fn snapshot_count_not_backed_by_rows_is_refused() {
        let err = parse_snapshot(&snapshot_json(&[], 3, 0)).unwrap_err();
        assert!(err.contains("count its own rows do not back"), "{err}");
    }

    #[test]
    fn snapshot_total_not_backed_by_rows_is_refused() {
        let err = parse_snapshot(&snapshot_json(
            &[("core::num::<impl u32>::checked_add", 3)],
            1,
            9,
        ))
        .unwrap_err();
        assert!(err.contains("total its own rows do not back"), "{err}");
    }

    #[test]
    fn snapshot_out_of_scope_row_is_refused() {
        let err = parse_snapshot(&snapshot_json(
            &[("core::slice::index::<usize as SliceIndex>::index", 1)],
            1,
            1,
        ))
        .unwrap_err();
        assert!(err.contains("outside the std-core-num-l0 scope"), "{err}");
    }

    #[test]
    fn snapshot_duplicate_def_path_is_refused() {
        let err = parse_snapshot(&snapshot_json(
            &[
                ("core::num::<impl u32>::checked_add", 1),
                ("core::num::<impl u32>::checked_add", 1),
            ],
            2,
            2,
        ))
        .unwrap_err();
        assert!(err.contains("more than once"), "{err}");
    }

    #[test]
    fn snapshot_unknown_top_level_key_is_refused() {
        let text = snapshot_json(&[], 0, 0)
            .replace("\"lane\":", "\"self_proof\": true, \"lane\":");
        let err = parse_snapshot(&text).unwrap_err();
        assert!(err.contains("unknown top-level key `self_proof`"), "{err}");
    }

    #[test]
    fn snapshot_unknown_row_key_is_refused() {
        let text = snapshot_json(&[("core::num::<impl u8>::count_ones", 1)], 1, 1).replace(
            "\"discharged_l0_obligations\": 1",
            "\"discharged_l0_obligations\": 1, \"assumed\": 4",
        );
        let err = parse_snapshot(&text).unwrap_err();
        assert!(err.contains("unknown key `assumed`"), "{err}");
    }

    #[test]
    fn snapshot_missing_key_is_refused() {
        let err = parse_snapshot("{\"schema\": \"trust-std-coverage-v1\"}").unwrap_err();
        assert!(err.contains("missing required key"), "{err}");
    }

    /// Both accepted def_path spellings really are accepted — the external
    /// `core::num::...` and the crate-local `num::...` this repo's dumps show.
    #[test]
    fn both_scope_spellings_are_accepted() {
        let snap = parsed_snapshot(
            &[
                ("core::num::<impl u32>::leading_zeros", 0),
                ("num::<impl i64>::saturating_sub", 1),
            ],
            2,
            1,
        );
        assert_eq!(snap.rows.len(), 2);
    }
}
