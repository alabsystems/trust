//! Historical published dispositions are measurements, not saved proof reports.
//! This deliberately does not relax obligations::parse_package_ndjson, whose
//! current header/grade requirements remain the sole proof-record boundary.

use std::io;

use serde_json::Value;

use super::parse::{self, Attributions, Audit};
use super::*;

type Published = BTreeMap<(String, String), Verdict>;
type CrateFunction = (String, String);
const SCHEMA: &str = "trust.obligations.v1";

pub(super) fn compare(
    pair: AuditInputPair<'_>,
    policy: &ComparisonPolicy,
    mut attributions: Attributions,
) -> ComparisonReport {
    let (parent, parent_errors) = match read(pair.parent) {
        Ok(result) => result,
        Err(error) => return ComparisonReport::could_not_run(error.to_string()),
    };
    let (candidate, candidate_errors) = match read(pair.candidate) {
        Ok(result) => result,
        Err(error) => return ComparisonReport::could_not_run(error.to_string()),
    };
    if parent.is_empty() || candidate.is_empty() {
        let mut report = ComparisonReport::new();
        report.parent.obligations = parent.len();
        report.candidate.obligations = candidate.len();
        report.malformed = parent_errors.into_iter().chain(candidate_errors).collect();
        if !report.malformed.is_empty() {
            report.diagnostics(false);
            report.conclude(
                ComparisonOutcome::CouldNotRun,
                "OBLIGATIONS: COULD NOT RUN — malformed records",
            );
            return report;
        }
        report.conclude(
            ComparisonOutcome::CouldNotRun,
            "OBLIGATIONS: COULD NOT RUN — a side has no trust.obligations.v1 record",
        );
        return report;
    }
    let mut clock = BTreeSet::<CrateFunction>::new();
    for records in [&parent, &candidate] {
        for ((package, key), (_, stop)) in records {
            if clock_verdict(stop) {
                clock.insert((package.clone(), key_function(key).into()));
            }
        }
    }
    let parent_audit = match optional_audit(pair.parent) {
        Ok(audit) => audit,
        Err(error) => return ComparisonReport::could_not_run(error.to_string()),
    };
    let candidate_audit = match optional_audit(pair.candidate) {
        Ok(audit) => audit,
        Err(error) => return ComparisonReport::could_not_run(error.to_string()),
    };
    let judged = policy.judged_sites();
    let mut audit_clock = BTreeSet::<CrateFunction>::new();
    for audit in [parent_audit.as_ref(), candidate_audit.as_ref()].into_iter().flatten() {
        audit_clock.extend(functions_by_key(audit, &audit.unreproducible_functions()));
    }
    let mut audit_caps = BTreeMap::<CrateFunction, Vec<String>>::new();
    let mut report = ComparisonReport::new();
    if let Some(audit) = &parent_audit {
        attributions.validate(audit, &judged);
        for (function, sites) in l4::cap_attributed(audit, &attributions, &judged) {
            for crate_function in functions_by_key(audit, &[function].into_iter().collect()) {
                audit_caps.insert(crate_function, sites.clone());
            }
        }
        report.unattributed = l4::unattributed_crate_caps(audit, &attributions, &judged);
        report.parent = audit.census();
    } else {
        attributions.no_parent();
    }
    if let Some(audit) = &candidate_audit {
        report.violations = l4::candidate_deleted_caps(audit, &judged);
        report.candidate = audit.census();
    }
    report.parent.obligations = parent.len();
    report.candidate.obligations = candidate.len();
    let keys = parent.keys().chain(candidate.keys()).collect::<BTreeSet<_>>();
    for (package, key) in keys {
        let before = parent.get(&(package.clone(), key.clone()));
        let after = candidate.get(&(package.clone(), key.clone()));
        if before == after {
            continue;
        }
        let function = key_function(key);
        let crate_function = (package.replace('-', "_"), function.to_owned());
        let detail = format!("{} -> {}", disposition(before), disposition(after));
        if clock.contains(&(package.clone(), function.into()))
            || audit_clock.contains(&crate_function)
        {
            report.listed.push(format!("obligation clock-stopped\t{package}\t{key}\t{detail}"));
        } else if let Some(sites) = audit_caps.get(&crate_function) {
            report.listed.push(format!(
                "obligation cap-attributed ({})\t{package}\t{key}\t{detail}",
                l4::site_labels(sites)
            ));
        } else {
            report.violations.push(format!("obligation moved\t{package}\t{key}\t{detail}"));
        }
    }
    let mut audit_names = Vec::new();
    if parent_audit.is_some() {
        audit_names.push("parent");
    }
    if candidate_audit.is_some() {
        audit_names.push("tip");
    }
    let audit_names = if audit_names.is_empty() {
        "none".into()
    } else {
        format!(
            "[{}]",
            audit_names.iter().map(|name| py_string(name)).collect::<Vec<_>>().join(", ")
        )
    };
    report.lines.push(format!(
        "parent   : {} obligations; tip: {} obligations; audits read: {audit_names}",
        parent.len(),
        candidate.len()
    ));
    report.malformed =
        parent_errors.into_iter().chain(candidate_errors).chain(attributions.errors).collect();
    for (name, audit) in [("parent", parent_audit.as_ref()), ("tip", candidate_audit.as_ref())] {
        if let Some(audit) = audit {
            report.malformed.extend(audit.malformed.iter().map(|line| format!("{name}\t{line}")));
        }
    }
    report.diagnostics(false);
    if !report.malformed.is_empty() {
        report.conclude(
            ComparisonOutcome::CouldNotRun,
            "OBLIGATIONS: COULD NOT RUN — malformed records",
        );
    } else if !report.unattributed.is_empty() {
        report.conclude(
            ComparisonOutcome::CouldNotRun,
            format!(
                "OBLIGATIONS: COULD NOT RUN — {} unattributed crate-level hit(s)",
                report.unattributed.len()
            ),
        );
    } else if !report.violations.is_empty() {
        report.conclude(
            ComparisonOutcome::Violation,
            format!("OBLIGATIONS: {} violation(s)", report.violations.len()),
        );
    } else {
        report.conclude(
            ComparisonOutcome::Pass,
            "OBLIGATIONS: published dispositions identical up to the listed rows",
        );
    }
    report
}

fn optional_audit(root: &Path) -> io::Result<Option<Audit>> {
    if root.is_dir() && !parse::audit_files(root)?.is_empty() {
        Audit::read(root, true).map(Some)
    } else {
        Ok(None)
    }
}

fn key_function(key: &str) -> &str {
    key.rsplit_once('#').map(|(function, _)| function).unwrap_or(key)
}

fn functions_by_key(audit: &Audit, functions: &BTreeSet<Function>) -> BTreeSet<CrateFunction> {
    audit
        .t9_keys
        .iter()
        .filter(|(function, _)| functions.contains(*function))
        .flat_map(|(function, keys)| {
            keys.iter().map(move |key| (function[2].clone(), key_function(key).to_owned()))
        })
        .collect()
}

fn disposition(value: Option<&Verdict>) -> String {
    value
        .map(|(status, stop)| format!("({}, {})", py_string(status), py_string(stop)))
        .unwrap_or_else(|| "absent".into())
}

fn read(root: &Path) -> io::Result<(Published, Vec<String>)> {
    let files = if root.is_dir() {
        parse::walk_files(root)?
            .into_iter()
            .filter(|path| path.extension().is_some_and(|extension| extension == "ndjson"))
            .collect::<Vec<_>>()
    } else if root.exists() {
        vec![root.to_owned()]
    } else {
        Vec::new()
    };
    let mut records = Published::new();
    let mut errors = Vec::new();
    for path in files {
        let bytes = parse::read_bytes(&path)?;
        let text = String::from_utf8_lossy(&bytes);
        let mut lines = parse::historical_lines(&text);
        let Some(header_line) = lines.next() else {
            continue;
        };
        let header = match serde_json::from_str::<Value>(header_line) {
            Ok(header) => header,
            Err(error) => {
                errors.push(format!("{}:1: not JSON header: {error}", path.display()));
                continue;
            }
        };
        let Some(header) = Some(header).filter(|header| {
            header.is_object() && header.get("schema").and_then(Value::as_str) == Some(SCHEMA)
        }) else {
            continue;
        };
        // Minimal historical v1 headers are intentionally supported here. They
        // confer no grade/seal authority and cannot reach the proof reader.
        let package = match header.get("package") {
            None => "-".into(),
            Some(Value::String(package)) => package.clone(),
            Some(_) => {
                errors.push(format!("{}:1: package must be a string", path.display()));
                continue;
            }
        };
        for (index, line) in lines.enumerate() {
            let number = index + 2;
            let row = match serde_json::from_str::<Value>(line) {
                Ok(row) => row,
                Err(_) => {
                    errors.push(format!("{}:{number}: not JSON", path.display()));
                    continue;
                }
            };
            // A function line, or a compile error (a disposition of no
            // obligation: the package's missing obligations are what the
            // comparison sees of it).
            if row.get("fn").is_some() || row.get("compile_error").is_some() {
                continue;
            }
            let Some(((key, status), stop)) = row
                .get("key")
                .and_then(Value::as_str)
                .zip(row.get("status").and_then(Value::as_str))
                .zip(row.get("stop").and_then(Value::as_str))
            else {
                errors.push(format!(
                    "{}:{number}: an obligation without key, status and stop",
                    path.display()
                ));
                continue;
            };
            let identity = (package.clone(), key.to_owned());
            if records.contains_key(&identity) {
                errors.push(format!("{}:{number}: {package} {key} recorded twice", path.display()));
                continue;
            }
            records.insert(identity, (status.into(), stop.into()));
        }
    }
    Ok((records, errors))
}
