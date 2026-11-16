//! L4's row/verdict/elision multisets, exact refusal attribution and oracles.

use super::parse::{Attributions, Audit};
use super::*;

pub(super) type Attributed = BTreeMap<Function, Vec<String>>;

pub(super) fn compare(
    pair: AuditInputPair<'_>,
    policy: &ComparisonPolicy,
    mut attributions: Attributions,
) -> ComparisonReport {
    let (parent, candidate) = match Audit::read(pair.parent, true)
        .and_then(|parent| Audit::read(pair.candidate, true).map(|candidate| (parent, candidate)))
    {
        Ok(pair) => pair,
        Err(error) => return ComparisonReport::could_not_run(error.to_string()),
    };
    let judged = policy.judged_sites();
    let parent_clock = parent.unreproducible_functions();
    let candidate_clock = candidate.unreproducible_functions();
    let clock = parent_clock.union(&candidate_clock).cloned().collect::<BTreeSet<_>>();
    attributions.validate(&parent, &judged);
    let attributed = cap_attributed(&parent, &attributions, &judged);
    let mut report = ComparisonReport::new();
    report.violations = candidate_deleted_caps(&candidate, &judged);
    let mut vacuous = Vec::new();
    compare_verdicts(&parent, &candidate, &clock, &attributed, &mut report);
    compare_rows(&parent, &candidate, &clock, &attributed, &mut report);
    compare_elided(&parent, &candidate, &clock, &attributed, &mut report);
    compare_parity(&parent, &candidate, &policy.required_oracles, &mut report, &mut vacuous);
    report.unattributed = unattributed_crate_caps(&parent, &attributions, &judged);
    report.side_summaries(&parent, &candidate);
    detailed_summaries(&parent, &candidate, &judged, &mut report);
    let candidate_only = candidate_clock.difference(&parent_clock).collect::<Vec<_>>();
    report.lines.push(format!("clock-stopped functions: {} ({} on the parent, {} on the candidate only); cap-attributed functions: {}",clock.len(),parent_clock.len(),candidate_only.len(),attributed.len()));
    for function in candidate_only {
        report.lines.push(format!("  CANDIDATE-CLOCK\t{}", joined(function)));
    }
    for (name, side) in [("parent", &parent), ("candidate", &candidate)] {
        report.malformed.extend(side.malformed.iter().map(|line| format!("{name}\t{line}")));
    }
    report
        .malformed
        .extend(attributions.errors.into_iter().map(|line| format!("--attributed\t{line}")));
    report.diagnostics(true);
    if !report.malformed.is_empty() {
        report.conclude(
            ComparisonOutcome::CouldNotRun,
            "ELIDE AUDIT (L4): COULD NOT RUN — malformed audit rows",
        );
    } else if !report.unattributed.is_empty() {
        report.conclude(ComparisonOutcome::CouldNotRun,format!("ELIDE AUDIT (L4): COULD NOT RUN — {} crate-level hit(s) of a deleted cap site no --attributed line names (read the unit and attribute them)",report.unattributed.len()));
    } else if !report.violations.is_empty() {
        report.conclude(
            ComparisonOutcome::Violation,
            format!("ELIDE AUDIT (L4): {} violation(s)", report.violations.len()),
        );
    } else {
        if parent.elided.is_empty() {
            vacuous.push("the parent elided no check".into());
        }
        if parent.verdict_rows == 0 || candidate.verdict_rows == 0 {
            vacuous.push("a side recorded no VERDICT row".into());
        }
        if parent.rowdigest_rows == 0 || candidate.rowdigest_rows == 0 {
            vacuous.push("a side recorded no ROWDIGEST row".into());
        }
        if vacuous.is_empty() {
            report.conclude(ComparisonOutcome::Pass,"ELIDE AUDIT (L4): verdicts, rows and the elided set identical up to the listed rows; every oracle's PARITY row at mismatches=0");
        } else {
            report.conclude(
                ComparisonOutcome::CouldNotRun,
                format!("ELIDE AUDIT (L4): COULD NOT RUN — vacuous: {}", vacuous.join("; ")),
            );
        }
    }
    report
}

pub(super) fn cap_attributed(
    parent: &Audit,
    attributions: &Attributions,
    judged: &BTreeSet<String>,
) -> Attributed {
    let mut attributed = BTreeMap::<Function, BTreeSet<String>>::new();
    for (function, sites) in &parent.caps {
        if is_crate_level(function) {
            continue;
        }
        for site in
            sites.keys().filter(|site| judged.contains(*site) && !caps::answer_preserving(site))
        {
            attributed.entry(function.clone()).or_default().insert(site.clone());
        }
    }
    for (function, sites) in &attributions.functions {
        for site in
            sites.iter().filter(|site| judged.contains(*site) && !caps::answer_preserving(site))
        {
            attributed.entry(function.clone()).or_default().insert(site.clone());
        }
    }
    attributed
        .into_iter()
        .filter(|(_, sites)| !sites.is_empty())
        .map(|(function, sites)| (function, sites.into_iter().collect()))
        .collect()
}

pub(super) fn unattributed_crate_caps(
    parent: &Audit,
    attributions: &Attributions,
    judged: &BTreeSet<String>,
) -> Vec<String> {
    let mut missing = Vec::new();
    for (function, sites) in &parent.caps {
        if !is_crate_level(function) {
            continue;
        }
        for (site, count) in sites {
            let named =
                [function[0].clone(), function[1].clone(), function[2].clone(), site.clone()];
            if judged.contains(site)
                && !caps::answer_preserving(site)
                && !attributions.named.contains(&named)
            {
                missing.push(format!("{}\t{site}\t({count} hit(s))", joined(function)));
            }
        }
    }
    missing
}

pub(super) fn candidate_deleted_caps(candidate: &Audit, judged: &BTreeSet<String>) -> Vec<String> {
    let mut found = Vec::new();
    for (function, sites) in &candidate.caps {
        for (site, count) in sites {
            if judged.contains(site) && !caps::moved(site) {
                found.push(format!(
                    "candidate still refuses at a deleted cap site ({} {site}, {count} hit(s))\t{}",
                    caps::site_commit(site).expect("validated cap"),
                    joined(function)
                ));
            }
        }
    }
    found
}

fn judge(
    function: &Function,
    clock: &BTreeSet<Function>,
    attributed: &Attributed,
) -> Option<String> {
    if clock.contains(function) {
        return Some("clock-stopped".into());
    }
    attributed.get(function).map(|sites| format!("cap-attributed ({})", site_labels(sites)))
}

pub(super) fn site_labels(sites: &[String]) -> String {
    sites
        .iter()
        .map(|site| format!("{} {site}", caps::site_commit(site).expect("validated cap")))
        .collect::<Vec<_>>()
        .join(", ")
}

fn compare_verdicts(
    parent: &Audit,
    candidate: &Audit,
    clock: &BTreeSet<Function>,
    attributed: &Attributed,
    report: &mut ComparisonReport,
) {
    let keys = parent.verdicts.keys().chain(candidate.verdicts.keys()).collect::<BTreeSet<_>>();
    let empty = Counter::new();
    for key in keys {
        let before = parent.verdicts.get(key).unwrap_or(&empty);
        let after = candidate.verdicts.get(key).unwrap_or(&empty);
        if before == after {
            continue;
        }
        let detail = format!("{} -> {}", verdicts(before), verdicts(after));
        if let Some(why) = judge(&function_of(key), clock, attributed) {
            report.listed.push(format!("verdict {why}\t{}\t{detail}", joined(key)));
        } else {
            report.violations.push(format!("verdict moved\t{}\t{detail}", joined(key)));
        }
    }
}

fn compare_rows(
    parent: &Audit,
    candidate: &Audit,
    clock: &BTreeSet<Function>,
    attributed: &Attributed,
    report: &mut ComparisonReport,
) {
    let functions =
        parent.rowdigests.keys().chain(candidate.rowdigests.keys()).collect::<BTreeSet<_>>();
    let empty = Counter::new();
    for function in functions {
        let before = parent.rowdigests.get(function).unwrap_or(&empty);
        let after = candidate.rowdigests.get(function).unwrap_or(&empty);
        if before == after {
            continue;
        }
        let gone = subtract(before, after);
        let new = subtract(after, before);
        let mut shown = Vec::new();
        for (sign, rows) in [("-", &gone), ("+", &new)] {
            shown.extend(
                rows.iter()
                    .flat_map(|((kind, location, digest), count)| {
                        std::iter::repeat_n(format!("{sign}{kind} {location} {digest}"), *count)
                    })
                    .take(3),
            );
        }
        let detail = format!(
            "{} parent-only, {} candidate-only: {}",
            sum(&gone),
            sum(&new),
            shown.join("; ")
        );
        if let Some(why) = judge(function, clock, attributed) {
            report.listed.push(format!("rows {why}\t{}\t{detail}", joined(function)));
        } else {
            report.violations.push(format!("rows moved\t{}\t{detail}", joined(function)));
        }
    }
}

fn compare_elided(
    parent: &Audit,
    candidate: &Audit,
    clock: &BTreeSet<Function>,
    attributed: &Attributed,
    report: &mut ComparisonReport,
) {
    let mut parent_kept = parent.kept.clone();
    let mut candidate_kept = candidate.kept.clone();
    for (label, ours, theirs, their_kept) in [
        ("elided by the parent only", &parent.elided, &candidate.elided, &mut candidate_kept),
        ("elided by the candidate only", &candidate.elided, &parent.elided, &mut parent_kept),
    ] {
        for (row, count) in subtract(ours, theirs) {
            let function = function_of(&row);
            let key = identity(&function, [row.last().expect("elided key").clone()]);
            for _ in 0..count {
                let reason = pop_worst(their_kept.entry(key.clone()).or_default());
                let line = joined(&row);
                if reason.as_deref().is_some_and(|reason| VERDICT_GATES.contains(&reason))
                    && clock.contains(&function)
                {
                    report.listed.push(format!(
                        "{label}: verdict clock-stopped ({})\t{line}",
                        reason.as_deref().unwrap()
                    ));
                } else if attributed.contains_key(&function) {
                    report.listed.push(format!(
                        "{label}: {}\t{line}",
                        judge(&function, &BTreeSet::new(), attributed).unwrap()
                    ));
                } else {
                    report.violations.push(format!(
                        "{label} (other side {})\t{line}",
                        reason.as_deref().unwrap_or("no disposition")
                    ));
                }
            }
        }
    }
}

fn compare_parity(
    parent: &Audit,
    candidate: &Audit,
    oracles: &[String],
    report: &mut ComparisonReport,
    vacuous: &mut Vec<String>,
) {
    for (name, side) in [("parent", parent), ("candidate", candidate)] {
        for parity in &side.parity {
            if parity.mismatches == 0 {
                continue;
            }
            let line = format!(
                "({name}, {})\t{}\trows={} mismatches={}\tcorpus {}",
                parity.oracle,
                joined(&parity.function),
                parity.rows,
                parity.mismatches,
                parity.corpus
            );
            if parity.oracle == "identity-scope" {
                report.listed.push(format!("unjudged binding {line}"));
            } else {
                report.violations.push(format!("parity mismatch {line}"));
            }
        }
    }
    for oracle in oracles {
        for corpus in &candidate.corpora {
            if !candidate
                .parity
                .iter()
                .any(|row| row.corpus == *corpus && row.oracle == *oracle && row.rows > 0)
            {
                vacuous.push(format!("oracle `{oracle}` has rows=0 on corpus {corpus}"));
            }
        }
    }
}

fn detailed_summaries(
    parent: &Audit,
    candidate: &Audit,
    judged: &BTreeSet<String>,
    report: &mut ComparisonReport,
) {
    for (name, side) in [("parent", parent), ("candidate", candidate)] {
        let unreproducible = side
            .stops
            .values()
            .flat_map(|entries| entries.iter())
            .filter(|(_, cause)| !reproducible(cause))
            .count();
        let crate_stops = side
            .stops
            .iter()
            .filter(|(function, _)| is_crate_level(*function))
            .flat_map(|(_, entries)| entries.iter())
            .filter(|(_, cause)| !reproducible(cause))
            .count();
        let certify = side.certify_stops.values().map(Vec::len).sum::<usize>();
        let mut groups = Counter::new();
        let mut crate_caps = 0;
        for (function, sites) in &side.caps {
            for (site, count) in sites {
                *groups
                    .entry(caps::site_commit(site).expect("validated cap").to_owned())
                    .or_default() += count;
                if is_crate_level(function) {
                    crate_caps += count;
                }
            }
        }
        let mut parity = BTreeMap::<String, (u128, u128)>::new();
        for row in &side.parity {
            let counts = parity.entry(row.oracle.clone()).or_default();
            counts.0 += u128::from(row.rows);
            counts.1 += u128::from(row.mismatches);
        }
        let parity = format!(
            "{{{}}}",
            parity
                .iter()
                .map(|(oracle, (rows, mismatches))| format!(
                    "{}: {}",
                    py_string(oracle),
                    py_string(&format!("rows={rows} mismatches={mismatches}"))
                ))
                .collect::<Vec<_>>()
                .join(", ")
        );
        let corpora = format!(
            "[{}]",
            side.corpora.iter().map(|value| py_string(value)).collect::<Vec<_>>().join(", ")
        );
        report.lines.push(format!("{name:9}: {} rowdigest rows in {} functions; {unreproducible} unreproducible STOP rows ({crate_stops} crate-level); {certify} CERTIFY-STOP rows; CAP hits by commit {} ({crate_caps} crate-level); PARITY {parity}; corpora {corpora}",side.rowdigest_rows,side.rowdigests.len(),string_counter(&groups)));
    }
    if !judged.is_empty() {
        report.lines.push(format!("deleted cap sites judged: {}", judged.len()));
    }
}
