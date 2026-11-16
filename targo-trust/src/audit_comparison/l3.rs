//! L3's exact disposition multiset and explicitly listed origin transitions.

use super::parse::Audit;
use super::*;

pub(super) fn compare(pair: AuditInputPair<'_>) -> ComparisonReport {
    let (parent, candidate) = match Audit::read(pair.parent, false)
        .and_then(|parent| Audit::read(pair.candidate, false).map(|candidate| (parent, candidate)))
    {
        Ok(pair) => pair,
        Err(error) => return ComparisonReport::could_not_run(error.to_string()),
    };
    let mut report = ComparisonReport::new();
    let clock = compare_verdicts(&parent, &candidate, &mut report);
    compare_elided(&parent, &candidate, &clock, &mut report);
    report.side_summaries(&parent, &candidate);
    for (name, side) in [("parent", &parent), ("candidate", &candidate)] {
        let details = side
            .ignored
            .iter()
            .map(|(kind, count)| format!("{kind} {count}"))
            .collect::<Vec<_>>()
            .join(", ");
        let suffix = if details.is_empty() { String::new() } else { format!(" ({details})") };
        report
            .lines
            .push(format!("{name:9}: {} L4 rows ignored in L3 mode{suffix}", sum(&side.ignored)));
    }
    let truncated = parent
        .origins
        .iter()
        .filter(|(function, states)| {
            states.get("complete").copied().unwrap_or(0) > 0
                && candidate
                    .origins
                    .get(*function)
                    .and_then(|states| states.get("complete"))
                    .copied()
                    .unwrap_or(0)
                    == 0
        })
        .map(|(function, _)| function)
        .collect::<Vec<_>>();
    if !truncated.is_empty() {
        report.lines.push(format!(
            "functions with a complete parent table and no complete candidate table: {}",
            truncated.len()
        ));
        for function in truncated {
            report.lines.push(format!(
                "  TABLE\t{}\tcandidate {}",
                joined(function),
                candidate.table_states(function)
            ));
        }
    }
    for (name, side) in [("parent", &parent), ("candidate", &candidate)] {
        report.malformed.extend(side.malformed.iter().map(|line| format!("{name}\t{line}")));
    }
    report.diagnostics(true);
    if !report.malformed.is_empty() {
        report.conclude(
            ComparisonOutcome::CouldNotRun,
            "ELIDE AUDIT: COULD NOT RUN — malformed audit rows",
        );
    } else if !report.violations.is_empty() {
        report.conclude(
            ComparisonOutcome::Violation,
            format!("ELIDE AUDIT: {} violation(s)", report.violations.len()),
        );
    } else {
        let mut vacuous = Vec::new();
        if parent.elided.is_empty() {
            vacuous.push("the parent elided no check");
        }
        if !candidate
            .origins
            .values()
            .any(|states| states.get("complete").copied().unwrap_or(0) > 0)
        {
            vacuous.push("the candidate built no complete origin table");
        }
        if parent.verdict_rows == 0 || candidate.verdict_rows == 0 {
            vacuous.push("a side recorded no verdict row");
        }
        if vacuous.is_empty() {
            report.conclude(ComparisonOutcome::Pass,"ELIDE AUDIT: verdict vectors identical up to the listed clock-stopped rows; elided set equal up to the listed rows");
        } else {
            report.conclude(
                ComparisonOutcome::CouldNotRun,
                format!("ELIDE AUDIT: COULD NOT RUN — vacuous: {}", vacuous.join("; ")),
            );
        }
    }
    report
}

fn compare_verdicts(
    parent: &Audit,
    candidate: &Audit,
    report: &mut ComparisonReport,
) -> BTreeSet<Function> {
    let mut unreproducible = BTreeSet::new();
    for side in [parent, candidate] {
        for (key, entries) in &side.verdicts {
            if entries.keys().any(|(_, stop)| !reproducible(stop)) {
                unreproducible.insert(function_of(key));
            }
        }
    }
    let mut clock = BTreeSet::new();
    let keys = parent.verdicts.keys().chain(candidate.verdicts.keys()).collect::<BTreeSet<_>>();
    let empty = Counter::new();
    for key in keys {
        let before = parent.verdicts.get(key).unwrap_or(&empty);
        let after = candidate.verdicts.get(key).unwrap_or(&empty);
        if before == after {
            continue;
        }
        let function = function_of(key);
        let changed = subtract(before, after)
            .into_keys()
            .chain(subtract(after, before).into_keys())
            .any(|(_, stop)| !reproducible(&stop));
        let detail = format!("{} -> {}", verdicts(before), verdicts(after));
        if changed
            || ((before.is_empty() || after.is_empty()) && unreproducible.contains(&function))
        {
            clock.insert(function);
            report.listed.push(format!("verdict clock-stopped\t{}\t{detail}", joined(key)));
        } else {
            report.violations.push(format!("verdict moved\t{}\t{detail}", joined(key)));
        }
    }
    clock
}

fn compare_elided(
    parent: &Audit,
    candidate: &Audit,
    clock: &BTreeSet<Function>,
    report: &mut ComparisonReport,
) {
    let mut parent_kept = parent.kept.clone();
    let mut candidate_kept = candidate.kept.clone();
    for (row, count) in subtract(&parent.elided, &candidate.elided) {
        let function = function_of(&row);
        let key = identity(&function, [row.last().expect("elided key").clone()]);
        for _ in 0..count {
            let reason = pop_worst(candidate_kept.entry(key.clone()).or_default());
            let line = joined(&row);
            if reason.as_deref() == Some("statement") {
                report.listed.push(format!("kept by the candidate: statement-only origin\t{line}"));
            } else if reason.as_deref().is_some_and(|reason| VERDICT_GATES.contains(&reason))
                && clock.contains(&function)
            {
                report.listed.push(format!(
                    "kept by the candidate: verdict clock-stopped ({})\t{line}",
                    reason.as_deref().unwrap()
                ));
            } else {
                report.violations.push(format!(
                    "kept by the candidate ({}; candidate table {}), elided by the parent\t{line}",
                    reason.as_deref().unwrap_or("no disposition"),
                    candidate.table_states(&function)
                ));
            }
        }
    }
    for (row, count) in subtract(&candidate.elided, &parent.elided) {
        let function = function_of(&row);
        let key = identity(&function, [row.last().expect("elided key").clone()]);
        for _ in 0..count {
            let reason = pop_worst(parent_kept.entry(key.clone()).or_default());
            let line = joined(&row);
            let states = parent.origins.get(&function);
            if reason.as_deref() == Some("absent")
                && states.and_then(|states| states.get("refused")).copied().unwrap_or(0) > 0
            {
                report.listed.push(format!("parent replay refused\t{line}"));
            } else if reason.as_deref() == Some("absent")
                && states.and_then(|states| states.get("complete")).copied().unwrap_or(0) > 0
            {
                report.listed.push(format!("parent table lacked the key (C05-GATE-1)\t{line}"));
            } else if (reason.is_none()
                || reason.as_deref().is_some_and(|reason| VERDICT_GATES.contains(&reason)))
                && clock.contains(&function)
            {
                report.listed.push(format!(
                    "parent verdict clock-stopped ({})\t{line}",
                    reason.as_deref().unwrap_or("no disposition")
                ));
            } else {
                report.violations.push(format!(
                    "elided by the candidate only (parent {}; parent table {})\t{line}",
                    reason.as_deref().unwrap_or("no disposition"),
                    parent.table_states(&function)
                ));
            }
        }
    }
}
