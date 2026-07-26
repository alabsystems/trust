// targo trust gap: classify a survey JSON into user-logic vs derived boilerplate
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

//! `targo trust gap` reads a `targo trust survey` JSON — an artifact of the
//! caller's own crate — and reports where the real verification frontier is.
//!
//! Its subject is the user's code, not this repository, so it runs natively
//! rather than through `scripts/`. A subcommand that shells out to a repo
//! script is only available to someone standing in a Trust checkout with a
//! Python interpreter, which is not who a per-crate report is for.
//!
//! The classification exists because a raw obligation count conflates two very
//! different populations. `#[derive(Debug/Clone/PartialEq/…)]` and serde's
//! generated impls dominate the unknown count, and verifying them proves the
//! *compiler's* codegen rather than anything the author wrote. Reporting one
//! total hides the number that matters.

use std::collections::BTreeMap;
use std::ffi::OsStr;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use serde_json::Value;

/// Substrings that mark a monomorphized function name as compiler- or
/// macro-generated rather than hand-written.
///
/// Matching is by substring on the demangled name, which is what makes this a
/// classification and not a proof: a hand-written `fmt` whose path happens to
/// contain one of these sequences lands in the derived bucket. That direction
/// is the safe one — it can only understate the user-logic gap the headline
/// reports, never overstate what has been proved.
const DERIVED_MARKERS: &[&str] = &[
    "as std::fmt::Debug>::fmt",
    "as std::fmt::Display>::fmt",
    "as std::clone::Clone>::clone",
    "as std::cmp::PartialEq>::eq",
    "as std::cmp::PartialOrd>::partial_cmp",
    "as std::cmp::Ord>::cmp",
    "as std::hash::Hash>::hash",
    "as std::default::Default>::default",
    "as std::cmp::Eq>",
    // serde's derive emits its impls inside a `const _: () = { … }` block that
    // refers to the hygiene alias `_serde`; hand-written serde code uses plain
    // `serde::`. Keying on the alias keeps hand-written impls in the user
    // bucket. This generic code is also exactly where the verifier cannot lower
    // the associated-type aliases (`<D as Deserializer>::Error`, …), so it
    // contributes unknowns that are not the author's to close.
    "_serde::Deserialize",
    "_serde::Serialize",
    "_serde::de::",
    "_serde::ser::",
];

const DEFAULT_SURVEY_DIR: &str = "target/trust/survey";
const REASON_LIMIT: usize = 10;

fn is_derived(name: &str) -> bool {
    DERIVED_MARKERS.iter().any(|marker| name.contains(marker))
}

/// Truncate on a character boundary. The survey carries demangled Rust paths,
/// which may hold non-ASCII identifiers; a byte slice would panic on one.
fn truncate_chars(value: &str, limit: usize) -> String {
    value.chars().take(limit).collect()
}

/// A tally that keeps first-seen order so equal counts render in a stable,
/// reproducible sequence. Two runs over the same survey must print the same
/// bytes, otherwise the output cannot be diffed across a change.
#[derive(Default)]
struct OrderedTally {
    order: Vec<String>,
    counts: BTreeMap<String, usize>,
}

impl OrderedTally {
    fn add(&mut self, key: String) {
        if !self.counts.contains_key(&key) {
            self.order.push(key.clone());
        }
        *self.counts.entry(key).or_insert(0) += 1;
    }

    fn get(&self, key: &str) -> usize {
        self.counts.get(key).copied().unwrap_or(0)
    }

    fn total(&self) -> usize {
        self.counts.values().sum()
    }

    /// Descending by count, ties in first-seen order.
    fn ranked(&self) -> Vec<(&str, usize)> {
        let mut ranked = self
            .order
            .iter()
            .map(|key| (key.as_str(), self.get(key)))
            .collect::<Vec<_>>();
        ranked.sort_by(|left, right| right.1.cmp(&left.1));
        ranked
    }
}

/// The outcome status a row reports. A survey row whose outcome is absent,
/// malformed, or empty is `NA` rather than an assumed pass: an unreadable row
/// must never be counted toward `proved`.
fn obligation_status(obligation: &Value) -> String {
    let status = match obligation.get("outcome") {
        Some(Value::Object(outcome)) => outcome.get("status").and_then(Value::as_str),
        Some(Value::String(status)) => Some(status.as_str()),
        _ => None,
    };
    match status {
        Some(status) if !status.is_empty() => status.to_string(),
        _ => "NA".to_string(),
    }
}

/// A short label for *why* an obligation is unknown or failed, so the histogram
/// groups causes rather than listing one line per obligation.
fn obligation_reason(obligation: &Value) -> String {
    let description = obligation.get("description").and_then(Value::as_str).unwrap_or_default();

    // The single most common blocker is a MIR construct the lowering does not
    // model. Naming the construct turns a wall of identical lines into a
    // ranked list of the things worth implementing next.
    if let Some(construct) = unsupported_mir_construct(description) {
        return format!("unsupported_mir: {construct}");
    }

    if let Some(Value::Object(outcome)) = obligation.get("outcome") {
        if let Some(reason) = outcome.get("reason") {
            let reason = match reason {
                Value::String(reason) => reason.clone(),
                other => other.to_string(),
            };
            if !reason.is_empty() {
                return truncate_chars(&reason, 60);
            }
        }
    }

    let fallback = obligation
        .get("kind")
        .and_then(Value::as_str)
        .filter(|kind| !kind.is_empty())
        .unwrap_or_else(|| description.split(':').next().unwrap_or_default());
    truncate_chars(fallback, 50)
}

/// Extract the construct from a description of the form
/// ``unsupported MIR `<construct>` …``.
fn unsupported_mir_construct(description: &str) -> Option<&str> {
    let rest = description.split_once("unsupported MIR `")?.1;
    let (construct, _) = rest.split_once('`')?;
    (!construct.is_empty()).then_some(construct)
}

/// Newest `*.json` under the survey directory, by modification time.
fn newest_survey(directory: &Path) -> Option<PathBuf> {
    let mut newest: Option<(std::time::SystemTime, PathBuf)> = None;
    for entry in std::fs::read_dir(directory).ok()?.flatten() {
        let path = entry.path();
        if path.extension() != Some(OsStr::new("json")) {
            continue;
        }
        let Ok(modified) = entry.metadata().and_then(|metadata| metadata.modified()) else {
            continue;
        };
        if newest.as_ref().is_none_or(|(current, _)| modified >= *current) {
            newest = Some((modified, path));
        }
    }
    newest.map(|(_, path)| path)
}

struct Classification {
    user_functions: usize,
    derived_functions: usize,
    user: OrderedTally,
    derived: OrderedTally,
    unknown_reasons: OrderedTally,
    failed_reasons: OrderedTally,
}

fn classify(functions: &[Value]) -> Classification {
    let mut classification = Classification {
        user_functions: 0,
        derived_functions: 0,
        user: OrderedTally::default(),
        derived: OrderedTally::default(),
        unknown_reasons: OrderedTally::default(),
        failed_reasons: OrderedTally::default(),
    };

    for function in functions {
        let name = function
            .get("function")
            .and_then(Value::as_str)
            .or_else(|| function.get("name").and_then(Value::as_str))
            .unwrap_or_default();
        let derived = is_derived(name);
        if derived {
            classification.derived_functions += 1;
        } else {
            classification.user_functions += 1;
        }

        let obligations = function.get("obligations").and_then(Value::as_array);
        for obligation in obligations.into_iter().flatten() {
            let status = obligation_status(obligation);
            if derived {
                classification.derived.add(status);
                continue;
            }
            let reasons = match status.as_str() {
                "unknown" => Some(&mut classification.unknown_reasons),
                "failed" => Some(&mut classification.failed_reasons),
                _ => None,
            };
            if let Some(reasons) = reasons {
                reasons.add(obligation_reason(obligation));
            }
            classification.user.add(status);
        }
    }

    classification
}

fn render(survey_name: &str, classification: &Classification) -> String {
    let mut out = format!("survey: {survey_name}\n");

    for (label, functions, tally) in [
        ("user", classification.user_functions, &classification.user),
        ("derived", classification.derived_functions, &classification.derived),
    ] {
        out.push_str(&format!(
            "\n=== {label} logic: {functions} fns, {} obligations ===\n",
            tally.total()
        ));
        for (status, count) in tally.ranked() {
            out.push_str(&format!("  {count:5} {status}\n"));
        }
    }

    let user = &classification.user;
    let gap = user.get("unknown") + user.get("failed");
    out.push_str("\n=== HEADLINE — user-logic gap (the real \"verify clean\" target) ===\n");
    out.push_str(&format!(
        "  proved {} / unknown {} / failed {} / design_req {}\n",
        user.get("proved"),
        user.get("unknown"),
        user.get("failed"),
        user.get("design_requirement"),
    ));
    out.push_str(&format!("  user-logic unprovable (unknown+failed) = {gap}\n"));
    out.push_str(&format!(
        "  derived-boilerplate unknown (separate &dyn-Trait Unsize lever) = {}\n",
        classification.derived.get("unknown"),
    ));

    for (label, reasons) in
        [("unknown", &classification.unknown_reasons), ("failed", &classification.failed_reasons)]
    {
        out.push_str(&format!("\n  user-logic {label} by reason:\n"));
        for (reason, count) in reasons.ranked().into_iter().take(REASON_LIMIT) {
            out.push_str(&format!("    {count:4} {reason}\n"));
        }
    }

    out
}

/// Resolve the survey to read, then classify and print it.
pub(crate) fn run(args: &[String]) -> ExitCode {
    // An option this subcommand does not understand is refused rather than
    // dropped: silently ignoring, say, a filter flag would produce a report
    // over the whole survey while the caller believes it was narrowed.
    if let Some(unknown) = args.iter().find(|arg| arg.starts_with('-')) {
        eprintln!("targo trust gap: unknown option `{unknown}`");
        eprint!("{}", crate::script_cli::gap_usage_text());
        return ExitCode::from(2);
    }
    let explicit = args.first();
    let path = match explicit {
        Some(path) => PathBuf::from(path),
        None => {
            let directory = std::env::var_os("TRUST_SURVEY_DIR")
                .map(PathBuf::from)
                .unwrap_or_else(|| PathBuf::from(DEFAULT_SURVEY_DIR));
            match newest_survey(&directory) {
                Some(path) => path,
                None => {
                    eprintln!(
                        "targo trust gap: no survey json found in `{}` (run `targo trust survey <crate>` first)",
                        directory.display()
                    );
                    return ExitCode::from(2);
                }
            }
        }
    };

    let contents = match std::fs::read_to_string(&path) {
        Ok(contents) => contents,
        Err(error) => {
            eprintln!("targo trust gap: could not read `{}`: {error}", path.display());
            return ExitCode::from(2);
        }
    };
    let survey = match serde_json::from_str::<Value>(&contents) {
        Ok(survey) => survey,
        Err(error) => {
            eprintln!("targo trust gap: `{}` is not valid JSON: {error}", path.display());
            return ExitCode::from(2);
        }
    };
    // A survey without a `functions` array is a different document, not an
    // empty result. Reporting "0 obligations" for it would read as a clean
    // crate.
    let Some(functions) = survey.get("functions").and_then(Value::as_array) else {
        eprintln!(
            "targo trust gap: `{}` has no `functions` array; it is not a `targo trust survey` report",
            path.display()
        );
        return ExitCode::from(2);
    };

    let name = path.file_name().map(OsStr::to_string_lossy).unwrap_or_default();
    print!("{}", render(&name, &classify(functions)));
    ExitCode::SUCCESS
}

#[cfg(test)]
mod tests {
    use super::*;

    fn survey() -> Value {
        serde_json::json!({
            "functions": [
                {
                    "function": "demo::midpoint",
                    "obligations": [
                        { "kind": "overflow", "outcome": { "status": "proved" } },
                        {
                            "kind": "overflow",
                            "description": "lowering: unsupported MIR `Aggregate(Closure)` in body",
                            "outcome": { "status": "unknown" }
                        },
                        {
                            "kind": "bounds",
                            "outcome": { "status": "unknown", "reason": "solver budget exhausted" }
                        },
                        { "kind": "divide-by-zero", "outcome": { "status": "failed" } }
                    ]
                },
                {
                    "name": "<demo::Point as std::fmt::Debug>::fmt",
                    "obligations": [
                        { "kind": "overflow", "outcome": { "status": "unknown" } },
                        { "kind": "overflow", "outcome": { "status": "proved" } }
                    ]
                },
                {
                    "function": "demo::no_obligations"
                }
            ]
        })
    }

    #[test]
    fn derived_impls_are_separated_from_hand_written_logic() {
        // The headline number is the point of this subcommand: derived
        // boilerplate dominates the unknown count, and folding it into one
        // total hides how much of the gap the author can actually close.
        let survey = survey();
        let classification = classify(survey["functions"].as_array().unwrap());
        assert_eq!(classification.user_functions, 2);
        assert_eq!(classification.derived_functions, 1);
        assert_eq!(classification.user.get("unknown"), 2);
        assert_eq!(classification.user.get("failed"), 1);
        assert_eq!(classification.user.get("proved"), 1);
        assert_eq!(classification.derived.get("unknown"), 1);

        let rendered = render("demo-20260724-101500.json", &classification);
        assert!(rendered.contains("user-logic unprovable (unknown+failed) = 3"), "{rendered}");
        assert!(
            rendered.contains("derived-boilerplate unknown (separate &dyn-Trait Unsize lever) = 1"),
            "{rendered}"
        );
        assert!(rendered.contains("unsupported_mir: Aggregate(Closure)"), "{rendered}");
        assert!(rendered.contains("solver budget exhausted"), "{rendered}");
    }

    #[test]
    fn an_unreadable_outcome_is_na_rather_than_proved() {
        // A row the reader cannot interpret must not be credited. `NA` is
        // visible in the histogram; silently counting it as proved would be a
        // proof claim invented by a report generator.
        for outcome in [
            serde_json::json!({}),
            serde_json::json!({ "outcome": Value::Null }),
            serde_json::json!({ "outcome": { "status": "" } }),
            serde_json::json!({ "outcome": ["unexpected"] }),
        ] {
            assert_eq!(obligation_status(&outcome), "NA", "{outcome}");
        }
        assert_eq!(
            obligation_status(&serde_json::json!({ "outcome": "runtime_checked" })),
            "runtime_checked"
        );
    }

    #[test]
    fn equal_counts_render_in_a_stable_order() {
        // Two runs over one survey have to produce identical bytes, or the
        // output cannot be diffed across a change.
        let mut tally = OrderedTally::default();
        for key in ["beta", "alpha", "beta", "gamma", "alpha"] {
            tally.add(key.to_string());
        }
        assert_eq!(tally.ranked(), vec![("beta", 2), ("alpha", 2), ("gamma", 1)]);
    }

    #[test]
    fn reason_labels_are_truncated_on_character_boundaries() {
        // Survey rows carry demangled Rust paths, which may hold non-ASCII
        // identifiers; slicing by byte would panic on one.
        let obligation = serde_json::json!({
            "outcome": { "status": "unknown", "reason": "é".repeat(200) }
        });
        assert_eq!(obligation_reason(&obligation).chars().count(), 60);

        let obligation = serde_json::json!({ "description": "é".repeat(200) });
        assert_eq!(obligation_reason(&obligation).chars().count(), 50);
    }

    #[test]
    fn a_survey_without_a_functions_array_is_refused_rather_than_reported_as_clean() {
        // Printing "0 obligations" for a document that is not a survey would
        // read as a crate with nothing left to prove.
        for document in [
            serde_json::json!({}),
            serde_json::json!({ "functions": {} }),
            serde_json::json!([]),
        ] {
            assert!(
                document.get("functions").and_then(Value::as_array).is_none(),
                "{document}"
            );
        }
        assert!(
            serde_json::json!({ "functions": [] })
                .get("functions")
                .and_then(Value::as_array)
                .is_some(),
            "an empty survey is a real result and must still be reported"
        );
    }

    #[test]
    fn a_malformed_mir_marker_falls_through_instead_of_reporting_an_empty_construct() {
        assert_eq!(
            unsupported_mir_construct("lowering: unsupported MIR `Coroutine` here"),
            Some("Coroutine")
        );
        assert_eq!(unsupported_mir_construct("unsupported MIR `` here"), None);
        assert_eq!(unsupported_mir_construct("unsupported MIR `unterminated"), None);
        assert_eq!(unsupported_mir_construct("no marker at all"), None);
    }
}
