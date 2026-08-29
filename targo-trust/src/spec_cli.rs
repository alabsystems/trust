// targo trust spec: the compiler-authoritative spec-goal surface (v6/D1).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

//! `targo trust spec --emit clean [-p <pkg>]`
//!
//! Standing ruling v6/D1: this subcommand prints "the Clean goal the compiler
//! actually elaborated and the kernel actually checked". An offline
//! re-elaboration in targo-trust was considered and REJECTED — it can print a
//! different proposition than the kernel saw, precisely when someone is
//! debugging a failure. So this module never elaborates anything. It:
//!
//! 1. provisions a fresh, empty session directory (so no stale artifact from
//!    an earlier run can ever satisfy the read);
//! 2. drives a `targo trust check`-equivalent verified compilation with the
//!    emission knob (`--spec-emit-dir <dir>`, which the pipeline transports to
//!    the compiler — `TRUST_SPEC_EMIT_DIR` in Cargo crate mode, the typed
//!    `-Ztrust-dump=spec-clean:` sink for a direct trustc invocation);
//! 3. reads back the artifact the compiler session sealed, validates its
//!    format version and its seal, and prints the goals.
//!
//! FAIL-CLOSED: no artifact, an unknown format version, or a torn artifact
//! (missing seal / seal count mismatch) is a REFUSAL carrying the fix options
//! (v7/D3), never an excuse to re-derive the goals locally. The goals print
//! even when the verified build itself failed — that is the debugging case
//! the ruling exists for — but the failing exit status is preserved.

use std::path::Path;
use std::process::ExitCode;

use crate::types::Subcommand;

/// Artifact format tag; every line of the compiler-written JSONL carries it.
/// Mirror of `rustc_mir_transform::trust_spec_emit::SPEC_CLEAN_FORMAT`.
const SPEC_CLEAN_FORMAT: &str = "trust-spec-clean";

/// The one artifact version this reader understands. An unknown version is a
/// refusal, not a best-effort parse.
const SPEC_CLEAN_SUPPORTED_VERSION: u64 = 1;

/// Per-unit artifact filename suffix.
const SPEC_CLEAN_FILE_SUFFIX: &str = ".spec-clean.jsonl";

/// Parsed `targo trust spec` arguments.
#[derive(Debug)]
struct SpecArgs {
    /// Raw machine-readable row output instead of the human rendering.
    json: bool,
    /// Everything forwarded to the underlying verified check.
    forwarded: Vec<String>,
}

/// Parse the spec surface. `--emit clean` is MANDATORY and `clean` is the only
/// supported value: the subcommand exists to print kernel-checked Clean goals,
/// and refusing anything else with the options listed is the v7/D3 contract.
fn parse_spec_args(args: &[String]) -> Result<SpecArgs, String> {
    let mut emit: Option<String> = None;
    let mut json = false;
    let mut forwarded = Vec::new();
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--emit" => {
                i += 1;
                let value = args.get(i).ok_or_else(|| {
                    "targo trust spec: `--emit` requires a value; the supported surface is \
                     `--emit clean`"
                        .to_string()
                })?;
                emit = Some(value.clone());
            }
            s if s.starts_with("--emit=") => {
                emit = Some(s["--emit=".len()..].to_string());
            }
            "--json" => {
                json = true;
            }
            s if s == "--spec-emit-dir" || s.starts_with("--spec-emit-dir=") => {
                return Err(
                    "targo trust spec: `--spec-emit-dir` is provisioned by the subcommand itself \
                     (a fresh directory per run, so a stale artifact can never satisfy the read). \
                     To keep the raw artifact, run `targo trust check --spec-emit-dir <abs dir>` \
                     and read the *.spec-clean.jsonl files directly."
                        .to_string(),
                );
            }
            _ => forwarded.push(args[i].clone()),
        }
        i += 1;
    }
    match emit.as_deref() {
        Some("clean") => Ok(SpecArgs { json, forwarded }),
        Some(other) => Err(format!(
            "targo trust spec: `--emit {other}` is not a supported goal surface. Options:\n  \
             - `--emit clean` prints the Clean goals the kernel actually graded (the only \
             spec surface today)\n  \
             - for the TrustIr lowering artifact use `--emit=trust-ir` on a direct trustc \
             invocation, or `-Ztrust-dump=ir:<dir>`"
        )),
        None => Err(
            "targo trust spec: `--emit clean` is required — this surface prints the Clean goals \
             the kernel actually checked (v6/D1). Run: `targo trust spec --emit clean [-p <pkg>]`"
                .to_string(),
        ),
    }
}

/// One kernel-graded goal row read back from the artifact.
#[derive(Debug, Clone, PartialEq)]
struct GoalRow {
    krate: String,
    session: String,
    def_path: String,
    origin: String,
    clause: String,
    theorem: String,
    goal_clean: Option<String>,
    elab_error: Option<String>,
    verdict: String,
    detail: Option<String>,
    /// The raw line, for `--json` passthrough (byte-preserving output).
    raw: String,
}

/// One sealed per-unit artifact file.
#[derive(Debug)]
struct UnitArtifact {
    krate: String,
    session: String,
    goals: Vec<GoalRow>,
}

/// Why the artifact read REFUSED. Every variant carries its fix (v7/D3).
#[derive(Debug, PartialEq)]
enum SpecRefusal {
    NoArtifact,
    Malformed { file: String, detail: String },
    UnsupportedVersion { file: String, version: String },
    Unsealed { file: String },
    Torn { file: String, sealed: u64, counted: u64 },
}

impl SpecRefusal {
    fn render(&self) -> String {
        match self {
            SpecRefusal::NoArtifact => "targo trust spec: REFUSED — no compiler spec artifact \
                 was produced by this run.\n\
                 `--emit clean` is compiler-authoritative (v6/D1): it prints only Clean goals a \
                 live kernel session actually graded; it never re-elaborates offline, so with no \
                 session artifact there is nothing it may claim. Causes and fixes:\n  \
                 - the compilation failed before verification ran: fix the build errors reported \
                 above and re-run\n  \
                 - the installed trustc predates the spec-clean emitter: rebuild the toolchain \
                 (`./x.py build`) so trustc understands `-Ztrust-dump=spec-clean:<dir>`\n  \
                 - verification did not run for this invocation (an unverified or compat lane): \
                 run from the verified workspace lane — only an enabled verification walk writes \
                 and seals the artifact"
                .to_string(),
            SpecRefusal::Malformed { file, detail } => format!(
                "targo trust spec: REFUSED — spec artifact `{file}` is not well-formed \
                 ({detail}).\n\
                 The artifact is written only by trustc; a malformed file means a torn write or \
                 an incompatible producer. Fix: re-run `targo trust spec`; if it persists, \
                 rebuild the toolchain so trustc and targo-trust agree on the artifact format"
            ),
            SpecRefusal::UnsupportedVersion { file, version } => format!(
                "targo trust spec: REFUSED — spec artifact `{file}` carries format version \
                 {version}, and this targo-trust understands only version \
                 {SPEC_CLEAN_SUPPORTED_VERSION}.\n\
                 Fix: rebuild targo-trust and trustc from the same tree so the producer and the \
                 reader agree, then re-run"
            ),
            SpecRefusal::Unsealed { file } => format!(
                "targo trust spec: REFUSED — spec artifact `{file}` has no session seal.\n\
                 The seal is written when the verification walk COMPLETES; its absence means the \
                 compiler session died mid-walk (or an incompatible producer wrote the file). \
                 Fix: address the compiler failure reported above and re-run"
            ),
            SpecRefusal::Torn { file, sealed, counted } => format!(
                "targo trust spec: REFUSED — spec artifact `{file}` is torn: the session seal \
                 records {sealed} goal row(s) but the file holds {counted}.\n\
                 Fix: re-run `targo trust spec` (the session directory is provisioned fresh per \
                 run); if it persists, report it — two writers on one session directory is a bug"
            ),
        }
    }
}

fn parse_optional_string(value: &serde_json::Value, key: &str) -> Option<String> {
    value.get(key).and_then(|v| v.as_str()).map(str::to_string)
}

fn parse_required_string(
    value: &serde_json::Value,
    key: &str,
    file: &str,
) -> Result<String, SpecRefusal> {
    value.get(key).and_then(|v| v.as_str()).map(str::to_string).ok_or_else(|| {
        SpecRefusal::Malformed { file: file.to_string(), detail: format!("row missing `{key}`") }
    })
}

/// Parse and validate ONE per-unit artifact file: every line self-describes
/// the format and version, exactly one session seal is present, and the seal's
/// goal count matches the goal rows read.
fn parse_unit_artifact(file_name: &str, contents: &str) -> Result<UnitArtifact, SpecRefusal> {
    let mut goals: Vec<GoalRow> = Vec::new();
    let mut seal: Option<(String, String, u64)> = None;
    for line in contents.lines() {
        if line.trim().is_empty() {
            continue;
        }
        let value: serde_json::Value =
            serde_json::from_str(line).map_err(|error| SpecRefusal::Malformed {
                file: file_name.to_string(),
                detail: format!("invalid JSON line: {error}"),
            })?;
        let format = value.get("format").and_then(|v| v.as_str()).unwrap_or_default();
        if format != SPEC_CLEAN_FORMAT {
            return Err(SpecRefusal::Malformed {
                file: file_name.to_string(),
                detail: format!("unexpected format tag `{format}`"),
            });
        }
        // Version gate BEFORE any row interpretation: unknown versions refuse.
        match value.get("v").and_then(|v| v.as_u64()) {
            Some(SPEC_CLEAN_SUPPORTED_VERSION) => {}
            other => {
                return Err(SpecRefusal::UnsupportedVersion {
                    file: file_name.to_string(),
                    version: other
                        .map(|v| v.to_string())
                        .unwrap_or_else(|| "<non-integer>".to_string()),
                });
            }
        }
        match value.get("row").and_then(|v| v.as_str()) {
            Some("goal") => {
                goals.push(GoalRow {
                    krate: parse_required_string(&value, "crate", file_name)?,
                    session: parse_optional_string(&value, "session").unwrap_or_default(),
                    def_path: parse_required_string(&value, "def_path", file_name)?,
                    origin: parse_required_string(&value, "origin", file_name)?,
                    clause: parse_required_string(&value, "clause", file_name)?,
                    theorem: parse_required_string(&value, "theorem", file_name)?,
                    goal_clean: parse_optional_string(&value, "goal_clean"),
                    elab_error: parse_optional_string(&value, "elab_error"),
                    verdict: parse_required_string(&value, "verdict", file_name)?,
                    detail: parse_optional_string(&value, "detail"),
                    raw: line.to_string(),
                });
            }
            Some("session") => {
                if seal.is_some() {
                    return Err(SpecRefusal::Malformed {
                        file: file_name.to_string(),
                        detail: "more than one session seal".to_string(),
                    });
                }
                let goals_sealed =
                    value.get("goals").and_then(|v| v.as_u64()).ok_or_else(|| {
                        SpecRefusal::Malformed {
                            file: file_name.to_string(),
                            detail: "session seal missing `goals` count".to_string(),
                        }
                    })?;
                seal = Some((
                    parse_required_string(&value, "crate", file_name)?,
                    parse_optional_string(&value, "session").unwrap_or_default(),
                    goals_sealed,
                ));
            }
            other => {
                return Err(SpecRefusal::Malformed {
                    file: file_name.to_string(),
                    detail: format!("unknown row kind {other:?}"),
                });
            }
        }
    }
    let Some((krate, session, sealed)) = seal else {
        return Err(SpecRefusal::Unsealed { file: file_name.to_string() });
    };
    let counted = goals.len() as u64;
    if sealed != counted {
        return Err(SpecRefusal::Torn { file: file_name.to_string(), sealed, counted });
    }
    Ok(UnitArtifact { krate, session, goals })
}

/// Read every sealed per-unit artifact from the session directory. Zero files
/// is the fail-closed `NoArtifact` refusal — this is the property that makes
/// the subcommand a live-session instrument rather than an offline derivation.
fn read_spec_artifacts(dir: &Path) -> Result<Vec<UnitArtifact>, SpecRefusal> {
    let mut units = Vec::new();
    let mut names: Vec<std::path::PathBuf> = match std::fs::read_dir(dir) {
        Ok(entries) => entries
            .filter_map(|entry| entry.ok().map(|e| e.path()))
            .filter(|path| {
                path.file_name()
                    .and_then(|n| n.to_str())
                    .is_some_and(|n| n.ends_with(SPEC_CLEAN_FILE_SUFFIX))
            })
            .collect(),
        Err(_) => return Err(SpecRefusal::NoArtifact),
    };
    names.sort();
    for path in names {
        let file_name =
            path.file_name().and_then(|n| n.to_str()).unwrap_or("<non-utf8>").to_string();
        let contents = std::fs::read_to_string(&path).map_err(|error| SpecRefusal::Malformed {
            file: file_name.clone(),
            detail: format!("unreadable: {error}"),
        })?;
        units.push(parse_unit_artifact(&file_name, &contents)?);
    }
    if units.is_empty() {
        return Err(SpecRefusal::NoArtifact);
    }
    Ok(units)
}

fn render_goal_row(row: &GoalRow) -> String {
    let mut out = String::new();
    out.push_str(&format!("  fn {}\n", row.def_path));
    out.push_str(&format!("    origin   {}\n", row.origin));
    out.push_str(&format!("    clause   `{}`\n", row.clause));
    out.push_str(&format!("    theorem  `{}`\n", row.theorem));
    match &row.detail {
        Some(detail) => out.push_str(&format!("    verdict  {} ({detail})\n", row.verdict)),
        None => out.push_str(&format!("    verdict  {}\n", row.verdict)),
    }
    match (&row.goal_clean, &row.elab_error) {
        (Some(goal), _) => out.push_str(&format!("    goal     {goal}\n")),
        (None, Some(reason)) => {
            out.push_str(&format!("    goal     (elaboration refused: {reason})\n"))
        }
        (None, None) => out.push_str("    goal     (absent)\n"),
    }
    out
}

fn render_units_human(units: &[UnitArtifact]) -> String {
    let mut out = String::new();
    out.push_str("targo trust spec --emit clean (compiler-authoritative, v6/D1)\n");
    for unit in units {
        let session_short: String = unit.session.chars().take(12).collect();
        out.push_str(&format!(
            "\ncrate {} (session {}…): {} kernel-graded goal(s)\n",
            unit.krate,
            session_short,
            unit.goals.len()
        ));
        for row in &unit.goals {
            out.push('\n');
            out.push_str(&render_goal_row(row));
        }
        if unit.goals.is_empty() {
            out.push_str(
                "\n  (the verification session completed and sealed the artifact, but graded no \
                 cited-ensures goals in this crate.\n   Goals exist where an `ensures` clause \
                 carries a `by <theorem>` citation against a clean{ } island theorem —\n   see \
                 tests/ui/trust/e9_definitional_call_discharge.rs for the shape.)\n",
            );
        }
    }
    out
}

/// Trim the hidden Cargo proof-unit identity subject (`cargo-target(...)`)
/// off a report crate/function name for HUMAN display. The full subject is
/// authoritative identity and stays in `--json`/report artifacts; here it
/// buries the one thing the reader needs (which function failed) under a
/// 500-character envelope. Purely lexical: no identity is re-derived, and a
/// name without the envelope prefix passes through unchanged.
fn strip_cargo_subject_prefix(name: &str) -> &str {
    if let Some(rest) = name.strip_prefix("cargo-target(") {
        if let Some(index) = rest.find(")::") {
            return &rest[index + ")::".len()..];
        }
    }
    name
}

/// The `package="..."` component of a hidden Cargo identity subject, for the
/// human crate label; the whole subject when the shape is not recognized.
fn human_crate_label(crate_name: &str) -> &str {
    if !crate_name.starts_with("cargo-target(") {
        return crate_name;
    }
    let Some(start) = crate_name.find("package=\"") else {
        return crate_name;
    };
    let rest = &crate_name[start + "package=\"".len()..];
    match rest.find('"') {
        Some(end) => &rest[..end],
        None => crate_name,
    }
}

/// One human line per obligation that kept the verified run from passing:
/// Failed / Unknown / Timeout rows, exactly as the sealed canonical report
/// records them. Proved, runtime-checked, and design-requirement rows are not
/// failures and are deliberately absent — this is a failure account, not a
/// report rendering (the spec surface suppresses those).
fn unfavorable_obligation_lines(report: &trust_types::JsonProofReport) -> Vec<String> {
    let mut lines = Vec::new();
    for function in &report.functions {
        for obligation in &function.obligations {
            let verdict = match &obligation.outcome {
                trust_types::ObligationOutcome::Failed { .. } => "FAILED".to_string(),
                trust_types::ObligationOutcome::Unknown { reason } => {
                    format!("UNKNOWN ({reason})")
                }
                trust_types::ObligationOutcome::Timeout { timeout_ms } => {
                    format!("TIMEOUT ({timeout_ms}ms)")
                }
                trust_types::ObligationOutcome::Proved { .. }
                | trust_types::ObligationOutcome::RuntimeChecked { .. }
                | trust_types::ObligationOutcome::DesignRequirement { .. } => continue,
                // `#[non_exhaustive]`: an outcome this build does not know is
                // DISCLOSED, never silently skipped — skipping would hide the
                // very row that failed the gate.
                other => format!("UNRECOGNIZED OUTCOME ({other:?})"),
            };
            let location = obligation
                .location
                .as_ref()
                .map(|span| format!(" @ {}:{}", span.file, span.line_start))
                .unwrap_or_default();
            lines.push(format!(
                "  {}: [{}] {} -> {verdict}{location}",
                strip_cargo_subject_prefix(&function.function),
                obligation.kind,
                obligation.description
            ));
        }
    }
    lines
}

/// Render the failing-run account from the sealed canonical report (when one
/// was sealed). A non-zero exit must never be silent: the spec surface
/// suppresses ordinary report rendering, so without this the strict gate's
/// verdict — which lives only in that report — would be invisible.
fn render_failed_run_account(sealed: Option<&trust_types::JsonProofReport>) -> String {
    let Some(report) = sealed else {
        return "targo trust spec: note: the verification run itself did not pass, and no \
                canonical report was sealed for this run — the failure happened before or \
                outside the verification walk (see the compiler/Cargo diagnostics above)"
            .to_string();
    };
    let mut out = String::new();
    let summary = &report.summary;
    out.push_str(&format!(
        "targo trust spec: note: the verification run itself did not pass; the goals above are \
         what the kernel graded before the failure.\n\
         targo trust spec: strict-gate summary for crate {}: {} proved, {} failed, {} \
         runtime-checked, {} unknown, {} timed out of {} obligation(s)",
        human_crate_label(&report.crate_name),
        summary.total_proved,
        summary.total_failed,
        summary.total_runtime_checked,
        summary.total_unknown,
        summary.total_timed_out,
        summary.total_obligations,
    ));
    let lines = unfavorable_obligation_lines(report);
    if lines.is_empty() {
        out.push_str(
            "\ntargo trust spec: no obligation in the sealed report is unproved — the failure \
             is outside the obligation rows (coverage, proof-frontier exclusion, or compiler \
             exit; see the diagnostics above)",
        );
    } else {
        out.push_str(&format!(
            "\ntargo trust spec: {} obligation(s) did not reach a favorable outcome:",
            lines.len()
        ));
        for line in &lines {
            out.push('\n');
            out.push_str(line);
        }
    }
    out
}

fn spec_usage() -> &'static str {
    "targo trust spec --emit clean [-p <pkg>] [check options]\n\
     \n\
     Prints the Clean goals the kernel actually graded for this crate's cited\n\
     `ensures` clauses — compiler-authoritative (v6/D1): the goals come from a\n\
     live verified compilation this command drives, never from an offline\n\
     re-elaboration, and the command REFUSES when no session artifact exists.\n\
     \n\
     Options:\n\
     \x20 --emit clean   required; the only supported goal surface today\n\
     \x20 --json         print the raw artifact rows (JSONL) instead of the human view\n\
     \x20 <everything else> is forwarded to the underlying `targo trust check`\n"
}

/// Entry point for `targo trust spec`.
pub(crate) fn run_spec_subcommand(args: &[String]) -> ExitCode {
    if args.iter().any(|arg| arg == "--help" || arg == "-h") {
        print!("{}", spec_usage());
        return ExitCode::SUCCESS;
    }
    let parsed = match parse_spec_args(args) {
        Ok(parsed) => parsed,
        Err(message) => {
            eprintln!("{message}");
            return ExitCode::from(2);
        }
    };
    // A FRESH directory per run: the read below can only be satisfied by an
    // artifact THIS compiler session wrote and sealed.
    let session_dir = match tempfile::Builder::new().prefix("targo-trust-spec-").tempdir() {
        Ok(dir) => dir,
        Err(error) => {
            eprintln!("targo trust spec: could not provision a session directory: {error}");
            return ExitCode::from(2);
        }
    };
    let session_path = match session_dir.path().canonicalize() {
        Ok(path) => path,
        Err(error) => {
            eprintln!("targo trust spec: could not canonicalize the session directory: {error}");
            return ExitCode::from(2);
        }
    };
    let Some(session_path_str) = session_path.to_str() else {
        eprintln!("targo trust spec: session directory path is not valid Unicode");
        return ExitCode::from(2);
    };

    // Drive the check-equivalent verified compilation with the emission knob.
    // Ordinary report rendering is suppressed (no report artifacts were
    // requested); compiler and verifier diagnostics still stream, which is
    // what the failing-build debugging case needs.
    let mut check_args = parsed.forwarded.clone();
    check_args.push("--spec-emit-dir".to_string());
    check_args.push(session_path_str.to_string());
    // Capture the sealed canonical report so a FAILING run can say why it
    // failed: ordinary report rendering is suppressed on this surface, and the
    // strict gate's verdict lives only in that report — without this capture a
    // gate failure exits non-zero with no visible cause (the fail-silent
    // class). Capturing is observational; verdicts and exit codes are the
    // check pipeline's alone.
    let mut sealed_report: Option<trust_types::JsonProofReport> = None;
    let mut capture_sealed_report =
        |live: &crate::report::LiveCanonicalReport| -> Result<(), String> {
            sealed_report = Some(live.for_spec_gate_disclosure().clone());
            Ok(())
        };
    let check_exit = crate::run_subcommand_with_live_report(
        Subcommand::Check,
        &check_args,
        Some(&mut capture_sealed_report),
        false,
    );

    // Fail-closed read-back: refusal wins over every other outcome.
    let units = match read_spec_artifacts(&session_path) {
        Ok(units) => units,
        Err(refusal) => {
            eprintln!("{}", refusal.render());
            return ExitCode::from(2);
        }
    };

    if parsed.json {
        for unit in &units {
            for row in &unit.goals {
                println!("{}", row.raw);
            }
        }
    } else {
        print!("{}", render_units_human(&units));
    }

    // The goals print even when the verified build failed — that is the
    // debugging case v6/D1 exists for — but the failure still fails, and it
    // says why (from the sealed canonical report, never a local re-derivation).
    if check_exit != ExitCode::SUCCESS {
        eprintln!("{}", render_failed_run_account(sealed_report.as_ref()));
        return check_exit;
    }
    check_exit
}

#[cfg(test)]
mod tests {
    use super::*;

    fn args(list: &[&str]) -> Vec<String> {
        list.iter().map(|s| s.to_string()).collect()
    }

    #[test]
    fn emit_clean_is_required_and_the_refusal_carries_the_fix() {
        let error = parse_spec_args(&args(&["-p", "demo"])).expect_err("missing --emit");
        assert!(error.contains("--emit clean"), "{error}");

        let error =
            parse_spec_args(&args(&["--emit", "trust-ir"])).expect_err("wrong emit surface");
        assert!(error.contains("not a supported goal surface"), "{error}");
        assert!(error.contains("--emit clean"), "options must be listed: {error}");
        assert!(error.contains("trust-dump=ir"), "options must be listed: {error}");
    }

    #[test]
    fn spec_owns_its_session_directory() {
        let error = parse_spec_args(&args(&["--emit", "clean", "--spec-emit-dir", "/tmp/x"]))
            .expect_err("--spec-emit-dir is subcommand-provisioned");
        assert!(error.contains("provisioned by the subcommand"), "{error}");
        assert!(error.contains("targo trust check --spec-emit-dir"), "fix option: {error}");
    }

    #[test]
    fn package_selection_and_json_parse_and_forward() {
        let parsed = parse_spec_args(&args(&["--emit=clean", "--json", "-p", "demo"]))
            .expect("valid spec args");
        assert!(parsed.json);
        assert_eq!(parsed.forwarded, args(&["-p", "demo"]));
    }

    const GOAL_LINE: &str = r#"{"format":"trust-spec-clean","v":1,"row":"goal","crate":"demo","session":"abc123","def_path":"demo::caller","origin":"ensures-citation","clause":"ident(x) >= ident(x)","theorem":"u64_ge_refl","goal_clean":"∀ (x : UInt64), Nat.le (UInt64.toNat (demo_ident x)) (UInt64.toNat (demo_ident x))","elab_error":null,"verdict":"certified","detail":null}"#;

    fn seal_line(goals: u64) -> String {
        format!(
            r#"{{"format":"trust-spec-clean","v":1,"row":"session","crate":"demo","session":"abc123","goals":{goals}}}"#
        )
    }

    #[test]
    fn a_sealed_artifact_round_trips_byte_preserving() {
        let contents = format!("{GOAL_LINE}\n{}\n", seal_line(1));
        let unit = parse_unit_artifact("demo.spec-clean.jsonl", &contents).expect("sealed unit");
        assert_eq!(unit.krate, "demo");
        assert_eq!(unit.goals.len(), 1);
        let row = &unit.goals[0];
        assert_eq!(row.verdict, "certified");
        assert_eq!(row.theorem, "u64_ge_refl");
        // --json passthrough must reproduce the compiler's bytes, not a
        // re-serialization: the goal text is the authoritative payload.
        assert_eq!(row.raw, GOAL_LINE);
        assert!(row.goal_clean.as_deref().unwrap_or_default().contains("UInt64.toNat"));
    }

    #[test]
    fn an_unknown_version_refuses_with_the_supported_one_named() {
        let line = GOAL_LINE.replace(r#""v":1"#, r#""v":2"#);
        let contents = format!("{line}\n{}\n", seal_line(1));
        let refusal =
            parse_unit_artifact("demo.spec-clean.jsonl", &contents).expect_err("v=2 must refuse");
        match &refusal {
            SpecRefusal::UnsupportedVersion { version, .. } => assert_eq!(version, "2"),
            other => panic!("expected UnsupportedVersion, got {other:?}"),
        }
        assert!(refusal.render().contains("understands only version 1"), "{}", refusal.render());
    }

    #[test]
    fn a_missing_seal_refuses_as_an_incomplete_session() {
        let contents = format!("{GOAL_LINE}\n");
        let refusal = parse_unit_artifact("demo.spec-clean.jsonl", &contents)
            .expect_err("unsealed must refuse");
        assert!(matches!(refusal, SpecRefusal::Unsealed { .. }), "{refusal:?}");
        assert!(refusal.render().contains("COMPLETES"), "{}", refusal.render());
    }

    #[test]
    fn a_seal_count_mismatch_refuses_as_torn() {
        let contents = format!("{GOAL_LINE}\n{}\n", seal_line(2));
        let refusal = parse_unit_artifact("demo.spec-clean.jsonl", &contents)
            .expect_err("count mismatch must refuse");
        assert!(matches!(refusal, SpecRefusal::Torn { sealed: 2, counted: 1, .. }), "{refusal:?}");
    }

    #[test]
    fn an_empty_session_directory_is_the_no_artifact_refusal() {
        let dir = tempfile::tempdir().expect("tempdir");
        let refusal = read_spec_artifacts(dir.path()).expect_err("no files must refuse");
        assert_eq!(refusal, SpecRefusal::NoArtifact);
        let rendered = refusal.render();
        // v7/D3: the refusal must carry the fix, with options.
        assert!(rendered.contains("compiler-authoritative"), "{rendered}");
        assert!(rendered.contains("./x.py build"), "{rendered}");
        assert!(rendered.contains("fix the build errors"), "{rendered}");
        assert!(rendered.contains("-Ztrust-dump=spec-clean:"), "{rendered}");
    }

    fn obligation_row(
        kind: &str,
        description: &str,
        outcome: trust_types::ObligationOutcome,
    ) -> trust_types::ObligationReport {
        trust_types::ObligationReport {
            obligation_id: None,
            description: description.to_string(),
            kind: kind.to_string(),
            proof_level: trust_types::ProofLevel::L1Functional,
            location: Some(trust_types::SourceSpan {
                file: "src/main.rs".to_string(),
                line_start: 9,
                col_start: 1,
                line_end: 9,
                col_end: 2,
            }),
            outcome,
            solver: "clean-kernel-citation".to_string(),
            time_ms: 0,
            evidence: None,
            proof_evidence: None,
            transport_evidence: None,
        }
    }

    #[test]
    fn a_failing_run_account_names_each_unfavorable_obligation() {
        let function = trust_types::FunctionProofReport {
            function: "demo::caller".to_string(),
            summary: trust_types::FunctionSummary {
                total_obligations: 3,
                proved: 1,
                runtime_checked: 0,
                failed: 1,
                unknown: 1,
                timed_out: 0,
                design_requirements: 0,
                unattributed_failed: 0,
                unattributed_unknown: 0,
                unattributed_proved: 0,
                total_time_ms: 0,
                max_proof_level: Some(trust_types::ProofLevel::L1Functional),
                verdict: trust_types::FunctionVerdict::Inconclusive,
            },
            obligations: vec![
                obligation_row(
                    "postcondition",
                    "postcondition",
                    trust_types::ObligationOutcome::Proved {
                        strength: trust_types::ProofStrength::smt_unsat_certified(),
                    },
                ),
                obligation_row(
                    "unsupported_mir",
                    "unsupported MIR `SpecEnsuresUnparseable`",
                    trust_types::ObligationOutcome::Unknown {
                        reason: "unsupported MIR obligations cannot carry proved outcomes"
                            .to_string(),
                    },
                ),
                obligation_row(
                    "assertion",
                    "assertion may fail",
                    trust_types::ObligationOutcome::Failed { counterexample: None },
                ),
            ],
        };
        let report = trust_types::JsonProofReport {
            metadata: trust_types::ReportMetadata {
                schema_version: "1.0".to_string(),
                trust_version: "test".to_string(),
                timestamp: String::new(),
                total_time_ms: 0,
                timeout_ms: None,
                function_budget_ms: None,
            },
            crate_name: "demo".to_string(),
            summary: trust_types::CrateSummary {
                functions_analyzed: 1,
                functions_verified: 0,
                functions_runtime_checked: 0,
                functions_with_violations: 1,
                functions_inconclusive: 0,
                total_obligations: 3,
                total_proved: 1,
                total_runtime_checked: 0,
                total_failed: 1,
                total_unknown: 1,
                total_timed_out: 0,
                total_design_requirements: 0,
                total_unattributed_failed: 0,
                total_unattributed_unknown: 0,
                total_unattributed_proved: 0,
                proof_grade_engine_statuses: Vec::new(),
                verdict: trust_types::CrateVerdict::HasViolations,
            },
            functions: vec![function],
            hardened: None,
            assumptions: Vec::new(),
            verification_gate: None,
            cargo_proof_inventory: None,
        };
        let lines = unfavorable_obligation_lines(&report);
        assert_eq!(lines.len(), 2, "{lines:?}");
        assert!(lines[0].contains("UNKNOWN (unsupported MIR obligations"), "{}", lines[0]);
        assert!(lines[0].contains("demo::caller"), "{}", lines[0]);
        assert!(lines[0].contains("src/main.rs:9"), "{}", lines[0]);
        assert!(lines[1].contains("FAILED"), "{}", lines[1]);
        // The account renders the summary AND the rows; a proved row never
        // appears as a failure.
        let account = render_failed_run_account(Some(&report));
        assert!(account.contains("did not pass"), "{account}");
        assert!(account.contains("2 obligation(s) did not reach a favorable outcome"), "{account}");
        assert!(!account.contains("postcondition -> "), "{account}");
    }

    #[test]
    fn cargo_identity_subjects_trim_for_display_only() {
        let subject = r#"cargo-target(package_id="path+file:///w/demo#0.1.0",package="demo",kind=["bin"],target="demo")"#;
        assert_eq!(
            strip_cargo_subject_prefix(&format!("{subject}::demo::caller")),
            "demo::caller"
        );
        assert_eq!(human_crate_label(subject), "demo");
        // Unrecognized shapes pass through UNCHANGED — trimming must never
        // invent a name.
        assert_eq!(strip_cargo_subject_prefix("demo::caller"), "demo::caller");
        assert_eq!(human_crate_label("demo"), "demo");
        assert_eq!(human_crate_label("cargo-target(no package key)"), "cargo-target(no package key)");
    }

    #[test]
    fn a_failing_run_without_a_sealed_report_says_so() {
        let account = render_failed_run_account(None);
        assert!(account.contains("did not pass"), "{account}");
        assert!(account.contains("no canonical report was sealed"), "{account}");
    }

    #[test]
    fn sealed_files_in_a_directory_are_read_and_sorted() {
        let dir = tempfile::tempdir().expect("tempdir");
        std::fs::write(
            dir.path().join("b_unit-0000000000000002.spec-clean.jsonl"),
            format!("{}\n", seal_line(0)),
        )
        .expect("write b");
        std::fs::write(
            dir.path().join("a_unit-0000000000000001.spec-clean.jsonl"),
            format!("{GOAL_LINE}\n{}\n", seal_line(1)),
        )
        .expect("write a");
        // A non-artifact file is ignored rather than parsed.
        std::fs::write(dir.path().join("notes.txt"), "not an artifact").expect("write noise");
        let units = read_spec_artifacts(dir.path()).expect("both units sealed");
        assert_eq!(units.len(), 2);
        assert_eq!(units[0].goals.len(), 1, "lexicographic file order");
        assert_eq!(units[1].goals.len(), 0);
        let human = render_units_human(&units);
        assert!(human.contains("1 kernel-graded goal(s)"), "{human}");
        assert!(human.contains("graded no"), "empty unit is reported honestly: {human}");
    }
}
