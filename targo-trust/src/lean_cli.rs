// targo trust: the pure-Lean front door.
//
// Trust accepts two authoritative languages. Rust arrives through the cargo
// lane; a standalone Clean/Lean file arrives here. The check is IN PROCESS —
// `trust-certify` links the same parser, elaborator, and CIC kernel the
// `clean { … }` island lane uses, so the verdict cannot depend on which
// `clean` binary happens to be on `PATH`, and there is no state in which a
// missing subprocess turns an unchecked file into a pass.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::{Path, PathBuf};
use std::process::ExitCode;

use trust_certify::clean_island::check_clean_island;

/// The operand suffix that selects this lane.
const LEAN_EXTENSION: &str = "lean";

/// Whether `path` names a Clean/Lean source operand.
fn is_lean_operand(arg: &str) -> bool {
    !arg.starts_with('-') && Path::new(arg).extension().is_some_and(|ext| ext == LEAN_EXTENSION)
}

/// Does this argument list select the Lean lane?
///
/// A `.lean` token anywhere before the `--` wrapper separator is enough. That
/// is deliberately looser than the Rust single-file rule, which has to worry
/// about a `.rs` path being the VALUE of some cargo option it must forward
/// verbatim. Nothing is forwarded here: [`parse`] refuses every argument it
/// does not itself define, so the only invocations this lane can consume are
/// ones made entirely of `.lean` operands and its own options. A `.lean` token
/// that really was an option's value produces a refusal naming that option,
/// never a check of the wrong thing.
///
/// After `--` the arguments belong to a child command, so they are not read.
pub(crate) fn selects_lean_lane(args: &[String]) -> bool {
    args.iter().take_while(|arg| arg.as_str() != "--").any(|arg| is_lean_operand(arg))
}

/// Everything the Lean lane accepts, resolved from the raw argument list.
#[derive(Debug)]
struct LeanRequest {
    files: Vec<PathBuf>,
    json: bool,
}

fn parse(args: &[String]) -> Result<LeanRequest, String> {
    let mut files = Vec::new();
    let mut json = false;

    let mut index = 0;
    while index < args.len() {
        let arg = args[index].as_str();
        match arg {
            "--json" => json = true,
            // Accept both spellings of the shared `--format` option so the Lean
            // lane reads the same as the Rust lane on the command line.
            "--format" => {
                index += 1;
                let value = args
                    .get(index)
                    .ok_or_else(|| "--format requires a value (terminal, json)".to_string())?;
                json = format_selects_json(value)?;
            }
            _ if arg.starts_with("--format=") => {
                json = format_selects_json(arg.trim_start_matches("--format="))?;
            }
            _ if is_lean_operand(arg) => files.push(PathBuf::from(arg)),
            other => {
                return Err(format!(
                    "`{other}` is not accepted alongside a Clean/Lean operand; the Lean lane \
                     takes `.lean` paths, `--json`, and `--format`.\n\
                     Cargo/rustc options belong to the Rust lane, which is selected by a crate \
                     or a `.rs` operand."
                ));
            }
        }
        index += 1;
    }

    if files.is_empty() {
        return Err("no `.lean` operand".to_string());
    }
    Ok(LeanRequest { files, json })
}

fn format_selects_json(value: &str) -> Result<bool, String> {
    match value {
        "json" => Ok(true),
        "terminal" => Ok(false),
        // HTML is a whole-crate report renderer; there is no crate-shaped
        // report behind a single kernel verdict, and emitting an empty one
        // would read as a clean report rather than an unsupported request.
        other => Err(format!("the Lean lane has no `{other}` format; use `terminal` or `json`")),
    }
}

/// One file's verdict.
struct FileVerdict {
    path: PathBuf,
    /// Declaration names that parsed, elaborated, and kernel-checked.
    registered: Vec<String>,
    /// Rendered `path:line:col: message` diagnostics. Non-empty ⇒ REJECTED.
    diagnostics: Vec<String>,
}

impl FileVerdict {
    fn accepted(&self) -> bool {
        self.diagnostics.is_empty()
    }
}

/// Translate a byte offset into the 1-based line/column a human can act on.
/// Columns count characters, not bytes, so a diagnostic inside Lean's unicode
/// operators points where the reader sees the operator.
fn line_and_column(source: &str, offset: usize) -> (usize, usize) {
    let offset = offset.min(source.len());
    let before = &source[..offset];
    let line = before.matches('\n').count() + 1;
    let line_start = before.rfind('\n').map_or(0, |nl| nl + 1);
    let column = source[line_start..offset].chars().count() + 1;
    (line, column)
}

fn check_file(path: &Path) -> FileVerdict {
    let source = match std::fs::read_to_string(path) {
        Ok(source) => source,
        Err(error) => {
            return FileVerdict {
                path: path.to_path_buf(),
                registered: Vec::new(),
                diagnostics: vec![format!("{}: {error}", path.display())],
            };
        }
    };

    let outcome = check_clean_island(&source);
    let diagnostics = outcome
        .errors
        .iter()
        .map(|error| {
            let (line, column) = line_and_column(&source, error.start);
            format!("{}:{line}:{column}: {}", path.display(), error.message)
        })
        .collect();
    FileVerdict { path: path.to_path_buf(), registered: outcome.registered, diagnostics }
}

fn render_json(verdicts: &[FileVerdict]) -> String {
    let files = verdicts
        .iter()
        .map(|verdict| {
            serde_json::json!({
                "path": verdict.path.display().to_string(),
                "accepted": verdict.accepted(),
                "registered": verdict.registered,
                "diagnostics": verdict.diagnostics,
            })
        })
        .collect::<Vec<_>>();
    let accepted = verdicts.iter().filter(|verdict| verdict.accepted()).count();
    serde_json::json!({
        "language": "clean",
        "checker": "in-process clean kernel (trust-certify)",
        "import_search": "disabled",
        "files": files,
        "accepted": accepted,
        "rejected": verdicts.len() - accepted,
    })
    .to_string()
}

/// `targo trust check <file.lean> …`
///
/// Fail-closed in every direction: an unreadable file, a parse error, a
/// declaration the kernel rejects, and an assumption (`axiom`, `sorry`, a
/// valueless `opaque`, a `partial`/`unsafe` marker) all exit non-zero. A file
/// is reported accepted only when the CIC kernel accepted every declaration in
/// it with no trust debt in the reachable closure.
pub(crate) fn run_check(args: &[String]) -> ExitCode {
    let request = match parse(args) {
        Ok(request) => request,
        Err(error) => {
            eprintln!("targo trust check: {error}");
            return ExitCode::from(2);
        }
    };

    let verdicts = request.files.iter().map(|path| check_file(path)).collect::<Vec<_>>();
    let rejected = verdicts.iter().filter(|verdict| !verdict.accepted()).count();

    if request.json {
        println!("{}", render_json(&verdicts));
    } else {
        for verdict in &verdicts {
            for diagnostic in &verdict.diagnostics {
                eprintln!("error: {diagnostic}");
            }
        }
        for verdict in &verdicts {
            if verdict.accepted() {
                println!(
                    "PROVED {} — {} declaration(s) kernel-checked",
                    verdict.path.display(),
                    verdict.registered.len()
                );
            } else {
                println!("REJECTED {}", verdict.path.display());
            }
        }
        // The import surface is a capability boundary, not a footnote: this
        // lane resolves nothing outside Clean's built-in preludes, so a reader
        // must never take a green verdict as covering an external library.
        println!(
            "checked in process by the Clean CIC kernel; external `.olean` import search is \
             disabled, so only crate-local Clean is authority"
        );
    }

    if rejected == 0 { ExitCode::SUCCESS } else { ExitCode::FAILURE }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn args(items: &[&str]) -> Vec<String> {
        items.iter().map(|item| (*item).to_string()).collect()
    }

    #[test]
    fn a_lean_operand_selects_the_lane() {
        assert!(selects_lean_lane(&args(&["proofs/x.lean"])));
        assert!(selects_lean_lane(&args(&["--json", "proofs/x.lean"])));
        assert!(!selects_lean_lane(&args(&["src/lib.rs"])));
        assert!(!selects_lean_lane(&args(&["--release"])));
    }

    #[test]
    fn arguments_after_the_wrapper_separator_belong_to_the_child() {
        assert!(!selects_lean_lane(&args(&["--", "proofs/x.lean"])));
    }

    #[test]
    fn a_lean_token_used_as_an_option_value_is_refused_not_checked() {
        let selected = args(&["--manifest-path", "weird.lean"]);
        assert!(selects_lean_lane(&selected));
        let error = parse(&selected).expect_err("must refuse rather than check `weird.lean`");
        assert!(error.contains("--manifest-path"), "{error}");
    }

    #[test]
    fn a_cargo_option_alongside_a_lean_operand_is_refused() {
        let error = parse(&args(&["--release", "x.lean"])).expect_err("must refuse");
        assert!(error.contains("--release"), "{error}");
    }

    #[test]
    fn both_format_spellings_select_json_and_an_unsupported_one_is_refused() {
        assert!(parse(&args(&["--format", "json", "x.lean"])).expect("parses").json);
        assert!(parse(&args(&["--format=json", "x.lean"])).expect("parses").json);
        assert!(!parse(&args(&["--format=terminal", "x.lean"])).expect("parses").json);
        assert!(parse(&args(&["--json", "x.lean"])).expect("parses").json);
        parse(&args(&["--format=html", "x.lean"])).expect_err("html must be refused");
    }

    #[test]
    fn line_and_column_are_one_based_and_count_characters() {
        let source = "def a := 1\ndef ∀b := 2\n";
        assert_eq!(line_and_column(source, 0), (1, 1));
        assert_eq!(line_and_column(source, 11), (2, 1));
        let unicode_offset = source.find('b').expect("fixture has `b`");
        assert_eq!(line_and_column(source, unicode_offset), (2, 6));
    }

    #[test]
    fn a_missing_file_is_a_rejection_not_a_pass() {
        let verdict = check_file(Path::new("/nonexistent/trust/absent.lean"));
        assert!(!verdict.accepted());
    }

    #[test]
    fn the_kernel_accepts_a_proof_and_refuses_an_assumption() {
        let dir = tempfile::tempdir().expect("tempdir");
        let good = dir.path().join("good.lean");
        std::fs::write(&good, "theorem t : 0 = 0 := rfl\n").expect("write");
        assert!(check_file(&good).accepted());

        let bad = dir.path().join("bad.lean");
        std::fs::write(&bad, "axiom assumed : True\n").expect("write");
        assert!(!check_file(&bad).accepted());
    }
}
