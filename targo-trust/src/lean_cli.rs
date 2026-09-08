// targo trust: the pure-Lean front door.
//
// Trust accepts two authoritative languages. Rust arrives through the cargo
// lane; a standalone Clean/Lean file arrives here. The check is IN PROCESS —
// `trust-certify` links the same parser, elaborator, and CIC kernel the
// `clean { … }` island lane uses, so the verdict cannot depend on which
// `clean` binary happens to be on `PATH`, and there is no state in which a
// missing subprocess turns an unchecked file into a pass.
//
// ONE INVOCATION IS ONE RESOLUTION UNIT. Every `.lean` operand of a single
// invocation is checked as one batch through the island session's header-first
// module elaboration (`CleanIslandSession::check_all`), so a declaration in
// one file may cite a declaration in another operand, source-order-
// independently — exactly as the islands of one crate resolve. Separate
// invocations stay isolated. Two refusals are wholesale by design:
//
//  * an UNREADABLE operand refuses the whole invocation — elaboration is not
//    monotone (`clean_island_batch`'s module doc), so a batch missing one unit
//    could silently change what a sibling declaration MEANS, not merely fail
//    to resolve it;
//  * a dependency CYCLE registers nothing (the batch facility's contract), so
//    no file may report PROVED — the members carry span-bearing diagnostics
//    plus Clean's own rendered options verbatim.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::{Path, PathBuf};
use std::process::ExitCode;

use trust_certify::clean_island::CleanIslandSession;

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
#[derive(Debug)]
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

/// One batch member: a listed operand, or a file the import closure pulled.
struct BatchMember {
    path: PathBuf,
    /// The module key this file supplies: a listed operand's file stem, or a
    /// pulled file's dotted module name exactly as imported. This is the key
    /// marked satisfied-from-source and the key the duplicate rule ranges over.
    module: String,
    source: String,
}

/// The module named by an `unresolved import` diagnostic, if `message` is one.
/// Bound to `clean_elab::ElabError::UnresolvedImport`'s own rendering
/// (`"unresolved import \`{module}\`: {reason}..."`); the closure below uses
/// the elaborator's refusals as its DISCOVERY mechanism, so no heuristic text
/// scan of Lean source exists anywhere in this lane — a module is pulled only
/// after the real parser+elaborator declared it imported and unresolved.
fn unresolved_import_module(message: &str) -> Option<&str> {
    let rest = message.split("unresolved import `").nth(1)?;
    rest.split('`').next()
}

/// Check every operand of ONE invocation as ONE batch (module doc: one
/// invocation is one resolution unit), pulling the invocation's TRANSITIVE
/// intra-project import closure (W2/lean-import-closure): an `import M` whose
/// dotted path names a `.lean` file relative to the importing file's own
/// directory joins the batch as a first-class member — parsed, elaborated,
/// kernel-checked, and REPORTED with its own verdict row, so nothing pulled is
/// ever silent. Resolution never leaves the members' directories except
/// downward through dotted segments; an import resolving to no such file keeps
/// the elaborator's verbatim refusal. Island-relative offsets are
/// file-relative here, so the per-file rendering is unchanged.
fn check_files(paths: &[PathBuf]) -> Vec<FileVerdict> {
    let wholesale = |members: &[BatchMember], refusal: &str| -> Vec<FileVerdict> {
        members
            .iter()
            .map(|member| FileVerdict {
                path: member.path.clone(),
                registered: Vec::new(),
                diagnostics: vec![refusal.to_string()],
            })
            .collect()
    };

    // Listed operands first; an unreadable one refuses the whole invocation
    // (v7/D3: the refusal carries the fix, with options — and a batch missing
    // one unit could change what a sibling declaration MEANS, so no partial
    // batch runs).
    let mut members: Vec<BatchMember> = Vec::with_capacity(paths.len());
    let mut unreadable: Vec<String> = Vec::new();
    for path in paths {
        let module = path
            .file_stem()
            .and_then(|s| s.to_str())
            .map_or_else(|| path.display().to_string(), str::to_string);
        match std::fs::read_to_string(path) {
            Ok(source) => members.push(BatchMember { path: path.clone(), module, source }),
            Err(error) => {
                unreadable.push(format!("{}: {error}", path.display()));
                members.push(BatchMember { path: path.clone(), module, source: String::new() });
            }
        }
    }
    if !unreadable.is_empty() {
        let refusal = format!(
            "batch refused: unreadable operand(s): {}. One invocation is one resolution \
             unit, and a partial unit could change what a sibling declaration means. \
             Options: fix or remove the unreadable operand(s), or check the readable \
             files in their own invocation",
            unreadable.join("; "),
        );
        let mut verdicts = wholesale(&members, &refusal);
        for (verdict, member) in verdicts.iter_mut().zip(&members) {
            if let Some(own) =
                unreadable.iter().find(|m| m.starts_with(&member.path.display().to_string()))
            {
                verdict.diagnostics.insert(0, own.clone());
            }
        }
        return verdicts;
    }

    // The closure fixpoint. Each iteration marks every member's module key
    // satisfied-from-source (W2/lean-sibling-imports) and batch-checks; the
    // elaborator's own unresolved-import refusals then name exactly the
    // modules still missing, and any that resolve to a `.lean` file relative
    // to an importing member's directory are pulled as new members. A module
    // that stays unresolvable keeps the verbatim refusal in the final render.
    // Terminates: every iteration adds at least one member (else it returns),
    // members come only from files on disk, and the cap fails CLOSED.
    const CLOSURE_ITERATION_CAP: usize = 64;
    for _iteration in 0..CLOSURE_ITERATION_CAP {
        // Duplicate module keys make the satisfied record ambiguous about
        // which file supplies the module — refuse wholesale with the fix.
        let mut by_module: std::collections::BTreeMap<&str, Vec<&Path>> =
            std::collections::BTreeMap::new();
        for member in &members {
            by_module.entry(member.module.as_str()).or_default().push(member.path.as_path());
        }
        let duplicated: Vec<String> = by_module
            .iter()
            .filter(|(_, files)| files.len() > 1)
            .map(|(module, files)| {
                format!(
                    "`{module}` ({})",
                    files.iter().map(|p| p.display().to_string()).collect::<Vec<_>>().join(", ")
                )
            })
            .collect();
        if !duplicated.is_empty() {
            let refusal = format!(
                "batch refused: duplicate module stem(s): {}. An `import` of that module \
                 would be ambiguous about which operand supplies it. Options: rename one \
                 file, or check the duplicates in separate invocations",
                duplicated.join("; "),
            );
            return wholesale(&members, &refusal);
        }

        let mut session = CleanIslandSession::new();
        for module in by_module.keys() {
            session.mark_import_satisfied_from_source(module);
        }
        let source_refs: Vec<&str> = members.iter().map(|m| m.source.as_str()).collect();
        let batch = session.check_all(&source_refs);

        if !batch.cycles.is_empty() {
            // NOTHING was registered (the batch facility's contract), so no
            // file may read PROVED. Members get span-bearing rows plus Clean's
            // own rendered options verbatim; everyone else the batch refusal.
            let mut per_file: Vec<Vec<String>> = vec![Vec::new(); members.len()];
            let mut rendered_cycles: Vec<String> = Vec::new();
            for cycle in &batch.cycles {
                rendered_cycles.push(cycle.render());
                for site in &cycle.sites {
                    if let (Some(bucket), Some(member)) =
                        (per_file.get_mut(site.island), members.get(site.island))
                    {
                        let (line, column) = line_and_column(&member.source, site.start);
                        bucket.push(format!(
                            "{}:{line}:{column}: declaration `{}` is on the dependency cycle {}",
                            member.path.display(),
                            site.name,
                            cycle.render(),
                        ));
                    }
                }
                for bucket in &mut per_file {
                    if !bucket.is_empty() {
                        bucket.push(cycle.message.clone());
                    }
                }
            }
            return members
                .iter()
                .zip(per_file)
                .map(|(member, mut diagnostics)| {
                    if diagnostics.is_empty() {
                        diagnostics.push(format!(
                            "batch refused by dependency cycle(s) {} — nothing from this \
                             invocation was registered, so this file cannot report PROVED; \
                             break the cycle (or check this file in its own invocation)",
                            rendered_cycles.join(", "),
                        ));
                    }
                    FileVerdict { path: member.path.clone(), registered: Vec::new(), diagnostics }
                })
                .collect();
        }

        // DISCOVERY: modules the elaborator refused as unresolved, resolved
        // relative to the directory of the member whose diagnostic named them.
        let mut pulls: Vec<(PathBuf, String)> = Vec::new();
        for (member, outcome) in members.iter().zip(&batch.outcomes) {
            for error in &outcome.errors {
                let Some(module) = unresolved_import_module(&error.message) else { continue };
                if by_module.contains_key(module)
                    || pulls.iter().any(|(_, pulled)| pulled == module)
                {
                    continue;
                }
                let mut candidate =
                    member.path.parent().map_or_else(PathBuf::new, Path::to_path_buf);
                for segment in module.split('.') {
                    candidate.push(segment);
                }
                let candidate = candidate.with_extension("lean");
                if candidate.is_file() {
                    pulls.push((candidate, module.to_string()));
                }
            }
        }
        if pulls.is_empty() {
            // Fixpoint: render the final verdicts over every member — pulled
            // files included, each with its own row (the disclosure).
            return members
                .iter()
                .zip(batch.outcomes)
                .map(|(member, outcome)| {
                    let diagnostics = outcome
                        .errors
                        .iter()
                        .map(|error| {
                            let (line, column) = line_and_column(&member.source, error.start);
                            format!("{}:{line}:{column}: {}", member.path.display(), error.message)
                        })
                        .collect();
                    FileVerdict {
                        path: member.path.clone(),
                        registered: outcome.registered,
                        diagnostics,
                    }
                })
                .collect();
        }
        for (path, module) in pulls {
            match std::fs::read_to_string(&path) {
                Ok(source) => members.push(BatchMember { path, module, source }),
                Err(error) => {
                    let refusal = format!(
                        "batch refused: `import {module}` resolves to {} but it cannot be \
                         read ({error}). Options: fix the file, or remove the import",
                        path.display(),
                    );
                    return wholesale(&members, &refusal);
                }
            }
        }
    }
    let refusal = format!(
        "batch refused: the import closure did not settle within \
         {CLOSURE_ITERATION_CAP} iterations. This is a fail-closed cap, not a \
         verdict; report this invocation's file graph",
    );
    wholesale(&members, &refusal)
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
/// All operands of one invocation are checked as ONE batch ([`check_files`]),
/// so cross-file citations within the invocation resolve; separate
/// invocations stay isolated.
///
/// Fail-closed in every direction: an unreadable file (which refuses the whole
/// batch), a parse error, a dependency cycle, a declaration the kernel
/// rejects, and an assumption (`axiom`, `sorry`, a valueless `opaque`, a
/// `partial`/`unsafe` marker) all exit non-zero. A file is reported accepted
/// only when the CIC kernel accepted every declaration in it with no trust
/// debt in the reachable closure.
pub(crate) fn run_check(args: &[String]) -> ExitCode {
    let request = match parse(args) {
        Ok(request) => request,
        Err(error) => {
            eprintln!("targo trust check: {error}");
            return ExitCode::from(2);
        }
    };

    let verdicts = check_files(&request.files);
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
        let verdicts = check_files(&[PathBuf::from("/nonexistent/trust/absent.lean")]);
        assert!(!verdicts[0].accepted());
    }

    #[test]
    fn the_kernel_accepts_a_proof_and_refuses_an_assumption() {
        let dir = tempfile::tempdir().expect("tempdir");
        let good = dir.path().join("good.lean");
        std::fs::write(&good, "theorem t : 0 = 0 := rfl\n").expect("write");
        assert!(check_files(&[good]).remove(0).accepted());

        let bad = dir.path().join("bad.lean");
        std::fs::write(&bad, "axiom assumed : True\n").expect("write");
        assert!(!check_files(&[bad]).remove(0).accepted());
    }

    /// Write `name := source` fixtures and batch-check them in the given order.
    fn batch(dir: &tempfile::TempDir, files: &[(&str, &str)]) -> Vec<FileVerdict> {
        let paths: Vec<PathBuf> = files
            .iter()
            .map(|(name, source)| {
                let path = dir.path().join(name);
                std::fs::write(&path, source).expect("write fixture");
                path
            })
            .collect();
        check_files(&paths)
    }

    #[test]
    fn a_cross_file_citation_resolves_in_either_order() {
        let dir = tempfile::tempdir().expect("tempdir");
        let base = ("a.lean", "def base : Nat := 7\n");
        let uses = ("b.lean", "def uses : Nat := base\n");
        for order in [[base, uses], [uses, base]] {
            let verdicts = batch(&dir, &order);
            assert!(
                verdicts.iter().all(FileVerdict::accepted),
                "one invocation is one resolution unit, order {:?}: {:?}",
                order.map(|(name, _)| name),
                verdicts.iter().flat_map(|v| &v.diagnostics).collect::<Vec<_>>(),
            );
        }
    }

    #[test]
    fn separate_invocations_stay_isolated() {
        let dir = tempfile::tempdir().expect("tempdir");
        assert!(batch(&dir, &[("a.lean", "def base : Nat := 7\n")])[0].accepted());
        // A NEW invocation must not see the previous invocation's names.
        let verdicts = batch(&dir, &[("b.lean", "def uses : Nat := base\n")]);
        assert!(!verdicts[0].accepted(), "isolation across invocations must hold");
    }

    #[test]
    fn a_cycle_is_refused_with_named_members_and_nothing_proved() {
        let dir = tempfile::tempdir().expect("tempdir");
        let verdicts = batch(
            &dir,
            &[
                ("a.lean", "def x : Nat := y\n"),
                ("b.lean", "def y : Nat := x\n"),
                ("c.lean", "def unrelated : Nat := 3\n"),
            ],
        );
        assert!(
            verdicts.iter().all(|verdict| !verdict.accepted()),
            "a cycle registers nothing, so NO file may report PROVED: {verdicts:?}",
        );
        assert!(verdicts.iter().all(|verdict| verdict.registered.is_empty()));
        let all: String =
            verdicts.iter().flat_map(|v| &v.diagnostics).cloned().collect::<Vec<_>>().join("\n");
        assert!(all.contains('x') && all.contains('y'), "members must be named: {all}");
    }

    #[test]
    fn an_axiom_in_one_operand_rejects_that_file_in_the_batch() {
        let dir = tempfile::tempdir().expect("tempdir");
        let verdicts = batch(
            &dir,
            &[("good.lean", "def base : Nat := 7\n"), ("bad.lean", "axiom assumed : True\n")],
        );
        assert!(verdicts[0].accepted(), "{:?}", verdicts[0].diagnostics);
        assert!(!verdicts[1].accepted(), "the strict authority policy holds in a batch");
    }

    #[test]
    fn a_sibling_import_is_satisfied_in_either_order() {
        let dir = tempfile::tempdir().expect("tempdir");
        let base = ("A.lean", "def base : Nat := 7\n");
        let uses = ("B.lean", "import A\ndef uses : Nat := base\n");
        for order in [[base, uses], [uses, base]] {
            let verdicts = batch(&dir, &order);
            assert!(
                verdicts.iter().all(FileVerdict::accepted),
                "a sibling import is the no-op batch resolution already makes, order {:?}: {:?}",
                order.map(|(name, _)| name),
                verdicts.iter().flat_map(|v| &v.diagnostics).collect::<Vec<_>>(),
            );
        }
    }

    #[test]
    fn a_non_sibling_import_keeps_the_verbatim_refusal() {
        let dir = tempfile::tempdir().expect("tempdir");
        let verdicts =
            batch(&dir, &[("A.lean", "def base : Nat := 7\n"), ("B.lean", "import Absent\n")]);
        assert!(verdicts[0].accepted());
        assert!(!verdicts[1].accepted());
        let diags = verdicts[1].diagnostics.join("\n");
        assert!(diags.contains("unresolved import `Absent`"), "{diags}");
    }

    #[test]
    fn duplicate_module_stems_refuse_the_whole_batch() {
        let dir = tempfile::tempdir().expect("tempdir");
        let sub = dir.path().join("sub");
        std::fs::create_dir(&sub).expect("mkdir");
        let a1 = dir.path().join("A.lean");
        let a2 = sub.join("A.lean");
        std::fs::write(&a1, "def x : Nat := 1\n").expect("write");
        std::fs::write(&a2, "def y : Nat := 2\n").expect("write");
        let verdicts = check_files(&[a1, a2]);
        assert!(verdicts.iter().all(|verdict| !verdict.accepted()));
        let diags = verdicts[0].diagnostics.join("\n");
        assert!(diags.contains("duplicate module stem"), "{diags}");
        assert!(diags.contains("Options:"), "{diags}");
    }

    #[test]
    fn a_single_operand_pulls_its_import_closure() {
        let dir = tempfile::tempdir().expect("tempdir");
        std::fs::write(dir.path().join("Helper.lean"), "def base : Nat := 7\n").expect("write");
        let main = dir.path().join("Main.lean");
        std::fs::write(&main, "import Helper\ndef uses : Nat := base\n").expect("write");
        let verdicts = check_files(&[main]);
        assert_eq!(verdicts.len(), 2, "the pulled file gets its own row: {verdicts:?}");
        assert!(
            verdicts.iter().all(FileVerdict::accepted),
            "{:?}",
            verdicts.iter().flat_map(|v| &v.diagnostics).collect::<Vec<_>>(),
        );
        assert!(verdicts.iter().any(|v| v.path.ends_with("Helper.lean")));
    }

    #[test]
    fn a_transitive_chain_is_pulled_depth_safely() {
        let dir = tempfile::tempdir().expect("tempdir");
        std::fs::write(dir.path().join("Base.lean"), "def origin : Nat := 3\n").expect("write");
        std::fs::write(
            dir.path().join("Helper.lean"),
            "import Base\ndef doubled : Nat := origin + origin\n",
        )
        .expect("write");
        let main = dir.path().join("Main.lean");
        std::fs::write(&main, "import Helper\ndef uses : Nat := doubled\n").expect("write");
        let verdicts = check_files(&[main]);
        assert_eq!(verdicts.len(), 3, "{verdicts:?}");
        assert!(
            verdicts.iter().all(FileVerdict::accepted),
            "{:?}",
            verdicts.iter().flat_map(|v| &v.diagnostics).collect::<Vec<_>>(),
        );
    }

    #[test]
    fn a_dotted_import_resolves_below_the_importer() {
        let dir = tempfile::tempdir().expect("tempdir");
        std::fs::create_dir(dir.path().join("Sub")).expect("mkdir");
        std::fs::write(dir.path().join("Sub").join("Mod.lean"), "def inner : Nat := 9\n")
            .expect("write");
        let main = dir.path().join("Main.lean");
        std::fs::write(&main, "import Sub.Mod\ndef uses : Nat := inner\n").expect("write");
        let verdicts = check_files(&[main]);
        assert_eq!(verdicts.len(), 2, "{verdicts:?}");
        assert!(
            verdicts.iter().all(FileVerdict::accepted),
            "{:?}",
            verdicts.iter().flat_map(|v| &v.diagnostics).collect::<Vec<_>>(),
        );
    }

    #[test]
    fn a_pulled_file_rejection_fails_the_invocation() {
        let dir = tempfile::tempdir().expect("tempdir");
        std::fs::write(dir.path().join("Helper.lean"), "axiom assumed : True\n").expect("write");
        let main = dir.path().join("Main.lean");
        std::fs::write(&main, "import Helper\ndef ok : Nat := 1\n").expect("write");
        let verdicts = check_files(&[main]);
        assert!(
            verdicts.iter().any(|v| v.path.ends_with("Helper.lean") && !v.accepted()),
            "a pulled file's trust debt must be visible and failing: {verdicts:?}",
        );
    }

    #[test]
    fn an_unreadable_operand_refuses_the_whole_batch_with_the_fix() {
        let dir = tempfile::tempdir().expect("tempdir");
        let good = dir.path().join("good.lean");
        std::fs::write(&good, "def base : Nat := 7\n").expect("write");
        let verdicts = check_files(&[PathBuf::from("/nonexistent/trust/absent.lean"), good]);
        assert!(verdicts.iter().all(|verdict| !verdict.accepted()));
        let good_diags = verdicts[1].diagnostics.join("\n");
        assert!(good_diags.contains("batch refused"), "{good_diags}");
        assert!(good_diags.contains("Options:"), "the refusal must carry the fix: {good_diags}");
    }
}
