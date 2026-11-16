// targo trust: the pure-Lean front door.
//
// Trust accepts two authoritative languages. Rust arrives through the cargo
// lane; a standalone Clean/Lean file — or a DIRECTORY of them that no
// Cargo/Targo manifest governs — arrives here. The check is IN PROCESS —
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
// The batch is all or nothing in every other refusal too: a file rejected
// anywhere commits nothing, and the reference kernel recheck and the
// accepted-source binding run only for an accepted batch. So a file whose own
// declarations all kernel-checked beside a REJECTED sibling prints
// `NOT ACCEPTED` with the sibling named, never PROVED (`FileReport`), exactly
// as its `trust.obligations.v1` record leaves its rows `unknown`.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::{Path, PathBuf};
use std::process::ExitCode;

use trust_certify::lean_source_batch::{
    AcceptedLeanSourceContext, CheckedLeanSourceBatch, LeanBatchTiming, LeanSourceAlias,
    LeanSourceInput,
};

pub(crate) mod census;
pub(crate) mod records;
pub(crate) mod run_record;

/// The operand suffix that selects this lane.
const LEAN_EXTENSION: &str = "lean";

/// Whether `path` names a Clean/Lean source operand.
fn is_lean_operand(arg: &str) -> bool {
    !arg.starts_with('-') && Path::new(arg).extension().is_some_and(|ext| ext == LEAN_EXTENSION)
}

/// How deep a DIRECTORY operand is walked for `.lean` sources.
const LEAN_DIR_MAX_DEPTH: usize = 32;

/// `.lean` file names that are BUILD CONFIGURATION, not proof sources.
///
/// A Lake project's `lakefile.lean` is Lake DSL: it `import Lake`, which no
/// Clean-native prelude provides, and its `package`/`lean_lib` commands do not
/// parse as declarations. Kernel-checking it produced a confident REJECTED row
/// for a project `clean lake build` builds cleanly, so the directory walk skips
/// it. It is skipped rather than refused because a caller who names the file
/// EXPLICITLY still gets the ordinary verdict; only the implicit sweep is
/// narrowed.
const LEAN_BUILD_CONFIG_NAMES: &[&str] = &["lakefile.lean"];

/// Does a Cargo/Targo manifest govern `dir` — at it, or at any ancestor?
///
/// This is the EXACT question the Rust lane's own package selection asks; its
/// refusal names it ("could not find `Targo.toml` or `Cargo.toml` in <dir> or
/// any parent directory"). Answering `true` therefore means the Rust lane CAN
/// resolve this directory, and the Lean lane must leave it alone. That is what
/// keeps the directory operand strictly ADDITIVE: it can only ever convert a
/// hard Rust-lane refusal into a check, never redirect an invocation that
/// worked. A mixed tree (`.lean` files inside a crate) stays with the Rust
/// lane by construction; its Clean is reachable by naming the files.
///
/// Fail-closed: a path that will not canonicalize answers `true`, so an
/// unreadable operand keeps the Rust lane's own diagnostics rather than being
/// silently adopted here.
fn manifest_governs(dir: &Path) -> bool {
    let Ok(canonical) = std::fs::canonicalize(dir) else {
        return true;
    };
    canonical
        .ancestors()
        .any(|base| base.join("Cargo.toml").is_file() || base.join("Targo.toml").is_file())
}

/// Every `.lean` source under `dir`, in a deterministic (sorted) order.
///
/// Hidden entries (`.git`, `.lake`, an editor's scratch dir) and symlinks are
/// skipped and the walk is depth-bounded, so a directory operand can never
/// become an unbounded or cyclic traversal. An unreadable subdirectory is
/// skipped rather than fatal — an operand that yields NO sources simply is not
/// a Lean operand, and the Rust lane keeps it.
fn lean_files_under(dir: &Path) -> Vec<PathBuf> {
    fn collect(dir: &Path, depth: usize, found: &mut Vec<PathBuf>) {
        if depth >= LEAN_DIR_MAX_DEPTH {
            return;
        }
        let Ok(entries) = std::fs::read_dir(dir) else {
            return;
        };
        for entry in entries.flatten() {
            if entry.file_name().to_string_lossy().starts_with('.') {
                continue;
            }
            let Ok(file_type) = entry.file_type() else {
                continue;
            };
            if file_type.is_symlink() {
                continue;
            }
            let path = entry.path();
            if file_type.is_dir() {
                collect(&path, depth + 1, found);
            } else if file_type.is_file()
                && path.extension().is_some_and(|ext| ext == LEAN_EXTENSION)
                && !LEAN_BUILD_CONFIG_NAMES.contains(&entry.file_name().to_string_lossy().as_ref())
            {
                found.push(path);
            }
        }
    }
    let mut found = Vec::new();
    collect(dir, 0, &mut found);
    found.sort();
    found
}

/// Whether `arg` names a DIRECTORY of Clean/Lean sources that the Rust lane
/// provably cannot resolve. See [`manifest_governs`] for why both halves of
/// the condition are required.
fn is_lean_directory_operand(arg: &str) -> bool {
    if arg.starts_with('-') {
        return false;
    }
    let path = Path::new(arg);
    path.is_dir() && !manifest_governs(path) && !lean_files_under(path).is_empty()
}

/// Does this argument list select the Lean lane?
///
/// A `.lean` token — or a DIRECTORY holding one, per [`is_lean_directory_operand`]
/// — anywhere before the `--` wrapper separator is enough. That is deliberately
/// looser than the Rust single-file rule, which has to worry about a `.rs` path
/// being the VALUE of some cargo option it must forward verbatim. Nothing is
/// forwarded here: whichever parser the selected route uses refuses every
/// argument it does not itself define — [`parse`] for `check`, and for `build`
/// either `lean_build`'s own parser, which adds the `--emit`, `--out` and
/// `--verbose` that [`parse`] refuses, or, when `--emit=diagnostic-runtime-trust-ir`
/// selects the diagnostic lane, `lean_build::runtime`'s, which adds `--entry`
/// and `--entry-json` on top of those. `--census` and `--census-olean-path` are
/// deliberately NOT in that list: [`parse`] defines both itself, so neither
/// distinguishes the routes. So the only invocations this lane can consume are
/// ones made entirely of `.lean` operands, such directories, and the selected
/// route's own options. This predicate gates BOTH routes (`main.rs`, the
/// `check` and `build` arms), so naming only [`parse`] understated what it
/// admits. A `.lean` token that really was an option's value is CONSUMED by
/// that option, so the route's parser refuses either way — naming the option
/// when its own guard rejects the value, as `--format` does, and otherwise
/// naming the `.lean` operand that is now missing — never a check of the wrong
/// thing.
///
/// The directory form is narrow by construction, which is what keeps the
/// argument above honest: it takes no leading `-`, it must BE a directory, it
/// must hold a `.lean` file, and a directory a cargo manifest governs is
/// refused — so it cannot swallow a workspace path meant for another lane.
///
/// After `--` the arguments belong to a child command, so they are not read.
pub(crate) fn selects_lean_lane(args: &[String]) -> bool {
    args.iter()
        .take_while(|arg| arg.as_str() != "--")
        .any(|arg| is_lean_operand(arg) || is_lean_directory_operand(arg))
}

/// Everything the Lean lane accepts, resolved from the raw argument list.
#[derive(Debug)]
struct LeanRequest {
    files: Vec<PathBuf>,
    json: bool,
    census_output: Option<PathBuf>,
    olean_paths: Vec<PathBuf>,
    /// Directory operands that hold a `lakefile.lean`, kept so the run can
    /// DISCLOSE that Lake's own resolution was not used. Never a verdict input.
    lake_dirs: Vec<PathBuf>,
    /// `--since <token>` and `--all-rows` (`crate::agent_delta`).
    delta: crate::agent_delta::DeltaRequest,
    /// `--target-dir DIR`: where the run's records go — its
    /// `trust.lean-run.v1` timing record and its `trust.obligations.v1`
    /// records and snapshots (`records::record_target_dir`, the one
    /// resolver for both). Never a verdict input.
    target_dir: Option<PathBuf>,
}

fn parse(args: &[String]) -> Result<LeanRequest, String> {
    let mut args = args.to_vec();
    let delta = crate::agent_delta::DeltaRequest::take_from(&mut args)?;
    let args = args.as_slice();
    let mut files = Vec::new();
    let mut lake_dirs: Vec<PathBuf> = Vec::new();
    let mut json = false;
    let mut census_output = None;
    let mut olean_paths = Vec::new();
    let mut target_dir = None;

    let mut index = 0;
    while index < args.len() {
        // Cargo's job count schedules nothing here (the kernel checks the
        // batch itself); aterm's build admission appends `--jobs=N` to every
        // admitted line, so it is accepted and ignored rather than refused.
        if let Some(width) = crate::cli::cargo_jobs_hint_width(args, index) {
            index += width;
            continue;
        }
        let arg = args[index].as_str();
        match arg {
            "--json" => json = true,
            "--target-dir" => {
                index += 1;
                let value = args.get(index).ok_or("--target-dir requires a directory")?;
                if value.is_empty() || value.starts_with('-') || target_dir.is_some() {
                    return Err("--target-dir requires exactly one directory".into());
                }
                target_dir = Some(PathBuf::from(value));
            }
            _ if arg.starts_with("--target-dir=") => {
                let value = arg.strip_prefix("--target-dir=").expect("matched prefix");
                if value.is_empty() || target_dir.is_some() {
                    return Err("--target-dir requires exactly one directory".into());
                }
                target_dir = Some(PathBuf::from(value));
            }
            "--census-olean-path" => {
                index += 1;
                let value = args.get(index).ok_or("--census-olean-path requires a directory")?;
                if value.is_empty() || value.starts_with('-') {
                    return Err("--census-olean-path requires a directory".into());
                }
                olean_paths.push(PathBuf::from(value));
            }
            _ if arg.starts_with("--census-olean-path=") => {
                let value = arg.strip_prefix("--census-olean-path=").expect("matched prefix");
                if value.is_empty() || value.starts_with('-') {
                    return Err("--census-olean-path requires a directory".into());
                }
                olean_paths.push(PathBuf::from(value));
            }
            "--census" => {
                index += 1;
                let value = args
                    .get(index)
                    .ok_or_else(|| "--census requires a new output path".to_string())?;
                if value.starts_with('-') || value.is_empty() || census_output.is_some() {
                    return Err("--census requires exactly one new output path".to_string());
                }
                census_output = Some(PathBuf::from(value));
            }
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
            _ if is_lean_directory_operand(arg) => {
                let dir = Path::new(arg);
                // A Lake project is RECORDED, not refused and not dispatched: Lake
                // BUILDS and judges nothing, so routing a check there would let a
                // successful compile read as a discharged proof.
                if LEAN_BUILD_CONFIG_NAMES.iter().any(|name| dir.join(name).is_file()) {
                    lake_dirs.push(dir.to_path_buf());
                }
                files.extend(lean_files_under(dir));
            }
            other => {
                return Err(format!(
                    "`{other}` is not accepted alongside a Clean/Lean operand; the Lean lane \
                     takes `.lean` paths, a directory of `.lean` sources, `--json`, \
                     `--format`, `--since TOKEN`, `--all-rows`, `--target-dir DIR`, \
                     `--census PATH`, `--census-olean-path DIR`, which requires \
                     `--census`, and Cargo's `--jobs N`, which it ignores.\n\
                     Cargo/rustc options belong to the Rust lane, which is selected by a crate \
                     or a `.rs` operand."
                ));
            }
        }
        index += 1;
    }

    // A directory operand and one of its own files can both be named. The
    // batch's duplicate-module rule would then refuse the WHOLE invocation for
    // a duplication the caller never wrote, so collapse them on identity,
    // keeping the caller's first spelling for the reported path.
    let mut seen: Vec<PathBuf> = Vec::new();
    files.retain(|path| {
        let key = std::fs::canonicalize(path).unwrap_or_else(|_| path.clone());
        if seen.contains(&key) {
            false
        } else {
            seen.push(key);
            true
        }
    });

    if files.is_empty() {
        return Err("no `.lean` operand".to_string());
    }
    if !olean_paths.is_empty() && census_output.is_none() {
        return Err("--census-olean-path requires --census; it inventories dependencies but does not enable external imports".into());
    }
    Ok(LeanRequest { files, json, census_output, olean_paths, lake_dirs, delta, target_dir })
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
pub(crate) struct FileVerdict {
    path: PathBuf,
    /// Declaration names that parsed, elaborated, and kernel-checked.
    registered: Vec<String>,
    /// Rendered `path:line:col: message` diagnostics. Non-empty ⇒ REJECTED.
    diagnostics: Vec<String>,
    /// `import`s the parsed batch ACCEPTED with no crate-local source behind
    /// them and no `.olean`: Clean served its built-in prelude stand-in for a
    /// module it names verbatim (`Mathlib`, `Lean`, `Lean.*`). Not a
    /// kernel rejection — every declaration was checked against that stand-in
    /// — but standalone `check` refuses to call this a proof of the real
    /// library. Measured 2026-09-15: `import Mathlib` printed a bare PROVED
    /// on both the sealed pack and HEAD; clean-elab logs the substitution at
    /// `warn`, and this lane installs no subscriber, so the notice was lost.
    standin_imports: Vec<String>,
}

impl FileVerdict {
    pub(crate) fn accepted(&self) -> bool {
        self.diagnostics.is_empty()
    }

    pub(crate) fn standin_imports(&self) -> &[String] {
        &self.standin_imports
    }

    pub(crate) fn path(&self) -> &Path {
        &self.path
    }

    pub(crate) fn diagnostics(&self) -> &[String] {
        &self.diagnostics
    }
}

/// What `check` reports for one file, terminal and JSON alike.
///
/// One invocation is one all-or-nothing Clean batch: a refusal anywhere
/// commits nothing, and the reference kernel recheck and the accepted-source
/// binding run only for an accepted batch. So a file with no diagnostic of its
/// own (every declaration in it kernel-checked) is still NOT accepted when the
/// batch was refused, and is never printed PROVED. This is the file row's
/// status in its `trust.obligations.v1` record (`records::file_status`):
/// `proved` only when the whole batch was accepted, `unknown`
/// (`not-dispatched`) for such a file.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum FileReport {
    /// The whole batch was accepted ([`CheckedLeanBatch::accepted_context`]).
    Proved,
    /// No diagnostic of its own, but its batch was refused by `refused_by`
    /// (the files with diagnostics; empty only when no file has one and the
    /// batch still yields no accepted context).
    NotAccepted { refused_by: Vec<PathBuf> },
    /// Its own diagnostics refused it (and so the batch).
    Rejected,
}

impl FileReport {
    /// The status word the JSON form carries.
    pub(crate) fn status(&self) -> &'static str {
        match self {
            Self::Proved => "proved",
            Self::NotAccepted { .. } => "not-accepted",
            Self::Rejected => "rejected",
        }
    }

    /// Why a [`Self::NotAccepted`] file is not accepted.
    fn refusal_reason(refused_by: &[PathBuf]) -> String {
        if refused_by.is_empty() {
            "its batch was refused: the checked batch has no accepted kernel context".to_string()
        } else {
            let names: Vec<String> =
                refused_by.iter().map(|path| path.display().to_string()).collect();
            format!("its batch was refused by {}", names.join(", "))
        }
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

/// The bytes read for a listed operand or an import-closure member. A failed
/// read is explicit, not an empty source that could be mistaken for checked.
#[derive(Debug)]
pub(crate) struct LeanSourceSnapshot {
    path: PathBuf,
    /// The module key this file supplies: a listed operand's file stem, or a
    /// pulled file's dotted module name exactly as imported. This is the key
    /// marked satisfied-from-source and the key the duplicate rule ranges over.
    module: String,
    source: Result<String, String>,
    /// Hash even malformed UTF-8 from the same read, never a later path reread.
    raw_sha256: Option<String>,
    raw_size: Option<usize>,
}

fn read_source(path: PathBuf, module: String) -> LeanSourceSnapshot {
    let (source, raw_sha256, raw_size) = match std::fs::read(&path) {
        Ok(bytes) => {
            let digest = trust_types::digest::stable_sha256_hex(&bytes);
            let size = bytes.len();
            // Preserve read_to_string's existing invalid-data diagnostic while
            // also retaining a hash of bytes that could not become Lean input.
            let source = String::from_utf8(bytes)
                .map_err(|_| "stream did not contain valid UTF-8".to_string());
            (source, Some(digest), Some(size))
        }
        Err(error) => (Err(error.to_string()), None, None),
    };
    LeanSourceSnapshot { path, module, source, raw_sha256, raw_size }
}

// These read-only accessors are preparation for the standalone lowering lane.
// They do not attest source authority or make the diagnostic census a gate.
#[allow(dead_code)]
impl LeanSourceSnapshot {
    pub(crate) fn path(&self) -> &Path {
        &self.path
    }

    pub(crate) fn module(&self) -> &str {
        &self.module
    }

    pub(crate) fn source(&self) -> Result<&str, &str> {
        self.source.as_deref().map_err(String::as_str)
    }
}

/// An unresolved import from the real elaborator, retained even when a later
/// source-read or closure-cap refusal prevents a final kernel attempt.
#[derive(Debug)]
pub(crate) struct UnresolvedLeanImport {
    source_path: PathBuf,
    module: String,
    diagnostic: String,
}

impl UnresolvedLeanImport {
    pub(crate) fn source_path(&self) -> &Path {
        &self.source_path
    }

    pub(crate) fn module(&self) -> &str {
        &self.module
    }

    pub(crate) fn diagnostic(&self) -> &str {
        &self.diagnostic
    }
}

/// Own the exact final fixed-point session and its inputs together. A refused
/// closure has no reusable context, even if an earlier attempt registered
/// some declarations. This is a checked source context, NOT G4 attestation,
/// runtime-body completeness, or permission to emit a native artifact.
pub(crate) struct CheckedLeanBatch {
    checked_source: Option<CheckedLeanSourceBatch>,
    sources: Vec<LeanSourceSnapshot>,
    aliases: Vec<LeanSourceAlias>,
    verdicts: Vec<FileVerdict>,
    unresolved_imports: Vec<UnresolvedLeanImport>,
    observation: Option<census::Observation>,
    /// Where the invocation's wall time went: one entry per kernel attempt of
    /// the import-closure fixpoint, and the whole batch. Never a verdict input.
    timing: LeanRunTiming,
}

/// The wall time of one Lean invocation's checking ([`check_batch`]).
#[derive(Debug, Clone, Default)]
pub(crate) struct LeanRunTiming {
    /// Each kernel attempt of the closure fixpoint, in order.
    pub(crate) attempts: Vec<LeanBatchTiming>,
    /// The whole batch, reading the operands included.
    pub(crate) total: std::time::Duration,
}

impl CheckedLeanBatch {
    pub(crate) fn sources(&self) -> &[LeanSourceSnapshot] {
        &self.sources
    }

    pub(crate) fn verdicts(&self) -> &[FileVerdict] {
        &self.verdicts
    }

    /// One [`FileReport`] per verdict row, in order.
    pub(crate) fn file_reports(&self) -> Vec<FileReport> {
        let batch_accepted = self.accepted_context().is_some();
        let refused_by: Vec<PathBuf> = self
            .verdicts
            .iter()
            .filter(|verdict| !verdict.accepted())
            .map(|verdict| verdict.path.clone())
            .collect();
        self.verdicts
            .iter()
            .map(|verdict| {
                if !verdict.accepted() {
                    FileReport::Rejected
                } else if batch_accepted {
                    FileReport::Proved
                } else {
                    FileReport::NotAccepted { refused_by: refused_by.clone() }
                }
            })
            .collect()
    }

    pub(crate) fn unresolved_imports(&self) -> &[UnresolvedLeanImport] {
        &self.unresolved_imports
    }

    pub(crate) fn timing(&self) -> &LeanRunTiming {
        &self.timing
    }

    /// The final attempt's per-source outcomes, when the batch was elaborated
    /// and they line up one-to-one with [`Self::sources`].
    pub(crate) fn outcomes(&self) -> Option<&[trust_certify::clean_island::CleanIslandOutcome]> {
        let outcomes = &self.checked_source.as_ref()?.attempt()?.outcomes;
        (outcomes.len() == self.sources.len()).then_some(outcomes.as_slice())
    }

    /// Optional final-attempt measurement only; never a source of authority.
    pub(crate) fn census(&self) -> Option<&serde_json::Value> {
        self.checked_source.as_ref()?.attempt()?.census.as_ref().map(|census| &census.report)
    }

    pub(crate) fn accepted_context(&self) -> Option<AcceptedLeanSourceContext<'_>> {
        let checked_source = self.checked_source.as_ref()?;
        let batch = checked_source.attempt()?;
        if self.sources.is_empty()
            || self.sources.len() != self.verdicts.len()
            || self.sources.len() != batch.outcomes.len()
            || self.sources.iter().any(|source| source.source.is_err())
            || self.verdicts.iter().any(|verdict| !verdict.accepted())
            || !self.unresolved_imports.is_empty()
            || batch.is_rejected()
        {
            return None;
        }
        let accepted = checked_source.accepted_context()?;
        if accepted.sources().len() != self.sources.len()
            || accepted.aliases() != self.aliases
            || accepted.sources().iter().zip(&self.sources).any(|(core, local)| {
                core.module != local.module
                    || core.path != local.path.display().to_string()
                    || local.source() != Ok(core.source.as_str())
            })
        {
            return None;
        }
        Some(accepted)
    }

    fn refused(
        sources: Vec<LeanSourceSnapshot>,
        aliases: Vec<LeanSourceAlias>,
        verdicts: Vec<FileVerdict>,
        unresolved_imports: Vec<UnresolvedLeanImport>,
        observation: Option<census::Observation>,
    ) -> Self {
        Self {
            checked_source: None,
            sources,
            aliases,
            verdicts,
            unresolved_imports,
            observation,
            timing: LeanRunTiming::default(),
        }
    }

    fn finished(
        checked_source: CheckedLeanSourceBatch,
        sources: Vec<LeanSourceSnapshot>,
        aliases: Vec<LeanSourceAlias>,
        verdicts: Vec<FileVerdict>,
        unresolved_imports: Vec<UnresolvedLeanImport>,
        observation: Option<census::Observation>,
    ) -> Self {
        Self {
            checked_source: Some(checked_source),
            sources,
            aliases,
            verdicts,
            unresolved_imports,
            observation,
            timing: LeanRunTiming::default(),
        }
    }
}

/// Whether two paths name the SAME FILE on disk.
///
/// Compared canonically, because the batch can reach one file by two routes: a
/// listed operand (keyed by its file stem) and an `import` the closure resolves
/// (keyed by its dotted module). Falling back to the literal paths keeps an
/// uncanonicalizable path from silently comparing equal to everything.
fn is_same_file(a: &Path, b: &Path) -> bool {
    match (std::fs::canonicalize(a), std::fs::canonicalize(b)) {
        (Ok(x), Ok(y)) => x == y,
        _ => a == b,
    }
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

/// The standalone check must not report a proved external dependency when the
/// kernel actually checked against a built-in stand-in. Keep the underlying
/// batch result intact for diagnostic build consumers, which have their own
/// artifact refusal, and refuse only this product-facing check verdict.
fn refuse_standin_imports_for_check(checked: &mut CheckedLeanBatch) {
    let Some(batch) = checked.checked_source.as_ref().and_then(CheckedLeanSourceBatch::attempt)
    else {
        return;
    };
    for ((source, verdict), outcome) in
        checked.sources.iter().zip(&mut checked.verdicts).zip(&batch.outcomes)
    {
        for import in &outcome.standin_imports {
            let location = source
                .source()
                .ok()
                .filter(|text| text.is_char_boundary(import.start))
                .map(|text| {
                    let (line, column) = line_and_column(text, import.start);
                    format!("{}:{line}:{column}", source.path.display())
                })
                .unwrap_or_else(|| source.path.display().to_string());
            verdict.diagnostics.push(format!(
                "{location}: `import {}` was served by Clean's built-in prelude \
                 stand-in, not the library of that name. Trust cannot accept this check: \
                 the external `.olean` dependency closure and its transitive axioms were \
                 not checked. Options: vendor needed declarations as a local `.lean` module \
                 with a non-stand-in name and import that module; remove the import if unused; \
                 or use `clean lake build` to compile against the real library (not a Trust proof)",
                import.module,
            ));
        }
    }
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
///
/// Retains the final import-closure check for a later lowering consumer. The
/// census remains opt-in; neither its presence nor its contents decide whether
/// the checked kernel context can be borrowed.
pub(crate) fn check_batch(paths: &[PathBuf], collect_census: bool) -> CheckedLeanBatch {
    check_batch_impl(paths, collect_census, false)
}

/// The same real source-import discovery/check loop with baseline observation
/// requested for each attempt. Refused earlier attempts cannot lend a context.
/// The census is NOT opt-in here, unlike in [`check_batch`] above: the
/// diagnostic runtime lane requires `--census`, so it is always collected.
pub(crate) fn check_batch_for_runtime(paths: &[PathBuf]) -> CheckedLeanBatch {
    check_batch_impl(paths, true, true)
}

fn check_batch_impl(
    paths: &[PathBuf],
    collect_census: bool,
    runtime_baseline: bool,
) -> CheckedLeanBatch {
    let started = std::time::Instant::now();
    let mut attempts = Vec::new();
    let mut checked = check_batch_attempts(paths, collect_census, runtime_baseline, &mut attempts);
    checked.timing = LeanRunTiming { attempts, total: started.elapsed() };
    checked
}

/// [`check_batch_impl`]'s closure fixpoint; pushes each kernel attempt's
/// timing to `attempts`.
fn check_batch_attempts(
    paths: &[PathBuf],
    collect_census: bool,
    runtime_baseline: bool,
    attempts: &mut Vec<LeanBatchTiming>,
) -> CheckedLeanBatch {
    let mut observation = collect_census.then(census::Observation::default);
    let wholesale = |members: &[LeanSourceSnapshot], refusal: &str| -> Vec<FileVerdict> {
        members
            .iter()
            .map(|member| FileVerdict {
                path: member.path.clone(),
                registered: Vec::new(),
                diagnostics: vec![refusal.to_string()],
                standin_imports: Vec::new(),
            })
            .collect()
    };

    // Listed operands first; an unreadable one refuses the whole invocation
    // (v7/D3: the refusal carries the fix, with options — and a batch missing
    // one unit could change what a sibling declaration MEANS, so no partial
    // batch runs).
    let mut members: Vec<LeanSourceSnapshot> = Vec::with_capacity(paths.len());
    let mut unreadable: Vec<String> = Vec::new();
    for path in paths {
        let module = path
            .file_stem()
            .and_then(|s| s.to_str())
            .map_or_else(|| path.display().to_string(), str::to_string);
        let member = read_source(path.clone(), module);
        if let Err(error) = &member.source {
            unreadable.push(format!("{}: {error}", path.display()));
        }
        members.push(member);
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
        return CheckedLeanBatch::refused(members, Vec::new(), verdicts, Vec::new(), observation);
    }

    // The closure fixpoint. Each iteration marks every member's module key
    // satisfied-from-source (W2/lean-sibling-imports) and batch-checks; the
    // elaborator's own unresolved-import refusals then name exactly the
    // modules still missing, and any that resolve to a `.lean` file relative
    // to an importing member's directory are pulled as new members. A module
    // that stays unresolvable keeps the verbatim refusal in the final render.
    // Each iteration adds a member or a new same-file alias (else it returns),
    // and the cap fails CLOSED if that fixed point does not settle.
    const CLOSURE_ITERATION_CAP: usize = 64;
    let mut unresolved_imports = Vec::new();
    // Modules supplied by a file that is ALREADY a member under a different
    // key. They are marked satisfied like any member module, but they mint no
    // second member — see the pull site below.
    let mut aliases: Vec<LeanSourceAlias> = Vec::new();
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
            let verdicts = wholesale(&members, &refusal);
            return CheckedLeanBatch::refused(
                members,
                aliases,
                verdicts,
                unresolved_imports,
                observation,
            );
        }

        let inputs = members
            .iter()
            .map(|member| LeanSourceInput {
                module: member.module.clone(),
                path: member.path.display().to_string(),
                source: member
                    .source()
                    .expect("unreadable source refused before elaboration")
                    .to_owned(),
            })
            .collect();
        let checked_source = if runtime_baseline {
            CheckedLeanSourceBatch::check_with_aliases_and_runtime_baseline(
                inputs,
                aliases.clone(),
                collect_census,
            )
        } else {
            CheckedLeanSourceBatch::check_with_aliases(inputs, aliases.clone(), collect_census)
        };
        attempts.push(checked_source.timing().clone());
        if let Some(observation) = &mut observation {
            observation.record_attempt(&checked_source);
        }
        if !checked_source.errors().is_empty() || checked_source.attempt().is_none() {
            let refusal = format!("batch refused: {}", checked_source.errors().join("; "));
            let verdicts = wholesale(&members, &refusal);
            return CheckedLeanBatch::finished(
                checked_source,
                members,
                aliases,
                verdicts,
                unresolved_imports,
                observation,
            );
        }
        let batch = checked_source.attempt().expect("checked attempt above");

        unresolved_imports = members
            .iter()
            .zip(&batch.outcomes)
            .flat_map(|(member, outcome)| {
                outcome.errors.iter().filter_map(|error| {
                    let module = unresolved_import_module(&error.message)?;
                    Some(UnresolvedLeanImport {
                        source_path: member.path.clone(),
                        module: module.to_string(),
                        diagnostic: error.message.clone(),
                    })
                })
            })
            .collect();

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
                        let (line, column) =
                            line_and_column(member.source().expect("checked source"), site.start);
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
            let verdicts = members
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
                    FileVerdict {
                        path: member.path.clone(),
                        registered: Vec::new(),
                        diagnostics,
                        standin_imports: Vec::new(),
                    }
                })
                .collect();
            return CheckedLeanBatch::finished(
                checked_source,
                members,
                aliases,
                verdicts,
                unresolved_imports,
                observation,
            );
        }

        // DISCOVERY: modules the elaborator refused as unresolved, resolved
        // relative to the directory of the member whose diagnostic named them.
        let mut pulls: Vec<(PathBuf, String)> = Vec::new();
        let mut newly_satisfied = false;
        for (member, outcome) in members.iter().zip(&batch.outcomes) {
            for error in &outcome.errors {
                let Some(module) = unresolved_import_module(&error.message) else { continue };
                if by_module.contains_key(module)
                    || pulls.iter().any(|(_, pulled)| pulled == module)
                    || aliases.iter().any(|known| known.module == module)
                {
                    continue;
                }
                let mut candidate =
                    member.path.parent().map_or_else(PathBuf::new, Path::to_path_buf);
                for segment in module.split('.') {
                    candidate.push(segment);
                }
                let candidate = candidate.with_extension("lean");
                let is_file = candidate.is_file();
                if let Some(observation) = &mut observation {
                    observation.record_discovery(member, module, &candidate, is_file);
                }
                if !is_file {
                    continue;
                }
                // ONE FILE IS ONE MEMBER. A directory operand lists
                // `Sub/Leaf.lean` under the stem `Leaf`, and an `import
                // Sub.Leaf` in a sibling resolves to that SAME file under the
                // dotted key. Pushing it again put the file's source into the
                // batch twice, so every declaration in it registered twice and
                // the kernel reported `declared twice in this batch` — a
                // confident REJECTED for a directory that is perfectly fine.
                // Record the module as satisfied instead, and let the loop run
                // once more so the elaborator sees it resolved.
                let source_index = members
                    .iter()
                    .position(|member| is_same_file(&member.path, &candidate))
                    .or_else(|| {
                        pulls
                            .iter()
                            .position(|(path, _)| is_same_file(path, &candidate))
                            .map(|index| members.len() + index)
                    });
                if let Some(source_index) = source_index {
                    aliases.push(LeanSourceAlias { module: module.to_string(), source_index });
                    newly_satisfied = true;
                    continue;
                }
                pulls.push((candidate, module.to_string()));
            }
        }
        if pulls.is_empty() && !newly_satisfied {
            // Fixpoint: render the final verdicts over every member — pulled
            // files included, each with its own row (the disclosure).
            //
            // The checked batch reports stand-ins from its full parsed source,
            // including imports after declarations and inside nested commands.
            // Do not reconstruct that record from a header-only source scan.
            let verdicts = members
                .iter()
                .zip(&batch.outcomes)
                .map(|(member, outcome)| {
                    let diagnostics = outcome
                        .errors
                        .iter()
                        .map(|error| {
                            let (line, column) = line_and_column(
                                member.source().expect("checked source"),
                                error.start,
                            );
                            format!("{}:{line}:{column}: {}", member.path.display(), error.message)
                        })
                        .collect();
                    let standin_imports = outcome
                        .standin_imports
                        .iter()
                        .map(|import| import.module.clone())
                        .collect();
                    FileVerdict {
                        path: member.path.clone(),
                        registered: outcome.registered.clone(),
                        diagnostics,
                        standin_imports,
                    }
                })
                .collect();
            return CheckedLeanBatch::finished(
                checked_source,
                members,
                aliases,
                verdicts,
                unresolved_imports,
                observation,
            );
        }
        for (path, module) in pulls {
            let member = read_source(path, module);
            match &member.source {
                Ok(_) => members.push(member),
                Err(error) => {
                    let path = &member.path;
                    let module = &member.module;
                    let refusal = format!(
                        "batch refused: `import {module}` resolves to {} but it cannot be \
                         read ({error}). Options: fix the file, or remove the import",
                        path.display(),
                    );
                    let verdicts = wholesale(&members, &refusal);
                    // Preserve the failed read too, but do not add a new CLI
                    // verdict row: the existing wholesale refusal is unchanged.
                    members.push(member);
                    return CheckedLeanBatch::refused(
                        members,
                        aliases,
                        verdicts,
                        unresolved_imports,
                        observation,
                    );
                }
            }
        }
    }
    let refusal = format!(
        "batch refused: the import closure did not settle within \
         {CLOSURE_ITERATION_CAP} iterations. This is a fail-closed cap, not a \
         verdict; report this invocation's file graph",
    );
    let verdicts = wholesale(&members, &refusal);
    CheckedLeanBatch::refused(members, aliases, verdicts, unresolved_imports, observation)
}

/// Reject obvious output failures before expensive kernel work, without
/// creating anything. This is only a usability preflight: `write_census` must
/// still use exclusive creation because the filesystem may change meanwhile.
pub(crate) fn preflight_census(path: &Path) -> Result<(), String> {
    match std::fs::symlink_metadata(path) {
        Ok(_) => {
            return Err(format!(
                "{} already exists; --census requires a new output path",
                path.display()
            ));
        }
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
        Err(error) => return Err(format!("{}: {error}", path.display())),
    }
    let parent = path
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
        .unwrap_or_else(|| Path::new("."));
    let metadata = std::fs::metadata(parent)
        .map_err(|error| format!("census output parent {}: {error}", parent.display()))?;
    if !metadata.is_dir() {
        return Err(format!("census output parent {} is not a directory", parent.display()));
    }
    #[cfg(unix)]
    {
        use std::os::unix::ffi::OsStrExt;
        let encoded = std::ffi::CString::new(parent.as_os_str().as_bytes())
            .map_err(|error| format!("census output parent {}: {error}", parent.display()))?;
        // SAFETY: the CString is NUL-terminated and lives through this call.
        // access only observes permissions; the final create_new is authority.
        if unsafe { libc::access(encoded.as_ptr(), libc::W_OK | libc::X_OK) } != 0 {
            return Err(format!(
                "census output parent {}: {}",
                parent.display(),
                std::io::Error::last_os_error()
            ));
        }
    }
    Ok(())
}

/// Diagnostic output must never overwrite an input or an earlier measurement.
/// Serialize first, so serialization errors cannot create a truncated report.
pub(crate) fn write_census(path: &Path, report: &serde_json::Value) -> Result<(), String> {
    use std::io::Write;
    let mut bytes = serde_json::to_vec_pretty(report).map_err(|error| error.to_string())?;
    bytes.push(b'\n');
    let parent = path.parent().filter(|p| !p.as_os_str().is_empty()).unwrap_or(Path::new("."));
    let mut file = tempfile::NamedTempFile::new_in(parent).map_err(|error| error.to_string())?;
    file.write_all(&bytes).map_err(|error| format!("{}: {error}", path.display()))?;
    file.as_file().sync_all().map_err(|error| error.to_string())?;
    file.persist_noclobber(path).map_err(|error| {
        format!("{}: {}; --census requires a new output path", path.display(), error.error)
    })?;
    Ok(())
}

/// The JSON form of a check: per file, the same [`FileReport`] the terminal
/// form prints. `accepted` is true only for a `proved` file; a `not-accepted`
/// file names the files whose refusal refused its batch, and its `registered`
/// names what the kernel checked in that refused batch, which commits nothing.
fn render_json(checked: &CheckedLeanBatch) -> String {
    let reports = checked.file_reports();
    let files = checked
        .verdicts()
        .iter()
        .zip(&reports)
        .map(|(verdict, report)| {
            let refused_by: Vec<String> = match report {
                FileReport::NotAccepted { refused_by } => {
                    refused_by.iter().map(|path| path.display().to_string()).collect()
                }
                FileReport::Proved | FileReport::Rejected => Vec::new(),
            };
            serde_json::json!({
                "path": verdict.path.display().to_string(),
                "status": report.status(),
                "accepted": *report == FileReport::Proved,
                "batch_refused_by": refused_by,
                "registered": verdict.registered,
                "diagnostics": verdict.diagnostics,
                "standin_imports": verdict.standin_imports(),
            })
        })
        .collect::<Vec<_>>();
    let count = |wanted: fn(&FileReport) -> bool| reports.iter().filter(|r| wanted(r)).count();
    serde_json::json!({
        "language": "clean",
        "checker": "in-process clean kernel (trust-certify)",
        "import_search": "local-source-only",
        "external_olean_imports": "unsupported",
        "files": files,
        "accepted": count(|report| *report == FileReport::Proved),
        "not_accepted": count(|report| matches!(report, FileReport::NotAccepted { .. })),
        "rejected": count(|report| *report == FileReport::Rejected),
    })
    .to_string()
}

/// `targo trust check <file.lean> …`
///
/// All operands of one invocation are checked as ONE batch ([`check_batch`]),
/// so cross-file citations within the invocation resolve; separate
/// invocations stay isolated.
/// `--census NEW_PATH` writes an independent owned-kernel roster over the final
/// source-import closure. It is diagnostic only, not a runtime-body denominator
/// or a replacement for this check's verdict, and never overwrites a file.
///
/// Fail-closed in every direction: an unreadable file (which refuses the whole
/// batch), a parse error, a dependency cycle, a declaration the kernel
/// rejects, and an assumption (`axiom`, `sorry`, a valueless `opaque`, a
/// `partial`/`unsafe` marker) all exit non-zero. A file is reported PROVED
/// only when the whole batch was accepted: the CIC kernel accepted every
/// declaration of every file with no trust debt in the reachable closure, and
/// the batch's final acceptance checks passed. A file with no diagnostic of its
/// own in a refused batch is reported NOT ACCEPTED ([`FileReport`]).
pub(crate) fn run_check(args: &[String]) -> ExitCode {
    let request = match parse(args) {
        Ok(request) => request,
        Err(error) => {
            eprintln!("targo trust check: {error}");
            return ExitCode::from(2);
        }
    };

    if let Some(path) = &request.census_output {
        if let Err(error) = preflight_census(path) {
            eprintln!("targo trust check: cannot write diagnostic census: {error}");
            return ExitCode::from(2);
        }
    }

    let tool_before = if request.census_output.is_some() {
        match census::tool_identity() {
            Ok(identity) => Some(identity),
            Err(error) => {
                eprintln!("targo trust check: cannot bind census tool image: {error}");
                return ExitCode::from(2);
            }
        }
    } else {
        None
    };
    let mut checked = check_batch(&request.files, request.census_output.is_some());
    refuse_standin_imports_for_check(&mut checked);
    let verdicts = checked.verdicts();
    let reports = checked.file_reports();
    // Success is every file PROVED: the whole batch accepted. A file with no
    // diagnostic of its own beside a refused sibling is not (`FileReport`).
    let all_proved = reports.iter().all(|report| *report == FileReport::Proved);
    // Observational, as the Rust lane's records are: a write failure is
    // reported, never a verdict and never an exit status.
    let registered: Vec<String> =
        verdicts.iter().flat_map(|verdict| verdict.registered.iter().cloned()).collect();
    // One target directory for every record this check writes (the timing
    // record here, the obligation records and snapshots below). Outside every
    // workspace with none named, nothing is written and one `note:` says why.
    let target_dir = records::record_target_dir(request.target_dir.as_deref())
        .map_err(|error| {
            format!("no record written: {error}; pass --target-dir DIR to keep this run's records")
        })
        .and_then(|dir| dir.ok_or_else(|| records::NO_TARGET_DIR.to_string()));
    if let Ok(target_dir) = &target_dir {
        if let Err(error) =
            run_record::write(target_dir, &request.files, all_proved, &registered, checked.timing())
        {
            eprintln!(
                "targo trust check: warning: could not write the Lean run record under \
                 `{}`: {error}",
                run_record::records_dir(target_dir).display()
            );
        }
    }

    if let Some(path) = &request.census_output {
        let external = match census::observe_external(&checked, &request.olean_paths, &[path]) {
            Ok(external) => external,
            Err(error) => {
                eprintln!("targo trust check: cannot publish diagnostic census: {error}");
                return ExitCode::from(2);
            }
        };
        let tool_after =
            census::tool_identity().unwrap_or_else(|error| serde_json::json!({"error": error}));
        let tool_before = tool_before.as_ref().expect("requested observation");
        let mut report =
            census::report(&checked, &request.files, "check", tool_before, &tool_after);
        if let Some(external) = external {
            report["external_olean_observation"] = external;
        }
        if let Err(error) = write_census(path, &report) {
            eprintln!("targo trust check: cannot write diagnostic census: {error}");
            return ExitCode::from(2);
        }
        if tool_before != &tool_after {
            eprintln!(
                "targo trust check: census tool image changed or became unreadable; diagnostic report retained"
            );
            return ExitCode::from(2);
        }
    }

    // Live-edit-loop step 2: one `trust.obligations.v1` record per file (a row
    // for the file's verdict and one per declaration Clean parsed), written and
    // snapshotted for the changed-only view only when the caller asked for it:
    // a caller session, `--since` or `--target-dir`. Observational: no verdict
    // or exit status reads it.
    let caller = crate::agent_delta::caller_session_from_env();
    let mut delta = crate::agent_delta::DeltaView::default();
    let wants_delta =
        caller.is_some() || request.delta.since.is_some() || request.target_dir.is_some();
    match &target_dir {
        Ok(target_dir) if wants_delta => {
            let file_records = records::file_records(&checked);
            for (package, bytes) in &file_records {
                let path = records::record_path(target_dir, package);
                let written =
                    path.parent().map_or(Ok(()), std::fs::create_dir_all).and_then(|()| {
                        crate::durable_io::atomic_write_private(&path, bytes.as_bytes())
                    });
                if let Err(error) = written {
                    eprintln!(
                        "targo trust check: warning: could not write the obligation record \
                         `{}`: {error}",
                        path.display()
                    );
                }
            }
            delta = crate::agent_delta::publish(
                target_dir,
                &file_records,
                &request.delta,
                caller.as_deref(),
                true,
            );
        }
        Ok(_) => {}
        // The one note for both records: with the changed-only view it is
        // the view's own note, printed with it; otherwise on stderr, so the
        // verdict lines a caller reads are what they were.
        Err(why) if wants_delta => delta.notes.push(why.clone()),
        Err(why) => eprintln!("note: {why}"),
    }

    if request.json {
        println!("{}", render_json(&checked));
        for line in delta.lines() {
            eprintln!("{line}");
        }
    } else {
        for verdict in verdicts {
            for diagnostic in &verdict.diagnostics {
                eprintln!("error: {diagnostic}");
            }
        }
        for (verdict, report) in verdicts.iter().zip(&reports) {
            match report {
                FileReport::Proved => println!(
                    "PROVED {} — {} declaration(s) kernel-checked",
                    verdict.path.display(),
                    verdict.registered.len()
                ),
                // The count is information only: the kernel checked these
                // declarations in a batch that committed nothing.
                FileReport::NotAccepted { refused_by } => println!(
                    "NOT ACCEPTED {} — {}; {} declaration(s) kernel-checked in the refused \
                     batch, none accepted",
                    verdict.path.display(),
                    FileReport::refusal_reason(refused_by),
                    verdict.registered.len()
                ),
                FileReport::Rejected => println!("REJECTED {}", verdict.path.display()),
            }
        }
        for line in delta.lines() {
            println!("{line}");
        }
        // The import surface is a capability boundary, not a footnote: this
        // lane checks local source imports, not external .olean libraries.
        println!(
            "checked in process by the Clean CIC kernel; `.lean` imports resolve from local \
             source only; external `.olean` imports are unsupported"
        );
        if !request.lake_dirs.is_empty() {
            println!(
                "note: {} operand(s) hold a `lakefile.lean`. Lake's dependency \
                 resolution is NOT used here: this lane checks the project's own \
                 `.lean` sources in process and resolves no external `.olean`, so a \
                 module importing `Std` or a Lake dependency is REJECTED as \
                 unresolved rather than checked. Options: name the self-contained \
                 files directly; vendor the dependency's source so it is \
                 crate-local; or run `clean lake build`, which COMPILES and judges \
                 nothing -- a successful build is not a discharged proof.",
                request.lake_dirs.len()
            );
        }
    }

    if all_proved { ExitCode::SUCCESS } else { ExitCode::FAILURE }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `run_check` with its `trust.lean-run.v1` record under `--target-dir`
    /// beside the first operand, in the test's own temporary directory, so an
    /// in-process check writes nothing into the workspace's target directory.
    fn run_check_scratch(args: &[String]) -> ExitCode {
        let target = Path::new(&args[0]).parent().expect("an operand path").join("target");
        let mut args = args.to_vec();
        args.extend(["--target-dir".to_string(), target.display().to_string()]);
        run_check(&args)
    }

    /// [`check_batch`] reduced to its verdict rows, without the census.
    fn check_files(paths: &[PathBuf]) -> Vec<FileVerdict> {
        check_files_impl(paths, None)
    }

    /// [`check_batch`] reduced to its verdict rows, copying the census into
    /// `census` when one is requested.
    fn check_files_impl(
        paths: &[PathBuf],
        census: Option<&mut serde_json::Value>,
    ) -> Vec<FileVerdict> {
        let checked = check_batch(paths, census.is_some());
        if let (Some(destination), Some(report)) = (census, checked.census()) {
            *destination = report.clone();
        }
        checked.verdicts
    }

    fn args(items: &[&str]) -> Vec<String> {
        items.iter().map(|item| (*item).to_string()).collect()
    }

    // The stand-in DISCLOSURE fixtures below import `Lean`, the eligible
    // stand-in. TG8-REFERENCE-ISLANDS-2 (6411a62394) made the `Mathlib`
    // stand-in an ineligible reference base: it installs a structural
    // `IsClosed` record, so a batch that imports it is refused whole before
    // anything can be disclosed. trust-certify's own disclosure controls moved
    // to `import Lean` then (7d407f631b, f477b4ece7); these did not, and were
    // red with "reference base refused: StructuralProvenance { .. IsClosed .. }".
    // What they check is unchanged: a stand-in import on an ACCEPTED row is
    // disclosed, and `check` refuses it. The `Mathlib` refusal is pinned by
    // `checked_batch_refuses_every_mathlib_standin_spelling_as_an_ineligible_base`.

    #[test]
    fn checked_batch_discloses_a_prelude_stand_in_import_on_an_accepted_file() {
        let dir = tempfile::tempdir().unwrap();
        let with_standin = dir.path().join("WithLean.lean");
        let with_helper = dir.path().join("Main.lean");
        let helper = dir.path().join("Helper.lean");
        std::fs::write(
            &with_standin,
            "module\npublic import Lean\ndef sq (n : Nat) : Nat := n * n\n",
        )
        .unwrap();
        std::fs::write(&with_helper, "import Helper\ndef uses : Nat := base\n").unwrap();
        std::fs::write(&helper, "def base : Nat := 7\n").unwrap();

        let checked = check_batch(&[with_standin.clone(), with_helper.clone()], false);
        let verdicts = checked.verdicts();
        let standin = verdicts.iter().find(|v| v.path() == with_standin).expect("row");
        assert!(standin.accepted(), "{:?}", standin.diagnostics());
        assert_eq!(standin.standin_imports(), ["Lean".to_string()]);
        let main = verdicts.iter().find(|v| v.path() == with_helper).expect("row");
        assert!(main.accepted(), "{:?}", main.diagnostics());
        assert!(main.standin_imports().is_empty(), "a pulled local module is not a stand-in");
        let rendered = render_json(&checked);
        assert!(rendered.contains("\"standin_imports\":[\"Lean\"]"), "{rendered}");
    }

    #[test]
    fn checked_batch_discloses_late_import_without_comment_or_identifier_false_positives() {
        let dir = tempfile::tempdir().unwrap();
        let late = dir.path().join("Late.lean");
        let plain = dir.path().join("Plain.lean");
        std::fs::write(&late, "def before : Nat := 1\nimport Lean\ndef after : Nat := 2\n")
            .unwrap();
        std::fs::write(
            &plain,
            "/- import Mathlib -/\n-- import Lean\ndef importCounter : Nat := 3\n",
        )
        .unwrap();

        let checked = check_batch(&[late.clone(), plain.clone()], true);
        let late_row = checked.verdicts().iter().find(|row| row.path() == late).unwrap();
        let plain_row = checked.verdicts().iter().find(|row| row.path() == plain).unwrap();
        assert!(late_row.accepted(), "{:?}", late_row.diagnostics());
        assert!(plain_row.accepted(), "{:?}", plain_row.diagnostics());
        assert_eq!(late_row.standin_imports(), ["Lean".to_string()]);
        assert!(plain_row.standin_imports().is_empty());
        let report: serde_json::Value = serde_json::from_str(&render_json(&checked)).unwrap();
        assert_eq!(report["files"][0]["standin_imports"], serde_json::json!(["Lean"]));
        assert_eq!(report["files"][1]["standin_imports"], serde_json::json!([]));
    }

    #[test]
    fn checked_batch_discloses_transitive_public_meta_import() {
        let dir = tempfile::tempdir().unwrap();
        let main = dir.path().join("Main.lean");
        let helper = dir.path().join("Helper.lean");
        std::fs::write(&main, "import Helper\ndef mainValue : Nat := helperValue\n").unwrap();
        std::fs::write(&helper, "module\npublic meta import Lean\ndef helperValue : Nat := 1\n")
            .unwrap();

        let checked = check_batch(&[main], false);
        let helper_row = checked.verdicts().iter().find(|row| row.path() == helper).unwrap();
        assert!(helper_row.accepted(), "{:?}", helper_row.diagnostics());
        assert_eq!(helper_row.standin_imports(), ["Lean".to_string()]);
    }

    #[test]
    fn checked_batch_discloses_imports_inside_set_option_and_open() {
        let dir = tempfile::tempdir().unwrap();
        let set_option = dir.path().join("SetOption.lean");
        let open = dir.path().join("Open.lean");
        let comments = dir.path().join("Comments.lean");
        std::fs::write(
            &set_option,
            "def setValue : Nat := 1\nset_option maxHeartbeats 400000 in import Lean\n",
        )
        .unwrap();
        std::fs::write(&open, "def openValue : Nat := 2\nopen Nat in import Lean\n").unwrap();
        std::fs::write(
            &comments,
            "/- set_option maxHeartbeats 400000 in import Lean -/\n\
             -- open Nat in import Lean\ndef importCounter : Nat := 3\n",
        )
        .unwrap();

        let checked = check_batch(&[set_option.clone(), open.clone(), comments.clone()], true);
        for (path, expected) in
            [(set_option, &["Lean"][..]), (open, &["Lean"][..]), (comments, &[][..])]
        {
            let row = checked.verdicts().iter().find(|row| row.path() == path).unwrap();
            assert!(row.accepted(), "{}: {:?}", path.display(), row.diagnostics());
            assert_eq!(row.standin_imports(), expected, "{}", path.display());
        }
        let report: serde_json::Value = serde_json::from_str(&render_json(&checked)).unwrap();
        assert_eq!(report["files"][0]["standin_imports"], serde_json::json!(["Lean"]));
        assert_eq!(report["files"][1]["standin_imports"], serde_json::json!(["Lean"]));
        assert_eq!(report["files"][2]["standin_imports"], serde_json::json!([]));
    }

    #[test]
    fn check_refuses_standin_even_with_an_external_olean_candidate() {
        let dir = tempfile::tempdir().unwrap();
        let input = dir.path().join("Main.lean");
        let output = dir.path().join("census.json");
        std::fs::write(&input, "module\npublic import Lean\ndef value : Nat := 1\n").unwrap();
        std::fs::write(dir.path().join("Lean.olean"), b"not an attested olean").unwrap();

        let mut checked = check_batch(std::slice::from_ref(&input), true);
        assert!(checked.accepted_context().is_some(), "kernel checked the stand-in");
        refuse_standin_imports_for_check(&mut checked);
        assert!(checked.accepted_context().is_none());
        assert_eq!(checked.verdicts()[0].standin_imports(), ["Lean"]);
        let diagnostic = &checked.verdicts()[0].diagnostics()[0];
        assert!(diagnostic.starts_with(&format!("{}:2:8:", input.display())), "{diagnostic}");
        for expected in [
            "`import Lean` was served by Clean's built-in prelude stand-in",
            "external `.olean` dependency closure and its transitive axioms were not checked",
            "Options: vendor needed declarations",
            "remove the import if unused",
            "not a Trust proof",
        ] {
            assert!(diagnostic.contains(expected), "{diagnostic}");
        }
        let json: serde_json::Value = serde_json::from_str(&render_json(&checked)).unwrap();
        assert_eq!(json["accepted"], 0);
        assert_eq!(json["rejected"], 1);
        assert_eq!(json["files"][0]["accepted"], false);
        assert_eq!(json["files"][0]["standin_imports"], serde_json::json!(["Lean"]));

        assert_eq!(
            run_check_scratch(&[
                input.display().to_string(),
                "--json".into(),
                "--census".into(),
                output.display().to_string(),
                "--census-olean-path".into(),
                dir.path().display().to_string(),
            ]),
            ExitCode::FAILURE,
        );
        let report: serde_json::Value =
            serde_json::from_slice(&std::fs::read(output).unwrap()).unwrap();
        assert_eq!(report["authority"], "diagnostic-only");
        assert_eq!(report["check_report"]["rejected"], 1);
        assert_eq!(report["source_graph"]["source_closure_accepted"], false);
        assert!(report.get("external_olean_observation").is_some());
    }

    // A modified import requires a module header and belongs before commands.
    // Keep these refusals separate from the valid stand-in disclosure fixtures.
    #[test]
    fn checked_batch_refuses_modified_imports_outside_a_module_header() {
        for (source, expected) in [
            (
                "public import Mathlib\ndef value : Nat := 1\n",
                "cannot use `public import` without `module`",
            ),
            (
                "meta import Mathlib\ndef value : Nat := 1\n",
                "cannot use `meta import` without `module`",
            ),
            (
                "module\ndef value : Nat := 1\npublic meta import Mathlib\n",
                "unexpected token 'import'",
            ),
        ] {
            let dir = tempfile::tempdir().unwrap();
            let input = dir.path().join("Main.lean");
            std::fs::write(&input, source).unwrap();
            let checked = check_batch(std::slice::from_ref(&input), false);
            assert!(checked.accepted_context().is_none(), "{source}");
            let verdict = &checked.verdicts()[0];
            assert!(!verdict.accepted(), "{source}");
            assert!(
                verdict.diagnostics().iter().any(|diagnostic| diagnostic.contains(expected)),
                "{source}: {:?}",
                verdict.diagnostics()
            );
            assert_eq!(
                run_check_scratch(&[input.display().to_string(), "--json".into()]),
                ExitCode::FAILURE,
            );
        }
    }

    #[test]
    fn check_refuses_a_transitive_standin_but_accepts_local_source_imports() {
        let dir = tempfile::tempdir().unwrap();
        let main = dir.path().join("Main.lean");
        let helper = dir.path().join("Helper.lean");
        std::fs::write(&main, "import Helper\ndef value : Nat := helperValue\n").unwrap();
        std::fs::write(&helper, "module\npublic meta import Lean\ndef helperValue : Nat := 1\n")
            .unwrap();

        let mut checked = check_batch(std::slice::from_ref(&main), false);
        refuse_standin_imports_for_check(&mut checked);
        assert!(checked.accepted_context().is_none());
        assert!(checked.verdicts()[0].accepted(), "the local importer has no stand-in");
        let helper_row = checked.verdicts().iter().find(|row| row.path() == helper).unwrap();
        assert!(!helper_row.accepted());
        assert!(
            helper_row.diagnostics()[0].starts_with(&format!("{}:2:13:", helper.display())),
            "{:?}",
            helper_row.diagnostics()
        );
        assert_eq!(
            run_check_scratch(&[main.display().to_string(), "--json".into()]),
            ExitCode::FAILURE
        );

        std::fs::write(&helper, "def helperValue : Nat := 1\n").unwrap();
        let mut local = check_batch(std::slice::from_ref(&main), false);
        refuse_standin_imports_for_check(&mut local);
        assert!(local.accepted_context().is_some());
        assert!(local.verdicts().iter().all(FileVerdict::accepted));
        assert_eq!(
            run_check_scratch(&[main.display().to_string(), "--json".into()]),
            ExitCode::SUCCESS
        );
    }

    #[test]
    fn check_standin_refusal_survives_a_lost_source_snapshot() {
        let dir = tempfile::tempdir().unwrap();
        let input = dir.path().join("Main.lean");
        std::fs::write(&input, "import Lean\ndef value : Nat := 1\n").unwrap();
        let mut checked = check_batch(std::slice::from_ref(&input), false);
        assert!(checked.verdicts()[0].accepted(), "{:?}", checked.verdicts()[0].diagnostics());
        checked.sources[0].source = Err("source read failed after check".into());

        refuse_standin_imports_for_check(&mut checked);
        assert!(checked.accepted_context().is_none());
        assert!(!checked.verdicts()[0].accepted());
        assert!(
            checked.verdicts()[0].diagnostics()[0]
                .starts_with(&format!("{}: `import Lean`", input.display()))
        );
    }

    /// The negative twin of the `Lean` disclosure fixtures above
    /// (TG8-REFERENCE-ISLANDS-2): every `Mathlib` spelling they used to carry
    /// is still REFUSED, now by the kernel lane itself, because the `Mathlib`
    /// stand-in is an ineligible reference base. The refusal comes before the
    /// `check` front door's stand-in refusal and a refused row reports no
    /// green, so nothing is disclosed as a stand-in either.
    #[test]
    fn checked_batch_refuses_every_mathlib_standin_spelling_as_an_ineligible_base() {
        for source in [
            "import Mathlib\ndef value : Nat := 1\n",
            "module\npublic import Mathlib\ndef value : Nat := 1\n",
            "module\npublic meta import Mathlib\ndef value : Nat := 1\n",
            "def value : Nat := 1\nimport Mathlib\n",
            "def value : Nat := 1\nset_option maxHeartbeats 400000 in import Mathlib\n",
            "def value : Nat := 1\nopen Nat in import Mathlib\n",
        ] {
            let dir = tempfile::tempdir().unwrap();
            let input = dir.path().join("Main.lean");
            std::fs::write(&input, source).unwrap();
            let checked = check_batch(std::slice::from_ref(&input), false);
            assert!(checked.accepted_context().is_none(), "{source}");
            let verdict = &checked.verdicts()[0];
            assert!(!verdict.accepted(), "{source}");
            assert!(
                verdict.diagnostics().iter().any(|diagnostic| {
                    diagnostic.contains("reference base refused")
                        && diagnostic.contains("StructuralProvenance")
                }),
                "{source}: {:?}",
                verdict.diagnostics()
            );
            assert!(verdict.standin_imports().is_empty(), "{source}");
            assert_eq!(
                run_check_scratch(&[input.display().to_string(), "--json".into()]),
                ExitCode::FAILURE,
            );
        }
    }

    #[test]
    fn checked_batch_retains_exact_final_environment_and_source_snapshots() {
        let dir = tempfile::tempdir().unwrap();
        let main = dir.path().join("Main.lean");
        let helper = dir.path().join("Helper.lean");
        let main_source = "import Helper\ndef uses : Nat := base\n";
        let helper_source = "def base : Nat := 7\n";
        std::fs::write(&main, main_source).unwrap();
        std::fs::write(&helper, helper_source).unwrap();
        let mut checked = check_batch(std::slice::from_ref(&main), true);
        let accepted = checked.accepted_context().expect("complete source closure accepted");
        let env = accepted.environment();
        assert!(std::ptr::eq(
            env,
            checked.checked_source.as_ref().unwrap().accepted_context().unwrap().environment()
        ));
        assert!(checked.unresolved_imports().is_empty(), "discarded attempts do not leak");
        assert_eq!(accepted.sources().len(), 2);
        assert_eq!(accepted.sources()[0].path, main.display().to_string());
        assert_eq!(accepted.sources()[1].module, "Helper");
        for name in ["uses", "base"] {
            let info = env.constants().find(|info| info.name.to_string() == name).unwrap();
            assert!(info.value.is_some(), "retain the typed computational body for {name}");
        }
        let report = checked.census().unwrap();
        for (input, snapshot) in report["inputs"].as_array().unwrap().iter().zip(checked.sources())
        {
            assert_eq!(input["path"], snapshot.path().display().to_string());
            assert_eq!(input["module"], snapshot.module());
            assert_eq!(
                input["sha256"],
                trust_types::digest::stable_sha256_hex(snapshot.source().unwrap().as_bytes())
            );
        }
        assert_eq!(report["denominator_status"], "denominator_unverified");

        // A later consumer borrows these checked bytes, never rereads the path.
        std::fs::write(&main, "axiom changedAfterCheck : False\n").unwrap();
        std::fs::remove_file(&helper).unwrap();
        assert_eq!(accepted.sources()[0].source, main_source);
        assert_eq!(accepted.sources()[1].source, helper_source);
        assert!(!env.constants().any(|info| info.name.to_string() == "changedAfterCheck"));
        assert!(checked.accepted_context().is_some());
        // The CLI cannot accidentally pair different snapshots with the core's
        // accepted environment even if a later internal edit changes a member.
        let accepted_report: serde_json::Value = serde_json::from_str(&render_json(&checked)).unwrap();
        assert_eq!(accepted_report["accepted"], 2);
        checked.sources[0].source = Ok("def substituted : Nat := 0\n".into());
        assert!(checked.accepted_context().is_none());
        assert!(checked.verdicts().iter().all(FileVerdict::accepted));
        let refused_report: serde_json::Value = serde_json::from_str(&render_json(&checked)).unwrap();
        assert_eq!(refused_report["accepted"], 0, "local outcomes cannot replace the bound context");
        assert_eq!(refused_report["not_accepted"], 2);
        assert_eq!(refused_report["rejected"], 0);
    }

    #[test]
    fn checked_batch_without_census_retains_context_but_no_denominator_claim() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("Good.lean");
        std::fs::write(&path, "def value : Nat := 1\n").unwrap();
        let checked = check_batch(&[path], false);
        assert!(checked.accepted_context().is_some());
        assert!(checked.census().is_none());
        assert!(checked.verdicts().iter().all(FileVerdict::accepted));
    }

    #[test]
    fn checked_batch_partial_rejection_never_exposes_a_kernel_context() {
        let dir = tempfile::tempdir().unwrap();
        let good = dir.path().join("Good.lean");
        let bad = dir.path().join("Bad.lean");
        std::fs::write(&good, "def valid : Nat := 1\n").unwrap();
        std::fs::write(&bad, "theorem wrong : 0 = 1 := rfl\n").unwrap();
        let checked = check_batch(&[good, bad], true);
        assert!(checked.verdicts()[0].accepted(), "preserve the existing per-file verdict");
        assert!(!checked.verdicts()[1].accepted());
        assert!(checked.accepted_context().is_none());
        assert!(checked.checked_source.as_ref().unwrap().accepted_context().is_none());
        assert!(checked.census().is_some(), "failed measurements remain inspectable");
        let mut displayed_census = checked.census().unwrap().clone();
        displayed_census["batch_rejected"] = serde_json::json!(false);
        displayed_census["denominator_status"] = serde_json::json!("complete");
        assert_eq!(displayed_census["batch_rejected"], false);
        assert!(checked.accepted_context().is_none(), "diagnostic JSON cannot grant acceptance");
    }

    #[test]
    fn checked_batch_retains_unresolved_import_identity_and_refusal() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("MissingImport.lean");
        std::fs::write(&path, "import Absent.Library\n").unwrap();
        let checked = check_batch(std::slice::from_ref(&path), true);
        assert!(checked.accepted_context().is_none());
        assert!(!checked.verdicts()[0].accepted());
        let imports = checked.unresolved_imports();
        assert_eq!(imports.len(), 1);
        assert_eq!(imports[0].source_path(), path);
        assert_eq!(imports[0].module(), "Absent.Library");
        assert!(imports[0].diagnostic().contains("unresolved import `Absent.Library`"));
        assert!(
            checked.verdicts()[0]
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.contains(imports[0].diagnostic()))
        );
    }

    #[test]
    fn checked_batch_retains_unreadable_sources_without_partial_context() {
        let dir = tempfile::tempdir().unwrap();
        let good = dir.path().join("Good.lean");
        let absent = dir.path().join("Absent.lean");
        let source = "def valid : Nat := 1\n";
        std::fs::write(&good, source).unwrap();
        let checked = check_batch(&[good, absent.clone()], true);
        assert!(checked.accepted_context().is_none());
        assert!(checked.checked_source.is_none());
        assert!(checked.census().is_none());
        assert!(checked.verdicts().iter().all(|verdict| !verdict.accepted()));
        assert_eq!(checked.sources()[0].source(), Ok(source));
        assert_eq!(checked.sources()[1].path(), absent);
        assert!(checked.sources()[1].source().is_err());
    }

    #[test]
    fn checked_batch_failed_import_read_retains_attempt_and_original_verdict_rows() {
        let dir = tempfile::tempdir().unwrap();
        let main = dir.path().join("Main.lean");
        let invalid = dir.path().join("Invalid.lean");
        std::fs::write(&main, "import Invalid\n").unwrap();
        // A regular local file is discovered, but cannot be read as Lean UTF-8.
        std::fs::write(&invalid, [0xff, 0xfe]).unwrap();
        let checked = check_batch(&[main], true);
        assert!(checked.accepted_context().is_none());
        assert!(checked.checked_source.is_none(), "do not retain the provisional session");
        assert!(checked.census().is_none(), "do not report a provisional census");
        assert_eq!(checked.sources().len(), 2);
        assert_eq!(checked.sources()[1].path(), invalid);
        assert!(checked.sources()[1].source().is_err());
        assert_eq!(checked.verdicts().len(), 1, "the legacy wholesale row is unchanged");
        assert!(checked.verdicts()[0].diagnostics[0].contains("cannot be read"));
        assert_eq!(checked.unresolved_imports()[0].module(), "Invalid");
    }

    #[test]
    fn checked_batch_cycle_retains_diagnostics_but_no_accepted_context() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("Cycle.lean");
        std::fs::write(&path, "def x : Nat := y\ndef y : Nat := x\n").unwrap();
        let checked = check_batch(&[path], true);
        assert!(checked.accepted_context().is_none());
        assert!(!checked.checked_source.as_ref().unwrap().attempt().unwrap().cycles.is_empty());
        assert!(checked.verdicts().iter().all(|verdict| !verdict.accepted()));
        assert_eq!(checked.census().unwrap()["batch_committed"], false);
    }

    #[test]
    fn census_option_requires_one_path_and_never_becomes_an_operand() {
        let request = parse(&args(&["--census", "roster.json", "a.lean"])).unwrap();
        assert_eq!(request.files, vec![PathBuf::from("a.lean")]);
        assert_eq!(request.census_output, Some(PathBuf::from("roster.json")));
        assert!(parse(&args(&["a.lean", "--census"])).is_err());
        assert!(parse(&args(&["a.lean", "--census", "--json"])).is_err());
        assert!(parse(&args(&["a.lean", "--census", "one", "--census", "two"])).is_err());
    }

    #[test]
    fn olean_census_paths_are_explicit_repeatable_and_require_census() {
        let request = parse(&args(&[
            "a.lean",
            "--census",
            "new.json",
            "--census-olean-path",
            "one",
            "--census-olean-path=two",
        ]))
        .unwrap();
        assert_eq!(request.olean_paths, vec![PathBuf::from("one"), PathBuf::from("two")]);
        assert_eq!(request.files, vec![PathBuf::from("a.lean")]);
        for argv in [
            vec!["a.lean", "--census-olean-path", "one"],
            vec!["a.lean", "--census", "new.json", "--census-olean-path"],
            vec!["a.lean", "--census", "new.json", "--census-olean-path="],
            vec!["a.lean", "--census", "new.json", "--census-olean-path=--json"],
        ] {
            assert!(parse(&args(&argv)).is_err(), "{argv:?}");
        }
    }

    #[test]
    fn census_contains_final_import_closure_and_exact_checked_source_hashes() {
        let dir = tempfile::tempdir().unwrap();
        let main = dir.path().join("Main.lean");
        let imported = dir.path().join("Source.lean");
        let main_source = "import Source\ndef mainValue : Nat := importedValue\n";
        let imported_source = "def importedValue : Nat := 4\n";
        std::fs::write(&main, main_source).unwrap();
        std::fs::write(&imported, imported_source).unwrap();
        let checked = check_batch(std::slice::from_ref(&main), true);
        let report = checked.census().expect("census requested").clone();
        let verdicts = checked.verdicts();
        assert!(verdicts.iter().all(FileVerdict::accepted), "{verdicts:?}");
        let check_report: serde_json::Value = serde_json::from_str(&render_json(&checked)).unwrap();
        assert_eq!(check_report["import_search"], "local-source-only");
        assert_eq!(check_report["external_olean_imports"], "unsupported");
        let inputs = report["inputs"].as_array().unwrap();
        assert_eq!(inputs.len(), 2);
        assert_eq!(inputs[0]["path"], main.display().to_string());
        assert_eq!(inputs[1]["path"], imported.display().to_string());
        assert_eq!(
            inputs[1]["sha256"],
            trust_types::digest::stable_sha256_hex(imported_source.as_bytes())
        );
        let rows = report["declarations"].as_array().unwrap();
        assert_eq!(rows.iter().filter(|row| row["name"] == "importedValue").count(), 1);
        assert_eq!(report["denominator_status"], "denominator_unverified");
    }

    #[test]
    fn census_output_never_overwrites_existing_artifacts_or_sources() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("roster.json");
        let report = serde_json::json!({"authority": "diagnostic-only"});
        write_census(&path, &report).unwrap();
        let before = std::fs::read(&path).unwrap();
        assert!(write_census(&path, &serde_json::Value::Null).is_err());
        assert_eq!(std::fs::read(&path).unwrap(), before);
        assert_eq!(serde_json::from_slice::<serde_json::Value>(&before).unwrap(), report);
    }

    #[test]
    fn census_preflight_refuses_existing_output_before_checking_the_input() {
        let dir = tempfile::tempdir().unwrap();
        let output = dir.path().join("roster.json");
        std::fs::write(&output, "existing measurement").unwrap();
        // A missing operand would normally fail the check with exit 1. The
        // output-path refusal must happen before checking it, and exit 2.
        assert_eq!(
            run_check(&[
                dir.path().join("Missing.lean").display().to_string(),
                "--census".to_string(),
                output.display().to_string(),
            ]),
            ExitCode::from(2)
        );
        assert_eq!(std::fs::read_to_string(output).unwrap(), "existing measurement");
    }

    #[test]
    fn census_preflight_rejects_unusable_parents_without_creating_anything() {
        let dir = tempfile::tempdir().unwrap();
        let absent_parent = dir.path().join("absent");
        assert!(preflight_census(&absent_parent.join("roster.json")).is_err());
        assert!(!absent_parent.exists());
        let file_parent = dir.path().join("file");
        std::fs::write(&file_parent, "not a directory").unwrap();
        assert!(preflight_census(&file_parent.join("roster.json")).is_err());
        assert_eq!(std::fs::read_to_string(file_parent).unwrap(), "not a directory");
    }

    #[test]
    fn census_preflight_does_not_replace_the_exclusive_creation_race_guard() {
        let dir = tempfile::tempdir().unwrap();
        let output = dir.path().join("roster.json");
        preflight_census(&output).unwrap();
        assert!(!output.exists());
        std::fs::write(&output, "concurrent writer").unwrap();
        assert!(write_census(&output, &serde_json::Value::Null).is_err());
        assert_eq!(std::fs::read_to_string(output).unwrap(), "concurrent writer");
    }

    #[cfg(unix)]
    #[test]
    fn census_preflight_refuses_a_dangling_output_symlink() {
        let dir = tempfile::tempdir().unwrap();
        let target = dir.path().join("absent");
        let output = dir.path().join("roster.json");
        std::os::unix::fs::symlink(&target, &output).unwrap();
        assert!(preflight_census(&output).is_err());
        assert!(!target.exists());
        assert_eq!(std::fs::read_link(output).unwrap(), target);
    }

    #[test]
    fn census_retains_cycle_and_unreadable_invocation_failures() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("Cycle.lean");
        std::fs::write(&path, "def x : Nat := y\ndef y : Nat := x\n").unwrap();
        let mut report = serde_json::Value::Null;
        let verdicts = check_files_impl(&[path], Some(&mut report));
        assert!(verdicts.iter().all(|verdict| !verdict.accepted()));
        assert_eq!(report["batch_rejected"], true);
        assert_eq!(report["batch_committed"], false);
        assert_eq!(report["declarations"], serde_json::json!([]));
        let mut unreadable_report = serde_json::Value::Null;
        let verdicts =
            check_files_impl(&[dir.path().join("Missing.lean")], Some(&mut unreadable_report));
        assert!(!verdicts[0].accepted());
        assert_eq!(unreadable_report, serde_json::Value::Null);
    }

    #[test]
    fn census_cli_writes_diagnostic_only_envelope_without_changing_refusal() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("Bad.lean");
        let output = dir.path().join("roster.json");
        std::fs::write(&path, "axiom assumed : True\n").unwrap();
        let status = run_check_scratch(&[
            path.display().to_string(),
            "--census".to_string(),
            output.display().to_string(),
        ]);
        assert_eq!(status, ExitCode::FAILURE);
        let report: serde_json::Value =
            serde_json::from_slice(&std::fs::read(output).unwrap()).unwrap();
        assert_eq!(report["authority"], "diagnostic-only");
        assert_eq!(report["kernel_roster"]["denominator_status"], "denominator_unverified");
        assert_eq!(report["check_report"]["rejected"], 1);
    }

    #[test]
    fn a_lean_operand_selects_the_lane() {
        assert!(selects_lean_lane(&args(&["proofs/x.lean"])));
        assert!(selects_lean_lane(&args(&["--json", "proofs/x.lean"])));
        assert!(!selects_lean_lane(&args(&["src/lib.rs"])));
        assert!(!selects_lean_lane(&args(&["--release"])));
    }

    /// Write `rel` (which may name subdirectories) under `root`.
    fn write_under(root: &Path, rel: &str, source: &str) -> PathBuf {
        let path = root.join(rel);
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent).expect("create fixture dir");
        }
        std::fs::write(&path, source).expect("write fixture");
        path
    }

    /// A directory of `.lean` sources is a Lean operand and expands to every
    /// source under it, deterministically ordered. Before this, such a
    /// directory fell through to the Rust lane and died on "could not find
    /// `Targo.toml` or `Cargo.toml`", so a Lean project had no front door at
    /// all.
    #[test]
    fn a_directory_of_lean_sources_selects_the_lane_and_expands_recursively() {
        let dir = tempfile::tempdir().expect("tempdir");
        write_under(dir.path(), "B.lean", "def b : Nat := 1\n");
        write_under(dir.path(), "sub/A.lean", "def a : Nat := 2\n");
        write_under(dir.path(), "notes.md", "not lean\n");
        let operand = dir.path().to_string_lossy().to_string();

        assert!(selects_lean_lane(std::slice::from_ref(&operand)));
        let request = parse(&[operand]).expect("a directory of .lean sources parses");
        let found: Vec<String> = request
            .files
            .iter()
            .map(|path| {
                path.strip_prefix(dir.path()).expect("under the operand").to_string_lossy().into()
            })
            .collect();
        assert_eq!(found, vec!["B.lean".to_string(), "sub/A.lean".to_string()]);
    }

    /// A directory whose files import EACH OTHER by dotted path must prove
    /// them. The walk lists `Sub/Leaf.lean` under the stem `Leaf` while the
    /// closure resolves a sibling's `import Sub.Leaf` to the same file under
    /// the dotted key; before the fix that minted a SECOND member, the file's
    /// source reached the kernel twice, every declaration in it registered
    /// twice, and the directory was REJECTED for `declared twice in this
    /// batch`. Every earlier directory test used files that do not import each
    /// other, which is exactly why they all passed.
    #[test]
    fn a_directory_whose_files_import_each_other_is_checked_once() {
        let dir = tempfile::tempdir().expect("tempdir");
        write_under(dir.path(), "Top.lean", "import Sub.Leaf\n\ndef top : Nat := 1\n");
        write_under(dir.path(), "Sub/Leaf.lean", "def leaf : Nat := 2\n");

        let request = parse(&[dir.path().to_string_lossy().to_string()]).expect("parses");
        let verdicts = check_files(&request.files);
        let refused: Vec<String> = verdicts
            .iter()
            .filter(|verdict| !verdict.accepted())
            .map(|verdict| format!("{}: {:?}", verdict.path.display(), verdict.diagnostics))
            .collect();
        assert!(refused.is_empty(), "every file must prove: {refused:?}");
        assert_eq!(verdicts.len(), 2, "one row per FILE, never a second row for the same file");
    }

    #[test]
    fn directory_census_waits_for_alias_resolution_and_counts_each_file_once() {
        let dir = tempfile::tempdir().expect("tempdir");
        write_under(dir.path(), "Top.lean", "import Sub.Leaf\ndef top : Nat := leaf\n");
        let leaf = write_under(dir.path(), "Sub/Leaf.lean", "def leaf : Nat := 2\n");
        write_under(dir.path(), "lakefile.lean", "import Lake\n");
        let census_path = dir.path().join("roster.json");
        let request = parse(&[
            dir.path().display().to_string(),
            "--census".to_string(),
            census_path.display().to_string(),
        ])
        .expect("directory and census options coexist");
        assert_eq!(request.census_output, Some(census_path));
        assert_eq!(request.lake_dirs, vec![dir.path().to_path_buf()]);
        assert_eq!(request.files.len(), 2);
        let mut report = serde_json::Value::Null;
        let verdicts = check_files_impl(&request.files, Some(&mut report));
        assert_eq!(verdicts.len(), 2);
        assert!(verdicts.iter().all(FileVerdict::accepted), "{verdicts:?}");
        let inputs = report["inputs"].as_array().expect("final input census");
        assert_eq!(inputs.len(), 2);
        assert_eq!(
            inputs.iter().filter(|row| row["path"] == leaf.display().to_string()).count(),
            1
        );
        let declarations = report["declarations"].as_array().expect("declaration census");
        for name in ["top", "leaf"] {
            assert_eq!(declarations.iter().filter(|row| row["name"] == name).count(), 1);
        }
        assert_eq!(report["denominator_status"], "denominator_unverified");
    }

    #[test]
    fn directory_alias_retains_one_final_checked_context_and_rejects_rebinding() {
        let dir = tempfile::tempdir().unwrap();
        write_under(dir.path(), "Top.lean", "import Sub.Leaf\ndef top : Nat := leaf\n");
        let leaf = write_under(dir.path(), "Sub/Leaf.lean", "def leaf : Nat := 2\n");
        let request = parse(&[dir.path().display().to_string()]).unwrap();
        let mut checked = check_batch(&request.files, true);
        let context = checked.accepted_context().expect("final alias fixpoint checks");
        let leaf_index = checked.sources().iter().position(|source| source.path() == leaf).unwrap();
        let expected =
            vec![LeanSourceAlias { module: "Sub.Leaf".into(), source_index: leaf_index }];
        assert_eq!(context.aliases(), expected);
        assert_eq!(context.sources().len(), 2);
        assert_eq!(checked.verdicts().len(), 2);
        assert!(checked.unresolved_imports().is_empty());
        assert!(std::ptr::eq(
            context.environment(),
            checked.checked_source.as_ref().unwrap().accepted_context().unwrap().environment()
        ));
        let root = context.source_closure_sha256().to_string();
        let report = census::report(
            &checked,
            &request.files,
            "check",
            &serde_json::Value::Null,
            &serde_json::Value::Null,
        );
        let attempts = report["source_graph"]["attempts"].as_array().unwrap();
        assert_eq!(attempts.len(), 2, "alias-only progress must trigger a final fresh attempt");
        assert_eq!(attempts[0]["source_aliases"], serde_json::json!([]));
        let expected_json = serde_json::json!([{"module": "Sub.Leaf", "source_index": leaf_index}]);
        assert_eq!(attempts[1]["source_aliases"], expected_json);
        assert_eq!(report["source_graph"]["source_aliases"], expected_json);
        for name in ["top", "leaf"] {
            assert_eq!(
                report["kernel_roster"]["declarations"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .filter(|row| row["name"] == name)
                    .count(),
                1
            );
        }
        std::fs::write(&leaf, "axiom replacedAfterCheck : False").unwrap();
        assert_eq!(checked.accepted_context().unwrap().source_closure_sha256(), root);
        assert_eq!(checked.sources()[leaf_index].source(), Ok("def leaf : Nat := 2\n"));
        checked.aliases[0].source_index = (leaf_index + 1) % 2;
        assert!(
            checked.accepted_context().is_none(),
            "same alias cannot borrow another snapshot's seal"
        );
        checked.aliases = expected.clone();
        checked.aliases[0].module = "Other.Leaf".into();
        assert!(checked.accepted_context().is_none(), "module key is part of the seal");
        checked.aliases = expected;
        assert!(checked.accepted_context().is_some());
        checked.aliases.clear();
        assert!(
            checked.accepted_context().is_none(),
            "dropping the final alias loses the exact binding"
        );
    }

    #[cfg(unix)]
    #[test]
    fn two_new_import_paths_to_one_file_share_one_pulled_snapshot() {
        let dir = tempfile::tempdir().unwrap();
        let top = write_under(
            dir.path(),
            "Top.lean",
            "import Leaf\nimport Alias\ndef top : Nat := leaf\n",
        );
        let leaf = write_under(dir.path(), "Leaf.lean", "def leaf : Nat := 2\n");
        std::os::unix::fs::symlink(&leaf, dir.path().join("Alias.lean")).unwrap();
        let checked = check_batch(&[top], true);
        let context =
            checked.accepted_context().expect("pending-pull aliases do not duplicate source");
        assert_eq!(context.sources().len(), 2);
        assert_eq!(context.aliases().len(), 1);
        assert_eq!(context.aliases()[0].source_index, 1);
        let keys = std::collections::BTreeSet::from([
            context.sources()[1].module.as_str(),
            context.aliases()[0].module.as_str(),
        ]);
        assert_eq!(keys, std::collections::BTreeSet::from(["Leaf", "Alias"]));
        assert_eq!(checked.verdicts().len(), 2);
        assert!(checked.verdicts().iter().all(FileVerdict::accepted));
        let report = checked.census().unwrap();
        assert_eq!(report["inputs"].as_array().unwrap().len(), 2);
        assert_eq!(
            report["declarations"]
                .as_array()
                .unwrap()
                .iter()
                .filter(|row| row["name"] == "leaf")
                .count(),
            1
        );
    }

    #[test]
    fn directory_alias_never_hides_rejection_in_the_same_source() {
        let dir = tempfile::tempdir().unwrap();
        write_under(dir.path(), "Top.lean", "import Sub.Leaf\ndef top : Nat := 1\n");
        write_under(dir.path(), "Sub/Leaf.lean", "axiom unchecked : False\n");
        let request = parse(&[dir.path().display().to_string()]).unwrap();
        let checked = check_batch(&request.files, true);
        assert_eq!(checked.sources().len(), 2);
        assert_eq!(checked.aliases.len(), 1);
        assert_eq!(checked.verdicts().len(), 2);
        assert!(checked.verdicts().iter().any(|verdict| !verdict.accepted()));
        assert!(checked.accepted_context().is_none());
        assert!(checked.checked_source.as_ref().unwrap().accepted_context().is_none());
        assert!(
            checked.unresolved_imports().is_empty(),
            "resolved alias does not discharge the axiom"
        );
        assert_eq!(checked.census().unwrap()["inputs"].as_array().unwrap().len(), 2);
    }

    /// `lakefile.lean` is Lake DSL build configuration. Sweeping it in as a
    /// proof source REJECTED a project that `clean lake build` builds cleanly.
    #[test]
    fn a_lakefile_is_not_swept_in_as_a_proof_source() {
        let dir = tempfile::tempdir().expect("tempdir");
        write_under(dir.path(), "A.lean", "def a : Nat := 1\n");
        write_under(
            dir.path(),
            "lakefile.lean",
            "import Lake\nopen Lake DSL\npackage Demo where\n  version := \"0.1.0\"\n",
        );

        let request = parse(&[dir.path().to_string_lossy().to_string()]).expect("parses");
        let found: Vec<String> = request
            .files
            .iter()
            .map(|path| path.file_name().expect("named").to_string_lossy().into())
            .collect();
        assert_eq!(found, vec!["A.lean".to_string()]);
    }

    /// A Lake project is RECORDED so the run can disclose that Lake's own
    /// resolution was not used. The lakefile still never becomes a proof source.
    #[test]
    fn a_lake_project_directory_is_recorded_for_disclosure() {
        let dir = tempfile::tempdir().expect("tempdir");
        write_under(dir.path(), "A.lean", "def a : Nat := 1\n");
        write_under(dir.path(), "lakefile.lean", "import Lake\n");
        let request = parse(&[dir.path().to_string_lossy().to_string()]).expect("parses");
        assert_eq!(request.lake_dirs.len(), 1, "the Lake project must be recorded");
        assert_eq!(request.files.len(), 1, "and the lakefile is still not a proof source");

        let plain = tempfile::tempdir().expect("tempdir");
        write_under(plain.path(), "B.lean", "def b : Nat := 2\n");
        let plain_req = parse(&[plain.path().to_string_lossy().to_string()]).expect("parses");
        assert!(plain_req.lake_dirs.is_empty(), "a non-Lake directory records nothing");
    }

    /// The directory rule is ADDITIVE: it may never take a directory the Rust
    /// lane can resolve, at the directory itself OR at any ancestor — Cargo
    /// walks up, so a nested `proofs/` inside a crate is the Rust lane's.
    #[test]
    fn a_directory_the_rust_lane_can_resolve_is_left_to_it() {
        let here = tempfile::tempdir().expect("tempdir");
        write_under(here.path(), "P.lean", "def p : Nat := 1\n");
        write_under(here.path(), "Cargo.toml", "[package]\nname = \"x\"\n");
        assert!(!selects_lean_lane(&[here.path().to_string_lossy().to_string()]));

        let above = tempfile::tempdir().expect("tempdir");
        write_under(above.path(), "Cargo.toml", "[package]\nname = \"y\"\n");
        write_under(above.path(), "proofs/Q.lean", "def q : Nat := 1\n");
        let nested = above.path().join("proofs");
        assert!(!selects_lean_lane(&[nested.to_string_lossy().to_string()]));
    }

    /// A directory with no VISIBLE `.lean` source is not a Lean operand, so
    /// the Rust lane keeps it and its diagnostics. Hidden directories are
    /// skipped by the walk, so they cannot make one either.
    #[test]
    fn a_directory_with_no_visible_lean_source_is_not_a_lean_operand() {
        let dir = tempfile::tempdir().expect("tempdir");
        write_under(dir.path(), "README.md", "nothing here\n");
        write_under(dir.path(), ".hidden/H.lean", "def h : Nat := 1\n");
        assert!(
            !selects_lean_lane(&[dir.path().to_string_lossy().to_string()]),
            "a hidden directory's sources must not make this a Lean operand"
        );
    }

    /// Naming a directory AND one of its own files is one operand, not a
    /// duplicate — the batch's duplicate-module rule would otherwise refuse
    /// the whole invocation for a duplication the caller never wrote.
    #[test]
    fn a_directory_and_one_of_its_own_files_are_listed_once() {
        let dir = tempfile::tempdir().expect("tempdir");
        let file = write_under(dir.path(), "Only.lean", "def only : Nat := 1\n");
        let request =
            parse(&[dir.path().to_string_lossy().to_string(), file.to_string_lossy().to_string()])
                .expect("parses");
        assert_eq!(request.files.len(), 1, "{:?}", request.files);
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
        // The refusal is the lane's only enumeration of what it accepts, so it
        // names every option `parse` defines. It omitted `--census-olean-path`.
        for option in [
            "`--json`",
            "`--format`",
            "`--target-dir DIR`",
            "`--census PATH`",
            "`--census-olean-path DIR`",
            "`--jobs N`",
        ] {
            assert!(error.contains(option), "refusal roster omits {option}: {error}");
        }
    }

    #[test]
    fn cargo_jobs_hint_alongside_a_lean_operand_is_ignored() {
        for argv in [
            &["x.lean", "--jobs=2"][..],
            &["--jobs", "2", "x.lean"],
            &["-j", "2", "x.lean"],
            &["x.lean", "-j2"],
            &["x.lean", "-j=2"],
            &["-j", "x.lean"],
        ] {
            let request = parse(&args(argv)).unwrap_or_else(|error| panic!("{argv:?}: {error}"));
            assert_eq!(request.files, [std::path::PathBuf::from("x.lean")], "{argv:?}");
            // `targo trust build` takes the same lane (`selects_lean_lane`), and its
            // own parser must accept the same count beside its required options.
            let mut build = vec!["--emit=trust-ir", "--out", "o.json"];
            build.extend_from_slice(argv);
            crate::lean_build::parse(&args(&build))
                .unwrap_or_else(|error| panic!("build {build:?}: {error}"));
        }
        parse(&args(&["--jobs=many", "x.lean"])).expect_err("not a job count");
        crate::lean_build::parse(&args(&["x.lean", "--emit=trust-ir", "--out", "o.json", "--jobs=many"]))
            .expect_err("build: not a job count");
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

    /// LEAN-PROVED-BESIDE-REFUSED-1: one invocation is one all-or-nothing
    /// batch, so a file whose declarations kernel-checked beside a rejected
    /// sibling is NOT ACCEPTED, never PROVED, in the terminal and JSON forms
    /// alike, as its record says
    /// (`records::tests::a_file_beside_a_rejected_sibling_records_no_proof`).
    /// The exit status is what it was: failure.
    #[test]
    fn a_file_beside_a_rejected_sibling_is_not_accepted_in_every_form() {
        let dir = tempfile::tempdir().expect("tempdir");
        let a = dir.path().join("A.lean");
        let b = dir.path().join("B.lean");
        std::fs::write(&a, "theorem a : 1 = 1 := rfl\n").unwrap();
        std::fs::write(&b, "theorem b : 1 = 2 := rfl\n").unwrap();

        let checked = check_batch(&[a.clone(), b.clone()], false);
        assert!(checked.verdicts()[0].accepted(), "A's own declarations kernel-checked");
        assert_eq!(checked.verdicts()[0].registered.len(), 1);
        assert!(!checked.verdicts()[1].accepted());
        assert!(checked.accepted_context().is_none());
        assert_eq!(
            checked.file_reports(),
            [FileReport::NotAccepted { refused_by: vec![b.clone()] }, FileReport::Rejected]
        );
        let json: serde_json::Value = serde_json::from_str(&render_json(&checked)).unwrap();
        let files = &json["files"];
        assert_eq!(files[0]["status"], "not-accepted", "{json:#}");
        assert_eq!(files[0]["accepted"], false, "{json:#}");
        assert_eq!(files[0]["batch_refused_by"], serde_json::json!([b.display().to_string()]));
        assert_eq!(files[0]["registered"].as_array().map(Vec::len), Some(1), "information only");
        assert_eq!(files[1]["status"], "rejected");
        assert_eq!(files[1]["accepted"], false);
        assert_eq!(files[1]["batch_refused_by"], serde_json::json!([]));
        assert_eq!(json["accepted"], 0);
        assert_eq!(json["not_accepted"], 1);
        assert_eq!(json["rejected"], 1);
        assert_eq!(
            run_check_scratch(&[a.display().to_string(), b.display().to_string()]),
            ExitCode::FAILURE
        );

        // The same pair with B fixed: the batch is accepted, so both are PROVED.
        std::fs::write(&b, "theorem b : 2 = 2 := rfl\n").unwrap();
        let checked = check_batch(&[a.clone(), b.clone()], false);
        assert_eq!(checked.file_reports(), [FileReport::Proved, FileReport::Proved]);
        let json: serde_json::Value = serde_json::from_str(&render_json(&checked)).unwrap();
        assert_eq!(json["files"][0]["status"], "proved");
        assert_eq!(json["files"][0]["accepted"], true);
        assert_eq!(json["accepted"], 2);
        assert_eq!(json["not_accepted"], 0);
        assert_eq!(json["rejected"], 0);
        assert_eq!(
            run_check_scratch(&[a.display().to_string(), b.display().to_string()]),
            ExitCode::SUCCESS
        );
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
