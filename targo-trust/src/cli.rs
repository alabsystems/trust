// targo trust CLI: argument parsing and usage output
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use anyhow::{Context, Result, bail};

use crate::config::{
    DEFAULT_TRUST_PROFILE, known_codegen_backend_names, normalize_codegen_backend,
};
use crate::solver_detect;
use crate::types::OutputFormat;

#[derive(Debug)]
pub(crate) struct SubcommandArgs {
    pub(crate) format: OutputFormat,
    pub(crate) passthrough: Vec<String>,
    pub(crate) manifest_path: Option<String>,
    pub(crate) single_file: Option<String>,
    pub(crate) is_single_file: bool,
    /// When true, run the prove-strengthen-backprop loop instead of one-shot.
    pub(crate) rewrite: bool,
    /// Maximum number of rewrite loop iterations (default: 10).
    pub(crate) max_iterations: usize,
    /// Path to an intent document (design doc / chat) guiding AI-in-the-loop
    /// repair. Overrides `[package.metadata.trust] intent` when set.
    pub(crate) intent: Option<String>,
    /// Path to a baseline report JSON file for `diff` subcommand.
    pub(crate) baseline: Option<String>,
    /// Git ref for the "from" side of a diff (e.g., `main`, `HEAD~3`).
    pub(crate) from_ref: Option<String>,
    /// Git ref for the "to" side of a diff (e.g., `feature`, `HEAD`).
    pub(crate) to_ref: Option<String>,
    /// Scope filter for git diff (e.g., `crates/`, `src/`).
    pub(crate) scope: Option<String>,
    /// Path to a current report JSON file for `diff` subcommand.
    pub(crate) current: Option<String>,
    /// When true, use standalone source-level analysis instead of invoking trustc.
    pub(crate) standalone: bool,
    /// When true, allow Level 0 verifier gaps to remain compiler warnings.
    pub(crate) allow_l0_gaps: bool,
    /// When true, enable hardened boundary obligations for Rust-bugs Rust won't catch.
    pub(crate) hardened: bool,
    /// When true, run the artifact-backed full verifier in non-aborting survey mode
    /// — per-function proved/unknown/failed coverage without fail-closed abort
    /// (passes the tracked `-Z trust-policy=advisory` option). Useful as a CI
    /// reporting gate over a whole crate.
    pub(crate) survey: bool,
    /// Explicit CLI hardened choice; None means config/default decides.
    pub(crate) hardened_override: Option<bool>,
    /// Optional hardened trust profile name to expose to compiler and source checks.
    pub(crate) trust_profile: Option<String>,
    /// Output directory for proof report files (JSON, HTML, NDJSON).
    pub(crate) report_dir: Option<String>,
    /// Focus `targo trust check` exit semantics on one function selector.
    pub(crate) focused_function: Option<String>,
    /// Request a routed solver backend for compiler-backed source verification.
    pub(crate) solver: Option<String>,
    /// Force a specific codegen backend (llvm or trust-cg).
    pub(crate) backend: Option<String>,
    /// When true, write inert, commented contract candidates into source files (for `init`).
    pub(crate) inline: bool,
    /// Entry address for `lift`, accepted as decimal or 0x-prefixed hex.
    pub(crate) entry: Option<String>,
    /// When true, lift all detected functions instead of the binary entry.
    pub(crate) all_functions: bool,
    /// When true, unsupported lift coverage makes `lift` fail.
    pub(crate) strict: bool,
    /// When true, `targo trust check`/`build` run the explicit advisory memory-safe
    /// gate (`-Z trust-policy=memory-safe`): reachable-but-memory-safe Level-0
    /// refutations and lowering-failures in functions with no `unsafe` are demoted to warnings,
    /// so correct memory-safe code compiles (undefined behavior is still rejected).
    /// The compiler/codegen policy remains strict; only authenticated safe-code
    /// demotions may receive a conditional result. Genuine unknowns and unsafe
    /// failures remain nonzero. The legacy `--allow-memory-safe-panics` spelling
    /// maps to the same complete mode.
    pub(crate) memory_safe: bool,
    /// `--certify`: the RELEASE gate. Demands full static discharge — every
    /// non-proved obligation fails, including one whose operation keeps its
    /// runtime check. The default lane reports such a row and succeeds
    /// (completeness-gap ruling, Andrew 2026-07-25); `--certify` is what a
    /// release must pass.
    pub(crate) certify: bool,
    /// Checked binary certificate artifacts to import into `verify-binary`.
    pub(crate) checked_certificate_artifacts: Vec<String>,
    /// Checked binary certificate manifests to import into `verify-binary`.
    pub(crate) checked_certificate_manifests: Vec<String>,
    /// Directory requested for checked binary certificate production/export artifacts.
    pub(crate) checked_certificate_export_dir: Option<String>,
    /// External production checker executable for loaded checked binary certificates.
    pub(crate) checked_certificate_checker: Option<String>,
    /// Path where decompile/convert should write a validated proof-grade release transcript.
    pub(crate) proof_grade_release_transcript_out: Option<String>,
    /// Exact binary-address to source provenance artifacts to import into runtime rewrite mode.
    pub(crate) binary_source_provenance_artifacts: Vec<String>,
}

impl SubcommandArgs {
    pub(crate) fn single_file_path(&self) -> Option<&str> {
        self.single_file.as_deref()
    }

    /// Whether compiler artifacts and the result gate must use the canonical
    /// strict policy. Strict is the default and no longer has an enable flag.
    pub(crate) fn strict_artifact_policy(&self) -> bool {
        !self.survey && !self.allow_l0_gaps
    }

    /// Whether non-proved ledger rows must make the command fail. The narrow
    /// memory-safe mode keeps strict artifacts but permits its authenticated
    /// safe-code assumptions to produce an explicit conditional success.
    pub(crate) fn strict_result_gate(&self) -> bool {
        self.strict_artifact_policy() && !self.memory_safe
    }

    /// Whether this run is the release gate (`--certify`): full static discharge,
    /// every non-proved bucket fatal.
    pub(crate) fn certify_lane(&self) -> bool {
        self.certify
    }

    /// Trust (assumption ledger): `--allow-l0-gaps` selects advisory allow_l0_gaps mode
    /// (`-Z trust-policy=advisory`). The parser rejects combining it with full mode.
    pub(crate) fn allow_l0_gaps_lane(&self) -> bool {
        self.allow_l0_gaps
    }

    /// The child-facing Cargo argument list for a crate-mode run.
    ///
    /// `--all` names two unrelated options that reach this one wrapper parser:
    /// Cargo's historical alias for `--workspace`, and the binary-lift "every
    /// detected function" selector. Parsing cannot tell them apart before the
    /// subcommand is known, so crate mode restores the Cargo meaning — and it
    /// does so HERE, once, because the compile command, the canonical package
    /// selection, and the post-build gate replay each rebuild this list from the
    /// same parse. When one of them silently dropped the flag, verification
    /// covered the default members while the gates resolved the whole
    /// workspace, so the proof scope a report claims stopped matching the code
    /// the compiler actually saw.
    ///
    /// Insertion respects a `--` that survives into this list. The wrapper's
    /// own separator is consumed during parsing, so one that reaches here is
    /// Cargo's: everything past it belongs to the program Cargo runs, and a
    /// selector placed there would be handed to a test binary rather than
    /// widening the build.
    pub(crate) fn crate_mode_cargo_args(&self) -> Vec<String> {
        let mut args = self.passthrough.clone();
        if self.all_functions && !args.iter().any(|arg| arg == "--workspace" || arg == "--all") {
            let separator = args.iter().position(|arg| arg == "--").unwrap_or(args.len());
            args.insert(separator, "--workspace".to_string());
        }
        args
    }
}

pub(crate) fn parse_subcommand_args(args: &[String]) -> Result<SubcommandArgs> {
    let mut format = OutputFormat::Terminal;
    let mut passthrough = Vec::new();
    let mut manifest_path: Option<String> = None;
    let mut single_file: Option<String> = None;
    let mut rewrite = false;
    let mut max_iterations: usize = 10;
    let mut intent: Option<String> = None;
    let mut baseline: Option<String> = None;
    let mut from_ref: Option<String> = None;
    let mut to_ref: Option<String> = None;
    let mut scope: Option<String> = None;
    let mut current: Option<String> = None;
    let mut standalone = false;
    let mut allow_l0_gaps = false;
    // Trust: batteries-on default. Hardened boundary obligations (the classes of
    // Rust bug that stock Rust won't catch) are ON by default under the
    // `unix_hardened` profile — no `--hardened` opt-in needed
    // (DESIGN_PHILOSOPHY.md §2/§3). `--no-hardened` still turns them off for
    // triage; because `hardened_override`/`trust_profile` stay unset here, that
    // opt-out path keeps working unchanged.
    //
    // This resolves to `-Ztrust-verify-profile=<name>` and nothing else, so the
    // obligation set a project gets here is the one a raw `trustc` gets from
    // the same profile. It is a project policy that reaches the compiler as a
    // named profile, not a second default the compiler also holds an opinion
    // about.
    let mut hardened = true;
    let mut survey = false;
    let mut hardened_override: Option<bool> = None;
    let mut trust_profile: Option<String> = None;
    let mut report_dir: Option<String> = None;
    let mut focused_function: Option<String> = None;
    let mut solver: Option<String> = None;
    let mut backend: Option<String> = None;
    let mut inline = false;
    let mut entry: Option<String> = None;
    let mut all_functions = false;
    let mut strict = true;
    // Keep the explicit source-mode request separate from `strict`, whose
    // value also controls binary coverage and defaults to true. Resolving
    // conflicting source modes after parsing makes the result independent of
    // argument order.
    let mut explicit_strict = false;
    let mut explicit_allow_unsupported = false;
    // Source verification is fail-closed by default. Memory-safe demotion is an
    // explicit advisory mode, never a latent boolean suppressed by full mode.
    let mut memory_safe = false;
    let mut certify = false;
    let mut checked_certificate_artifacts = Vec::new();
    let mut checked_certificate_manifests = Vec::new();
    let mut checked_certificate_export_dir: Option<String> = None;
    let mut checked_certificate_checker: Option<String> = None;
    let mut proof_grade_release_transcript_out: Option<String> = None;
    let mut binary_source_provenance_artifacts = Vec::new();
    // Single-file mode is selected only by the first child-facing positional.
    // Once an opaque Cargo/rustc argument has been seen, a later `.rs` token may
    // be that option's value (for example `--config custom.rs`) and must not
    // silently switch the entire invocation from targo to direct trustc.
    let mut saw_passthrough_argument = false;
    let mut i = 0;

    while i < args.len() {
        match args[i].as_str() {
            "--" => {
                // Wrapper separator: consume it and forward everything after
                // it byte-for-byte. In particular, Trust options and `.rs`
                // operands after this point belong to the child command and
                // must not mutate this parser's mode.
                passthrough.extend(args[i + 1..].iter().cloned());
                break;
            }
            "--json" => {
                format = OutputFormat::Json;
            }
            "--format" => {
                i += 1;
                let value =
                    args.get(i).context("--format requires a value (terminal, json, html)")?;
                format = OutputFormat::from_str(value)?;
            }
            s if s.starts_with("--format=") => {
                let value = s.strip_prefix("--format=").expect("invariant: prefix checked");
                format = OutputFormat::from_str(value)?;
            }
            "--rewrite" => {
                rewrite = true;
            }
            "--fresh" => {
                bail!(
                    "--fresh has been removed: compiler-backed verifier commands always collect fresh structured evidence"
                );
            }
            s if s.starts_with("--fresh=") => {
                bail!(
                    "--fresh has been removed: compiler-backed verifier commands always collect fresh structured evidence"
                );
            }
            "--standalone" => {
                standalone = true;
            }
            "--full-verifier" => {
                bail!(
                    "--full-verifier has been removed: strict verification runs by default; \
                     use --allow-l0-gaps to select the advisory lane"
                );
            }
            "--unsafe-memory" => {
                // Consumed here; exact `report --unsafe-memory` routing is
                // handled before generic source verification begins.
            }
            "--allow-l0-gaps" => {
                allow_l0_gaps = true;
            }
            "--allow-level0-gaps" => {
                bail!("--allow-level0-gaps has been removed; use --allow-l0-gaps");
            }
            s if s.starts_with("--allow-level0-gaps=") => {
                bail!("--allow-level0-gaps has been removed; use --allow-l0-gaps");
            }
            "--survey" => {
                survey = true;
            }
            "--hardened" => {
                if hardened_override == Some(false) {
                    bail!("--hardened conflicts with --no-hardened");
                }
                hardened_override = Some(true);
                hardened = true;
                if trust_profile.is_none() {
                    trust_profile = Some(DEFAULT_TRUST_PROFILE.to_string());
                }
            }
            "--no-hardened" => {
                if hardened_override == Some(true) || trust_profile.is_some() {
                    bail!("--no-hardened conflicts with --hardened/--trust-profile");
                }
                hardened_override = Some(false);
                hardened = false;
                trust_profile = None;
            }
            "--trust-profile" => {
                if hardened_override == Some(false) {
                    bail!("--trust-profile conflicts with --no-hardened");
                }
                i += 1;
                let value = args
                    .get(i)
                    .context("--trust-profile requires a profile name, e.g. unix_hardened")?;
                validate_trust_profile_value(value)?;
                hardened_override = Some(true);
                hardened = true;
                trust_profile = Some(value.clone());
            }
            s if s.starts_with("--trust-profile=") => {
                if hardened_override == Some(false) {
                    bail!("--trust-profile conflicts with --no-hardened");
                }
                let value = s.strip_prefix("--trust-profile=").expect("invariant: prefix checked");
                validate_trust_profile_value(value)?;
                hardened_override = Some(true);
                hardened = true;
                trust_profile = Some(value.to_string());
            }
            "--inline" => {
                inline = true;
            }
            "--all" => {
                all_functions = true;
            }
            "--strict" => {
                strict = true;
                explicit_strict = true;
            }
            "--certify" => {
                // Release gate: restore the historical all-buckets-fatal
                // predicate AND ask the compiler for full static discharge.
                certify = true;
            }
            "--memory-safe" | "--allow-memory-safe-panics" => {
                // Narrow loosener: demote supported memory-safe panics while
                // retaining the strict crate-under-check verification scope.
                memory_safe = true;
            }
            "--allow-unsupported" => {
                strict = false;
                explicit_allow_unsupported = true;
            }
            "--checked-cert-artifact" => {
                i += 1;
                let value = args.get(i).context("--checked-cert-artifact requires a file path")?;
                checked_certificate_artifacts.push(value.clone());
            }
            s if s.starts_with("--checked-cert-artifact=") => {
                let value =
                    s.strip_prefix("--checked-cert-artifact=").expect("invariant: prefix checked");
                checked_certificate_artifacts.push(value.to_string());
            }
            "--checked-cert-manifest" => {
                i += 1;
                let value = args.get(i).context("--checked-cert-manifest requires a file path")?;
                checked_certificate_manifests.push(value.clone());
            }
            s if s.starts_with("--checked-cert-manifest=") => {
                let value =
                    s.strip_prefix("--checked-cert-manifest=").expect("invariant: prefix checked");
                checked_certificate_manifests.push(value.to_string());
            }
            "--checked-cert-export-dir" => {
                i += 1;
                let value =
                    args.get(i).context("--checked-cert-export-dir requires a directory path")?;
                checked_certificate_export_dir = Some(value.clone());
            }
            s if s.starts_with("--checked-cert-export-dir=") => {
                let value = s
                    .strip_prefix("--checked-cert-export-dir=")
                    .expect("invariant: prefix checked");
                checked_certificate_export_dir = Some(value.to_string());
            }
            "--checked-cert-checker" => {
                i += 1;
                let value =
                    args.get(i).context("--checked-cert-checker requires an executable path")?;
                checked_certificate_checker = Some(value.clone());
            }
            s if s.starts_with("--checked-cert-checker=") => {
                let value =
                    s.strip_prefix("--checked-cert-checker=").expect("invariant: prefix checked");
                checked_certificate_checker = Some(value.to_string());
            }
            "--proof-grade-release-transcript-out" => {
                i += 1;
                let value = args
                    .get(i)
                    .context("--proof-grade-release-transcript-out requires a file path")?;
                proof_grade_release_transcript_out = Some(value.clone());
            }
            s if s.starts_with("--proof-grade-release-transcript-out=") => {
                let value = s
                    .strip_prefix("--proof-grade-release-transcript-out=")
                    .expect("invariant: prefix checked");
                proof_grade_release_transcript_out = Some(value.to_string());
            }
            "--binary-source-provenance-artifact" => {
                i += 1;
                let value = args
                    .get(i)
                    .context("--binary-source-provenance-artifact requires a file path")?;
                binary_source_provenance_artifacts.push(value.clone());
            }
            s if s.starts_with("--binary-source-provenance-artifact=") => {
                let value = s
                    .strip_prefix("--binary-source-provenance-artifact=")
                    .expect("invariant: prefix checked");
                binary_source_provenance_artifacts.push(value.to_string());
            }
            "--entry" => {
                i += 1;
                let value = args.get(i).context("--entry requires an address")?;
                entry = Some(value.clone());
            }
            s if s.starts_with("--entry=") => {
                let value = s.strip_prefix("--entry=").expect("invariant: prefix checked");
                entry = Some(value.to_string());
            }
            "--max-iterations" => {
                i += 1;
                let value = args.get(i).context("--max-iterations requires a numeric value")?;
                max_iterations = value
                    .parse::<usize>()
                    .context("--max-iterations must be a positive integer")?;
                if max_iterations == 0 {
                    anyhow::bail!("--max-iterations must be at least 1");
                }
            }
            s if s.starts_with("--max-iterations=") => {
                let value = s.strip_prefix("--max-iterations=").expect("invariant: prefix checked");
                max_iterations = value
                    .parse::<usize>()
                    .context("--max-iterations must be a positive integer")?;
                if max_iterations == 0 {
                    anyhow::bail!("--max-iterations must be at least 1");
                }
            }
            "--intent" => {
                i += 1;
                let value = args.get(i).context("--intent requires a file path")?;
                intent = Some(value.clone());
            }
            s if s.starts_with("--intent=") => {
                let value = s.strip_prefix("--intent=").expect("invariant: prefix checked");
                intent = Some(value.to_string());
            }
            "--baseline" => {
                i += 1;
                let value = args.get(i).context("--baseline requires a file path")?;
                baseline = Some(value.clone());
            }
            s if s.starts_with("--baseline=") => {
                let value = s.strip_prefix("--baseline=").expect("invariant: prefix checked");
                baseline = Some(value.to_string());
            }
            "--current" => {
                i += 1;
                let value = args.get(i).context("--current requires a file path")?;
                current = Some(value.clone());
            }
            s if s.starts_with("--current=") => {
                let value = s.strip_prefix("--current=").expect("invariant: prefix checked");
                current = Some(value.to_string());
            }
            "--report-dir" => {
                i += 1;
                let value = args.get(i).context("--report-dir requires a directory path")?;
                report_dir = Some(value.clone());
            }
            s if s.starts_with("--report-dir=") => {
                let value = s.strip_prefix("--report-dir=").expect("invariant: prefix checked");
                report_dir = Some(value.to_string());
            }
            "--function" => {
                i += 1;
                let value = args.get(i).context("--function requires a function name")?;
                focused_function = Some(value.clone());
            }
            s if s.starts_with("--function=") => {
                let value = s.strip_prefix("--function=").expect("invariant: prefix checked");
                focused_function = Some(value.to_string());
            }
            "--solver" => {
                i += 1;
                let value = args.get(i).context(
                    "--solver requires a solver name (for check/build/report routing: ay; solvers/doctor can inspect known tools)",
                )?;
                if !solver_detect::is_known_solver(value) {
                    let known = solver_detect::known_solver_names().join(", ");
                    anyhow::bail!("unknown solver `{value}`: known solvers are {known}");
                }
                solver = Some(value.clone());
            }
            s if s.starts_with("--solver=") => {
                let value = s.strip_prefix("--solver=").expect("invariant: prefix checked");
                if !solver_detect::is_known_solver(value) {
                    let known = solver_detect::known_solver_names().join(", ");
                    anyhow::bail!("unknown solver `{value}`: known solvers are {known}");
                }
                solver = Some(value.to_string());
            }
            "--backend" => {
                i += 1;
                let value =
                    args.get(i).context("--backend requires a backend name (llvm, trust-cg)")?;
                let backend_name = normalize_codegen_backend(value).ok_or_else(|| {
                    let known = known_codegen_backend_names().join(", ");
                    anyhow::anyhow!("unknown backend `{value}`: known backends are {known}")
                })?;
                backend = Some(backend_name.to_string());
            }
            s if s.starts_with("--backend=") => {
                let value = s.strip_prefix("--backend=").expect("invariant: prefix checked");
                let backend_name = normalize_codegen_backend(value).ok_or_else(|| {
                    let known = known_codegen_backend_names().join(", ");
                    anyhow::anyhow!("unknown backend `{value}`: known backends are {known}")
                })?;
                backend = Some(backend_name.to_string());
            }
            "--from" => {
                i += 1;
                let value = args.get(i).context("--from requires a git ref")?;
                from_ref = Some(value.clone());
            }
            s if s.starts_with("--from=") => {
                let value = s.strip_prefix("--from=").expect("invariant: prefix checked");
                from_ref = Some(value.to_string());
            }
            "--to" => {
                i += 1;
                let value = args.get(i).context("--to requires a value")?;
                to_ref = Some(value.clone());
            }
            s if s.starts_with("--to=") => {
                let value = s.strip_prefix("--to=").expect("invariant: prefix checked");
                to_ref = Some(value.to_string());
            }
            "--scope" => {
                i += 1;
                let value = args.get(i).context("--scope requires a path prefix")?;
                scope = Some(value.clone());
            }
            s if s.starts_with("--scope=") => {
                let value = s.strip_prefix("--scope=").expect("invariant: prefix checked");
                scope = Some(value.to_string());
            }
            "--manifest-path" => {
                i += 1;
                let value = args.get(i).context("--manifest-path requires a file path")?;
                manifest_path = Some(value.clone());
                passthrough.push("--manifest-path".to_string());
                passthrough.push(value.clone());
                saw_passthrough_argument = true;
            }
            s if s.starts_with("--manifest-path=") => {
                let value = s.strip_prefix("--manifest-path=").expect("invariant: prefix checked");
                manifest_path = Some(value.to_string());
                passthrough.push(args[i].clone());
                saw_passthrough_argument = true;
            }
            _ => {
                let arg = args[i].clone();
                if manifest_path.is_none()
                    && single_file.is_none()
                    && !saw_passthrough_argument
                    && arg.ends_with(".rs")
                    && !arg.starts_with('-')
                {
                    single_file = Some(arg.clone());
                }
                passthrough.push(arg);
                saw_passthrough_argument = true;
            }
        }
        i += 1;
    }

    let is_single_file = single_file.is_some();
    if explicit_strict && memory_safe {
        bail!(
            "--strict conflicts with --memory-safe; choose fail-closed strict verification or the advisory memory-safe mode"
        );
    }
    if explicit_strict && allow_l0_gaps {
        bail!(
            "--strict conflicts with --allow-l0-gaps; choose fail-closed strict verification or the advisory gap-tolerant mode"
        );
    }
    if explicit_strict && explicit_allow_unsupported {
        bail!(
            "--strict conflicts with --allow-unsupported; choose strict complete binary coverage or explicitly permit partial coverage"
        );
    }
    if explicit_strict && survey {
        bail!(
            "--strict conflicts with --survey; choose fail-closed strict verification or non-aborting survey coverage"
        );
    }
    if survey && allow_l0_gaps {
        bail!(
            "--survey conflicts with --allow-l0-gaps; survey already selects a non-aborting native route"
        );
    }
    if certify && (memory_safe || allow_l0_gaps || survey) {
        bail!(
            "--certify is the release gate (full static discharge) and cannot be combined with a loosening lane (--memory-safe, --allow-l0-gaps, --survey)"
        );
    }
    if memory_safe && allow_l0_gaps {
        bail!(
            "--memory-safe conflicts with --allow-l0-gaps; choose the narrow authenticated safe-code demotion or the broad advisory gap-tolerant lane"
        );
    }
    if survey && memory_safe {
        bail!(
            "--survey conflicts with --allow-memory-safe-panics; survey already selects a non-aborting native route"
        );
    }

    Ok(SubcommandArgs {
        format,
        passthrough,
        manifest_path,
        single_file,
        is_single_file,
        rewrite,
        max_iterations,
        intent,
        baseline,
        from_ref,
        to_ref,
        scope,
        current,
        standalone,
        allow_l0_gaps,
        hardened,
        survey,
        hardened_override,
        trust_profile,
        report_dir,
        focused_function,
        solver,
        backend,
        inline,
        entry,
        all_functions,
        strict,
        memory_safe,
        certify,
        checked_certificate_artifacts,
        checked_certificate_manifests,
        checked_certificate_export_dir,
        checked_certificate_checker,
        proof_grade_release_transcript_out,
        binary_source_provenance_artifacts,
    })
}

fn validate_trust_profile_value(value: &str) -> Result<()> {
    if value.trim().is_empty() {
        bail!("--trust-profile requires a non-empty profile name");
    }
    if value.starts_with('-') {
        bail!("--trust-profile value `{value}` looks like another flag");
    }
    Ok(())
}

pub(crate) fn usage_text() -> String {
    [
        "targo trust: Trust verification driver",
        "Canonical frontend: targo is the Trust Cargo replacement; use `targo trust ...` for Trust verification and release evidence.",
        "",
        "Subcommands:",
        "  targo trust check [file]       Verify the current crate or a single file",
        "  targo trust check <file.lean>  Kernel-check standalone Clean/Lean with the linked CIC kernel",
        "  targo trust build [file]       Verify and build the crate or a single file",
        "  targo trust test               Verify and run tests with certified clause monitors",
        "  targo trust version            Emit Trust product/toolchain identity",
        "  targo trust release check      Run Trust release evidence gates",
        "  targo trust release validate <gate>  Run release validation gates",
        "  targo trust deps validate       Validate Trust-owned dependency metadata",
        "  targo trust verify examples     Check verifier example Expected headers/output",
        "  targo trust verify cargo-cache  Materialize registry-only Cargo seed cache for release full-verify",
        "  targo trust gate check-all      Run repository compile and CLI metadata gates",
        "  targo trust gate coherence      Check recorded submodule SHAs type-check together",
        "  targo trust gate verify-examples  Alias for examples verify",
        "  targo trust falsify            Run the verifier falsification self-test (proved/ prove, mutant/ fail)",
        "  targo trust prove --source <file.rs> [--json]  Measure fail-closed kernel-proof coverage",
        "  targo trust survey <crate>     Survey a crate's obligations to per-obligation JSON (status + reason)",
        "  targo trust gap [survey.json]  Classify a survey into user-logic vs derived gap + reason histogram",
        "  targo trust benchmark program-index  Run compile/verify program-index benchmarks",
        "  targo trust lift <binary>      Lift a binary into TrustIr and summarize coverage",
        "  targo trust verify-binary <binary>  Generate binary VCs from a lifted binary",
        "  targo trust decompile <binary> --to trust_ir|rust|trust-cg|wasm  Produce conservative decompilation output",
        "  targo trust convert <binary> --to trust_ir|rust|trust-cg|wasm  Convert binary-derived TrustIr",
        "  targo trust exploit-find <input> --target compiler|verifier|lifter  Report Phase VI scaffold status",
        "  targo trust hardened-lab      Gate standalone hardened claims plus rootless walkthroughs",
        "  targo trust proof-concurrency-producer  Audit/gate concurrency proof artifact production",
        "  targo trust domination         Prove or block Rust-vs-Trust total-domination claims",
        "  targo trust domination upstream-tests  Re-import/adapt upstream Rust tests and write the scorecard",
        "  targo trust report [file]      Generate a verification report",
        "  targo trust report-query --report <json> [--function <name>]  Query a saved verification report",
        "  targo trust loop [file]        Run the prove-strengthen-backprop loop",
        "  targo trust self-improve       Measure the Trust-on-Trust proof frontier and repair targets",
        "  targo trust repo <command>      Run repository maintenance/build helpers",
        "  targo trust bootstrap <command> Run Trust stage0 maintenance scripts",
        "  targo trust diff <ref>..<ref>   Run a non-proof source-contract audit between git refs",
        "  targo trust diff [baseline.json]  Compare verification state against a baseline",
        "  targo trust init [file]        Scaffold inert, review-required contract candidates",
        "  targo trust temporal [path]    Inspect the temporal engine boundary; exits 2 without harness execution pending authenticated input/output binding",
        "  targo trust solvers            Detect and report solver status",
        "  targo trust doctor             Show compiler/setup status and solver availability",
        "  targo trust cache stats        Print build-cache entries, total size, root path",
        "  targo trust cache gc [--max-size N]  LRU evict build-cache entries to fit cap",
        "  targo trust cache clear --yes  Wipe the build-cache (requires --yes confirm)",
        "  targo trust cache info <hex>   Print metadata.json for one build-cache entry",
        "  targo trust help               Show this help",
        "",
        "Options:",
        "  --format <fmt>            Output format: terminal (default), json, html",
        "  --json                    Alias for --format json",
        "  --standalone              Run a non-proof source audit (compiler verification is not performed)",
        "  --allow-l0-gaps           Broad development warning mode; conflicts with --memory-safe",
        "  --allow-memory-safe-panics  Narrow safe-code panic demotion; rejects unsafe UB and conflicts with --allow-l0-gaps (alias: --memory-safe)",
        "  --hardened                Explicitly enable default hardened boundary profile",
        "  --no-hardened             Disable the default hardened boundary profile for this run",
        "  --trust-profile <name>    Select hardened profile (default: unix_hardened)",
        "  --rewrite                 Enable rewrite loop mode on check/build",
        "  --max-iterations <N>      Maximum loop iterations (default: 10)",
        "  --from <ref>              Git ref for the 'from' side of diff",
        "  --to <value>              Git ref for diff, or binary output target: trust_ir, rust, trust-cg, or wasm",
        "  --scope <path>            Scope git diff to a path prefix (e.g., crates/)",
        "  --baseline <path>         Baseline report JSON for diff subcommand",
        "  --current <path>          Current report JSON for diff (compare two reports)",
        "  --report-dir <dir>        Write proof report files (JSON, HTML, NDJSON) to dir",
        "  --function <name>         Focus check exit semantics on one function selector",
        "  --inline                  Write inert, commented contract candidates into source files (init)",
        "  --entry <addr>            Entry address for binary commands (decimal or 0x-prefixed hex)",
        "  --all                     Select all detected function symbols for binary commands",
        "  --strict                  Explicit fail-closed mode; conflicts with --memory-safe (binary strictness is the default)",
        "  --allow-unsupported       Permit partial binary coverage",
        "  --checked-cert-artifact <path>  Import/reference a checked binary certificate artifact for verify-binary/decompile/convert",
        "  --checked-cert-manifest <path>  Import/reference checked binary certificate artifacts listed by manifest",
        "  --checked-cert-export-dir <dir>  Request checked certificate production/export artifacts for verify-binary/decompile/convert",
        "  --checked-cert-checker <path>  Run an external checked-certificate production checker for loaded certificate rows",
        "  --proof-grade-release-transcript-out <path>  Write/read back a validated proof-grade release transcript artifact from decompile/convert release evidence",
        "  --binary-source-provenance-artifact <path>  Import exact binary-source provenance for rewrite mode",
        "  --target <target>         Target for exploit-find: compiler, verifier, or lifter",
        "  --backend <name>          Codegen backend: llvm (default) or trust-cg",
        "  --solver <name>           Request source solver routing (currently ay); solvers/doctor inspect known tools",
        "  --manifest-path <path>    Anchor crate-mode commands to a specific Cargo.toml",
        "",
        "Binary target support:",
        "  Supported lifting/decompilation targets: little-endian ELF x86-64/AArch64 and little-endian Mach-O AArch64",
        "  AArch64 support includes conservative lift/decompile coverage; proof-grade replay, checked certificates, exact provenance, source-backprop reconstruction, and target validation still fail closed when evidence is missing",
        "  JSON reports expose source_backpropagation_gate and proof_grade_release_* fields so binary/decompile evidence is not confused with source rewrite permission",
        "  Unsupported targets, big-endian binaries, PE/COFF lifting, Mach-O x86-64, AArch32, and i386 fail closed",
        "",
        "Examples:",
        "  targo trust check                     Verify the current crate",
        "  targo trust check path.rs             Verify a single file",
        "  targo trust version --json            JSON identity for the complete bound Trust toolchain",
        "  targo trust release check --profile metadata --json",
        "  targo trust release check --profile publication --visibility public --json",
        "  targo trust release check --profile product-proof --json",
        "  targo trust verify examples --metadata-only",
        "  targo trust verify cargo-cache --repo-root . --cargo-home build/full-verify/cargo-seed-home --json-output build/full-verify/cargo-cache-materialization.json",
        "  targo trust repo check",
        "  targo trust repo dev-test trust-vcgen",
        "  targo trust bootstrap recreate --check",
        "  targo trust verify self --full-verifier",
        "  targo trust deps status --fetch",
        "  targo trust gate check-all --repo-root .",
        "  targo trust benchmark program-index --suite proof-design --limit 2",
        "  targo trust lift ./target/release/app  Lift binary functions into TrustIr",
        "  targo trust verify-binary ./target/release/app  Generate binary VCs",
        "  targo trust lift app --all --allow-unsupported",
        "  targo trust lift app --entry 0x401000 --json",
        "  targo trust verify-binary app --entry 0x401000 --json",
        "  targo trust lift app --strict          Fail on unsupported lift coverage",
        "  targo trust decompile app --to trust_ir    Summarize partial lifted TrustIr output",
        "  targo trust decompile app --to rust --json  JSON report with exploratory Rust skeleton",
        "  targo trust convert app --to wasm   Report unsupported binary-to-Wasm conversion",
        "  targo trust exploit-find app --target lifter --json",
        "  targo trust proof-concurrency-producer audit --format json",
        "  targo trust domination               One-line launch/readiness comparison gate",
        "  targo trust domination upstream-tests  Refresh, apply, execute, and score upstream tests",
        "  targo trust domination --json        Machine-readable blocker and AI-directive report",
        "  targo trust domination --write-template domination.toml",
        "  targo trust check --standalone        Non-proof hardened source audit (no compiler verification)",
        "  targo trust check                     Verify with default Unix hardened profile",
        "  targo trust check --no-hardened       Verify without hardened boundary profile",
        "  targo trust check --trust-profile coreutils_hardened  Select a named hardened profile",
        "  targo trust check --function midpoint --format json",
        "  targo trust hardened-lab --json       Validate standalone claims plus walkthroughs",
        "  targo trust check --allow-l0-gaps     Development comparison: leave verifier gaps as warnings",
        "  targo trust build --backend trust-cg     Verify and build with the trust-cg backend",
        "  targo trust report --format json       JSON verification report",
        "  targo trust report --trust-profile coreutils_hardened --format json",
        "  targo trust report --format html       HTML verification report",
        "  targo trust report-query --report target/trust/report.json --function midpoint",
        "  targo trust loop file.rs --max-iterations 5",
        "  targo trust diff main..feature         Git ref source-contract audit (non-proof)",
        "  targo trust diff --from HEAD~5 --to HEAD  Diff last 5 commits",
        "  targo trust diff main..HEAD --scope crates/  Scope to crates/",
        "  targo trust diff main..HEAD --format json   JSON diff output",
        "  targo trust diff --baseline base.json --current cur.json",
        "  targo trust diff --baseline report.json   # baseline vs empty (CI gate)",
        "  targo trust init                      Print commented contract candidates for review",
        "  targo trust init --inline             Write commented candidates; review before enabling",
        "  targo trust init src/lib.rs           Scaffold commented candidates for one file",
        "  targo trust doctor                    Show compiler, backend, config, transport, and solver status",
        "  targo trust doctor --format json      Machine-readable setup status",
        "  targo trust solvers                   Show solver status",
        "  targo trust solvers --format json     Solver status as JSON",
        "  targo trust check --solver ay         Request ay for source verification",
        "",
        "Configuration:",
        "  Declare a [trust] table in your project's Targo.toml (or Cargo.toml) to control verification.",
        "  See targo-trust/README.md, section `[trust]`, for the supported keys and defaults.",
        "  TRUSTFLAGS is to trust verification what RUSTFLAGS is to codegen: space-separated -Ztrust-* options",
        "  appended after the [trust]-derived policy for one run, so the TRUSTFLAGS value wins",
        "  (e.g. TRUSTFLAGS=\"-Ztrust-verify-function-budget-ms=60000\" targo trust check).",
        "  CARGO_ENCODED_TRUSTFLAGS (U+001F-separated) takes precedence over TRUSTFLAGS, like Cargo's encoded rustflags.",
        "  Only verified -Ztrust-* policy options are accepted; reserved authentication/transport options",
        "  (session, crate-role, package-name, proof-artifact-root, output) and non-trust flags are rejected —",
        "  use RUSTFLAGS for codegen flags. -Ztrust-* inside RUSTFLAGS is ignored with a warning.",
        "",
        "Behavior:",
        "  Invokes the discovered Trust toolchain: trustc, plus the sibling targo binary for crate-mode Cargo execution.",
        "  Source check/build/report/loop verify STRICT (fail-closed) for the crate under check by default; --allow-l0-gaps selects allow_l0_gaps (warnings).",
        "  Frontend architecture: Rust/THIR and Lean/Clean lower directly to canonical typed TrustIr. Until source contracts and obligation ownership are bound to TrustIr SSA, crate check/report retain authenticated MIR-derived compatibility and differential evidence; MIR is not the canonical semantics or end-state frontend.",
        "  Removed release aliases (`targo trust verify full`, `preflight`, and `full-preflight`) reject Python/shell-era orchestration; use cargo-cache, repo-gate, verify self --full-verifier, and release check for default evidence.",
        "  `targo trust domination upstream-tests` dispatches the Trust-owned `trust-upstream-compat port` engine; Python is not used.",
        "  Compiler discovery priority: sibling trustc next to targo-trust, then repo-local stage2/stage3 Trust builds.",
        "  Check/build/report/loop enable the unix_hardened profile by default; pass --no-hardened only for compatibility triage.",
        "  Check/report require canonical trustc by default; --standalone is an explicit non-proof source audit and still uses hardened checks unless --no-hardened is passed.",
        "",
        "Exit codes:",
        "  0  All obligations proved, no compiler errors",
        "  1  Verification failures, runtime-checked or inconclusive results after compiler success",
        "  2  Internal/setup/report error (e.g., trustc not found, missing --baseline)",
        "  other nonzero  Underlying trustc/targo compiler exit code when compilation fails",
    ]
    .join("\n")
        + "\n"
}

pub(crate) fn print_usage() {
    eprint!("{}", usage_text());
}

pub(crate) fn print_usage_stdout() {
    print!("{}", usage_text());
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rust_vs_trust_cli_help_pins_domination_upstream_tests_to_rust_porting() {
        let usage = usage_text();

        assert!(usage.contains("targo trust domination upstream-tests"));
        assert!(usage.contains("Trust-owned `trust-upstream-compat port` engine"));
        assert!(usage.contains("Python is not used."));
        assert!(!usage.contains("targo trust rust-vs-trust"));
        assert!(!usage.lines().any(|line| line.trim_start().starts_with("cargo trust ")));
        assert!(!usage.contains("cargo.rs"), "help must not expose bootstrap cargo.rs internals");
    }

    #[test]
    fn usage_text_documents_trust_only_pipeline_discovery() {
        let usage = usage_text();

        assert!(usage.contains("Canonical frontend: targo is the Trust Cargo replacement"));
        assert!(usage.contains("sibling trustc next to targo-trust"));
        assert!(usage.contains("repo-local stage2/stage3 Trust builds"));
        assert!(usage.contains("sibling targo binary"));
        assert!(usage.contains("Trust stage0 maintenance scripts"));
        assert_eq!(
            usage.matches("targo trust gate check-all").count(),
            2,
            "help should list one subcommand row and one example, not duplicate subcommand rows"
        );
        assert!(!usage.contains("cargo sanity gates"));
        assert!(!usage.contains("rustup"), "help must not advertise inherited toolchain discovery");
        assert!(!usage.contains("TRUSTC="), "help must not advertise compiler env overrides");
    }

    #[test]
    fn usage_text_documents_full_release_cli_surface() {
        let usage = usage_text();

        for expected in ["targo trust release check", "targo trust release validate <gate>"] {
            assert!(usage.contains(expected), "missing `{expected}`");
        }
        assert!(usage.contains(
            "Removed release aliases (`targo trust verify full`, `preflight`, and `full-preflight`)"
        ));
        assert!(
            !usage.contains("targo trust verify full-preflight"),
            "removed full-preflight must not be advertised as a normal top-level command or example"
        );
    }

    #[test]
    fn usage_text_does_not_advertise_deprecated_deps_aliases() {
        let usage = usage_text();

        assert!(usage.contains("targo trust deps validate"));
        assert!(usage.contains("targo trust deps status --fetch"));
        assert!(!usage.contains("targo trust deps report"));
        assert!(!usage.contains("targo trust deps verify"));
        assert!(!usage.contains("targo trust deps alignment"));
    }

    #[test]
    fn usage_text_points_to_the_actual_configuration_reference() {
        let usage = usage_text();

        assert!(usage.contains("targo-trust/README.md"));
        assert!(usage.contains("section `[trust]`"));
        assert!(!usage.contains("trust-config crate docs"));
    }

    #[test]
    fn usage_text_documents_the_trustflags_override_channel() {
        let usage = usage_text();

        assert!(usage.contains("TRUSTFLAGS is to trust verification what RUSTFLAGS is to codegen"));
        assert!(usage.contains("CARGO_ENCODED_TRUSTFLAGS"));
        assert!(usage.contains("TRUSTFLAGS=\"-Ztrust-verify-function-budget-ms=60000\""));
        assert!(usage.contains("use RUSTFLAGS for codegen flags"));
        assert!(usage.contains("-Ztrust-* inside RUSTFLAGS is ignored with a warning"));
    }

    #[test]
    fn hardened_flag_selects_default_profile() {
        let args = vec!["--hardened".to_string()];
        let parsed = parse_subcommand_args(&args).expect("should parse hardened flag");

        assert!(parsed.hardened);
        assert_eq!(parsed.hardened_override, Some(true));
        assert_eq!(parsed.trust_profile.as_deref(), Some("unix_hardened"));
    }

    #[test]
    fn trust_profile_enables_hardened_mode() {
        let args = vec!["--trust-profile=coreutils_hardened".to_string()];
        let parsed = parse_subcommand_args(&args).expect("should parse trust profile");

        assert!(parsed.hardened);
        assert_eq!(parsed.hardened_override, Some(true));
        assert_eq!(parsed.trust_profile.as_deref(), Some("coreutils_hardened"));
    }

    #[test]
    fn no_hardened_disables_profile_selection() {
        let args = vec!["--no-hardened".to_string()];
        let parsed = parse_subcommand_args(&args).expect("should parse no-hardened flag");

        assert!(!parsed.hardened);
        assert_eq!(parsed.hardened_override, Some(false));
        assert_eq!(parsed.trust_profile, None);
    }

    #[test]
    fn no_hardened_conflicts_with_profile_selection() {
        let args = vec!["--no-hardened".to_string(), "--trust-profile=coreutils_hardened".into()];
        let error = parse_subcommand_args(&args).expect_err("conflicting hardened flags fail");

        assert!(error.to_string().contains("conflicts"));
    }

    #[test]
    fn survey_uses_non_aborting_native_route_without_full_flag() {
        let parsed = parse_subcommand_args(&["--survey".to_string()]).expect("survey parses");
        assert!(parsed.survey);
        assert!(!parsed.strict_artifact_policy());
        assert!(!parsed.strict_result_gate());
        assert!(!parsed.allow_l0_gaps_lane());
    }

    #[test]
    fn memory_safe_is_an_explicit_advisory_mode() {
        let parsed =
            parse_subcommand_args(&["--memory-safe".to_string()]).expect("memory-safe mode parses");
        assert!(parsed.memory_safe);
        assert!(!parsed.allow_l0_gaps);
        assert!(!parsed.allow_l0_gaps_lane());
        assert!(parsed.strict_artifact_policy());
        assert!(!parsed.strict_result_gate());

        let default = parse_subcommand_args(&[]).expect("defaults parse");
        assert!(!default.memory_safe);
        assert!(default.strict_artifact_policy());
        assert!(default.strict_result_gate());

        let error =
            parse_subcommand_args(&["--full-verifier".to_string(), "--memory-safe".to_string()])
                .expect_err("full and memory-safe modes conflict");
        assert!(error.to_string().contains("has been removed"));
    }

    #[test]
    fn strict_and_memory_safe_conflict_independent_of_argument_order() {
        for args in [
            ["--strict".to_string(), "--memory-safe".to_string()],
            ["--memory-safe".to_string(), "--strict".to_string()],
        ] {
            let error = parse_subcommand_args(&args)
                .expect_err("strict and memory-safe must be rejected in either order");
            let message = error.to_string();
            assert!(message.contains("--strict conflicts with --memory-safe"), "{message}");
        }
    }

    #[test]
    fn strict_and_allow_l0_gaps_conflict_independent_of_argument_order() {
        for args in [
            vec!["--strict".to_string(), "--allow-l0-gaps".to_string()],
            vec!["--allow-l0-gaps".to_string(), "--strict".to_string()],
        ] {
            let error = parse_subcommand_args(&args)
                .expect_err("strict and gap-tolerant verification must conflict");
            assert!(error.to_string().contains("--strict conflicts with --allow-l0-gaps"));
        }
    }

    #[test]
    fn memory_safe_and_allow_l0_gaps_conflict_independent_of_argument_order() {
        for args in [
            vec!["--memory-safe".to_string(), "--allow-l0-gaps".to_string()],
            vec!["--allow-l0-gaps".to_string(), "--memory-safe".to_string()],
        ] {
            let error = parse_subcommand_args(&args)
                .expect_err("narrow memory-safe and broad advisory modes must conflict");
            assert!(error.to_string().contains("--memory-safe conflicts with --allow-l0-gaps"));
        }
    }

    #[test]
    fn strict_and_allow_unsupported_conflict_independent_of_argument_order() {
        for args in [
            vec!["--strict".to_string(), "--allow-unsupported".to_string()],
            vec!["--allow-unsupported".to_string(), "--strict".to_string()],
        ] {
            let error = parse_subcommand_args(&args)
                .expect_err("strict and partial binary coverage must conflict");
            assert!(error.to_string().contains("--strict conflicts with --allow-unsupported"));
        }
    }

    #[test]
    fn strict_and_survey_conflict_independent_of_argument_order() {
        for args in [
            vec!["--strict".to_string(), "--survey".to_string()],
            vec!["--survey".to_string(), "--strict".to_string()],
        ] {
            let error =
                parse_subcommand_args(&args).expect_err("strict and survey verification conflict");
            assert!(error.to_string().contains("--strict conflicts with --survey"));
        }
    }

    #[test]
    fn survey_rejects_conflicting_verification_modes() {
        for args in [
            vec!["--survey".to_string(), "--allow-l0-gaps".to_string()],
            vec!["--survey".to_string(), "--memory-safe".to_string()],
        ] {
            let error = parse_subcommand_args(&args).expect_err("survey mode conflict");
            assert!(error.to_string().contains("conflicts"), "{error}");
        }
    }

    #[test]
    fn function_selector_is_consumed_for_focused_check() {
        let args = vec![
            "--function".to_string(),
            "crate::math::midpoint".to_string(),
            "src/lib.rs".to_string(),
        ];
        let parsed = parse_subcommand_args(&args).expect("should parse focused function selector");

        assert_eq!(parsed.focused_function.as_deref(), Some("crate::math::midpoint"));
        assert_eq!(parsed.passthrough, vec!["src/lib.rs"]);
        assert!(parsed.is_single_file);
    }

    #[test]
    fn function_selector_accepts_equals_form() {
        let args = vec!["--function=midpoint".to_string()];
        let parsed = parse_subcommand_args(&args).expect("should parse focused function selector");

        assert_eq!(parsed.focused_function.as_deref(), Some("midpoint"));
        assert!(parsed.passthrough.is_empty());
    }

    #[test]
    fn option_separator_prevents_wrapper_option_capture() {
        let args = vec![
            "--".to_string(),
            "--solver".to_string(),
            "not-a-trust-solver".to_string(),
            "child.rs".to_string(),
        ];
        let parsed = parse_subcommand_args(&args).expect("child arguments should be opaque");

        assert_eq!(parsed.solver, None);
        assert_eq!(parsed.single_file, None);
        assert!(!parsed.is_single_file);
        assert_eq!(parsed.passthrough, args[1..]);
    }

    #[test]
    fn source_before_separator_keeps_single_file_mode() {
        let args = vec![
            "source.rs".to_string(),
            "--".to_string(),
            "--edition".to_string(),
            "2024".to_string(),
        ];
        let parsed =
            parse_subcommand_args(&args).expect("single-file child arguments should parse");

        assert_eq!(parsed.single_file.as_deref(), Some("source.rs"));
        assert!(parsed.is_single_file);
        assert_eq!(
            parsed.passthrough,
            vec!["source.rs".to_string(), "--edition".to_string(), "2024".to_string()]
        );
    }

    #[test]
    fn option_separator_keeps_ref_like_child_arguments_opaque() {
        let args = vec!["--".to_string(), "main..feature".to_string()];
        let parsed = parse_subcommand_args(&args).expect("child ref-like argument should parse");

        assert_eq!(parsed.from_ref, None);
        assert_eq!(parsed.to_ref, None);
        assert_eq!(parsed.passthrough, vec!["main..feature".to_string()]);
    }

    #[test]
    fn generic_parser_does_not_steal_ref_like_cargo_arguments() {
        let args = vec!["--package".to_string(), "crate..variant".to_string()];
        let parsed = parse_subcommand_args(&args).expect("Cargo arguments should remain intact");

        assert_eq!(parsed.from_ref, None);
        assert_eq!(parsed.to_ref, None);
        assert_eq!(parsed.passthrough, args);
    }

    #[test]
    fn rust_suffixed_child_option_value_does_not_select_single_file_mode() {
        let args = vec!["--config".to_string(), "custom.rs".to_string()];
        let parsed = parse_subcommand_args(&args).expect("Cargo arguments should remain opaque");

        assert_eq!(parsed.single_file, None);
        assert!(!parsed.is_single_file);
        assert_eq!(parsed.passthrough, args);
    }

    #[test]
    fn source_must_be_the_first_child_facing_positional() {
        let direct = parse_subcommand_args(&[
            "source.rs".to_string(),
            "--cfg".to_string(),
            "feature=\"demo\"".to_string(),
        ])
        .expect("source-first direct invocation should parse");
        assert_eq!(direct.single_file.as_deref(), Some("source.rs"));

        let cargo = parse_subcommand_args(&["--release".to_string(), "source.rs".to_string()])
            .expect("Cargo invocation should parse");
        assert_eq!(cargo.single_file, None);
        assert!(!cargo.is_single_file);
    }

    #[test]
    fn init_help_requires_review_and_describes_commented_output() {
        let usage = usage_text();
        assert!(usage.contains("Scaffold inert, review-required contract candidates"));
        assert!(usage.contains("Write inert, commented contract candidates into source files"));
        assert!(usage.contains("Write commented candidates; review before enabling"));
    }

    #[test]
    fn crate_mode_restores_cargos_workspace_meaning_of_all() {
        // The compile command, the canonical package selection, and the
        // post-build gate replay all derive their Cargo argv from this one
        // method. When only the gates restored `--workspace`, `targo trust
        // build --all` compiled the default members while the gates resolved
        // every member — a report whose scope the compiler never saw.
        let parsed = parse_subcommand_args(&["--all".to_string()]).expect("`--all` parses");
        assert!(parsed.all_functions);
        assert_eq!(parsed.crate_mode_cargo_args(), vec!["--workspace".to_string()]);

        // An explicit `--workspace` is never doubled. A repeated `--all` still
        // yields exactly one, because the parser consumes every `--all` for the
        // binary-lift selector and none of them survive into the Cargo list.
        for extra in ["--workspace", "--all"] {
            let parsed = parse_subcommand_args(&["--all".to_string(), extra.to_string()])
                .expect("explicit selector parses");
            assert_eq!(
                parsed.crate_mode_cargo_args().iter().filter(|arg| *arg == "--workspace").count(),
                1,
                "`--all {extra}` must select the workspace exactly once"
            );
        }

        // The wrapper's own `--` is consumed here and everything after it is
        // forwarded byte-for-byte, so the Cargo list normally holds no
        // separator at all.
        let parsed = parse_subcommand_args(&[
            "--all".to_string(),
            "--".to_string(),
            "--nocapture".to_string(),
        ])
        .expect("wrapper separator parses");
        assert_eq!(
            parsed.crate_mode_cargo_args(),
            vec!["--nocapture".to_string(), "--workspace".to_string()]
        );

        // A separator that does reach the Cargo list is Cargo's own, and it
        // ends Cargo's arguments: a selector placed after it would be handed to
        // the test binary rather than widening the build.
        let parsed = parse_subcommand_args(&[
            "--all".to_string(),
            "--".to_string(),
            "--".to_string(),
            "--nocapture".to_string(),
        ])
        .expect("forwarded Cargo separator parses");
        assert_eq!(
            parsed.crate_mode_cargo_args(),
            vec!["--workspace".to_string(), "--".to_string(), "--nocapture".to_string()]
        );

        // Without `--all` the list is exactly what the user typed.
        let parsed =
            parse_subcommand_args(&["--release".to_string()]).expect("plain invocation parses");
        assert_eq!(parsed.crate_mode_cargo_args(), vec!["--release".to_string()]);
    }
}
