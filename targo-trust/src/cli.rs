// targo trust CLI: argument parsing and usage output
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use anyhow::{Context, Result, bail};

use crate::config::{
    DEFAULT_TRUST_PROFILE, known_codegen_backend_names, normalize_codegen_backend,
};
use crate::solver_detect;
use crate::test_target_panics::{TestTargetPanicChoice, TestTargetPanicPolicy};
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
    /// `targo trust diff --baseline <file>`: the committed obligation
    /// baseline (`trust-baseline v1`, `crate::baseline`) a live check is
    /// compared against.
    pub(crate) baseline: Option<String>,
    /// `targo trust check --save-baseline <file>`: write this run's proved
    /// obligation keys into the committed baseline (`crate::baseline`).
    pub(crate) save_baseline: Option<String>,
    /// Git ref for the "from" side of a diff (e.g., `main`, `HEAD~3`).
    pub(crate) from_ref: Option<String>,
    /// Git ref for the "to" side of a diff (e.g., `feature`, `HEAD`).
    pub(crate) to_ref: Option<String>,
    /// Scope filter for git diff (e.g., `crates/`, `src/`).
    pub(crate) scope: Option<String>,
    /// When true, use standalone source-level analysis instead of invoking trustc.
    pub(crate) standalone: bool,
    /// When true, allow Level 0 verifier gaps to remain compiler warnings, and
    /// have the exit-code gate REPORT a genuine unknown as a condition of the
    /// pass rather than fail on it (the ramp; strict/certify are the destination).
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
    /// Fresh output directory for observational MIR/native-bundle exports in normal Cargo check.
    pub(crate) dump_verifier_inputs: Option<String>,
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
    /// Trust (v6/D1): directory where the compiler must publish the
    /// kernel-graded Clean goal artifact (`-Ztrust-dump=spec-clean:` for a
    /// direct trustc invocation, the `TRUST_SPEC_EMIT_DIR` driver transport in
    /// Cargo crate mode). Set by `targo trust spec --emit clean`, which reads
    /// the artifact back; absolute path required.
    pub(crate) spec_emit_dir: Option<String>,
    /// `--test-target-panics=<strict|runtime-checked>`: how a PANIC-CLASS
    /// obligation raised in a cargo target of kind `["test"]` is classified.
    /// NO DEFAULT and NO environment variable — an absent flag resolves to
    /// `TestTargetPanicChoice::Strict`, which is byte-for-byte today's
    /// behaviour.
    ///
    /// This is the RAW choice. Nothing may apply it without first binding it to
    /// this run's check environment through
    /// [`SubcommandArgs::test_target_panic_policy`]; see
    /// `crate::test_target_panics` for the exact obligation set and why the
    /// environment is part of the decision.
    pub(crate) test_target_panics: TestTargetPanicChoice,
    /// `--worker-threads <n>`: the verifier worker-thread cap for this run
    /// (`-Ztrust-verify-worker-threads`, 0..=256; 0, the default, is no cap).
    /// A scheduling choice, not a bound: the budget profile records it and
    /// keeps it out of its id. Its one spelling since TRUSTFLAGS was deleted
    /// (DECISION_QUEUE T7a).
    pub(crate) worker_threads: u64,
    /// `--no-proc-macro-isolation` clears this (D21). By default a verified
    /// unit's proc macros expand in the compiler's sandboxed worker, which is
    /// what admits an unaudited proc-macro dependency; without it they would
    /// run in the verifying compiler, so the unit is refused.
    pub(crate) proc_macro_isolation: bool,
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

    /// The RESOLVED `--test-target-panics` policy for this run: the user's raw
    /// choice bound to the check environment `strict_artifact_policy()`
    /// establishes.
    ///
    /// This is the ONLY way a `TestTargetPanicPolicy::RuntimeChecked` is
    /// constructed outside tests, so the reclassification can never be applied
    /// against an environment nobody established. It lives here, next to
    /// `strict_artifact_policy`, because that is the one bit it reads: in the
    /// strict lane targo appends `-C overflow-checks=yes` to every compiled
    /// unit itself, and in the advisory/survey lanes it deliberately preserves
    /// the Cargo profile and therefore cannot claim the check was emitted.
    pub(crate) fn test_target_panic_policy(&self) -> TestTargetPanicPolicy {
        self.test_target_panics.resolve(self.strict_artifact_policy())
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
    /// (`-Z trust-policy=advisory`): unknowns are reported, never fatal. The
    /// parser rejects combining it with full mode.
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
        let separator = args.iter().position(|arg| arg == "--").unwrap_or(args.len());
        if self.all_functions
            && !args[..separator].iter().any(|arg| arg == "--workspace" || arg == "--all")
        {
            args.insert(separator, "--workspace".to_string());
        }
        args
    }
}

/// A value Cargo accepts for `-j`/`--jobs`: an integer (negative counts back
/// from the CPU count) or `default`.
pub(crate) fn is_cargo_jobs_value(value: &str) -> bool {
    value == "default" || value.parse::<i32>().is_ok()
}

/// Cargo's job count spelled as one token: `--jobs=N`, `-jN` or `-j=N`.
pub(crate) fn is_inline_cargo_jobs(arg: &str) -> bool {
    arg.strip_prefix("--jobs=")
        .or_else(|| arg.strip_prefix("-j").map(|rest| rest.strip_prefix('=').unwrap_or(rest)))
        .is_some_and(is_cargo_jobs_value)
}

/// How many arguments, from `args[index]`, spell Cargo's job count: 2 for
/// `-j N` or `--jobs N`, 1 for a bare `-j`/`--jobs` or an inline spelling
/// ([`is_inline_cargo_jobs`]), `None` when `args[index]` is not one. The Lean
/// routes accept the count and ignore it: the kernel schedules its own batch, and
/// aterm's build admission appends `--jobs=N` to every admitted command line.
pub(crate) fn cargo_jobs_hint_width(args: &[String], index: usize) -> Option<usize> {
    let arg = args.get(index)?.as_str();
    if arg == "-j" || arg == "--jobs" {
        let takes_value = args.get(index + 1).is_some_and(|value| is_cargo_jobs_value(value));
        return Some(if takes_value { 2 } else { 1 });
    }
    is_inline_cargo_jobs(arg).then_some(1)
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
    let mut save_baseline: Option<String> = None;
    let mut from_ref: Option<String> = None;
    let mut to_ref: Option<String> = None;
    let mut scope: Option<String> = None;
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
    let mut dump_verifier_inputs: Option<String> = None;
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
    let mut spec_emit_dir: Option<String> = None;
    // Absent flag == `Strict` == today. Never inferred from anything else.
    let mut test_target_panics = TestTargetPanicChoice::default();
    let mut worker_threads: u64 = 0;
    let mut proc_macro_isolation = true;
    // Single-file mode is selected only by the first child-facing positional.
    // Once an opaque Cargo/rustc argument has been seen, a later `.rs` token may
    // be that option's value (for example `--config custom.rs`) and must not
    // silently switch the entire invocation from targo to direct trustc.
    let mut saw_passthrough_argument = false;
    // Cargo's job count is a scheduling hint, not an operand or an option
    // whose value could be a `.rs` path. It is forwarded to Cargo unchanged,
    // does not count as the first passthrough argument, and is dropped in
    // single-file mode, where trustc runs once and nothing schedules jobs.
    // aterm's build admission appends `--jobs=N` to every admitted line.
    let mut jobs_positions: Vec<usize> = Vec::new();
    let mut i = 0;

    while i < args.len() {
        match args[i].as_str() {
            "-j" | "--jobs" => {
                jobs_positions.push(passthrough.len());
                passthrough.push(args[i].clone());
                if let Some(value) = args.get(i + 1).filter(|value| is_cargo_jobs_value(value)) {
                    i += 1;
                    jobs_positions.push(passthrough.len());
                    passthrough.push(value.clone());
                }
            }
            s if is_inline_cargo_jobs(s) => {
                jobs_positions.push(passthrough.len());
                passthrough.push(args[i].clone());
            }
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
            crate::test_target_panics::FLAG => {
                i += 1;
                let value = args.get(i).with_context(|| {
                    format!(
                        "{} requires a value (`{}` or `{}`)",
                        crate::test_target_panics::FLAG,
                        crate::test_target_panics::STRICT_VALUE,
                        crate::test_target_panics::RUNTIME_CHECKED_VALUE,
                    )
                })?;
                test_target_panics = TestTargetPanicChoice::parse(value)?;
            }
            s if s.starts_with(crate::test_target_panics::FLAG_EQ) => {
                let value = s
                    .strip_prefix(crate::test_target_panics::FLAG_EQ)
                    .expect("invariant: prefix checked");
                test_target_panics = TestTargetPanicChoice::parse(value)?;
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
                let canonical = canonical_trust_profile_value(value)?;
                hardened_override = Some(true);
                hardened = true;
                trust_profile = Some(canonical.to_string());
            }
            s if s.starts_with("--trust-profile=") => {
                if hardened_override == Some(false) {
                    bail!("--trust-profile conflicts with --no-hardened");
                }
                let value = s.strip_prefix("--trust-profile=").expect("invariant: prefix checked");
                let canonical = canonical_trust_profile_value(value)?;
                hardened_override = Some(true);
                hardened = true;
                trust_profile = Some(canonical.to_string());
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
            "--worker-threads" => {
                i += 1;
                let value = args.get(i).context(WORKER_THREADS_DOMAIN)?;
                worker_threads = parse_worker_threads(value)?;
            }
            "--no-proc-macro-isolation" => {
                proc_macro_isolation = false;
            }
            s if s.starts_with("--worker-threads=") => {
                let value = s.strip_prefix("--worker-threads=").expect("invariant: prefix checked");
                worker_threads = parse_worker_threads(value)?;
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
            "--save-baseline" => {
                i += 1;
                let value = args.get(i).context("--save-baseline requires a file path")?;
                save_baseline = Some(value.clone());
            }
            s if s.starts_with("--save-baseline=") => {
                let value = s.strip_prefix("--save-baseline=").expect("invariant: prefix checked");
                save_baseline = Some(value.to_string());
            }
            "--report-dir" => {
                i += 1;
                let value = args.get(i).context("--report-dir requires a directory path")?;
                report_dir = Some(value.clone());
            }
            "--dump-verifier-inputs" => {
                i += 1;
                let value =
                    args.get(i).context("--dump-verifier-inputs requires a new directory")?;
                if value.is_empty() || value.starts_with('-') || dump_verifier_inputs.is_some() {
                    bail!("--dump-verifier-inputs requires exactly one nonempty directory");
                }
                dump_verifier_inputs = Some(value.clone());
            }
            s if s.starts_with("--dump-verifier-inputs=") => {
                let value = s.strip_prefix("--dump-verifier-inputs=").expect("prefix checked");
                if value.is_empty() || dump_verifier_inputs.is_some() {
                    bail!("--dump-verifier-inputs requires exactly one nonempty directory");
                }
                dump_verifier_inputs = Some(value.to_owned());
            }
            "--spec-emit-dir" => {
                i += 1;
                let value =
                    args.get(i).context("--spec-emit-dir requires an absolute directory path")?;
                validate_spec_emit_dir_value(value)?;
                spec_emit_dir = Some(value.clone());
            }
            s if s.starts_with("--spec-emit-dir=") => {
                let value = s.strip_prefix("--spec-emit-dir=").expect("invariant: prefix checked");
                validate_spec_emit_dir_value(value)?;
                spec_emit_dir = Some(value.to_string());
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
    if is_single_file {
        for position in jobs_positions.into_iter().rev() {
            passthrough.remove(position);
        }
    }
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
        save_baseline,
        from_ref,
        to_ref,
        scope,
        standalone,
        allow_l0_gaps,
        hardened,
        survey,
        hardened_override,
        trust_profile,
        report_dir,
        dump_verifier_inputs,
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
        spec_emit_dir,
        test_target_panics,
        worker_threads,
        proc_macro_isolation,
    })
}

/// What `--worker-threads` accepts: the compiler's own domain for
/// `-Ztrust-verify-worker-threads` (`parse_trust_verify_worker_threads`).
const WORKER_THREADS_DOMAIN: &str =
    "--worker-threads requires an integer from 0 through 256 (0, the default, is no cap)";

fn parse_worker_threads(value: &str) -> Result<u64> {
    match value.parse::<u64>() {
        Ok(count) if count <= 256 => Ok(count),
        _ => bail!("{WORKER_THREADS_DOMAIN}; got `{value}`"),
    }
}

/// Trust (v6/D1): the spec-emit directory is handed to the compiler as an
/// artifact sink, so it must never be resolved against ambient cwd — the same
/// absolute-path rule `trust-proof-artifact-root` enforces compiler-side.
fn validate_spec_emit_dir_value(value: &str) -> Result<()> {
    if value.trim().is_empty() {
        bail!("--spec-emit-dir requires a non-empty absolute directory path");
    }
    if !std::path::Path::new(value).is_absolute() {
        bail!(
            "--spec-emit-dir requires an ABSOLUTE path (got `{value}`): the compiler refuses to \
             publish a session artifact relative to ambient cwd"
        );
    }
    Ok(())
}

/// The canonical registry spelling of a `--trust-profile` value, or an error.
///
/// A profile label is the SOLE carrier of the hardened obligation set, so an
/// unregistered one is refused here rather than passed through. Accepting it
/// would enable hardened mode, print "hardened profile `<name>` enabled", copy
/// that claim into the proof record's `hardened.profile.name` — and generate
/// zero hardened obligations, because `-Ztrust-verify-profile` selects nothing
/// else. `--no-hardened` is how an invocation asks for no hardened
/// obligations; a misspelled profile is a mistake, not a request.
///
/// The returned value is the registry's spelling, so the flag cannot put the
/// user's casing, separators or surrounding whitespace into an evidence record
/// (or into a rustflags string that is split on whitespace).
fn canonical_trust_profile_value(value: &str) -> Result<&'static str> {
    if value.trim().is_empty() {
        bail!("--trust-profile requires a non-empty profile name");
    }
    if value.starts_with('-') {
        bail!("--trust-profile value `{value}` looks like another flag");
    }
    trust_vcgen::canonical_profile(value).ok_or_else(|| {
        anyhow::anyhow!(
            "unknown trust profile `{value}`: known profiles are {} \
             (`-` and `_` are the same separator, case-insensitive). \
             A profile selects the hardened obligation set, so an unregistered name would \
             announce hardening and generate none; use --no-hardened to turn hardened \
             obligations off deliberately.",
            trust_vcgen::known_hardened_profiles().join(", ")
        )
    })
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
        "  targo trust build <file.lean> --emit=trust-ir --out <new-path>  Write a checked local-source Lean IR-library JSON envelope (not an executable or raw .tir)",
        "  targo trust test               Verify and run tests with certified clause monitors",
        "  targo trust spec --emit clean [-p <pkg>]  Print the Clean goals the kernel actually graded (compiler-authoritative, v6/D1)",
        "  targo trust version            Emit Trust product/toolchain identity",
        "  targo trust release check      Run Trust release evidence gates",
        "  targo trust release validate <gate>  Run release validation gates",
        "  targo trust verify examples     Check verifier example Expected headers/output",
        "  targo trust verify cargo-cache  Materialize registry-only Cargo seed cache for release full-verify",
        "  targo trust gate check-all      Run repository compile and CLI metadata gates",
        "  targo trust gate coherence      Check recorded submodule SHAs type-check together",
        "  targo trust gate compare-audit  Compare saved elision/obligation audit populations natively",
        "  targo trust gate compare-seal   Decide a cut's consumer check from saved runs: PASS, SHARED_RED or NEW_RED",
        "  targo trust gate corpus-delta --old <trustc> --new <trustc>  Compile the daily-driver corpora with two compilers; print each case whose verdict moved against its pin",
        "  targo trust gate verify-examples  Alias for verify examples",
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
        "  targo trust diff --baseline <file> [-p <pkg>]...  Re-check and fail on any proof lost against a committed obligation baseline",
        "  targo trust delta [--since <token>] [--all-rows] <record.ndjson>...  Snapshot a check's obligation records and print the rows that changed since <token> or since this agent session's last run",
        "  targo trust stability [--axes <list>] [--against <dir>]  Re-run the check in legs under pairs of conditions; exit 1 names every obligation whose verdict moved, or a record's solver fault or unexplained stop",
        "  targo trust meter [--target-dir DIR] [--gate-runs DIR] [--hook-log FILE] [--json] [--check]  Where an agent's time went (proof, Lean, gate legs, push), largest wait first; --check names every phase not measured",
        "  targo trust init [file]        Scaffold inert, review-required contract candidates",
        "  targo trust temporal [path]    Inspect the proof-bearing temporal engine boundary; exits 2 pending authenticated build binding",
        "  targo trust temporal ingest <spec.tla> --config <spec.cfg> [--out <image.json>]  Emit a bounded zero-authority canonical Lean/Clean proposition image",
        "  targo trust solvers            Detect and report solver status",
        "  targo trust doctor             Show compiler/setup status and solver availability",
        "  targo trust store verify --facts  Re-check every local kernel fact (quarantines a mismatch)",
        "  targo trust help               Show this help",
        "",
        "Options:",
        "  --format <fmt>            Output format: terminal (default), json, html",
        "  --json                    Alias for --format json",
        "  --dump-verifier-inputs <new-dir>  Export actual MIR/native verifier inputs during normal Cargo check; preserves verdicts and failures",
        "  --standalone              Run a non-proof source audit (compiler verification is not performed)",
        "  --allow-l0-gaps           Broad development warning mode (-Z trust-policy=advisory): evidence-grade TCB boundaries such as in-process proc macros and certified-monitor seals are forfeited with a warning instead of refusing the build; conflicts with --memory-safe",
        "  --allow-memory-safe-panics  Narrow safe-code panic demotion; rejects unsafe UB and conflicts with --allow-l0-gaps (alias: --memory-safe)",
        "  --certify                 Release gate: full static discharge; every non-proved row is fatal, runtime-checked included",
    ]
    .iter()
    .copied()
    // The flag's own help lives beside the flag, in `test_target_panics`, so
    // the text and the behaviour cannot drift apart.
    .chain(crate::test_target_panics::help_lines())
    .chain(
        [
        "  --hardened                Explicitly enable default hardened boundary profile",
        "  --no-hardened             Disable the default hardened boundary profile for this run",
        "  --no-proc-macro-isolation Expand proc macros in the compiler, not its sandboxed worker; a verified unit with an unaudited proc-macro dependency is then refused",
        // Deliberately does NOT enumerate the registry: a second copy of the
        // profile list is how a front end ends up advertising a label the
        // verifier no longer knows. The refusal in
        // `canonical_trust_profile_value` prints the live registry instead.
        "  --trust-profile <name>    Select a registered hardened profile (default: unix_hardened)",
        "  --worker-threads <N>      Cap the verifier's worker threads (1 = serial engine batches; 0, the default, = no cap);",
        "                            recorded in the budget profile, not in its id",
        "  --rewrite                 Enable rewrite loop mode on check/build (`loop` always runs it)",
        "  --max-iterations <N>      Maximum loop iterations (default: 10)",
        "  --from <ref>              Git ref for the 'from' side of diff",
        "  --to <value>              Git ref for diff, or binary output target: trust_ir, rust, trust-cg, or wasm",
        "  --scope <path>            Scope git diff to a path prefix (e.g., crates/)",
        "  --baseline <path>         Committed obligation baseline (`trust-baseline v1`) for `diff`",
        "  --save-baseline <path>    `check`: write this run's proved obligation keys to a committed baseline",
        "  --since <token>           `check`: print the rows that changed since that snapshot token, and every row not plainly proved (crate or .lean)",
        "  --all-rows                `check`: print every row as well as the changes since the base",
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
        "  targo trust check --lib --save-baseline trust.baseline   Record the proved obligations",
        "  targo trust diff --baseline trust.baseline              Fail (exit 1) on any lost proof",
        "  targo trust stability --axes repetition,path --lib      Same inputs, same verdict vector? (stability --help)",
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
        "  Budgets are [trust] effort and backstop in the workspace root, and nothing else.",
        "  backstop is the one wall-clock backstop: above 1000 per mille it also scales each verified compiler",
        "  process's bounds (8h absolute at 1000 and below), and the retired compiler_timeout_secs is refused naming it.",
        "  A run selects its lane with --certify, --memory-safe or --allow-l0-gaps, its hardened profile with",
        "  --trust-profile or --no-hardened, and its worker threads with --worker-threads. A level below the",
        "  resolved one is `level` in the [trust] table. A tightening (a higher level,",
        "  -Ztrust-verify-include-dependencies=yes, -Ztrust-ir-lower=strict) is Cargo configuration: the",
        "  project's .cargo/config.toml, or --config for one run; project configuration never loosens a run.",
        "  TRUSTFLAGS and CARGO_ENCODED_TRUSTFLAGS are not read: a non-empty one is ignored with a notice.",
        "  -Ztrust-* inside RUSTFLAGS is ignored with a warning; use RUSTFLAGS for codegen flags.",
        "",
        "Behavior:",
        "  Invokes the discovered Trust toolchain: trustc, plus the sibling targo binary for crate-mode Cargo execution.",
        "  Source check/build/report/loop verify STRICT (fail-closed) for the crate under check by default; --allow-l0-gaps selects allow_l0_gaps (warnings).",
        "  Standalone Lean IR-library builds require every computational declaration to pass the independent UInt wrapping-binop/parameter-projection/literal-return source/SSA gate, including homogeneous wrapping expression trees of 2..=32 Add/Sub/Mul nodes; unused literal parameters may use distinct exact UInt8/16/32/64 carriers, and unsupported siblings refuse the whole artifact. Serialized bindings must be rechecked on import, not trusted as certificates. Native Lean codegen and mixed-language linking remain unavailable.",
        "  Lean build refusals list every refused declaration and typed category; add --verbose to the .lean build command for full underlying details (same admission and exit behavior).",
        "  Lean check/build --census NEW_PATH retains the independent pre-production kernel roster and source/import-discovery attempts, including failures; it is diagnostic only, not a complete runtime denominator or proof authority.",
        "  Add --census-olean-path DIR (repeatable, requires --census) to inventory external dependency artifacts; this does NOT enable external imports or kernel authority.",
        "  Frontend architecture: Rust/THIR and Lean/Clean lower directly to canonical typed TrustIr. Until source contracts and obligation ownership are bound to TrustIr SSA, crate check/report retain authenticated MIR-derived compatibility and differential evidence; MIR is not the canonical semantics or end-state frontend.",
        "  Removed release aliases (`targo trust verify full`, `preflight`, and `full-preflight`) reject Python/shell-era orchestration; use cargo-cache, repo-gate, verify self --full-verifier, and release check for default evidence.",
        "  `targo trust domination upstream-tests` dispatches the Trust-owned `trust-upstream-compat port` engine; Python is not used.",
        "  Compiler discovery priority: sibling trustc next to targo-trust, then repo-local stage2/stage3 Trust builds.",
        "  Check/build/report/loop enable the unix_hardened profile by default; pass --no-hardened only for compatibility triage.",
        "  unix_hardened also declares Unix-tool process semantics: `main` installs SIGPIPE -> SIG_DFL (a write to a closed pipe ends the",
        "  process quietly, like C tools), which discharges its stdout process_semantics mandate; RUSTFLAGS=-Zon-broken-pipe=error keeps Rust semantics.",
        "  Check/report require canonical trustc by default; --standalone is an explicit non-proof source audit and still uses hardened checks unless --no-hardened is passed.",
        "",
        "Exit codes:",
        "  0  Requested operation succeeded. For Rust, compiler succeeded, the run is a measurement and the result lane passed:",
        "     on the default lane every obligation is proved or",
        "     runtime-checked (keeps rustc's runtime check; completeness-gap ruling); under --certify, all proved;",
        "     under --allow-l0-gaps (the advisory ramp) an UNPROVED obligation is a stated CONDITION of the pass,",
        "     not a failure — the Result and Gate lines name every condition, and none of them is a proof claim",
        "     Lean check/IR-library success does not establish executable verification or release completeness",
        "  1  Verification failures, or inconclusive results after compiler success (unknown/assumed/mandated/",
        "     contract-panic rows; a runtime-checked row is inconclusive only under --certify). The advisory lane",
        "     (--allow-l0-gaps) reports an unproved obligation and exits 0; strict/certify/memory-safe keep it fatal",
        "  2  Internal/setup/report error (e.g., trustc not found, a malformed --baseline file)",
        "  3  COULD NOT RUN: the run is not a measurement and failed for that alone, so it is no verdict either",
        "     way. Its rows are could-not-run or not-reproducible (a solver refused admission, a row with no",
        "     stable key, a clock, a solver fault or an unexplained stop), the run's [trust] backstop ended",
        "     the compiler, or trustd could not be established (a missing or unusable sibling trustd is 2).",
        "     Any command exits 3 when SIGINT, SIGTERM or SIGHUP, or the end of the process that started it,",
        "     interrupts it (a signal ignored at start stays ignored; with SIGHUP ignored, so is that end):",
        "     its children are stopped first (SIGTERM; SIGKILL after 10s, or at once on a second signal),",
        "     and the COULD NOT RUN line names the cause. That is targo-trust's exit: through `targo trust`",
        "     a shell still reads 130 after Ctrl-C, or 143 after a SIGTERM to targo, until targo passes 3 on.",
        "     A lane that would pass, or fail on an unproved row, exits 3 instead; a refuted obligation still",
        "     exits 1, and failing tests, a compiler error the rows do not account for, or a hardened or",
        "     Cargo-exclusion gate failure exit as a measured run does.",
        "     --rewrite/loop: the loop converged on rows that are no measurement. `diff --baseline`/`check",
        "     --save-baseline`: nothing was lost, but the run is not a measurement. `stability`: nothing",
        "     differed and no record is not reproducible, but a leg could not run (its own exits are in",
        "     `targo trust stability --help`)",
        "  other nonzero  Underlying trustc/targo compiler exit code when compilation fails, or the Cargo",
        "     test run's when `targo trust test`'s tests fail",
        ]
        .iter()
        .copied(),
    )
    .collect::<Vec<_>>()
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
    fn verifier_input_export_option_is_typed_and_not_a_cargo_rustflag() {
        let parsed = parse_subcommand_args(&[
            "--dump-verifier-inputs".into(),
            "new directory:one".into(),
            "--locked".into(),
        ])
        .unwrap();
        assert_eq!(parsed.dump_verifier_inputs.as_deref(), Some("new directory:one"));
        assert_eq!(parsed.passthrough, vec!["--locked"]);
        for args in [
            vec!["--dump-verifier-inputs"],
            vec!["--dump-verifier-inputs="],
            vec!["--dump-verifier-inputs=a", "--dump-verifier-inputs=b"],
            vec!["--dump-verifier-inputs", "--certify"],
        ] {
            assert!(
                parse_subcommand_args(&args.iter().map(|s| s.to_string()).collect::<Vec<_>>())
                    .is_err(),
                "{args:?}"
            );
        }
    }

    #[test]
    fn usage_text_documents_lean_library_boundary() {
        let usage = usage_text();
        assert!(usage.contains("build <file.lean> --emit=trust-ir --out <new-path>"));
        assert!(usage.contains("not an executable or raw .tir"));
        assert!(usage.contains("unsupported siblings refuse the whole artifact"));
        assert!(usage.contains("wrapping-binop/parameter-projection/literal-return"));
        assert!(
            usage.contains("homogeneous wrapping expression trees of 2..=32 Add/Sub/Mul nodes")
        );
        assert!(
            usage.contains(
                "unused literal parameters may use distinct exact UInt8/16/32/64 carriers"
            )
        );
        assert!(usage.contains("Serialized bindings must be rechecked on import"));
        assert!(usage.contains("add --verbose to the .lean build command"));
        assert!(usage.contains("same admission and exit behavior"));
        assert!(
            usage.contains("Native Lean codegen and mixed-language linking remain unavailable")
        );
        assert!(
            usage.contains(
                "Lean check/IR-library success does not establish executable verification"
            )
        );
    }

    /// T7b: the one backstop that replaced `compiler_timeout_secs` is on the
    /// help page.
    #[test]
    fn usage_text_documents_the_one_backstop() {
        let usage = usage_text();
        assert!(usage.contains("backstop is the one wall-clock backstop"), "{usage}");
        assert!(usage.contains("compiler_timeout_secs is refused naming it"), "{usage}");
    }

    /// T7b: the exit a consumer reads COULD NOT RUN from is on the help page.
    #[test]
    fn usage_text_documents_the_could_not_run_exit() {
        let usage = usage_text();
        assert!(usage.contains("  3  COULD NOT RUN: the run is not a measurement"), "{usage}");
        assert!(usage.contains("a refuted obligation still"), "{usage}");
        assert!(usage.contains("exits 1, and failing tests, a compiler error the rows"), "{usage}");
        assert_eq!(crate::determinism_report::EXIT_COULD_NOT_RUN, 3);
    }

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

        // TRUST-08: the lock-driven deps verbs are retired; the top-level
        // usage must not advertise a command that can only refuse.
        assert!(!usage.contains("targo trust deps validate"));
        assert!(!usage.contains("targo trust deps status"));
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

    /// T7a: the usage names where each per-run selection lives and says
    /// TRUSTFLAGS is ignored; it no longer documents an override channel.
    #[test]
    fn usage_text_names_each_per_run_selection_and_no_trustflags_channel() {
        let usage = usage_text();

        assert!(usage.contains("TRUSTFLAGS and CARGO_ENCODED_TRUSTFLAGS are not read"));
        assert!(!usage.contains("TRUSTFLAGS is to trust verification"));
        assert!(!usage.contains("TRUSTFLAGS="));
        assert!(usage.contains("--worker-threads <N>"));
        assert!(usage.contains("its worker threads with --worker-threads"));
        assert!(usage.contains("`level` in the [trust] table"));
        assert!(usage.contains("or --config for one run"));
        assert!(usage.contains("[trust] effort and backstop"));
        assert!(usage.contains("use RUSTFLAGS for codegen flags"));
        assert!(usage.contains("-Ztrust-* inside RUSTFLAGS is ignored with a warning"));
    }

    #[test]
    fn proc_macro_isolation_is_on_unless_the_run_turns_it_off() {
        let parse = |args: &[&str]| {
            parse_subcommand_args(&args.iter().map(|arg| arg.to_string()).collect::<Vec<_>>())
                .expect("parse")
        };
        assert!(parse(&[]).proc_macro_isolation);
        assert!(parse(&["--certify"]).proc_macro_isolation);
        let off = parse(&["--certify", "--no-proc-macro-isolation"]);
        assert!(!off.proc_macro_isolation);
        // The flag is the wrapper's: it is not replayed to Cargo.
        assert!(
            !off.crate_mode_cargo_args().iter().any(|arg| arg.contains("proc-macro-isolation"))
        );
    }

    #[test]
    fn worker_threads_takes_the_compilers_domain() {
        let parse = |args: &[&str]| {
            parse_subcommand_args(&args.iter().map(|arg| arg.to_string()).collect::<Vec<_>>())
        };
        assert_eq!(parse(&[]).unwrap().worker_threads, 0);
        assert_eq!(parse(&["--worker-threads", "1"]).unwrap().worker_threads, 1);
        assert_eq!(parse(&["--worker-threads=256"]).unwrap().worker_threads, 256);
        assert_eq!(parse(&["--worker-threads=0"]).unwrap().worker_threads, 0);
        for bad in
            [&["--worker-threads"][..], &["--worker-threads=257"], &["--worker-threads", "x"]]
        {
            let error = parse(bad).expect_err("outside the compiler's domain").to_string();
            assert!(error.contains("from 0 through 256"), "{bad:?}: {error}");
        }
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
    fn cargo_jobs_hint_never_hides_a_single_file_operand() {
        let parse = |args: &[&str]| {
            parse_subcommand_args(&args.iter().map(|arg| arg.to_string()).collect::<Vec<_>>())
                .expect("jobs spellings parse")
        };
        // The expected passthrough is exact: a trustc option's integer value
        // (`--edition 2021`) stays, only Cargo's job count goes.
        for (args, expected) in [
            (&["add.rs", "--jobs=2"][..], &["add.rs"][..]),
            (&["add.rs", "--jobs", "2"], &["add.rs"]),
            (&["add.rs", "-j", "2"], &["add.rs"]),
            (&["add.rs", "-j2"], &["add.rs"]),
            (&["-j=2", "add.rs"], &["add.rs"]),
            (&["add.rs", "-j=default"], &["add.rs"]),
            (&["-j", "1", "add.rs"], &["add.rs"]),
            (&["--jobs=2", "add.rs"], &["add.rs"]),
            (&["-j1", "add.rs", "--edition", "2021"], &["add.rs", "--edition", "2021"]),
            (&["add.rs", "--edition", "2021", "-j", "4"], &["add.rs", "--edition", "2021"]),
        ] {
            let parsed = parse(args);
            assert!(parsed.is_single_file, "{args:?}");
            assert_eq!(parsed.single_file.as_deref(), Some("add.rs"), "{args:?}");
            assert_eq!(
                parsed.passthrough, expected,
                "single-file mode must not forward Cargo's job count to trustc: {args:?}"
            );
        }
    }

    #[test]
    fn cargo_jobs_hint_is_forwarded_unchanged_in_cargo_mode() {
        let args: Vec<String> = ["-p", "member", "--jobs=4", "-j", "3", "-j2", "-j=1"]
            .iter()
            .map(|a| a.to_string())
            .collect();
        let parsed = parse_subcommand_args(&args).expect("cargo-mode jobs parse");
        assert!(!parsed.is_single_file);
        assert_eq!(parsed.passthrough, args);
    }

    #[test]
    fn cargo_jobs_hint_width_counts_each_spelling() {
        let args = |list: &[&str]| list.iter().map(|a| a.to_string()).collect::<Vec<_>>();
        for (list, width) in [
            (&["-j", "4"][..], Some(2)),
            (&["--jobs", "default"], Some(2)),
            (&["-j", "x.lean"], Some(1)),
            (&["--jobs"], Some(1)),
            (&["--jobs=4"], Some(1)),
            (&["-j4"], Some(1)),
            (&["-j=4"], Some(1)),
            (&["-j=-1"], Some(1)),
            (&["--jobs=many"], None),
            (&["-j="], None),
            (&["-jx"], None),
            (&["x.lean"], None),
        ] {
            assert_eq!(cargo_jobs_hint_width(&args(list), 0), width, "{list:?}");
        }
        assert_eq!(cargo_jobs_hint_width(&args(&["-j"]), 1), None, "past the end");
    }

    #[test]
    fn a_rust_file_after_bare_jobs_is_not_taken_as_its_value() {
        let args: Vec<String> = ["-j", "add.rs"].iter().map(|a| a.to_string()).collect();
        let parsed = parse_subcommand_args(&args).expect("parse");
        assert!(parsed.is_single_file);
        assert_eq!(parsed.passthrough, ["add.rs"]);
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

    #[test]
    fn crate_mode_workspace_selection_ignores_opaque_child_flags() {
        for child_flag in ["--workspace", "--all"] {
            let parsed = parse_subcommand_args(&[
                "--all".to_string(),
                "--".to_string(),
                "--".to_string(),
                child_flag.to_string(),
            ])
            .expect("workspace selection with an opaque child flag parses");
            assert_eq!(
                parsed.crate_mode_cargo_args(),
                ["--workspace", "--", child_flag],
                "a child flag cannot replace Cargo's workspace selection"
            );
        }
    }
}
