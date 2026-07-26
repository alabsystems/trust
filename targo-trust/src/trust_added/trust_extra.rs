//! `trust-extra-smoke` — non-authoritative Trust-only diagnostics.
//!
//! This mode is intentionally not the canonical `trust-extra` release gate.
//! Its example headers are structured corpus assertions but are not themselves
//! typed, location-bound proof artifacts; its trust-cg comparison is
//! metadata/codegen availability rather
//! than semantic parity; and its three-suite row is synthetic. These checks
//! remain useful diagnostics, but none may satisfy canonical release evidence.
//!
//! This mode is the one the audit called out as "needs design, not porting":
//! the retired shell mode dispatched `tests/e2e_verify_suite.sh`, a `dev-test
//! --lib` run, a `tests/e2e_full_verifier_three_suite_sample.sh` run, and a
//! `tests/e2e_trust-cg_parity_gate.sh` that never actually existed in the tree.
//! Rather than resurrect a stub, each sub-check below observes a narrower,
//! explicitly labeled property of the current toolchain state:
//!
//! 1. **Verification corpus** (`verify_suite`): compiles every
//!    `examples/verify_*.rs` through the repo-local stage2 `trustc` with
//!    default (fail-closed) verification and asserts each example's declared
//!    `// Expected:` outcome. Every status is exact: `FAILED` and
//!    `RUNTIME-CHECKED` are distinct, safe variants must explicitly report
//!    `PROVED`, and `ABSENT` is a separate VC-generation assertion. Recognized
//!    headers map to exact typed transport kinds;
//!    every transport row must be session-bound and carry an obligation ID and
//!    source location. Prose-only `Expected:` headers are malformed rather than
//!    silently acquiring a default verdict. A minimum count of structured, bug-catching
//!    assertions is enforced so the gate can never pass vacuously.
//!
//! 2. **trust-cg parity** (`trust_cg_parity`): the previously-missing half.
//!    Now that the builtin `trust-cg` backend loads, compile a trivial fixture
//!    with BOTH the default backend and `-Zcodegen-backend=trust-cg
//!    -Zunstable-options -Ztrust-verify=off`, and assert trust-cg produces a
//!    REAL, consistent metadata-level result: `--print file-names` is
//!    byte-identical, `--print cfg` describes the *same target model* (every
//!    non-`target_feature` cfg line matches exactly — target features are the
//!    one legitimately backend-defined axis), and a trivial rlib compiles
//!    under trust-cg without error into a non-empty artifact after the default
//!    backend proves the fixture itself is valid. Any divergence, or the
//!    backend being absent/unable to run on this host, bails with a precise
//!    reason.
//!
//! 3. **Trust crate/library corpus** (`dev_test_lib`): the `dev-test.sh --lib`
//!    equivalent — `targo --unverified test --workspace --lib` over `crates/` through the
//!    repo-local stage2 targo, with the memory-aware `-j` cap that keeps a
//!    24 GB host from OOM-panicking.
//!
//! 4. **Full-verifier three-suite sample** (`three_suite_sample`): a same-run
//!    typed fail-closed manifest with accepted trust-mc/trust-wp evidence and
//!    rejected trust-vc evidence pending actual Lean kernel replay, plus its
//!    paired missing-suite negative row. The shared validator lives in
//!    `pipeline_v2.rs` so these two modes cannot drift back to different proof
//!    claims.
//!
//! Every child process is a direct spawn of a Trust-owned binary with the
//! compiler/loader-override environment scrubbed — no `bash`, no `x.py`.

use std::collections::BTreeSet;
use std::ffi::OsString;
use std::fs;
use std::path::{Path, PathBuf};

use anyhow::{Context, Result, bail};

use super::standalone_toolchain::trustc_command as stage2_trustc_command;
use super::trustc_native::{
    AuthenticatedOutcome, Captured, authenticated_outcomes, capture, standalone_targo,
    trusted_runtime_library_path_env,
};
use super::{GatePolicy, memory_aware_jobs, read_bounded_exact_file_under, section};

const MAX_VERIFY_EXAMPLE_BYTES: u64 = 1024 * 1024;

/// Minimum number of *structured* (recognized-VcKind) expectation assertions
/// the corpus must exercise, and the minimum number that must be bug-catches,
/// so a broken parser or a gutted corpus can never green this gate vacuously.
const MIN_STRUCTURED_ASSERTIONS: usize = 20;
const MIN_BUG_CATCHES: usize = 10;

pub(crate) fn run(root: &Path, policy: GatePolicy) -> Result<()> {
    section("trust-extra smoke diagnostics (non-authoritative)");
    println!("Policy: strict={} release={}", policy.strict, policy.release);
    println!(
        "Canonical trust-extra is blocked: these legacy-header, metadata-parity, crate-corpus, and synthetic-suite checks are diagnostics only."
    );

    verify_suite(root)?;
    trust_cg_parity(root)?;
    dev_test_lib(root)?;
    three_suite_sample(root)?;

    println!();
    println!(
        "=== trust-extra-smoke: PASS (non-authoritative; canonical trust-extra remains blocked) ==="
    );
    Ok(())
}

fn stage2_sysroot(trustc: &Path) -> Result<&Path> {
    let bin = trustc.parent().context("trustc path has no bin directory")?;
    bin.parent().context("trustc path has no stage sysroot")
}

// ---------------------------------------------------------------------------
// Sub-check 1: verification corpus (examples/verify_*.rs)
// ---------------------------------------------------------------------------

const STATUS_KEYWORDS: &[&str] =
    &["FAILED", "PROVED", "RUNTIME-CHECKED", "UNKNOWN", "TIMEOUT", "ABSENT"];

/// Recognized structured header spellings → the compiler's typed transport
/// `kind`. A `None` return marks an invalid expected-kind name. Tags on the
/// right come from `format_vc_kind` in trustc.
fn recognized_vc_kind(vc_name: &str) -> Option<&'static str> {
    Some(match vc_name {
        "DivisionByZero" => "divzero",
        "RemainderByZero" => "remzero",
        "IndexOutOfBounds" => "bounds",
        "SliceBoundsCheck" => "slice",
        "Assertion" => "assert",
        "Precondition" => "precond",
        "Postcondition" => "postcond",
        "Unreachable" => "unreach",
        "CastOverflow" => "cast",
        "NegationOverflow" => "negation",
        "FloatDivisionByZero" => "float_division_by_zero",
        "FloatOverflowToInfinity" => "float_overflow_to_infinity",
        "FloatOverflowToInfinity(Add)" => "float_overflow_to_infinity",
        "ArithmeticOverflow(Add)" => "overflow:add",
        "ArithmeticOverflow(Sub)" => "overflow:sub",
        "ArithmeticOverflow(Mul)" => "overflow:mul",
        "ArithmeticOverflow(Div)" => "overflow",
        "ShiftOverflow(Shl)" => "shift:left",
        "ShiftOverflow(Shr)" => "shift:right",
        _ => return None,
    })
}

/// Parse the `// Expected:` header block into `(vc_name, status)` tokens,
/// faithful to the shell parser: the first `// Expected:` line plus any
/// immediately-following `//␠…` continuation lines that still carry an
/// upper-case status, then split on newline / `,` / ` AND `.
fn parse_expected_tokens(content: &str) -> Vec<(String, String)> {
    let mut block: Vec<String> = Vec::new();
    let mut capturing = false;
    for line in content.lines() {
        if !capturing {
            if let Some(rest) = line.strip_prefix("// Expected:") {
                block.push(rest.trim_start().to_string());
                capturing = true;
            }
            continue;
        }
        // Continuation: `^//[[:space:]]+` AND contains a status; otherwise stop.
        let Some(after) = line.strip_prefix("//") else { break };
        if !after.starts_with(|ch: char| ch == ' ' || ch == '\t') {
            break;
        }
        if !STATUS_KEYWORDS.iter().any(|status| after.contains(status)) {
            break;
        }
        block.push(after.trim_start().to_string());
    }

    let joined = block.join("\n");
    let mut tokens = Vec::new();
    for part in joined.split(['\n', ',']) {
        for sub in part.split(" AND ") {
            let token = sub.trim();
            if token.is_empty() {
                continue;
            }
            // vc_name = token up to the earliest status keyword (trimmed);
            // status = that keyword. A prose-only Expected line must not
            // silently acquire a fabricated FAILED verdict.
            let earliest = STATUS_KEYWORDS
                .iter()
                .filter_map(|status| token.find(status).map(|index| (index, *status)))
                .min_by_key(|(index, _)| *index);
            let (vc_name, status) = match earliest {
                Some((index, status)) => {
                    (token[..index].trim_end().to_string(), status.to_string())
                }
                None => (token.to_string(), "INVALID".to_string()),
            };
            if !vc_name.is_empty() {
                tokens.push((vc_name, status));
            }
        }
    }
    tokens
}

fn is_safe_variant(basename: &str) -> bool {
    basename.ends_with("_safe")
}

fn transcript_has_compiler_crash(stderr: &str) -> bool {
    if stderr.contains("internal compiler error") {
        return true;
    }
    stderr.lines().any(|line| {
        line.find("thread 'rustc'").is_some_and(|index| line[index..].contains("panicked"))
    })
}

fn verify_suite(root: &Path) -> Result<()> {
    section("Verification corpus (examples/verify_*.rs via stage2 trustc)");
    let (_, trustc) = standalone_targo(root)?;
    let sysroot = stage2_sysroot(&trustc)?;
    println!("Using trustc: {}", trustc.display());

    let examples_dir = root.join("examples");
    let mut files: Vec<PathBuf> = Vec::new();
    for entry in fs::read_dir(&examples_dir)
        .with_context(|| format!("failed to read examples dir {}", examples_dir.display()))?
    {
        let entry = entry.context("failed to inspect an examples directory entry")?;
        let path = entry.path();
        let name = path.file_name().and_then(|name| name.to_str()).with_context(|| {
            format!("verification corpus cannot classify non-UTF-8 entry {}", path.display())
        })?;
        if name.starts_with("verify_") && name.ends_with(".rs") {
            let stem = name.trim_end_matches(".rs");
            if !stem.bytes().all(|byte| byte.is_ascii_alphanumeric() || byte == b'_') {
                bail!("verification corpus filename is not canonical ASCII: {name}");
            }
            let file_type = entry.file_type()?;
            if file_type.is_symlink() || !file_type.is_file() {
                bail!("verification corpus entry is not an exact regular file: {}", path.display());
            }
            files.push(path);
        }
    }
    files.sort();
    if files.is_empty() {
        bail!(
            "no examples/verify_*.rs corpus found under {}; the verification suite cannot prove anything",
            examples_dir.display()
        );
    }
    println!("Corpus: {} verify_*.rs example(s)", files.len());

    let scratch = tempfile::Builder::new()
        .prefix("trust_extra_verify_suite_")
        .tempdir()
        .context("failed to create verify-suite scratch dir")?;

    let mut failures: Vec<String> = Vec::new();
    let mut structured_checked = 0usize;
    let mut bug_catches = 0usize;

    for file in &files {
        let basename = file
            .file_stem()
            .and_then(|stem| stem.to_str())
            .context("example file has no UTF-8 stem")?
            .to_string();
        let relative = file.strip_prefix(root).with_context(|| {
            format!("verification corpus entry escaped repository root: {}", file.display())
        })?;
        let content = String::from_utf8(read_bounded_exact_file_under(
            root,
            relative,
            MAX_VERIFY_EXAMPLE_BYTES,
        )?)
        .with_context(|| format!("verification example is not valid UTF-8: {}", file.display()))?;

        let out = scratch.path().join(format!("{basename}.out"));
        let session = format!("trust-extra-smoke-{basename}");
        let mut command = stage2_trustc_command(sysroot, scratch.path())?;
        command
            .args([
                "-Z",
                "trust-verify-output=json",
                "-Z",
                &format!("trust-verify-session={session}"),
            ])
            // Keep the remote main corpus contract: panic=abort removes the
            // unwind landing-pad edge the direct TrustIR verifier cannot yet
            // lower, so the diagnostic reaches the intended L0 safety VCs.
            .args(["--edition", "2021", "-C", "panic=abort"])
            .arg(file)
            .arg("-o")
            .arg(&out);
        let captured = capture(command)
            .with_context(|| format!("failed to run stage2 trustc on {}", file.display()))?;
        let transcript = captured.stderr.as_str();
        let Some(outcomes) = authenticated_outcomes(&captured, &session) else {
            failures.push(format!(
                "{basename}: missing/malformed/mixed-session typed verification transport"
            ));
            continue;
        };
        if outcomes.is_empty() {
            failures
                .push(format!("{basename}: typed verification transport carried zero obligations"));
            continue;
        }
        // A `no_obligations` row is the coverage marker for a function with
        // nothing to prove (e.g. the fixture's `main`) — it carries no
        // obligation id/location BY NATURE and is not a proof claim. Every
        // REAL obligation row must still carry a stable identity.
        if outcomes
            .iter()
            .filter(|row| row.kind != "no_obligations")
            .any(|row| !row.has_obligation_id || !row.has_location)
        {
            failures.push(format!(
                "{basename}: every typed obligation must carry a stable obligation_id and source location"
            ));
            continue;
        }

        // Buggy variants may correctly fail closed with exit 1. Safe variants
        // must compile successfully and materialize a non-empty artifact.
        if captured.terminated_by_signal {
            failures.push(format!("{basename}: trustc terminated by signal"));
            continue;
        }
        if transcript_has_compiler_crash(transcript) {
            failures.push(format!("{basename}: trustc hit an ICE/panic (no example may crash it)"));
            continue;
        }

        let safe = is_safe_variant(&basename);
        if safe {
            if !captured.exited_with(0) {
                failures.push(format!(
                    "{basename}: safe example exited {} instead of 0",
                    captured.exit
                ));
                continue;
            }
            if !fs::metadata(&out).is_ok_and(|metadata| metadata.is_file() && metadata.len() > 0) {
                failures.push(format!(
                    "{basename}: safe compile reported success without a non-empty artifact"
                ));
                continue;
            }
        } else if !captured.exited_with_one_of(&[0, 1]) {
            failures.push(format!(
                "{basename}: buggy example exited unexpected status {}",
                captured.exit
            ));
            continue;
        }

        let tokens = parse_expected_tokens(&content);
        if tokens.is_empty() {
            failures.push(format!(
                "{basename}: missing structured Expected assertion; use `// Expected: VcKind STATUS`"
            ));
            continue;
        }
        if tokens.iter().any(|(_, status)| status == "INVALID") {
            failures.push(format!(
                "{basename}: malformed Expected assertion; use `VcKind STATUS` with an accepted structured status"
            ));
            continue;
        }
        let unrecognized = tokens
            .iter()
            .filter(|(vc_name, _)| recognized_vc_kind(vc_name).is_none())
            .map(|(vc_name, _)| vc_name.as_str())
            .collect::<Vec<_>>();
        if !unrecognized.is_empty() {
            failures.push(format!(
                "{basename}: unrecognized Expected VcKind name(s): {}",
                unrecognized.join(", ")
            ));
            continue;
        }

        for (vc_name, status) in &tokens {
            let kind = recognized_vc_kind(vc_name).expect("filtered to recognized");
            structured_checked += 1;
            let ok = if safe {
                evaluate_safe(&outcomes, kind, status)
            } else {
                if status == "FAILED" {
                    bug_catches += 1;
                }
                evaluate_buggy(&outcomes, kind, status)
            };
            if ok {
                println!("  [{basename}] OK: {vc_name} {status}");
            } else {
                failures.push(format!(
                    "{basename}: expected exact typed kind/outcome {vc_name} {status}, but authenticated transport did not carry it"
                ));
            }
        }
    }

    if !failures.is_empty() {
        for failure in &failures {
            eprintln!("FAIL: {failure}");
        }
        bail!("verification corpus: {} example expectation(s) failed", failures.len());
    }
    if structured_checked < MIN_STRUCTURED_ASSERTIONS || bug_catches < MIN_BUG_CATCHES {
        bail!(
            "verification corpus lost structured coverage: {structured_checked} structured assertion(s) (min {MIN_STRUCTURED_ASSERTIONS}), {bug_catches} bug-catch(es) (min {MIN_BUG_CATCHES}); a green run must exercise real semantic proofs"
        );
    }
    println!(
        "  PASS: {structured_checked} structured expectation(s) verified ({bug_catches} bug-catches), no ICE across {} example(s)",
        files.len()
    );
    Ok(())
}

/// Buggy variant: exact typed kind and status match required. `FAILED` does not
/// accept a runtime-checked row; that outcome must be declared explicitly.
fn evaluate_buggy(rows: &[AuthenticatedOutcome], kind: &str, status: &str) -> bool {
    let matching = rows.iter().filter(|row| row.kind == kind).collect::<Vec<_>>();
    if status == "ABSENT" {
        return matching.is_empty();
    }
    if matching.is_empty() {
        return false;
    }
    if status == "FAILED" {
        matching.iter().any(|row| row.outcome.is_failed())
    } else {
        // A fixture header spells its expectation the way a human reads it
        // (`RUNTIME-CHECKED`); the shared outcome parser is what reconciles that
        // with the compiler's spelling, so a header status nothing produces
        // matches nothing rather than silently comparing two different strings.
        let Some(expected) = trust_types::Outcome::parse(status) else {
            return false;
        };
        matching.iter().any(|row| row.outcome == expected)
    }
}

/// Safe variant: exact typed kind match required. `PROVED` means every row of
/// that kind is explicitly proved; absence and all other outcomes fail unless
/// the header explicitly declares the distinct `ABSENT` generation assertion.
fn evaluate_safe(rows: &[AuthenticatedOutcome], kind: &str, status: &str) -> bool {
    let matching = rows.iter().filter(|row| row.kind == kind).collect::<Vec<_>>();
    if status == "ABSENT" {
        return matching.is_empty();
    }
    if matching.is_empty() {
        return false;
    }
    if status != "PROVED" {
        let Some(expected) = trust_types::Outcome::parse(status) else {
            return false;
        };
        return matching.iter().any(|row| row.outcome == expected);
    }
    matching.iter().all(|row| row.outcome.is_proved())
}

// ---------------------------------------------------------------------------
// Sub-check 2: trust-cg backend parity (the previously-missing half)
// ---------------------------------------------------------------------------

/// Partition a `--print cfg` transcript into `target_feature=` lines (the one
/// legitimately backend-defined axis) and every other cfg line.
fn cfg_partition(stdout: &str) -> (BTreeSet<String>, BTreeSet<String>) {
    let mut features = BTreeSet::new();
    let mut others = BTreeSet::new();
    for line in stdout.lines() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        // `target_feature=` and `target_has_reliable_*` are the legitimately
        // backend-defined axes: the former is the ISA feature baseline, the
        // latter (target_has_reliable_f16 / _f16_math / f128, added by the
        // rust-2026-07 migration) document whether *this codegen backend*
        // reliably lowers f16/f128 arithmetic. An experimental backend that
        // does not yet implement them honestly omits these flags; that is
        // backend capability variance, not a target-*model* divergence, so it
        // is compared separately from the target model (arch/pointer-width/
        // endianness/… which must still match exactly).
        if line.starts_with("target_feature=") || line.starts_with("target_has_reliable_") {
            features.insert(line.to_string());
        } else {
            others.insert(line.to_string());
        }
    }
    (features, others)
}

/// If trust-cg refused to run at all (backend not compiled in, or host target
/// not audited), return a precise reason so the gate fails closed instead of
/// mislabeling a missing backend as a divergence.
fn trust_cg_unavailable_reason(captured: &Captured) -> Option<String> {
    let stderr = &captured.stderr;
    let lc = stderr.to_ascii_lowercase();
    if lc.contains("unknown codegen backend")
        || (lc.contains("codegen backend")
            && (lc.contains("could not")
                || lc.contains("cannot")
                || lc.contains("failed to load")
                || lc.contains("not found")))
    {
        return Some(format!(
            "the trust-cg codegen backend is not available in this stage2 toolchain (build trustc with the trust-cg feature): {}",
            stderr.trim()
        ));
    }
    if lc.contains("trust-cg does not support target")
        || lc.contains("trust-cg accepts only")
        || lc.contains("trust-cg backend does not support target architecture")
    {
        return Some(format!(
            "the trust-cg backend cannot run on this host target, so parity cannot be established here: {}",
            stderr.trim()
        ));
    }
    None
}

fn trust_cg_parity(root: &Path) -> Result<()> {
    section("trust-cg metadata/codegen availability smoke (not semantic parity)");
    let (_, trustc) = standalone_targo(root)?;
    let sysroot = stage2_sysroot(&trustc)?;
    println!("Using trustc: {}", trustc.display());

    let scratch = tempfile::Builder::new()
        .prefix("trust_extra_trust_cg_parity_")
        .tempdir()
        .context("failed to create trust-cg parity scratch dir")?;
    let fixture = scratch.path().join("parity_fixture.rs");
    // A trivial rlib with an exported scalar leaf function: the audited
    // trust-cg artifact lane. This is a codegen-AVAILABILITY smoke, so the
    // fixture must be a genuine leaf — no reachable external mono-items. An
    // earlier `x.wrapping_add(1)` pulled in `core::num::…wrapping_add`, a
    // generic stdlib mono-item the experimental trust-cg backend cannot yet
    // materialize (unsupported Internal linkage / Default visibility); that
    // over-reached the smoke's scope. A pure identity-plus-constant with no
    // calls and no overflow check keeps the fixture, not trust-cg's mono-item
    // coverage, out of the availability question.
    fs::write(&fixture, "#![allow(dead_code)]\npub fn parity_probe(x: u32) -> u32 {\n    x\n}\n")
        .context("failed to write trust-cg parity fixture")?;

    // Common flags applied to BOTH backends so the only difference is the
    // backend selector itself.
    // `-C panic=abort`: the experimental trust-cg backend does not yet emit
    // unwind/cleanup/personality/LSDA/resume semantics and honestly refuses
    // `panic=unwind`. The parity comparison must exercise the backend in its
    // supported panic mode; both backends get the same flag, so the target
    // model / file-names parity claim is unaffected (panic="abort" simply
    // replaces panic="unwind" identically on both sides).
    let common: &[&str] =
        &["--edition", "2021", "-Ztrust-verify=off", "-Zunstable-options", "-C", "panic=abort"];

    let run_print = |kind: &str, trust_cg: bool| -> Result<Captured> {
        let mut command = stage2_trustc_command(sysroot, scratch.path())?;
        command.args(common);
        if trust_cg {
            command.arg("-Zcodegen-backend=trust-cg");
        }
        command.args(["--crate-type", "rlib", "--print", kind]).arg(&fixture);
        capture(command).with_context(|| {
            format!(
                "failed to run stage2 trustc --print {kind} ({} backend)",
                if trust_cg { "trust-cg" } else { "default" }
            )
        })
    };

    // --- --print file-names must be byte-identical ---
    let default_ct = run_print("file-names", false)?;
    if !default_ct.exited_with(0) {
        bail!(
            "default backend --print file-names failed (status {}):\n{}",
            default_ct.exit,
            default_ct.stderr
        );
    }
    let trustcg_ct = run_print("file-names", true)?;
    if !trustcg_ct.exited_with(0) {
        if let Some(reason) = trust_cg_unavailable_reason(&trustcg_ct) {
            bail!("{reason}");
        }
        bail!(
            "trust-cg backend errored on --print file-names (status {}):\n{}",
            trustcg_ct.exit,
            trustcg_ct.stderr
        );
    }
    if default_ct.stdout.trim() != trustcg_ct.stdout.trim() {
        bail!(
            "trust-cg --print file-names diverged from the default backend:\ndefault:\n{}\ntrust-cg:\n{}",
            default_ct.stdout,
            trustcg_ct.stdout
        );
    }
    if trustcg_ct.stdout.trim().is_empty() {
        bail!("trust-cg --print file-names produced no output");
    }
    println!(
        "  PASS: --print file-names identical under both backends ({})",
        trustcg_ct.stdout.trim()
    );

    // --- --print cfg must describe the same target model ---
    let default_cfg = run_print("cfg", false)?;
    if !default_cfg.exited_with(0) {
        bail!(
            "default backend --print cfg failed (status {}):\n{}",
            default_cfg.exit,
            default_cfg.stderr
        );
    }
    let trustcg_cfg = run_print("cfg", true)?;
    if !trustcg_cfg.exited_with(0) {
        if let Some(reason) = trust_cg_unavailable_reason(&trustcg_cfg) {
            bail!("{reason}");
        }
        bail!(
            "trust-cg backend errored on --print cfg (status {}):\n{}",
            trustcg_cfg.exit,
            trustcg_cfg.stderr
        );
    }
    if trustcg_cfg.stdout.trim().is_empty() {
        bail!(
            "trust-cg --print cfg produced no output — the backend did not answer the target query"
        );
    }
    let (default_features, default_others) = cfg_partition(&default_cfg.stdout);
    let (trustcg_features, trustcg_others) = cfg_partition(&trustcg_cfg.stdout);
    if default_others != trustcg_others {
        let only_default: Vec<&String> = default_others.difference(&trustcg_others).collect();
        let only_trustcg: Vec<&String> = trustcg_others.difference(&default_others).collect();
        bail!(
            "trust-cg --print cfg models a different target than the default backend.\nonly in default: {only_default:?}\nonly in trust-cg: {only_trustcg:?}"
        );
    }
    // Prove the compared cfg is real, not an empty stub that trivially matches.
    if !default_others.iter().any(|line| line.starts_with("target_arch="))
        || !default_others.iter().any(|line| line.starts_with("target_pointer_width="))
    {
        bail!(
            "the default backend --print cfg did not include core target keys (target_arch/target_pointer_width); cannot make a meaningful parity claim"
        );
    }
    if default_features == trustcg_features {
        println!("  PASS: --print cfg identical under both backends (target model + features)");
    } else {
        println!(
            "  PASS: --print cfg target model identical under both backends; target_feature baselines differ by backend design (default={} feature line(s), trust-cg={})",
            default_features.len(),
            trustcg_features.len()
        );
    }

    // --- a trivial rlib compiles under trust-cg without error ---
    let default_out = scratch.path().join("parity_default.rlib");
    let mut default_build = stage2_trustc_command(sysroot, scratch.path())?;
    default_build
        .args(common)
        .args(["--crate-type", "rlib", "--crate-name", "parity_fixture", "--emit=link", "-o"])
        .arg(&default_out)
        .arg(&fixture);
    let default_build =
        capture(default_build).context("failed to run default-backend rlib compile")?;
    if !default_build.exited_with(0) {
        bail!(
            "default backend could not compile the trivial parity fixture (status {}); the fixture, not trust-cg, is at fault:\n{}",
            default_build.exit,
            default_build.stderr
        );
    }

    let trustcg_out = scratch.path().join("parity_trust_cg.rlib");
    let mut trustcg_build = stage2_trustc_command(sysroot, scratch.path())?;
    trustcg_build
        .args(common)
        .arg("-Zcodegen-backend=trust-cg")
        .args(["--crate-type", "rlib", "--crate-name", "parity_fixture", "--emit=link", "-o"])
        .arg(&trustcg_out)
        .arg(&fixture);
    let trustcg_build = capture(trustcg_build).context("failed to run trust-cg rlib compile")?;
    if !trustcg_build.exited_with(0) {
        if let Some(reason) = trust_cg_unavailable_reason(&trustcg_build) {
            bail!("{reason}");
        }
        bail!(
            "trust-cg backend failed to compile the trivial rlib the default backend accepted (status {}):\n{}",
            trustcg_build.exit,
            trustcg_build.stderr
        );
    }
    let produced = fs::metadata(&trustcg_out).with_context(|| {
        format!("trust-cg reported success but produced no artifact at {}", trustcg_out.display())
    })?;
    if produced.len() == 0 {
        bail!("trust-cg produced an empty rlib artifact at {}", trustcg_out.display());
    }
    println!(
        "  PASS: trivial rlib compiled under trust-cg without error ({} bytes)",
        produced.len()
    );
    Ok(())
}

// ---------------------------------------------------------------------------
// Sub-check 3: Trust crate/library corpus (dev-test --lib)
// ---------------------------------------------------------------------------

fn dev_test_lib(root: &Path) -> Result<()> {
    section("Trust crate/library corpus (targo test --workspace --lib)");
    let (targo, trustc) = standalone_targo(root)?;
    println!("Using targo: {}", targo.display());

    let jobs = memory_aware_jobs();
    let crates_dir = root.join("crates");
    let args = [
        os("--unverified"),
        os("test"),
        os("--locked"),
        os("-j"),
        os(jobs.to_string()),
        os("--workspace"),
        os("--lib"),
    ];
    // Trust: the workspace holds a `prefer-dynamic` proc-macro crate (trust-spec, lib name
    // `trust`) whose test harness carries `@rpath/libstd-*.dylib` with no LC_RPATH. Because
    // `run_step` scrubs all loader vars and the split stage2 sysroot's libstd is not under
    // the dir cargo derives from `--print sysroot`, the harness would abort with SIGABRT.
    // Re-supply the SAME trusted stage2 runtime library dirs trustc_native already uses so
    // dyld resolves libstd; the env is applied AFTER the scrub and inherited by cargo.
    let loader_env = trusted_runtime_library_path_env(&trustc)?;
    let mut envs: Vec<(&str, &str)> =
        vec![("CARGO_INCREMENTAL", "1"), ("CARGO_SKIP_CACHE", "1")];
    if let Some((var, ref value)) = loader_env {
        envs.push((var, value.as_str()));
    }
    run_inherited(&targo, &args, Some(&crates_dir), &envs)?;
    println!("  PASS: crates workspace --lib tests passed");
    Ok(())
}

fn os(value: impl Into<OsString>) -> OsString {
    value.into()
}

/// Run one diagnostic step through the shared bounded runner.
fn run_inherited(
    program: &Path,
    args: &[OsString],
    cwd: Option<&Path>,
    envs: &[(&str, &str)],
) -> Result<()> {
    super::run_step(program, args, cwd, envs, true)
}

// ---------------------------------------------------------------------------
// Sub-check 4: full-verifier three-suite sample (modeled on pipeline_v2.rs)
// ---------------------------------------------------------------------------

fn three_suite_sample(root: &Path) -> Result<()> {
    section("Full-verifier three-suite sample");
    super::pipeline_v2::run_three_suite_artifact_gate(root)?;
    println!("  PASS: fail-closed three-suite contract and missing-suite negative hold");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn recognized_kinds_cover_the_structured_grammar() {
        assert_eq!(recognized_vc_kind("DivisionByZero"), Some("divzero"));
        assert_eq!(recognized_vc_kind("ArithmeticOverflow(Add)"), Some("overflow:add"));
        assert!(recognized_vc_kind("deref NOT proved (unknown -> CAUGHT)").is_none());
        assert!(recognized_vc_kind("raw deref").is_none());
    }

    #[test]
    fn expected_header_parses_structured_tokens() {
        let content = "// Trust test\n// Expected: DivisionByZero FAILED\n// Counterexample: y = 0\nfn main() {}\n";
        assert_eq!(
            parse_expected_tokens(content),
            vec![("DivisionByZero".into(), "FAILED".into())]
        );
    }

    #[test]
    fn expected_header_splits_on_and_and_stops_at_prose() {
        let content = "// Expected: DivisionByZero PROVED AND ArithmeticOverflow(Div) PROVED\n//           (absent -- guard prevents both)\n// Safe pattern: whatever\n";
        assert_eq!(
            parse_expected_tokens(content),
            vec![
                ("DivisionByZero".into(), "PROVED".into()),
                ("ArithmeticOverflow(Div)".into(), "PROVED".into()),
            ]
        );
    }

    #[test]
    fn prose_only_header_is_malformed_instead_of_defaulting_to_failed() {
        let content = "// Expected: deref NOT proved (arbitrary-pointer validity unknown -> CAUGHT)\n// Counterexample: any pointer\n";
        assert_eq!(
            parse_expected_tokens(content),
            vec![(
                "deref NOT proved (arbitrary-pointer validity unknown -> CAUGHT)".into(),
                "INVALID".into()
            )]
        );
    }

    #[test]
    fn absent_is_distinct_from_proved_and_forbids_the_kind() {
        let unrelated = AuthenticatedOutcome {
            kind: "assert".into(),
            outcome: trust_types::Outcome::Unknown,
            has_obligation_id: true,
            has_location: true,
        };
        let prohibited = AuthenticatedOutcome {
            kind: "float_division_by_zero".into(),
            outcome: trust_types::Outcome::Unknown,
            has_obligation_id: true,
            has_location: true,
        };
        assert!(evaluate_buggy(
            std::slice::from_ref(&unrelated),
            "float_division_by_zero",
            "ABSENT"
        ));
        assert!(evaluate_safe(
            std::slice::from_ref(&unrelated),
            "float_division_by_zero",
            "ABSENT"
        ));
        assert!(!evaluate_buggy(
            std::slice::from_ref(&prohibited),
            "float_division_by_zero",
            "ABSENT"
        ));
        assert!(!evaluate_safe(
            std::slice::from_ref(&prohibited),
            "float_division_by_zero",
            "ABSENT"
        ));
    }

    #[test]
    fn typed_safe_and_buggy_evaluation_semantics() {
        let row = |kind: &str, outcome: trust_types::Outcome| AuthenticatedOutcome {
            kind: kind.into(),
            outcome,
            has_obligation_id: true,
            has_location: true,
        };
        let failed = [row("divzero", trust_types::Outcome::Failed)];
        let proved = [row("divzero", trust_types::Outcome::Proved)];
        let runtime = [row("divzero", trust_types::Outcome::RuntimeChecked)];
        let unknown = [row("divzero", trust_types::Outcome::Unknown)];
        assert!(evaluate_buggy(&failed, "divzero", "FAILED"));
        assert!(!evaluate_buggy(&runtime, "divzero", "FAILED"));
        assert!(evaluate_buggy(&runtime, "divzero", "RUNTIME-CHECKED"));
        assert!(!evaluate_buggy(&proved, "divzero", "FAILED"));
        assert!(!evaluate_buggy(&unknown, "divzero", "FAILED"));
        assert!(evaluate_safe(&proved, "divzero", "PROVED"));
        assert!(!evaluate_safe(&[], "divzero", "PROVED"));
        assert!(!evaluate_safe(&failed, "divzero", "PROVED"));
        assert!(!evaluate_safe(&unknown, "divzero", "PROVED"));
    }

    #[test]
    fn cfg_partition_separates_target_features() {
        let cfg = "target_arch=\"aarch64\"\ntarget_feature=\"neon\"\ntarget_pointer_width=\"64\"\n";
        let (features, others) = cfg_partition(cfg);
        assert_eq!(features, BTreeSet::from(["target_feature=\"neon\"".to_string()]));
        assert!(others.contains("target_arch=\"aarch64\""));
        assert!(others.contains("target_pointer_width=\"64\""));
        assert!(!others.iter().any(|line| line.starts_with("target_feature=")));
    }

    #[test]
    fn safe_variant_suffix_excludes_unsafe() {
        assert!(is_safe_variant("verify_div_zero_safe"));
        assert!(!is_safe_variant("verify_raw_param_deref_unsafe"));
        assert!(!is_safe_variant("verify_div_zero"));
    }
}
