//! `local-stage2-surface-smoke` — non-authoritative repo-local toolchain smoke.
//!
//! This observes a repo-local `build/*/stage2` sysroot. It does not install a
//! toolchain into a clean external prefix, exercise a fresh user's PATH, or
//! mutate/resolve a default toolchain. It therefore must never satisfy the
//! canonical `installed` or `installed-default` release-gate IDs.
//!
//! The smoke checks that a built stage2 sysroot exposes the expected local,
//! Trust-only surface without any rustup linkage:
//!
//! 1. `discover_sysroot` — the first `build/*/stage2` whose `bin/trustc` is an
//!    executable, canonicalized.
//! 2. `assert_toolchain_surface` — all 11 required Trust-branded tools are
//!    executable and confined; the two compat aliases
//!    (`rustc`/`cargo`) are byte-identical to their Trust targets; every stock
//!    Rust alias is absent; and optional Miri is a paired Trust-only surface.
//! 3. `assert_compiler_identity` — the discovered `trustc` prints exactly the
//!    discovered sysroot and a host triple, with only sysroot-derived loader
//!    paths injected.
//! 4. `compile_smoke` — a tiny safe temp crate compiles with authenticated,
//!    complete verification transport and yields an artifact.
//!
//! `policy.strict` (strict/release) fails closed: a missing sysroot is a
//! failure, never a skip. Developer mode may skip a missing sysroot with a
//! note. Every executed check is a real filesystem/process observation.

use std::fs;
use std::io::{BufReader, Read as _};
use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{Context, Result, bail};

use super::trustc_native::{self, authenticated_outcomes, capture};
use super::{GatePolicy, find_stage2_tool, section};
use crate::stage2_tools::host_executable_name;

/// Trust-branded tools that MUST be present as executable regular files in the
/// standalone stage2 `bin/` surface. The two compat aliases (`rustc`/`cargo`)
/// are checked separately as byte-identical pairs.
///
/// Keep this surface aligned with the canonical toolchain contract in
/// `pipeline::surface`: the Tippy rebrand is complete, and its legacy
/// Clippy-derived public spellings are forbidden below.
const REQUIRED_TRUST_TOOLS: &[&str] = &[
    "trustc",
    "targo",
    "targo-trust",
    "trustdoc",
    "trustfmt",
    "targo-fmt",
    "tippy",
    "targo-tippy",
    "tippy-driver",
    "trust-analyzer",
    "trustd",
];

/// Same-sysroot Rust compatibility entrypoints. Each must be present AND
/// byte-identical to its Trust target (rustup registration needs a `rustc`/
/// `cargo` in `bin/`, so they are kept as same-artifact aliases).
const COMPAT_ALIAS_PAIRS: &[(&str, &str)] = &[("rustc", "trustc"), ("cargo", "targo")];

/// Stock or retired Rust-named aliases that must be ABSENT from the Trust-only
/// surface. Presence of any (even as a dangling symlink) fails the gate.
const FORBIDDEN_STOCK_ALIASES: &[&str] = &[
    "cargo-trust",
    "tcargo",
    "tcargo-trust",
    "tcargo-fmt",
    "rustdoc",
    "rustfmt",
    "cargo-fmt",
    "cargo-clippy",
    "clippy-driver",
    "targo-clippy",
    "trust-clippy",
    "trust-clippy-driver",
    "rust-analyzer",
    "miri",
    "cargo-miri",
    "rust-gdb",
    "rust-gdbgui",
    "rust-lldb",
    "rust-windbg.cmd",
];

const MAX_TOOL_BYTES: u64 = 512 * 1024 * 1024;

pub(crate) fn run(root: &Path, policy: GatePolicy) -> Result<()> {
    section("local stage2 toolchain surface smoke (non-authoritative)");
    println!(
        "Scope: repo-local stage2 only; canonical installed/default evidence requires a clean external installation and an authenticated native verifier, and remains blocked."
    );

    let Some(sysroot) = discover_sysroot(root)? else {
        if policy.strict {
            bail!(
                "strict/release standalone-toolchain gate could not find an executable build/*/stage2/bin/trustc; build it with `./x.py build --stage 2`"
            );
        }
        println!(
            "NOTE: no stage2 sysroot with an executable bin/trustc was found; skipping (developer mode only)."
        );
        return Ok(());
    };

    let bin_dir = sysroot.join("bin");
    println!("sysroot: {}", sysroot.display());
    println!("tools:   {}", bin_dir.display());

    assert_toolchain_surface(&sysroot)?;

    let scratch = tempfile::Builder::new()
        .prefix("trust_installed_toolchain_")
        .tempdir()
        .context("failed to create standalone-toolchain scratch dir")?;

    let identity = assert_compiler_identity(&sysroot, scratch.path())?;
    println!("host triple: {}", identity.host_triple);
    println!("release:     {}", identity.release);

    compile_smoke(&sysroot, scratch.path())?;

    println!();
    println!(
        "=== local-stage2-surface-smoke: PASS (non-authoritative; installed and installed-default remain blocked) ==="
    );
    Ok(())
}

// ---------------------------------------------------------------------------
// (1) discover_sysroot
// ---------------------------------------------------------------------------

/// The first `build/*/stage2` sysroot whose `bin/trustc` is an executable,
/// canonicalized. Mirrors the shell gate's `CANDIDATES` list — `build/host`
/// first (the bootstrap convenience alias), then every concrete `build/<triple>`
/// — and resolves symlink aliases to a single canonical directory.
pub(super) fn discover_sysroot(root: &Path) -> Result<Option<PathBuf>> {
    let Some(trustc) = find_stage2_tool(root, "trustc")? else {
        return Ok(None);
    };
    let bin = trustc.parent().context("validated stage2 trustc has no bin directory")?;
    let sysroot = bin.parent().context("validated stage2 trustc has no sysroot")?;
    Ok(Some(sysroot.to_path_buf()))
}

// ---------------------------------------------------------------------------
// (2) assert_bin_surface
// ---------------------------------------------------------------------------

pub(super) fn assert_toolchain_surface(sysroot: &Path) -> Result<()> {
    assert_bin_surface(&sysroot.join("bin"))?;
    assert_libexec_surface(sysroot)?;
    assert_tippy_identity(sysroot)
}

fn assert_bin_surface(bin_dir: &Path) -> Result<()> {
    // Required Trust-branded tools plus the two compat aliases are each an
    // executable regular file (symlinks that resolve to an executable regular
    // file are accepted — the shell gate used `-x`, which follows symlinks).
    for tool in REQUIRED_TRUST_TOOLS.iter().copied().chain(["rustc", "cargo"]) {
        let path = bin_dir.join(host_executable_name(tool));
        if !is_executable_confined(&path, bin_dir) {
            bail!("standalone toolchain is missing an executable {tool}: {}", path.display());
        }
    }

    // The compat aliases must be byte-identical, same-artifact aliases of their
    // Trust targets (the shell gate's `cmp -s` equivalence).
    for &(alias, trust) in COMPAT_ALIAS_PAIRS {
        let alias_path = bin_dir.join(host_executable_name(alias));
        let trust_path = bin_dir.join(host_executable_name(trust));
        if !files_equal_bounded(&alias_path, &trust_path)? {
            bail!(
                "alias pair {alias}/{trust} are not byte-identical same-surface artifacts: {} vs {}",
                alias_path.display(),
                trust_path.display()
            );
        }
    }

    // Every stock or retired Rust-named alias must be absent (a dangling
    // symlink still counts as present and fails closed).
    for forbidden in FORBIDDEN_STOCK_ALIASES.iter().copied() {
        let path = public_bin_path(bin_dir, forbidden);
        if path_exists_lexical(&path) {
            bail!(
                "forbidden stock or retired tool alias is present in the Trust-only surface: {}",
                path.display()
            );
        }
    }

    // The Miri surface is optional but paired: if either Trust-branded Miri
    // entrypoint is present, both must be present as executable regular files.
    // (The Rust-named `miri`/`cargo-miri` are already forbidden above.)
    let trust_miri = bin_dir.join(host_executable_name("trust-miri"));
    let targo_miri = bin_dir.join(host_executable_name("targo-miri"));
    if path_exists_lexical(&trust_miri) || path_exists_lexical(&targo_miri) {
        if !is_executable_confined(&trust_miri, bin_dir) {
            bail!(
                "optional Miri surface present but trust-miri is not an executable regular file: {}",
                trust_miri.display()
            );
        }
        if !is_executable_confined(&targo_miri, bin_dir) {
            bail!(
                "optional Miri surface present but targo-miri is not an executable regular file: {}",
                targo_miri.display()
            );
        }
    }

    println!(
        "  PASS: Trust-only bin surface present; compat aliases byte-identical; stock aliases absent"
    );
    Ok(())
}

/// Enforce the stage0/public-surface secondary-alias policy for the analyzer
/// proc-macro helper. A complete sysroot that requires `trust-analyzer` must
/// also carry its owned runtime helper. The stock spelling is forbidden even
/// as a dangling symlink, and the Trust spelling must resolve to executable
/// code confined to this sysroot's libexec.
fn assert_libexec_surface(sysroot: &Path) -> Result<()> {
    let libexec = sysroot.join("libexec");
    let forbidden = libexec.join(host_executable_name("rust-analyzer-proc-macro-srv"));
    if path_exists_lexical(&forbidden) {
        bail!("forbidden stock secondary libexec alias is present: {}", forbidden.display());
    }
    let owned = libexec.join(host_executable_name("trust-analyzer-proc-macro-srv"));
    if !is_executable_confined(&owned, &libexec) {
        bail!(
            "required Trust analyzer proc-macro helper is missing or not an executable confined to libexec: {}",
            owned.display()
        );
    }
    println!("  PASS: required Trust libexec helper is owned-named; stock alias absent");
    Ok(())
}

/// Exercise every public Tippy spelling, not merely its executable bit. All
/// three entrypoints must report the canonical Tippy product identity; a
/// renamed file that still exposes stock Clippy identity is not a completed
/// rebrand and must not satisfy the surface smoke.
fn assert_tippy_identity(sysroot: &Path) -> Result<()> {
    let bin = sysroot.join("bin");
    let trustc = bin.join(host_executable_name("trustc"));
    for tool in ["tippy", "targo-tippy", "tippy-driver"] {
        let path = bin.join(host_executable_name(tool));
        let mut command = Command::new(&path);
        command.arg("--version").current_dir(sysroot);
        super::scrub_gate_process_environment(&mut command);
        trustc_native::apply_trusted_runtime_library_path(&mut command, &trustc)?;
        let version = capture(command)
            .with_context(|| format!("failed to execute canonical Tippy entrypoint {tool}"))?;
        if !version.exited_with(0) {
            bail!(
                "canonical Tippy entrypoint {tool} --version failed with exit {}:\n{}",
                version.exit,
                version.stderr
            );
        }
        let identity = canonical_tippy_version(&version.stdout).with_context(|| {
            format!(
                "canonical Tippy entrypoint {tool} returned non-Tippy or malformed product identity: {:?}",
                version.stdout
            )
        })?;
        if !version.stderr.is_empty() {
            bail!(
                "canonical Tippy entrypoint {tool} emitted unexpected stderr: {}",
                version.stderr
            );
        }
        println!("  PASS: {tool} reports canonical product identity {identity}");
    }

    let targo = bin.join(host_executable_name("targo"));
    let mut dispatch = Command::new(&targo);
    dispatch.args(["tippy", "--version"]).current_dir(sysroot);
    super::scrub_gate_process_environment(&mut dispatch);
    super::pin_targo_sibling_toolchain(&mut dispatch, &targo)?;
    trustc_native::apply_trusted_runtime_library_path(&mut dispatch, &trustc)?;
    let dispatched = capture(dispatch).context("failed to execute `targo tippy --version`")?;
    if !dispatched.exited_with(0) {
        bail!("targo tippy --version failed with exit {}:\n{}", dispatched.exit, dispatched.stderr);
    }
    let identity = canonical_tippy_version(&dispatched.stdout).with_context(|| {
        format!(
            "targo tippy dispatch returned non-Tippy or malformed product identity: {:?}",
            dispatched.stdout
        )
    })?;
    if !dispatched.stderr.is_empty() {
        bail!("targo tippy --version emitted unexpected stderr: {}", dispatched.stderr);
    }
    println!("  PASS: targo tippy dispatch reports canonical product identity {identity}");
    Ok(())
}

fn canonical_tippy_version(output: &str) -> Option<&str> {
    let line = output.strip_suffix('\n').unwrap_or(output);
    let line = line.strip_suffix('\r').unwrap_or(line);
    if line.is_empty()
        || line.contains('\n')
        || line.contains('\r')
        || line.chars().any(char::is_control)
        || !line.starts_with("tippy ")
        || line.to_ascii_lowercase().contains("clippy")
    {
        return None;
    }
    Some(line)
}

// ---------------------------------------------------------------------------
// (3) assert_compiler_identity
// ---------------------------------------------------------------------------

/// Spawn the discovered `trustc` for `--print sysroot` (must equal the
/// discovered sysroot) and `-vV` (extract the host triple), injecting only
/// sysroot-derived loader paths. Returns the typed identity fields consumed by
/// both local surface diagnostics.
pub(super) struct CompilerIdentity {
    pub(super) host_triple: String,
    pub(super) release: String,
}

pub(super) fn assert_compiler_identity(sysroot: &Path, cwd: &Path) -> Result<CompilerIdentity> {
    let mut sysroot_command = trustc_command(sysroot, cwd)?;
    sysroot_command.args(["--print", "sysroot"]);
    let printed = capture(sysroot_command)?;
    if !printed.exited_with(0) {
        bail!(
            "stage2 trustc could not print sysroot (exit {}):\n{}\n{}",
            printed.exit,
            printed.stdout,
            printed.stderr
        );
    }
    let printed_sysroot = printed.stdout.trim();
    if printed_sysroot.is_empty() {
        bail!("stage2 trustc --print sysroot produced no output");
    }
    let printed_canonical = fs::canonicalize(printed_sysroot).with_context(|| {
        format!("failed to canonicalize trustc-reported sysroot {printed_sysroot}")
    })?;
    if printed_canonical != *sysroot {
        bail!(
            "standalone trust sysroot mismatch: expected {}, got {}",
            sysroot.display(),
            printed_canonical.display()
        );
    }

    let mut version_command = trustc_command(sysroot, cwd)?;
    version_command.arg("-vV");
    let version = capture(version_command)?;
    if !version.exited_with(0) {
        bail!("stage2 trustc -vV failed (exit {}):\n{}", version.exit, version.stderr);
    }
    let Some(host_triple) = parse_verbose_field(&version.stdout, "host") else {
        bail!("could not determine host triple from trustc -vV:\n{}", version.stdout);
    };
    let Some(release) = parse_verbose_field(&version.stdout, "release") else {
        bail!("could not determine release from trustc -vV:\n{}", version.stdout);
    };

    println!("  PASS: trustc reports the discovered sysroot, host, and release");
    Ok(CompilerIdentity { host_triple, release })
}

fn parse_verbose_field(version_output: &str, field: &str) -> Option<String> {
    let prefix = format!("{field}:");
    for line in version_output.lines() {
        if let Some(rest) = line.strip_prefix(&prefix) {
            let value = rest.trim();
            if !value.is_empty() {
                return Some(value.to_string());
            }
        }
    }
    None
}

// ---------------------------------------------------------------------------
// (4) compile_smoke
// ---------------------------------------------------------------------------

/// Compile a tiny safe temp crate with the discovered `trustc`, requiring a
/// complete typed transport transcript so an inherited verification-disable
/// channel cannot silently turn this smoke green.
fn compile_smoke(sysroot: &Path, cwd: &Path) -> Result<()> {
    let source = cwd.join("standalone_toolchain_smoke.rs");
    fs::write(&source, "pub fn smoke_add(a: u8, b: u8) -> u16 {\n    a as u16 + b as u16\n}\n")
        .with_context(|| format!("failed to write smoke crate {}", source.display()))?;

    let artifact = cwd.join("standalone_toolchain_smoke.rmeta");
    let mut command = trustc_command(sysroot, cwd)?;
    command
        .args([
            "-Z",
            "trust-verify-output=json",
            "-Z",
            "trust-verify-session=trust-added-local-stage2-smoke",
        ])
        .args(["--edition", "2021", "--crate-name", "standalone_toolchain_smoke"])
        .args(["--crate-type", "lib", "--emit", "metadata", "-o"])
        .arg(&artifact)
        .arg(&source);
    let compiled = capture(command)?;
    if !compiled.exited_with(0) {
        bail!(
            "standalone trustc failed to compile the smoke crate (exit {}):\n{}",
            compiled.exit,
            compiled.stderr
        );
    }
    let Some(outcomes) = authenticated_outcomes(&compiled, "trust-added-local-stage2-smoke") else {
        bail!(
            "standalone trustc compile lacked complete typed verification transport bound to the smoke session"
        );
    };
    if outcomes.is_empty()
        || outcomes
            .iter()
            .any(|row| !row.outcome.is_proved() || !row.has_obligation_id || !row.has_location)
    {
        bail!(
            "standalone smoke verification was vacuous, non-proof, or lacked stable obligation IDs/source locations: {outcomes:?}"
        );
    }
    let metadata = fs::metadata(&artifact).with_context(|| {
        format!("smoke compile reported success but produced no artifact at {}", artifact.display())
    })?;
    if !metadata.is_file() || metadata.len() == 0 {
        bail!("smoke compile artifact is not a non-empty file: {}", artifact.display());
    }

    println!("  PASS: standalone trustc compiled a smoke crate to a metadata artifact");
    Ok(())
}

// ---------------------------------------------------------------------------
// Shared plumbing
// ---------------------------------------------------------------------------

/// A `trustc` invocation through the single shared trustc-native process path:
/// caller compiler/loader authority scrubbed, symlink-free sysroot runtime
/// directories only, and fail-closed runtime-path encoding.
pub(super) fn trustc_command(sysroot: &Path, cwd: &Path) -> Result<Command> {
    let trustc = sysroot.join("bin").join(host_executable_name("trustc"));
    trustc_native::trustc_command(&trustc, cwd)
}

/// Require an executable regular file whose fully-resolved target remains in
/// the exact selected repo-local stage2 `bin/`. In-tree compatibility symlinks are allowed;
/// external tool substitution is not.
fn is_executable_confined(path: &Path, bin_dir: &Path) -> bool {
    let Ok(canonical_bin) = fs::canonicalize(bin_dir) else { return false };
    let Ok(canonical) = fs::canonicalize(path) else { return false };
    if !canonical.starts_with(&canonical_bin) {
        return false;
    }
    let Ok(metadata) = fs::symlink_metadata(&canonical) else { return false };
    if !metadata.is_file() {
        return false;
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt as _;
        metadata.permissions().mode() & 0o111 != 0
    }
    #[cfg(not(unix))]
    {
        true
    }
}

fn files_equal_bounded(left: &Path, right: &Path) -> Result<bool> {
    let left_file = fs::File::open(left)
        .with_context(|| format!("failed to open tool artifact {}", left.display()))?;
    let right_file = fs::File::open(right)
        .with_context(|| format!("failed to open tool artifact {}", right.display()))?;
    let left_metadata = left_file.metadata()?;
    let right_metadata = right_file.metadata()?;
    if !left_metadata.is_file() || !right_metadata.is_file() {
        bail!("tool aliases must resolve to regular files");
    }
    let left_len = left_metadata.len();
    let right_len = right_metadata.len();
    if left_len != right_len {
        return Ok(false);
    }
    if left_len > MAX_TOOL_BYTES {
        bail!(
            "tool artifact exceeds the {MAX_TOOL_BYTES}-byte comparison bound: {} ({left_len} bytes)",
            left.display()
        );
    }
    let mut left = BufReader::new(left_file);
    let mut right = BufReader::new(right_file);
    let mut left_chunk = [0u8; 64 * 1024];
    let mut right_chunk = [0u8; 64 * 1024];
    let mut compared = 0u64;
    loop {
        let left_read = left.read(&mut left_chunk)?;
        let right_read = right.read(&mut right_chunk)?;
        if left_read != right_read || left_chunk[..left_read] != right_chunk[..right_read] {
            return Ok(false);
        }
        compared = compared
            .checked_add(left_read as u64)
            .context("tool artifact comparison byte count overflowed")?;
        if compared > MAX_TOOL_BYTES {
            bail!("tool artifact grew beyond the {MAX_TOOL_BYTES}-byte comparison bound");
        }
        if left_read == 0 {
            return Ok(compared == left_len
                && left.get_ref().metadata()?.len() == left_len
                && right.get_ref().metadata()?.len() == right_len);
        }
    }
}

fn public_bin_path(bin_dir: &Path, name: &str) -> PathBuf {
    if name.ends_with(".cmd") {
        bin_dir.join(name)
    } else {
        bin_dir.join(host_executable_name(name))
    }
}

/// `-e`-style presence, but stricter: a path entry exists at all — including a
/// dangling symlink — so a forbidden alias cannot hide behind a broken link.
fn path_exists_lexical(path: &Path) -> bool {
    fs::symlink_metadata(path).is_ok()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn identity_fields_are_extracted_from_verbose_version() {
        let output = "trustc 1.90.0\nbinary: trustc\nhost: aarch64-apple-darwin\nrelease: 1.90.0\n";
        assert_eq!(parse_verbose_field(output, "host").as_deref(), Some("aarch64-apple-darwin"));
        assert_eq!(parse_verbose_field(output, "release").as_deref(), Some("1.90.0"));
        assert_eq!(parse_verbose_field("no host line here", "host"), None);
        assert_eq!(parse_verbose_field("host:   \n", "host"), None);
    }

    #[test]
    fn tippy_version_identity_is_canonical_and_single_line() {
        assert_eq!(
            canonical_tippy_version("tippy 0.1.98 (abcdef 2026-07-12)\n"),
            Some("tippy 0.1.98 (abcdef 2026-07-12)")
        );
        for invalid in [
            "clippy 0.1.98\n",
            "tippy 0.1.98 (clippy compatibility)\n",
            "tippy 0.1.98\nextra\n",
            " tippy 0.1.98\n",
            "",
        ] {
            assert!(canonical_tippy_version(invalid).is_none(), "accepted {invalid:?}");
        }
    }

    #[test]
    fn forbidden_and_required_surfaces_are_disjoint() {
        for forbidden in FORBIDDEN_STOCK_ALIASES {
            assert!(
                !REQUIRED_TRUST_TOOLS.contains(forbidden),
                "{forbidden} cannot be both required and forbidden"
            );
            assert!(
                !["rustc", "cargo"].contains(forbidden),
                "{forbidden} is a compat alias, not a forbidden stock alias"
            );
        }
    }

    #[test]
    fn tippy_surface_uses_only_completed_rebrand_names() {
        for required in ["tippy", "targo-tippy", "tippy-driver"] {
            assert!(REQUIRED_TRUST_TOOLS.contains(&required), "missing canonical {required}");
        }
        for retired in
            ["cargo-clippy", "clippy-driver", "targo-clippy", "trust-clippy", "trust-clippy-driver"]
        {
            assert!(
                FORBIDDEN_STOCK_ALIASES.contains(&retired),
                "retired Tippy alias {retired} must fail closed"
            );
        }
    }

    #[test]
    fn trustd_is_required_in_the_standalone_stage2_inventory() {
        assert!(REQUIRED_TRUST_TOOLS.contains(&"trustd"));
    }
}
