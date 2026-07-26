//! `prepublish-local-surface-smoke` — non-authoritative local prepublish checks.
//!
//! This checks local version/channel and stage2 surface coherence only. It does
//! not build distribution artifacts, install them into a clean prefix, verify
//! their manifests/checksums, or exercise signing/publication. Consequently it
//! must never satisfy the canonical `prepublish` release-gate ID.
//! Real dist tarballs do not exist in a dev checkout,
//! so signing/packaging/upload of `.tar.xz` artifacts cannot be exercised here.
//! Faking a tarball pass would violate `docs/testing-strategy.md` ("Shell-backed
//! or manual replacement evidence must not be promoted into a passing domination
//! dimension"). Instead this gate verifies the honest, genuinely-checkable
//! preconditions of a publish — the state that a real dist step would consume:
//!
//! 1. `assert_version_coherence` — `src/version` parses as a canonical
//!    `MAJOR.MINOR.PATCH` version and `src/ci/channel` is exactly `trust`. This
//!    is verifiable with no build at all: a publish that shipped an unparseable
//!    version or a stock (`nightly`/`beta`/`stable`) channel would be malformed.
//! 2. `discover_sysroot` — resolve the first `build/*/stage2` whose `bin/trustc`
//!    is an executable, canonicalized. Absent under strict/release ⇒ failure.
//! 3. `assert_toolchain_surface` — the daily-driver toolchain and analyzer
//!    helper surface is complete and self-consistent: Trust-branded tools are
//!    executable, the two compat aliases (`rustc`/`cargo`) are byte-identical
//!    to `trustc`/`targo`, and every forbidden stock alias is absent.
//! 4. `assert_compiler_identity` — the discovered `trustc` prints exactly the
//!    discovered sysroot and a host triple, injecting only sysroot-derived loader
//!    paths (proves the resolved compiler is the standalone one, not an ambient
//!    rustup toolchain).
//! 5. `compile_smoke` — a trivial crate compiles under the toolchain's real
//!    verification-by-default settings and yields a metadata artifact.
//!
//! Every executed check is a real filesystem/process observation of the CURRENT
//! repo state; nothing is rigged to pass. `policy.strict` (strict/release) fails
//! closed — a missing sysroot is a failure, never a skip. Developer mode may
//! still verify the (build-free) version coherence and then skip the
//! toolchain-surface checks with a loud note when no stage2 sysroot exists.

use std::fs;
use std::path::Path;

use anyhow::{Context, Result, bail};

use super::standalone_toolchain::{
    assert_compiler_identity, assert_toolchain_surface, discover_sysroot, trustc_command,
};
use super::trustc_native::capture;
use super::{GatePolicy, read_bounded_exact_file_under, section};

/// The channel a Trust release must carry. A stock Rust checkout would spell
/// this `nightly`/`beta`/`stable`; requiring `trust` proves the workspace is
/// configured as a Trust release, not an accidental upstream one.
const EXPECTED_CHANNEL: &str = "trust";

const MAX_VERSION_BYTES: u64 = 4 * 1024;
const MAX_CHANNEL_BYTES: u64 = 4 * 1024;

pub(crate) fn run(root: &Path, policy: GatePolicy) -> Result<()> {
    section("prepublish local-surface smoke (non-authoritative)");
    println!(
        "Scope: the honest preconditions a Trust publish depends on — no dist tarball is fabricated."
    );
    println!(
        "Canonical prepublish remains blocked until a native verifier can authenticate real dist, checksum, and clean-install evidence."
    );

    // (1) Workspace version coherence — verifiable with no build at all.
    let version = assert_version_coherence(root)?;
    println!("workspace version: {version} (channel={EXPECTED_CHANNEL})");

    // (2) Resolve the stage2 sysroot the publish would package.
    let Some(sysroot) = discover_sysroot(root)? else {
        if policy.strict {
            bail!(
                "strict/release prepublish gate could not find an executable build/*/stage2/bin/trustc; a publishable toolchain must be built first (`./x.py build --stage 2`)"
            );
        }
        println!(
            "NOTE: no stage2 sysroot with an executable bin/trustc was found; version coherence PASSED but the toolchain-surface + smoke preconditions are skipped (developer mode only)."
        );
        return Ok(());
    };

    let bin_dir = sysroot.join("bin");
    println!("sysroot: {}", sysroot.display());
    println!("tools:   {}", bin_dir.display());

    // (3) The daily-driver toolchain surface is complete and self-consistent.
    assert_toolchain_surface(&sysroot)?;

    let scratch = tempfile::Builder::new()
        .prefix("trust_prepublish_")
        .tempdir()
        .context("failed to create prepublish scratch dir")?;

    // (4) The resolved trustc is the standalone one (reports this exact sysroot).
    let identity = assert_compiler_identity(&sysroot, scratch.path())?;
    println!("host triple: {}", identity.host_triple);
    // Trust: bootstrap renders the `trust` channel release as `{src/version}-dev`
    // (src/bootstrap lib.rs `release()`), and the canonical version identity
    // (`targo trust version` → trust.version.v2 `rust_compat_version`) documents
    // exactly that spelling. The publishable precondition is therefore the
    // channel-derived compat version, not the bare src/version.
    let expected_release = format!("{version}-dev");
    if identity.release != expected_release {
        bail!(
            "stage2 trustc release {:?} does not match the trust-channel compat version {:?} (src/version {:?} + trust-channel `-dev` suffix)",
            identity.release,
            expected_release,
            version
        );
    }
    println!("compiler release matches the trust-channel compat version: {expected_release}");

    // (5) A trivial crate compiles under the toolchain's real defaults.
    compile_smoke(&sysroot, scratch.path())?;

    println!();
    println!(
        "=== prepublish-local-surface-smoke: PASS (non-authoritative; canonical prepublish remains blocked) ==="
    );
    Ok(())
}

// ---------------------------------------------------------------------------
// (1) version + channel coherence
// ---------------------------------------------------------------------------

/// Read `src/version` (must parse as `MAJOR.MINOR.PATCH`, ignoring an optional
/// `-pre`/`+build` suffix) and `src/ci/channel` (must be exactly `trust`).
/// Both reads go through the bounded, symlink-safe evidence reader.
fn assert_version_coherence(root: &Path) -> Result<String> {
    let version_bytes =
        read_bounded_exact_file_under(root, Path::new("src/version"), MAX_VERSION_BYTES)?;
    let version_text =
        String::from_utf8(version_bytes).context("src/version is not valid UTF-8")?;
    let version = version_text.trim();
    if version.is_empty() {
        bail!("src/version is empty; a publishable Trust release must carry a workspace version");
    }
    if !is_semver_core(version) {
        bail!(
            "src/version is not a parseable MAJOR.MINOR.PATCH version: {version:?} (a publish would embed a malformed version)"
        );
    }

    let channel_bytes =
        read_bounded_exact_file_under(root, Path::new("src/ci/channel"), MAX_CHANNEL_BYTES)?;
    let channel_text =
        String::from_utf8(channel_bytes).context("src/ci/channel is not valid UTF-8")?;
    let channel = channel_text.trim();
    if channel != EXPECTED_CHANNEL {
        bail!(
            "src/ci/channel must be {EXPECTED_CHANNEL:?} for a Trust release; found {channel:?} — publishing under a stock Rust channel is not a Trust release"
        );
    }

    println!(
        "  PASS: workspace version {version} is a parseable MAJOR.MINOR.PATCH and channel is {EXPECTED_CHANNEL}"
    );
    Ok(version.to_string())
}

/// A canonical SemVer spelling with exactly three numeric core fields. Numeric
/// core and prerelease identifiers reject leading zeroes; prerelease/build
/// identifiers are non-empty ASCII alphanumeric-or-hyphen dot components.
fn is_semver_core(version: &str) -> bool {
    let mut build_split = version.split('+');
    let before_build = build_split.next().unwrap_or_default();
    let build = build_split.next();
    if build_split.next().is_some() || build.is_some_and(|value| !valid_identifiers(value, false)) {
        return false;
    }

    let (core, prerelease) = before_build
        .split_once('-')
        .map_or((before_build, None), |(core, suffix)| (core, Some(suffix)));
    if prerelease.is_some_and(|value| !valid_identifiers(value, true)) {
        return false;
    }
    let fields = core.split('.').collect::<Vec<_>>();
    fields.len() == 3 && fields.into_iter().all(valid_numeric_identifier)
}

fn valid_numeric_identifier(value: &str) -> bool {
    !value.is_empty()
        && value.bytes().all(|byte| byte.is_ascii_digit())
        && (value == "0" || !value.starts_with('0'))
}

fn valid_identifiers(value: &str, numeric_no_leading_zero: bool) -> bool {
    !value.is_empty()
        && value.split('.').all(|identifier| {
            !identifier.is_empty()
                && identifier.bytes().all(|byte| byte.is_ascii_alphanumeric() || byte == b'-')
                && (!numeric_no_leading_zero
                    || !identifier.bytes().all(|byte| byte.is_ascii_digit())
                    || valid_numeric_identifier(identifier))
        })
}

// ---------------------------------------------------------------------------
// (2-4) Stage2 discovery, surface validation, and compiler identity are shared
// with `local-stage2-surface-smoke`; see `standalone_toolchain`.
// ---------------------------------------------------------------------------

// (5) compile_smoke
// ---------------------------------------------------------------------------

/// Compile a trivial crate with the discovered `trustc` under its real
/// verification-by-default settings. The crate carries zero verification
/// obligations, so a green compile proves the toolchain compiles code as
/// shipped — not that verification was disabled to force a pass.
fn compile_smoke(sysroot: &Path, cwd: &Path) -> Result<()> {
    let source = cwd.join("prepublish_smoke.rs");
    fs::write(&source, "pub fn smoke_identity(x: u16) -> u16 {\n    x\n}\n")
        .with_context(|| format!("failed to write smoke crate {}", source.display()))?;

    let artifact = cwd.join("prepublish_smoke.rmeta");
    let mut command = trustc_command(sysroot, cwd)?;
    command
        .args(["--edition", "2021", "--crate-name", "prepublish_smoke"])
        .args(["--crate-type", "lib", "--emit", "metadata", "-o"])
        .arg(&artifact)
        .arg(&source);
    let compiled = capture(command)?;
    if !compiled.exited_with(0) {
        bail!(
            "standalone trustc failed to compile the trivial smoke crate (exit {}):\n{}",
            compiled.exit,
            compiled.stderr
        );
    }
    let metadata = fs::metadata(&artifact).with_context(|| {
        format!("smoke compile reported success but produced no artifact at {}", artifact.display())
    })?;
    if !metadata.is_file() || metadata.len() == 0 {
        bail!("smoke compile artifact is not a non-empty file: {}", artifact.display());
    }

    println!("  PASS: standalone trustc compiled a trivial crate to a metadata artifact");
    Ok(())
}

// Shared stage2 process plumbing lives in `standalone_toolchain`.

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn semver_core_accepts_canonical_versions() {
        assert!(is_semver_core("1.99.0"));
        assert!(is_semver_core("0.0.0"));
        assert!(is_semver_core("12.34.567"));
        // Optional pre-release / build metadata suffixes are tolerated.
        assert!(is_semver_core("1.99.0-nightly"));
        assert!(is_semver_core("1.99.0+trust.1"));
    }

    #[test]
    fn semver_core_rejects_malformed_versions() {
        assert!(!is_semver_core(""));
        assert!(!is_semver_core("1.99"));
        assert!(!is_semver_core("1.99.0.1"));
        assert!(!is_semver_core("1..0"));
        assert!(!is_semver_core("1.x.0"));
        assert!(!is_semver_core("v1.99.0"));
        assert!(!is_semver_core("1.99.0 "));
        assert!(!is_semver_core("01.99.0"));
        assert!(!is_semver_core("1.99.0-01"));
        assert!(!is_semver_core("1.99.0-"));
        assert!(!is_semver_core("1.99.0+"));
        assert!(!is_semver_core("1.99.0+a..b"));
        assert!(!is_semver_core("1.99.0+a+b"));
    }

    #[test]
    fn expected_channel_is_trust_not_a_stock_rust_channel() {
        assert_eq!(EXPECTED_CHANNEL, "trust");
        for stock in ["nightly", "beta", "stable", "dev"] {
            assert_ne!(EXPECTED_CHANNEL, stock);
        }
    }
}
