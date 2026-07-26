use std::collections::HashMap;
use std::fs;
use std::fs::File;
use std::hash::Hash;
use std::io::Read as _;
use std::path::Path;
use std::path::PathBuf;
use std::sync::Arc;
use std::time::{Duration, SystemTime};

use anyhow::{Context as _, anyhow, bail};
use cargo_util::{ProcessBuilder, Sha256, StreamingOutputLimits, paths};
use serde::Deserialize;
use serde::Serialize;

use crate::CargoResult;
use crate::core::compiler::BuildRunner;
use crate::core::compiler::CompileKind;
use crate::util::Rustc;
use crate::util::context::GlobalContext;
use crate::util::file_identity::{
    OpenedFileIdentity, metadata_is_plain_file, opened_file_identity,
};
use crate::util::process_authority::configure_verified_tool_loader_environment;

// Trust: from here to `RustdocFingerprintJson` is Trust-authored. Upstream
// keys the documentation cache on `rustc -vV` alone, which is a *version*
// rather than an identity — two different trustdoc launchers report the same
// string, so a swapped launcher replays as fresh. The identity below closes
// that, and is deliberately scoped as a cache/diagnostic signal rather than
// execution authority: hashing a path around a spawn cannot prove which object
// the kernel executed. That guarantee comes from process_authority's
// fail-closed pathname/runtime closure.
//
// The bounds and timeout exist because the launcher is queried by running it;
// an unbounded read of a hostile or wedged child would hang the build instead
// of failing it.
const VERIFIED_RUSTDOC_MAX_LAUNCHER_BYTES: u64 = 256 * 1024 * 1024;
const VERIFIED_RUSTDOC_VERSION_MAX_LINE_BYTES: usize = 16 * 1024;
const VERIFIED_RUSTDOC_VERSION_MAX_STREAM_BYTES: usize = 64 * 1024;
// This is a local identity probe, so ten seconds leaves ample cold-start
// margin while keeping authenticated Targo unavailable to a wedged launcher.
const VERIFIED_RUSTDOC_VERSION_TIMEOUT: Duration = Duration::from_secs(10);

/// Persistent cache fingerprint of the `trustdoc` launcher selected by
/// verified Targo.
///
/// This digest is not execution authority: hashing a path before and after a
/// spawn cannot prove which object the kernel executed. Production authority
/// comes from process_authority's fail-closed immutable pathname/runtime
/// closure; this value invalidates cached documentation and diagnoses any
/// unexpected privileged mutation.
#[derive(Clone, Debug, Eq, Hash, PartialEq, Serialize, Deserialize)]
pub(in crate::core::compiler) struct VerifiedRustdocLauncherFingerprint {
    launcher_sha256: String,
    verbose_version_sha256: String,
}

/// Once-per-build verified `trustdoc` launcher identity.
///
/// Each actual documentation child checks the live path against this value as
/// an additional integrity diagnostic. The path is intentionally not
/// serialized: verified tool selection separately requires a canonical plain
/// `trustdoc` sibling whose entire path is outside the invoking identity's
/// write authority.
#[derive(Debug)]
pub(in crate::core::compiler) struct VerifiedRustdocLauncherIdentity {
    path: PathBuf,
    fingerprint: VerifiedRustdocLauncherFingerprint,
    initial_snapshot: LauncherSnapshot,
}

#[derive(Debug, Eq, PartialEq)]
struct LauncherSnapshot {
    file_identity: OpenedFileIdentity,
    len: u64,
    modified: Option<SystemTime>,
    sha256: String,
}

impl VerifiedRustdocLauncherIdentity {
    pub(in crate::core::compiler) fn capture_for_build(
        gctx: &GlobalContext,
        rustc: &Rustc,
    ) -> CargoResult<Self> {
        let path = gctx.rustdoc()?.to_path_buf();
        let release = rustc.version.to_string();
        let commit_hash = rustc.commit_hash.as_deref().ok_or_else(|| {
            anyhow!(
                "verified Targo selected trustc without a commit-hash identity; documentation requires a rebuilt repository toolchain"
            )
        })?;
        if !is_full_commit_hash(commit_hash) {
            bail!(
                "verified Targo selected trustc with malformed commit-hash identity `{commit_hash}`; expected a canonical 40- or 64-digit hexadecimal object id"
            );
        }
        let expected = ExpectedRustdocVersionIdentity {
            commit_hash,
            host: rustc.host.as_str(),
            release: &release,
        };
        let (fingerprint, initial_snapshot) =
            capture_verified_rustdoc_launcher_fingerprint(&path, expected)?;
        Ok(Self {
            path,
            fingerprint,
            initial_snapshot,
        })
    }

    pub(in crate::core::compiler) fn fingerprint(&self) -> &VerifiedRustdocLauncherFingerprint {
        &self.fingerprint
    }

    /// Re-hash the selected launcher at an execution endpoint.
    ///
    /// This detects mutation but does not authorize the intervening spawn. The
    /// immutable pathname/runtime closure is the authority boundary.
    pub(in crate::core::compiler) fn ensure_current(&self) -> CargoResult<()> {
        // `-Vv` is deliberately captured only once per build. Repeating a
        // process spawn before and after every dependency doc would add O(N)
        // child startups without strengthening launcher-byte continuity. The
        // endpoint still hashes the complete bounded launcher so same-size,
        // same-mtime edits cannot retain cache authority.
        let observed = capture_launcher_snapshot(&self.path)?;
        if observed != self.initial_snapshot {
            bail!(
                "verified Targo trustdoc launcher object identity changed during documentation (expected launcher_sha256={}; observed launcher_sha256={})",
                self.fingerprint.launcher_sha256,
                observed.sha256,
            );
        }
        Ok(())
    }
}

#[derive(Clone, Copy)]
struct ExpectedRustdocVersionIdentity<'a> {
    commit_hash: &'a str,
    host: &'a str,
    release: &'a str,
}

fn capture_verified_rustdoc_launcher_fingerprint(
    path: &Path,
    expected: ExpectedRustdocVersionIdentity<'_>,
) -> CargoResult<(VerifiedRustdocLauncherFingerprint, LauncherSnapshot)> {
    capture_verified_rustdoc_launcher_fingerprint_with_timeout(
        path,
        expected,
        VERIFIED_RUSTDOC_VERSION_TIMEOUT,
    )
}

fn capture_verified_rustdoc_launcher_fingerprint_with_timeout(
    path: &Path,
    expected: ExpectedRustdocVersionIdentity<'_>,
    timeout: Duration,
) -> CargoResult<(VerifiedRustdocLauncherFingerprint, LauncherSnapshot)> {
    let before = capture_launcher_snapshot(path)?;

    let mut command = ProcessBuilder::new(path);
    command.arg("-Vv");
    configure_verified_tool_loader_environment(&mut command, path)?;
    let output = command
        .exec_with_streaming_limits(
            &mut |_| Ok(()),
            &mut |_| Ok(()),
            true,
            StreamingOutputLimits::new(
                VERIFIED_RUSTDOC_VERSION_MAX_LINE_BYTES,
                VERIFIED_RUSTDOC_VERSION_MAX_STREAM_BYTES,
            )
            .with_timeout(timeout),
        )
        .with_context(|| {
            format!(
                "failed to obtain bounded verbose-version identity from verified Targo trustdoc launcher `{}`",
                path.display()
            )
        })?;

    let after = capture_launcher_snapshot(path)?;
    if before != after {
        bail!(
            "verified Targo trustdoc launcher `{}` changed while its launcher identity was captured",
            path.display()
        );
    }

    validate_verbose_version_identity(path, &output.stdout, expected)?;

    // Frame the two streams so concatenation ambiguity cannot alias distinct
    // version responses. Success status is enforced by the process helper.
    let mut version_hasher = Sha256::new();
    version_hasher
        .update(&(output.stdout.len() as u64).to_le_bytes())
        .update(&output.stdout)
        .update(&(output.stderr.len() as u64).to_le_bytes())
        .update(&output.stderr);

    Ok((
        VerifiedRustdocLauncherFingerprint {
            launcher_sha256: before.sha256.clone(),
            verbose_version_sha256: version_hasher.finish_hex(),
        },
        before,
    ))
}

fn validate_verbose_version_identity(
    path: &Path,
    stdout: &[u8],
    expected: ExpectedRustdocVersionIdentity<'_>,
) -> CargoResult<()> {
    let stdout = std::str::from_utf8(stdout).with_context(|| {
        format!(
            "verified Targo trustdoc launcher `{}` returned non-UTF-8 -Vv output",
            path.display()
        )
    })?;
    let first = stdout.lines().next().ok_or_else(|| {
        anyhow!(
            "verified Targo trustdoc launcher `{}` returned empty -Vv output",
            path.display()
        )
    })?;
    let Some(version) = first.strip_prefix("rustc ") else {
        bail!(
            "verified Targo trustdoc launcher `{}` -Vv leading line must use exact `rustc` compatibility branding, got `{first}`",
            path.display()
        );
    };
    if version.is_empty() || version.trim() != version || version.chars().any(char::is_control) {
        bail!(
            "verified Targo trustdoc launcher `{}` returned a malformed leading version line",
            path.display()
        );
    }

    let unique_field = |field: &str| -> CargoResult<&str> {
        let label = format!("{field}:");
        let prefix = format!("{label} ");
        let matching = stdout
            .lines()
            .filter(|line| line.starts_with(&label))
            .collect::<Vec<_>>();
        let value = match matching.as_slice() {
            [line] => line.strip_prefix(&prefix).ok_or_else(|| {
                anyhow!(
                    "verified Targo trustdoc launcher `{}` -Vv field `{field}` must use exact `{prefix}<value>` syntax",
                    path.display()
                )
            })?,
            [] => bail!(
                "verified Targo trustdoc launcher `{}` -Vv output is missing `{field}:`",
                path.display()
            ),
            _ => bail!(
                "verified Targo trustdoc launcher `{}` -Vv output has duplicate `{field}:` identities",
                path.display()
            ),
        };
        if value.is_empty()
            || value.trim() != value
            || value
                .bytes()
                .any(|byte| byte.is_ascii_whitespace() || byte.is_ascii_control())
        {
            bail!(
                "verified Targo trustdoc launcher `{}` -Vv output has malformed atomic `{field}` value `{value}`",
                path.display()
            );
        }
        Ok(value)
    };

    let binary = unique_field("binary")?;
    if binary != "trustdoc" {
        bail!(
            "verified Targo trustdoc launcher `{}` reported `binary: {binary}` instead of exact `binary: trustdoc`",
            path.display()
        );
    }
    let host = unique_field("host")?;
    if host != expected.host {
        bail!(
            "verified Targo trustdoc launcher `{}` host `{host}` does not match selected trustc host `{}`",
            path.display(),
            expected.host
        );
    }
    let release = unique_field("release")?;
    if release != expected.release {
        bail!(
            "verified Targo trustdoc launcher `{}` release `{release}` does not match selected trustc release `{}`",
            path.display(),
            expected.release
        );
    }
    let commit = unique_field("commit-hash")?;
    if !is_full_commit_hash(commit) {
        bail!(
            "verified Targo trustdoc launcher `{}` reported malformed canonical 40- or 64-hex commit-hash `{commit}`",
            path.display()
        );
    }
    if commit != expected.commit_hash {
        bail!(
            "verified Targo trustdoc launcher `{}` commit `{commit}` does not match selected trustc commit `{}`",
            path.display(),
            expected.commit_hash
        );
    }
    Ok(())
}

fn is_full_commit_hash(value: &str) -> bool {
    matches!(value.len(), 40 | 64) && value.bytes().all(|byte| byte.is_ascii_hexdigit())
}

fn capture_launcher_snapshot(path: &Path) -> CargoResult<LauncherSnapshot> {
    let before = fs::symlink_metadata(path).with_context(|| {
        format!(
            "failed to inspect verified Targo trustdoc launcher `{}`",
            path.display()
        )
    })?;
    if !metadata_is_plain_file(&before) {
        bail!(
            "verified Targo trustdoc launcher `{}` is not a regular non-symlink, non-reparse file",
            path.display()
        );
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt as _;

        if before.permissions().mode() & 0o111 == 0 {
            bail!(
                "verified Targo trustdoc launcher `{}` is not executable",
                path.display()
            );
        }
    }

    let file = File::open(path).with_context(|| {
        format!(
            "failed to open verified Targo trustdoc launcher `{}`",
            path.display()
        )
    })?;
    let opened_before = file.metadata().with_context(|| {
        format!(
            "failed to inspect open verified Targo trustdoc launcher `{}`",
            path.display()
        )
    })?;
    if !metadata_is_plain_file(&opened_before) {
        bail!(
            "opened verified Targo trustdoc launcher `{}` is not a regular plain file",
            path.display()
        );
    }
    if opened_before.len() > VERIFIED_RUSTDOC_MAX_LAUNCHER_BYTES {
        bail!(
            "verified Targo trustdoc launcher `{}` is {} bytes, exceeding the {}-byte launcher hashing limit",
            path.display(),
            opened_before.len(),
            VERIFIED_RUSTDOC_MAX_LAUNCHER_BYTES,
        );
    }
    let file_identity = opened_file_identity(&file).with_context(|| {
        format!(
            "failed to capture opened-file identity for verified Targo trustdoc launcher `{}`",
            path.display()
        )
    })?;
    let mut hasher = Sha256::new();
    let mut reader = (&file).take(VERIFIED_RUSTDOC_MAX_LAUNCHER_BYTES + 1);
    let mut buffer = [0_u8; 64 * 1024];
    let mut hashed_bytes = 0_u64;
    loop {
        let read = reader.read(&mut buffer).with_context(|| {
            format!(
                "failed to hash verified Targo trustdoc launcher `{}`",
                path.display()
            )
        })?;
        if read == 0 {
            break;
        }
        hashed_bytes = hashed_bytes
            .checked_add(read as u64)
            .ok_or_else(|| anyhow!("verified trustdoc launcher byte count overflowed"))?;
        if hashed_bytes > VERIFIED_RUSTDOC_MAX_LAUNCHER_BYTES {
            bail!(
                "verified Targo trustdoc launcher `{}` grew beyond the {}-byte launcher hashing limit while it was read",
                path.display(),
                VERIFIED_RUSTDOC_MAX_LAUNCHER_BYTES,
            );
        }
        hasher.update(&buffer[..read]);
    }
    if hashed_bytes != opened_before.len() {
        bail!(
            "verified Targo trustdoc launcher `{}` changed length while its bytes were hashed",
            path.display()
        );
    }
    let opened_after = file.metadata().with_context(|| {
        format!(
            "failed to re-inspect open verified Targo trustdoc launcher `{}`",
            path.display()
        )
    })?;

    let path_after = fs::symlink_metadata(path).with_context(|| {
        format!(
            "failed to re-inspect verified Targo trustdoc launcher `{}`",
            path.display()
        )
    })?;
    if !metadata_is_plain_file(&path_after) {
        bail!(
            "verified Targo trustdoc launcher `{}` stopped being a regular plain file while it was hashed",
            path.display()
        );
    }
    let reopened = File::open(path).with_context(|| {
        format!(
            "failed to reopen verified Targo trustdoc launcher `{}`",
            path.display()
        )
    })?;
    let reopened_identity = opened_file_identity(&reopened).with_context(|| {
        format!(
            "failed to recapture opened-file identity for verified Targo trustdoc launcher `{}`",
            path.display()
        )
    })?;
    if file_identity != reopened_identity
        || opened_before.len() != opened_after.len()
        || opened_before.len() != path_after.len()
        || opened_before.modified().ok() != opened_after.modified().ok()
        || opened_before.modified().ok() != path_after.modified().ok()
    {
        return Err(anyhow!(
            "verified Targo trustdoc launcher `{}` changed while its bytes were hashed",
            path.display()
        ));
    }

    Ok(LauncherSnapshot {
        file_identity,
        len: opened_before.len(),
        modified: opened_before.modified().ok(),
        sha256: hasher.finish_hex(),
    })
}

/// JSON Schema of the [`RustdocFingerprint`] file.
#[derive(Debug, Serialize, Deserialize)]
struct RustdocFingerprintJson {
    /// `rustc -vV` verbose version output.
    pub rustc_vv: String,

    /// Trust: verified-only identity of the selected canonical `trustdoc`
    /// launcher. Optional and skipped when absent so an ordinary-Cargo or
    /// unverified-Targo fingerprint file stays readable by both.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub verified_trustdoc_launcher: Option<VerifiedRustdocLauncherFingerprint>,

    /// Relative paths to cross crate info JSON files from previous `cargo doc` invocations.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub doc_parts: Vec<PathBuf>,
}

/// Structure used to deal with Rustdoc fingerprinting
///
/// This is important because the `.js`/`.html` & `.css` files
/// that are generated by Rustc don't have any versioning yet
/// (see <https://github.com/rust-lang/cargo/issues/8461>).
/// Therefore, we can end up with weird bugs and behaviours
/// if we mix different versions of these files.
///
/// We need to make sure that if there were any previous docs already compiled,
/// they were compiled with the same Rustc version that we're currently using.
/// Otherwise we must remove the `doc/` folder and compile again forcing a rebuild.
#[derive(Debug)]
pub struct RustdocFingerprint {
    /// Path to the fingerprint file.
    path: PathBuf,
    /// `rustc -vV` verbose version output for the current session.
    rustc_vv: String,
    /// Verified-only `trustdoc` launcher cache/integrity fingerprint.
    verified_trustdoc_launcher: Option<Arc<VerifiedRustdocLauncherIdentity>>,
    /// Absolute paths to new cross crate info JSON files generated in the current session.
    doc_parts: Vec<PathBuf>,
    /// The fingerprint file on disk.
    on_disk: Option<RustdocFingerprintJson>,
}

impl RustdocFingerprint {
    /// Checks whether the latest version of rustc used to compile this workspace's docs
    /// was the same as the one is currently being used in this `cargo doc` call.
    ///
    /// In case it's not,
    /// it takes care of removing the `<build-dir>/doc/` folder
    /// as well as overwriting the rustdoc fingerprint info.
    /// This is to guarantee that we won't end up with mixed versions of the `js/html/css` files
    /// which `rustdoc` autogenerates without any versioning.
    ///
    /// Each requested target platform maintains its own fingerprint file.
    /// That is, if you run `cargo doc` and then `cargo doc --target wasm32-wasip1`,
    /// you will have two separate fingerprint files:
    ///
    /// * `<build-dir>/.rustdoc_fingerprint.json` for host
    /// * `<build-dir>/wasm32-wasip1/.rustdoc_fingerprint.json`
    pub fn check_rustdoc_fingerprint(build_runner: &BuildRunner<'_, '_>) -> CargoResult<()> {
        if build_runner
            .bcx
            .gctx
            .cli_unstable()
            .skip_rustdoc_fingerprint
            && build_runner.verified_rustdoc_launcher.is_none()
        {
            return Ok(());
        }
        let new_fingerprint = RustdocFingerprintJson {
            rustc_vv: build_runner.bcx.rustc().verbose_version.clone(),
            verified_trustdoc_launcher: build_runner
                .verified_rustdoc_launcher
                .as_ref()
                .map(|identity| identity.fingerprint().clone()),
            doc_parts: Vec::new(),
        };

        for kind in &build_runner.bcx.build_config.requested_kinds {
            check_fingerprint(build_runner, &new_fingerprint, *kind)?;
        }

        Ok(())
    }

    /// Creates a new fingerprint with given doc parts paths.
    pub fn new(
        build_runner: &BuildRunner<'_, '_>,
        kind: CompileKind,
        doc_parts: Vec<PathBuf>,
    ) -> Self {
        let path = fingerprint_path(build_runner, kind);
        let rustc_vv = build_runner.bcx.rustc().verbose_version.clone();
        let verified_trustdoc_launcher = build_runner.verified_rustdoc_launcher.clone();
        let on_disk = load_on_disk(&path).filter(|on_disk| {
            verified_trustdoc_launcher
                .as_ref()
                .map_or(true, |identity| {
                    on_disk.verified_trustdoc_launcher.as_ref() == Some(identity.fingerprint())
                })
        });
        Self {
            path,
            rustc_vv,
            verified_trustdoc_launcher,
            doc_parts,
            on_disk,
        }
    }

    /// Persists the fingerprint.
    ///
    /// The closure will run before persisting the fingerprint,
    /// and will be given a list of doc parts directories for passing to
    /// `rustdoc --include-parts-dir`.
    pub fn persist<F>(&self, exec: F) -> CargoResult<()>
    where
        // 1. paths for `--include-parts-dir`
        F: Fn(&[&Path]) -> CargoResult<()>,
    {
        // Dedupe crate with the same name by file stem (which is effectively crate name),
        // since rustdoc doesn't distinguish different crate versions.
        //
        // Rules applied here:
        //
        // * If name collides, favor the one selected via CLI over cached ones
        //   (done by the insertion order)
        let base = self.path.parent().unwrap();
        let on_disk_doc_parts: Vec<_> = self
            .on_disk
            .iter()
            .flat_map(|on_disk| {
                on_disk
                    .doc_parts
                    .iter()
                    // Make absolute so that we can pass to rustdoc
                    .map(|p| base.join(p))
                    // Doc parts may be selectively cleaned by `cargo clean -p <doc>`.
                    // We should stop caching those no-exist.
                    .filter(|p| p.exists())
            })
            .collect();
        let dedup_map = on_disk_doc_parts
            .iter()
            .chain(self.doc_parts.iter())
            .map(|p| (p.file_stem(), p))
            .collect::<HashMap<_, _>>();
        let mut doc_parts: Vec<_> = dedup_map.into_values().collect();
        doc_parts.sort_unstable();

        // Prepare args for `rustdoc --include-parts-dir`
        let doc_parts_dirs: Vec<_> = doc_parts.iter().map(|p| p.parent().unwrap()).collect();
        // Trust: the merge step spawns rustdoc again, long after the compile
        // phase checked it. Bracket this spawn too, and report a launcher
        // change in preference to the child's own failure.
        if let Some(identity) = &self.verified_trustdoc_launcher {
            identity.ensure_current()?;
        }
        let result = exec(&doc_parts_dirs);
        let post_identity = self
            .verified_trustdoc_launcher
            .as_ref()
            .map(|identity| identity.ensure_current())
            .transpose();
        if let Err(identity_error) = post_identity {
            if let Err(child_error) = result {
                return Err(identity_error.context(format!(
                    "the rustdoc merge child also failed before its verified trustdoc launcher endpoint check: {child_error:#}"
                )));
            }
            return Err(identity_error);
        }
        result?;

        // Persist with relative paths to the directory where fingerprint file is at.
        let json = RustdocFingerprintJson {
            rustc_vv: self.rustc_vv.clone(),
            verified_trustdoc_launcher: self
                .verified_trustdoc_launcher
                .as_ref()
                .map(|identity| identity.fingerprint().clone()),
            doc_parts: doc_parts
                .iter()
                .map(|p| p.strip_prefix(base).unwrap_or(p).to_owned())
                .collect(),
        };
        paths::write(&self.path, serde_json::to_string(&json)?)?;

        Ok(())
    }

    /// Checks if the fingerprint is outdated comparing against given doc parts file paths.
    pub fn is_dirty(&self) -> bool {
        let Some(on_disk) = self.on_disk.as_ref() else {
            return true;
        };

        let Some(fingerprint_mtime) = paths::mtime(&self.path).ok() else {
            return true;
        };

        if self.rustc_vv != on_disk.rustc_vv {
            return true;
        }
        if self
            .verified_trustdoc_launcher
            .as_ref()
            .is_some_and(|identity| {
                on_disk.verified_trustdoc_launcher.as_ref() != Some(identity.fingerprint())
            })
        {
            return true;
        }

        for path in &self.doc_parts {
            let parts_mtime = match paths::mtime(&path) {
                Ok(mtime) => mtime,
                Err(e) => {
                    tracing::debug!("failed to read mtime of {}: {e}", path.display());
                    return true;
                }
            };

            if parts_mtime > fingerprint_mtime {
                return true;
            }
        }

        false
    }
}

/// Returns the path to rustdoc fingerprint file for a given [`CompileKind`].
fn fingerprint_path(build_runner: &BuildRunner<'_, '_>, kind: CompileKind) -> PathBuf {
    build_runner
        .files()
        .layout(kind)
        .build_dir()
        .root()
        .join(".rustdoc_fingerprint.json")
}

/// Checks rustdoc fingerprint file for a given [`CompileKind`].
fn check_fingerprint(
    build_runner: &BuildRunner<'_, '_>,
    new_fingerprint: &RustdocFingerprintJson,
    kind: CompileKind,
) -> CargoResult<()> {
    let fingerprint_path = fingerprint_path(build_runner, kind);

    let write_fingerprint = || -> CargoResult<()> {
        paths::write(&fingerprint_path, serde_json::to_string(new_fingerprint)?)
    };

    let Ok(rustdoc_data) = paths::read(&fingerprint_path) else {
        // If the fingerprint does not exist, do not clear out the doc
        // directories. Otherwise this ran into problems where projects
        // like bootstrap were creating the doc directory before running
        // `cargo doc` in a way that deleting it would break it. Verified Targo
        // cannot inherit that compatibility exception: missing identity means
        // existing docs have no authenticated launcher provenance.
        if new_fingerprint.verified_trustdoc_launcher.is_some() {
            clean_doc_dir(build_runner, kind)?;
        }
        return write_fingerprint();
    };

    match serde_json::from_str::<RustdocFingerprintJson>(&rustdoc_data) {
        Ok(on_disk_fingerprint) => {
            if rustdoc_fingerprints_match(&on_disk_fingerprint, new_fingerprint) {
                return Ok(());
            } else {
                tracing::debug!(
                    "doc fingerprint changed:\noriginal:\n{on_disk_fingerprint:?}\nnew:\n{new_fingerprint:?}"
                );
            }
        }
        Err(e) => {
            tracing::debug!("could not deserialize {:?}: {}", fingerprint_path, e);
        }
    };
    // Fingerprint does not match, delete the doc directories and write a new fingerprint.
    tracing::debug!(
        "fingerprint {:?} mismatch, clearing doc directories",
        fingerprint_path
    );
    clean_doc_dir(build_runner, kind)?;

    write_fingerprint()?;

    Ok(())
}

/// Trust: a launcher identity is required to match only when the current run
/// has one. An unverified run must be able to reuse a verified run's
/// documentation, but not the reverse — that direction would let an
/// unauthenticated launcher's output satisfy a verified request.
fn rustdoc_fingerprints_match(
    on_disk: &RustdocFingerprintJson,
    current: &RustdocFingerprintJson,
) -> bool {
    on_disk.rustc_vv == current.rustc_vv
        && current
            .verified_trustdoc_launcher
            .as_ref()
            .map_or(true, |identity| {
                on_disk.verified_trustdoc_launcher.as_ref() == Some(identity)
            })
}

fn clean_doc_dir(build_runner: &BuildRunner<'_, '_>, kind: CompileKind) -> CargoResult<()> {
    let doc_dir = build_runner
        .files()
        .layout(kind)
        .artifact_dir()
        .expect("artifact-dir was not locked")
        .doc();
    if doc_dir.exists() {
        clean_doc(doc_dir)?;
    }
    Ok(())
}

/// Loads an on-disk fingerprint JSON file.
fn load_on_disk(path: &Path) -> Option<RustdocFingerprintJson> {
    let on_disk = match paths::read(path) {
        Ok(data) => data,
        Err(e) => {
            tracing::debug!("failed to read rustdoc fingerprint at {path:?}: {e}");
            return None;
        }
    };

    match serde_json::from_str::<RustdocFingerprintJson>(&on_disk) {
        Ok(on_disk) => Some(on_disk),
        Err(e) => {
            tracing::debug!("could not deserialize {path:?}: {e}");
            None
        }
    }
}

fn clean_doc(path: &Path) -> CargoResult<()> {
    let entries = path
        .read_dir()
        .with_context(|| format!("failed to read directory `{}`", path.display()))?;
    for entry in entries {
        let entry = entry?;
        // Don't remove hidden files. Rustdoc does not create them,
        // but the user might have.
        if entry
            .file_name()
            .to_str()
            .map_or(false, |name| name.starts_with('.'))
        {
            continue;
        }
        let path = entry.path();
        if entry.file_type()?.is_dir() {
            paths::remove_dir_all(path)?;
        } else {
            paths::remove_file(path)?;
        }
    }
    Ok(())
}

// Trust: pins the launcher-identity capture and the asymmetric cache-match rule
// above, including the bounded/timed version probe, which cannot be exercised
// from an integration test without a real wedged launcher.
#[cfg(test)]
mod tests {
    use super::{
        ExpectedRustdocVersionIdentity, RustdocFingerprintJson, VerifiedRustdocLauncherFingerprint,
        VerifiedRustdocLauncherIdentity, capture_verified_rustdoc_launcher_fingerprint,
        capture_verified_rustdoc_launcher_fingerprint_with_timeout, rustdoc_fingerprints_match,
        validate_verbose_version_identity,
    };

    fn expected_version() -> ExpectedRustdocVersionIdentity<'static> {
        ExpectedRustdocVersionIdentity {
            commit_hash: "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
            host: "test-host",
            release: "test",
        }
    }

    fn launcher(launcher_sha256: &str) -> VerifiedRustdocLauncherFingerprint {
        VerifiedRustdocLauncherFingerprint {
            launcher_sha256: launcher_sha256.to_owned(),
            verbose_version_sha256: "version".to_owned(),
        }
    }

    fn fingerprint(launcher: Option<VerifiedRustdocLauncherFingerprint>) -> RustdocFingerprintJson {
        RustdocFingerprintJson {
            rustc_vv: "unchanged rustc -vV".to_owned(),
            verified_trustdoc_launcher: launcher,
            doc_parts: Vec::new(),
        }
    }

    #[test]
    fn ordinary_rustdoc_fingerprint_remains_compatible_with_verified_extension() {
        let ordinary = fingerprint(None);
        let verified_on_disk = fingerprint(Some(launcher("old-launcher")));
        assert!(rustdoc_fingerprints_match(&verified_on_disk, &ordinary));
    }

    #[test]
    fn verified_rustdoc_fingerprint_requires_exact_launcher_identity() {
        let current = fingerprint(Some(launcher("current-launcher")));
        assert!(!rustdoc_fingerprints_match(&fingerprint(None), &current));
        assert!(!rustdoc_fingerprints_match(
            &fingerprint(Some(launcher("different-launcher"))),
            &current,
        ));
        assert!(rustdoc_fingerprints_match(&current, &current));
    }

    #[test]
    fn verbose_version_identity_is_semantic_and_unique() {
        let path = std::path::Path::new("trustdoc");
        let expected = ExpectedRustdocVersionIdentity {
            commit_hash: "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
            host: "test-host",
            release: "test",
        };
        validate_verbose_version_identity(
            path,
            b"rustc test (trustdoc)\nbinary: trustdoc\ncommit-hash: aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\nhost: test-host\nrelease: test\n",
            expected,
        )
        .unwrap();
        let sha256 = "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";
        validate_verbose_version_identity(
            path,
            format!(
                "rustc test (trustdoc)\nbinary: trustdoc\ncommit-hash: {sha256}\nhost: test-host\nrelease: test\n"
            )
            .as_bytes(),
            ExpectedRustdocVersionIdentity {
                commit_hash: sha256,
                host: "test-host",
                release: "test",
            },
        )
        .unwrap();

        for invalid in [
            "trustdoc test\nbinary: trustdoc\ncommit-hash: aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\nhost: test-host\nrelease: test\n",
            "rustc test (trustdoc)\nbinary: rustdoc\ncommit-hash: aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\nhost: test-host\nrelease: test\n",
            "rustc test (trustdoc)\nbinary: trustdoc\ncommit-hash: other\nhost: test-host\nrelease: test\n",
            "rustc test (trustdoc)\nbinary: trustdoc\nbinary: trustdoc\ncommit-hash: aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\nhost: test-host\nrelease: test\n",
            "rustc test (trustdoc)\nbinary: trustdoc\ncommit-hash: aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\nhost: other-host\nrelease: test\n",
            "rustc test (trustdoc)\nbinary: trustdoc\ncommit-hash: aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\nhost: test-host\nrelease: other\n",
            "rustc test (trustdoc)\nbinary:trustdoc\ncommit-hash: aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\nhost: test-host\nrelease: test\n",
        ] {
            assert!(
                validate_verbose_version_identity(path, invalid.as_bytes(), expected).is_err(),
                "accepted invalid verbose identity: {invalid}"
            );
        }
    }

    #[cfg(unix)]
    fn write_executable(path: &std::path::Path, contents: &str) {
        use std::os::unix::fs::PermissionsExt as _;

        std::fs::write(path, contents).unwrap();
        let mut permissions = std::fs::metadata(path).unwrap().permissions();
        permissions.set_mode(0o755);
        std::fs::set_permissions(path, permissions).unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn launcher_bytes_participate_even_when_verbose_version_is_unchanged() {
        let directory = tempfile::TempDir::new().unwrap();
        let first = directory.path().join("trustdoc-first");
        let second = directory.path().join("trustdoc-second");
        let version_script = |marker| {
            format!(
                "#!/bin/sh\n# {marker}\nprintf 'rustc test (trustdoc)\\nbinary: trustdoc\\ncommit-hash: aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\\nhost: test-host\\nrelease: test\\n'\n"
            )
        };
        write_executable(&first, &version_script("first launcher bytes"));
        write_executable(&second, &version_script("second launcher bytes"));

        let first = capture_verified_rustdoc_launcher_fingerprint(&first, expected_version())
            .unwrap()
            .0;
        let second = capture_verified_rustdoc_launcher_fingerprint(&second, expected_version())
            .unwrap()
            .0;
        assert_ne!(first.launcher_sha256, second.launcher_sha256);
        assert_eq!(first.verbose_version_sha256, second.verbose_version_sha256);
        assert_ne!(first, second);
    }

    #[cfg(unix)]
    #[test]
    fn launcher_mutation_during_version_probe_fails_closed() {
        let directory = tempfile::TempDir::new().unwrap();
        let trustdoc = directory.path().join("trustdoc");
        write_executable(
            &trustdoc,
            r#"#!/bin/sh
printf 'rustc test (trustdoc)\nbinary: trustdoc\ncommit-hash: aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\nhost: test-host\nrelease: test\n'
printf '#!/bin/sh\nexit 0\n' > "$0"
"#,
        );

        let error = capture_verified_rustdoc_launcher_fingerprint(&trustdoc, expected_version())
            .unwrap_err();
        assert!(
            format!("{error:#}").contains("changed while its launcher identity was captured"),
            "unexpected error: {error:#}"
        );
    }

    #[cfg(unix)]
    #[test]
    fn verbose_version_probe_has_a_finite_output_budget() {
        let directory = tempfile::TempDir::new().unwrap();
        let trustdoc = directory.path().join("trustdoc");
        write_executable(
            &trustdoc,
            r#"#!/bin/sh
i=0
while [ "$i" -lt 20000 ]; do
    printf x
    i=$((i + 1))
done
"#,
        );

        let error = capture_verified_rustdoc_launcher_fingerprint(&trustdoc, expected_version())
            .unwrap_err();
        let rendered = format!("{error:#}");
        assert!(
            rendered.contains("output") && rendered.contains("limit"),
            "unexpected error: {rendered}"
        );
    }

    #[cfg(unix)]
    #[test]
    fn verbose_version_probe_has_a_wall_clock_timeout() {
        let directory = tempfile::TempDir::new().unwrap();
        let trustdoc = directory.path().join("trustdoc");
        write_executable(
            &trustdoc,
            r#"#!/bin/sh
while :; do
    sleep 60
done
"#,
        );

        let started = std::time::Instant::now();
        let error = capture_verified_rustdoc_launcher_fingerprint_with_timeout(
            &trustdoc,
            expected_version(),
            std::time::Duration::from_millis(200),
        )
        .unwrap_err();
        assert!(
            started.elapsed() < std::time::Duration::from_secs(5),
            "silent trustdoc timeout took {:?}",
            started.elapsed()
        );
        let rendered = format!("{error:#}");
        assert!(rendered.contains("wall-clock timeout"), "{rendered}");
    }

    #[cfg(unix)]
    #[test]
    fn oversized_launcher_is_rejected_before_hashing_or_execution() {
        use super::VERIFIED_RUSTDOC_MAX_LAUNCHER_BYTES;
        use std::os::unix::fs::PermissionsExt as _;

        let directory = tempfile::TempDir::new().unwrap();
        let trustdoc = directory.path().join("trustdoc");
        let file = std::fs::File::create(&trustdoc).unwrap();
        // Sparse extension keeps the regression cheap while proving the size
        // gate runs before hashing hundreds of megabytes.
        file.set_len(VERIFIED_RUSTDOC_MAX_LAUNCHER_BYTES + 1)
            .unwrap();
        let mut permissions = file.metadata().unwrap().permissions();
        permissions.set_mode(0o755);
        std::fs::set_permissions(&trustdoc, permissions).unwrap();

        let error = capture_verified_rustdoc_launcher_fingerprint(&trustdoc, expected_version())
            .unwrap_err();
        assert!(
            format!("{error:#}").contains("launcher hashing limit"),
            "unexpected error: {error:#}"
        );
    }

    #[cfg(unix)]
    #[test]
    fn same_bytes_different_file_replacement_breaks_endpoint_continuity() {
        let directory = tempfile::TempDir::new().unwrap();
        let trustdoc = directory.path().join("trustdoc");
        let replacement = directory.path().join("replacement");
        let script = "#!/bin/sh\nprintf 'rustc test (trustdoc)\\nbinary: trustdoc\\ncommit-hash: aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\\nhost: test-host\\nrelease: test\\n'\n";
        write_executable(&trustdoc, script);
        write_executable(&replacement, script);
        let (fingerprint, initial_snapshot) =
            capture_verified_rustdoc_launcher_fingerprint(&trustdoc, expected_version()).unwrap();
        let identity = VerifiedRustdocLauncherIdentity {
            path: trustdoc.clone(),
            fingerprint,
            initial_snapshot,
        };

        std::fs::remove_file(&trustdoc).unwrap();
        std::fs::rename(&replacement, &trustdoc).unwrap();
        let error = identity.ensure_current().unwrap_err();
        assert!(
            format!("{error:#}").contains("object identity changed"),
            "unexpected error: {error:#}"
        );
    }
}
