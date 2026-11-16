use crate::compiler::{Compilation, Doctest, Unit, UnitHash, UnitOutput};
use crate::ops;
use crate::util::data_structures::HashMap;
use crate::util::errors::CargoResult;
// Trust: a libtest summary's four numbers.
use crate::util::machine_message::TestCounts;
use crate::util::{CliError, CliResult, GlobalContext, add_path_args};
use crate::workspace::profiles::PanicStrategy;
use crate::workspace::{TargetKind, Workspace};
use anyhow::{Context as _, format_err};
use cargo_util::{ProcessBuilder, ProcessError, Sha256};
use cargo_util_terminal::{ColorChoice, Verbosity};
use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::ffi::OsString;
use std::fmt::Write;
use std::fs::{self, File};
use std::hash::Hash;
use std::io::Read as _;
use std::path::{Path, PathBuf};

/// Validate harness arguments against the native scheduler's thread ownership.
/// Capability discovery and actual graph execution use this same policy.
pub fn validate_native_test_arguments(args: &[&str]) -> CargoResult<()> {
    worker_budget::visit_thread_requests(args, |_| Err(NativeTestBudgetRefusal.into()))
}

/// A real libtest worker option conflicts with the native scheduler's owner.
/// Callers must establish the selected native libtest scope before promoting
/// this typed refusal; custom harness arguments have their own grammar.
#[derive(Debug)]
pub struct NativeTestBudgetRefusal;

impl std::fmt::Display for NativeTestBudgetRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("build.test-jobs owns libtest's thread budget; omit --test-threads and use --config build.test-jobs=N")
    }
}

impl std::error::Error for NativeTestBudgetRefusal {}

// Trust: compile and execution nodes use one existing dependency queue.
// Trust: only owned native scheduling transports cross authenticated test exec.
#[cfg(any(target_os = "linux", target_os = "macos"))]
pub(crate) mod auth_scheduling;
#[cfg(all(
    test,
    any(target_os = "linux", target_os = "macos"),
    any(target_arch = "x86_64", target_arch = "aarch64")
))]
mod authenticated_lifecycle;
pub(crate) mod graph;
// Trust: per-harness weight and exclusivity for native test actions.
pub(crate) mod harness_policy;
// Trust: `targo test --plan`: several requests in one build graph.
pub mod plan;
// Trust: which requests of a plan one run performs.
pub mod plan_select;
// Trust: the paths a git range changed, read by Targo itself.
pub mod plan_change;
// Trust: how a plan run ended: its exit status and closing record.
pub mod plan_clock;
pub mod plan_outcome;
// Trust: what a plan run judged beyond each harness's exit.
pub(crate) mod plan_judge;
// Trust: a plan's known-red file: the failures a plan run expects.
pub(crate) mod plan_expect;
// Trust: holds a plan's one unit graph to its requests' standalone graphs.
pub mod plan_parity;
// Trust: a plan's `[[tool]]` and `[[workspace]]` phases, each under its own
// manifest.
pub mod plan_phases;
// Trust: holds the repository's checked-in plan to the tree.
#[cfg(test)]
mod plan_checked_in;
mod prepared;
#[cfg(any(target_os = "linux", target_os = "macos"))]
pub(crate) mod retained;
pub(crate) mod workload;
// Trust: cooperative libtest ceilings bind both native and prepared execution.
mod worker_budget;
pub use prepared::try_run_prepared_tests;

#[cfg(any(target_os = "linux", target_os = "macos"))]
use std::io::{Seek as _, Write as _};
#[cfg(target_os = "linux")]
use std::os::fd::{AsRawFd as _, FromRawFd as _, OwnedFd};
#[cfg(target_os = "linux")]
use std::os::unix::process::CommandExt as _;

pub struct TestOptions {
    pub compile_opts: ops::CompileOptions,
    pub no_run: bool,
    pub no_fail_fast: bool,
    /// Trust: binary harnesses that must actually be present in the selected test
    /// inventory and report passing tests, without narrowing that inventory.
    pub required_test_bins: Vec<String>,
}

// Trust: from here to `enum TestKind` is Trust-authored — test-execution
// authority. Running a test binary is arbitrary code execution, and upstream
// runs whatever file is at the expected path. A verified session must instead
// run exactly the binaries it compiled and authorized, so the frontend hands
// this process a manifest naming them by digest and the manifest itself is
// bound to the session. The bounds are there because the manifest is read
// before it is trusted.
const TRUST_TARGO_PREPARED_TEST_SESSION: &str = "TRUST_TARGO_PREPARED_TEST_SESSION";
const TRUST_TARGO_TEST_EXECUTION_MANIFEST: &str = "TRUST_TARGO_TEST_EXECUTION_MANIFEST";
const TRUST_TARGO_TEST_EXECUTION_MANIFEST_SHA256: &str =
    "TRUST_TARGO_TEST_EXECUTION_MANIFEST_SHA256";
const TEST_EXECUTION_AUTHORITY_SCHEMA: &str = "trust.targo-test-execution-authority.v2";
const MAX_TEST_EXECUTION_AUTHORITY_BYTES: u64 = 8 * 1024 * 1024;
const MAX_TEST_EXECUTION_AUTHORITY_ENTRIES: usize = 4096;

#[derive(Debug, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct TestExecutionAuthorityManifest {
    schema: String,
    verification_session: String,
    target_directory: String,
    executables: Vec<TestExecutionAuthorityEntry>,
    #[serde(default)]
    prepared: Option<trust_test_execution::PreparedTests>,
}

#[derive(Debug, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct TestExecutionAuthorityEntry {
    target: String,
    path: String,
    sha256: String,
    size: u64,
}

struct TestExecutionAuthority {
    executables: BTreeMap<PathBuf, TestExecutionAuthorityEntry>,
    prepared: Option<trust_test_execution::PreparedTests>,
}

impl TestExecutionAuthority {
    fn validate_executable(&self, path: &Path) -> CargoResult<()> {
        let metadata = fs::symlink_metadata(path).with_context(|| {
            format!(
                "cannot inspect authorized test executable `{}`",
                path.display()
            )
        })?;
        if metadata.file_type().is_symlink() || !metadata.file_type().is_file() {
            anyhow::bail!(
                "authorized test executable `{}` is not a regular non-symlink file",
                path.display()
            );
        }
        let canonical = path.canonicalize().with_context(|| {
            format!(
                "cannot canonicalize authorized test executable `{}`",
                path.display()
            )
        })?;
        let expected = self.executables.get(&canonical).ok_or_else(|| {
            anyhow::format_err!(
                "Cargo attempted to execute `{}` outside the authenticated phase-A inventory",
                canonical.display()
            )
        })?;
        let (sha256, size) = exact_regular_test_executable_identity(&canonical)?;
        if size != expected.size || sha256 != expected.sha256 {
            anyhow::bail!(
                "test executable `{}` changed after phase A (expected size={} sha256={}, observed size={} sha256={})",
                canonical.display(),
                expected.size,
                expected.sha256,
                size,
                sha256,
            );
        }
        Ok(())
    }

    /// Copy the exact authorized bytes into a sealed anonymous execution image.
    ///
    /// An open descriptor alone is not enough: another process can still write
    /// the underlying inode between hashing and `exec`.  Linux memfd seals make
    /// the byte identity immutable before the child exists, and executing the
    /// descriptor directly prevents a rename/replace race on the Cargo artifact.
    #[cfg(target_os = "linux")]
    fn executable_snapshot(&self, path: &Path) -> CargoResult<AuthenticatedExecutableSnapshot> {
        let canonical = path.canonicalize().with_context(|| {
            format!(
                "cannot canonicalize authorized test executable `{}`",
                path.display()
            )
        })?;
        let expected = self.executables.get(&canonical).ok_or_else(|| {
            anyhow::format_err!(
                "Cargo attempted to execute `{}` outside the authenticated phase-A inventory",
                canonical.display()
            )
        })?;
        AuthenticatedExecutableSnapshot::capture(&canonical, expected)
    }

    #[cfg(target_os = "macos")]
    fn mac_executable_snapshot(
        &self,
        path: &Path,
    ) -> CargoResult<AuthenticatedMacExecutableSnapshot> {
        let canonical = path.canonicalize().with_context(|| {
            format!(
                "cannot canonicalize authorized test executable `{}`",
                path.display()
            )
        })?;
        let expected = self.executables.get(&canonical).ok_or_else(|| {
            anyhow::format_err!(
                "Cargo attempted to execute `{}` outside the authenticated phase-A inventory",
                canonical.display()
            )
        })?;
        AuthenticatedMacExecutableSnapshot::capture(&canonical, expected)
    }
}

/// Move an owned descriptor out of the stdio range without creating a leak on
/// either the success or failure path. `F_DUPFD_CLOEXEC` preserves the private
/// execution handle across `fork` but closes it after successful `execveat`.
#[cfg(target_os = "linux")]
fn owned_fd_at_least(fd: OwnedFd, minimum: libc::c_int) -> std::io::Result<OwnedFd> {
    if fd.as_raw_fd() >= minimum {
        return Ok(fd);
    }
    let duplicated = unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_DUPFD_CLOEXEC, minimum) };
    if duplicated < 0 {
        return Err(std::io::Error::last_os_error());
    }
    // `fd` remains RAII-owned and closes as this function returns. The new
    // descriptor is independently owned, including if a later operation fails.
    Ok(unsafe { OwnedFd::from_raw_fd(duplicated) })
}

/// Linux-only immutable image used for evidence-grade test execution.
///
/// The descriptor is always at least 3 and retains `FD_CLOEXEC`, so it cannot
/// alias stdin/stdout/stderr. `Command::pre_exec` passes it directly to
/// `execveat(AT_EMPTY_PATH)` while it is still present; successful `exec` then
/// closes it so test code does not inherit the authority handle. Because the
/// executed object is an anonymous copy, `/proc/self/exe`, `current_exe()`,
/// inode/xattr/mode identity, and self-reexecution by the discovered path do
/// not have ordinary pathname-launch semantics.
#[cfg(target_os = "linux")]
struct AuthenticatedExecutableSnapshot {
    file: File,
}

#[cfg(target_os = "linux")]
impl AuthenticatedExecutableSnapshot {
    fn capture(
        path: &Path,
        expected: &TestExecutionAuthorityEntry,
    ) -> CargoResult<AuthenticatedExecutableSnapshot> {
        use std::os::unix::fs::{MetadataExt as _, OpenOptionsExt as _, PermissionsExt as _};

        let before = fs::symlink_metadata(path)
            .with_context(|| format!("cannot inspect test executable `{}`", path.display()))?;
        if before.file_type().is_symlink() || !before.file_type().is_file() {
            anyhow::bail!(
                "authorized test executable `{}` is not a regular non-symlink file",
                path.display()
            );
        }
        if before.permissions().mode() & 0o111 == 0 {
            anyhow::bail!("test artifact `{}` is not executable", path.display());
        }

        // O_NOFOLLOW closes the final-component swap between the metadata check
        // and open. A rename to another regular file is harmless only if the
        // bytes copied below still match the authenticated digest exactly.
        let mut source = fs::OpenOptions::new()
            .read(true)
            .custom_flags(libc::O_CLOEXEC | libc::O_NOFOLLOW)
            .open(path)
            .with_context(|| format!("cannot open test executable `{}`", path.display()))?;
        let opened = source
            .metadata()
            .with_context(|| format!("cannot inspect open test executable `{}`", path.display()))?;
        if !opened.file_type().is_file() || opened.mode() & 0o111 == 0 {
            anyhow::bail!(
                "authorized test executable `{}` did not open as an executable regular file",
                path.display()
            );
        }

        let name = b"trust-certified-test\0";
        let fd = unsafe {
            libc::memfd_create(
                name.as_ptr().cast(),
                libc::MFD_CLOEXEC | libc::MFD_ALLOW_SEALING,
            )
        };
        if fd < 0 {
            return Err(std::io::Error::last_os_error())
                .context("cannot create sealed certified-test execution image");
        }
        let image_fd = unsafe { OwnedFd::from_raw_fd(fd) };
        let image_fd = owned_fd_at_least(image_fd, 3)
            .context("cannot move certified-test execution image out of the stdio fd range")?;
        let mut image = File::from(image_fd);

        let mut hasher = Sha256::new();
        let mut size = 0_u64;
        let mut buffer = [0_u8; 64 * 1024];
        loop {
            let read = source
                .read(&mut buffer)
                .with_context(|| format!("cannot copy test executable `{}`", path.display()))?;
            if read == 0 {
                break;
            }
            size = size.checked_add(read as u64).ok_or_else(|| {
                anyhow::format_err!("test executable `{}` is too large", path.display())
            })?;
            hasher.update(&buffer[..read]);
            image.write_all(&buffer[..read]).with_context(|| {
                format!(
                    "cannot populate sealed execution image for `{}`",
                    path.display()
                )
            })?;
        }
        let sha256 = hasher.finish_hex();
        if size != expected.size || sha256 != expected.sha256 {
            anyhow::bail!(
                "test executable `{}` changed before its immutable execution image was captured (expected size={} sha256={}, observed size={} sha256={})",
                path.display(),
                expected.size,
                expected.sha256,
                size,
                sha256,
            );
        }

        let executable = fs::Permissions::from_mode(0o500);
        image.set_permissions(executable).with_context(|| {
            format!(
                "cannot mark sealed execution image for `{}` executable",
                path.display()
            )
        })?;
        image
            .seek(std::io::SeekFrom::Start(0))
            .with_context(|| format!("cannot rewind execution image for `{}`", path.display()))?;

        let required_seals =
            libc::F_SEAL_WRITE | libc::F_SEAL_GROW | libc::F_SEAL_SHRINK | libc::F_SEAL_SEAL;
        if unsafe { libc::fcntl(image.as_raw_fd(), libc::F_ADD_SEALS, required_seals) } < 0 {
            return Err(std::io::Error::last_os_error()).with_context(|| {
                format!(
                    "cannot seal certified-test execution image for `{}`",
                    path.display()
                )
            });
        }
        let observed_seals = unsafe { libc::fcntl(image.as_raw_fd(), libc::F_GET_SEALS) };
        if observed_seals < 0 || observed_seals & required_seals != required_seals {
            anyhow::bail!(
                "certified-test execution image for `{}` did not retain its required immutable seals",
                path.display()
            );
        }

        // Authenticate once more after sealing. This also closes the narrow
        // window in which another same-UID process could try to open the memfd
        // through procfs and modify it after the streaming hash but before the
        // seals took effect: the second hash observes immutable bytes.
        image
            .seek(std::io::SeekFrom::Start(0))
            .with_context(|| format!("cannot rewind sealed image for `{}`", path.display()))?;
        let mut sealed_hasher = Sha256::new();
        sealed_hasher.update_file(&image).with_context(|| {
            format!(
                "cannot authenticate sealed execution image for `{}`",
                path.display()
            )
        })?;
        let sealed_size = image
            .metadata()
            .with_context(|| format!("cannot inspect sealed image for `{}`", path.display()))?
            .len();
        let sealed_sha256 = sealed_hasher.finish_hex();
        if sealed_size != expected.size || sealed_sha256 != expected.sha256 {
            anyhow::bail!(
                "sealed execution image for `{}` does not match its authenticated identity (expected size={} sha256={}, observed size={} sha256={})",
                path.display(),
                expected.size,
                expected.sha256,
                sealed_size,
                sealed_sha256,
            );
        }
        image
            .seek(std::io::SeekFrom::Start(0))
            .with_context(|| format!("cannot rewind sealed image for `{}`", path.display()))?;
        Ok(AuthenticatedExecutableSnapshot { file: image })
    }

    fn fd(&self) -> libc::c_int {
        self.file.as_raw_fd()
    }
}

/// A private, byte-authenticated Mach-O image used by the macOS execution
/// backend. macOS has no `fexecve`, so the pathname is used only to ask the
/// kernel to create a *suspended* process. Before a single instruction is
/// resumed, the parent authenticates the live process's code-directory hash
/// against the exact bytes copied here and requires kernel kill-on-invalid
/// enforcement. A pathname replacement can therefore only make launch fail or
/// produce a different live CDHash; it cannot run unauthenticated user code.
#[cfg(target_os = "macos")]
struct AuthenticatedMacExecutableSnapshot {
    _directory: tempfile::TempDir,
    path: PathBuf,
    file: File,
    sha256: String,
    size: u64,
    cdhash: String,
}

#[cfg(target_os = "macos")]
impl AuthenticatedMacExecutableSnapshot {
    fn capture(
        path: &Path,
        expected: &TestExecutionAuthorityEntry,
    ) -> CargoResult<AuthenticatedMacExecutableSnapshot> {
        use std::os::unix::fs::{MetadataExt as _, OpenOptionsExt as _, PermissionsExt as _};

        let before = fs::symlink_metadata(path)
            .with_context(|| format!("cannot inspect test executable `{}`", path.display()))?;
        if before.file_type().is_symlink()
            || !before.file_type().is_file()
            || before.permissions().mode() & 0o111 == 0
        {
            anyhow::bail!(
                "authorized test executable `{}` is not an executable regular non-symlink file",
                path.display()
            );
        }
        let mut source = fs::OpenOptions::new()
            .read(true)
            .custom_flags(libc::O_CLOEXEC | libc::O_NOFOLLOW)
            .open(path)
            .with_context(|| format!("cannot open test executable `{}`", path.display()))?;
        let opened = source
            .metadata()
            .with_context(|| format!("cannot inspect open test executable `{}`", path.display()))?;
        if !opened.file_type().is_file() || opened.mode() & 0o111 == 0 {
            anyhow::bail!(
                "authorized test executable `{}` did not open as an executable regular file",
                path.display()
            );
        }

        let directory = tempfile::Builder::new()
            .prefix("trust-certified-test.")
            .tempdir()
            .context("cannot create private certified-test execution directory")?;
        fs::set_permissions(directory.path(), fs::Permissions::from_mode(0o700))
            .context("cannot make certified-test execution directory private")?;
        let snapshot_path = directory.path().join("authenticated-test");
        let mut image = fs::OpenOptions::new()
            .create_new(true)
            .write(true)
            .custom_flags(libc::O_CLOEXEC | libc::O_NOFOLLOW)
            .mode(0o600)
            .open(&snapshot_path)
            .with_context(|| {
                format!(
                    "cannot create certified-test execution image `{}`",
                    snapshot_path.display()
                )
            })?;

        let mut hasher = Sha256::new();
        let mut size = 0_u64;
        let mut buffer = [0_u8; 64 * 1024];
        loop {
            let read = source
                .read(&mut buffer)
                .with_context(|| format!("cannot copy test executable `{}`", path.display()))?;
            if read == 0 {
                break;
            }
            size = size.checked_add(read as u64).ok_or_else(|| {
                anyhow::format_err!("test executable `{}` is too large", path.display())
            })?;
            hasher.update(&buffer[..read]);
            image.write_all(&buffer[..read]).with_context(|| {
                format!(
                    "cannot populate certified-test execution image for `{}`",
                    path.display()
                )
            })?;
        }
        let sha256 = hasher.finish_hex();
        if size != expected.size || sha256 != expected.sha256 {
            anyhow::bail!(
                "test executable `{}` changed while its private execution image was captured (expected size={} sha256={}, observed size={} sha256={})",
                path.display(),
                expected.size,
                expected.sha256,
                size,
                sha256,
            );
        }
        image.sync_all().with_context(|| {
            format!(
                "cannot synchronize certified-test execution image for `{}`",
                path.display()
            )
        })?;
        image
            .set_permissions(fs::Permissions::from_mode(0o500))
            .with_context(|| {
                format!(
                    "cannot mark certified-test execution image for `{}` executable",
                    path.display()
                )
            })?;
        drop(image);

        // Retain only a read handle. The live-process CDHash check below is the
        // authority boundary; this handle additionally lets us authenticate the
        // captured bytes immediately before resume and after child exit.
        let mut file = fs::OpenOptions::new()
            .read(true)
            .custom_flags(libc::O_CLOEXEC | libc::O_NOFOLLOW)
            .open(&snapshot_path)
            .with_context(|| {
                format!(
                    "cannot reopen certified-test execution image `{}`",
                    snapshot_path.display()
                )
            })?;
        authenticate_open_mac_snapshot(&mut file, &sha256, size)?;
        let cdhash = macho_sha256_cdhash(&mut file)?;
        Ok(AuthenticatedMacExecutableSnapshot {
            _directory: directory,
            path: snapshot_path,
            file,
            sha256,
            size,
            cdhash,
        })
    }
}

#[cfg(target_os = "macos")]
fn authenticate_open_mac_snapshot(
    file: &mut File,
    expected_sha256: &str,
    expected_size: u64,
) -> CargoResult<()> {
    file.seek(std::io::SeekFrom::Start(0))
        .context("cannot rewind certified-test execution image")?;
    let mut hasher = Sha256::new();
    hasher
        .update_file(&*file)
        .context("cannot authenticate certified-test execution image")?;
    let size = file
        .metadata()
        .context("cannot inspect certified-test execution image")?
        .len();
    let sha256 = hasher.finish_hex();
    if size != expected_size || sha256 != expected_sha256 {
        anyhow::bail!(
            "certified-test execution image changed (expected size={expected_size} sha256={expected_sha256}, observed size={size} sha256={sha256})"
        );
    }
    file.seek(std::io::SeekFrom::Start(0))
        .context("cannot rewind authenticated certified-test execution image")?;
    Ok(())
}

/// Derive the SHA-256 code-directory hash macOS exposes through
/// `csops(CS_OPS_CDHASH)` from the exact captured Mach-O bytes. Cargo test
/// executables are native thin x86-64/aarch64 images. Other formats fail
/// closed instead of guessing which fat slice dyld will select.
#[cfg(target_os = "macos")]
fn macho_sha256_cdhash(file: &mut File) -> CargoResult<String> {
    const LC_CODE_SIGNATURE: u32 = 0x1d;
    const CSMAGIC_EMBEDDED_SIGNATURE: u32 = 0xfade_0cc0;
    const CSMAGIC_CODEDIRECTORY: u32 = 0xfade_0c02;
    const MAX_LOAD_COMMAND_BYTES: usize = 16 * 1024 * 1024;
    const MAX_CODE_SIGNATURE_BYTES: usize = 32 * 1024 * 1024;

    let le_u32 = |bytes: &[u8]| -> Option<u32> {
        Some(u32::from_le_bytes(bytes.get(..4)?.try_into().ok()?))
    };
    let be_u32 = |bytes: &[u8]| -> Option<u32> {
        Some(u32::from_be_bytes(bytes.get(..4)?.try_into().ok()?))
    };

    file.seek(std::io::SeekFrom::Start(0))
        .context("cannot rewind Mach-O execution image")?;
    let mut header = [0_u8; 32];
    file.read_exact(&mut header)
        .context("certified-test image has a truncated Mach-O header")?;
    let header_size = match &header[..4] {
        // MH_MAGIC_64 / MH_MAGIC in little-endian file order.
        [0xcf, 0xfa, 0xed, 0xfe] => 32_usize,
        [0xce, 0xfa, 0xed, 0xfe] => 28_usize,
        _ => anyhow::bail!(
            "evidence-grade macOS execution requires a native thin little-endian Mach-O image"
        ),
    };
    let ncmds = le_u32(&header[16..20])
        .ok_or_else(|| anyhow::format_err!("Mach-O header has no load-command count"))?
        as usize;
    let sizeofcmds = le_u32(&header[20..24])
        .ok_or_else(|| anyhow::format_err!("Mach-O header has no load-command size"))?
        as usize;
    if ncmds > 4096 || sizeofcmds > MAX_LOAD_COMMAND_BYTES {
        anyhow::bail!("Mach-O load-command table exceeds the evidence-grade safety bound");
    }
    file.seek(std::io::SeekFrom::Start(header_size as u64))
        .context("cannot seek to Mach-O load commands")?;
    let mut commands = vec![0_u8; sizeofcmds];
    file.read_exact(&mut commands)
        .context("certified-test image has truncated Mach-O load commands")?;
    let mut cursor = 0_usize;
    let mut signature = None;
    for _ in 0..ncmds {
        let cmd = le_u32(commands.get(cursor..).unwrap_or_default())
            .ok_or_else(|| anyhow::format_err!("truncated Mach-O load command"))?;
        let cmdsize = le_u32(commands.get(cursor + 4..).unwrap_or_default())
            .ok_or_else(|| anyhow::format_err!("truncated Mach-O load-command size"))?
            as usize;
        if cmdsize < 8
            || cursor
                .checked_add(cmdsize)
                .is_none_or(|end| end > commands.len())
        {
            anyhow::bail!("malformed Mach-O load-command extent");
        }
        if cmd == LC_CODE_SIGNATURE {
            if cmdsize < 16 || signature.is_some() {
                anyhow::bail!("Mach-O image has a malformed or duplicate code-signature command");
            }
            let dataoff = le_u32(&commands[cursor + 8..cursor + 12]).unwrap() as u64;
            let datasize = le_u32(&commands[cursor + 12..cursor + 16]).unwrap() as usize;
            if datasize == 0 || datasize > MAX_CODE_SIGNATURE_BYTES {
                anyhow::bail!("Mach-O code signature exceeds the evidence-grade safety bound");
            }
            signature = Some((dataoff, datasize));
        }
        cursor += cmdsize;
    }
    if cursor != commands.len() {
        anyhow::bail!("Mach-O load-command byte count is not canonical");
    }
    let (dataoff, datasize) =
        signature.ok_or_else(|| anyhow::format_err!("Mach-O test image is not code-signed"))?;
    let image_size = file
        .metadata()
        .context("cannot inspect Mach-O test image")?
        .len();
    if dataoff
        .checked_add(datasize as u64)
        .is_none_or(|end| end > image_size)
    {
        anyhow::bail!("Mach-O code-signature extent is outside the execution image");
    }
    file.seek(std::io::SeekFrom::Start(dataoff))
        .context("cannot seek to Mach-O code signature")?;
    let mut superblob = vec![0_u8; datasize];
    file.read_exact(&mut superblob)
        .context("certified-test image has a truncated code signature")?;
    if be_u32(&superblob) != Some(CSMAGIC_EMBEDDED_SIGNATURE) {
        anyhow::bail!("Mach-O code signature is not an embedded signature superblob");
    }
    let blob_len = be_u32(&superblob[4..])
        .ok_or_else(|| anyhow::format_err!("truncated code-signature superblob"))?
        as usize;
    let count = be_u32(&superblob[8..])
        .ok_or_else(|| anyhow::format_err!("truncated code-signature index"))?
        as usize;
    if blob_len > superblob.len()
        || blob_len < 12
        || count > 128
        || 12_usize
            .checked_add(count.saturating_mul(8))
            .is_none_or(|end| end > blob_len)
    {
        anyhow::bail!("malformed code-signature superblob extent");
    }

    let mut candidates = Vec::new();
    for index in 0..count {
        let entry = 12 + index * 8;
        let offset = be_u32(&superblob[entry + 4..entry + 8]).unwrap() as usize;
        if offset.checked_add(8).is_none_or(|end| end > blob_len)
            || be_u32(&superblob[offset..]) != Some(CSMAGIC_CODEDIRECTORY)
        {
            continue;
        }
        let length = be_u32(&superblob[offset + 4..])
            .ok_or_else(|| anyhow::format_err!("truncated Mach-O code directory"))?
            as usize;
        if length < 44 || offset.checked_add(length).is_none_or(|end| end > blob_len) {
            anyhow::bail!("malformed Mach-O code-directory extent");
        }
        let hash_type = superblob[offset + 37];
        if matches!(hash_type, 2 | 3) {
            let mut hasher = Sha256::new();
            hasher.update(&superblob[offset..offset + length]);
            let digest = hasher.finish_hex();
            candidates.push(digest[..40].to_string());
        }
    }
    candidates.sort();
    candidates.dedup();
    match candidates.as_slice() {
        [only] => Ok(only.clone()),
        [] => anyhow::bail!("Mach-O image has no SHA-256 code directory"),
        _ => anyhow::bail!(
            "Mach-O image has multiple SHA-256 code directories; architecture selection is ambiguous"
        ),
    }
}

fn exact_regular_test_executable_identity(path: &Path) -> CargoResult<(String, u64)> {
    let before = fs::symlink_metadata(path)
        .with_context(|| format!("cannot inspect test executable `{}`", path.display()))?;
    if before.file_type().is_symlink() || !before.file_type().is_file() {
        anyhow::bail!(
            "test executable `{}` is not a regular non-symlink file",
            path.display()
        );
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt as _;

        if before.permissions().mode() & 0o111 == 0 {
            anyhow::bail!("test artifact `{}` is not executable", path.display());
        }
    }
    let file = File::open(path)
        .with_context(|| format!("cannot open test executable `{}`", path.display()))?;
    let opened = file
        .metadata()
        .with_context(|| format!("cannot inspect open test executable `{}`", path.display()))?;
    let mut hasher = Sha256::new();
    hasher
        .update_file(&file)
        .with_context(|| format!("cannot hash test executable `{}`", path.display()))?;
    let after = fs::symlink_metadata(path)
        .with_context(|| format!("cannot re-inspect test executable `{}`", path.display()))?;
    let stable = !after.file_type().is_symlink()
        && after.file_type().is_file()
        && before.len() == opened.len()
        && opened.len() == after.len()
        && before.modified().ok() == opened.modified().ok()
        && opened.modified().ok() == after.modified().ok();
    #[cfg(unix)]
    let stable = {
        use std::os::unix::fs::MetadataExt as _;

        stable
            && before.dev() == opened.dev()
            && opened.dev() == after.dev()
            && before.ino() == opened.ino()
            && opened.ino() == after.ino()
    };
    if !stable {
        anyhow::bail!(
            "test executable `{}` changed while its identity was checked",
            path.display()
        );
    }
    Ok((hasher.finish_hex(), opened.len()))
}

#[cfg(all(
    target_os = "linux",
    any(target_arch = "x86_64", target_arch = "aarch64")
))]
struct CertifiedTestExecveatPlan {
    fd: libc::c_int,
    // Own the strings whose addresses are stored in argv/envp for the forked
    // child. Boxed slices keep every CString allocation and pointer stable.
    _argv: Box<[std::ffi::CString]>,
    argv: Box<[usize]>,
    _env: Box<[std::ffi::CString]>,
    envp: Box<[usize]>,
}

#[cfg(all(
    target_os = "linux",
    any(target_arch = "x86_64", target_arch = "aarch64")
))]
impl CertifiedTestExecveatPlan {
    fn new(
        command: &std::process::Command,
        snapshot: &AuthenticatedExecutableSnapshot,
        argv0: Option<&std::ffi::OsStr>,
        environment: BTreeMap<OsString, OsString>,
    ) -> CargoResult<Self> {
        use std::os::unix::ffi::OsStrExt as _;

        let cstring = |value: &std::ffi::OsStr, what: &str| {
            std::ffi::CString::new(value.as_bytes()).map_err(|_| {
                anyhow::format_err!(
                    "certified-test {what} contains an interior NUL and cannot be authenticated"
                )
            })
        };

        let mut argv = Vec::new();
        argv.push(cstring(
            argv0.unwrap_or_else(|| command.get_program()),
            "argv[0]",
        )?);
        for argument in command.get_args() {
            argv.push(cstring(argument, "argument")?);
        }
        let argv = argv.into_boxed_slice();
        let argv_ptrs = argv
            .iter()
            .map(|argument| argument.as_ptr() as usize)
            .chain(std::iter::once(0))
            .collect::<Vec<_>>()
            .into_boxed_slice();

        // Trust: use the builder's complete environment, including its closed
        // prepared-plan snapshot and the selected owned jobserver overlay.
        // std::Command cannot expose env_clear, so reconstructing this from
        // ambient variables would silently change the authenticated plan.
        let mut env = Vec::with_capacity(environment.len());
        for (name, value) in environment {
            let mut entry = name;
            entry.push("=");
            entry.push(value);
            env.push(cstring(&entry, "environment entry")?);
        }
        let env = env.into_boxed_slice();
        let envp = env
            .iter()
            .map(|entry| entry.as_ptr() as usize)
            .chain(std::iter::once(0))
            .collect::<Vec<_>>()
            .into_boxed_slice();

        let fd = snapshot.fd();
        Ok(Self {
            fd,
            _argv: argv,
            argv: argv_ptrs,
            _env: env,
            envp,
        })
    }

    /// Enter the source-code execution boundary. This runs after fork and must
    /// remain allocation-free and async-signal-safe.
    fn exec(&self) -> std::io::Result<()> {
        let empty = b"\0";
        unsafe {
            libc::execveat(
                self.fd,
                empty.as_ptr().cast(),
                self.argv.as_ptr().cast(),
                self.envp.as_ptr().cast(),
                libc::AT_EMPTY_PATH,
            )
        };
        Err(std::io::Error::last_os_error())
    }
}

#[cfg(all(
    target_os = "linux",
    any(target_arch = "x86_64", target_arch = "aarch64")
))]
fn execute_authenticated_snapshot_with_cancel(
    snapshot: AuthenticatedExecutableSnapshot,
    command: &ProcessBuilder,
    poll_cancel: &mut dyn FnMut() -> bool,
) -> CargoResult<()> {
    let prepared = command.prepare_isolated_child()?;
    let mut std_command = command.build_command();
    // Trust: sealed-image execution retains the shared scheduler's group custody.
    std_command.process_group(0);
    let plan = CertifiedTestExecveatPlan::new(
        &std_command,
        &snapshot,
        command.get_arg0(),
        command.get_effective_envs()?,
    )?;
    unsafe {
        std_command.pre_exec(move || plan.exec());
    }
    if poll_cancel() {
        anyhow::bail!("authenticated test cancelled before launch");
    }
    prepared.check_cancelled()?;
    let child = std_command
        .spawn()
        .with_context(|| ProcessError::could_not_execute(command))?;
    // The forked child owns its descriptor copy. Dropping the parent copy here
    // prevents later code from accidentally treating it as ambient authority.
    drop(snapshot);
    // SAFETY: this newly spawned direct child is unreaped and is the isolated
    // group leader; the guard becomes its only wait owner.
    let child = unsafe { prepared.adopt_std(child) };
    let status = child
        .wait_with_cancel(poll_cancel)
        .with_context(|| format!("could not wait for certified test `{command}`"))?;
    if status.success() {
        Ok(())
    } else {
        Err(ProcessError::new(
            &format!("process didn't exit successfully: {command}"),
            Some(status),
            None,
        )
        .into())
    }
}

#[cfg(all(
    target_os = "linux",
    any(target_arch = "x86_64", target_arch = "aarch64")
))]
fn execute_authenticated_test_with_cancel(
    authority: &TestExecutionAuthority,
    path: &Path,
    command: &ProcessBuilder,
    poll_cancel: &mut dyn FnMut() -> bool,
) -> CargoResult<()> {
    execute_authenticated_test_with_cancel_and_scheduling(
        authority,
        path,
        command,
        poll_cancel,
        None,
    )
}

#[cfg(all(
    target_os = "macos",
    any(target_arch = "x86_64", target_arch = "aarch64")
))]
unsafe extern "C" {
    fn csops(
        pid: libc::pid_t,
        ops: libc::c_uint,
        useraddr: *mut libc::c_void,
        usersize: libc::size_t,
    ) -> libc::c_int;
    fn posix_spawn_file_actions_addinherit_np(
        actions: *mut libc::posix_spawn_file_actions_t,
        fd: libc::c_int,
    ) -> libc::c_int;
    fn posix_spawn_file_actions_addchdir_np(
        actions: *mut libc::posix_spawn_file_actions_t,
        path: *const libc::c_char,
    ) -> libc::c_int;
}

#[cfg(all(
    target_os = "macos",
    any(target_arch = "x86_64", target_arch = "aarch64")
))]
fn mac_live_process_cdhash(pid: libc::pid_t) -> CargoResult<String> {
    const CS_OPS_STATUS: libc::c_uint = 0;
    const CS_OPS_CDHASH: libc::c_uint = 5;
    const CS_VALID: u32 = 0x0000_0001;
    const CS_KILL: u32 = 0x0000_0200;

    let mut status = 0_u32;
    if unsafe {
        csops(
            pid,
            CS_OPS_STATUS,
            (&mut status as *mut u32).cast(),
            std::mem::size_of_val(&status),
        )
    } != 0
    {
        return Err(std::io::Error::last_os_error())
            .context("cannot authenticate suspended test process code-signing status");
    }
    if status & (CS_VALID | CS_KILL) != CS_VALID | CS_KILL {
        anyhow::bail!(
            "suspended test process lacks required valid + kill-on-invalid code-signing enforcement (status=0x{status:08x})"
        );
    }

    let mut cdhash = [0_u8; 20];
    if unsafe { csops(pid, CS_OPS_CDHASH, cdhash.as_mut_ptr().cast(), cdhash.len()) } != 0 {
        return Err(std::io::Error::last_os_error())
            .context("cannot authenticate suspended test process code-directory hash");
    }
    let mut rendered = String::with_capacity(cdhash.len() * 2);
    for byte in cdhash {
        write!(rendered, "{byte:02x}").unwrap();
    }
    Ok(rendered)
}

#[cfg(all(
    target_os = "macos",
    any(target_arch = "x86_64", target_arch = "aarch64")
))]
#[cfg(test)]
fn execute_authenticated_mac_snapshot_with_cancel(
    snapshot: AuthenticatedMacExecutableSnapshot,
    authorized_path: &Path,
    command: &ProcessBuilder,
    poll_cancel: &mut dyn FnMut() -> bool,
) -> CargoResult<()> {
    execute_authenticated_mac_snapshot_with_cancel_and_scheduling(
        snapshot,
        authorized_path,
        command,
        poll_cancel,
        None,
    )
}

// Trust: the optional scheduler consists of explicitly owned transport, not
// advertisements reconstructed from the authenticated command environment.
#[cfg(all(
    target_os = "macos",
    any(target_arch = "x86_64", target_arch = "aarch64")
))]
fn execute_authenticated_mac_snapshot_with_cancel_and_scheduling(
    mut snapshot: AuthenticatedMacExecutableSnapshot,
    authorized_path: &Path,
    command: &ProcessBuilder,
    poll_cancel: &mut dyn FnMut() -> bool,
    scheduling: Option<&auth_scheduling::OwnedSchedulingHandoff>,
) -> CargoResult<()> {
    use std::os::unix::ffi::OsStrExt as _;
    // Trust: prepare shared cancellation and nonreaping custody before spawn.
    let prepared = command.prepare_isolated_child()?;

    // A target runner/wrapper is another executable edge absent from the
    // phase-A manifest. The former Linux implementation silently replaced the
    // runner program with test bytes while retaining runner argv, which was
    // neither runner semantics nor a valid direct test invocation.
    let selected_program = PathBuf::from(command.get_program());
    let selected_program = selected_program.canonicalize().with_context(|| {
        format!(
            "cannot canonicalize authenticated test command program `{}`",
            selected_program.display()
        )
    })?;
    let authorized_path = authorized_path.canonicalize().with_context(|| {
        format!(
            "cannot canonicalize authorized test program `{}`",
            authorized_path.display()
        )
    })?;
    if selected_program != authorized_path {
        anyhow::bail!(
            "evidence-grade test execution refuses unauthenticated target runner `{}` for authorized test `{}`",
            selected_program.display(),
            authorized_path.display()
        );
    }

    let cstring = |value: &std::ffi::OsStr, what: &str| {
        std::ffi::CString::new(value.as_bytes()).map_err(|_| {
            anyhow::format_err!(
                "certified-test {what} contains an interior NUL and cannot be authenticated"
            )
        })
    };
    let spawn_path = cstring(snapshot.path.as_os_str(), "snapshot path")?;
    let mut argv = Vec::new();
    argv.push(cstring(
        command.get_arg0().unwrap_or(snapshot.path.as_os_str()),
        "argv[0]",
    )?);
    for argument in command.get_args() {
        argv.push(cstring(argument, "argument")?);
    }
    let mut argv_ptrs = argv
        .iter()
        .map(|argument| argument.as_ptr().cast_mut())
        .chain(std::iter::once(std::ptr::null_mut()))
        .collect::<Vec<_>>();

    let environment = command
        .get_effective_envs()
        .context("cannot materialize certified-test environment")?;
    let mut env = Vec::with_capacity(environment.len());
    for (name, value) in environment {
        let mut entry = name;
        entry.push("=");
        entry.push(value);
        env.push(cstring(&entry, "environment entry")?);
    }
    let mut env_ptrs = env
        .iter()
        .map(|entry| entry.as_ptr().cast_mut())
        .chain(std::iter::once(std::ptr::null_mut()))
        .collect::<Vec<_>>();

    authenticate_open_mac_snapshot(&mut snapshot.file, &snapshot.sha256, snapshot.size)?;
    if poll_cancel() {
        anyhow::bail!("authenticated test cancelled before launch");
    }
    prepared.check_cancelled()?;
    let mut actions: libc::posix_spawn_file_actions_t = std::ptr::null_mut();
    let actions_result = unsafe { libc::posix_spawn_file_actions_init(&mut actions) };
    if actions_result != 0 {
        return Err(std::io::Error::from_raw_os_error(actions_result))
            .context("cannot initialize certified-test spawn file actions");
    }
    let action_error = (|| -> CargoResult<()> {
        // POSIX_SPAWN_CLOEXEC_DEFAULT closes every descriptor unless a file
        // action explicitly retains it. Keep ordinary stdio and only the
        // selected owner's scheduling transport. Proof/control guards and
        // unrelated command descriptors never cross this edge.
        for fd in [libc::STDIN_FILENO, libc::STDOUT_FILENO, libc::STDERR_FILENO] {
            let result = unsafe { posix_spawn_file_actions_addinherit_np(&mut actions, fd) };
            if result != 0 {
                return Err(std::io::Error::from_raw_os_error(result))
                    .context("cannot retain certified-test stdio");
            }
        }
        if let Some(scheduling) = scheduling {
            for fd in scheduling.descriptors() {
                let result = unsafe { posix_spawn_file_actions_addinherit_np(&mut actions, fd) };
                if result != 0 {
                    return Err(std::io::Error::from_raw_os_error(result))
                        .context("cannot retain owned certified-test scheduling descriptor");
                }
            }
        }
        if let Some(cwd) = command.get_cwd() {
            let cwd = cstring(cwd.as_os_str(), "working directory")?;
            let result =
                unsafe { posix_spawn_file_actions_addchdir_np(&mut actions, cwd.as_ptr()) };
            if result != 0 {
                return Err(std::io::Error::from_raw_os_error(result)).with_context(|| {
                    format!(
                        "cannot bind certified-test working directory `{}`",
                        cwd.to_string_lossy()
                    )
                });
            }
        }
        Ok(())
    })();
    if let Err(error) = action_error {
        unsafe {
            libc::posix_spawn_file_actions_destroy(&mut actions);
        }
        return Err(error);
    }

    let mut attrs: libc::posix_spawnattr_t = std::ptr::null_mut();
    let attr_result = unsafe { libc::posix_spawnattr_init(&mut attrs) };
    if attr_result != 0 {
        unsafe {
            libc::posix_spawn_file_actions_destroy(&mut actions);
        }
        return Err(std::io::Error::from_raw_os_error(attr_result))
            .context("cannot initialize certified-test spawn attributes");
    }
    let flags = (libc::POSIX_SPAWN_START_SUSPENDED
        | libc::POSIX_SPAWN_CLOEXEC_DEFAULT
        | libc::POSIX_SPAWN_SETPGROUP) as libc::c_short;
    let flags_result = unsafe { libc::posix_spawnattr_setpgroup(&mut attrs, 0) };
    let flags_result = if flags_result == 0 {
        unsafe { libc::posix_spawnattr_setflags(&mut attrs, flags) }
    } else {
        flags_result
    };
    if flags_result != 0 {
        unsafe {
            libc::posix_spawnattr_destroy(&mut attrs);
            libc::posix_spawn_file_actions_destroy(&mut actions);
        }
        return Err(std::io::Error::from_raw_os_error(flags_result))
            .context("cannot require suspended certified-test launch");
    }

    let mut pid = 0;
    let spawn_result = unsafe {
        libc::posix_spawn(
            &mut pid,
            spawn_path.as_ptr(),
            &actions,
            &attrs,
            argv_ptrs.as_mut_ptr(),
            env_ptrs.as_mut_ptr(),
        )
    };
    unsafe {
        libc::posix_spawnattr_destroy(&mut attrs);
        libc::posix_spawn_file_actions_destroy(&mut actions);
    }
    if spawn_result != 0 {
        return Err(std::io::Error::from_raw_os_error(spawn_result))
            .with_context(|| ProcessError::could_not_execute(command));
    }

    // SAFETY: successful posix_spawn returned this sole unreaped direct child;
    // POSIX_SPAWN_SETPGROUP with pgroup=0 made it its own group leader. Adopt
    // immediately so every authorization/error/unwind path retains cleanup.
    let child = unsafe { prepared.adopt(pid) };
    let authorization = (|| -> CargoResult<()> {
        let live_cdhash = mac_live_process_cdhash(pid)?;
        if live_cdhash != snapshot.cdhash {
            anyhow::bail!(
                "suspended test process code identity differs from the authenticated image (expected CDHash={}, observed CDHash={live_cdhash})",
                snapshot.cdhash
            );
        }
        authenticate_open_mac_snapshot(&mut snapshot.file, &snapshot.sha256, snapshot.size)?;
        if poll_cancel() {
            anyhow::bail!("authenticated test cancelled before resume");
        }
        child.check_cancelled()?;
        Ok(())
    })();
    if let Err(error) = authorization {
        return match child.cancel_and_wait() {
            Ok(_) => Err(error),
            Err(cleanup) => Err(error.context(format!("authenticated test cleanup: {cleanup}"))),
        };
    }
    if unsafe { libc::kill(pid, libc::SIGCONT) } != 0 {
        let error = std::io::Error::last_os_error();
        return match child.cancel_and_wait() {
            Ok(_) => Err(error).context("cannot resume authenticated certified-test process"),
            Err(cleanup) => Err(error).context(format!(
                "cannot resume authenticated certified-test process; cleanup: {cleanup}"
            )),
        };
    }
    let status = child
        .wait_with_cancel(poll_cancel)
        .context("could not wait for authenticated certified test")?;
    authenticate_open_mac_snapshot(&mut snapshot.file, &snapshot.sha256, snapshot.size)?;
    if status.success() {
        Ok(())
    } else {
        Err(ProcessError::new(
            &format!("process didn't exit successfully: {command}"),
            Some(status),
            None,
        )
        .into())
    }
}

#[cfg(all(
    target_os = "macos",
    any(target_arch = "x86_64", target_arch = "aarch64")
))]
fn execute_authenticated_test_with_cancel(
    authority: &TestExecutionAuthority,
    path: &Path,
    command: &ProcessBuilder,
    poll_cancel: &mut dyn FnMut() -> bool,
) -> CargoResult<()> {
    execute_authenticated_test_with_cancel_and_scheduling(
        authority,
        path,
        command,
        poll_cancel,
        None,
    )
}

/// Trust: authenticate exactly the selected image while retaining only the
/// actual native scheduler's explicitly owned transport. Legacy prepared
/// execution passes `None` and remains scheduler-free.
#[cfg(any(target_os = "linux", target_os = "macos"))]
fn execute_authenticated_test_with_cancel_and_scheduling(
    authority: &TestExecutionAuthority,
    path: &Path,
    command: &ProcessBuilder,
    poll_cancel: &mut dyn FnMut() -> bool,
    scheduling: Option<&auth_scheduling::OwnedSchedulingHandoff>,
) -> CargoResult<()> {
    let command = auth_scheduling::authenticated_command(command, scheduling)?;
    #[cfg(all(
        target_os = "linux",
        any(target_arch = "x86_64", target_arch = "aarch64")
    ))]
    {
        let snapshot = authority.executable_snapshot(path)?;
        execute_authenticated_snapshot_with_cancel(snapshot, &command, poll_cancel)
    }
    #[cfg(all(
        target_os = "macos",
        any(target_arch = "x86_64", target_arch = "aarch64")
    ))]
    {
        let snapshot = authority.mac_executable_snapshot(path)?;
        execute_authenticated_mac_snapshot_with_cancel_and_scheduling(
            snapshot,
            path,
            &command,
            poll_cancel,
            scheduling,
        )
    }
    #[cfg(not(any(
        all(
            target_os = "linux",
            any(target_arch = "x86_64", target_arch = "aarch64")
        ),
        all(
            target_os = "macos",
            any(target_arch = "x86_64", target_arch = "aarch64")
        )
    )))]
    {
        let _ = (authority, command, poll_cancel, scheduling);
        anyhow::bail!(
            "evidence-grade test execution for `{}` requires Linux sealed-memfd execveat or macOS suspended CDHash-authenticated execution on x86-64/aarch64",
            path.display()
        )
    }
}

#[cfg(not(any(
    all(
        target_os = "linux",
        any(target_arch = "x86_64", target_arch = "aarch64")
    ),
    all(
        target_os = "macos",
        any(target_arch = "x86_64", target_arch = "aarch64")
    )
)))]
fn execute_authenticated_test_with_cancel(
    _authority: &TestExecutionAuthority,
    path: &Path,
    _command: &ProcessBuilder,
    _poll_cancel: &mut dyn FnMut() -> bool,
) -> CargoResult<()> {
    anyhow::bail!(
        "evidence-grade test execution for `{}` requires Linux sealed-memfd execveat or macOS suspended CDHash-authenticated execution on x86-64/aarch64",
        path.display()
    )
}

#[cfg(all(
    test,
    target_os = "linux",
    any(target_arch = "x86_64", target_arch = "aarch64")
))]
fn execute_authenticated_snapshot(
    snapshot: AuthenticatedExecutableSnapshot,
    command: &ProcessBuilder,
) -> CargoResult<()> {
    execute_authenticated_snapshot_with_cancel(snapshot, command, &mut || false)
}

#[cfg(all(
    test,
    target_os = "macos",
    any(target_arch = "x86_64", target_arch = "aarch64")
))]
fn execute_authenticated_mac_snapshot(
    snapshot: AuthenticatedMacExecutableSnapshot,
    path: &Path,
    command: &ProcessBuilder,
) -> CargoResult<()> {
    execute_authenticated_mac_snapshot_with_cancel(snapshot, path, command, &mut || false)
}

#[cfg(test)]
fn execute_authenticated_test(
    authority: &TestExecutionAuthority,
    path: &Path,
    command: &ProcessBuilder,
) -> CargoResult<()> {
    execute_authenticated_test_with_cancel(authority, path, command, &mut || false)
}

fn test_execution_authority_inputs(
    session: Option<OsString>,
    manifest_path: Option<OsString>,
    manifest_sha256: Option<OsString>,
) -> CargoResult<Option<(OsString, OsString, OsString)>> {
    match (session, manifest_path, manifest_sha256) {
        (None, None, None) => Ok(None),
        (Some(session), Some(manifest_path), Some(manifest_sha256)) => {
            Ok(Some((session, manifest_path, manifest_sha256)))
        }
        _ => anyhow::bail!(
            "{TRUST_TARGO_PREPARED_TEST_SESSION}, {TRUST_TARGO_TEST_EXECUTION_MANIFEST}, and {TRUST_TARGO_TEST_EXECUTION_MANIFEST_SHA256} must be supplied together"
        ),
    }
}

fn canonical_sha256_hex(value: &str) -> bool {
    value.len() == 64
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

/// Read and authenticate the authority through one handle before parsing it.
///
/// The expected digest is a private value installed directly by outer Targo.
/// Reading first into a bounded buffer means a pathname replacement can at
/// most make this check fail; it cannot substitute the digest inventory used
/// to select the later sealed execution image.
fn read_test_execution_authority_manifest(
    manifest_path: &Path,
    expected_sha256: &str,
) -> CargoResult<TestExecutionAuthorityManifest> {
    if !canonical_sha256_hex(expected_sha256) {
        anyhow::bail!(
            "{TRUST_TARGO_TEST_EXECUTION_MANIFEST_SHA256} is not a canonical SHA-256 digest"
        );
    }

    let mut options = fs::OpenOptions::new();
    options.read(true);
    #[cfg(target_os = "linux")]
    {
        use std::os::unix::fs::OpenOptionsExt as _;

        options.custom_flags(libc::O_CLOEXEC | libc::O_NOFOLLOW);
    }
    let file = options.open(manifest_path).with_context(|| {
        format!(
            "cannot open test execution authority `{}`",
            manifest_path.display()
        )
    })?;
    let metadata = file.metadata().with_context(|| {
        format!(
            "cannot inspect open test execution authority `{}`",
            manifest_path.display()
        )
    })?;
    if !metadata.file_type().is_file() {
        anyhow::bail!("test execution authority must open as a regular file");
    }
    if metadata.len() > MAX_TEST_EXECUTION_AUTHORITY_BYTES {
        anyhow::bail!(
            "test execution authority exceeds the {MAX_TEST_EXECUTION_AUTHORITY_BYTES}-byte safety limit"
        );
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt as _;

        if metadata.permissions().mode() & 0o077 != 0 {
            anyhow::bail!("test execution authority is not private");
        }
    }

    let mut bytes = Vec::with_capacity(metadata.len() as usize);
    file.take(MAX_TEST_EXECUTION_AUTHORITY_BYTES + 1)
        .read_to_end(&mut bytes)
        .with_context(|| {
            format!(
                "cannot read test execution authority `{}`",
                manifest_path.display()
            )
        })?;
    if bytes.len() as u64 > MAX_TEST_EXECUTION_AUTHORITY_BYTES {
        anyhow::bail!(
            "test execution authority exceeds the {MAX_TEST_EXECUTION_AUTHORITY_BYTES}-byte safety limit"
        );
    }
    let mut hasher = Sha256::new();
    hasher.update(&bytes);
    let observed_sha256 = hasher.finish_hex();
    if observed_sha256 != expected_sha256 {
        anyhow::bail!(
            "test execution authority digest does not match outer Targo (expected {expected_sha256}, observed {observed_sha256})"
        );
    }
    serde_json::from_slice(&bytes).context("cannot parse authenticated test execution authority")
}

fn load_test_execution_authority(
    gctx: &GlobalContext,
) -> CargoResult<Option<TestExecutionAuthority>> {
    let session = gctx
        .get_env_os(TRUST_TARGO_PREPARED_TEST_SESSION)
        .map(ToOwned::to_owned);
    let manifest_path = gctx
        .get_env_os(TRUST_TARGO_TEST_EXECUTION_MANIFEST)
        .map(ToOwned::to_owned);
    let manifest_sha256 = gctx
        .get_env_os(TRUST_TARGO_TEST_EXECUTION_MANIFEST_SHA256)
        .map(ToOwned::to_owned);
    let Some((session, manifest_path, manifest_sha256)) =
        test_execution_authority_inputs(session, manifest_path, manifest_sha256)?
    else {
        return Ok(None);
    };
    let session = session
        .to_str()
        .ok_or_else(|| anyhow::anyhow!("verified test session is not Unicode"))?;
    let digest = manifest_sha256
        .to_str()
        .ok_or_else(|| anyhow::anyhow!("test authority digest is not Unicode"))?;
    load_test_execution_authority_from_inputs(session, Path::new(&manifest_path), digest).map(Some)
}

// The retained queue consumes opaque grant inputs directly. Both callers use
// this exact validator; an environment marker never creates a retained grant.
fn load_test_execution_authority_from_inputs(
    session: &str,
    manifest_path: &Path,
    manifest_sha256: &str,
) -> CargoResult<TestExecutionAuthority> {
    if !cfg!(any(
        all(
            target_os = "linux",
            any(target_arch = "x86_64", target_arch = "aarch64")
        ),
        all(
            target_os = "macos",
            any(target_arch = "x86_64", target_arch = "aarch64")
        )
    )) {
        anyhow::bail!(
            "evidence-grade Cargo test execution requires Linux sealed-memfd execveat or macOS suspended CDHash-authenticated execution on x86-64/aarch64; this platform has no implemented authenticated launch backend"
        );
    }
    if !manifest_path.is_absolute() {
        anyhow::bail!("test execution authority path must be absolute");
    }
    let manifest = read_test_execution_authority_manifest(&manifest_path, manifest_sha256)?;
    if manifest.schema != TEST_EXECUTION_AUTHORITY_SCHEMA {
        anyhow::bail!(
            "unsupported test execution authority schema `{}`",
            manifest.schema
        );
    }
    if manifest.verification_session != session {
        anyhow::bail!("test execution authority does not match the verified Cargo session");
    }
    if manifest.executables.is_empty()
        || manifest.executables.len() > MAX_TEST_EXECUTION_AUTHORITY_ENTRIES
    {
        anyhow::bail!("test execution authority has an invalid executable inventory size");
    }
    let target_directory = PathBuf::from(&manifest.target_directory);
    if !target_directory.is_absolute() {
        anyhow::bail!("authorized Cargo target directory must be absolute");
    }
    let target_metadata = fs::symlink_metadata(&target_directory).with_context(|| {
        format!(
            "cannot inspect authorized target directory `{}`",
            target_directory.display()
        )
    })?;
    if target_metadata.file_type().is_symlink() || !target_metadata.is_dir() {
        anyhow::bail!("authorized Cargo target directory must be a non-symlink directory");
    }
    let target_directory = target_directory.canonicalize().with_context(|| {
        format!(
            "cannot canonicalize authorized target directory `{}`",
            target_directory.display()
        )
    })?;
    let mut executables = BTreeMap::new();
    for entry in manifest.executables {
        if entry.target.is_empty()
            || entry.sha256.len() != 64
            || !entry
                .sha256
                .bytes()
                .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
        {
            anyhow::bail!("test execution authority contains malformed target or SHA-256 identity");
        }
        let path = PathBuf::from(&entry.path);
        if !path.is_absolute() {
            anyhow::bail!("authorized test executable path must be absolute");
        }
        let metadata = fs::symlink_metadata(&path).with_context(|| {
            format!(
                "cannot inspect authorized test executable `{}`",
                path.display()
            )
        })?;
        if metadata.file_type().is_symlink() || !metadata.file_type().is_file() {
            anyhow::bail!("authorized test executable must be a regular non-symlink file");
        }
        let canonical = path.canonicalize().with_context(|| {
            format!(
                "cannot canonicalize authorized test executable `{}`",
                path.display()
            )
        })?;
        if !canonical.starts_with(&target_directory) {
            anyhow::bail!(
                "authorized test executable `{}` escapes target directory `{}`",
                canonical.display(),
                target_directory.display()
            );
        }
        if executables.insert(canonical.clone(), entry).is_some() {
            anyhow::bail!(
                "duplicate authorized test executable `{}`",
                canonical.display()
            );
        }
    }

    let authorized_inventory = executables.keys().cloned().collect::<BTreeSet<_>>();
    let authority = TestExecutionAuthority {
        executables,
        prepared: manifest.prepared,
    };
    if let Some(plan) = &authority.prepared {
        if Path::new(&plan.target_directory) != target_directory {
            anyhow::bail!("prepared test plan differs from the authorized target directory");
        }
        let expected = authority
            .executables
            .iter()
            .map(|(path, entry)| {
                (
                    path.to_string_lossy().into_owned(),
                    (entry.sha256.clone(), entry.size),
                )
            })
            .collect();
        plan.validate(session, &expected)
            .map_err(anyhow::Error::msg)?;
    }
    for path in &authorized_inventory {
        authority.validate_executable(path)?;
    }
    Ok(authority)
}

fn reject_unharnessed_certified_test_target(
    execution_authority_loaded: bool,
    harness: bool,
    target: &str,
) -> CargoResult<()> {
    if execution_authority_loaded && !harness {
        anyhow::bail!(
            "evidence-grade Cargo test execution rejects target `{target}` with `harness = false`: arbitrary target `main` is outside the certified test-harness boundary"
        );
    }
    Ok(())
}

fn reject_unbound_test_loader_env<K>(
    script_metas: Option<&[K]>,
    extra_env: &HashMap<K, Vec<(String, String)>>,
) -> CargoResult<()>
where
    K: Eq + Hash,
{
    for script_meta in script_metas.into_iter().flatten() {
        let Some(env) = extra_env.get(script_meta) else {
            continue;
        };
        if let Some((name, _)) = env.iter().find(|(name, _)| {
            let name = name.to_ascii_uppercase();
            name.starts_with("LD_")
                || name.starts_with("DYLD_")
                || matches!(
                    name.as_str(),
                    "LIBPATH" | "SHLIB_PATH" | "LDR_PRELOAD" | "PATH"
                )
        }) {
            anyhow::bail!(
                "build-script test environment `{name}` can alter executable loading and is not authenticated by the phase-A artifact manifest"
            );
        }
    }
    Ok(())
}

fn reject_unbound_test_native_dirs(native_dirs: &BTreeSet<PathBuf>) -> CargoResult<()> {
    if native_dirs.is_empty() {
        return Ok(());
    }
    let rendered = native_dirs
        .iter()
        .map(|path| path.display().to_string())
        .collect::<Vec<_>>()
        .join(", ");
    anyhow::bail!(
        "evidence-grade Cargo test execution does not yet authenticate build-script native-library directories: {rendered}"
    );
}

/// Test binaries consume verification results but are not proof-control
/// processes. Remove inherited and late build-script/config authority after
/// `target_process` has applied every environment source.
#[allow(clippy::disallowed_methods)]
fn strip_test_execution_authority_env(command: &mut ProcessBuilder) {
    // Test code receives no build-scheduler capability. This also keeps the
    // macOS authenticated `posix_spawn` lane honest: it closes every non-stdio
    // descriptor, so retaining jobserver environment that names those fds
    // would be a stale and forgeable capability claim.
    command.clear_jobserver();
    let names = env::vars_os()
        .filter_map(|(name, _)| name.into_string().ok())
        .chain(command.get_envs().keys().cloned())
        .filter(|name| {
            name.starts_with("TRUST_")
                || name.starts_with("TRUSTD_")
                || name.to_ascii_uppercase().starts_with("LD_")
                || name.to_ascii_uppercase().starts_with("DYLD_")
                || matches!(
                    name.to_ascii_uppercase().as_str(),
                    "LIBPATH" | "SHLIB_PATH" | "LDR_PRELOAD"
                )
                || matches!(
                    name.as_str(),
                    "RUSTFLAGS"
                        | "RUSTDOCFLAGS"
                        | "CARGO_ENCODED_RUSTFLAGS"
                        | "CARGO_ENCODED_RUSTDOCFLAGS"
                        | "CARGO_BUILD_RUSTFLAGS"
                        | "CARGO_BUILD_RUSTDOCFLAGS"
                        | "RUSTC"
                        | "RUSTDOC"
                        | "RUSTC_WRAPPER"
                        | "RUSTC_WORKSPACE_WRAPPER"
                        | "CARGO_BUILD_RUSTC"
                        | "CARGO_BUILD_RUSTDOC"
                        | "CARGO_BUILD_RUSTC_WRAPPER"
                        | "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER"
                        | "CARGO_MAKEFLAGS"
                        | "MAKEFLAGS"
                        | "MFLAGS"
                )
        })
        .collect::<BTreeSet<_>>();
    for name in names {
        command.env_remove(&name);
    }
    // An unset macOS fallback path has a user-writable default (`$HOME/lib`
    // and `/usr/local/lib`). Install a fixed system-only fallback after
    // deleting every inherited/target_process DYLD channel.
    #[cfg(target_os = "macos")]
    command.env(
        "DYLD_FALLBACK_LIBRARY_PATH",
        "/usr/lib:/System/Library/Frameworks",
    );
    #[cfg(target_os = "macos")]
    command.env("DYLD_FALLBACK_FRAMEWORK_PATH", "/System/Library/Frameworks");
}

/// The kind of test.
///
/// This is needed because `Unit` does not track whether or not something is a
/// benchmark.
#[derive(Copy, Clone)]
enum TestKind {
    Test,
    Bench,
    Doctest,
}

/// A unit that failed to run.
struct UnitTestError {
    unit: Unit,
    kind: TestKind,
    // Trust: the arguments that rerun this action when the unit's own
    // package and target flags would not: a test plan's request, or the
    // command of a `[[workspace]]` phase.
    rerun: Option<plan::Rerun>,
}

impl UnitTestError {
    // Trust: a plan's rerun arguments name a request, which may cover many
    // targets; this names the one that failed.
    fn plan_target(&self) -> Option<String> {
        self.rerun.as_ref().map(|_| {
            format!(
                "{} of `{}`",
                self.unit.target.description_named(),
                self.unit.pkg.name()
            )
        })
    }

    /// Returns the CLI args needed to target this unit.
    fn cli_args(&self, ws: &Workspace<'_>, opts: &ops::CompileOptions) -> String {
        // Trust: see `rerun`.
        match &self.rerun {
            Some(plan::Rerun::Arguments(rerun) | plan::Rerun::Command(rerun)) => {
                return rerun.clone();
            }
            None => {}
        }
        let mut args = if opts.spec.needs_spec_flag(ws) {
            format!("-p {} ", self.unit.pkg.name())
        } else {
            String::new()
        };
        let mut add = |which| write!(args, "--{which} {}", self.unit.target.name()).unwrap();

        match self.kind {
            TestKind::Test | TestKind::Bench => match self.unit.target.kind() {
                TargetKind::Lib(_) => args.push_str("--lib"),
                TargetKind::Bin => add("bin"),
                TargetKind::Test => add("test"),
                TargetKind::Bench => add("bench"),
                TargetKind::ExampleLib(_) | TargetKind::ExampleBin => add("example"),
                TargetKind::CustomBuild => panic!("unexpected CustomBuild kind"),
            },
            TestKind::Doctest => args.push_str("--doc"),
        }
        args
    }
}

/// Compiles and runs tests.
///
/// On error, the returned [`CliError`] will have the appropriate process exit
/// code that Cargo should use.
pub fn run_tests(ws: &Workspace<'_>, options: &TestOptions, test_args: &[&str]) -> CliResult {
    if try_run_prepared_tests(ws.gctx())? {
        return Ok(());
    }
    if crate::trust_verified_targo() && !options.no_run {
        return Err(anyhow::anyhow!(
            "verified tests require the current prepared execution authority"
        )
        .into());
    }

    if ws.gctx().build_config()?.test_jobs == Some(0) {
        return Err(anyhow::anyhow!("build.test-jobs must be positive").into());
    }
    if options.no_run && !options.required_test_bins.is_empty() {
        return Err(anyhow::anyhow!("--require-test-bin cannot be combined with --no-run").into());
    }
    // Trust: a plan is refused while it asks for something this invocation
    // would not do.
    plan::require_honored(ws, options, test_args)?;
    // Trust: what refuses a plan's run before anything is built judged
    // nothing (`plan_outcome`).
    let planned = options.compile_opts.build_config.test_plan.is_some();
    let route = graph::request(ws, options, test_args).map_err(|error| {
        if planned {
            plan_outcome::cannot_judge(error)
        } else {
            error
        }
    })?;
    let mut compilation = match route {
        graph::TestRoute::Graph(request) => {
            let mut compilation = ops::cargo_compile::compile_with_test_execution(
                ws,
                &options.compile_opts,
                request,
            )?;
            compilation.tests.sort_by_key(|output| output.unit.clone());
            compilation
        }
        graph::TestRoute::Sequential(policy) => {
            let compilation = compile_tests(ws, options)?;
            // Trust: an entry for a tested package outside the workspace is
            // checked here as on the graph route, before any test body; this
            // route applies none of the policy, so other entries go unremarked.
            policy.check_selected(
                ws.gctx(),
                compilation.tests.iter().map(|test| &test.unit.pkg).chain(
                    compilation
                        .to_doc_test
                        .iter()
                        .map(|doctest| &doctest.unit.pkg),
                ),
                harness_policy::Unselected::Ignore,
            )?;
            compilation
        }
    };
    require_test_bin_inventory(&compilation, &options.required_test_bins)?;

    // Trust: diagnostic graph/dry-run requests do not execute predicted paths.
    if options.compile_opts.build_config.dry_run || options.compile_opts.build_config.unit_graph {
        return Ok(());
    }

    if options.no_run && !ws.gctx().has_retained_test() {
        prepared::export(ws, options, test_args, &compilation)?;
        if !options.compile_opts.build_config.emit_json() {
            display_no_run_information(ws, test_args, &compilation, "unittests")?;
        }
        return Ok(());
    }
    if ws.gctx().has_retained_test() && compilation.test_execution.is_none() {
        return Err(anyhow::anyhow!(
            "retained verified tests did not execute through their original queue"
        )
        .into());
    }
    let mut errors = if let Some(execution) = compilation.test_execution.take() {
        // Trust: each action carries its own arguments.
        graph::consume(ws, options, execution)?
    } else {
        run_unit_tests(ws, options, test_args, &compilation, TestKind::Test)?
    };

    if ws.gctx().has_retained_test() {
        // Retained compilation keeps default doctest inventory/census data,
        // but its execution actions are ordinary Test units only. Do not run
        // the legacy rustdoc process after that queue's owned admission ends.
        return no_fail_fast_err(ws, &options.compile_opts, &errors);
    }
    let doctest_errors = run_doc_tests(ws, options, test_args, &compilation)?;
    errors.extend(doctest_errors);
    no_fail_fast_err(ws, &options.compile_opts, &errors)
}

/// Trust: require the actual resolved execution inventory, rather than a manifest
/// label or a success line printed by a different harness. Default target
/// selection may omit missing, disabled, or feature-ineligible binaries.
fn require_test_bin_inventory(
    compilation: &Compilation<'_>,
    required: &[String],
) -> CargoResult<()> {
    if !required.is_empty() && !cfg!(any(target_os = "linux", target_os = "macos")) {
        anyhow::bail!("--require-test-bin currently requires Linux or macOS process supervision");
    }
    let mut seen = BTreeSet::new();
    for name in required {
        if !seen.insert(name) {
            anyhow::bail!("required test binary `{name}` was requested more than once");
        }
        let units = compilation
            .tests
            .iter()
            .filter(|item| {
                matches!(item.unit.target.kind(), TargetKind::Bin)
                    && item.unit.target.name() == name
            })
            .collect::<Vec<_>>();
        if units.len() != 1 {
            anyhow::bail!(
                "required test binary `{name}` must occur exactly once in the resolved test execution inventory (found {})",
                units.len()
            );
        }
        let unit = &units[0].unit;
        if !unit.target.harness() {
            anyhow::bail!("required test binary `{name}` must use the Rust test harness");
        }
        if compilation.target_runner(unit.kind).is_some() {
            anyhow::bail!("required test binary `{name}` does not support a custom target runner");
        }
    }
    Ok(())
}

// Trust: a nonempty result belongs to its required harness, never another target.
#[derive(Default)]
struct RequiredTestSummary {
    passed: Option<u64>,
    failed: bool,
    // Trust: what a test plan reads besides (plan_judge.rs): the run the
    // harness announced, its last closing line, and the result lines of the
    // tests the plan watches.
    plan: plan_judge::Reading,
}

impl RequiredTestSummary {
    // Trust: also records the result lines of each of `names`.
    fn watching(names: &[String]) -> Self {
        Self {
            plan: plan_judge::Reading::watching(names),
            ..Self::default()
        }
    }

    fn observe_stdout(&mut self, line: &str) {
        if let Some(summary) = line.strip_prefix("test result: ok. ") {
            // Accept the complete plain libtest summary, once. A truncated
            // prefix or a later positive line cannot overwrite a failed or
            // empty result. This is test reporting, not authenticated proof
            // of arbitrary test code's behavior.
            if self.passed.is_some() {
                self.failed = true;
            }
            // Trust: an `ok` line that counts a failure contradicts itself
            // (`Closing::new`); the plan's reading keeps all its numbers.
            let closing = plan_judge::Closing::new(true, Self::parse_summary(summary));
            self.passed = closing.counts.map(|counts| counts.passed);
            if self.passed.is_none() {
                self.failed = true;
            }
            self.plan.close(closing);
        // Trust: a plan reads the failed closing line and every other line.
        } else if let Some(summary) = line.strip_prefix("test result: FAILED. ") {
            self.plan.close(plan_judge::Closing::new(
                false,
                Self::parse_summary(summary),
            ));
        } else {
            self.plan.line(line);
        }
        self.observe_failure(line);
    }

    // Trust: all four counts and `measured`, for a plan's reading.
    fn parse_summary(mut summary: &str) -> Option<(TestCounts, u64)> {
        fn count<'a>(text: &mut &'a str, suffix: &str) -> Option<u64> {
            let (number, rest) = text.split_once(suffix)?;
            if number.is_empty() || !number.bytes().all(|b| b.is_ascii_digit()) {
                return None;
            }
            *text = rest;
            number.parse().ok()
        }
        let passed = count(&mut summary, " passed; ")?;
        let failed = count(&mut summary, " failed; ")?;
        let ignored = count(&mut summary, " ignored; ")?;
        let measured = count(&mut summary, " measured; ")?;
        let (filtered, elapsed) = summary
            .split_once("; finished in ")
            .map_or((summary, None), |(filtered, elapsed)| {
                (filtered, Some(elapsed))
            });
        let filtered = filtered.strip_suffix(" filtered out")?;
        if filtered.is_empty() || !filtered.bytes().all(|b| b.is_ascii_digit()) {
            return None;
        }
        let filtered_out = filtered.parse::<u64>().ok()?;
        if let Some(elapsed) = elapsed {
            let seconds = elapsed.strip_suffix('s')?.parse::<f64>().ok()?;
            if !seconds.is_finite() || seconds < 0.0 {
                return None;
            }
        }
        Some((
            TestCounts {
                passed,
                failed,
                ignored,
                filtered_out,
            },
            measured,
        ))
    }

    fn observe_failure(&mut self, line: &str) {
        if line.starts_with("test result: FAILED.") || line.trim_start().starts_with("SKIPPED:") {
            self.failed = true;
        }
    }

    /// Judge a harness that exited successfully: the record keeps its exit.
    // Trust: `who` requires the result: a required test binary, or a test
    // plan's instrument.
    fn finish(&self, who: &str) -> CargoResult<()> {
        if self.failed || !self.passed.is_some_and(|passed| passed > 0) {
            return Err(graph::JudgedAfterExit {
                exit_code: 0,
                reason: format!("{who} reported no passing tests"),
            }
            .into());
        }
        Ok(())
    }
}

/// Trust: capture only the judged harness's own execution, so another target's
/// nonempty summary cannot satisfy its obligation. Output remains visible.
/// `who` requires the harness to report a passing test, if anyone does; a
/// test plan's action leaves what the harness reported in `watch`, which
/// holds a successful exit to the harness's closing line.
fn execute_judged(
    command: &ProcessBuilder,
    who: Option<&str>,
    watch: Option<&plan_judge::Watch>,
    sink: graph::OutputSink,
) -> CargoResult<()> {
    use crate::util::machine_message::TestOutputStream;
    use std::cell::RefCell;

    let summary = RefCell::new(RequiredTestSummary::watching(
        watch.map_or(&[], plan_judge::Watch::names),
    ));
    let exit = command.exec_with_streaming_limits(
        &mut |line| {
            // Trust: a line on either stream is progress (`plan_clock`).
            if let Some(watch) = watch {
                watch.progress().touch();
            }
            summary.borrow_mut().observe_stdout(line);
            sink.write(TestOutputStream::Stdout, line)
        },
        &mut |line| {
            if let Some(watch) = watch {
                watch.progress().touch();
            }
            // libtest's result belongs to stdout. Stderr can report failure,
            // but cannot supply or replace a positive harness result.
            summary.borrow_mut().observe_failure(line);
            sink.write(TestOutputStream::Stderr, line)
        },
        false,
        graph::harness_output_limits(),
    );
    let summary = summary.into_inner();
    // A failed exit is recorded with what the harness reported before it.
    let disagreement = watch.and_then(|watch| watch.conclude(&exit, &summary.plan));
    // Streaming execution returns only after a successful exit; a failing
    // one is its `ProcessError` here.
    exit?;
    if let Some(reason) = disagreement {
        return Err(graph::JudgedAfterExit {
            exit_code: 0,
            reason,
        }
        .into());
    }
    who.map_or(Ok(()), |who| summary.finish(who))
}

/// Compiles and runs benchmarks.
///
/// On error, the returned [`CliError`] will have the appropriate process exit
/// code that Cargo should use.
pub fn run_benches(ws: &Workspace<'_>, options: &TestOptions, args: &[&str]) -> CliResult {
    let compilation = compile_tests(ws, options)?;

    if options.no_run {
        if !options.compile_opts.build_config.emit_json() {
            display_no_run_information(ws, args, &compilation, "benches")?;
        }
        return Ok(());
    }

    let mut args = args.to_vec();
    args.push("--bench");

    let errors = run_unit_tests(ws, options, &args, &compilation, TestKind::Bench)?;
    no_fail_fast_err(ws, &options.compile_opts, &errors)
}

fn compile_tests<'a>(ws: &Workspace<'a>, options: &TestOptions) -> CargoResult<Compilation<'a>> {
    let mut compilation = ops::compile(ws, &options.compile_opts)?;
    compilation.tests.sort_by_key(|u| u.unit.clone());
    Ok(compilation)
}

/// Runs the unit and integration tests of a package.
///
/// Returns a `Vec` of tests that failed when `--no-fail-fast` is used.
/// If `--no-fail-fast` is *not* used, then this returns an `Err`.
fn run_unit_tests(
    ws: &Workspace<'_>,
    options: &TestOptions,
    test_args: &[&str],
    compilation: &Compilation<'_>,
    test_kind: TestKind,
) -> Result<Vec<UnitTestError>, CliError> {
    let gctx = ws.gctx();
    let cwd = gctx.cwd();
    let mut errors = Vec::new();

    // Trust: only ordinary native Rust harnesses participate in this cooperative
    // policy. Prepared/authenticated commands, benches and custom runners retain
    // their existing execution boundary and arguments.
    let worker_budget = if matches!(test_kind, TestKind::Test)
        && compilation.tests.iter().any(|output| {
            output.unit.target.harness() && compilation.target_runner(output.unit.kind).is_none()
        }) {
        worker_budget::WorkerBudget::native(gctx)?
    } else {
        None
    };
    for UnitOutput {
        unit,
        path,
        script_metas,
        env,
    } in compilation.tests.iter()
    {
        let (exe_display, mut cmd) = cmd_builds(
            gctx,
            cwd,
            unit,
            path,
            script_metas.as_ref(),
            env,
            test_args,
            compilation,
            "unittests",
        )?;

        // Trust: inspect the effective target environment after cmd_builds has
        // applied build-script values, rather than ambient process globals.
        if unit.target.harness()
            && compilation.target_runner(unit.kind).is_none()
            && let Some(budget) = worker_budget
        {
            budget.apply(&mut cmd, test_args)?;
        }

        if gctx.extra_verbose() {
            cmd.display_env_vars();
        }

        gctx.shell()
            .concise(|shell| shell.status("Running", &exe_display))?;
        gctx.shell()
            .verbose(|shell| shell.status("Running", &cmd))?;

        let required = matches!(unit.target.kind(), TargetKind::Bin)
            && options
                .required_test_bins
                .iter()
                .any(|name| name == unit.target.name());
        let execution_result = if required {
            // Trust: the judge names who requires the result.
            let who = format!("required test binary `{}`", unit.target.name());
            execute_judged(&cmd, Some(&who), None, graph::OutputSink::Raw)
        } else if matches!(test_kind, TestKind::Bench) {
            // Trust: compilation has returned its queue/credits. Direct bench
            // leaves use the same funded target owner as run, never a second
            // admission or the already-managed test-action queue's scheduler.
            compilation.prepare_target_execution(cmd)?.exec()
        } else {
            cmd.exec()
        };
        if let Err(e) = execution_result {
            // An interrupted/unsettled native direct phase cannot dispatch
            // another bench, even after target0 or with no-fail-fast set.
            let cannot_continue = e
                .downcast_ref::<cargo_util::TargetExecutionError>()
                .is_some();
            let code = if cannot_continue {
                101
            } else {
                fail_fast_code(&e)
            };
            let unit_err = UnitTestError {
                unit: unit.clone(),
                kind: test_kind,
                rerun: None, // Trust: only a test plan's actions name one.
            };
            report_test_error(ws, test_args, &options.compile_opts, &unit_err, e);
            errors.push(unit_err);
            if cannot_continue || !options.no_fail_fast {
                return Err(CliError::code(code));
            }
        }
    }
    Ok(errors)
}

/// Trust (D2b, 2026-09-28): the verified lane refuses the doctest execution
/// edge only when there IS a doctest unit to execute. Phase B of `targo trust
/// test` selects `--tests` (or the caller's explicit target selector), which
/// schedules no doctest unit, so `to_doc_test` is empty there; refusing that
/// empty set failed phase B with exit 101 after its unit tests had passed. That
/// was observed only in the advisory (`--allow-l0-gaps`) lane — the strict lane
/// never reached phase B before D2 was fixed. A non-empty set still refuses.
fn verified_doctest_execution_refusal(
    verified_targo: bool,
    doctest_units: usize,
) -> Option<anyhow::Error> {
    (verified_targo && doctest_units > 0).then(|| {
        anyhow::anyhow!(
            "verified Targo doctest execution is unavailable: rustdoc launches generated test executables internally, but no sealed handle-bound trustdoc + nested-doctest execution closure is implemented; pathname hash checks cannot authorize this edge"
        )
    })
}

/// Runs doc tests.
///
/// Returns a `Vec` of tests that failed when `--no-fail-fast` is used.
/// If `--no-fail-fast` is *not* used, then this returns an `Err`.
fn run_doc_tests(
    ws: &Workspace<'_>,
    options: &TestOptions,
    test_args: &[&str],
    compilation: &Compilation<'_>,
) -> Result<Vec<UnitTestError>, CliError> {
    // Trust: doctests are the one execution edge this design cannot yet close —
    // rustdoc compiles and launches the test binaries itself, inside a process
    // tree Cargo never sees, so there is nothing to authenticate against. Fail
    // closed rather than run them under an authority that does not exist.
    if let Some(refusal) = verified_doctest_execution_refusal(
        crate::is_targo_invocation() && crate::trust_verified_targo(),
        compilation.to_doc_test.len(),
    ) {
        return Err(refusal.into());
    }
    let gctx = ws.gctx();
    let mut errors = Vec::new();
    let color = gctx.shell().color_choice();

    for doctest_info in &compilation.to_doc_test {
        let Doctest {
            args,
            unstable_opts,
            unit,
            linker,
            script_metas,
            env,
        } = doctest_info;

        gctx.shell().status("Doc-tests", unit.target.name())?;
        let mut p = compilation.rustdoc_process(unit, script_metas.as_ref())?;

        for (var, value) in env {
            p.env(var, value);
        }

        let color_arg = match color {
            ColorChoice::Always => "always",
            ColorChoice::Never => "never",
            ColorChoice::CargoAuto => "auto",
        };
        p.arg("--color").arg(color_arg);

        p.arg("--crate-name").arg(&unit.target.crate_name());
        p.arg("--test");

        add_path_args(ws, unit, &mut p);
        p.arg("--test-run-directory").arg(unit.pkg.root());

        unit.kind.add_target_arg(&mut p);

        if let Some((runtool, runtool_args)) = compilation.target_runner(unit.kind) {
            p.arg("--test-runtool").arg(runtool);
            for arg in runtool_args {
                p.arg("--test-runtool-arg").arg(arg);
            }
        }
        if let Some(linker) = linker {
            let mut joined = OsString::from("linker=");
            joined.push(linker);
            p.arg("-C").arg(joined);
        }

        if unit.profile.panic != PanicStrategy::Unwind {
            p.arg("-C").arg(format!("panic={}", unit.profile.panic));
        }

        for native_dep in compilation.native_dirs.iter() {
            p.arg("-L").arg(native_dep);
        }

        for arg in test_args {
            p.arg("--test-args").arg(arg);
        }

        if gctx.shell().verbosity() == Verbosity::Quiet {
            p.arg("--test-args").arg("--quiet");
        }

        p.args(unit.pkg.manifest().lint_rustflags());

        p.args(args);

        if *unstable_opts {
            p.arg("-Zunstable-options");
        }

        if gctx.extra_verbose() {
            p.display_env_vars();
        }

        gctx.shell()
            .verbose(|shell| shell.status("Running", p.to_string()))?;

        // Trust: doctest execution runs rustdoc a third time, after the build
        // reported. Bracket it like the compile and merge spawns.
        compilation.ensure_verified_rustdoc_launcher_current()?;
        let execution = compilation.prepare_doc_test_execution(p)?.exec();
        // Recheck even when rustdoc itself failed: an endpoint replacement is
        // an integrity failure and must not be hidden behind the child status.
        compilation.ensure_verified_rustdoc_launcher_current()?;

        if let Err(e) = execution {
            let code = fail_fast_code(&e);
            let unit_err = UnitTestError {
                unit: unit.clone(),
                kind: TestKind::Doctest,
                rerun: None, // Trust: only a test plan's actions name one.
            };
            report_test_error(ws, test_args, &options.compile_opts, &unit_err, e);
            errors.push(unit_err);
            if !options.no_fail_fast {
                return Err(CliError::code(code));
            }
        }
    }
    Ok(errors)
}

/// Displays human-readable descriptions of the test executables.
///
/// This is used when `cargo test --no-run` is used.
fn display_no_run_information(
    ws: &Workspace<'_>,
    test_args: &[&str],
    compilation: &Compilation<'_>,
    exec_type: &str,
) -> CargoResult<()> {
    let gctx = ws.gctx();
    let cwd = gctx.cwd();
    for UnitOutput {
        unit,
        path,
        script_metas,
        env,
    } in compilation.tests.iter()
    {
        let (exe_display, cmd) = cmd_builds(
            gctx,
            cwd,
            unit,
            path,
            script_metas.as_ref(),
            env,
            test_args,
            compilation,
            exec_type,
        )?;
        gctx.shell()
            .concise(|shell| shell.status("Executable", &exe_display))?;
        gctx.shell()
            .verbose(|shell| shell.status("Executable", &cmd))?;
    }

    Ok(())
}

/// Creates a [`ProcessBuilder`] for executing a single test.
///
/// Returns a tuple `(exe_display, process)` where `exe_display` is a string
/// to display that describes the executable path in a human-readable form.
/// `process` is the `ProcessBuilder` to use for executing the test.
fn cmd_builds(
    gctx: &GlobalContext,
    cwd: &Path,
    unit: &Unit,
    path: &PathBuf,
    script_metas: Option<&Vec<UnitHash>>,
    env: &HashMap<String, OsString>,
    test_args: &[&str],
    compilation: &Compilation<'_>,
    exec_type: &str,
) -> CargoResult<(String, ProcessBuilder)> {
    let test_path = unit.target.src_path().path().unwrap();
    let short_test_path = test_path
        .strip_prefix(unit.pkg.root())
        .unwrap_or(test_path)
        .display();

    let exe_display = match unit.target.kind() {
        TargetKind::Test | TargetKind::Bench => format!(
            "{} ({})",
            short_test_path,
            path.strip_prefix(cwd).unwrap_or(path).display()
        ),
        _ => format!(
            "{} {} ({})",
            exec_type,
            short_test_path,
            path.strip_prefix(cwd).unwrap_or(path).display()
        ),
    };

    let mut cmd = compilation.target_process(path, unit.kind, &unit.pkg, script_metas)?;
    cmd.args(test_args);
    if unit.target.harness() && gctx.shell().verbosity() == Verbosity::Quiet {
        cmd.arg("--quiet");
    }
    for (key, val) in env.iter() {
        cmd.env(key, val);
    }

    Ok((exe_display, cmd))
}

/// Returns the error code to use when *not* using `--no-fail-fast`.
///
/// Cargo will return the error code from the test process itself. If some
/// other error happened (like a failure to launch the process), then it will
/// return a standard 101 error code.
///
/// When using `--no-fail-fast`, Cargo always uses the 101 exit code (since
/// there may not be just one process to report).
fn fail_fast_code(error: &anyhow::Error) -> i32 {
    if let Some(proc_err) = error.downcast_ref::<ProcessError>() {
        if let Some(code) = proc_err.code {
            return code;
        }
    }
    101
}

/// Returns the `CliError` when using `--no-fail-fast` and there is at least
/// one error.
fn no_fail_fast_err(
    ws: &Workspace<'_>,
    opts: &ops::CompileOptions,
    errors: &[UnitTestError],
) -> CliResult {
    // TODO: This could be improved by combining the flags on a single line when feasible.
    let args: Vec<_> = errors
        .iter()
        .map(|unit_err| {
            // Trust: a plan's failed target is named beside its request.
            let target = unit_err
                .plan_target()
                .map_or_else(String::new, |target| format!(" ({target})"));
            format!("    `{}`{target}", unit_err.cli_args(ws, opts))
        })
        .collect();
    let message = match errors.len() {
        0 => return Ok(()),
        1 => format!("1 target failed:\n{}", args.join("\n")),
        n => format!("{n} targets failed:\n{}", args.join("\n")),
    };
    Err(anyhow::Error::msg(message).into())
}

/// Trust: the exit code of a test process whose exit is all that went wrong:
/// the top of the error chain, never an exit beneath a reason Targo put
/// above it (`report_test_error`).
fn exit_that_is_the_whole_error(test_error: &anyhow::Error) -> Option<i32> {
    test_error
        .chain()
        .next()
        .and_then(|top| top.downcast_ref::<ProcessError>())
        .and_then(|proc_err| proc_err.code)
}

#[cfg(test)]
mod whole_error_tests {
    use super::exit_that_is_the_whole_error;
    use cargo_util::ProcessError;

    #[test]
    fn an_exit_beneath_targos_own_reason_is_not_a_simple_test_failure() {
        let exit = || ProcessError {
            desc: "process didn't exit successfully".to_owned(),
            code: Some(101),
            signal: None,
            stdout: None,
            stderr: None,
        };
        assert_eq!(exit_that_is_the_whole_error(&exit().into()), Some(101));
        // A harness Targo stopped (its output past the aggregate limit, a
        // cancellation) may have exited 101 by then; the reason is the error.
        let stopped = anyhow::Error::from(exit())
            .context("streaming stdout exceeds the 536870912-byte aggregate safety limit");
        assert!(stopped.downcast_ref::<ProcessError>().is_some());
        assert_eq!(exit_that_is_the_whole_error(&stopped), None);
    }
}

/// Displays an error on the console about a test failure.
fn report_test_error(
    ws: &Workspace<'_>,
    test_args: &[&str],
    opts: &ops::CompileOptions,
    unit_err: &UnitTestError,
    test_error: anyhow::Error,
) {
    let which = match unit_err.kind {
        TestKind::Test => "test failed",
        TestKind::Bench => "bench failed",
        TestKind::Doctest => "doctest failed",
    };

    // Trust: a plan's failed target is named before its request.
    let which = unit_err
        .plan_target()
        .map_or_else(|| which.to_owned(), |target| format!("{target}: {which}"));
    // Trust: a `[[workspace]]` phase is rerun by a command of its own, not
    // by arguments added to this invocation.
    let verb = match unit_err.rerun {
        Some(plan::Rerun::Command(_)) => "run",
        _ => "pass",
    };
    let mut err = format_err!(
        "{}, to rerun {verb} `{}`",
        which,
        unit_err.cli_args(ws, opts)
    );
    // Don't show "process didn't exit successfully" for simple errors.
    // libtest exits with 101 for normal errors.
    // Trust: only where the exit is the whole error. `downcast_ref` also
    // finds the exit beneath a reason Targo put above it (harness output past
    // the aggregate limit, a cancellation), and a harness stopped for that
    // reason may still have exited 101; calling that "simple" printed
    // "test failed" with the reason dropped (`graph::Termination::of` reads
    // the same top of the chain).
    let (is_simple, executed) = exit_that_is_the_whole_error(&test_error)
        .map_or((false, false), |code| (code == 101, true));

    if !is_simple {
        err = test_error.context(err);
    }

    crate::display_error(&err, &mut ws.gctx().shell());

    let harness: bool = unit_err.unit.target.harness();
    let nocapture: bool = test_args.contains(&"--nocapture") || test_args.contains(&"--no-capture");

    if !is_simple && executed && harness && !nocapture {
        drop(ws.gctx().shell().note(
            "test exited abnormally; to see the full output pass --no-capture to the harness.",
        ));
    }
}

// Trust: the judge of a required test binary and of a test plan's actions
// reads libtest's lines; what it takes from each is asserted here.
#[cfg(test)]
mod judged_summary_tests {
    use super::{RequiredTestSummary, plan_judge::Closing};
    use crate::util::machine_message::TestCounts;

    const OK: &str = "test result: ok. 3 passed; 0 failed; 1 ignored; 0 measured; 2 filtered out; \
                      finished in 0.01s";
    const FAILED: &str = "test result: FAILED. 3 passed; 2 failed; 1 ignored; 0 measured; 4 \
                          filtered out; finished in 0.01s";

    fn counts(passed: u64, failed: u64, ignored: u64, filtered_out: u64) -> Option<TestCounts> {
        Some(TestCounts {
            passed,
            failed,
            ignored,
            filtered_out,
        })
    }

    fn after(lines: &[&str]) -> RequiredTestSummary {
        let mut summary =
            RequiredTestSummary::watching(&["m::one".to_owned(), "m::slow".to_owned()]);
        for line in lines {
            summary.observe_stdout(line);
        }
        summary
    }

    #[test]
    fn a_closing_line_gives_all_four_numbers() {
        let summary = after(&["running 4 tests", OK]);
        assert_eq!(
            summary.plan.closing(),
            Some(Closing {
                ok: true,
                counts: counts(3, 0, 1, 2),
                measured: 0,
            })
        );
        summary.finish("who").unwrap();

        let summary = after(&[FAILED]);
        assert_eq!(
            summary.plan.closing(),
            Some(Closing {
                ok: false,
                counts: counts(3, 2, 1, 4),
                measured: 0,
            })
        );
        assert!(summary.finish("who").is_err());
        // `measured` is read too: it is part of what the run announced.
        let measured = "test result: ok. 1 passed; 0 failed; 2 ignored; 3 measured; 4 filtered out";
        assert_eq!(
            after(&[measured]).plan.closing(),
            Some(Closing {
                ok: true,
                counts: counts(1, 0, 2, 4),
                measured: 3,
            })
        );

        // No closing line, a truncated one, and an `ok` that counts a failure.
        assert_eq!(
            after(&["running 1 test", "test m::one ... ok"])
                .plan
                .closing(),
            None
        );
        for line in [
            "test result: ok. 3 passed; 0 failed;",
            "test result: ok. 3 passed; 1 failed; 0 ignored; 0 measured; 0 filtered out",
            "test result: FAILED. x passed; 1 failed; 0 ignored; 0 measured; 0 filtered out",
        ] {
            let closing = after(&[line]).plan.closing().expect(line);
            assert_eq!(closing.counts, None, "{line}");
        }
    }

    #[test]
    fn the_last_closing_line_is_the_harness_s_own() {
        let summary = after(&[OK, FAILED]);
        assert_eq!(summary.plan.closing().unwrap().ok, false);
        let summary = after(&[FAILED, OK]);
        assert_eq!(summary.plan.closing().unwrap().ok, true);
        // Whoever requires a passing test still takes one summary only.
        assert!(summary.finish("who").is_err());
        assert!(after(&[OK, OK]).finish("who").is_err());
    }
}

// Trust: pins the test-execution authority — manifest parsing and its bounds,
// the session binding, and the environment/native-dir closure a test process is
// allowed to inherit. Each of these is a refusal, so a regression here is
// silent unless it is asserted.
#[cfg(test)]
mod trust_test_execution_tests {
    use super::{
        read_test_execution_authority_manifest, reject_unbound_test_loader_env,
        reject_unbound_test_native_dirs, reject_unharnessed_certified_test_target,
        strip_test_execution_authority_env, test_execution_authority_inputs,
        verified_doctest_execution_refusal,
    };
    use crate::util::data_structures::HashMap;
    use cargo_util::{ProcessBuilder, Sha256};
    use std::collections::BTreeSet;

    fn authority_manifest_bytes(session: &str) -> Vec<u8> {
        serde_json::to_vec(&serde_json::json!({
            "schema": "trust.targo-test-execution-authority.v2",
            "verification_session": session,
            "target_directory": "/authenticated/target",
            "executables": [{
                "target": "fixture",
                "path": "/authenticated/target/fixture",
                "sha256": "a".repeat(64),
                "size": 1,
            }],
        }))
        .expect("serialize authority fixture")
    }

    fn sha256(bytes: &[u8]) -> String {
        let mut hasher = Sha256::new();
        hasher.update(bytes);
        hasher.finish_hex()
    }

    fn write_private(path: &std::path::Path, bytes: &[u8]) {
        std::fs::write(path, bytes).expect("write authority fixture");
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt as _;

            std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o600))
                .expect("make authority fixture private");
        }
    }

    #[test]
    fn authenticated_execution_requires_the_complete_manifest_binding_tuple() {
        assert!(
            test_execution_authority_inputs(None, None, None)
                .expect("ordinary Cargo has no execution authority")
                .is_none()
        );
        let error = test_execution_authority_inputs(
            Some("session".into()),
            Some("/authority.json".into()),
            None,
        )
        .expect_err("a manifest path without its authenticated digest must fail closed");
        assert!(
            error
                .to_string()
                .contains("TRUST_TARGO_TEST_EXECUTION_MANIFEST_SHA256"),
            "{error:#}"
        );
    }

    #[test]
    fn authenticated_execution_reads_the_exact_digest_bound_manifest() {
        let temp = tempfile::tempdir().expect("authority fixture directory");
        let path = temp.path().join("authority.json");
        let bytes = authority_manifest_bytes("fresh-session");
        write_private(&path, &bytes);
        let manifest = read_test_execution_authority_manifest(&path, &sha256(&bytes))
            .expect("exact outer-Targo manifest digest must authenticate");
        assert_eq!(manifest.verification_session, "fresh-session");
        assert_eq!(manifest.executables.len(), 1);
    }

    #[test]
    fn authenticated_execution_rejects_malformed_and_mismatched_manifest_digests() {
        let temp = tempfile::tempdir().expect("authority fixture directory");
        let path = temp.path().join("authority.json");
        let bytes = authority_manifest_bytes("fresh-session");
        write_private(&path, &bytes);
        let malformed = read_test_execution_authority_manifest(&path, "not-a-digest")
            .expect_err("malformed expected digest must fail closed");
        assert!(
            malformed.to_string().contains("canonical SHA-256"),
            "{malformed:#}"
        );
        let mismatch = read_test_execution_authority_manifest(&path, &"0".repeat(64))
            .expect_err("mismatched manifest bytes must fail closed");
        assert!(
            mismatch.to_string().contains("digest does not match"),
            "{mismatch:#}"
        );
    }

    #[test]
    fn authenticated_execution_rejects_manifest_path_replacement() {
        let temp = tempfile::tempdir().expect("authority fixture directory");
        let path = temp.path().join("authority.json");
        let original = authority_manifest_bytes("fresh-session");
        write_private(&path, &original);
        let expected = sha256(&original);
        std::fs::rename(&path, temp.path().join("original-authority.json"))
            .expect("move authenticated manifest away");
        write_private(&path, &authority_manifest_bytes("attacker-session"));

        let error = read_test_execution_authority_manifest(&path, &expected)
            .expect_err("a replacement at the same authority pathname must fail closed");
        assert!(
            error.to_string().contains("digest does not match"),
            "{error:#}"
        );
    }

    #[test]
    fn authenticated_test_execution_requires_the_standard_test_harness() {
        let error = reject_unharnessed_certified_test_target(true, false, "arbitrary-main")
            .expect_err("harness=false must not enter certified phase B");
        assert!(error.to_string().contains("harness = false"), "{error:#}");
        reject_unharnessed_certified_test_target(true, true, "libtest")
            .expect("standard harness is in scope");
        reject_unharnessed_certified_test_target(false, false, "ordinary-cargo")
            .expect("ordinary Cargo behavior is unchanged");
    }

    #[test]
    fn authenticated_test_execution_rejects_build_script_loader_injection() {
        let script_metas = [7_u64];
        for name in [
            "LD_PRELOAD",
            "DYLD_INSERT_LIBRARIES",
            "LIBPATH",
            "LDR_PRELOAD",
            "PATH",
        ] {
            let extra_env = [(
                script_metas[0],
                vec![(name.to_string(), "/unbound/injection".to_string())],
            )]
            .into_iter()
            .collect::<HashMap<_, _>>();
            let error = reject_unbound_test_loader_env(Some(&script_metas), &extra_env)
                .expect_err("loader-affecting rustc-env must fail closed");
            assert!(error.to_string().contains(name), "{error:#}");
        }

        let benign = [(
            script_metas[0],
            vec![("FIXTURE_MODE".to_string(), "strict".to_string())],
        )]
        .into_iter()
        .collect::<HashMap<_, _>>();
        reject_unbound_test_loader_env(Some(&script_metas), &benign)
            .expect("ordinary build-script test environment is retained");

        let unrelated = [(
            99_u64,
            vec![("LD_PRELOAD".to_string(), "/unbound/injection".to_string())],
        )]
        .into_iter()
        .collect::<HashMap<_, _>>();
        reject_unbound_test_loader_env(Some(&script_metas), &unrelated)
            .expect("another unit's build-script environment is not applied to this test");
    }

    #[test]
    fn authenticated_test_execution_rejects_native_dirs_and_strips_authority() {
        let native_dirs = [std::path::PathBuf::from("/unbound/native")]
            .into_iter()
            .collect::<BTreeSet<_>>();
        assert!(
            reject_unbound_test_native_dirs(&native_dirs)
                .expect_err("native closure is not yet authenticated")
                .to_string()
                .contains("native-library directories")
        );
        reject_unbound_test_native_dirs(&BTreeSet::new()).expect("no native closure");

        let mut command = ProcessBuilder::new("test-binary");
        for name in [
            "TRUST_TARGO_PREPARED_TEST_SESSION",
            "TRUST_TARGO_TEST_EXECUTION_MANIFEST",
            "TRUST_TARGO_TEST_EXECUTION_MANIFEST_SHA256",
            "TRUST_TARGO_TEST_MONITOR_AUTHORITY_SESSION",
            "TRUST_TARGO_TEST_MONITOR_SESSION",
            "TRUST_TARGO_VERIFY",
            "TRUST_MEMORY_JOBSERVER_SOCK",
            "TRUST_MEMORY_JOBSERVER",
            "TRUST_TARGO_LANE_RUSTFLAGS",
            "CARGO_ENCODED_RUSTFLAGS",
            "RUSTC",
            "LD_LIBRARY_PATH",
            "LD_PRELOAD",
            "DYLD_INSERT_LIBRARIES",
            "LIBPATH",
        ] {
            command.env(name, "private-proof-authority");
        }
        command.env("FIXTURE_MODE", "strict");
        strip_test_execution_authority_env(&mut command);
        for name in [
            "TRUST_TARGO_PREPARED_TEST_SESSION",
            "TRUST_TARGO_TEST_EXECUTION_MANIFEST",
            "TRUST_TARGO_TEST_EXECUTION_MANIFEST_SHA256",
            "TRUST_TARGO_TEST_MONITOR_AUTHORITY_SESSION",
            "TRUST_TARGO_TEST_MONITOR_SESSION",
            "TRUST_TARGO_VERIFY",
            "TRUST_MEMORY_JOBSERVER_SOCK",
            "TRUST_MEMORY_JOBSERVER",
            "TRUST_TARGO_LANE_RUSTFLAGS",
            "CARGO_ENCODED_RUSTFLAGS",
            "RUSTC",
            "LD_LIBRARY_PATH",
            "LD_PRELOAD",
            "DYLD_INSERT_LIBRARIES",
            "LIBPATH",
        ] {
            assert_eq!(command.get_env(name), None, "{name}");
        }
        #[cfg(target_os = "macos")]
        assert_eq!(
            command.get_env("DYLD_FALLBACK_LIBRARY_PATH").as_deref(),
            Some(std::ffi::OsStr::new("/usr/lib:/System/Library/Frameworks"))
        );
        #[cfg(target_os = "macos")]
        assert_eq!(
            command.get_env("DYLD_FALLBACK_FRAMEWORK_PATH").as_deref(),
            Some(std::ffi::OsStr::new("/System/Library/Frameworks"))
        );
        assert_eq!(
            command.get_env("FIXTURE_MODE").as_deref(),
            Some(std::ffi::OsStr::new("strict"))
        );
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn authenticated_execution_moves_authority_fds_above_stdio_with_cloexec() {
        use std::os::fd::{AsRawFd as _, OwnedFd};

        let ordinary: OwnedFd = std::fs::File::open("/dev/null")
            .expect("open harmless descriptor")
            .into();
        let ordinary =
            super::owned_fd_at_least(ordinary, 3).expect("production minimum must be available");
        assert!(ordinary.as_raw_fd() >= 3);
        let ordinary_flags = unsafe { libc::fcntl(ordinary.as_raw_fd(), libc::F_GETFD) };
        assert!(
            ordinary_flags >= 0,
            "production descriptor must remain open"
        );
        assert_ne!(
            ordinary_flags & libc::FD_CLOEXEC,
            0,
            "production descriptor lost CLOEXEC"
        );

        // Force the duplication branch without closing process-global stdio.
        let original: OwnedFd = std::fs::File::open("/dev/null")
            .expect("open descriptor to duplicate")
            .into();
        let original_number = original.as_raw_fd();
        let raised = super::owned_fd_at_least(original, original_number + 1)
            .expect("duplicate descriptor above requested minimum");
        assert!(raised.as_raw_fd() > original_number);
        let flags = unsafe { libc::fcntl(raised.as_raw_fd(), libc::F_GETFD) };
        assert!(flags >= 0, "duplicated descriptor must remain open");
        assert_ne!(
            flags & libc::FD_CLOEXEC,
            0,
            "duplicated descriptor lost CLOEXEC"
        );
    }

    #[cfg(any(
        all(
            target_os = "linux",
            any(target_arch = "x86_64", target_arch = "aarch64")
        ),
        all(
            target_os = "macos",
            any(target_arch = "x86_64", target_arch = "aarch64")
        )
    ))]
    fn authority_for(path: &std::path::Path) -> super::TestExecutionAuthority {
        let canonical = path.canonicalize().expect("canonical executable");
        let (sha256, size) =
            super::exact_regular_test_executable_identity(&canonical).expect("hash executable");
        let entry = super::TestExecutionAuthorityEntry {
            target: "certified-test-fixture".to_string(),
            path: canonical.display().to_string(),
            sha256,
            size,
        };
        super::TestExecutionAuthority {
            executables: [(canonical, entry)].into_iter().collect(),
            prepared: None,
        }
    }

    #[cfg(all(
        target_os = "linux",
        any(target_arch = "x86_64", target_arch = "aarch64")
    ))]
    #[test]
    fn authenticated_execution_snapshot_is_sealed_against_source_replacement() {
        use std::io::{Seek as _, Write as _};

        let temp = tempfile::tempdir().expect("temporary executable directory");
        let executable = temp.path().join("authorized-test");
        std::fs::copy(
            std::env::current_exe().expect("current test binary"),
            &executable,
        )
        .expect("copy test executable");
        let authority = authority_for(&executable);
        let snapshot = authority
            .executable_snapshot(&executable)
            .expect("capture sealed execution image");
        let expected = authority
            .executables
            .values()
            .next()
            .expect("authorized entry")
            .sha256
            .clone();

        // Replacing the Cargo pathname after capture cannot change the anonymous
        // image selected for execveat.
        std::fs::write(&executable, b"attacker-controlled replacement")
            .expect("replace original path");
        let mut image = snapshot
            .file
            .try_clone()
            .expect("clone snapshot descriptor");
        image
            .seek(std::io::SeekFrom::Start(0))
            .expect("rewind snapshot");
        let mut digest = cargo_util::Sha256::new();
        digest.update_file(&image).expect("hash snapshot");
        assert_eq!(digest.finish_hex(), expected);

        image
            .seek(std::io::SeekFrom::End(0))
            .expect("seek sealed snapshot");
        let error = image
            .write_all(b"tamper")
            .expect_err("F_SEAL_WRITE must reject in-place image mutation");
        assert_eq!(error.raw_os_error(), Some(libc::EPERM));
    }

    #[cfg(all(
        target_os = "linux",
        any(target_arch = "x86_64", target_arch = "aarch64")
    ))]
    #[test]
    fn authenticated_execveat_binds_sealed_image_and_preserves_subprocesses() {
        const FIXTURE: &str = "CARGO_CERTIFIED_TEST_EXECVEAT_FIXTURE";
        if std::env::var_os(FIXTURE).is_some() {
            assert!(
                std::process::Command::new("/bin/true")
                    .status()
                    .expect("spawn subprocess from authenticated test")
                    .success(),
                "authenticated execution must retain ordinary subprocess semantics"
            );
            return;
        }

        let temp = tempfile::tempdir().expect("temporary executable directory");
        let executable = temp.path().join("authorized-test");
        std::fs::copy(
            std::env::current_exe().expect("current test binary"),
            &executable,
        )
        .expect("copy test executable");
        let authority = authority_for(&executable);
        let snapshot = authority
            .executable_snapshot(&executable)
            .expect("capture sealed execution image");

        // A pathname-based launch would now fail. The authenticated launch must
        // instead execute the already-sealed bytes selected by the open handle.
        std::fs::write(&executable, b"not an executable")
            .expect("replace authorized source path after snapshot");
        let mut command = ProcessBuilder::new(&executable);
        command
            .env(FIXTURE, "1")
            .arg("--test-threads=1")
            .arg("authenticated_execveat_binds_sealed_image_and_preserves_subprocesses");
        super::execute_authenticated_snapshot(snapshot, &command)
            .expect("nested test must execute from the sealed image");
    }

    #[cfg(all(
        target_os = "macos",
        any(target_arch = "x86_64", target_arch = "aarch64")
    ))]
    #[test]
    fn macos_macho_parser_matches_the_live_kernel_cdhash() {
        let current = std::env::current_exe().expect("current test executable");
        let mut file = std::fs::File::open(&current).expect("open current test executable");
        let parsed = super::macho_sha256_cdhash(&mut file).expect("parse Mach-O code directory");
        let live =
            super::mac_live_process_cdhash(std::process::id() as libc::pid_t).expect("live CDHash");
        assert_eq!(parsed, live, "static and live code identity must agree");
    }

    #[cfg(all(
        target_os = "macos",
        any(target_arch = "x86_64", target_arch = "aarch64")
    ))]
    #[test]
    #[expect(
        clippy::disallowed_methods,
        reason = "the authenticated child image distinguishes its actual inherited fixture tag, without a GlobalContext"
    )]
    fn authenticated_macos_launch_binds_live_cdhash_and_preserves_subprocesses() {
        const FIXTURE: &str = "CARGO_CERTIFIED_TEST_MACOS_FIXTURE";
        if std::env::var_os(FIXTURE).is_some() {
            assert!(
                std::process::Command::new("/usr/bin/true")
                    .status()
                    .expect("spawn subprocess from authenticated test")
                    .success(),
                "authenticated execution must retain ordinary subprocess semantics"
            );
            return;
        }

        let temp = tempfile::tempdir().expect("temporary executable directory");
        let executable = temp.path().join("authorized-test");
        std::fs::copy(
            std::env::current_exe().expect("current test binary"),
            &executable,
        )
        .expect("copy test executable");
        let authority = authority_for(&executable);
        let snapshot = authority
            .mac_executable_snapshot(&executable)
            .expect("capture private signed execution image");

        // The phase-A artifact path is no longer executable. Launch must use
        // the private image and then bind its exact CDHash to the suspended
        // live process before this nested fixture can run.
        std::fs::write(&executable, b"attacker-controlled replacement")
            .expect("replace authorized source path");
        let mut command = ProcessBuilder::new(&executable);
        command
            .env(FIXTURE, "1")
            .arg("--test-threads=1")
            .arg("authenticated_macos_launch_binds_live_cdhash_and_preserves_subprocesses");
        super::execute_authenticated_mac_snapshot(snapshot, &executable, &command)
            .expect("nested test must execute from the CDHash-bound image");
    }

    #[cfg(all(
        target_os = "macos",
        any(target_arch = "x86_64", target_arch = "aarch64")
    ))]
    #[test]
    fn authenticated_macos_launch_rejects_snapshot_path_substitution_before_resume() {
        use std::os::unix::fs::PermissionsExt as _;

        let temp = tempfile::tempdir().expect("temporary executable directory");
        let executable = temp.path().join("authorized-test");
        std::fs::copy(
            std::env::current_exe().expect("current test binary"),
            &executable,
        )
        .expect("copy test executable");
        let authority = authority_for(&executable);
        let snapshot = authority
            .mac_executable_snapshot(&executable)
            .expect("capture private signed execution image");
        std::fs::set_permissions(&snapshot.path, std::fs::Permissions::from_mode(0o700))
            .expect("owner can attempt to replace its snapshot");
        std::fs::copy("/usr/bin/true", &snapshot.path).expect("substitute another signed image");
        let command = ProcessBuilder::new(&executable);
        let error = super::execute_authenticated_mac_snapshot(snapshot, &executable, &command)
            .expect_err("changed snapshot must never be resumed");
        assert!(
            error.to_string().contains("execution image changed"),
            "{error:#}"
        );
    }

    #[cfg(not(any(
        all(
            target_os = "linux",
            any(target_arch = "x86_64", target_arch = "aarch64")
        ),
        all(
            target_os = "macos",
            any(target_arch = "x86_64", target_arch = "aarch64")
        )
    )))]
    #[test]
    fn evidence_grade_execution_fails_closed_without_a_sealed_handle_backend() {
        let authority = super::TestExecutionAuthority {
            executables: std::collections::BTreeMap::new(),
            prepared: None,
        };
        let command = ProcessBuilder::new("unused");
        let error = super::execute_authenticated_test(
            &authority,
            std::path::Path::new("/unauthorized/test"),
            &command,
        )
        .expect_err("unsupported hosts must not fall back to pathname execution");
        assert!(
            error
                .to_string()
                .contains("requires Linux sealed-memfd execveat or macOS"),
            "{error:#}"
        );
    }

    /// D2b (2026-09-28): phase B of `targo trust test` runs `--tests`, which
    /// schedules no doctest unit. Refusing the EMPTY doctest set failed every
    /// such phase B with exit 101 after its tests passed; a real doctest unit
    /// must still be refused, and the unverified lane is never refused.
    #[test]
    fn verified_doctest_refusal_requires_a_doctest_unit_to_execute() {
        assert!(
            verified_doctest_execution_refusal(true, 0).is_none(),
            "phase B (`--tests`) has no doctest unit and must not be refused"
        );
        let refusal = verified_doctest_execution_refusal(true, 1)
            .expect("a doctest unit in the verified lane is still refused");
        assert!(
            refusal
                .to_string()
                .contains("doctest execution is unavailable"),
            "{refusal}"
        );
        assert!(verified_doctest_execution_refusal(false, 1).is_none());
        assert!(verified_doctest_execution_refusal(false, 0).is_none());
    }
}
