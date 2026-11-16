//! Trust: participate in the existing build/measurement mkdir lock natively.
//!
//! Deliberately no stale takeover, break, waiting policy or alternate lock pool:
//! existing holders and the legacy measurement marker cause a refusal. The
//! shell lock's status/recovery tools continue to understand this holder.

use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;

use crate::trust_build_lock::NamespaceGuard;

#[cfg(any(target_os = "macos", target_os = "linux"))]
pub mod incremental;
#[cfg(any(target_os = "macos", target_os = "linux"))]
pub mod management;

/// Owns this process's exact holder in the existing build/measurement namespace.
///
/// Keep the actual value until protected work settles. The holder excludes
/// cooperating actors only; it supplies neither source immutability nor
/// crash-surviving quarantine. Parent-managed holders preserve their existing
/// explicit outer-owner release contract. A forked copy is not a release owner.
#[must_use = "dropping an independently owned lease releases its exact holder"]
pub struct BuildLease {
    root: Root,
    owner: u32,
    directory: PathBuf,
    // Unsupported platforms cannot acquire the guard; exact-byte reads are Unix-only.
    #[cfg_attr(not(unix), allow(dead_code))]
    info: String,
    parent_managed: bool,
    holder: fs::Metadata,
    directory_identity: fs::Metadata,
    holder_file: fs::File,
    directory_file: fs::File,
}

impl BuildLease {
    /// Acquire for the native check, preserving actual direct-parent validation
    /// when that protocol is explicitly supplied in this process's environment.
    pub fn acquire(root: &Path) -> Result<Self, String> {
        Self::acquire_after_claim(root, false, || {})
    }

    /// Require the existing validated actual-parent release handoff.
    pub fn acquire_for_parent(root: &Path) -> Result<Self, String> {
        Self::acquire_after_claim(root, true, || {})
    }

    // Trust: an installation is a direct compiled writer, without a parent release protocol.
    pub fn acquire_for_installation(root: &Path) -> Result<Self, String> {
        if parent_handoff()?.is_some() {
            return Err("installation does not support a parent release handoff".into());
        }
        Self::acquire_named(
            root,
            false,
            None,
            "native immutable WP prerequisite installation",
            "bootstrap install trust-wp-installation",
            || {},
        )
    }

    /// Acquire a new holder owned by this process, without inspecting or
    /// adopting any inherited parent fields or tokens. An existing holder
    /// refuses instead of being borrowed or waited on. The root must exist.
    /// Namespace transactions retain their bounded wait; synchronous process
    /// and filesystem observations have no strict execution deadline.
    pub fn acquire_independent(
        root: &Path,
        purpose: &str,
        invocation: &str,
    ) -> Result<Self, String> {
        Self::acquire_named(root, false, None, purpose, invocation, || {})
    }

    /// Validate the original root mapping, pinned holder directory and file,
    /// and exact record bytes. Failure never adopts or deletes a replacement.
    /// Namespace contention retains the existing bounded transaction wait;
    /// synchronous filesystem operations have no strict execution deadline.
    pub fn check_current(&self) -> Result<(), String> {
        if std::process::id() != self.owner {
            return Err("a forked build lease copy has no original-owner authority".into());
        }
        self.root.check_current()?;
        let _namespace = NamespaceGuard::acquire(&self.root.physical).map_err(|e| e.to_string())?;
        self.check_current_locked()
    }

    /// Observe that the requested repository is this actual acquisition's
    /// original root. A matching pathname or token never constructs a lease.
    pub fn check_root(&self, root: &Path) -> Result<(), String> {
        self.check_current()?;
        self.root.check_expected(root)
    }

    fn check_current_locked(&self) -> Result<(), String> {
        if std::process::id() != self.owner {
            return Err("a forked build lease copy has no original-owner authority".into());
        }
        self.root.check_current()?;
        let info = self.directory.join("info");
        if !same_inode(
            &self.directory_identity,
            fs::symlink_metadata(&self.directory).ok().as_ref(),
        ) || !same_inode(&self.directory_identity, self.directory_file.metadata().ok().as_ref())
            || !same_inode(&self.holder, fs::symlink_metadata(&info).ok().as_ref())
            || !same_inode(&self.holder, self.holder_file.metadata().ok().as_ref())
        {
            return Err("the original build holder directory or file changed".into());
        }
        #[cfg(unix)]
        {
            use std::os::unix::fs::FileExt;
            self.check_record_metadata()?;
            let mut observed = vec![0; self.info.len()];
            self.holder_file.read_exact_at(&mut observed, 0).map_err(|e| e.to_string())?;
            if observed != self.info.as_bytes() {
                return Err("the original build holder record changed".into());
            }
            self.check_record_metadata()?;
            self.root.check_current()
        }
        #[cfg(not(unix))]
        {
            Err("checked build holder identity requires Unix".into())
        }
    }

    #[cfg(unix)]
    fn check_record_metadata(&self) -> Result<(), String> {
        use std::os::unix::fs::MetadataExt;
        let opened = self.holder_file.metadata().map_err(|e| e.to_string())?;
        let named = fs::symlink_metadata(self.directory.join("info")).map_err(|e| e.to_string())?;
        for metadata in [&opened, &named] {
            if !metadata.is_file()
                || !same_inode(&self.holder, Some(metadata))
                || metadata.nlink() != 1
                || metadata.uid() != unsafe { libc::geteuid() }
                || metadata.len() != self.info.len() as u64
            {
                return Err("the original build holder record changed".into());
            }
        }
        Ok(())
    }

    fn acquire_after_claim(
        root: &Path,
        required_parent: bool,
        after_claim: impl FnOnce(),
    ) -> Result<Self, String> {
        Self::acquire_named(
            root,
            required_parent,
            parent_handoff()?,
            "native compiler check and selected UI test",
            "bootstrap test --trust-repo-check",
            after_claim,
        )
    }

    fn acquire_named(
        root: &Path,
        required_parent: bool,
        // Trust: an explicit handoff is accepted only from our actual, live
        // direct parent (`parent_handoff`). A bare inherited boolean cannot
        // transfer release.
        handoff: Option<(String, String, String)>,
        purpose: &str,
        invocation: &str,
        after_claim: impl FnOnce(),
    ) -> Result<Self, String> {
        if required_parent && handoff.is_none() {
            return Err("native parent release v1 requires the validated actual-parent PID/start/token tuple".into());
        }
        for value in [purpose, invocation] {
            if value.chars().any(|character| {
                character.is_control() || matches!(character, '\u{2028}' | '\u{2029}')
            }) {
                return Err(
                    "build holder purpose and invocation must be single record lines".into()
                );
            }
        }
        let root = Root::open(root)?;
        let namespace = NamespaceGuard::acquire(&root.physical).map_err(|e| e.to_string())?;
        root.check_current()?;
        let path = &root.physical;
        if path.join(".trust-measurement-in-flight").exists() {
            return Err("the existing measurement marker holds this build tree".into());
        }
        let pid = std::process::id().to_string();
        let start = ps("lstart=", &pid)?;
        // Trust: EW18-LOCKUTC-1. `pstart` is in this process's TZ and locale, and a
        // reader in another one read it as a different process. `pstart_utc` is the
        // zone-free start every current reader compares; `pstart` stays beside it
        // for readers that predate the field.
        let start_utc = ps_utc("lstart=", &pid)?;
        let pgid = ps("pgid=", &pid)?;
        let mut temporary = tempfile::Builder::new()
            .prefix(".trust-build-lock.tmp.")
            .tempfile_in(path)
            .map_err(|e| e.to_string())?;
        let token = temporary.path().file_name().unwrap().to_string_lossy().into_owned();
        let started = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map_err(|e| e.to_string())?
            .as_secs();
        let mut info = format!(
            "token={token}\nkind=build\npid={pid}\npstart={start}\npstart_utc={start_utc}\n\
             pgid={pgid}\nstarted={started}\n\
             purpose={purpose}\n\
             cmd={invocation}\n\
             contract=the build tree is exclusive; execution facts only, no proof claim\n"
        );
        if let Some((parent, start, token)) = &handoff {
            info.push_str(&format!(
                "release_parent_pid={parent}\nrelease_parent_start={start}\nrelease_token={token}\n"
            ));
        }
        temporary.write_all(info.as_bytes()).map_err(|e| e.to_string())?;
        temporary.as_file().sync_all().map_err(|e| e.to_string())?;
        let directory = path.join(".trust-build-lock");
        create_holder_directory(&directory).map_err(|e| {
            format!(
                "cannot acquire the existing build/measurement lock {}: {e}",
                directory.display()
            )
        })?;
        let directory_file = open_directory(&directory)?;
        let directory_identity = directory_file.metadata().map_err(|e| e.to_string())?;
        after_claim();
        root.check_current()?;
        if !same_inode(&directory_identity, fs::symlink_metadata(&directory).ok().as_ref()) {
            return Err("the new build holder directory changed before publication".into());
        }
        let holder_file = match temporary.persist_noclobber(directory.join("info")) {
            Ok(file) => file,
            Err(error) => {
                if same_inode(&directory_identity, fs::symlink_metadata(&directory).ok().as_ref()) {
                    let _ = fs::remove_dir(&directory);
                }
                return Err(error.to_string());
            }
        };
        let holder = holder_file.metadata().map_err(|e| e.to_string())?;
        let lease = Self {
            root,
            owner: std::process::id(),
            directory,
            info,
            parent_managed: handoff.is_some(),
            holder,
            directory_identity,
            holder_file,
            directory_file,
        };
        // Drop may need the same namespace mutex if a legacy marker appeared.
        drop(namespace);
        lease.check_current()?;
        if lease.root.physical.join(".trust-measurement-in-flight").exists() {
            return Err("a legacy measurement appeared while acquiring the build tree".into());
        }
        Ok(lease)
    }
}

pub fn require_parent_handoff() -> Result<(), String> {
    parent_handoff()?.ok_or(
        "native parent release v1 requires the validated actual-parent PID/start/token tuple",
    )?;
    Ok(())
}

// Trust: EW-9 (22). The longest holder record judged: a seed's is a few hundred bytes.
#[cfg(unix)]
const RECORD_LIMIT: u64 = 4096;

// Trust: EW-9 (22). The fields `acquire_named` writes for an independent holder, each
// once. A record with any other line (a parent release handoff's among them, which the
// lock script never reclaims) is not judged.
#[cfg(unix)]
const INDEPENDENT_FIELDS: [&str; 10] = [
    "token",
    "kind",
    "pid",
    "pstart",
    "pstart_utc",
    "pgid",
    "started",
    "purpose",
    "cmd",
    "contract",
];

/// Trust: EW-9 (22). Read-only: the pid of the holder that `root/.trust-build-lock/info`
/// records, when that record is an independent holder's whose purpose is exactly
/// `purpose` and whose process is provably gone: no process has that pid (`kill(2)`
/// answers `ESRCH`), or the one that has it started at another time than the record's
/// zone-free `pstart_utc` (read as this module's writer reads it). This is the lock
/// script's stale rule for such a record, so the donor's next acquire reclaims that
/// holder; a zombie is alive to it and here (it is gone once reaped).
///
/// `None` on any doubt: a link at `.trust-build-lock` or `info`, an `info` that is not a
/// regular file this user owns with one link, longer than 4096 bytes, not UTF-8 or
/// not newline-terminated, a missing, repeated, empty-start or unknown field, another
/// kind or purpose, a pid that is not a plain positive number, a `ps` that does not
/// answer, or a live holder. Nothing is reclaimed, removed, created or changed, and no
/// namespace guard is taken: the answer only lets a caller stop waiting for the holder.
pub fn gone_independent_holder(root: &Path, purpose: &str) -> Option<u32> {
    #[cfg(unix)]
    {
        let record = read_holder_record(&root.join(".trust-build-lock"))?;
        let mut fields = std::collections::BTreeMap::new();
        for line in record.strip_suffix('\n')?.split('\n') {
            let (key, value) = line.split_once('=')?;
            if !INDEPENDENT_FIELDS.contains(&key) || fields.insert(key, value).is_some() {
                return None;
            }
        }
        if fields.len() != INDEPENDENT_FIELDS.len()
            || fields["kind"] != "build"
            || fields["purpose"] != purpose
            || fields["pstart_utc"].is_empty()
            || !fields["pid"].bytes().all(|byte| byte.is_ascii_digit())
        {
            return None;
        }
        let pid = fields["pid"].parse::<u32>().ok().filter(|&pid| pid != 0)?;
        holder_is_gone(pid, fields["pstart_utc"]).then_some(pid)
    }
    #[cfg(not(unix))]
    {
        let _ = (root, purpose);
        None
    }
}

// Trust: EW-9 (22). The bytes of `directory/info`, opened through the directory without
// following a link at either name, and without blocking on a FIFO put there.
#[cfg(unix)]
fn read_holder_record(directory: &Path) -> Option<String> {
    use std::io::Read;
    use std::os::fd::{AsRawFd, FromRawFd};
    use std::os::unix::fs::MetadataExt;
    let directory = open_directory(directory).ok()?;
    let flags = libc::O_RDONLY | libc::O_NOFOLLOW | libc::O_NONBLOCK | libc::O_CLOEXEC;
    // SAFETY: a valid directory descriptor and a NUL-terminated name; the result is owned.
    let fd = unsafe { libc::openat(directory.as_raw_fd(), c"info".as_ptr(), flags) };
    if fd < 0 {
        return None;
    }
    // SAFETY: `fd` was just opened here and nothing else owns it.
    let file = unsafe { fs::File::from_raw_fd(fd) };
    let metadata = file.metadata().ok()?;
    // SAFETY: `geteuid` cannot fail.
    if !metadata.is_file() || metadata.nlink() != 1 || metadata.uid() != unsafe { libc::geteuid() }
    {
        return None;
    }
    let mut bytes = Vec::new();
    file.take(RECORD_LIMIT + 1).read_to_end(&mut bytes).ok()?;
    if bytes.len() as u64 > RECORD_LIMIT {
        return None;
    }
    String::from_utf8(bytes).ok()
}

// Trust: EW-9 (22). The lock script's `pid_is_live`, negated, for a record that carries a
// non-empty `pstart_utc`: `kill(2)`'s `ESRCH` is the only "no process" answer (`EPERM` is
// a process of another user, judged by its start), and a start `ps` will not give is no
// verdict. A process that exits between the two calls is therefore not called gone.
#[cfg(unix)]
fn holder_is_gone(pid: u32, start_utc: &str) -> bool {
    holder_is_gone_by(pid, start_utc, |pid| ps_utc("lstart=", &pid.to_string()))
}

// Trust: EW-9 (22). `holder_is_gone` with the start reader passed in, so a `ps` that does
// not answer can be tested against a live process.
#[cfg(unix)]
fn holder_is_gone_by(
    pid: u32,
    start_utc: &str,
    start_of: impl FnOnce(u32) -> Result<String, String>,
) -> bool {
    let Ok(raw) = libc::pid_t::try_from(pid) else { return false };
    // SAFETY: signal 0 sends nothing; it asks only whether `raw` names a process.
    if unsafe { libc::kill(raw, 0) } != 0 {
        match std::io::Error::last_os_error().raw_os_error() {
            Some(libc::ESRCH) => return true,
            Some(libc::EPERM) => {}
            _ => return false,
        }
    }
    start_of(pid).is_ok_and(|now| now != start_utc)
}

impl Drop for BuildLease {
    fn drop(&mut self) {
        // Trust: keep durable ownership until the validated outer owner has
        // stopped descendants. It checks our PID/start and the exact handoff
        // token/bytes before release while our leader PID is still unreaped.
        // If that parent dies, retain the holder rather than unlocking writers.
        if self.parent_managed || std::process::id() != self.owner {
            return;
        }
        // A native writer can survive an unwinding/early-returning owner just
        // as it can survive x.py. The shared native manager retains/adopts it;
        // any uncertain observation keeps this original durable holder intact.
        #[cfg(any(target_os = "macos", target_os = "linux"))]
        {
            let released = management::Manager::release_original(self);
            #[cfg(test)]
            if let Err(error) = &released {
                eprintln!(
                    "native original holder retained at {}: {error}",
                    self.root.physical.display()
                );
            }
            let _ = released;
        }
        // Other platforms retain their original guard semantics. Native writer
        // discovery has not been implemented or qualified on those platforms.
        #[cfg(not(any(target_os = "macos", target_os = "linux")))]
        {
            if self.root.check_current().is_err() {
                return;
            }
            let Ok(_namespace) = NamespaceGuard::acquire(&self.root.physical) else { return };
            if self.check_current_locked().is_ok() {
                let _ = fs::remove_file(self.directory.join("info"));
                let _ = fs::remove_dir(&self.directory);
            }
        }
    }
}

// Unix-only identity fields remain unobserved where acquisition is Unsupported.
#[cfg_attr(not(unix), allow(dead_code))]
struct Root {
    logical: PathBuf,
    physical: PathBuf,
    logical_identity: fs::Metadata,
    identity: fs::Metadata,
    file: fs::File,
}

enum ExpectedRootError {
    Current(String),
    Selection(String),
}

impl Root {
    fn check_expected(&self, expected: &Path) -> Result<(), String> {
        self.check_expected_kind(expected).map_err(|error| match error {
            ExpectedRootError::Current(error) | ExpectedRootError::Selection(error) => error,
        })
    }

    fn check_expected_kind(&self, expected: &Path) -> Result<(), ExpectedRootError> {
        self.check_expected_during(|| {
            if fs::canonicalize(expected).map_err(|error| error.to_string())? != self.physical
                || !same_inode(&self.identity, fs::metadata(expected).ok().as_ref())
            {
                return Err("requested repository is not the original held root".into());
            }
            Ok(())
        })
    }

    fn check_expected_during(
        &self,
        select: impl FnOnce() -> Result<(), String>,
    ) -> Result<(), ExpectedRootError> {
        self.check_current().map_err(ExpectedRootError::Current)?;
        let selected = select();
        // A failed selector cannot hide observed drift of the original root.
        self.check_current().map_err(ExpectedRootError::Current)?;
        selected.map_err(ExpectedRootError::Selection)
    }

    fn open(path: &Path) -> Result<Self, String> {
        let logical = if path.is_absolute() {
            path.to_owned()
        } else {
            std::env::current_dir().map_err(|e| e.to_string())?.join(path)
        };
        let logical_identity = fs::symlink_metadata(&logical).map_err(|e| e.to_string())?;
        let physical = fs::canonicalize(&logical).map_err(|e| e.to_string())?;
        let file = open_directory(&physical)?;
        let identity = file.metadata().map_err(|e| e.to_string())?;
        let root = Self { logical, physical, logical_identity, identity, file };
        root.check_current()?;
        Ok(root)
    }

    fn check_current(&self) -> Result<(), String> {
        #[cfg(unix)]
        {
            use std::os::unix::fs::MetadataExt;
            let logical = fs::symlink_metadata(&self.logical).map_err(|e| e.to_string())?;
            if logical.dev() != self.logical_identity.dev()
                || logical.ino() != self.logical_identity.ino()
                || logical.mode() != self.logical_identity.mode()
                || fs::canonicalize(&self.logical).map_err(|e| e.to_string())? != self.physical
                || !same_inode(&self.identity, fs::symlink_metadata(&self.physical).ok().as_ref())
                || !same_inode(&self.identity, self.file.metadata().ok().as_ref())
            {
                return Err("the original build holder root or its logical mapping changed".into());
            }
            Ok(())
        }
        #[cfg(not(unix))]
        {
            Err("checked build holder identity requires Unix".into())
        }
    }
}

/// Creates a holder directory with mode 0755 less the umask, never group or
/// other writable. `fs::create_dir` asks for 0777 less the umask: 0755 under
/// the usual 022, but 0775 under 002, a Linux login default (user private
/// groups), and every `management` read refuses a group-writable holder
/// directory. Under that umask a Manager acquisition refused the holder it had
/// just published, and a BuildLease acquisition succeeded but its holder could
/// be neither read nor released, not even by its own Drop, which discards the
/// error and so kept the holder. Elsewhere no mode applies, so no builder is
/// kept mutable for one (`unused_mut` under `-D warnings`).
fn create_holder_directory(directory: &Path) -> std::io::Result<()> {
    #[cfg(unix)]
    {
        use std::os::unix::fs::DirBuilderExt as _;
        fs::DirBuilder::new().mode(0o755).create(directory)
    }
    #[cfg(not(unix))]
    {
        fs::create_dir(directory)
    }
}

fn open_directory(path: &Path) -> Result<fs::File, String> {
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        fs::OpenOptions::new()
            .read(true)
            .custom_flags(libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_NONBLOCK | libc::O_CLOEXEC)
            .open(path)
            .map_err(|e| e.to_string())
    }
    #[cfg(not(unix))]
    {
        let _ = path;
        Err("checked build holder identity requires Unix".into())
    }
}

#[cfg(unix)]
fn same_inode(expected: &fs::Metadata, current: Option<&fs::Metadata>) -> bool {
    use std::os::unix::fs::MetadataExt;
    current.is_some_and(|current| {
        expected.dev() == current.dev()
            && expected.ino() == current.ino()
            && expected.mode() == current.mode()
            && expected.uid() == current.uid()
            && expected.file_type() == current.file_type()
            && !current.file_type().is_symlink()
    })
}

#[cfg(not(unix))]
fn same_inode(_: &fs::Metadata, _: Option<&fs::Metadata>) -> bool {
    false
}

fn parent_handoff() -> Result<Option<(String, String, String)>, String> {
    const KEYS: [&str; 3] = [
        "TRUST_NATIVE_REPO_PARENT_PID",
        "TRUST_NATIVE_REPO_PARENT_START",
        "TRUST_NATIVE_REPO_PARENT_TOKEN",
    ];
    // Trust: EW18-LOCKUTC-1. The parent's zone-free start, sent beside the zoned
    // `..._START` by a parent that has it. The zoned value was the parent's
    // `lstart` in the parent's TZ and locale, compared with ours in ours, so a
    // child whose TZ or locale differed refused its actual live parent. When this
    // is set it alone identifies the parent; when it is absent the zoned value is
    // compared exactly as before. `..._START` is still required and is still what
    // the record's `release_parent_start` carries: the parent compares that field
    // with its own copy of the same string, which no zone can change.
    const START_UTC: &str = "TRUST_NATIVE_REPO_PARENT_START_UTC";
    let values = KEYS.map(std::env::var_os);
    let start_utc = std::env::var_os(START_UTC);
    if values.iter().all(Option::is_none) && start_utc.is_none() {
        return Ok(None);
    }
    let start_utc = start_utc
        .map(|value| {
            value
                .into_string()
                .map_err(|_| format!("non-UTF-8 native release handoff: {START_UTC}"))
        })
        .transpose()?;
    let mut values = values.into_iter().enumerate().map(|(index, value)| {
        value
            .ok_or_else(|| format!("incomplete native release handoff: {}", KEYS[index]))?
            .into_string()
            .map_err(|_| format!("non-UTF-8 native release handoff: {}", KEYS[index]))
    });
    let parent = values.next().unwrap()?;
    let start = values.next().unwrap()?;
    let token = values.next().unwrap()?;
    let own = std::process::id().to_string();
    // Trust: a present but empty zone-free start identifies nothing, so it is
    // refused (fail-closed), never replaced by the zoned comparison. A closure
    // keeps the checks in their original order.
    let start_differs = || -> Result<bool, String> {
        Ok(match &start_utc {
            Some(start_utc) => start_utc.is_empty() || ps_utc("lstart=", &parent)? != *start_utc,
            None => ps("lstart=", &parent)? != start,
        })
    };
    if parent.parse::<u32>().ok().is_none_or(|pid| pid == 0)
        || ps("ppid=", &own)? != parent
        || start_differs()?
        || ps("stat=", &parent)?.starts_with('Z')
        || !token.starts_with("trust-native-repo-owner-")
        || token.len() <= "trust-native-repo-owner-".len()
        || token.len() > 128
        || !token.bytes().all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'-' | b'_'))
    {
        return Err("native release handoff does not identify our actual live parent".into());
    }
    Ok(Some((parent, start, token)))
}

fn ps(field: &str, pid: &str) -> Result<String, String> {
    run_ps(Command::new("ps"), field, pid)
}

// Trust: EW18-LOCKUTC-1. `ps` with no time zone and no locale: LC_ALL=C overrides
// LANG and every LC_* variable, and TZ=UTC0 is a POSIX zone spec that needs no
// zoneinfo file, so `lstart` reads the same in every caller's environment.
fn ps_utc(field: &str, pid: &str) -> Result<String, String> {
    let mut command = Command::new("ps");
    command.env("LC_ALL", "C").env("TZ", "UTC0").env_remove("LANG").env_remove("LC_TIME");
    run_ps(command, field, pid)
}

fn run_ps(mut command: Command, field: &str, pid: &str) -> Result<String, String> {
    let output = command.args(["-o", field, "-p", pid]).output().map_err(|e| e.to_string())?;
    let value = String::from_utf8(output.stdout).map_err(|e| e.to_string())?;
    if !output.status.success() || value.trim().is_empty() {
        return Err("cannot establish the native build lock holder's process identity".into());
    }
    Ok(value.trim().to_owned())
}

#[cfg(all(test, unix))]
mod tests;
