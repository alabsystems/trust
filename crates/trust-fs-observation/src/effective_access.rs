// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

//! Bounded effective-credential execute-access observations for Unix paths.
//!
//! This is data, not an execution permission, an executable resolver, or an
//! `execve` success guarantee. A consumer must pair fresh observations with the
//! content observer's live window and qualify its actual transport on the same
//! host. Credentials must remain fixed throughout that transport: endpoint
//! equality cannot exclude an intervening credential change. Mount flags, MAC
//! policy, interpreters, loaders and subprocesses are outside this observation.
//! The consumer must also hold security namespaces and capability state fixed;
//! the serialized credential identity contains only the IDs/groups below.
//! Linux `AT_EACCESS` retains filesystem IDs: consumers must exclude overridden
//! fsuid/fsgid profiles or independently capture and hold those IDs fixed. Real,
//! effective and saved ID equality does not establish that condition. This
//! primitive does not call credential setters as getters or inspect procfs.
//!
//! Only macOS's kernel `faccessat(AT_EACCESS)` and Linux's kernel `faccessat2`
//! are supported. There is no real-ID check, libc ACL emulation, or fallback
//! when the effective-credential operation is unavailable. Current-process
//! set-ID profiles are refused. Serialized values cannot restore a live window.

use std::path::PathBuf;

use anyhow::Result;
#[cfg(any(target_os = "macos", target_os = "linux"))]
use anyhow::ensure;
use serde::{Deserialize, Serialize};

/// Maximum paths in one ordered access observation.
pub const MAX_PATHS: usize = 1_024;
/// Maximum bytes in one raw absolute Unix path.
pub const MAX_PATH_BYTES: usize = 32 * 1_024;
/// Maximum sum of raw path lengths in one observation.
pub const MAX_TOTAL_PATH_BYTES: usize = 1024 * 1024;
/// Maximum supplementary groups in the supported credential profile.
pub const MAX_GROUPS: usize = 1_024;

/// The kernel's effective-credential execute-access answer, not file validity.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum Outcome {
    Allowed,
    Denied,
    Missing,
}

/// Read-only credential data. Saved IDs and tainted profiles must pass capture
/// admission; decoding this data does not perform that admission again.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Credentials {
    uid: u32,
    euid: u32,
    gid: u32,
    egid: u32,
    supplementary_groups: Vec<u32>,
}

impl Credentials {
    pub fn uid(&self) -> u32 {
        self.uid
    }

    pub fn euid(&self) -> u32 {
        self.euid
    }

    pub fn gid(&self) -> u32 {
        self.gid
    }

    pub fn egid(&self) -> u32 {
        self.egid
    }

    /// Sorted, with the kernel-returned multiplicity retained.
    pub fn supplementary_groups(&self) -> &[u32] {
        &self.supplementary_groups
    }
}

/// One raw, non-canonicalized Unix path and its effective-access answer.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Entry {
    path: Vec<u8>,
    outcome: Outcome,
}

impl Entry {
    pub fn path_bytes(&self) -> &[u8] {
        &self.path
    }

    pub fn outcome(&self) -> Outcome {
        self.outcome
    }
}

/// Ordered data from one bounded capture on the named OS. It contains no file
/// descriptors, continuity stamps, execution permission or proof authority.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Snapshot {
    version: u32,
    host_os: String,
    credentials: Credentials,
    entries: Vec<Entry>,
}

impl Snapshot {
    /// Check decoded data shape, never live access or credential admission.
    pub fn valid(&self) -> bool {
        self.version == 1
            && matches!(self.host_os.as_str(), "macos" | "linux")
            && self.host_os == std::env::consts::OS
            && self.credentials.uid == self.credentials.euid
            && self.credentials.gid == self.credentials.egid
            && self.credentials.supplementary_groups.len() <= MAX_GROUPS
            && self
                .credentials
                .supplementary_groups
                .windows(2)
                .all(|g| g[0] <= g[1])
            && self.entries.len() <= MAX_PATHS
            && self.entries.iter().all(|entry| {
                entry.path.starts_with(b"/")
                    && entry.path.len() <= MAX_PATH_BYTES
                    && !entry.path.contains(&0)
            })
            && self
                .entries
                .iter()
                .map(|entry| entry.path.len())
                .sum::<usize>()
                <= MAX_TOTAL_PATH_BYTES
    }

    pub fn host_os(&self) -> &str {
        &self.host_os
    }

    pub fn credentials(&self) -> &Credentials {
        &self.credentials
    }

    pub fn entries(&self) -> &[Entry] {
        &self.entries
    }
}

/// Capture ordered raw absolute paths using effective credentials. Every input
/// is admitted before any access query. Any unsupported/error result other
/// than EACCES or ENOENT refuses the entire observation.
pub fn capture(paths: &[PathBuf]) -> Result<Snapshot> {
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    {
        capture_with(paths, platform::credentials, platform::check)
    }
    #[cfg(not(any(target_os = "macos", target_os = "linux")))]
    {
        let _ = paths;
        anyhow::bail!("effective execute-access observation is unavailable on this host")
    }
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
fn capture_with(
    paths: &[PathBuf],
    mut credentials: impl FnMut() -> Result<Credentials>,
    mut check: impl FnMut(&std::ffi::CStr) -> std::io::Result<Outcome>,
) -> Result<Snapshot> {
    use std::ffi::CString;
    use std::os::unix::ffi::OsStrExt as _;

    ensure!(paths.len() <= MAX_PATHS, "too many effective-access paths");
    let mut raw_paths = Vec::new();
    raw_paths.try_reserve_exact(paths.len())?;
    let mut total = 0_usize;
    for path in paths {
        let raw = path.as_os_str().as_bytes();
        ensure!(path.is_absolute(), "effective-access path is not absolute");
        ensure!(
            raw.len() <= MAX_PATH_BYTES,
            "effective-access path is too long"
        );
        total = total
            .checked_add(raw.len())
            .ok_or_else(|| anyhow::anyhow!("path sum overflow"))?;
        ensure!(
            total <= MAX_TOTAL_PATH_BYTES,
            "effective-access path sum is too large"
        );
        raw_paths.push(CString::new(raw)?);
    }
    let before = credentials()?;
    let mut entries = Vec::new();
    entries.try_reserve_exact(raw_paths.len())?;
    for path in raw_paths {
        let outcome = check(&path)?;
        entries.push(Entry {
            path: path.into_bytes(),
            outcome,
        });
    }
    ensure!(
        before == credentials()?,
        "credentials changed during effective-access capture"
    );
    Ok(Snapshot {
        version: 1,
        host_os: std::env::consts::OS.to_owned(),
        credentials: before,
        entries,
    })
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
mod platform {
    use std::ffi::CStr;
    use std::io;

    #[cfg(any(target_os = "linux", test))]
    use anyhow::Context as _;
    use anyhow::{Result, ensure};

    use super::{Credentials, MAX_GROUPS, Outcome};

    pub(super) fn credentials() -> Result<Credentials> {
        let before = ids()?;
        // SAFETY: A zero length makes the null group pointer valid.
        let count = unsafe { libc::getgroups(0, std::ptr::null_mut()) };
        ensure!(
            count >= 0,
            "getgroups size failed: {}",
            io::Error::last_os_error()
        );
        let count = usize::try_from(count)?;
        ensure!(count <= MAX_GROUPS, "too many supplementary groups");
        let mut groups = Vec::<libc::gid_t>::new();
        groups.try_reserve_exact(count)?;
        groups.resize(count, 0);
        // SAFETY: The initialized buffer has count gid_t entries; for count
        // zero getgroups only queries the current size and ignores its pointer.
        let actual = unsafe { libc::getgroups(count as libc::c_int, groups.as_mut_ptr()) };
        ensure!(
            actual >= 0,
            "getgroups failed: {}",
            io::Error::last_os_error()
        );
        ensure!(
            usize::try_from(actual)? == count,
            "supplementary groups changed during capture"
        );
        ensure!(
            before == ids()?,
            "credential IDs changed while reading groups"
        );
        groups.sort_unstable();
        Ok(Credentials {
            uid: before[0],
            euid: before[1],
            gid: before[2],
            egid: before[3],
            supplementary_groups: groups,
        })
    }

    #[cfg(target_os = "macos")]
    fn ids() -> Result<[u32; 4]> {
        // SAFETY: These queries take no pointers and do not mutate credentials.
        let (uid, euid, gid, egid, tainted) = unsafe {
            (
                libc::getuid(),
                libc::geteuid(),
                libc::getgid(),
                libc::getegid(),
                libc::issetugid(),
            )
        };
        ensure!(
            tainted == 0 && uid == euid && gid == egid,
            "set-ID credential profile is unsupported"
        );
        Ok([uid, euid, gid, egid])
    }

    #[cfg(target_os = "linux")]
    fn ids() -> Result<[u32; 4]> {
        let (mut uid, mut euid, mut saved_uid) = (0, 0, 0);
        let (mut gid, mut egid, mut saved_gid) = (0, 0, 0);
        // SAFETY: All output pointers refer to correctly typed live locals.
        let user_result = unsafe { libc::getresuid(&mut uid, &mut euid, &mut saved_uid) };
        if user_result != 0 {
            return Err(io::Error::last_os_error()).context("getresuid failed");
        }
        // SAFETY: All output pointers refer to correctly typed live locals.
        let group_result = unsafe { libc::getresgid(&mut gid, &mut egid, &mut saved_gid) };
        if group_result != 0 {
            return Err(io::Error::last_os_error()).context("getresgid failed");
        }
        ensure!(
            uid == euid && uid == saved_uid && gid == egid && gid == saved_gid,
            "set-ID credential profile is unsupported"
        );
        require_nonsecure_auxv(|| {
            // SAFETY: __errno_location returns this thread's writable errno
            // slot. Read it immediately after the read-only aux-vector query;
            // zero is admitted only when the query also reports no error.
            unsafe {
                let errno = libc::__errno_location();
                *errno = 0;
                let value = libc::getauxval(libc::AT_SECURE);
                (value, *errno)
            }
        })?;
        Ok([uid, euid, gid, egid])
    }

    #[cfg(any(target_os = "linux", test))]
    pub(super) fn require_nonsecure_auxv(
        query: impl FnOnce() -> (libc::c_ulong, libc::c_int),
    ) -> Result<()> {
        let (value, errno) = query();
        if errno != 0 {
            return Err(io::Error::from_raw_os_error(errno)).context("AT_SECURE query unavailable");
        }
        ensure!(
            value == 0,
            "secure-execution credential profile is unsupported"
        );
        Ok(())
    }

    pub(super) fn check(path: &CStr) -> io::Result<Outcome> {
        #[cfg(target_os = "macos")]
        // SAFETY: path is a NUL-terminated absolute pathname. The kernel
        // evaluates X_OK with effective credentials; the operation is read-only.
        let result =
            unsafe { libc::faccessat(libc::AT_FDCWD, path.as_ptr(), libc::X_OK, libc::AT_EACCESS) };
        #[cfg(target_os = "linux")]
        // SAFETY: This calls the kernel's four-argument faccessat2 directly,
        // avoiding libc real-ID or ACL-emulating fallbacks on older kernels.
        let result = unsafe {
            libc::syscall(
                libc::SYS_faccessat2,
                libc::AT_FDCWD,
                path.as_ptr(),
                libc::X_OK,
                libc::AT_EACCESS,
            )
        };
        if result == 0 {
            return Ok(Outcome::Allowed);
        }
        classify_error(io::Error::last_os_error())
    }

    pub(super) fn classify_error(error: io::Error) -> io::Result<Outcome> {
        match error.raw_os_error() {
            Some(libc::EACCES) => Ok(Outcome::Denied),
            Some(libc::ENOENT) => Ok(Outcome::Missing),
            _ => Err(error),
        }
    }
}

#[cfg(all(test, any(target_os = "macos", target_os = "linux")))]
mod tests {
    use std::ffi::OsString;
    use std::fs;
    use std::os::unix::ffi::OsStringExt as _;
    use std::os::unix::fs::PermissionsExt as _;
    use std::path::PathBuf;

    use super::*;

    #[test]
    fn executable_mode_change_and_missing_path_are_observed() {
        let world = tempfile::tempdir().unwrap();
        let file = world.path().join("tool");
        let missing = world.path().join("missing");
        fs::write(&file, b"fixed bytes").unwrap();
        fs::set_permissions(&file, fs::Permissions::from_mode(0o700)).unwrap();
        let paths = [file.clone(), missing.clone(), file.clone()];
        let before = capture(&paths).unwrap();
        assert_eq!(before.entries[0].outcome, Outcome::Allowed);
        assert_eq!(before.entries[1].outcome, Outcome::Missing);
        assert_eq!(before.entries[2], before.entries[0]);
        assert!(
            before
                .credentials
                .supplementary_groups
                .windows(2)
                .all(|g| g[0] <= g[1])
        );
        fs::set_permissions(&file, fs::Permissions::from_mode(0o600)).unwrap();
        let after = capture(&paths).unwrap();
        assert_eq!(after.entries[0].outcome, Outcome::Denied);
        assert_eq!(before.credentials, after.credentials);
        assert_eq!(fs::read(&file).unwrap(), b"fixed bytes");
    }

    #[test]
    fn raw_path_order_and_serialized_data_are_preserved() {
        let world = tempfile::tempdir().unwrap();
        let raw_name = OsString::from_vec(vec![b't', 0xff, b'l']);
        let raw_path = world.path().join(raw_name);
        let paths = [raw_path.clone(), world.path().join("absent"), raw_path];
        // Filesystems may reject non-UTF8 names before ENOENT. Exercise raw
        // data preservation independently of that filesystem-specific error.
        let snapshot =
            capture_with(&paths, platform::credentials, |_| Ok(Outcome::Missing)).unwrap();
        assert_eq!(snapshot.entries[0], snapshot.entries[2]);
        assert!(snapshot.entries[0].path.contains(&0xff));
        let encoded = serde_json::to_vec(&snapshot).unwrap();
        let restored: Snapshot = serde_json::from_slice(&encoded).unwrap();
        assert_eq!(restored, snapshot);
        assert_eq!(restored.entries().len(), 3);
        let mut extra = serde_json::to_value(&snapshot).unwrap();
        extra["permission_grant"] = true.into();
        assert!(serde_json::from_value::<Snapshot>(extra).is_err());
    }

    #[test]
    fn path_admission_is_bounded_and_precedes_kernel_queries() {
        let before = platform::credentials;
        let mut check = |_: &std::ffi::CStr| -> std::io::Result<Outcome> {
            panic!("invalid input reached access query")
        };
        assert!(capture_with(&[PathBuf::from("relative")], before, &mut check).is_err());
        assert!(capture_with(&[PathBuf::from("/nul\0path")], before, &mut check).is_err());
        assert!(
            capture_with(&vec![PathBuf::from("/"); MAX_PATHS + 1], before, &mut check).is_err()
        );
        let long = PathBuf::from(format!("/{}", "x".repeat(MAX_PATH_BYTES)));
        assert!(capture_with(&[long], before, &mut check).is_err());
        let path = PathBuf::from(format!("/{}", "x".repeat(MAX_PATH_BYTES - 1)));
        assert!(
            capture_with(
                &vec![path; MAX_TOTAL_PATH_BYTES / MAX_PATH_BYTES + 1],
                before,
                &mut check
            )
            .is_err()
        );
    }

    #[test]
    fn credential_changes_and_non_missing_errors_refuse() {
        let original = platform::credentials().unwrap();
        let mut calls = 0;
        let credentials = || {
            calls += 1;
            let mut value = original.clone();
            if calls == 2 {
                value.supplementary_groups.push(u32::MAX);
            }
            Ok(value)
        };
        assert!(
            capture_with(&[PathBuf::from("/absent")], credentials, |_| Ok(
                Outcome::Missing
            ))
            .unwrap_err()
            .to_string()
            .contains("credentials changed")
        );
        for errno in [
            libc::ENOSYS,
            libc::EINVAL,
            libc::ENOTDIR,
            libc::ELOOP,
            libc::EPERM,
        ] {
            assert!(platform::classify_error(std::io::Error::from_raw_os_error(errno)).is_err());
        }
        assert_eq!(
            platform::classify_error(std::io::Error::from_raw_os_error(libc::ENOENT)).unwrap(),
            Outcome::Missing
        );
        assert_eq!(
            platform::classify_error(std::io::Error::from_raw_os_error(libc::EACCES)).unwrap(),
            Outcome::Denied
        );
    }

    #[test]
    fn secure_profile_query_distinguishes_valid_zero_from_missing_or_error() {
        assert!(platform::require_nonsecure_auxv(|| (0, 0)).is_ok());
        assert!(platform::require_nonsecure_auxv(|| (1, 0)).is_err());
        for errno in [libc::ENOENT, libc::EIO] {
            let error = platform::require_nonsecure_auxv(|| (0, errno)).unwrap_err();
            assert!(error.to_string().contains("AT_SECURE query unavailable"));
            assert_eq!(
                error
                    .downcast_ref::<std::io::Error>()
                    .unwrap()
                    .raw_os_error(),
                Some(errno)
            );
        }
        assert!(platform::require_nonsecure_auxv(|| (1, libc::ENOENT)).is_err());
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn acl_execute_denial_changes_access_without_mode_or_content_change() {
        let world = tempfile::tempdir().unwrap();
        let file = world.path().join("tool");
        fs::write(&file, b"fixed bytes").unwrap();
        fs::set_permissions(&file, fs::Permissions::from_mode(0o700)).unwrap();
        let mode = fs::metadata(&file).unwrap().permissions().mode();
        assert_eq!(
            capture(std::slice::from_ref(&file)).unwrap().entries[0].outcome,
            Outcome::Allowed
        );
        let output = std::process::Command::new("/bin/chmod")
            .args(["+a", "everyone deny execute"])
            .arg(&file)
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "owned-file ACL setup failed: {output:?}"
        );
        assert_eq!(fs::metadata(&file).unwrap().permissions().mode(), mode);
        assert_eq!(fs::read(&file).unwrap(), b"fixed bytes");
        assert_eq!(
            capture(&[file]).unwrap().entries[0].outcome,
            Outcome::Denied
        );
    }
}
