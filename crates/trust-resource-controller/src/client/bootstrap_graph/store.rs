//! A separate fixed Bootstrap original-store locator. It cannot reinterpret a
//! workload locator or choose a pool/SDK/backend from request data.
use std::ffi::OsStr;
use std::io;
use std::time::Instant;

use crate::FileIdentity;
use crate::bootstrap_graph::{HOST_STORE_FD_ENV, HOST_STORE_TARGET_FD};
use crate::client::{Client, workload};

pub struct PendingHostStore(Option<(workload::PendingHostStore, FileIdentity)>);
pub struct EarlyHostStore(Option<workload::EarlyHostStore>);
impl PendingHostStore {
    pub fn is_present(&self) -> bool {
        self.0.is_some()
    }
}
impl EarlyHostStore {
    pub fn is_present(&self) -> bool {
        self.0.is_some()
    }
    pub fn discover(self, deadline: Instant) -> io::Result<Client> {
        if Instant::now() >= deadline {
            return Err(io::ErrorKind::TimedOut.into());
        }
        let actual = match self.0 {
            Some(original) => original.discover(deadline),
            None => Client::discover(deadline),
        }?;
        if Instant::now() >= deadline {
            return Err(io::ErrorKind::TimedOut.into());
        }
        Ok(actual)
    }
}
fn refused() -> io::Error {
    io::Error::new(io::ErrorKind::PermissionDenied, "original Bootstrap Host-store locator refused")
}
fn observe() -> io::Result<FileIdentity> {
    let fd = HOST_STORE_TARGET_FD as libc::c_int;
    let mut meta = std::mem::MaybeUninit::<libc::stat>::uninit();
    if unsafe { libc::fstat(fd, meta.as_mut_ptr()) } != 0 {
        return Err(io::Error::last_os_error());
    }
    let meta = unsafe { meta.assume_init() };
    let flags = unsafe { libc::fcntl(fd, libc::F_GETFL) };
    if flags < 0 {
        return Err(io::Error::last_os_error());
    }
    if meta.st_mode & libc::S_IFMT != libc::S_IFDIR
        || meta.st_mode & 0o077 != 0
        || meta.st_uid != unsafe { libc::geteuid() }
        || flags & libc::O_ACCMODE != libc::O_RDONLY
    {
        return Err(refused());
    }
    Ok(FileIdentity { device: meta.st_dev as u64, inode: meta.st_ino })
}

/// Observe before any descriptor allocation, beside SDK/other startup snapshots.
/// A selected failure is final; no alternate number/path or account fallback.
pub fn snapshot_host_store() -> io::Result<PendingHostStore> {
    let selected = std::env::var_os(HOST_STORE_FD_ENV);
    if selected.is_some()
        && [crate::workload::host::HOST_STORE_FD_ENV, crate::workload::host::CPU_SET_FDS_ENV]
            .iter()
            .any(|name| std::env::var_os(name).is_some())
    {
        return Err(refused());
    }
    snapshot(selected.as_deref())
}
fn snapshot(selected: Option<&OsStr>) -> io::Result<PendingHostStore> {
    let Some(selected) = selected else { return Ok(PendingHostStore(None)) };
    if selected != OsStr::new("7") {
        return Err(refused());
    }
    let before = observe()?;
    let actual = workload::snapshot_host_store_descriptor(HOST_STORE_TARGET_FD)?;
    Ok(PendingHostStore(Some((actual, before))))
}

/// # Safety
/// Only the original fixed native Bootstrap entry may consume the exclusively
/// mapped7. Snapshot ALL advertised slots before any importer; between snapshot
/// and capture only the fixed disjoint GNU3/4 and SDK5 importers may run. No
/// logger/config/callback/thread/child may close/reuse7 or read the environment
/// while its locator is removed. No second owner may own this mapped descriptor.
pub unsafe fn capture_host_store(pending: PendingHostStore) -> io::Result<EarlyHostStore> {
    unsafe { std::env::remove_var(HOST_STORE_FD_ENV) };
    let Some((pending, before)) = pending.0 else { return Ok(EarlyHostStore(None)) };
    // Recheck BEFORE taking ownership: a source unexpectedly closed/reused by
    // an earlier importer is refusal, never an invalid-fd owner or new locator.
    if observe()? != before {
        return Err(refused());
    }
    let original = unsafe { workload::capture_host_store_descriptor(pending) }?;
    Ok(EarlyHostStore(Some(original)))
}

#[cfg(test)]
mod tests {
    use std::os::fd::AsRawFd as _;
    use std::os::unix::fs::DirBuilderExt as _;
    use std::time::{Duration, SystemTime, UNIX_EPOCH};

    use super::*;
    #[test]
    fn only_the_distinct_exact_fixed_target_is_selected() {
        assert!(!snapshot(None).unwrap().is_present());
        for value in ["", "3", "4", "5", "6", "07", "+7", "8", "7,8", "/a/store"] {
            assert!(snapshot(Some(OsStr::new(value))).is_err(), "{value}");
        }
        assert_ne!(HOST_STORE_FD_ENV, crate::workload::host::HOST_STORE_FD_ENV);
    }

    #[test]
    fn actual_target7_capture_rejects_closed_or_reused_original_and_never_falls_back() {
        const NAME: &str = "client::bootstrap_graph::store::tests::actual_target7_capture_rejects_closed_or_reused_original_and_never_falls_back";
        const ROLE: &str = "TRUST_BOOTSTRAP_STORE_NATIVE_TEST";
        const MARKER: &str = "BOOTSTRAP_STORE_ASSERTIONS_COMPLETE";
        if std::env::var(ROLE).as_deref() != Ok(NAME) {
            let mut child = std::process::Command::new(std::env::current_exe().unwrap())
                .args(["--exact", NAME, "--nocapture"])
                .env(ROLE, NAME)
                .stdout(std::process::Stdio::piped())
                .stderr(std::process::Stdio::piped())
                .spawn()
                .unwrap();
            let until = Instant::now() + Duration::from_secs(60);
            loop {
                if child.try_wait().unwrap().is_some() {
                    break;
                }
                if Instant::now() >= until {
                    child.kill().unwrap();
                    child.wait().unwrap();
                    panic!("actual Bootstrap store actor did not finish");
                }
                std::thread::sleep(Duration::from_millis(5));
            }
            let actual = child.wait_with_output().unwrap();
            assert!(
                actual.status.success(),
                "{}\n{}",
                String::from_utf8_lossy(&actual.stdout),
                String::from_utf8_lossy(&actual.stderr)
            );
            assert!(String::from_utf8_lossy(&actual.stdout)
                .split_ascii_whitespace()
                .any(|word| word == MARKER));
            return;
        }
        // Own a fresh process table at its inherited limit. Never overwrite a
        // harness/peer descriptor just to force the fixed target into place.
        assert_eq!(unsafe { libc::fcntl(7, libc::F_GETFD) }, -1);
        assert_eq!(io::Error::last_os_error().raw_os_error(), Some(libc::EBADF));
        let root = std::env::temp_dir().join(format!(
            "bootstrap-store-{}-{}",
            std::process::id(),
            SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos()
        ));
        std::fs::DirBuilder::new().mode(0o700).create(&root).unwrap();
        let away_from_target = |file: std::fs::File| {
            if file.as_raw_fd() == 7 {
                let copy = file.try_clone().unwrap();
                drop(file);
                assert_ne!(copy.as_raw_fd(), 7);
                copy
            } else {
                file
            }
        };
        let file = away_from_target(std::fs::File::open(&root).unwrap());
        let original = file.metadata().unwrap();
        let duplicate = || {
            let raw = unsafe { libc::fcntl(file.as_raw_fd(), libc::F_DUPFD_CLOEXEC, 7) };
            assert_eq!(raw, 7, "a fresh mapped slot was not available; no overwrite permitted");
        };
        duplicate();
        let pending = snapshot(Some(OsStr::new("7"))).unwrap();
        let early = unsafe { capture_host_store(pending) }.unwrap();
        assert!(early.is_present());
        assert_ne!(unsafe { libc::fcntl(7, libc::F_GETFD) } & libc::FD_CLOEXEC, 0);
        // A real readonly private directory is still not a Host/store or a
        // grant. Its missing original book refuses; no canonical fallback.
        assert!(early.discover(Instant::now() + Duration::from_secs(1)).is_err());
        assert_eq!(unsafe { libc::fcntl(7, libc::F_GETFD) }, -1);
        duplicate();
        let pending = snapshot(Some(OsStr::new("7"))).unwrap();
        assert_eq!(unsafe { libc::close(7) }, 0);
        assert!(unsafe { capture_host_store(pending) }.is_err());
        duplicate();
        let pending = snapshot(Some(OsStr::new("7"))).unwrap();
        assert_eq!(unsafe { libc::close(7) }, 0);
        let other = away_from_target(std::fs::File::open("/dev/null").unwrap());
        assert_eq!(unsafe { libc::fcntl(other.as_raw_fd(), libc::F_DUPFD_CLOEXEC, 7) }, 7);
        assert!(unsafe { capture_host_store(pending) }.is_err());
        // This replacement was never adopted; only its actual fixture owner
        // closes it. A failed original must not close an unrelated importer.
        assert_ne!(unsafe { libc::fcntl(7, libc::F_GETFD) }, -1);
        assert_eq!(unsafe { libc::close(7) }, 0);
        use std::os::unix::fs::MetadataExt as _;
        assert_eq!(
            (file.metadata().unwrap().dev(), file.metadata().unwrap().ino()),
            (original.dev(), original.ino())
        );
        drop(file);
        std::fs::remove_dir_all(root).unwrap();
        println!("{MARKER}");
    }
}
