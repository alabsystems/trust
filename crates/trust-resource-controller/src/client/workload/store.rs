//! Original host-owned discovery locator captured before user configuration.
//! It opens nothing and grants no resource. The original store, actual native
//! ancestor, image/backing, SDK and workload context checks remain mandatory.
use std::os::unix::fs::MetadataExt as _;
use std::path::PathBuf;
use std::sync::Arc;

use super::*;

pub struct PendingHostStore(Option<(RawFd, FileIdentity)>);
pub struct EarlyHostStore(Option<(OwnedFd, FileIdentity)>);
impl PendingHostStore {
    pub fn is_present(&self) -> bool {
        self.0.is_some()
    }
}
impl EarlyHostStore {
    pub fn is_present(&self) -> bool {
        self.0.is_some()
    }
    /// Prefer actual inherited control originals. A selected pin never falls
    /// back to opening a book/store if any native check fails. The independent
    /// original Store locator must identify the SAME retained root.
    pub fn discover_with_control(
        self,
        control: super::control_pin::EarlyHostControl,
        deadline: Instant,
    ) -> io::Result<crate::client::Client> {
        let Some(pin) = control.into_pin(deadline)? else {
            return self.discover(deadline);
        };
        let Some((original, before)) = self.0 else {
            return Err(refused());
        };
        use std::os::fd::AsFd as _;
        if directory(original.as_raw_fd())? != before
            || !pin.same_original_store_directory(original.as_fd())?
        {
            return Err(refused());
        }
        pin.validate(deadline)?;
        Ok(crate::client::Client::from_helper(Arc::new(pin)))
    }
    /// No retry or fallback after a selected locator fails. The original
    /// independently configured host selects this directory, never Invocation40.
    pub fn discover(self, deadline: Instant) -> io::Result<crate::client::Client> {
        let Some((original, identity)) = self.0 else {
            return crate::client::Client::discover(deadline);
        };
        if directory(original.as_raw_fd())? != identity {
            return Err(refused());
        }
        let original_path = path(original.as_raw_fd())?;
        let check = || {
            if directory(original.as_raw_fd())? != identity
                || path(original.as_raw_fd())? != original_path
                || std::fs::symlink_metadata(&original_path)
                    .map(|meta| FileIdentity { device: meta.dev(), inode: meta.ino() })?
                    != identity
            {
                return Err(refused());
            }
            Ok(())
        };
        check()?;
        let store = trust_resource_provenance::Store::open_at(&original_path)?;
        use std::os::fd::AsFd as _;
        if !store.same_original_directory(original.as_fd())? {
            return Err(refused());
        }
        check()?;
        let host = store.connect_ancestor(deadline)?;
        check()?;
        let helper = host.into_helper(deadline)?;
        check()?;
        Ok(crate::client::Client::from_helper(Arc::new(helper)))
    }
}
fn directory(fd: RawFd) -> io::Result<FileIdentity> {
    let mut meta: libc::stat = unsafe { std::mem::zeroed() };
    if unsafe { libc::fstat(fd, &mut meta) } != 0 {
        return Err(io::Error::last_os_error());
    }
    if meta.st_mode & libc::S_IFMT != libc::S_IFDIR
        || meta.st_mode & 0o077 != 0
        || meta.st_uid != unsafe { libc::geteuid() }
    {
        return Err(refused());
    }
    Ok(FileIdentity { device: meta.st_dev as u64, inode: meta.st_ino as u64 })
}
pub fn snapshot_host_store() -> io::Result<PendingHostStore> {
    let Some(value) = std::env::var_os(host::HOST_STORE_FD_ENV) else {
        return Ok(PendingHostStore(None));
    };
    snapshot(value.to_str().ok_or_else(refused)?)
}
/// Snapshot the explicit original-store helper locator without opening or
/// allocating descriptions. This does not choose any account fallback.
pub fn snapshot_host_store_descriptor(fd: u32) -> io::Result<PendingHostStore> {
    if fd < 6 {
        return Err(refused());
    }
    snapshot(&fd.to_string())
}
/// # Safety
/// Only the exact fresh native helper entry may consume this exclusively
/// inherited directory. Its slot must be disjoint from stdio, control, proof,
/// SDK and every advertised source; no intervening code may close/reuse it.
/// Validate all source slots before discovery/imports may allocate any FD.
pub unsafe fn capture_host_store_descriptor(
    pending: PendingHostStore,
) -> io::Result<EarlyHostStore> {
    if !pending.is_present() {
        return Err(refused());
    }
    unsafe { take(pending) }
}
fn snapshot(value: &str) -> io::Result<PendingHostStore> {
    let fd: RawFd = value.parse().map_err(|_| refused())?;
    if fd < 3 || fd == 5 || fd.to_string() != value {
        return Err(refused());
    }
    Ok(PendingHostStore(Some((fd, directory(fd)?))))
}
/// # Safety
/// The actual host exclusively maps this directory descriptor disjoint from
/// stdio, SDK, GNU and CPU. Snapshot all bootstrap slots before any allocator;
/// capture after fixed importers, before config/threads/children. No intervening
/// code may close/reuse it; no other environment reader may run during capture.
pub unsafe fn capture_host_store(pending: PendingHostStore) -> io::Result<EarlyHostStore> {
    unsafe { std::env::remove_var(host::HOST_STORE_FD_ENV) };
    unsafe { take(pending) }
}
unsafe fn take(pending: PendingHostStore) -> io::Result<EarlyHostStore> {
    let Some((fd, before)) = pending.0 else {
        return Ok(EarlyHostStore(None));
    };
    let owned = unsafe { OwnedFd::from_raw_fd(fd) };
    if directory(owned.as_raw_fd())? != before {
        return Err(refused());
    }
    let flags = unsafe { libc::fcntl(fd, libc::F_GETFD) };
    if flags < 0 || unsafe { libc::fcntl(fd, libc::F_SETFD, flags | libc::FD_CLOEXEC) } != 0 {
        return Err(io::Error::last_os_error());
    }
    Ok(EarlyHostStore(Some((owned, before))))
}
#[cfg(target_os = "macos")]
fn path(fd: RawFd) -> io::Result<PathBuf> {
    use std::os::unix::ffi::OsStringExt as _;
    let mut bytes = [0u8; 4096];
    if unsafe { libc::fcntl(fd, libc::F_GETPATH, bytes.as_mut_ptr()) } != 0 {
        return Err(io::Error::last_os_error());
    }
    let end = bytes.iter().position(|byte| *byte == 0).ok_or_else(refused)?;
    let path = PathBuf::from(std::ffi::OsString::from_vec(bytes[..end].to_vec()));
    if !path.is_absolute() {
        return Err(refused());
    }
    Ok(path)
}
#[cfg(target_os = "linux")]
fn path(fd: RawFd) -> io::Result<PathBuf> {
    let path = std::fs::read_link(format!("/proc/self/fd/{fd}"))?;
    if !path.is_absolute() || path.as_os_str().as_encoded_bytes().len() > 4096 {
        return Err(refused());
    }
    Ok(path)
}
#[cfg(test)]
mod tests {
    use std::os::fd::AsFd as _;
    use std::os::unix::fs::OpenOptionsExt as _;

    use super::*;
    #[test]
    fn original_directory_locator_is_owned_close_on_exec_and_never_a_cpu_or_sdk_slot() {
        let root = super::super::tests::root();
        let file = std::fs::OpenOptions::new()
            .read(true)
            .custom_flags(libc::O_DIRECTORY | libc::O_NOFOLLOW)
            .open(&root)
            .unwrap();
        let raw = unsafe { libc::fcntl(file.as_raw_fd(), libc::F_DUPFD_CLOEXEC, 6) };
        assert!(raw >= 6);
        let pending = snapshot(&raw.to_string()).unwrap();
        let early = unsafe { take(pending) }.unwrap();
        assert!(early.is_present());
        assert_ne!(unsafe { libc::fcntl(raw, libc::F_GETFD) } & libc::FD_CLOEXEC, 0);
        assert_eq!(path(raw).unwrap(), root.canonicalize().unwrap());
        assert!(snapshot("5").is_err());
        assert!(snapshot("2").is_err());
        assert!(snapshot("03").is_err());
        drop(early);
        assert_eq!(unsafe { libc::fcntl(raw, libc::F_GETFD) }, -1);
        assert!(
            snapshot(&std::fs::File::open("/dev/null").unwrap().as_raw_fd().to_string()).is_err()
        );
        // The locator alone cannot make a host/store appear or fall back to
        // the canonical account controller when these original inputs refuse.
        let pending =
            PendingHostStore(Some((file.as_raw_fd(), directory(file.as_raw_fd()).unwrap())));
        let borrowed = EarlyHostStore(Some((
            file.as_fd().try_clone_to_owned().unwrap(),
            pending.0.unwrap().1,
        )));
        assert!(borrowed.discover(Instant::now() + std::time::Duration::from_secs(1)).is_err());
        drop(file);
        std::fs::remove_dir_all(root).unwrap();
    }
}
