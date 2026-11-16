// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Joint early descriptor capture. A locator grants nothing; authenticated
//! Context must later match the actual original inherited SDK lease.
use std::fs::File;
use std::io;
use std::os::fd::{AsRawFd, FromRawFd, RawFd};
use std::sync::OnceLock;

use crate::{Context, SdkCustody};

/// Locator for the descriptor actually mapped by the maintained custodian.
pub const SDK_LEASE_ENV: &str = "ATERM_SDK_LEASE_V3";
#[derive(Clone, Copy, PartialEq, Eq)]
struct Identity {
    device: u64,
    inode: u64,
    uid: u32,
    mode: u32,
    links: u64,
}
/// Snapshot performs no descriptor allocation and cannot reuse GNU slots.
pub struct PendingSdkCapture {
    original: Option<(RawFd, Identity)>,
}
struct Keeper {
    original: RawFd,
    identity: Identity,
    file: File,
}
static KEEPER: OnceLock<Option<Keeper>> = OnceLock::new();
/// Borrow of the actual process-entry owner. No Context/File/locator can
/// construct this; the original global keeper remains held until process exit.
pub(super) struct OriginalSdkKeeper(&'static Keeper);
impl OriginalSdkKeeper {
    pub(super) fn validate(&self, context: &Context) -> io::Result<()> {
        self.0.validate(context.sdk.as_ref().ok_or_else(refused)?)
    }
}
pub(super) fn retain_sdk_keeper(context: &Context) -> io::Result<OriginalSdkKeeper> {
    let keeper = KEEPER.get().and_then(Option::as_ref).ok_or_else(refused)?;
    keeper.validate(context.sdk.as_ref().ok_or_else(refused)?)?;
    Ok(OriginalSdkKeeper(keeper))
}
fn refused() -> io::Error {
    io::Error::new(io::ErrorKind::PermissionDenied, "original inherited SDK lease unavailable")
}
fn identity(fd: RawFd) -> io::Result<Identity> {
    // SAFETY: zero initializes native output storage; fstat observes an existing
    // numeric descriptor without taking ownership or allocating another one.
    let mut stat: libc::stat = unsafe { std::mem::zeroed() };
    // SAFETY: correctly sized writable native stat buffer.
    if unsafe { libc::fstat(fd, &mut stat) } != 0 {
        return Err(io::Error::last_os_error());
    }
    // SAFETY: geteuid only reads this process's effective identity.
    if stat.st_uid != unsafe { libc::geteuid() }
        || stat.st_mode & libc::S_IFMT != libc::S_IFREG
        || stat.st_mode & 0o077 != 0
        || stat.st_nlink != 1
    {
        return Err(refused());
    }
    Ok(Identity {
        device: stat.st_dev as u64,
        inode: stat.st_ino as u64,
        uid: stat.st_uid,
        mode: stat.st_mode as u32,
        links: stat.st_nlink as u64,
    })
}
/// FIRST native-main operation, before jobserver import or any descriptor
/// opening. Only reads locator/native metadata; it confers no SDK authority.
pub fn snapshot_sdk_lease() -> io::Result<PendingSdkCapture> {
    let Some(value) = std::env::var_os(SDK_LEASE_ENV) else {
        return Ok(PendingSdkCapture { original: None });
    };
    let value = value.to_str().ok_or_else(refused)?;
    let fd: RawFd = value.parse().map_err(|_| refused())?;
    if fd < 3 || fd.to_string() != value {
        return Err(refused());
    }
    Ok(PendingSdkCapture { original: Some((fd, identity(fd)?)) })
}
fn capture(pending: PendingSdkCapture) -> io::Result<Option<Keeper>> {
    let Some((original, before)) = pending.original else {
        return Ok(None);
    };
    if identity(original)? != before {
        return Err(refused());
    }
    // SAFETY: duplicate the still-original inherited descriptor into a fresh
    // CLOEXEC slot, without modifying/owning/closing its advertised number.
    let raw = unsafe { libc::fcntl(original, libc::F_DUPFD_CLOEXEC, 5) };
    if raw < 0 {
        return Err(io::Error::last_os_error());
    }
    // SAFETY: successful duplication transferred exactly this fresh descriptor.
    let file = unsafe { File::from_raw_fd(raw) };
    if identity(original)? != before || identity(file.as_raw_fd())? != before {
        return Err(refused());
    }
    Ok(Some(Keeper { original, identity: before, file }))
}
/// Immediately after the fixed early GNU import, before logging, callbacks,
/// configuration or probes. Never opens a path, locks or reconstructs a lease.
/// # Safety
/// Between snapshot and this call only the fixed early scheduler importer may
/// run. No arbitrary callback/thread may close/reuse the advertised slot. The
/// custodian maps SDK disjoint from every GNU/private bootstrap target slot.
pub unsafe fn capture_sdk_lease(pending: PendingSdkCapture) -> io::Result<()> {
    let keeper = capture(pending)?;
    KEEPER.set(keeper).map_err(|_| {
        io::Error::new(io::ErrorKind::AlreadyExists, "SDK early capture already complete")
    })
}
/// Observe only the immutable result of genuine entry capture. This grants no
/// lease or execution; missing capture is an error, never inferred absence.
pub fn original_lease_present() -> io::Result<bool> {
    KEEPER.get().map(|keeper| keeper.is_some()).ok_or_else(refused)
}

/// Forward only the still-original captured SDK locator, never a reopened path
/// or unrelated descriptor. The global keeper retains its duplicate while the
/// caller retains the original inherited number through child retirement.
/// Restore the locator from that capture even when the command environment was
/// cleared; never consult a later ambient value to select the descriptor.
/// No Context/lease authentication is inferred by this transparent handoff.
pub fn inherit_original_lease(command: &mut std::process::Command) -> io::Result<()> {
    let Some(keeper) = KEEPER.get().ok_or_else(refused)?.as_ref() else {
        return Ok(());
    };
    if identity(keeper.original)? != keeper.identity
        || identity(keeper.file.as_raw_fd())? != keeper.identity
    {
        return Err(refused());
    }
    super::member::inherit_descriptions(command, &[keeper.original])?;
    command.env(SDK_LEASE_ENV, keeper.original.to_string());
    Ok(())
}

impl Keeper {
    fn validate(&self, sdk: &SdkCustody) -> io::Result<()> {
        if sdk.inherited_fd != self.original as u32
            || sdk.lease.device != self.identity.device
            || sdk.lease.inode != self.identity.inode
            || identity(self.file.as_raw_fd())? != self.identity
        {
            return Err(refused());
        }
        Ok(())
    }
}
/// Call ONLY after authenticated native Context/actual subject validation.
/// Metadata comparison is not an OFD proof: original transfer and the strict
/// early capture ordering above establish custody. No lock is acquired here.
pub fn validate_sdk_keeper(context: &Context) -> io::Result<()> {
    let sdk = context.sdk.as_ref().ok_or_else(refused)?;
    KEEPER.get().and_then(Option::as_ref).ok_or_else(refused)?.validate(sdk)
}

#[cfg(test)]
mod tests {
    use std::os::unix::fs::{DirBuilderExt, OpenOptionsExt};
    use std::time::{SystemTime, UNIX_EPOCH};

    use super::*;
    #[test]
    fn close_only_keeper_retains_original_lock_without_changing_or_reopening_source() {
        const TEST: &str = "client::sdk::tests::close_only_keeper_retains_original_lock_without_changing_or_reopening_source";
        const ROLE: &str = "TRUST_SDK_KEEPER_FD_TEST";
        if std::env::var(ROLE).as_deref() != Ok(TEST) {
            // Assert final close after this process has executed, without an
            // unrelated parallel fork temporarily inheriting the description.
            // The child runs the same real duplicate/lock/close assertions.
            let output = std::process::Command::new(std::env::current_exe().unwrap())
                .args(["--exact", TEST, "--nocapture"])
                .env(ROLE, TEST)
                .output()
                .unwrap();
            assert!(output.status.success(), "original SDK keeper control failed: {output:?}");
            return;
        }
        let root = std::env::temp_dir().join(format!(
            "trust-sdk-keeper-{}-{}",
            std::process::id(),
            SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos()
        ));
        std::fs::DirBuilder::new().mode(0o700).create(&root).unwrap();
        let path = root.join("lease");
        let original = std::fs::OpenOptions::new()
            .read(true)
            .write(true)
            .create_new(true)
            .mode(0o600)
            .open(&path)
            .unwrap();
        original.try_lock_shared().unwrap();
        let raw = original.as_raw_fd();
        let before = identity(raw).unwrap();
        // SAFETY: observes descriptor flags without changing the held original.
        let flags = unsafe { libc::fcntl(raw, libc::F_GETFD) };
        let keeper = capture(PendingSdkCapture { original: Some((raw, before)) }).unwrap().unwrap();
        // SAFETY: both original and fresh captured descriptor remain held.
        unsafe {
            assert_eq!(libc::fcntl(raw, libc::F_GETFD), flags);
            assert_ne!(libc::fcntl(keeper.file.as_raw_fd(), libc::F_GETFD) & libc::FD_CLOEXEC, 0);
        }
        let mut sdk = SdkCustody {
            execution: root.as_os_str().as_encoded_bytes().to_vec(),
            build: 42,
            lease_path: path.as_os_str().as_encoded_bytes().to_vec(),
            lease: crate::FileIdentity { device: before.device, inode: before.inode },
            inherited_fd: raw as u32,
        };
        keeper.validate(&sdk).unwrap();
        sdk.lease.inode = sdk.lease.inode.wrapping_add(1);
        assert!(keeper.validate(&sdk).is_err());
        drop(original);
        let probe = std::fs::OpenOptions::new().read(true).write(true).open(&path).unwrap();
        assert!(matches!(probe.try_lock(), Err(std::fs::TryLockError::WouldBlock)));
        drop(keeper);
        probe.try_lock().unwrap();
        drop(probe);
        std::fs::remove_file(path).unwrap();
        std::fs::remove_dir(root).unwrap();
    }
}
