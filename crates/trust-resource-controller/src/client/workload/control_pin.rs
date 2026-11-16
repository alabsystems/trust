// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! First-entry control originals. Environment bytes only select the fixed
//! inherited set; actual peer/image/private backing checks occur on import.
use super::*;
use trust_resource_provenance::{ORIGINAL_CONTROL_DESCRIPTORS, PinnedHelper};

pub use crate::workload::host::{CONTROL_ADVERTISEMENT, CONTROL_FDS_ENV, CONTROL_TARGETS};
const _: () = assert!(CONTROL_TARGETS.len() == ORIGINAL_CONTROL_DESCRIPTORS);

pub struct PendingHostControl(Option<[FileIdentity; ORIGINAL_CONTROL_DESCRIPTORS]>);
pub struct EarlyHostControl(Option<[OwnedFd; ORIGINAL_CONTROL_DESCRIPTORS]>);
impl EarlyHostControl {
    pub(super) fn into_pin(self, deadline: Instant) -> io::Result<Option<PinnedHelper>> {
        self.0
            .map(|originals| {
                // SAFETY: only the FIRST-entry capturer below can create this
                // capsule, after checking/owning every disjoint inherited target.
                unsafe { PinnedHelper::from_inherited_control(originals, deadline) }
            })
            .transpose()
    }
    pub fn is_present(&self) -> bool {
        self.0.is_some()
    }
}
fn observed(fd: RawFd, index: usize) -> io::Result<FileIdentity> {
    let mut stat: libc::stat = unsafe { std::mem::zeroed() };
    if unsafe { libc::fstat(fd, &mut stat) } != 0 {
        return Err(io::Error::last_os_error());
    }
    let kind = match index {
        3..=5 => libc::S_IFREG,
        8 => libc::S_IFSOCK,
        _ => libc::S_IFDIR,
    };
    let flags = unsafe { libc::fcntl(fd, libc::F_GETFL) };
    if flags < 0
        || stat.st_mode & libc::S_IFMT != kind
        || (index != 8 && flags & libc::O_ACCMODE != libc::O_RDONLY)
    {
        return Err(refused());
    }
    Ok(FileIdentity {
        device: stat.st_dev as u64,
        inode: stat.st_ino as u64,
    })
}
/// Snapshot all fixed slots BEFORE GNU/SDK imports can allocate descriptions.
/// This selects no Host and creates no resource authority.
pub fn snapshot_host_control() -> io::Result<PendingHostControl> {
    let Some(value) = std::env::var_os(CONTROL_FDS_ENV) else {
        return Ok(PendingHostControl(None));
    };
    if value != std::ffi::OsStr::new(CONTROL_ADVERTISEMENT) {
        return Err(refused());
    }
    let mut before = [FileIdentity {
        device: 0,
        inode: 0,
    }; ORIGINAL_CONTROL_DESCRIPTORS];
    for (index, fd) in CONTROL_TARGETS.into_iter().enumerate() {
        before[index] = observed(fd, index)?;
    }
    Ok(PendingHostControl(Some(before)))
}
/// # Safety
/// FIRST native child entry exclusively owns fixed targets10..18. The native
/// launcher maps stdio/prelude/SDK/CPU/Store/GNU elsewhere. No code since the
/// snapshot may close/reuse these targets, and no other environment readers or
/// threads exist. Own the whole set before a fallible check can close any FD.
pub unsafe fn capture_host_control(pending: PendingHostControl) -> io::Result<EarlyHostControl> {
    unsafe { std::env::remove_var(CONTROL_FDS_ENV) };
    let Some(before) = pending.0 else {
        return Ok(EarlyHostControl(None));
    };
    let originals = CONTROL_TARGETS.map(|fd| unsafe { OwnedFd::from_raw_fd(fd) });
    for (index, file) in originals.iter().enumerate() {
        let fd = file.as_raw_fd();
        if observed(fd, index)? != before[index] {
            return Err(refused());
        }
        let flags = unsafe { libc::fcntl(fd, libc::F_GETFD) };
        if flags < 0 || unsafe { libc::fcntl(fd, libc::F_SETFD, flags | libc::FD_CLOEXEC) } != 0 {
            return Err(io::Error::last_os_error());
        }
    }
    Ok(EarlyHostControl(Some(originals)))
}
