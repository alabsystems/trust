// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Shared descriptor ACL checks, independent of Git, transport and TLS.
//! Callers retain ownership, mode, kind, link and path-custody checks.
//! These observations grant no resource, source, execution or proof authority.
#![cfg(unix)]

use std::fs::File;
use std::io;
use std::os::fd::AsRawFd;

fn refused(why: &str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, why)
}

/// Read-only ACL admission shared with native owners. The caller must also
/// check its required owner, kind, link count, POSIX modes and path custody.
/// No cache, process, resource or proof authority is created by this check.
pub fn require_no_acl_grants(file: &File) -> io::Result<()> {
    if acl_forbids(file, AclPolicy::NoGrants)? {
        return Err(refused("provenance backing ACL grants access"));
    }
    Ok(())
}

/// Require an empty extended ACL, including inherited and deny-only entries.
/// This is stricter than owner-only access: a proof store need not interpret
/// platform-specific ACL ordering or inheritance. Other descriptor checks
/// remain the caller's responsibility.
pub fn require_no_acl_entries(file: &File) -> io::Result<()> {
    if acl_forbids(file, AclPolicy::NoEntries)? {
        return Err(refused("provenance backing has extended ACL entries"));
    }
    Ok(())
}

#[derive(Clone, Copy)]
enum AclPolicy {
    NoGrants,
    NoEntries,
}
#[cfg(target_os = "macos")]
fn acl_forbids(file: &File, policy: AclPolicy) -> io::Result<bool> {
    use std::ffi::{c_int, c_void};
    // ABI and constants are the maintained astream-sys owner.rs declarations
    // from Apple's sys/acl.h, not a filesystem permission inference.
    unsafe extern "C" {
        fn acl_get_fd_np(fd: c_int, kind: c_int) -> *mut c_void;
        fn acl_get_entry(acl: *mut c_void, which: c_int, entry: *mut *mut c_void) -> c_int;
        fn acl_get_tag_type(entry: *mut c_void, tag: *mut c_int) -> c_int;
        fn acl_free(object: *mut c_void) -> c_int;
        fn acl_valid(acl: *mut c_void) -> c_int;
    }
    struct Acl(*mut c_void);
    impl Drop for Acl {
        fn drop(&mut self) {
            // SAFETY: this handle came from acl_get_fd_np and is freed once.
            unsafe {
                acl_free(self.0);
            }
        }
    }
    // SAFETY: the file is held through the call; success returns an owned ACL.
    let raw = unsafe { acl_get_fd_np(file.as_raw_fd(), 0x100) };
    if raw.is_null() {
        let error = io::Error::last_os_error();
        return if error.raw_os_error() == Some(libc::ENOENT) { Ok(false) } else { Err(error) };
    }
    let acl = Acl(raw);
    // SAFETY: acl is this owned, live ACL snapshot. Validate it before treating
    // the documented terminal EINVAL for our known cursor as end-of-list.
    if unsafe { acl_valid(acl.0) } != 0 {
        return Err(io::Error::last_os_error());
    }
    let mut which = 0; // ACL_FIRST_ENTRY, then ACL_NEXT_ENTRY=-1
    loop {
        let mut entry = std::ptr::null_mut();
        // SAFETY: acl is live and entry is one writable output pointer.
        if unsafe { acl_get_entry(acl.0, which, &mut entry) } != 0 {
            let error = io::Error::last_os_error();
            return if error.raw_os_error() == Some(libc::EINVAL) { Ok(false) } else { Err(error) };
        }
        if matches!(policy, AclPolicy::NoEntries) {
            return Ok(true);
        }
        which = -1;
        let mut tag = 0;
        // SAFETY: entry is from the live ACL and tag is writable.
        if unsafe { acl_get_tag_type(entry, &mut tag) } != 0 {
            return Err(io::Error::last_os_error());
        }
        if tag == 1 {
            return Ok(true);
        } // ACL_EXTENDED_ALLOW
        if tag != 2 {
            return Err(refused("unknown extended ACL tag"));
        } // ACL_EXTENDED_DENY
    }
}
#[cfg(not(target_os = "macos"))]
fn acl_forbids(file: &File, policy: AclPolicy) -> io::Result<bool> {
    // On Linux POSIX ACL permissions to other users are bounded by group mask
    // bits, which owned() rejects. Other platforms have no qualified route.
    #[cfg(target_os = "linux")]
    {
        if matches!(policy, AclPolicy::NoGrants) {
            return Ok(false);
        }
        for name in [c"system.posix_acl_access", c"system.posix_acl_default"] {
            // SAFETY: live descriptor and constant NUL-terminated name. A
            // null/zero buffer asks only whether this ACL attribute exists.
            let size = unsafe {
                libc::fgetxattr(file.as_raw_fd(), name.as_ptr(), std::ptr::null_mut(), 0)
            };
            if size >= 0 {
                return Ok(true);
            }
            let error = io::Error::last_os_error();
            if !matches!(error.raw_os_error(), Some(libc::ENODATA) | Some(libc::ENOTSUP)) {
                return Err(error);
            }
        }
        Ok(false)
    }
    #[cfg(not(target_os = "linux"))]
    {
        let _ = (file, policy);
        Err(io::ErrorKind::Unsupported.into())
    }
}
