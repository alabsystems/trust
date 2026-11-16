//! Authentication of two fixed live procfs roles, before the irreversible
//! profile. No caller path/digest can turn an arbitrary input into a resource.
use std::ffi::CStr;
use std::os::fd::{AsRawFd, FromRawFd, OwnedFd, RawFd};

use trust_process_isolation::{Budget, Charge};

use super::{Profile, checked, flags, stat, system};
use crate::Error;

fn procfs(fd: RawFd) -> Result<(), Error> {
    let mut value = std::mem::MaybeUninit::<libc::statfs>::zeroed();
    // SAFETY: live borrowed descriptor and complete statfs output.
    if unsafe { libc::fstatfs(fd, value.as_mut_ptr()) } != 0 {
        return Err(system("resource filesystem"));
    }
    // SAFETY: successful fstatfs initialized the complete structure.
    if unsafe { value.assume_init() }.f_type != 0x9fa0 {
        return Err(Error::Contract("live resource is not kernel procfs"));
    }
    Ok(())
}
fn open_at(parent: RawFd, leaf: &CStr, directory: bool) -> Result<OwnedFd, Error> {
    let extra = if directory { libc::O_DIRECTORY } else { 0 };
    // SAFETY: held parent FD, exact NUL-terminated literal/numeric child name,
    // readonly/no-follow flags, and no creation or truncation.
    let fd = unsafe {
        libc::openat(
            parent,
            leaf.as_ptr(),
            libc::O_RDONLY | libc::O_CLOEXEC | libc::O_NOFOLLOW | extra,
        )
    };
    if fd < 0 {
        return Err(system("resource canonical open"));
    }
    // SAFETY: openat transferred unique ownership of this new descriptor.
    Ok(unsafe { OwnedFd::from_raw_fd(fd) })
}
fn exact(fd: RawFd, expected: RawFd) -> Result<(), Error> {
    procfs(fd)?;
    let actual = stat(fd)?;
    let expected = stat(expected)?;
    let access = flags(fd)?;
    if access & libc::O_ACCMODE != libc::O_RDONLY
        || access & libc::O_PATH != 0
        || actual.st_mode & libc::S_IFMT != libc::S_IFREG
        || actual.st_dev != expected.st_dev
        || actual.st_ino != expected.st_ino
    {
        return Err(Error::Contract("fixed live resource identity/access"));
    }
    Ok(())
}

pub(super) fn validate(profile: &Profile<'_>, budget: &Budget) -> Result<(), Error> {
    if profile.inputs.len() != 1
        || profile.inputs[0].fd != 5
        || !profile.inputs[0].executable
        || profile.limits.descriptors < 8
    {
        return Err(Error::Contract("fixed checker resource layout"));
    }
    // Fixed stack storage and finite readonly inspections. There is no heap
    // path construction or normal-observation allocation in this role check.
    budget.charge(Charge { work: 64, ..Charge::default() }).map_err(Error::Budget)?;
    checked(budget)?;
    // SAFETY: fixed literal root, readonly directory and no symlink traversal.
    let fd = unsafe {
        libc::open(
            c"/proc".as_ptr(),
            libc::O_RDONLY | libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC,
        )
    };
    if fd < 0 {
        return Err(system("resource proc root"));
    }
    // SAFETY: successful open transferred unique ownership.
    let root = unsafe { OwnedFd::from_raw_fd(fd) };
    procfs(root.as_raw_fd())?;
    let mut digits = [0u8; 11];
    let mut at = digits.len() - 1;
    // SAFETY: scalar identity observation, not an authority supplied by caller.
    let mut pid =
        u32::try_from(unsafe { libc::getpid() }).map_err(|_| Error::Contract("worker PID"))?;
    if pid == 0 {
        return Err(Error::Contract("worker PID"));
    }
    while pid != 0 {
        at -= 1;
        digits[at] = b'0' + (pid % 10) as u8;
        pid /= 10;
    }
    let name = CStr::from_bytes_with_nul(&digits[at..])
        .map_err(|_| Error::Contract("numeric worker PID"))?;
    let own = open_at(root.as_raw_fd(), name, true)?;
    procfs(own.as_raw_fd())?;
    checked(budget)?;
    exact(6, open_at(own.as_raw_fd(), c"statm", false)?.as_raw_fd())?;
    exact(7, open_at(root.as_raw_fd(), c"meminfo", false)?.as_raw_fd())?;
    checked(budget)
}

#[cfg(test)]
mod tests;
