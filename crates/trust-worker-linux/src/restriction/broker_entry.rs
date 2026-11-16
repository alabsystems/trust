//! Trusted separate-broker confinement, before any notification or map request.
//! Parent/worker identity and immutable graph binding remain launcher duties.
use std::os::fd::RawFd;

use trust_process_isolation::{Budget, Charge};

use super::{
    Profile, Program, checked, flags, landlock, prepare_control, restrict_identity,
    restrict_limits, stat, system, validate_inner,
};
use crate::{Error, filter};

pub(crate) fn install_broker(
    profile: &Profile<'_>,
    budget: &Budget,
    worker: u32,
    listener: RawFd,
    memory: RawFd,
    maps: RawFd,
    retained: &[RawFd],
) -> Result<(), Error> {
    let result = inner(profile, budget, worker, listener, memory, maps, retained);
    if result.is_err() {
        budget.refuse(trust_process_isolation::Error::Phase);
    }
    result
}
fn inner(
    profile: &Profile<'_>,
    budget: &Budget,
    worker: u32,
    listener: RawFd,
    memory: RawFd,
    maps: RawFd,
    retained: &[RawFd],
) -> Result<(), Error> {
    checked(budget)?;
    if worker == 0 || profile.limits.descriptors != 1024 || retained.len() > 900 {
        return Err(Error::Contract("native broker finite role envelope"));
    }
    budget.charge(Charge { work: 64 * 1024, ..Charge::default() }).map_err(Error::Budget)?;
    // This fixed broker role alone admits the finite preopened source bank.
    // Public worker validation and native entry retain their64FD maximum.
    validate_inner(profile, budget, 1024)?;
    prepare_control(budget)?;
    super::native_entry::parent(profile.parent_pid)?;
    validate_handoff(worker, memory, maps)?;
    let first = 5 + profile.inputs.len();
    let mut keep = [false; 1024];
    keep[..first].fill(true);
    let mut roles = [listener, memory, maps];
    roles.sort_unstable();
    if roles[0] < first as i32 || roles[2] >= 1024 || roles[0] == roles[1] || roles[1] == roles[2] {
        return Err(Error::Contract("native broker retained role slots"));
    }
    for fd in roles {
        keep[fd as usize] = true;
    }
    for fd in retained {
        if *fd < first as i32 || *fd >= 1024 {
            return Err(Error::Contract("native broker source slot"));
        }
        if roles.contains(fd) {
            continue;
        }
        if keep[*fd as usize] {
            return Err(Error::Contract("native broker duplicate source"));
        }
        let value = stat(*fd)?;
        // SAFETY: scalar irreversible seal observation of a held source FD.
        let seals = unsafe { libc::fcntl(*fd, libc::F_GET_SEALS) };
        if value.st_mode & libc::S_IFMT != libc::S_IFREG
            || flags(*fd)? & libc::O_ACCMODE != libc::O_RDONLY
            || seals < 0
            || seals & super::SEALS != super::SEALS
        {
            return Err(Error::Contract("native broker immutable retained source"));
        }
        keep[*fd as usize] = true;
    }
    let filter = filter::broker::build(listener as u32, memory as u32, maps as u32)?;
    restrict_identity()?;
    for (fd, retain) in keep.iter().enumerate().skip(first) {
        if !retain {
            // SAFETY: trusted single-threaded setup closes only unretained
            // slots, all kept owners remain live and cannot be recycled here.
            if unsafe { libc::close(fd as i32) } != 0
                && std::io::Error::last_os_error().raw_os_error() != Some(libc::EBADF)
            {
                return Err(system("native broker ambient close"));
            }
        }
    }
    // SAFETY: all admitted capabilities are strictly below1024; no higher FD
    // may survive trusted startup. The bootstrap socket has already dropped.
    if unsafe { libc::syscall(libc::SYS_close_range, 1024u32, u32::MAX, 0u32) } != 0 {
        return Err(system("native broker high ambient close"));
    }
    restrict_limits(profile, budget)?;
    landlock(budget)?;
    super::native_entry::parent(profile.parent_pid)?;
    checked(budget)?;
    let program = Program { len: filter.len as u16, filter: filter.instructions.as_ptr() };
    // SAFETY: fixed complete immutable program, trusted sole startup thread,
    // no listener or policy fallback. All opaque service runs after this clamp.
    if unsafe { libc::syscall(libc::SYS_seccomp, 1u32, 0u32, &program) } != 0 {
        return Err(system("native broker seccomp"));
    }
    checked(budget)
}

pub(crate) fn validate_handoff(worker: u32, memory: RawFd, maps: RawFd) -> Result<(), Error> {
    if worker == 0 || memory == maps {
        return Err(Error::Contract("native retained distinct task/mm roles"));
    }
    retained_proc(memory, worker, b"/mem")?;
    retained_proc(maps, worker, b"/maps")
}
fn retained_proc(fd: RawFd, worker: u32, leaf: &[u8]) -> Result<(), Error> {
    let value = stat(fd)?;
    let mut fs = std::mem::MaybeUninit::<libc::statfs>::zeroed();
    // SAFETY: complete writable statfs record on the held transferred handle.
    if unsafe { libc::fstatfs(fd, fs.as_mut_ptr()) } != 0 {
        return Err(system("native retained procfs type"));
    }
    // SAFETY: successful fstatfs initialized the entire record.
    if unsafe { fs.assume_init() }.f_type != 0x9fa0
        || value.st_mode & libc::S_IFMT != libc::S_IFREG
        || flags(fd)? & libc::O_ACCMODE != libc::O_RDONLY
        || flags(fd)? & libc::O_PATH != 0
    {
        return Err(Error::Contract("native retained procfs access"));
    }
    let source = crate::launcher::snapshot::proc_path(b"self/fd/", fd as u32, b"")?;
    let expected = crate::launcher::snapshot::proc_path(b"", worker, leaf)?;
    let length = expected.iter().position(|byte| *byte == 0).unwrap();
    let mut target = [0; 64];
    // SAFETY: bounded terminated descriptor path and complete writable target.
    let n =
        unsafe { libc::readlink(source.as_ptr().cast(), target.as_mut_ptr().cast(), target.len()) };
    if n < 0 {
        return Err(system("native retained procfs identity"));
    }
    if n as usize != length || target[..length] != expected[..length] {
        return Err(Error::Contract("native retained exact task/mm leaf"));
    }
    Ok(())
}
