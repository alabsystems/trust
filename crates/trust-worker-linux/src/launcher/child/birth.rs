//! Clone-at-birth and exclusive child transfer; no public authority facts.
use std::os::fd::{FromRawFd, OwnedFd, RawFd};

use trust_process_isolation::Budget;

use super::{Child, Custody, Tree, contract};
use crate::{Error, system};

#[repr(C)]
#[derive(Default)]
struct CloneArgs {
    flags: u64,
    pidfd: u64,
    child_tid: u64,
    parent_tid: u64,
    exit_signal: u64,
    stack: u64,
    stack_size: u64,
    tls: u64,
    set_tid: u64,
    set_tid_size: u64,
    cgroup: u64,
}
pub(super) unsafe fn contained_clone(group: RawFd, pidfd: &mut RawFd) -> libc::pid_t {
    const INTO_CGROUP: u64 = 0x2_0000_0000;
    let args = CloneArgs {
        flags: INTO_CGROUP | libc::CLONE_PIDFD as u64,
        pidfd: (pidfd as *mut RawFd) as u64,
        exit_signal: libc::SIGCHLD as u64,
        cgroup: group as u64,
        ..CloneArgs::default()
    };
    // SAFETY: the exact C-layout clone3 structure and writable parent pidfd
    // slot remain live. No shared VM/thread flags or stack pointer are used;
    // the child is born inside this held cgroup before setup or user code.
    unsafe {
        libc::syscall(libc::SYS_clone3, &args, std::mem::size_of::<CloneArgs>()) as libc::pid_t
    }
}

pub(super) fn transfer(
    pid: libc::pid_t,
    birth_pidfd: RawFd,
    tree: Option<Tree>,
    budget: &Budget,
) -> Result<Custody, Error> {
    let child = match tree {
        Some(tree) => {
            // CLONE_PIDFD is mandatory on this route. No parent numeric
            // pidfd_open or fork/attach fallback can replace birth custody.
            if birth_pidfd < 0 {
                budget.cancel();
                let _ = tree.stop();
                return Err(contract("contained clone omitted birth pidfd"));
            }
            // SAFETY: successful CLONE_PIDFD returned this new owned FD.
            let pidfd = unsafe { OwnedFd::from_raw_fd(birth_pidfd) };
            Custody::Tree { pid, pidfd, reaped: false, tree, budget: budget.clone() }
        }
        None => {
            let mut legacy = Child { pid, pidfd: None, reaped: false, budget: budget.clone() };
            // SAFETY: the exclusively unreaped legacy PID cannot be reused.
            let fd = unsafe { libc::syscall(libc::SYS_pidfd_open, pid, 0u32) };
            if fd >= 0 {
                // SAFETY: successful pidfd_open returned a fresh owned FD.
                legacy.pidfd = Some(unsafe { OwnedFd::from_raw_fd(fd as i32) });
            } else if !matches!(
                std::io::Error::last_os_error().raw_os_error(),
                Some(libc::ENOSYS | libc::EINVAL | libc::EPERM)
            ) {
                return Err(system("worker pidfd"));
            }
            Custody::Legacy(legacy)
        }
    };
    Ok(child)
}
