//! Private trusted-entry installation, not a native loader or broker owner.
//!
//! The caller must own the unreaped child and its broker watchdog, authenticate
//! the post-exec mm and immutable runtime closure, and terminate on every error.
//! No untrusted constructor, thread, signal handler or FD mutator may run before
//! this entry returns. Budget clones across fork are not a shared process meter.
use std::os::fd::{AsRawFd, BorrowedFd, FromRawFd, OwnedFd, RawFd};

use trust_process_isolation::{Budget, Charge};

use super::{Installed, Profile, Program, checked, filter, landlock, restrict_entry, stat, system};
use crate::Error;

#[derive(Debug)]
pub(crate) struct NativeInstalled {
    pub(crate) listener: OwnedFd,
    pub(crate) restrictions: Installed,
}

/// Admission and clamping precede user entry. Identity, parent and budget
/// checks also run after irreversible steps; any partial failure is shared-
/// terminal in this process and cannot be retried. The local token carries no
/// compiler or proof authority.
pub(crate) fn install_native(
    profile: &Profile<'_>,
    budget: &Budget,
    transfer: BorrowedFd<'_>,
) -> Result<NativeInstalled, Error> {
    let result = install_inner(profile, budget, transfer);
    if result.is_err() {
        budget.refuse(trust_process_isolation::Error::Phase);
    }
    result
}

fn install_inner(
    profile: &Profile<'_>,
    budget: &Budget,
    transfer: BorrowedFd<'_>,
) -> Result<NativeInstalled, Error> {
    checked(budget)?;
    // Fixed syscall/descriptor inspections and filter setup are prepaid. Kernel
    // calls remain opaque intervals; an independent owner watchdog is required.
    budget.charge(Charge { work: 64, ..Charge::default() }).map_err(Error::Budget)?;
    super::validate(profile, budget)?;
    super::prepare_control(budget)?;
    // Native issuance has a fixed one-use 33..63 bank. B2 remains free to use
    // a smaller descriptor envelope, but native entry cannot promise that bank
    // under a contradictory kernel limit. H is inherited and closes first.
    if profile.limits.descriptors != 64 {
        return Err(Error::Contract("native bank descriptor envelope"));
    }
    let first =
        u32::try_from(5 + profile.inputs.len()).map_err(|_| Error::Contract("native FD count"))?;
    let fd = transfer.as_raw_fd();
    let transfer_id = Transfer::capture(fd, profile.parent_pid)?;
    parent(profile.parent_pid)?;
    let mut executable = [0; 27];
    let mut count = 0;
    for input in profile.inputs {
        if input.executable {
            executable[count] = input.fd as u32;
            count += 1;
        }
    }
    let filter = filter::native(first, &executable[..count], first, fd as u32)?;
    restrict_entry(profile, budget, first, Some(fd as u32))?;
    let abi = landlock(budget)?;
    // The trusted single-thread entry closes all ambient FDs. Recheck the
    // retained socket identity and parent immediately before native policy.
    transfer_id.same(Transfer::capture(fd, profile.parent_pid)?)?;
    parent(profile.parent_pid)?;
    checked(budget)?;
    let program = Program {
        len: u16::try_from(filter.len).map_err(|_| Error::Contract("native filter length"))?,
        filter: filter.instructions.as_ptr(),
    };
    // SAFETY: the initialized immutable filter and C-layout wrapper are live
    // until copied. Startup admission requires one trusted thread. These are
    // NEW_LISTENER|WAIT_KILLABLE_RECV, never a policy-relaxing fallback.
    let raw = unsafe { libc::syscall(libc::SYS_seccomp, 1u32, 8u32 | 32u32, &program) };
    if raw < 0 {
        return Err(system("native seccomp listener"));
    }
    let raw = i32::try_from(raw).map_err(|_| Error::Contract("native listener FD"))?;
    // SAFETY: successful NEW_LISTENER returned unique descriptor ownership.
    let listener = unsafe { OwnedFd::from_raw_fd(raw) };
    // Every slot above the dense inputs except H was closed; Landlock's one
    // temporary FD was dropped. A different result is never adapted silently.
    if raw as u32 != first {
        // Native policy only allows the expected listener close slot. If the
        // kernel violates that expectation, terminate rather than closing an
        // unexpected descriptor from a destructor under installed policy.
        std::mem::forget(listener);
        return Err(Error::Contract("native listener layout changed"));
    }
    checked(budget)?;
    Ok(NativeInstalled { listener, restrictions: Installed::new(abi, budget) })
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Transfer {
    device: libc::dev_t,
    inode: libc::ino_t,
    mode: libc::mode_t,
    uid: libc::uid_t,
    gid: libc::gid_t,
}
impl Transfer {
    fn capture(fd: RawFd, expected_parent: libc::pid_t) -> Result<Self, Error> {
        if !(64..=4096).contains(&fd) {
            return Err(Error::Contract("native transfer slot"));
        }
        socket_identity(fd, expected_parent, libc::SOCK_SEQPACKET)
    }
    fn same(self, other: Self) -> Result<(), Error> {
        if self == other { Ok(()) } else { Err(Error::Contract("native transfer changed")) }
    }
}

fn socket_identity(fd: RawFd, expected_parent: libc::pid_t, kind: i32) -> Result<Transfer, Error> {
    let s = stat(fd)?;
    if s.st_mode & libc::S_IFMT != libc::S_IFSOCK
        || super::flags(fd)? & libc::O_ACCMODE != libc::O_RDWR
    {
        return Err(Error::Contract("native transfer socket"));
    }
    for (option, expected) in [(libc::SO_DOMAIN, libc::AF_UNIX), (libc::SO_TYPE, kind)] {
        let mut actual = 0i32;
        let mut len = std::mem::size_of_val(&actual) as libc::socklen_t;
        // SAFETY: one complete writable native integer and exact length.
        if unsafe {
            libc::getsockopt(
                fd,
                libc::SOL_SOCKET,
                option,
                (&mut actual as *mut i32).cast(),
                &mut len,
            )
        } != 0
        {
            return Err(system("native transfer type"));
        }
        if len as usize != std::mem::size_of_val(&actual) || actual != expected {
            return Err(Error::Contract("native transfer type"));
        }
    }
    let mut peer = libc::ucred { pid: 0, uid: 0, gid: 0 };
    let mut len = std::mem::size_of_val(&peer) as libc::socklen_t;
    // SAFETY: the native credential buffer and exact length remain live.
    if unsafe {
        libc::getsockopt(
            fd,
            libc::SOL_SOCKET,
            libc::SO_PEERCRED,
            (&mut peer as *mut libc::ucred).cast(),
            &mut len,
        )
    } != 0
    {
        return Err(system("native transfer parent"));
    }
    // SAFETY: effective credential observations do not change authority.
    if len as usize != std::mem::size_of_val(&peer)
        || peer.pid != expected_parent
        || peer.uid != unsafe { libc::geteuid() }
        || peer.gid != unsafe { libc::getegid() }
    {
        return Err(Error::Contract("native transfer parent"));
    }
    Ok(Transfer {
        device: s.st_dev,
        inode: s.st_ino,
        mode: s.st_mode,
        uid: s.st_uid,
        gid: s.st_gid,
    })
}

/// Fixed trusted bootstrap checks before reading the prepaid allowance. The
/// caller remains at its owned post-exec rendezvous; no constructor or FD
/// mutator may run, and the outside monitor already owns the original deadline.
pub(crate) fn authenticate_bootstrap(
    transfer: RawFd,
    expected_parent: libc::pid_t,
) -> Result<(), Error> {
    Transfer::capture(transfer, expected_parent)?;
    socket_identity(3, expected_parent, libc::SOCK_STREAM)?;
    if super::flags(3)? & libc::O_NONBLOCK == 0 {
        return Err(Error::Contract("native bootstrap control must be nonblocking"));
    }
    parent(expected_parent)
}

pub(super) fn parent(expected: libc::pid_t) -> Result<(), Error> {
    let mut signal = 0i32;
    // SAFETY: PR_GET_PDEATHSIG writes one native integer to live exact storage.
    if unsafe { libc::prctl(libc::PR_GET_PDEATHSIG, &mut signal, 0, 0, 0) } != 0 {
        return Err(system("native parent-death signal"));
    }
    // SAFETY: getppid is a scalar observation of the current direct parent.
    if signal != libc::SIGKILL || unsafe { libc::getppid() } != expected {
        return Err(Error::Contract("native direct parent lifetime"));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn transfer_identity_substitution_is_not_an_equal_descriptor_number() {
        let original = Transfer { device: 1, inode: 2, mode: libc::S_IFSOCK, uid: 3, gid: 4 };
        assert!(original.same(original).is_ok());
        assert!(original.same(Transfer { inode: 9, ..original }).is_err());
        assert!(original.same(Transfer { mode: libc::S_IFREG, ..original }).is_err());
    }

    #[test]
    fn real_socket_substitution_on_same_number_refuses_identity() {
        fn pair() -> [OwnedFd; 2] {
            let mut fds = [-1; 2];
            // SAFETY: two exact writable FD slots; success owns both sockets.
            assert_eq!(
                unsafe {
                    libc::socketpair(
                        libc::AF_UNIX,
                        libc::SOCK_SEQPACKET | libc::SOCK_CLOEXEC,
                        0,
                        fds.as_mut_ptr(),
                    )
                },
                0
            );
            // SAFETY: successful socketpair returned unique descriptors.
            unsafe { [OwnedFd::from_raw_fd(fds[0]), OwnedFd::from_raw_fd(fds[1])] }
        }
        let original = pair();
        let replacement = pair();
        // SAFETY: duplicate the live original into a fresh high owned slot.
        let raw = unsafe { libc::fcntl(original[0].as_raw_fd(), libc::F_DUPFD_CLOEXEC, 64) };
        assert!(raw >= 64);
        // SAFETY: successful fcntl returned one fresh unique owned descriptor.
        let target = unsafe { OwnedFd::from_raw_fd(raw) };
        let parent = std::process::id() as libc::pid_t;
        let before = Transfer::capture(raw, parent).unwrap();
        // SAFETY: replace our test-owned slot only; both sockets have the same
        // role/peer credentials, so the before/after inode identity matters.
        assert_eq!(unsafe { libc::dup2(replacement[0].as_raw_fd(), raw) }, raw);
        let after = Transfer::capture(target.as_raw_fd(), parent).unwrap();
        assert!(before.same(after).is_err());
    }
}
