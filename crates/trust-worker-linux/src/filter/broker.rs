//! Fixed separate native-broker role. Never applied to an untrusted worker.
use super::{ARCH, Filter, JEQ, LD};
use crate::Error;

pub(crate) const RECEIVE: u32 = 0xc0502100;
pub(crate) const VALID: u32 = 0x40082102;
pub(crate) const ADD: u32 = 0x40182103;

pub(crate) fn build(listener: u32, memory: u32, maps: u32) -> Result<Filter, Error> {
    let roles = [listener, memory, maps];
    if ARCH == 0
        || roles.iter().any(|fd| !(5..1024).contains(fd))
        || listener == memory
        || listener == maps
        || memory == maps
    {
        return Err(Error::Contract("native broker fixed descriptor roles"));
    }
    let mut f = Filter::new();
    f.push(LD, 0, 0, 4)?;
    f.push(JEQ, 1, 0, ARCH)?;
    f.deny()?;
    f.push(LD, 0, 0, 0)?;
    for call in [libc::SYS_read, libc::SYS_readv] {
        f.rule(call, |f| f.fds(0, &[3], None))?;
    }
    for call in [libc::SYS_write, libc::SYS_writev] {
        f.rule(call, |f| f.fds(0, &[1, 2, 3], None))?;
    }
    f.rule(libc::SYS_pread64, |f| f.fds(0, &[memory, maps], None))?;
    f.rule(libc::SYS_ioctl, |f| {
        f.fds(0, &[listener], None)?;
        f.fds(1, &[RECEIVE, VALID, ADD], None)
    })?;
    // Rust's owned-FD destructor checks F_GETFD before close in diagnostic
    // builds. This observes only the fixed admitted descriptor envelope; no
    // mutation, duplication or new descriptor capability is granted.
    f.rule(libc::SYS_fcntl, |f| {
        f.fds(1, &[libc::F_GETFD as u32], None)?;
        f.arg(0)?;
        f.push(super::JGE, 0, 1, 1024)?;
        f.deny()
    })?;
    f.rule(libc::SYS_close, |f| {
        f.arg(0)?;
        for protected in [0, 1, 2, 3, listener, memory, maps] {
            f.push(JEQ, 0, 1, protected)?;
            f.deny()?;
        }
        Ok(())
    })?;
    f.rule(libc::SYS_mmap, |f| f.no_bits(2, libc::PROT_EXEC as u32))?;
    f.rule(libc::SYS_mprotect, |f| f.no_bits(2, libc::PROT_EXEC as u32))?;
    f.rule(libc::SYS_futex, |f| {
        f.arg(1)?;
        f.push(super::JSET, 1, 0, libc::FUTEX_PRIVATE_FLAG as u32)?;
        f.deny()
    })?;
    #[cfg(target_arch = "x86_64")]
    f.rule(libc::SYS_poll, |_| Ok(()))?;
    for call in [
        libc::SYS_brk,
        libc::SYS_munmap,
        libc::SYS_mremap,
        libc::SYS_madvise,
        libc::SYS_clock_gettime,
        libc::SYS_getrandom,
        libc::SYS_getpid,
        libc::SYS_gettid,
        libc::SYS_rt_sigaction,
        libc::SYS_rt_sigprocmask,
        libc::SYS_rt_sigreturn,
        libc::SYS_sigaltstack,
        libc::SYS_ppoll,
        libc::SYS_sched_yield,
        libc::SYS_restart_syscall,
        libc::SYS_exit,
        libc::SYS_exit_group,
    ] {
        f.rule(call, |_| Ok(()))?;
    }
    f.deny()?;
    Ok(f)
}

#[cfg(test)]
mod tests {
    use super::super::tests::evaluate;
    use super::super::{ALLOW, KILL, native};
    use super::*;
    #[test]
    fn broker_ioctls_and_reads_are_bound_to_their_exact_retained_roles() {
        let f = build(6, 7, 8).unwrap();
        for fd in 0..64 {
            for command in [RECEIVE, VALID, ADD, 0xc0182101, 0, u32::MAX] {
                assert_eq!(
                    evaluate(&f, ARCH, libc::SYS_ioctl, [fd, command as u64, 0, 0, 0, 0]),
                    if fd == 6 && [RECEIVE, VALID, ADD].contains(&command) { ALLOW } else { KILL }
                );
            }
            assert_eq!(
                evaluate(&f, ARCH, libc::SYS_pread64, [fd, 0, 0, 0, 0, 0]),
                if [7, 8].contains(&fd) { ALLOW } else { KILL }
            );
            assert_eq!(
                evaluate(&f, ARCH, libc::SYS_read, [fd, 0, 0, 0, 0, 0]),
                if fd == 3 { ALLOW } else { KILL }
            );
            for command in
                [libc::F_GETFD, libc::F_GETFL, libc::F_SETFD, libc::F_DUPFD, libc::F_SETFL]
            {
                assert_eq!(
                    evaluate(&f, ARCH, libc::SYS_fcntl, [fd, command as u64, 0, 0, 0, 0]),
                    if command == libc::F_GETFD { ALLOW } else { KILL }
                );
            }
        }
        assert_eq!(
            evaluate(&f, ARCH, libc::SYS_fcntl, [1024, libc::F_GETFD as u64, 0, 0, 0, 0]),
            KILL
        );
        for roles in [(3, 7, 8), (6, 6, 8), (6, 7, 7), (6, 7, 1024)] {
            assert!(build(roles.0, roles.1, roles.2).is_err());
        }
    }
    #[test]
    fn separate_broker_grants_no_path_process_network_or_executable_memory() {
        let f = build(6, 7, 8).unwrap();
        for call in [
            libc::SYS_openat,
            libc::SYS_openat2,
            libc::SYS_socket,
            libc::SYS_clone,
            libc::SYS_clone3,
            libc::SYS_execve,
            libc::SYS_execveat,
            libc::SYS_recvmsg,
            libc::SYS_sendmsg,
            libc::SYS_dup,
            libc::SYS_ptrace,
            libc::SYS_kill,
        ] {
            assert_eq!(evaluate(&f, ARCH, call, [0; 6]), KILL);
        }
        for call in [libc::SYS_mmap, libc::SYS_mprotect] {
            assert_eq!(evaluate(&f, ARCH, call, [0, 4096, libc::PROT_EXEC as u64, 0, 33, 0]), KILL);
        }
        assert_eq!(evaluate(&f, ARCH ^ 1, libc::SYS_read, [3, 0, 1, 0, 0, 0]), KILL);
        let worker = native(5, &[], 5, 128).unwrap();
        assert_eq!(evaluate(&worker, ARCH, libc::SYS_ioctl, [6, RECEIVE as u64, 0, 0, 0, 0]), KILL);
        assert_eq!(evaluate(&worker, ARCH, libc::SYS_pread64, [7, 0, 1, 0, 0, 0]), KILL);
    }
}
