use crate::Error;

pub(crate) mod broker;
mod resources;
mod threads;

const LD: u16 = 0x20;
const JEQ: u16 = 0x15;
const JGE: u16 = 0x35;
const JSET: u16 = 0x45;
const RET: u16 = 0x06;
pub(crate) const KILL: u32 = 0x8000_0000;
pub(crate) const ALLOW: u32 = 0x7fff_0000;
pub(crate) const NOTIFY: u32 = 0x7fc0_0000;
const MAX: usize = 512;
#[cfg(target_arch = "aarch64")]
const ARCH: u32 = 0xc000_00b7;
#[cfg(target_arch = "x86_64")]
const ARCH: u32 = 0xc000_003e;
#[cfg(not(any(target_arch = "aarch64", target_arch = "x86_64")))]
const ARCH: u32 = 0;

#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub(crate) struct Instruction {
    code: u16,
    jt: u8,
    jf: u8,
    k: u32,
}
const ZERO: Instruction = Instruction { code: 0, jt: 0, jf: 0, k: 0 };
#[derive(Debug)]
pub(crate) struct Filter {
    pub(crate) instructions: [Instruction; MAX],
    pub(crate) len: usize,
}
impl Filter {
    fn new() -> Self {
        Self { instructions: [ZERO; MAX], len: 0 }
    }
    fn push(&mut self, code: u16, jt: u8, jf: u8, k: u32) -> Result<(), Error> {
        if self.len == MAX {
            return Err(Error::Contract("filter size"));
        }
        self.instructions[self.len] = Instruction { code, jt, jf, k };
        self.len += 1;
        Ok(())
    }
    fn arg(&mut self, index: u32) -> Result<(), Error> {
        self.push(LD, 0, 0, 16 + 8 * index)
    }
    fn deny(&mut self) -> Result<(), Error> {
        self.push(RET, 0, 0, KILL)
    }
    fn allow(&mut self) -> Result<(), Error> {
        self.push(RET, 0, 0, ALLOW)
    }
    fn bank(&mut self, index: u32, known: &[u32]) -> Result<(), Error> {
        self.arg(index)?;
        for fd in known {
            self.push(JEQ, 0, 1, *fd)?;
            self.allow()?;
        }
        self.push(JGE, 1, 0, 33)?;
        self.deny()?;
        self.push(JGE, 0, 1, 64)?;
        self.deny()?;
        self.allow()
    }
    fn no_bits(&mut self, index: u32, bits: u32) -> Result<(), Error> {
        self.arg(index)?;
        self.push(JSET, 0, 1, bits)?;
        self.deny()
    }
    fn fds(&mut self, index: u32, known: &[u32], dynamic: Option<u32>) -> Result<(), Error> {
        self.arg(index)?;
        let tests = known.len() + usize::from(dynamic.is_some());
        if tests > 64 {
            return Err(Error::Contract("FD selector"));
        }
        let mut left = tests;
        if let Some(minimum) = dynamic {
            self.push(
                JGE,
                u8::try_from(left).map_err(|_| Error::Contract("FD jump"))?,
                0,
                minimum,
            )?;
            left -= 1;
        }
        for fd in known {
            self.push(JEQ, u8::try_from(left).map_err(|_| Error::Contract("FD jump"))?, 0, *fd)?;
            left -= 1;
        }
        self.deny()
    }
    fn rule(
        &mut self,
        syscall: libc::c_long,
        body: impl FnOnce(&mut Self) -> Result<(), Error>,
    ) -> Result<(), Error> {
        let start = self.len;
        self.push(
            JEQ,
            0,
            0,
            u32::try_from(syscall).map_err(|_| Error::Contract("syscall number"))?,
        )?;
        body(self)?;
        self.allow()?;
        self.instructions[start].jf =
            u8::try_from(self.len - start - 1).map_err(|_| Error::Contract("rule jump"))?;
        Ok(())
    }
}

/// Private foundation for an immutable-FD service. No production worker calls
/// this profile yet; closed B2 behavior remains unchanged.
pub(crate) fn native(
    first: u32,
    executable: &[u32],
    listener: u32,
    transfer: u32,
) -> Result<Filter, Error> {
    if ARCH == 0
        || !(5..=32).contains(&first)
        || listener != first
        || transfer < 64
        || transfer > 4096
        || executable.iter().any(|fd| *fd < 5 || *fd >= first)
    {
        return Err(Error::Contract("native descriptor layout"));
    }
    let mut f = Filter::new();
    f.push(LD, 0, 0, 4)?;
    f.push(JEQ, 1, 0, ARCH)?;
    f.deny()?;
    f.push(LD, 0, 0, 0)?;
    let mut readable = [0; 32];
    readable[0] = 0;
    readable[1] = 3;
    for (at, fd) in (5..first).enumerate() {
        readable[at + 2] = fd;
    }
    let read_count = (first - 5) as usize + 2;
    for call in [libc::SYS_read, libc::SYS_readv, libc::SYS_pread64] {
        f.rule(call, |f| f.bank(0, &readable[..read_count]))?;
    }
    for call in [libc::SYS_write, libc::SYS_writev, libc::SYS_pwrite64] {
        f.rule(call, |f| f.fds(0, &[1, 2, 3], None))?;
    }
    f.rule(libc::SYS_close, |f| f.bank(0, &[listener, transfer]))?;
    f.rule(libc::SYS_sendmsg, |f| f.fds(0, &[transfer], None))?;
    f.rule(libc::SYS_fcntl, |f| f.fds(1, &[libc::F_GETFD as u32, libc::F_GETFL as u32], None))?;
    for call in [libc::SYS_fstat, libc::SYS_lseek] {
        f.rule(call, |f| f.bank(0, &readable[..read_count]))?;
    }
    for call in [libc::SYS_openat, libc::SYS_openat2] {
        f.rule(call, |f| f.push(RET, 0, 0, NOTIFY))?;
    }
    #[cfg(target_arch = "x86_64")]
    f.rule(libc::SYS_open, |f| f.push(RET, 0, 0, NOTIFY))?;
    f.rule(libc::SYS_mmap, |f| {
        f.arg(2)?;
        f.push(JSET, 1, 0, libc::PROT_EXEC as u32)?;
        f.allow()?;
        f.no_bits(2, libc::PROT_WRITE as u32)?;
        f.no_bits(3, libc::MAP_ANONYMOUS as u32)?;
        f.bank(4, executable)
    })?;
    f.rule(libc::SYS_mprotect, |f| f.no_bits(2, libc::PROT_EXEC as u32))?;
    f.rule(libc::SYS_futex, |f| {
        f.arg(1)?;
        f.push(JSET, 1, 0, libc::FUTEX_PRIVATE_FLAG as u32)?;
        f.deny()
    })?;
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

pub(crate) fn build(first_dynamic: u32, executable: &[u32]) -> Result<Filter, Error> {
    build_role(first_dynamic, executable, ThreadRole::Single)
}

/// Fixed internal role; there is no caller-supplied syscall or clone mask.
pub(crate) fn checker_threads(first_dynamic: u32, executable: &[u32]) -> Result<Filter, Error> {
    build_role(first_dynamic, executable, ThreadRole::Checker)
}

pub(crate) fn checker_resources() -> Result<Filter, Error> {
    build_role(8, &[5], ThreadRole::CheckerResources)
}

#[derive(Clone, Copy)]
enum ThreadRole {
    Single,
    Checker,
    CheckerResources,
}

fn build_role(first_dynamic: u32, executable: &[u32], role: ThreadRole) -> Result<Filter, Error> {
    if ARCH == 0 {
        return Err(Error::Contract("unsupported audit architecture"));
    }
    if !(5..=32).contains(&first_dynamic)
        || executable.iter().any(|fd| *fd < 5 || *fd >= first_dynamic)
    {
        return Err(Error::Contract("descriptor layout"));
    }
    let mut f = Filter::new();
    f.push(LD, 0, 0, 4)?;
    f.push(JEQ, 1, 0, ARCH)?;
    f.deny()?;
    f.push(LD, 0, 0, 0)?;
    let mut readable = [0; 32];
    readable[0] = 0;
    readable[1] = 3;
    let mut read_count = 2;
    for fd in 5..first_dynamic {
        if matches!(role, ThreadRole::CheckerResources) && [6, 7].contains(&fd) {
            continue;
        }
        readable[read_count] = fd;
        read_count += 1;
    }
    for call in [libc::SYS_read, libc::SYS_readv] {
        f.rule(call, |f| f.fds(0, &readable[..read_count], Some(first_dynamic)))?;
    }
    f.rule(libc::SYS_pread64, |f| {
        if matches!(role, ThreadRole::CheckerResources) {
            resources::pread(f, &readable[..read_count])
        } else {
            f.fds(0, &readable[..read_count], Some(first_dynamic))
        }
    })?;
    for call in [libc::SYS_write, libc::SYS_writev, libc::SYS_pwrite64] {
        f.rule(call, |f| f.fds(0, &[1, 2, 3], Some(first_dynamic)))?;
    }
    f.rule(libc::SYS_close, |f| f.fds(0, &[], Some(first_dynamic)))?;
    f.rule(libc::SYS_fcntl, |f| f.fds(1, &[libc::F_GETFD as u32, libc::F_GETFL as u32], None))?;
    f.rule(libc::SYS_fstat, |_| Ok(()))?;
    f.rule(libc::SYS_lseek, |f| {
        if matches!(role, ThreadRole::CheckerResources) {
            resources::exclude(f, 0)?;
        }
        Ok(())
    })?;
    for call in [libc::SYS_ftruncate, libc::SYS_fsync, libc::SYS_fdatasync] {
        f.rule(call, |f| f.fds(0, &[], Some(first_dynamic)))?;
    }
    f.rule(libc::SYS_mmap, |f| {
        if matches!(role, ThreadRole::CheckerResources) {
            resources::exclude(f, 4)?;
        }
        f.arg(2)?;
        // Non-executable maps can use scratch or anonymous storage. Executable
        // maps can only read immutable inputs; protected FDs cannot be recycled.
        f.push(JSET, 1, 0, libc::PROT_EXEC as u32)?;
        f.allow()?;
        f.no_bits(2, libc::PROT_WRITE as u32)?;
        f.no_bits(3, libc::MAP_ANONYMOUS as u32)?;
        f.fds(4, executable, None)
    })?;
    f.rule(libc::SYS_mprotect, |f| f.no_bits(2, libc::PROT_EXEC as u32))?;
    if matches!(role, ThreadRole::Checker | ThreadRole::CheckerResources) {
        threads::append(&mut f)?;
    }
    if matches!(role, ThreadRole::CheckerResources) {
        resources::append(&mut f)?;
    }
    f.rule(libc::SYS_futex, |f| {
        f.arg(1)?;
        f.push(JSET, 1, 0, libc::FUTEX_PRIVATE_FLAG as u32)?;
        f.deny()
    })?;
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
    use super::*;
    pub(super) fn evaluate(
        filter: &Filter,
        arch: u32,
        syscall: libc::c_long,
        args: [u64; 6],
    ) -> u32 {
        let mut pc = 0;
        let mut a = 0;
        for _ in 0..MAX {
            let i = filter.instructions[pc];
            match i.code {
                LD => {
                    a = match i.k {
                        0 => syscall as u32,
                        4 => arch,
                        offset if offset >= 16 && offset < 64 && offset % 4 == 0 => {
                            let value = args[((offset - 16) / 8) as usize];
                            (value >> (8 * ((offset - 16) % 8))) as u32
                        }
                        _ => panic!("unsupported offset"),
                    }
                }
                JEQ | JGE | JSET => {
                    let yes = match i.code {
                        JEQ => a == i.k,
                        JGE => a >= i.k,
                        _ => a & i.k != 0,
                    };
                    pc += usize::from(if yes { i.jt } else { i.jf });
                }
                RET => return i.k,
                _ => panic!("unsupported opcode"),
            }
            pc += 1;
            assert!(pc < filter.len);
        }
        panic!("nonterminating filter")
    }
    fn decision(call: libc::c_long, args: [u64; 6]) -> u32 {
        evaluate(&build(7, &[5]).unwrap(), ARCH, call, args)
    }
    #[test]
    fn native_service_bank_and_max_layout_keep_roles_closed() {
        let all: Vec<u32> = (5..32).collect();
        for executable in [&[][..], &all[..]] {
            let f = native(32, executable, 32, 128).unwrap();
            assert!(f.len <= MAX);
            for fd in 0..140u64 {
                let bank = (33..=63).contains(&fd);
                let close = bank || fd == 32 || fd == 128;
                assert_eq!(
                    evaluate(&f, ARCH, libc::SYS_close, [fd, 0, 0, 0, 0, 0]),
                    if close { ALLOW } else { KILL }
                );
                assert_eq!(
                    evaluate(&f, ARCH, libc::SYS_sendmsg, [fd, 0, 0, 0, 0, 0]),
                    if fd == 128 { ALLOW } else { KILL }
                );
                let exec = bank || executable.contains(&(fd as u32));
                assert_eq!(
                    evaluate(
                        &f,
                        ARCH,
                        libc::SYS_mmap,
                        [0, 4096, libc::PROT_EXEC as u64, libc::MAP_PRIVATE as u64, fd, 0]
                    ),
                    if exec { ALLOW } else { KILL }
                );
                assert_eq!(
                    evaluate(&f, ARCH, libc::SYS_write, [fd, 0, 0, 0, 0, 0]),
                    if [1, 2, 3].contains(&fd) { ALLOW } else { KILL }
                );
            }
            for call in [libc::SYS_openat, libc::SYS_openat2] {
                assert_eq!(evaluate(&f, ARCH, call, [0; 6]), NOTIFY);
            }
            for call in [
                libc::SYS_recvmsg,
                libc::SYS_seccomp,
                libc::SYS_prctl,
                libc::SYS_ftruncate,
                libc::SYS_clone,
                libc::SYS_execve,
                libc::SYS_dup,
                libc::SYS_pkey_mprotect,
            ] {
                assert_eq!(evaluate(&f, ARCH, call, [0; 6]), KILL);
            }
            assert_eq!(evaluate(&f, ARCH ^ 1, libc::SYS_openat, [0; 6]), KILL);
        }
    }
    #[test]
    fn architecture_and_unknown_operations_never_fall_through() {
        let f = build(7, &[5]).unwrap();
        assert_eq!(evaluate(&f, ARCH ^ 1, libc::SYS_read, [0; 6]), KILL);
        for call in [
            libc::SYS_execve,
            libc::SYS_clone,
            libc::SYS_socket,
            libc::SYS_sendmsg,
            libc::SYS_recvmsg,
            libc::SYS_ptrace,
            libc::SYS_unshare,
            libc::SYS_ioctl,
            libc::SYS_dup,
            libc::SYS_dup3,
            libc::SYS_prctl,
            libc::SYS_seccomp,
        ] {
            assert_eq!(decision(call, [0; 6]), KILL);
        }
        assert_eq!(decision(0x4000_0000, [0; 6]), KILL);
    }
    #[test]
    fn protected_descriptors_cannot_be_reused_or_written() {
        for fd in 0..7 {
            assert_eq!(decision(libc::SYS_close, [fd, 0, 0, 0, 0, 0]), KILL);
        }
        assert_eq!(decision(libc::SYS_close, [7, 0, 0, 0, 0, 0]), ALLOW);
        assert_eq!(decision(libc::SYS_write, [5, 0, 0, 0, 0, 0]), KILL);
        assert_eq!(decision(libc::SYS_read, [1, 0, 0, 0, 0, 0]), KILL);
        assert_eq!(decision(libc::SYS_read, [5, 0, 0, 0, 0, 0]), ALLOW);
        assert_eq!(decision(libc::SYS_fcntl, [5, libc::F_DUPFD as u64, 0, 0, 0, 0]), KILL);
    }
    #[test]
    fn executable_maps_only_use_immutable_declared_inputs() {
        let map = |prot: i32, flags: i32, fd: u64| {
            decision(libc::SYS_mmap, [0, 4096, prot as u64, flags as u64, fd, 0])
        };
        assert_eq!(map(libc::PROT_READ | libc::PROT_EXEC, libc::MAP_PRIVATE, 5), ALLOW);
        assert_eq!(map(libc::PROT_WRITE | libc::PROT_EXEC, libc::MAP_PRIVATE, 5), KILL);
        assert_eq!(map(libc::PROT_EXEC, libc::MAP_PRIVATE | libc::MAP_ANONYMOUS, 5), KILL);
        for fd in [4, 6, 7, u64::MAX] {
            assert_eq!(map(libc::PROT_EXEC, libc::MAP_PRIVATE, fd), KILL);
        }
        assert_eq!(
            map(
                libc::PROT_READ | libc::PROT_WRITE,
                libc::MAP_PRIVATE | libc::MAP_ANONYMOUS,
                u64::MAX
            ),
            ALLOW
        );
        assert_eq!(decision(libc::SYS_mprotect, [0, 4096, libc::PROT_EXEC as u64, 0, 0, 0]), KILL);
    }
    #[test]
    fn ambient_filesystem_opens_and_shared_futexes_are_denied() {
        assert_eq!(decision(libc::SYS_openat, [4, 0, 0, 0, 0, 0]), KILL);
        assert_eq!(decision(libc::SYS_openat, [3, 0, 0, 0, 0, 0]), KILL);
        assert_eq!(decision(libc::SYS_openat, [libc::AT_FDCWD as u64, 0, 0, 0, 0, 0]), KILL);
        assert_eq!(decision(libc::SYS_getdents64, [4, 0, 0, 0, 0, 0]), KILL);
        assert_eq!(decision(libc::SYS_mkdirat, [4, 0, 0, 0, 0, 0]), KILL);
        assert_eq!(decision(libc::SYS_futex, [0, libc::FUTEX_WAIT as u64, 0, 0, 0, 0]), KILL);
        assert_eq!(
            decision(
                libc::SYS_futex,
                [0, (libc::FUTEX_WAIT | libc::FUTEX_PRIVATE_FLAG) as u64, 0, 0, 0, 0]
            ),
            ALLOW
        );
    }
    #[test]
    fn maximum_input_layout_fits_with_mixed_or_all_executable_roles() {
        let all = (5..32).collect::<Vec<_>>();
        let mixed = all.iter().copied().filter(|fd| fd % 2 == 1).collect::<Vec<_>>();
        for executable in [&all[..], &mixed[..], &[][..]] {
            let f = build(32, executable).unwrap();
            assert!(f.len < MAX);
            for fd in 5..32 {
                assert_eq!(evaluate(&f, ARCH, libc::SYS_read, [fd, 0, 0, 0, 0, 0]), ALLOW);
                assert_eq!(evaluate(&f, ARCH, libc::SYS_write, [fd, 0, 0, 0, 0, 0]), KILL);
                assert_eq!(evaluate(&f, ARCH, libc::SYS_close, [fd, 0, 0, 0, 0, 0]), KILL);
                assert_eq!(
                    evaluate(
                        &f,
                        ARCH,
                        libc::SYS_mmap,
                        [0, 4096, libc::PROT_EXEC as u64, libc::MAP_PRIVATE as u64, fd, 0]
                    ),
                    if executable.contains(&(fd as u32)) { ALLOW } else { KILL }
                );
            }
        }
    }
}
