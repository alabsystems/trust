use super::super::tests::evaluate;
use super::super::{ALLOW, ARCH, KILL, build, checker_resources, checker_threads};

fn decision(call: libc::c_long, args: [u64; 6]) -> u32 {
    evaluate(&checker_resources().unwrap(), ARCH, call, args)
}

#[test]
fn live_roles_only_admit_bounded_offset_zero_pread() {
    for fd in [6, 7] {
        for count in [0, 1, 256, 8192] {
            assert_eq!(decision(libc::SYS_pread64, [fd, 0, count, 0, 0, 0]), ALLOW);
        }
        for count in [8193, 1u64 << 32, u64::MAX] {
            assert_eq!(decision(libc::SYS_pread64, [fd, 0, count, 0, 0, 0]), KILL);
        }
        for offset in [1, 1u64 << 32, u64::MAX] {
            assert_eq!(decision(libc::SYS_pread64, [fd, 0, 1, offset, 0, 0]), KILL);
        }
    }
}

#[test]
fn live_roles_cannot_be_mutated_recycled_or_mapped() {
    for fd in [6, 7] {
        for call in [
            libc::SYS_read,
            libc::SYS_readv,
            libc::SYS_write,
            libc::SYS_writev,
            libc::SYS_pwrite64,
            libc::SYS_close,
            libc::SYS_ftruncate,
            libc::SYS_fsync,
            libc::SYS_fdatasync,
            libc::SYS_lseek,
            libc::SYS_dup,
            libc::SYS_dup3,
        ] {
            assert_eq!(decision(call, [fd, 0, 0, 0, 0, 0]), KILL, "{fd} {call}");
        }
        assert_eq!(
            decision(
                libc::SYS_mmap,
                [0, 4096, libc::PROT_READ as u64, libc::MAP_PRIVATE as u64, fd, 0]
            ),
            KILL
        );
    }
}

#[test]
fn resource_entry_allows_self_usage_without_general_kernel_authority() {
    assert_eq!(decision(libc::SYS_getrusage, [0; 6]), ALLOW);
    for who in [u64::MAX, 1, 1u64 << 32] {
        assert_eq!(decision(libc::SYS_getrusage, [who, 0, 0, 0, 0, 0]), KILL);
    }
    #[cfg(target_arch = "x86_64")]
    assert_eq!(decision(libc::SYS_setrlimit, [0; 6]), KILL);
    for call in [libc::SYS_openat, libc::SYS_openat2, libc::SYS_execve, libc::SYS_prlimit64] {
        assert_eq!(decision(call, [0; 6]), KILL, "{call}");
    }
}

#[test]
fn ordinary_input_scratch_and_other_profiles_preserve_their_roles() {
    assert_eq!(decision(libc::SYS_read, [5, 0, 8192, 0, 0, 0]), ALLOW);
    assert_eq!(decision(libc::SYS_write, [5, 0, 1, 0, 0, 0]), KILL);
    assert_eq!(decision(libc::SYS_pread64, [8, 0, 16384, 42, 0, 0]), ALLOW);
    assert_eq!(decision(libc::SYS_close, [8, 0, 0, 0, 0, 0]), ALLOW);
    for profile in [build(6, &[5]).unwrap(), checker_threads(6, &[5]).unwrap()] {
        assert_eq!(evaluate(&profile, ARCH, libc::SYS_getrusage, [0; 6]), KILL);
        assert_eq!(evaluate(&profile, ARCH, libc::SYS_openat, [0; 6]), KILL);
    }
}
