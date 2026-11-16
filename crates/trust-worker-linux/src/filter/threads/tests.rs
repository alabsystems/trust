use super::super::tests::evaluate;
use super::super::{ALLOW, ARCH, KILL, build, checker_threads, native};
use super::{PTHREAD_FLAGS, RSEQ_SIG, UNAVAILABLE};

fn decision(call: libc::c_long, args: [u64; 6]) -> u32 {
    evaluate(&checker_threads(7, &[5]).unwrap(), ARCH, call, args)
}
#[test]
fn only_the_exact_full_width_pthread_clone_word_is_admitted() {
    assert_eq!(decision(libc::SYS_clone, [u64::from(PTHREAD_FLAGS), 0, 0, 0, 0, 0]), ALLOW);
    for bit in 0..64 {
        assert_eq!(
            decision(libc::SYS_clone, [u64::from(PTHREAD_FLAGS) ^ (1u64 << bit), 0, 0, 0, 0, 0]),
            KILL,
            "bit {bit}"
        );
    }
    for flags in [
        0,
        libc::SIGCHLD as u64,
        libc::CLONE_VM as u64,
        (libc::CLONE_VM | libc::CLONE_VFORK | libc::SIGCHLD) as u64,
    ] {
        assert_eq!(decision(libc::SYS_clone, [flags, 0, 0, 0, 0, 0]), KILL);
    }
}
#[test]
fn clone3_and_optional_metadata_probes_return_only_enosys() {
    assert_eq!(decision(libc::SYS_clone3, [u64::MAX; 6]), UNAVAILABLE);
    assert_eq!(decision(libc::SYS_sched_getaffinity, [u64::MAX; 6]), UNAVAILABLE);
    assert_eq!(decision(libc::SYS_prctl, [super::PR_SET_VMA as u64, 0, 0, 0, 0, 0]), UNAVAILABLE);
    assert_eq!(decision(libc::SYS_prctl, [libc::PR_SET_NAME as u64, 0, 0, 0, 0, 0]), ALLOW);
    for option in [libc::PR_SET_DUMPABLE, libc::PR_SET_NO_NEW_PRIVS, libc::PR_SET_SECCOMP] {
        assert_eq!(decision(libc::SYS_prctl, [option as u64, 0, 0, 0, 0, 0]), KILL);
    }
}
#[test]
fn rseq_and_robust_registration_are_shape_checked() {
    assert_eq!(decision(libc::SYS_set_robust_list, [0, 24, 0, 0, 0, 0]), ALLOW);
    assert_eq!(decision(libc::SYS_set_robust_list, [0, 32, 0, 0, 0, 0]), KILL);
    assert_eq!(decision(libc::SYS_set_robust_list, [0, 24 | (1u64 << 32), 0, 0, 0, 0]), KILL);
    let valid = [0, 32, 0, RSEQ_SIG as u64, 0, 0];
    assert_eq!(decision(libc::SYS_rseq, valid), ALLOW);
    for slot in [1, 2, 3] {
        let mut invalid = valid;
        invalid[slot] ^= 1;
        assert_eq!(decision(libc::SYS_rseq, invalid), KILL);
    }
}
#[test]
fn shared_futex_admission_is_wait_only_and_private_operations_are_finite() {
    for operation in 0..1024 {
        let valid = [0, 9, 9 | 256, 128, 129, 9 | 128, 9 | 128 | 256].contains(&operation);
        assert_eq!(
            decision(libc::SYS_futex, [0, operation, 0, 0, 0, 0]),
            if valid { ALLOW } else { KILL }
        );
    }
}
#[test]
fn process_external_signal_exec_and_namespace_authority_stay_denied() {
    for call in [
        libc::SYS_execve,
        libc::SYS_execveat,
        libc::SYS_unshare,
        libc::SYS_setns,
        libc::SYS_ptrace,
        libc::SYS_pidfd_open,
        libc::SYS_kill,
        libc::SYS_tgkill,
        libc::SYS_tkill,
        libc::SYS_seccomp,
        libc::SYS_setpgid,
        libc::SYS_setsid,
    ] {
        assert_eq!(decision(call, [0; 6]), KILL);
    }
    assert_eq!(
        evaluate(
            &checker_threads(7, &[5]).unwrap(),
            ARCH ^ 1,
            libc::SYS_clone,
            [PTHREAD_FLAGS as u64, 0, 0, 0, 0, 0]
        ),
        KILL
    );
}
#[test]
fn existing_single_thread_and_native_profiles_do_not_gain_thread_admission() {
    for f in [build(7, &[5]).unwrap(), native(7, &[5], 7, 128).unwrap()] {
        for call in [
            libc::SYS_clone,
            libc::SYS_clone3,
            libc::SYS_set_robust_list,
            libc::SYS_rseq,
            libc::SYS_prctl,
        ] {
            assert_eq!(evaluate(&f, ARCH, call, [PTHREAD_FLAGS as u64, 0, 0, 0, 0, 0]), KILL);
        }
    }
    assert_eq!(
        evaluate(
            &checker_threads(32, &(5..32).collect::<Vec<_>>()).unwrap(),
            ARCH,
            libc::SYS_read,
            [5, 0, 0, 0, 0, 0]
        ),
        ALLOW
    );
}
