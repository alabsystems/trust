//! Fixed GNU pthread profile for an internally embedded static checker.
//!
//! Audited against glibc2.39 nptl/pthread_create.c, pthread_join_common.c and
//! sysdeps/unix/sysv/linux/clone-internal.c (links in the source audit note).
//! This is a restriction profile, never executable or proof authority.
use super::{Error, Filter, JEQ, LD, RET};

const ERRNO: u32 = 0x0005_0000;
pub(super) const UNAVAILABLE: u32 = ERRNO | libc::ENOSYS as u32;
pub(super) const PTHREAD_FLAGS: u32 = (libc::CLONE_VM
    | libc::CLONE_FS
    | libc::CLONE_FILES
    | libc::CLONE_SIGHAND
    | libc::CLONE_THREAD
    | libc::CLONE_SYSVSEM
    | libc::CLONE_SETTLS
    | libc::CLONE_PARENT_SETTID
    | libc::CLONE_CHILD_CLEARTID) as u32;
#[cfg(target_arch = "aarch64")]
const RSEQ_SIG: u32 = 0xd428_bc00;
#[cfg(target_arch = "x86_64")]
const RSEQ_SIG: u32 = 0x5305_3053;
#[cfg(not(any(target_arch = "aarch64", target_arch = "x86_64")))]
const RSEQ_SIG: u32 = 0;
const PR_SET_VMA: u32 = 0x5356_4d41;

fn equal(f: &mut Filter, index: u32, value: u32) -> Result<(), Error> {
    f.arg(index)?;
    f.push(JEQ, 1, 0, value)?;
    f.deny()
}
fn one_of(f: &mut Filter, index: u32, values: &[u32]) -> Result<(), Error> {
    f.arg(index)?;
    for value in values {
        f.push(JEQ, 0, 1, *value)?;
        f.allow()?;
    }
    f.deny()
}

pub(super) fn append(f: &mut Filter) -> Result<(), Error> {
    // clone's flags are unsigned long. Check both halves: accepting a valid
    // low word while ignoring CLONE_CLEAR_SIGHAND/new high flags is unsafe.
    f.rule(libc::SYS_clone, |f| {
        f.push(LD, 0, 0, 20)?;
        f.push(JEQ, 1, 0, 0)?;
        f.deny()?;
        equal(f, 0, PTHREAD_FLAGS)
    })?;
    // seccomp cannot dereference clone3's pointer without a broker/race. GNU
    // __clone_internal falls back only on ENOSYS to the checked legacy word.
    f.rule(libc::SYS_clone3, |f| f.push(RET, 0, 0, UNAVAILABLE))?;
    f.rule(libc::SYS_set_robust_list, |f| {
        f.push(LD, 0, 0, 28)?;
        f.push(JEQ, 1, 0, 0)?;
        f.deny()?;
        equal(f, 1, 24)
    })?;
    f.rule(libc::SYS_rseq, |f| {
        equal(f, 1, 32)?;
        equal(f, 2, 0)?;
        equal(f, 3, RSEQ_SIG)
    })?;
    f.rule(libc::SYS_futex, |f| {
        // Shared WAIT/WAIT_BITSET are needed for kernel CHILD_CLEARTID wakeup
        // and pthread creation-error cleanup. No shared wake, PI, requeue or
        // other operation can address an unrelated process through this role.
        let private = libc::FUTEX_PRIVATE_FLAG as u32;
        let realtime = libc::FUTEX_CLOCK_REALTIME as u32;
        one_of(
            f,
            1,
            &[
                libc::FUTEX_WAIT as u32,
                libc::FUTEX_WAIT_BITSET as u32,
                libc::FUTEX_WAIT_BITSET as u32 | realtime,
                libc::FUTEX_WAIT as u32 | private,
                libc::FUTEX_WAKE as u32 | private,
                libc::FUTEX_WAIT_BITSET as u32 | private,
                libc::FUTEX_WAIT_BITSET as u32 | private | realtime,
            ],
        )
    })?;
    f.rule(libc::SYS_prctl, |f| {
        f.arg(0)?;
        f.push(JEQ, 0, 1, libc::PR_SET_NAME as u32)?;
        f.allow()?;
        // glibc2.39 optionally annotates stack VMAs. Its void helper ignores
        // refusal. Do not admit general prctl or memory-map metadata mutation.
        f.push(JEQ, 0, 1, PR_SET_VMA)?;
        f.push(RET, 0, 0, UNAVAILABLE)?;
        f.deny()
    })?;
    // pthread_getattr_np probes affinity by TID. Its audited ENOSYS path
    // retains valid stack attributes; no cross-process query is performed.
    f.rule(libc::SYS_sched_getaffinity, |f| f.push(RET, 0, 0, UNAVAILABLE))?;
    f.rule(libc::SYS_clock_nanosleep, |f| {
        f.arg(0)?;
        f.push(JEQ, 2, 0, libc::CLOCK_REALTIME as u32)?;
        f.push(JEQ, 1, 0, libc::CLOCK_MONOTONIC as u32)?;
        f.deny()?;
        one_of(f, 1, &[0, libc::TIMER_ABSTIME as u32])
    })?;
    f.rule(libc::SYS_nanosleep, |_| Ok(()))?;
    Ok(())
}

#[cfg(test)]
mod tests;
