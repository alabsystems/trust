//! Actual OS controls require an exclusively delegated finite cgroup parent.
//! They use real clone3, cgroup events and pidfd wait; no modeled OS decisions.
use std::ffi::CString;
use std::time::{Duration, Instant};

use trust_process_isolation::Limits;

use super::*;

struct Domain {
    parent: File,
    directory: File,
    identity: super::super::tree::Identity,
    name: CString,
}
impl Drop for Domain {
    fn drop(&mut self) {
        // Test-only namespace retirement refuses a replacement. Production
        // Tree retains only held-FD kill/observation, never pathname removal.
        // SAFETY: fixture-only held parent and checked fresh basename; final
        // aliases refuse and the new descriptor is handled immediately.
        let fd = unsafe {
            libc::openat(
                self.parent.as_raw_fd(),
                self.name.as_ptr(),
                libc::O_RDONLY | libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC,
            )
        };
        if fd >= 0 {
            // SAFETY: successful openat returned a new owned descriptor.
            let current = unsafe { File::from_raw_fd(fd) };
            if super::super::tree::Identity::capture(&current, super::super::tree::Role::Directory)
                .ok()
                == Some(self.identity)
            {
                // SAFETY: exact fresh owned directory was reauthenticated;
                // unlinkat cannot remove a nonempty/populated cgroup.
                unsafe {
                    libc::unlinkat(self.parent.as_raw_fd(), self.name.as_ptr(), libc::AT_REMOVEDIR);
                }
            }
        }
    }
}
fn tree() -> Result<(Tree, Domain, Budget), Box<dyn std::error::Error>> {
    let parent = CString::new(std::env::var("TRUST_WORKER_TEST_CGROUP_PARENT")?)?;
    // SAFETY: fixture-only explicit delegated parent; final symlinks refuse.
    let fd = unsafe {
        libc::open(
            parent.as_ptr(),
            libc::O_RDONLY | libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC,
        )
    };
    if fd < 0 {
        return Err(system("test delegated parent").into());
    }
    // SAFETY: successful open returned a new owned directory.
    let parent = unsafe { File::from_raw_fd(fd) };
    static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(1);
    let name = CString::new(format!(
        "static-tree-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
    ))?;
    let budget = Budget::new(
        Limits {
            frame_bytes: 4096,
            wire_bytes: 8192,
            allocation_bytes: 8192,
            values: 100,
            work: 100_000_000,
            calls: 100,
            live_handles: 64,
            depth: 16,
        },
        Instant::now() + Duration::from_secs(3),
    )?;
    let tree = Tree::create(&parent, &name, 64 * 1024 * 1024, &budget)?;
    let directory = tree.directory.try_clone()?;
    let identity = tree.identity;
    Ok((tree, Domain { parent, directory, identity, name }, budget))
}
fn born(mut tree: Tree, budget: &Budget, spin: bool) -> Result<Custody, Error> {
    let group = tree.arm_birth(budget)?;
    let mut pidfd = -1;
    let (mut ready, ready_write) = pipe()?;
    nonblocking(ready.as_raw_fd())?;
    // SAFETY: real fork-equivalent clone3 with no shared VM. Child performs
    // only async-signal-safe syscall/_exit and never accesses Rust locks/heap.
    let pid = unsafe { contained_clone(group, &mut pidfd) };
    if pid < 0 {
        return Err(system("test contained birth"));
    }
    if pid == 0 {
        // SAFETY: child closes all inherited capabilities before deliberately
        // leaving its parent's process group. Cgroup membership is independent.
        unsafe {
            if libc::dup2(ready_write.as_raw_fd(), 1) < 0
                || libc::syscall(libc::SYS_close_range, 3u32, u32::MAX, 0u32) != 0
                || libc::setsid() < 0
                || libc::write(1, b"S".as_ptr().cast(), 1) != 1
            {
                libc::_exit(120);
            }
            if spin {
                loop {
                    libc::pause();
                }
            }
            libc::_exit(73);
        }
    }
    if pidfd < 0 {
        let _ = tree.stop();
        return Err(contract("test omitted birth pidfd"));
    }
    // SAFETY: clone3 returned this exact new birth pidfd.
    let pidfd = unsafe { OwnedFd::from_raw_fd(pidfd) };
    let custody = Custody::Tree { pid, pidfd, reaped: false, tree, budget: budget.clone() };
    drop(ready_write);
    use std::io::Read;
    let mut marker = [0];
    loop {
        checked(budget)?;
        match ready.read(&mut marker) {
            Ok(1) if marker == *b"S" => return Ok(custody),
            Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => {
                std::thread::sleep(Duration::from_millis(1))
            }
            _ => return Err(contract("test child did not actually reach setsid")),
        }
    }
}

#[test]
#[ignore = "requires exclusive finite cgroup-v2 delegated test parent and clone3; select explicitly with --ignored"]
fn setsid_leader_is_retired_by_held_domain_not_process_group_guess()
-> Result<(), Box<dyn std::error::Error>> {
    let (tree, domain, budget) = tree()?;
    let mut child = born(tree, &budget, true)?;
    assert!(child.used_pidfd());
    let status = child.stop_and_reap()?;
    assert!(libc::WIFSIGNALED(status));
    assert_eq!(libc::WTERMSIG(status), libc::SIGKILL);
    assert!(child.reaped());
    let events = super::super::tree::Control::open(
        &domain.directory,
        c"cgroup.events",
        super::super::tree::Access::Read,
    )?;
    let mut bytes = [0; 64];
    let n = events.read(&mut bytes, &budget)?;
    assert!(super::super::tree::empty_events(&bytes[..n])?);
    Ok(())
}

#[test]
#[ignore = "requires exclusive finite cgroup-v2 delegated test parent and clone3; select explicitly with --ignored"]
fn original_hard_exit_status_and_recursive_empty_domain_are_both_required()
-> Result<(), Box<dyn std::error::Error>> {
    let (tree, _domain, budget) = tree()?;
    let mut child = born(tree, &budget, false)?;
    while !child.exited()? {
        std::thread::sleep(Duration::from_millis(1));
    }
    let status = child.stop_and_reap()?;
    assert_eq!(libc::WEXITSTATUS(status), 73);
    assert!(libc::WIFEXITED(status));
    assert!(child.reaped());
    Ok(())
}

#[test]
#[ignore = "requires exclusive finite cgroup-v2 delegated test parent; select explicitly with --ignored"]
fn existing_named_domain_cannot_be_adopted_or_used_after_shared_refusal()
-> Result<(), Box<dyn std::error::Error>> {
    let (mut tree, domain, budget) = tree()?;
    assert!(Tree::create(&domain.parent, &domain.name, 64 * 1024 * 1024, &budget).is_err());
    assert!(budget.check().is_err());
    assert!(tree.arm_birth(&budget).is_err());
    assert!(!tree.armed);
    Ok(())
}

#[test]
#[ignore = "requires exclusive finite cgroup-v2 delegated test parent; select explicitly with --ignored"]
fn actual_task_cap_tampering_refuses_before_birth_and_latches_owner()
-> Result<(), Box<dyn std::error::Error>> {
    let (mut tree, domain, budget) = tree()?;
    // Actual test-owned control mutation, not a caller-provided mock fact.
    super::super::tree::set_scalar(&domain.directory, c"pids.max", 2)?;
    assert!(tree.arm_birth(&budget).is_err());
    assert!(budget.check().is_err());
    assert!(!tree.armed);
    Ok(())
}

#[test]
#[ignore = "requires exclusive finite cgroup-v2 delegated test parent and clone3; select explicitly with --ignored"]
fn sticky_cancellation_does_not_disable_held_tree_retirement()
-> Result<(), Box<dyn std::error::Error>> {
    let (tree, _domain, budget) = tree()?;
    let mut child = born(tree, &budget, true)?;
    let original = budget.deadline();
    budget.cancel();
    assert!(child.exited().is_err());
    let status = child.stop_and_reap()?;
    assert!(libc::WIFSIGNALED(status));
    assert!(child.reaped());
    assert!(budget.check().is_err());
    assert_eq!(budget.deadline(), original);
    Ok(())
}

#[test]
#[ignore = "requires exclusive finite cgroup-v2 delegated test parent and clone3; select explicitly with --ignored"]
fn relaxed_actual_cap_after_birth_cannot_produce_successful_retirement_receipt()
-> Result<(), Box<dyn std::error::Error>> {
    let (tree, domain, budget) = tree()?;
    let mut child = born(tree, &budget, true)?;
    super::super::tree::set_scalar(&domain.directory, c"pids.max", 2)?;
    assert!(child.exited().is_err());
    assert!(budget.check().is_err());
    assert!(child.stop_and_reap().is_err());
    // A direct child was reaped, but changed caps prevent a successful owned
    // closure. No fallback process-group or fresh owner can mask that refusal.
    assert!(child.reaped());
    Ok(())
}
