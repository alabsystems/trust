use std::fs::OpenOptions;
use std::num::NonZeroU32;
use std::os::unix::fs::OpenOptionsExt;
use std::time::{Duration, Instant};

use trust_build_cpu::{Pool, SlotState};

use super::*;

#[test]
fn sampled_pid_must_be_an_actual_owned_child() {
    assert!(owned_child_usage(std::process::id()).is_none());
}

#[test]
fn child_attribution_preserves_credit_and_restores_after_join() {
    let temp = tempfile::tempdir().unwrap();
    let legacy = temp.path().join("legacy");
    std::fs::create_dir(&legacy).unwrap();
    let files = ["slot-0", "admission.lock"]
        .into_iter()
        .map(|name| {
            let file = OpenOptions::new()
                .read(true)
                .write(true)
                .create_new(true)
                .mode(0o600)
                .open(legacy.join(name))
                .unwrap();
            file.lock_shared().unwrap();
            file
        })
        .collect();
    let fence = Arc::new(LegacyFence::from_inherited(&legacy, 1, files).unwrap());
    let pool = Pool::open_in(temp.path(), NonZeroU32::new(1).unwrap()).unwrap();
    let parent = trust_build_cpu::process_cpu::read(std::process::id()).unwrap().owner;
    let lease = Arc::new(pool.try_acquire(parent).unwrap().unwrap());
    let resources = ChildResources { leases: vec![lease], fence };
    let mut command = std::process::Command::new("/bin/sleep");
    command.arg("0.3");
    resources.configure(&mut command);
    let child = command.spawn().unwrap();
    drop(command);
    let pid = child.id();
    let observed = pool.clone();
    let ready = Arc::new(std::sync::Barrier::new(2));
    let started = Arc::clone(&ready);
    let observer = std::thread::spawn(move || {
        started.wait();
        let deadline = Instant::now() + Duration::from_secs(2);
        while Instant::now() < deadline {
            if observed.snapshot().is_ok_and(|slots| {
                matches!(slots[0], SlotState::Held { reported_owner: Some(owner), .. }
                    if owner.pid == pid && owner.birth.is_some())
            }) {
                return true;
            }
            std::thread::sleep(Duration::from_millis(1));
        }
        false
    });
    ready.wait();
    assert!(resources.wait_with_output(child).unwrap().status.success());
    assert!(observer.join().unwrap(), "the real child must own sampled CPU usage");
    assert!(matches!(pool.snapshot().unwrap()[0],
        SlotState::Held { reported_owner: Some(owner), .. } if owner == parent));
    assert!(pool.try_acquire(parent).unwrap().is_none());
    drop(resources);
    assert!(pool.try_acquire(parent).unwrap().is_some());
}
