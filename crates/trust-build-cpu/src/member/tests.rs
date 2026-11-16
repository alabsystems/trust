use std::fs::{File, OpenOptions};
use std::io::{Read as _, Write as _};
use std::num::NonZeroU32;
use std::os::unix::fs::OpenOptionsExt as _;
use std::os::unix::process::CommandExt as _;
use std::process::{Child, Command, Stdio};
use std::time::{Duration, Instant};

use super::*;

const ACTOR: &str = "member::tests::inherited_actor";

struct ChildGuard(Child);
impl Drop for ChildGuard {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}

fn fence(directory: &std::path::Path) -> Arc<LegacyFence> {
    crate::tests::private_dir(directory);
    let files = ["slot-0", "admission.lock"]
        .into_iter()
        .map(|name| {
            let file = OpenOptions::new()
                .create_new(true)
                .read(true)
                .write(true)
                .mode(0o600)
                .open(directory.join(name))
                .unwrap();
            file.lock_shared().unwrap();
            file
        })
        .collect();
    Arc::new(LegacyFence::from_inherited(directory, 1, files).unwrap())
}

#[test]
fn retained_member_owns_original_cpu_fence_and_gnu_through_actual_child() {
    let _fixture = crate::tests::kernel_fixture();
    let directory = crate::tests::private_tempdir();
    let pool = crate::Pool::open_in(directory.path(), NonZeroU32::new(1).unwrap()).unwrap();
    let owner = crate::Owner::current(None);
    let lease = Arc::new(pool.try_acquire(owner).unwrap().unwrap());
    let fence_path = directory.path().join("legacy");
    let original_fence = fence(&fence_path);
    let original_gnu = Jobserver::new(1).unwrap();
    let member = MemberScheduling::retain(lease, original_fence, original_gnu).unwrap();
    assert!(pool.try_acquire(owner).unwrap().is_none());
    let advertised = member.environment().into_iter().collect::<std::collections::BTreeMap<_, _>>();
    let owned = member.descriptors().map(|fd| fd.as_raw_fd()).collect::<Vec<_>>();
    assert_eq!(advertised[IMPLICIT_FD_ENV], OsString::from(owned[0].to_string()));
    assert_eq!(
        advertised["BUILD_SLOT_FENCE_FDS"],
        OsString::from(format!("{},{}", owned[1], owned[2]))
    );
    for file in member.descriptors() {
        let flags = unsafe { libc::fcntl(file.as_raw_fd(), libc::F_GETFD) };
        assert!(flags >= 0 && flags & libc::FD_CLOEXEC != 0);
    }

    let mut command = Command::new(std::env::current_exe().unwrap());
    command
        .args(["--exact", ACTOR, "--ignored", "--nocapture"])
        .env_clear()
        .env("MEMBER_TEST_POOL", directory.path())
        .env("MEMBER_TEST_FENCE", &fence_path)
        .envs(advertised)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::inherit());
    member.jobserver().configure(&mut command);
    // The production ProcessBuilder adapter explicitly inherits these same
    // descriptions. This child-only fixture hook leaves parent flags intact.
    unsafe {
        command.pre_exec(move || {
            for fd in &owned {
                if libc::fcntl(*fd, libc::F_SETFD, 0) != 0 {
                    return Err(io::Error::last_os_error());
                }
            }
            Ok(())
        });
    }
    let mut child = ChildGuard(command.spawn().unwrap());
    let output = child.0.stdout.as_mut().unwrap();
    let end = Instant::now() + Duration::from_secs(60);
    let mut bytes = Vec::new();
    while !bytes.ends_with(b"actual-member-ready\n") {
        let remaining = end.saturating_duration_since(Instant::now());
        assert!(!remaining.is_zero(), "actual member did not start");
        let mut descriptor =
            libc::pollfd { fd: output.as_raw_fd(), events: libc::POLLIN, revents: 0 };
        let ready =
            unsafe { libc::poll(&mut descriptor, 1, remaining.as_millis().min(1000) as i32) };
        assert!(ready >= 0);
        if ready != 0 {
            let mut byte = [0];
            assert_eq!(output.read(&mut byte).unwrap(), 1, "member closed before readiness");
            bytes.push(byte[0]);
            assert!(bytes.len() < 4096);
        }
    }
    // The actual child now holds the inherited original descriptions. Neither
    // dropping the member owner nor diagnostics can turn this into a free unit.
    drop(member);
    assert!(pool.try_acquire(owner).unwrap().is_none());
    let fence_probe = File::open(fence_path.join("slot-0")).unwrap();
    assert!(fence_probe.try_lock().is_err());
    child.0.stdin.take().unwrap().write_all(b"x").unwrap();
    let status = loop {
        if let Some(status) = child.0.try_wait().unwrap() {
            break status;
        }
        assert!(Instant::now() < end, "actual member did not drain");
        std::thread::sleep(Duration::from_millis(5));
    };
    assert!(status.success());
    assert!(pool.try_acquire(owner).unwrap().is_some());
    fence_probe.try_lock().unwrap();
}

#[test]
#[ignore = "actual inherited member subprocess only"]
fn inherited_actor() {
    // Import GNU before opening any other descriptor, as required by its
    // native startup contract. No server or replacement credit is constructed.
    let gnu = unsafe { Jobserver::from_env() }.unwrap().unwrap();
    assert!(gnu.pipe_descriptors().is_some());
    let cpu = crate::duplicate_descriptor(&std::env::var_os(IMPLICIT_FD_ENV).unwrap()).unwrap();
    let fences =
        crate::duplicate_descriptors(&std::env::var_os("BUILD_SLOT_FENCE_FDS").unwrap()).unwrap();
    let pool = crate::Pool::open_in(
        &std::path::PathBuf::from(std::env::var_os("MEMBER_TEST_POOL").unwrap()),
        NonZeroU32::new(1).unwrap(),
    )
    .unwrap();
    let _lease = pool.adopt_inherited_until(&cpu, Instant::now() + Duration::from_secs(5)).unwrap();
    let _fence = LegacyFence::from_inherited(
        &std::path::PathBuf::from(std::env::var_os("MEMBER_TEST_FENCE").unwrap()),
        1,
        fences,
    )
    .unwrap();
    println!("actual-member-ready");
    std::io::stdout().flush().unwrap();
    let mut byte = [0];
    assert_eq!(std::io::stdin().read(&mut byte).unwrap(), 1);
}
