use std::fs::File;
use std::os::fd::{AsRawFd, FromRawFd};
use std::time::{Duration, Instant};

use sha2::{Digest, Sha256};
use trust_process_isolation::{
    Binding, Budget, Envelope, Handle, HandleKind, Limits, Message, Session, Value,
};
use trust_worker_linux::KernelLimits;
use trust_worker_linux::launcher::{
    InputClosureIdentity, InputSource, LaunchLimits, Outcome, PreparedStaticWorker,
};

type Result<T = ()> = std::result::Result<T, Box<dyn std::error::Error>>;
struct Scratch(std::path::PathBuf, Option<Group>);
struct Group {
    parent: File,
    directory: File,
    name: std::ffi::CString,
}
impl Drop for Group {
    fn drop(&mut self) {
        use std::os::unix::fs::MetadataExt;
        // SAFETY: test-owned checked fresh name under the retained parent.
        let fd = unsafe {
            libc::openat(
                self.parent.as_raw_fd(),
                self.name.as_ptr(),
                libc::O_RDONLY | libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC,
            )
        };
        if fd >= 0 {
            // SAFETY: successful openat yielded this fresh owned descriptor.
            let now = unsafe { File::from_raw_fd(fd) };
            if let (Ok(a), Ok(b)) = (now.metadata(), self.directory.metadata()) {
                if a.dev() == b.dev() && a.ino() == b.ino() {
                    // SAFETY: only the same authenticated owned group name is
                    // removed; kernel refuses nonempty/populated cgroups.
                    unsafe {
                        libc::unlinkat(
                            self.parent.as_raw_fd(),
                            self.name.as_ptr(),
                            libc::AT_REMOVEDIR,
                        );
                    }
                }
            }
        }
    }
}
impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir(&self.0);
    }
}
fn budget(timeout: Duration) -> Budget {
    Budget::new(
        Limits {
            frame_bytes: 65536,
            wire_bytes: 4_000_000,
            allocation_bytes: 100_000_000,
            values: 10000,
            work: 500_000_000,
            calls: 100,
            live_handles: 64,
            depth: 16,
        },
        Instant::now() + timeout,
    )
    .unwrap()
}
fn prepare_contained(
    mode: &str,
    timeout: Duration,
) -> Result<(trust_worker_linux::launcher::OwnedWorker, Scratch, Budget)> {
    let b = budget(timeout);
    let fixture = std::env::var("TRUST_STATIC_WORKER_FIXTURE")?;
    let bytes = std::fs::read(&fixture)?;
    static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(1);
    let path = std::env::temp_dir().join(format!(
        "trust-b3-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
    ));
    std::fs::create_dir(&path)?;
    use std::os::unix::fs::PermissionsExt;
    std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o700))?;
    let mut scratch = Scratch(path, None);
    let worker_path = scratch.0.with_extension("worker");
    std::fs::write(&worker_path, &bytes)?;
    let worker = File::open(&worker_path)?;
    let ws = InputSource {
        file: &worker,
        sha256: Sha256::digest(&bytes).into(),
        size: bytes.len() as u64,
        executable: true,
    };
    let pathname = std::ffi::CString::new(scratch.0.as_os_str().as_encoded_bytes())?;
    // SAFETY: live terminated scratch path; successful open is uniquely owned.
    let fd = unsafe {
        libc::open(pathname.as_ptr(), libc::O_PATH | libc::O_DIRECTORY | libc::O_CLOEXEC)
    };
    if fd < 0 {
        return Err(std::io::Error::last_os_error().into());
    }
    // SAFETY: successful open yielded one fresh owned descriptor.
    let directory = unsafe { File::from_raw_fd(fd) };
    let input_path = scratch.0.with_extension("input");
    std::fs::write(&input_path, [b'p'; 4096])?;
    let input = File::open(&input_path)?;
    std::fs::remove_file(input_path)?;
    let ins = [InputSource {
        file: &input,
        sha256: Sha256::digest([b'p'; 4096]).into(),
        size: 4096,
        executable: false,
    }];
    let binding = Binding {
        version: 1,
        invocation: 1,
        compiler: [1; 32],
        worker: ws.sha256,
        artifact: [3; 32],
        metadata: [4; 32],
        unit: [5; 32],
        input_closure: InputClosureIdentity::from_plan(&ws, &ins, None)?.digest(),
        host_abi: [7; 32],
    };
    let limits = LaunchLimits {
        kernel: KernelLimits {
            address_space_bytes: 256 * 1024 * 1024,
            stack_bytes: 8 * 1024 * 1024,
            file_bytes: 1024 * 1024,
            descriptors: 64,
        },
        sampled_leader_rss_bytes: 128 * 1024 * 1024,
        output_bytes_per_stream: 8192,
        input_bytes: 64 * 1024 * 1024,
    };
    let session = Session::new(binding.clone(), b.clone())?;
    let prepared = PreparedStaticWorker::prepare(&ws, &ins, None, &session, limits)?;
    // Replace only an independently owned source copy; the build artifact stays
    // unchanged. Consumption must retain the already sealed expected bytes.
    let moved = worker_path.with_extension("moved");
    std::fs::rename(&worker_path, &moved)?;
    std::fs::write(&moved, b"replacement")?;
    std::fs::remove_file(moved)?;
    let stream = Handle { invocation: 1, slot: 0, generation: 1, kind: HandleKind::Stream };
    let span = Handle { invocation: 1, slot: 1, generation: 1, kind: HandleKind::Span };
    let begin = Envelope {
        binding,
        message: Message::Begin {
            declaration: 0,
            kind: 0,
            inputs: vec![stream],
            globals: [span; 3],
        },
    };
    let hex = ins[0].sha256.iter().map(|b| format!("{b:02x}")).collect::<String>();
    // SAFETY: duplicate a fresh ambient canary without replacing another test's
    // FD. It must close before any trusted worker startup/adversarial body.
    let canary_fd = unsafe { libc::fcntl(input.as_raw_fd(), libc::F_DUPFD_CLOEXEC, 40) };
    if canary_fd < 0 {
        return Err(std::io::Error::last_os_error().into());
    }
    // SAFETY: successful duplication yielded one uniquely owned descriptor.
    let _canary = unsafe { File::from_raw_fd(canary_fd) };
    let canary = canary_fd.to_string();
    let parent = File::open(std::env::var("TRUST_WORKER_TEST_CGROUP_PARENT")?)?;
    let name = std::ffi::CString::new(format!(
        "protocol-tree-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
    ))?;
    let owned = prepared.launch_contained(
        &[mode, &hex, &canary],
        &directory,
        begin,
        session,
        &parent,
        &name,
    )?;
    // SAFETY: production created this fresh name under the exclusive test
    // parent. This separate holder exists only for test namespace removal.
    let group_fd = unsafe {
        libc::openat(
            parent.as_raw_fd(),
            name.as_ptr(),
            libc::O_RDONLY | libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC,
        )
    };
    if group_fd < 0 {
        return Err(std::io::Error::last_os_error().into());
    }
    // SAFETY: successful openat returned this unique owned descriptor.
    scratch.1 = Some(Group { parent, directory: unsafe { File::from_raw_fd(group_fd) }, name });
    Ok((owned, scratch, b))
}
#[test]
#[ignore = "requires pinned static ET_EXEC fixture and exclusive finite delegated cgroup-v2 parent; run explicitly with --ignored"]
fn contained_static_protocol_retains_sealed_inputs_callback_and_finished_gate() -> Result {
    for mode in ["positive", "callback", "as"] {
        let (worker, _scratch, budget) = prepare_contained(mode, Duration::from_secs(5))?;
        let endpoint = budget.deadline();
        assert!(worker.used_pidfd());
        let receipt = worker.run(|_, session| {
            assert!(session.budget().shares_owner(&budget));
            Ok(Value::OptionalText(Some("owned callback".into())))
        })?;
        assert_eq!(receipt.outcome, Outcome::Finished);
        assert!(receipt.reaped && receipt.used_pidfd);
        assert_eq!(receipt.stdout, b"STATIC-PASS\n");
        assert_eq!(receipt.deadline, endpoint);
        assert!(budget.check().is_ok());
    }
    Ok(())
}

#[test]
#[ignore = "requires pinned static ET_EXEC fixture and exclusive finite delegated cgroup-v2 parent; run explicitly with --ignored"]
fn contained_static_missing_finish_and_abnormal_status_cannot_gain_protocol_credit() -> Result {
    for mode in ["early-exit", "partial", "wrong-binding", "abnormal"] {
        let (worker, _scratch, budget) = prepare_contained(mode, Duration::from_secs(5))?;
        let receipt = worker.run(|_, _| Ok(Value::Unit))?;
        assert_ne!(receipt.outcome, Outcome::Finished, "{mode}: {receipt:?}");
        assert!(receipt.reaped && receipt.used_pidfd);
        assert!(receipt.output.is_none());
        assert!(budget.check().is_err());
    }
    Ok(())
}

#[test]
#[ignore = "requires pinned static ET_EXEC fixture and exclusive finite delegated cgroup-v2 parent; run explicitly with --ignored"]
fn contained_callback_unwind_retires_original_domain_without_receipt_or_reset() -> Result {
    let (worker, scratch, budget) = prepare_contained("callback", Duration::from_secs(5))?;
    let original = budget.deadline();
    let observed = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _ = worker.run(|_, _| panic!("owned contained callback fixture"));
    }));
    assert!(observed.is_err());
    assert!(budget.check().is_err());
    assert_eq!(budget.deadline(), original);
    let group = scratch.1.as_ref().ok_or("test group holder missing")?;
    // SAFETY: fixed kernel leaf under the held test-owned child directory.
    let fd = unsafe {
        libc::openat(
            group.directory.as_raw_fd(),
            c"cgroup.events".as_ptr(),
            libc::O_RDONLY | libc::O_NOFOLLOW | libc::O_CLOEXEC,
        )
    };
    if fd < 0 {
        return Err(std::io::Error::last_os_error().into());
    }
    // SAFETY: successful openat produced this unique owned descriptor.
    let file = unsafe { File::from_raw_fd(fd) };
    use std::io::Read;
    let mut bytes = Vec::new();
    file.take(64).read_to_end(&mut bytes)?;
    assert_eq!(bytes, b"populated 0\nfrozen 0\n");
    Ok(())
}
