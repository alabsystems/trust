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
use trust_worker_linux::native::{
    NativeClosure, NativeObjectPlan, NativeRole, digest as native_digest,
};

type Result<T = ()> = std::result::Result<T, Box<dyn std::error::Error>>;
struct Scratch(std::path::PathBuf);
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
fn prepare(
    mode: &str,
    timeout: Duration,
) -> Result<(trust_worker_linux::launcher::OwnedWorker, Scratch, Budget)> {
    prepare_with_session(mode, timeout, |session| session)
}

#[derive(Clone, Copy)]
enum NativePreparation {
    None,
    Original,
    ForeignOwner,
    OverInputLimit,
}
fn prepare_with_session(
    mode: &str,
    timeout: Duration,
    transfer: impl FnOnce(Session) -> Session,
) -> Result<(trust_worker_linux::launcher::OwnedWorker, Scratch, Budget)> {
    prepare_with_native(mode, timeout, NativePreparation::None, transfer)
}

fn prepare_with_native(
    mode: &str,
    timeout: Duration,
    native_preparation: NativePreparation,
    transfer: impl FnOnce(Session) -> Session,
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
    let scratch = Scratch(path);
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
    let native_path = if matches!(native_preparation, NativePreparation::None) {
        None
    } else {
        Some(std::path::PathBuf::from(std::env::var("TRUST_NATIVE_OBJECT_FIXTURE")?))
    };
    let native_file = native_path.as_ref().map(File::open).transpose()?;
    let native_bytes = native_path.as_ref().map(std::fs::read).transpose()?;
    let native_plans = native_file.as_ref().zip(native_bytes.as_ref()).map(|(file, bytes)| {
        [NativeObjectPlan {
            source: InputSource {
                file,
                sha256: Sha256::digest(bytes).into(),
                size: bytes.len() as u64,
                executable: true,
            },
            role: NativeRole::Macro,
            soname: "libfixture.so",
            needed: &[],
            aliases: &["/trust-cap/libfixture.so"],
        }]
    });
    let graph =
        native_plans.as_ref().map(|plans| native_digest(plans, 64 << 20, &b)).transpose()?;
    let input_identity = InputClosureIdentity::from_plan(&ws, &ins, graph)?;
    let binding = Binding {
        version: 1,
        invocation: 1,
        compiler: [1; 32],
        worker: ws.sha256,
        artifact: native_plans.as_ref().map_or([3; 32], |plans| plans[0].source.sha256),
        metadata: [4; 32],
        unit: [5; 32],
        input_closure: input_identity.digest(),
        host_abi: [7; 32],
    };
    let mut limits = LaunchLimits {
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
    if matches!(native_preparation, NativePreparation::OverInputLimit) {
        limits.input_bytes = ws.size + ins[0].size;
    }
    let session = Session::new(binding.clone(), b.clone())?;
    let native = match &native_plans {
        None => None,
        Some(plans) => {
            let replacement;
            let owner = if matches!(native_preparation, NativePreparation::ForeignOwner) {
                replacement = Session::new(binding.clone(), b.clone())?;
                &replacement
            } else {
                &session
            };
            Some(NativeClosure::prepare(plans, input_identity, owner, 64 << 20)?)
        }
    };
    let prepared = match PreparedStaticWorker::prepare(&ws, &ins, native, &session, limits) {
        Ok(prepared) => prepared,
        Err(error) => {
            let _ = std::fs::remove_file(&worker_path);
            return Err(error.into());
        }
    };
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
    let owned = prepared.launch(&[mode, &hex, &canary], &directory, begin, transfer(session))?;
    Ok((owned, scratch, b))
}
fn reaped(pid: u32) {
    let mut status = 0;
    // SAFETY: WNOHANG only observes this test's previously owned child; ECHILD
    // establishes the launcher already reaped it, rather than leaving custody.
    assert_eq!(unsafe { libc::waitpid(pid as i32, &mut status, libc::WNOHANG) }, -1);
    assert_eq!(std::io::Error::last_os_error().raw_os_error(), Some(libc::ECHILD));
}
#[test]
#[ignore = "requires separately built static ET_EXEC fixture; run with TRUST_STATIC_WORKER_FIXTURE and --ignored"]
fn real_static_worker_transport_and_kernel_as() -> Result {
    for mode in ["positive", "callback", "as"] {
        let (w, _scratch, b) = prepare(mode, Duration::from_secs(5))?;
        let pid = w.pid();
        let r = w.run(|_, _| Ok(Value::OptionalText(None)))?;
        assert_eq!(r.outcome, Outcome::Finished, "{r:?}");
        assert!(r.reaped);
        assert_eq!(r.stdout, b"STATIC-PASS\n");
        assert!(r.stderr.is_empty());
        assert!(r.sampled_leader_rss_peak_bytes <= r.limits.sampled_leader_rss_bytes);
        assert!(b.check().is_ok());
        reaped(pid);
    }
    Ok(())
}

#[test]
#[ignore = "requires separately built static ET_EXEC fixture; run with TRUST_STATIC_WORKER_FIXTURE and --ignored"]
fn launcher_rejects_reconstructed_or_started_session_before_spawn() -> Result {
    for replacement in [false, true] {
        let mut original = None;
        let result = prepare_with_session("callback", Duration::from_secs(5), |mut session| {
            original = Some(session.budget().clone());
            if replacement {
                Session::new(session.binding().clone(), session.budget().clone()).unwrap()
            } else {
                session
                    .receive(Envelope {
                        binding: session.binding().clone(),
                        message: Message::Ready,
                    })
                    .unwrap();
                session
            }
        });
        assert!(result.is_err());
        assert!(original.unwrap().check().is_err());
    }
    Ok(())
}

#[test]
#[ignore = "requires separately built static ET_EXEC fixture; run with TRUST_STATIC_WORKER_FIXTURE and --ignored"]
fn real_child_callback_observes_original_session_owner() -> Result {
    let mut original = None;
    let (worker, _scratch, budget) =
        prepare_with_session("callback", Duration::from_secs(5), |session| {
            original = Some(session.owner());
            session
        })?;
    let pid = worker.pid();
    let mut called = false;
    let receipt = worker.run(|call, session| {
        called = true;
        assert!(original.as_ref().unwrap().matches(session));
        assert!(session.budget().shares_owner(&budget));
        session.validate_pending_call(&call).map_err(trust_worker_linux::Error::Budget)?;
        Ok(Value::OptionalText(None))
    })?;
    assert!(called);
    assert_eq!(receipt.outcome, Outcome::Finished);
    assert!(receipt.reaped);
    reaped(pid);
    Ok(())
}

#[test]
#[ignore = "requires separately built static ET_EXEC fixture; run with TRUST_STATIC_WORKER_FIXTURE and --ignored"]
fn callback_cannot_replace_session_with_a_replayed_pending_call() -> Result {
    let (worker, _scratch, budget) = prepare("callback", Duration::from_secs(5))?;
    let pid = worker.pid();
    let receipt = worker.run(|call, original| {
        let binding = original.binding().clone();
        let mut replacement = Session::new(binding.clone(), original.budget().clone())
            .map_err(trust_worker_linux::Error::Budget)?;
        replacement
            .receive(Envelope { binding: binding.clone(), message: Message::Ready })
            .map_err(trust_worker_linux::Error::Budget)?;
        replacement
            .receive(Envelope { binding, message: Message::Call(call) })
            .map_err(trust_worker_linux::Error::Budget)?;
        *original = replacement;
        Ok(Value::OptionalText(None))
    })?;
    assert_eq!(receipt.outcome, Outcome::Refused);
    assert!(receipt.output.is_none());
    assert!(receipt.reaped);
    assert_eq!(budget.check(), Err(trust_process_isolation::Error::Identity));
    reaped(pid);
    Ok(())
}
#[test]
#[ignore = "requires separately built static ET_EXEC fixture; run with TRUST_STATIC_WORKER_FIXTURE and --ignored"]
fn protocol_output_and_shared_deadline_refuse_then_reap() -> Result {
    for mode in [
        "wrong-binding",
        "partial",
        "trailing",
        "failure",
        "flood",
        "stall",
        "abnormal",
        "early-exit",
        "control-closed",
        "control-owner",
        "control-cancel",
        "control-deadline",
    ] {
        let (w, _scratch, b) = prepare(
            mode,
            if mode == "stall" { Duration::from_secs(2) } else { Duration::from_secs(5) },
        )?;
        let pid = w.pid();
        let r = w.run(|_, _| Ok(Value::OptionalText(None)))?;
        assert_ne!(r.outcome, Outcome::Finished, "{mode}: {r:?}");
        assert!(r.output.is_none());
        assert!(r.reaped);
        assert!(b.check().is_err());
        reaped(pid);
        if mode.starts_with("control-") {
            assert_eq!(r.stdout, b"CONTROL-REFUSED\n", "{mode}: {r:?}");
        }
        if mode == "failure" {
            assert_eq!(r.outcome, Outcome::WorkerFailure);
            assert_eq!(r.worker_failure.as_deref(), Some("fixture failure"));
        }
        if mode == "flood" {
            assert_eq!(r.stdout.len(), 8193);
        }
    }
    Ok(())
}

#[test]
#[ignore = "requires separately built static ET_EXEC fixture; run with TRUST_STATIC_WORKER_FIXTURE and --ignored"]
fn original_grant_cancellation_and_late_callback_cannot_resume() -> Result {
    let (w, _scratch, b) = prepare("callback", Duration::from_secs(5))?;
    let pid = w.pid();
    b.cancel();
    assert!(w.run(|_, _| Ok(Value::OptionalText(None))).is_err());
    reaped(pid);
    assert!(b.clone().check().is_err());
    let (w, _scratch, b) = prepare("callback", Duration::from_secs(2))?;
    let pid = w.pid();
    let r = w.run(|_, session| {
        let budget = session.budget();
        std::thread::sleep(
            budget.deadline().saturating_duration_since(Instant::now()) + Duration::from_millis(20),
        );
        Ok(Value::OptionalText(None))
    })?;
    assert_eq!(r.outcome, Outcome::Refused);
    assert!(r.output.is_none());
    assert!(b.clone().check().is_err());
    reaped(pid);
    Ok(())
}
#[test]
#[ignore = "requires separately built static ET_EXEC fixture; run with TRUST_STATIC_WORKER_FIXTURE and --ignored"]
fn callback_error_and_unwind_close_owner_without_replacement() -> Result {
    let (w, _scratch, b) = prepare("callback", Duration::from_secs(5))?;
    let pid = w.pid();
    let r = w.run(|_, _| Err(trust_worker_linux::Error::Contract("callback refusal")))?;
    assert_eq!(r.outcome, Outcome::Refused);
    assert!(b.check().is_err());
    reaped(pid);
    let (w, _scratch, b) = prepare("callback", Duration::from_secs(5))?;
    let pid = w.pid();
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _ = w.run(|_, _| panic!("bounded callback fixture"));
    }));
    assert!(result.is_err());
    assert!(b.check().is_err());
    reaped(pid);
    Ok(())
}

#[test]
#[ignore = "requires native static and ELF DSO fixtures; set TRUST_STATIC_WORKER_FIXTURE and TRUST_NATIVE_OBJECT_FIXTURE"]
fn owned_static_child_receipts_the_original_composite_native_inputs() -> Result {
    let native_bytes = std::fs::read(std::env::var("TRUST_NATIVE_OBJECT_FIXTURE")?)?;
    let worker_bytes = std::fs::metadata(std::env::var("TRUST_STATIC_WORKER_FIXTURE")?)?.len();
    let (worker, _scratch, budget) = prepare_with_native(
        "positive",
        Duration::from_secs(5),
        NativePreparation::Original,
        |session| session,
    )?;
    let pid = worker.pid();
    let receipt = worker.run(|_, _| panic!("unexpected compiler callback"))?;
    assert_eq!(receipt.outcome, Outcome::Finished, "{receipt:?}");
    assert!(receipt.reaped);
    reaped(pid);
    assert_eq!(receipt.binding.input_closure, receipt.input_identity.digest());
    assert_eq!(receipt.input_bytes, worker_bytes + 4096 + native_bytes.len() as u64);
    let native = receipt.native.unwrap();
    assert_eq!(native.identity, receipt.input_identity);
    assert_eq!(Some(native.graph_digest), native.identity.native_graph());
    assert_eq!(native.input_bytes, native_bytes.len() as u64);
    assert_eq!(native.objects.len(), 1);
    let expected: [u8; 32] = Sha256::digest(&native_bytes).into();
    assert_eq!(native.objects[0].input.sha256, expected);
    assert_eq!(native.objects[0].role, NativeRole::Macro);
    assert_eq!(native.objects[0].soname, b"libfixture.so");
    assert!(budget.check().is_ok());
    Ok(())
}

#[test]
#[ignore = "requires native static and ELF DSO fixtures; set TRUST_STATIC_WORKER_FIXTURE and TRUST_NATIVE_OBJECT_FIXTURE"]
fn native_join_rejects_foreign_session_and_charges_aggregate_input_before_spawn() -> Result {
    for preparation in [NativePreparation::ForeignOwner, NativePreparation::OverInputLimit] {
        assert!(
            prepare_with_native("success", Duration::from_secs(5), preparation, |session| session,)
                .is_err()
        );
    }
    Ok(())
}
