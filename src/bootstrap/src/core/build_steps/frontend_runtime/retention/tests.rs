//! Mechanical original-input/withholding controls, never a supported Host Root.
use std::fs::{self, File, OpenOptions};
use std::io::{Read, Write};
use std::os::unix::net::{UnixListener, UnixStream};
use std::process::{Child, Command, Stdio};
use std::time::Duration;

use build_helper::trust_output_lock::OutputLock;
use build_helper::trust_repo_lock::management::{
    Acquire, Kind as LeaseKind, LeaseAcquisition, Manager,
};
use trust_resource_controller::runtime_input_retention::transport;
use trust_resource_controller::{BirthKind, Channel, Cpu, Identity, JobBinding, Memory, Subject};

use super::*;

fn query() -> ContextQuery {
    ContextQuery {
        binding: JobBinding {
            session: "s-abcd".into(),
            root_attempt: [1; 16],
            capability: [2; 32],
        },
        call_attempt: [3; 16],
    }
}

// Data used ONLY in private state tests, never through a Client or support
// constructor. It grants no Root membership, execution or Host custody.
fn context() -> Context {
    let identity = Identity { pid: 42, birth: 77, birth_kind: BirthKind::MacosWallMicroseconds };
    Context {
        session: query().binding.session,
        root_attempt: query().binding.root_attempt,
        host: "test-data".into(),
        boot: "abc123".into(),
        original_root: identity,
        subject: Subject::Root { identity },
        cpu: Cpu::RetainedFixed { units: 1, native_manifest: FileIdentity { device: 1, inode: 2 } },
        memory: Memory {
            bytes: 1,
            namespace: [4; 16],
            marker: "1-2-3".into(),
            epoch: [5; 16],
            guard: FileIdentity { device: 1, inode: 3 },
        },
        sdk: None,
    }
}

fn original(root: &std::path::Path) -> build_helper::trust_repo_lock::management::Lease {
    acquire(root, None)
}

fn acquire(
    root: &std::path::Path,
    token: Option<String>,
) -> build_helper::trust_repo_lock::management::Lease {
    let request = Acquire {
        kind: LeaseKind::Build,
        owner_pid: std::process::id(),
        purpose: "original runtime retention state control".into(),
        contract: "durable original manager exclusion only; no Host".into(),
        wait: Duration::ZERO,
        inherited_token: token,
        break_reason: None,
    };
    match Manager::open(root).unwrap().acquire_lease(&request).unwrap() {
        LeaseAcquisition::Granted(lease) => lease,
        _ => panic!("private original manager unexpectedly busy"),
    }
}

#[test]
fn ordinary_command_cannot_offer_inputs_and_keeps_ordinary_drop() {
    let root = tempfile::tempdir().unwrap();
    let command = CommandOwnership::new(original(root.path()));
    assert!(command.retained_context().is_err());
    assert!(command.begin_input_transfer(&query()).is_err());
    command.check().unwrap();
    drop(command);
    assert!(Manager::open(root.path()).unwrap().status().unwrap().is_free());
}

#[test]
fn actual_withheld_one_use_and_poison_cannot_release_original_exclusion() {
    let root = tempfile::tempdir().unwrap();
    let command = CommandOwnership::new(original(root.path()));
    let lease = command.withhold_original().unwrap();
    let actual_owner = std::sync::Arc::downgrade(&lease);
    assert!(command.withhold_original().is_err());
    assert!(command.retained_context().is_err());
    assert!(command.begin_input_transfer(&query()).is_err());
    {
        let mut state = command.lease.lock().unwrap();
        let CommandState::Withheld { lease: held, retention, .. } = &mut *state else {
            panic!("original transition was not retained")
        };
        assert!(std::sync::Arc::ptr_eq(&lease, held));
        // Unit DATA only, never an opaque supported Host. This test attaches
        // the binding directly. Outside tests only the unwired
        // `prepare_input_retention` negotiation would, and that module and
        // this field are compiled only with tests.
        *retention = Some(RetentionBinding { context: context(), binding: query().binding });
    }
    drop(lease);
    let mut foreign = query();
    foreign.binding.capability[0] ^= 1;
    assert!(command.begin_input_transfer(&foreign).is_err());
    command.begin_input_transfer(&query()).unwrap();
    assert!(command.begin_input_transfer(&query()).is_err());
    let poisoned = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _original = command.lease.lock().unwrap();
        panic!("actual poisoned container control");
    }));
    assert!(poisoned.is_err());
    assert!(command.check().is_err());
    assert!(command.retained_context().is_err());
    drop(command);
    assert!(actual_owner.upgrade().is_none());
    let manager = Manager::open(root.path()).unwrap();
    assert!(manager.status().unwrap().holder.unwrap().is_withheld());
    assert!(manager.break_holder("poison is not original Host closure").is_err());
}

#[test]
fn engine_withholding_refuses_actual_borrowed_custody_without_promoting_it() {
    const NAME: &str = "core::build_steps::frontend_runtime::retention::tests::engine_withholding_refuses_actual_borrowed_custody_without_promoting_it";
    const ROOT: &str = "TRUST_TEST_COMMAND_BORROW_ROOT";
    const TOKEN: &str = "TRUST_TEST_COMMAND_BORROW_TOKEN";
    if let Some(root) = std::env::var_os(ROOT) {
        let lease = acquire(std::path::Path::new(&root), Some(std::env::var(TOKEN).unwrap()));
        assert!(lease.is_borrowed());
        let command = CommandOwnership::new(lease);
        assert!(command.withhold_original().is_err());
        command.check().unwrap();
        return;
    }
    let root = tempfile::tempdir().unwrap();
    let lease = original(root.path());
    let manager = Manager::open(root.path()).unwrap();
    let token = manager.status().unwrap().holder.unwrap().token;
    let info = root.path().join(".trust-build-lock/info");
    let before = fs::read(&info).unwrap();
    let output =
        crate::test_entry::uncaptured_actor(Command::new(std::env::current_exe().unwrap()))
            .args(["--exact", NAME, "--nocapture"])
            .env(ROOT, root.path())
            .env(TOKEN, token)
            .output()
            .unwrap();
    assert!(output.status.success(), "actual borrowed actor failed: {output:?}");
    lease.check_current().unwrap();
    assert_eq!(fs::read(info).unwrap(), before);
    drop(lease);
    assert!(manager.status().unwrap().is_free());
}

struct OwnChild {
    child: Child,
    reaped: bool,
}
impl Drop for OwnChild {
    fn drop(&mut self) {
        if !self.reaped {
            let _ = self.child.kill();
            let _ = self.child.wait();
        }
    }
}

const RECEIVER: &str =
    "core::build_steps::frontend_runtime::retention::tests::runtime_inputs_receiver";
const SOCKET: &str = "TRUST_TEST_RUNTIME_INPUT_SOCKET";

#[test]
fn runtime_inputs_receiver() {
    let Some(socket) = std::env::var_os(SOCKET) else { return };
    let mut channel = Channel::new(UnixStream::connect(socket).unwrap()).unwrap();
    let deadline = Instant::now().checked_add(Duration::from_secs(120)).unwrap();
    let request = Request::decode(&channel.receive(deadline).unwrap()).unwrap();
    assert_eq!(request.inputs.len(), 171);
    // This is explicitly a mechanical transport actor, NOT a Host. Actual
    // production uses original Job/peer/image authentication at every callback.
    let originals = transport::receive_inputs(&mut channel, &request, deadline, || Ok(())).unwrap();
    assert_eq!(originals.len(), request.inputs.len());
    channel.send(b"mechanical-original-inputs-retained", deadline).unwrap();
    transport::finish_reply(&mut channel).unwrap();
    let mut release = [0];
    std::io::stdin().read_exact(&mut release).unwrap();
    assert_eq!(release, [1]);
    drop(originals);
    drop(channel);
}

#[test]
#[ignore = "explicit immutable runtime only; set TRUST_NATIVE_LIVE_RUNTIME_INPUTS and TRUST_NATIVE_LIVE_RUNTIME_COMPILER_SHA256"]
fn actual_runtime_and_output_send_all_original_171_descriptions() {
    use crate::utils::retained_compiler_fixture::HeldRuntimeInputs;
    let root =
        std::path::PathBuf::from(std::env::var_os("TRUST_NATIVE_LIVE_RUNTIME_INPUTS").unwrap());
    let expected =
        digest(&std::env::var("TRUST_NATIVE_LIVE_RUNTIME_COMPILER_SHA256").unwrap()).unwrap();
    let runtime = HeldRuntimeInputs::capture(&root, "aarch64-apple-darwin").unwrap();
    fs::create_dir_all("/tmp/.ubd").unwrap();
    let scratch = tempfile::Builder::new().prefix("rti-").tempdir_in("/tmp/.ubd").unwrap();
    let output = OutputLock::try_acquire(&scratch.path().join("output")).unwrap().unwrap();
    let (request, descriptors) = {
        let runtime = runtime.original_descriptions().unwrap();
        // SAFETY: mechanical receiver closes only its SAME-OFD copies. No
        // cursor/flags/unlock mutation or receipt-to-owner conversion occurs.
        let output = unsafe { output.original_descriptions() }.unwrap();
        input_request(&runtime, &output, query(), [6; 16]).unwrap()
    };
    assert_eq!(request.inputs.len(), 171);
    assert_eq!(descriptors.len(), 171);
    assert_eq!(request.inputs.iter().filter(|i| i.kind == Kind::RuntimeFile).count(), 156);
    assert_eq!(request.inputs.iter().filter(|i| i.kind == Kind::RuntimeDirectory).count(), 12);
    assert_eq!(
        request.inputs.iter().find(|i| i.logical_path == b"bin/trustc").unwrap().sha256,
        Some(expected)
    );
    assert!(Request::decode(&request.encode().unwrap()).unwrap() == request);
    let observe = || {
        descriptors
            .iter()
            .map(|fd| {
                // XNU may add historical FMARK/FDEFER bookkeeping after descriptor use;
                // preserve every semantic flag, CLOEXEC and actual shared file cursor.
                let flags = unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_GETFL) } & !0x3000;
                let close = unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_GETFD) };
                let cursor = unsafe { libc::lseek(fd.as_raw_fd(), 0, libc::SEEK_CUR) };
                (flags, close, cursor)
            })
            .collect::<Vec<_>>()
    };
    let before = observe();
    let socket = scratch.path().join("socket");
    let listener = UnixListener::bind(&socket).unwrap();
    listener.set_nonblocking(true).unwrap();
    let mut child = OwnChild {
        child: crate::test_entry::uncaptured_actor(Command::new(std::env::current_exe().unwrap()))
            .args(["--exact", RECEIVER, "--nocapture"])
            .env(SOCKET, &socket)
            .stdin(Stdio::piped())
            .spawn()
            .unwrap(),
        reaped: false,
    };
    let deadline = Instant::now().checked_add(Duration::from_secs(120)).unwrap();
    let stream = loop {
        match listener.accept() {
            Ok((stream, _)) => break stream,
            Err(error) if error.kind() == io::ErrorKind::WouldBlock => {
                time(deadline).unwrap();
                std::thread::sleep(Duration::from_millis(5));
            }
            Err(error) => panic!("actual receiver connection failed: {error}"),
        }
    };
    let mut channel = Channel::new(stream).unwrap();
    channel.send(&request.encode().unwrap(), deadline).unwrap();
    transport::send_inputs(&mut channel, &request, &descriptors, deadline, || Ok(())).unwrap();
    assert_eq!(channel.receive(deadline).unwrap(), b"mechanical-original-inputs-retained");
    transport::require_reply_eof(&mut channel, deadline).unwrap();
    assert_eq!(observe(), before);
    drop(descriptors);
    drop(output);
    drop(runtime);
    let lock = scratch.path().join("output/lock");
    let independent: File = OpenOptions::new().read(true).write(true).open(lock).unwrap();
    assert!(matches!(independent.try_lock(), Err(std::fs::TryLockError::WouldBlock)));
    child.child.stdin.take().unwrap().write_all(&[1]).unwrap();
    let status = child.child.wait().unwrap();
    child.reaped = true;
    assert!(status.success());
    independent.try_lock().unwrap();
    println!(
        "actual original runtime169+output2 transmitted intact; source flags/cursors preserved; same output lock held through receiver final close; mechanical transport only, no CompletedRuntime/Host/SDK constructed or SDK tool executed"
    );
}
