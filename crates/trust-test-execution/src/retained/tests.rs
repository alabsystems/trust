use std::io::{BufRead as _, Read};
use std::sync::{Arc, Mutex, mpsc};

use super::*;

const SESSION: &str = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
const SHA: &str = "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";
const CONNECTION: &str = "dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd";
const ACTOR: &str = "TRUST_RETAINED_PROTOCOL_TEST_ACTOR";

fn receipt() -> PreparedTestsReceipt {
    PreparedTestsReceipt {
        schema: RECEIPT_SCHEMA.into(),
        session: SESSION.into(),
        path: "/retained-test/prepared.json".into(),
        sha256: SHA.into(),
    }
}

fn actor_name() -> String {
    let (_, module) = module_path!().split_once("::").unwrap();
    format!("{module}::retained_process_actor")
}

fn actor_command(role: &str) -> Command {
    let mut command = Command::new(std::env::current_exe().unwrap());
    command
        .args(["--ignored", "--exact", &actor_name(), "--nocapture"])
        .env(ACTOR, role)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    command
}

struct RunningChild(Child);
impl Drop for RunningChild {
    fn drop(&mut self) {
        if self.0.try_wait().ok().flatten().is_none() {
            let _ = self.0.kill();
            let _ = self.0.wait();
        }
    }
}

fn ready(owner: &mut SessionOwner, child: &mut Child, deadline: Instant) {
    while owner.poll_ready(deadline).unwrap().is_none() {
        assert!(child.try_wait().unwrap().is_none(), "child exited before its checkpoint");
        std::thread::sleep(Duration::from_millis(2));
    }
}

fn child_wait(child: &mut Child, deadline: Instant) -> std::process::ExitStatus {
    loop {
        if let Some(status) = child.try_wait().unwrap() {
            return status;
        }
        assert!(Instant::now() < deadline, "retained child did not terminate");
        std::thread::sleep(Duration::from_millis(2));
    }
}

fn read_evidence(child: &mut Child) -> (String, String) {
    let stdout = child.stdout.take().unwrap();
    let stderr = child.stderr.take().unwrap();
    let (send, receive) = mpsc::channel();
    for (index, mut pipe) in
        [Box::new(stdout) as Box<dyn Read + Send>, Box::new(stderr)].into_iter().enumerate()
    {
        let send = send.clone();
        std::thread::spawn(move || {
            let mut text = String::new();
            pipe.read_to_string(&mut text).unwrap();
            let _ = send.send((index, text));
        });
    }
    let mut outputs = [String::new(), String::new()];
    for _ in 0..2 {
        let (index, text) = receive
            .recv_timeout(Duration::from_secs(5))
            .expect("compile evidence must reach EOF while the compiler child stays alive");
        outputs[index] = text;
    }
    let [stdout, stderr] = outputs;
    (stdout, stderr)
}

fn drain_runtime(output: RuntimeOutput) -> (Arc<Mutex<Vec<u8>>>, Vec<std::thread::JoinHandle<()>>) {
    let captured = Arc::new(Mutex::new(Vec::new()));
    let mut handles = Vec::new();
    for mut stream in [output.stdout, output.stderr] {
        let captured = Arc::clone(&captured);
        handles.push(std::thread::spawn(move || {
            let mut bytes = [0u8; 1024];
            loop {
                let count = stream.read(&mut bytes).unwrap();
                if count == 0 {
                    break;
                }
                captured.lock().unwrap().extend_from_slice(&bytes[..count]);
            }
        }));
    }
    (captured, handles)
}

#[test]
fn actual_child_closes_compile_evidence_before_one_shot_grant() {
    let deadline = Instant::now() + Duration::from_secs(20);
    let mut command = actor_command("execute");
    let (child, mut owner, runtime) = SessionOwner::spawn(&mut command, SESSION, deadline).unwrap();
    let mut child = RunningChild(child);
    let (captured, drains) = drain_runtime(runtime);
    assert_eq!(owner.child_id(), child.0.id());
    ready(&mut owner, &mut child.0, deadline);
    assert!(owner.ready.as_ref().unwrap().is_success());
    assert!(same_receipt(owner.ready.as_ref().unwrap().receipt().unwrap(), &receipt()));
    let (stdout, stderr) = read_evidence(&mut child.0);
    assert!(stdout.contains("retained-compiler-prefix"));
    assert!(stderr.contains("retained-compiler-diagnostic"));
    assert!(!stdout.contains("retained-user-executed"));
    assert!(child.0.try_wait().unwrap().is_none());
    assert!(captured.lock().unwrap().is_empty(), "no runtime action before the grant");
    let mut granted =
        owner.grant(Path::new("/retained-test/authority.json"), SHA, deadline).unwrap();
    assert_eq!(granted.child_id(), child.0.id());
    assert!(child_wait(&mut child.0, deadline).success());
    granted.check_connected(deadline).unwrap();
    assert!(granted.drained(), "actual exit0 also requires the queue-drained event");
    drop(granted);
    for drain in drains {
        drain.join().unwrap()
    }
    let runtime = String::from_utf8(captured.lock().unwrap().clone()).unwrap();
    assert!(runtime.contains("retained-user-executed"));
    assert!(!runtime.contains("retained-compiler-prefix"));
}

#[test]
fn actual_controller_close_before_and_after_grant_stops_the_child() {
    for granted in [false, true] {
        let deadline = Instant::now() + Duration::from_secs(20);
        let (child, mut owner, runtime) =
            SessionOwner::spawn(&mut actor_command("cancel"), SESSION, deadline).unwrap();
        let mut child = RunningChild(child);
        ready(&mut owner, &mut child.0, deadline);
        let _ = read_evidence(&mut child.0);
        let RuntimeOutput { stdout, mut stderr } = runtime;
        let mut stdout = io::BufReader::new(stdout);
        stdout.get_ref().set_read_timeout(Some(Duration::from_secs(5))).unwrap();
        if granted {
            let held =
                owner.grant(Path::new("/retained-test/authority.json"), SHA, deadline).unwrap();
            let mut marker = String::new();
            stdout.read_line(&mut marker).unwrap();
            assert!(marker.contains("retained-user-executed"));
            drop(held);
        } else {
            drop(owner);
        }
        let status = child_wait(&mut child.0, deadline);
        assert_eq!(status.success(), granted);
        let mut tail = String::new();
        stdout.read_to_string(&mut tail).unwrap();
        stderr.read_to_string(&mut String::new()).unwrap();
        if granted {
            assert!(tail.contains("retained-controller-closed"))
        } else {
            assert!(!tail.contains("retained-user-executed"))
        }
    }
}

#[test]
fn actual_failed_compile_checkpoint_cannot_be_granted() {
    let deadline = Instant::now() + Duration::from_secs(20);
    let (child, mut owner, runtime) =
        SessionOwner::spawn(&mut actor_command("fail"), SESSION, deadline).unwrap();
    let mut child = RunningChild(child);
    let (_, drains) = drain_runtime(runtime);
    ready(&mut owner, &mut child.0, deadline);
    let checkpoint = owner.ready.as_ref().unwrap();
    assert!(!checkpoint.is_success());
    assert_eq!(checkpoint.failure(), Some("retained compile refused"));
    assert!(checkpoint.receipt().is_none());
    assert!(owner.grant(Path::new("/retained-test/authority.json"), SHA, deadline).is_err());
    assert!(!child_wait(&mut child.0, deadline).success());
    for drain in drains {
        drain.join().unwrap()
    }
}

#[test]
fn actual_postgrant_loss_replay_partial_and_foreign_completion_refuse() {
    for role in [
        "early-close",
        "extra-control",
        "duplicate-completion",
        "duplicate-completion-exit",
        "partial-completion",
        "partial-after-completion-exit",
        "foreign-completion",
    ] {
        let deadline = Instant::now() + Duration::from_secs(20);
        let (child, mut owner, runtime) =
            SessionOwner::spawn(&mut actor_command(role), SESSION, deadline).unwrap();
        let mut child = RunningChild(child);
        let (_, drains) = drain_runtime(runtime);
        ready(&mut owner, &mut child.0, deadline);
        let _ = read_evidence(&mut child.0);
        let mut granted =
            owner.grant(Path::new("/retained-test/authority.json"), SHA, deadline).unwrap();
        let already_exited = role.ends_with("-exit");
        if already_exited {
            assert!(child_wait(&mut child.0, deadline).success());
        }
        let error = loop {
            if let Err(error) = granted.check_connected(deadline) {
                break error;
            }
            if !already_exited {
                assert!(child.0.try_wait().unwrap().is_none(), "{role} must still be a live actor");
            }
            std::thread::sleep(Duration::from_millis(2));
        };
        assert!(
            matches!(error.kind(), io::ErrorKind::InvalidData | io::ErrorKind::UnexpectedEof),
            "{role}: {error}"
        );
        assert!(granted.check_connected(deadline).is_err(), "{role}: refusal is sticky");
        if !matches!(
            role,
            "duplicate-completion" | "duplicate-completion-exit" | "partial-after-completion-exit"
        ) {
            assert!(!granted.drained(), "{role} cannot complete the original queue");
        }
        drop((granted, child));
        for drain in drains {
            drain.join().unwrap();
        }
    }
}

#[test]
fn drained_event_is_one_use_and_checks_the_entire_original_binding() {
    let (mut child, _parent) = child_pair();
    assert!(!child.was_granted());
    assert!(child.publish_drained(child.deadline()).is_err(), "no completion before grant");
    for variant in 0..5 {
        let (stream, mut peer) = UnixStream::pair().unwrap();
        let deadline = Instant::now() + Duration::from_secs(5);
        let mut granted = GrantedSession {
            channel: Channel::new(stream, deadline).unwrap(),
            child_id: std::process::id(),
            session: SESSION.into(),
            connection: CONNECTION.into(),
            receipt: receipt(),
            drained: false,
        };
        let mut message = Message::DrainComplete {
            session: SESSION.into(),
            connection: CONNECTION.into(),
            receipt: receipt(),
        };
        if let Message::DrainComplete { session, connection, receipt } = &mut message {
            match variant {
                0 => *session = "c".repeat(64),
                1 => *connection = "c".repeat(64),
                2 => receipt.sha256 = "c".repeat(64),
                3 => receipt.path = "/foreign/prepared.json".into(),
                4 => receipt.schema = "foreign-schema".into(),
                _ => unreachable!(),
            }
        }
        raw_frame(&mut peer, VERSION, message);
        drop(peer);
        assert!(granted.check_connected(deadline).is_err());
        assert!(!granted.drained());
    }
    let (mut child, mut parent) = child_pair();
    raw_frame(&mut parent, VERSION, grant_message());
    assert!(child.poll_grant(child.deadline()).unwrap().is_some());
    assert!(child.was_granted());
    child.publish_drained(child.deadline()).unwrap();
    assert!(child.publish_drained(child.deadline()).is_err(), "the producer is one-use too");
}

fn child_pair() -> (RetainedChild, UnixStream) {
    let (child, parent) = UnixStream::pair().unwrap();
    (
        RetainedChild {
            channel: Channel::new(child, Instant::now() + Duration::from_secs(10)).unwrap(),
            session: SESSION.into(),
            connection: CONNECTION.into(),
            output: None,
            receipt: Some(receipt()),
            granted: false,
            drained: false,
            compile_failed: false,
        },
        parent,
    )
}

fn grant_message() -> Message {
    Message::Grant {
        session: SESSION.into(),
        connection: CONNECTION.into(),
        receipt: receipt(),
        authority_path: "/retained-test/authority.json".into(),
        authority_sha256: SHA.into(),
    }
}

fn raw_frame(stream: &mut UnixStream, version: u32, message: Message) {
    let bytes = serde_json::to_vec(&Frame { version, message }).unwrap();
    stream.write_all(&(bytes.len() as u32).to_be_bytes()).unwrap();
    stream.write_all(&bytes).unwrap();
}

#[test]
fn foreign_bindings_bad_versions_replays_and_unknown_frames_poison_the_session() {
    for variant in 0..8 {
        let (mut child, mut parent) = child_pair();
        let mut frame = grant_message();
        if let Message::Grant { session, connection, receipt, authority_path, authority_sha256 } =
            &mut frame
        {
            match variant {
                0 => *session = "c".repeat(64),
                1 => receipt.sha256 = "c".repeat(64),
                2 => receipt.path = "/foreign/prepared.json".into(),
                3 => *authority_path = "relative".into(),
                4 => *authority_sha256 = "invalid".into(),
                7 => *connection = "e".repeat(64),
                _ => {}
            }
        }
        if variant == 6 {
            let bytes = br#"{"version":1,"message":{"kind":"unknown"}}"#;
            parent.write_all(&(bytes.len() as u32).to_be_bytes()).unwrap();
            parent.write_all(bytes).unwrap();
        } else {
            raw_frame(&mut parent, if variant == 5 { 2 } else { VERSION }, frame)
        }
        assert!(child.poll_grant(child.deadline()).is_err());
        assert!(child.poll_grant(child.deadline()).is_err(), "rejection is sticky");
    }
    let (mut child, mut parent) = child_pair();
    raw_frame(&mut parent, VERSION, grant_message());
    raw_frame(&mut parent, VERSION, grant_message());
    assert!(
        child.poll_grant(child.deadline()).is_err(),
        "coalesced duplicate cannot unlock execution"
    );
    let (mut child, mut parent) = child_pair();
    raw_frame(&mut parent, VERSION, grant_message());
    assert!(child.poll_grant(child.deadline()).unwrap().is_some());
    assert!(child.poll_grant(child.deadline()).is_err(), "grant is consumed once");
}

#[test]
fn partial_oversized_eof_and_deadlines_never_authorize_or_extend() {
    for bytes in
        [vec![0, 0], ((MAX_FRAME_BYTES + 1) as u32).to_be_bytes().to_vec(), vec![0, 0, 0, 4, b'{']]
    {
        let (mut child, mut parent) = child_pair();
        parent.write_all(&bytes).unwrap();
        // Establish actual EOF even if another test is launching a process
        // with a temporary CLOEXEC copy of this peer descriptor.
        parent.shutdown(std::net::Shutdown::Write).unwrap();
        drop(parent);
        assert!(child.poll_grant(child.deadline()).is_err());
    }
    let (mut child, _parent) = child_pair();
    let expired = Instant::now();
    assert_eq!(child.poll_grant(expired).unwrap_err().kind(), io::ErrorKind::TimedOut);
    assert!(child.poll_grant(expired + Duration::from_secs(100)).is_err());
    let (mut child, mut parent) = child_pair();
    raw_frame(&mut parent, VERSION, grant_message());
    assert!(
        !child.poll_parent_closed().unwrap(),
        "qualification peek must retain the queued grant"
    );
    assert!(child.poll_grant(child.deadline()).unwrap().is_some());
    // Dropping one descriptor is not EOF while a concurrent fork holds a
    // copy until exec. Shutdown establishes EOF across those copies without
    // changing the original deadline or relaxing the cancellation assertion.
    parent.shutdown(std::net::Shutdown::Write).unwrap();
    drop(parent);
    assert!(child.poll_cancelled().unwrap());
}

#[test]
fn a_live_peer_copy_is_not_eof_and_write_shutdown_cancels_across_copies() {
    let (mut child, mut parent) = child_pair();
    raw_frame(&mut parent, VERSION, grant_message());
    assert!(child.poll_grant(child.deadline()).unwrap().is_some());
    // A fork can hold the same socket until exec even when its descriptor is
    // CLOEXEC. An owned duplicate deterministically pins that socket state.
    let held_copy = parent.try_clone().unwrap();
    drop(parent);
    assert!(!child.poll_cancelled().unwrap(), "the actual peer is still live");
    held_copy.shutdown(std::net::Shutdown::Write).unwrap();
    assert!(child.poll_cancelled().unwrap(), "actual EOF cancels immediately");
    assert!(child.poll_cancelled().unwrap(), "cancellation remains sticky");
}

#[test]
fn original_parent_deadline_replaces_startup_bound_but_cannot_be_renewed() {
    // Exercise different positions within the transport clock's tick while
    // retaining the original strict bound; conversion gets no tolerance.
    for _ in 0..32 {
        let (stream, _peer) = UnixStream::pair().unwrap();
        let startup = Instant::now() + Duration::from_millis(100);
        let parent = Instant::now() + Duration::from_secs(30);
        let mut channel = Channel::new(stream, startup).unwrap();
        channel.adopt_parent_expiry(transport::monotonic_expiry(parent).unwrap()).unwrap();
        assert!(channel.deadline() > startup);
        assert!(channel.deadline() <= parent);
        let shorter = Instant::now() + Duration::from_secs(10);
        channel.limit_deadline(shorter);
        channel.limit_deadline(parent + Duration::from_secs(100));
        assert_eq!(channel.deadline(), shorter);
    }
}

#[test]
fn root_control_refusal_preserves_opaque_harness_arguments() {
    let deadline = Instant::now() + Duration::from_secs(10);
    let mut refused = Command::new("/usr/bin/true");
    refused.arg("--__resource-root-control");
    assert!(SessionOwner::spawn(&mut refused, SESSION, deadline).is_err());
    let mut opaque = Command::new("/usr/bin/true");
    opaque.args(["--", "--skip", "--__resource-root-control"]);
    let (child, owner, output) = SessionOwner::spawn(&mut opaque, SESSION, deadline).unwrap();
    let mut child = RunningChild(child);
    assert!(child_wait(&mut child.0, deadline).success());
    drop((owner, output));
}

#[test]
fn actual_startup_rejects_wrong_runtime_roles_counts_and_descriptor_types() {
    for case in 0..3 {
        let deadline = Instant::now() + Duration::from_secs(20);
        let (parent, endpoint) = UnixStream::pair().unwrap();
        let (stdout, writer_stdout) = UnixStream::pair().unwrap();
        let (stderr, writer_stderr) = UnixStream::pair().unwrap();
        let regular = std::fs::File::open("/dev/null").unwrap();
        let mut parent = Channel::new(parent, deadline).unwrap();
        let roles = if case == 0 {
            [OutputRole::RuntimeStderr, OutputRole::RuntimeStdout]
        } else {
            [OutputRole::RuntimeStdout, OutputRole::RuntimeStderr]
        };
        let mut rights = vec![writer_stdout.as_raw_fd(), writer_stderr.as_raw_fd()];
        if case == 1 {
            rights.pop();
        }
        if case == 2 {
            rights[1] = regular.as_raw_fd();
        }
        parent
            .send(
                Message::Init {
                    session: SESSION.into(),
                    connection: CONNECTION.into(),
                    roles,
                    expires_monotonic_ns: transport::monotonic_expiry(deadline).unwrap(),
                },
                &rights,
            )
            .unwrap();
        drop(writer_stdout);
        drop(writer_stderr);
        let mut command = actor_command("execute");
        command.stdin(Stdio::from(OwnedFd::from(endpoint)));
        let mut child = RunningChild(command.spawn().unwrap());
        command.stdin(Stdio::null());
        assert!(!child_wait(&mut child.0, deadline).success());
        let (compile, _) = read_evidence(&mut child.0);
        assert!(!compile.contains("retained-user-executed"));
        drop((stdout, stderr));
    }
}

#[test]
fn controller_loss_and_early_grants_are_observed_during_compilation() {
    let (mut child, mut parent) = child_pair();
    child.receipt = None;
    assert!(!child.poll_parent_closed().unwrap());
    raw_frame(&mut parent, VERSION, grant_message());
    assert!(
        child.poll_parent_closed().is_err(),
        "an early grant cannot be queued for later authorization"
    );
    let (mut child, parent) = child_pair();
    child.receipt = None;
    drop(parent);
    assert!(child.poll_parent_closed().unwrap());
}

#[test]
#[ignore = "child actor entered only through the owned retained-session tests"]
fn retained_process_actor() -> io::Result<()> {
    let role = std::env::var(ACTOR).map_err(|error| invalid(error.to_string()))?;
    let mut child = RetainedChild::capture_stdin(Instant::now() + Duration::from_secs(5))?;
    assert_eq!(child.session(), SESSION);
    // Startup's short receive bound must not shorten the parent's lifetime.
    assert!(child.deadline() > Instant::now() + Duration::from_secs(8));
    for fd in std::iter::once(child.channel.stream_fd_for_test())
        .chain(child.output.as_ref().unwrap().iter().map(AsRawFd::as_raw_fd))
    {
        // SAFETY: all descriptors are still owned by this captured endpoint.
        let flags = unsafe { libc::fcntl(fd, libc::F_GETFD) };
        assert!(flags >= 0, "captured descriptors must remain live until the switch");
        assert_ne!(flags & libc::FD_CLOEXEC, 0);
    }
    println!("retained-compiler-prefix");
    eprintln!("retained-compiler-diagnostic");
    let deadline = child.deadline();
    if role == "fail" {
        child.publish_compile_failed("retained compile refused", deadline)?;
        return Err(io::Error::other("actual compile failure"));
    }
    child.publish_ready(&receipt(), deadline)?;
    let grant = loop {
        if let Some(grant) = child.poll_grant(deadline)? {
            break grant;
        }
        std::thread::sleep(Duration::from_millis(2));
    };
    assert_eq!(grant.session(), SESSION);
    assert_eq!(grant.plan_sha256(), SHA);
    assert_eq!(grant.authority_path(), Path::new("/retained-test/authority.json"));
    assert_eq!(grant.authority_sha256(), SHA);
    println!("retained-user-executed");
    io::stdout().flush()?;
    if role == "cancel" {
        while !child.poll_cancelled()? {
            std::thread::sleep(Duration::from_millis(2))
        }
        println!("retained-controller-closed");
        return Ok(());
    }
    match role.as_str() {
        "early-close" => {
            drop(child);
            std::thread::sleep(Duration::from_secs(5));
            return Ok(());
        }
        "extra-control" => child.channel.send(grant_message(), &[])?,
        "duplicate-completion" | "duplicate-completion-exit" => {
            child.publish_drained(deadline)?;
            child.channel.send(
                Message::DrainComplete {
                    session: child.session.clone(),
                    connection: child.connection.clone(),
                    receipt: receipt(),
                },
                &[],
            )?;
            if role == "duplicate-completion-exit" {
                std::process::exit(0);
            }
        }
        "foreign-completion" => {
            let mut foreign = receipt();
            foreign.sha256 = "c".repeat(64);
            child.channel.send(
                Message::DrainComplete {
                    session: child.session.clone(),
                    connection: child.connection.clone(),
                    receipt: foreign,
                },
                &[],
            )?;
        }
        "partial-completion" | "partial-after-completion-exit" => {
            if role == "partial-after-completion-exit" {
                child.publish_drained(deadline)?;
            }
            let bytes = [0u8, 0, 1];
            let fd = child.channel.stream_fd_for_test();
            // SAFETY: the actor borrows its live owned socket and initialized
            // bytes, then closes only its write direction to truncate a frame.
            unsafe {
                assert_eq!(libc::send(fd, bytes.as_ptr().cast(), bytes.len(), 0), 3);
                assert_eq!(libc::shutdown(fd, libc::SHUT_WR), 0);
            }
            if role == "partial-after-completion-exit" {
                std::process::exit(0);
            }
        }
        _ => {
            child.publish_drained(deadline)?;
            io::stdout().flush()?;
            io::stderr().flush()?;
            std::process::exit(0);
        }
    }
    // Adversarial roles stay alive so a protocol failure cannot be confused
    // with an ordinary process exit. The parent's owned guard ends the actor.
    std::thread::sleep(Duration::from_secs(5));
    Ok(())
}
