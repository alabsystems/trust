use super::*;

#[test]
#[expect(
    clippy::disallowed_methods,
    reason = "capture actor reads its parent's actual environment before a Cargo context exists"
)]
fn original_protocol_stdout_is_private_after_actual_native_capture() {
    const ACTOR: &str = "TRUST_WORKLOAD_OUTPUT_CAPTURE_TEST_ACTOR";
    const PAYLOAD: &[u8] = b"framed-original-output\0\xff";
    const UNFRAMED: &[u8] = b"ordinary-unframed-print-must-be-contained";
    if std::env::var_os(ACTOR).is_some() {
        let owner = Output::capture_stdout(
            Instant::now() + Duration::from_secs(5),
            Arc::new(AtomicBool::new(false)),
        )
        .unwrap();
        std::io::stdout().write_all(UNFRAMED).unwrap();
        owner
            .frame(PAYLOAD, Instant::now() + Duration::from_secs(5))
            .unwrap();
        std::process::exit(0);
    }
    let actual = std::process::Command::new(std::env::current_exe().unwrap())
        .args(["--exact", "workload_service::transport::tests::original_protocol_stdout_is_private_after_actual_native_capture", "--nocapture"])
        .env(ACTOR, "1")
        .output()
        .unwrap();
    assert!(actual.status.success(), "{:?}", actual);
    let mut framed = (PAYLOAD.len() as u32).to_be_bytes().to_vec();
    framed.extend(PAYLOAD);
    assert!(actual.stdout.ends_with(&framed));
    assert!(
        !actual
            .stdout
            .windows(UNFRAMED.len())
            .any(|bytes| bytes == UNFRAMED)
    );
}
use crate::util::GlobalContext;
use cargo_util_terminal::Shell;

fn write_frame(stream: &mut UnixStream, bytes: &[u8]) {
    stream
        .write_all(&(bytes.len() as u32).to_be_bytes())
        .unwrap();
    stream.write_all(bytes).unwrap();
}
fn binding() -> Binding {
    Binding {
        root_attempt: [1; 16],
        invocation_sha256: [2; 32],
    }
}
fn control() -> (Control, GlobalContext, UnixStream) {
    let (control, context, caller, _monitor) = control_with_monitor();
    (control, context, caller)
}
fn control_with_monitor() -> (Control, GlobalContext, UnixStream, UnixStream) {
    let (root, caller) = UnixStream::pair().unwrap();
    let monitor = root.try_clone().unwrap();
    let (control, queue) = Control::start(
        binding(),
        Input::from_stream(root),
        Instant::now() + Duration::from_secs(30),
        Arc::new(AtomicBool::new(false)),
    )
    .unwrap();
    let mut context = GlobalContext::new(
        Shell::from_write(Box::new(Vec::new())),
        std::env::current_dir().unwrap(),
        std::env::temp_dir(),
    );
    context.install_root_control(queue).unwrap();
    (control, context, caller, monitor)
}
fn stopped(context: &GlobalContext) {
    let until = Instant::now() + Duration::from_secs(5);
    while !context.poll_root_cancellation() {
        assert!(
            Instant::now() < until,
            "original queue did not receive stop intent"
        );
        std::thread::sleep(Duration::from_millis(1));
    }
    // The existing queue endpoint alone acknowledges its sticky dispatch stop.
    context.acknowledge_root_stopped();
}

#[test]
fn service_input_requires_one_exact_pending_continuation_and_wrong_binding_stops_original_queue() {
    let (mut control, context, mut caller) = control();
    let until = Instant::now() + Duration::from_secs(5);
    control.expect(1, [3; 32], until).unwrap();
    let mut ack = Continuation {
        root_attempt: [1; 16],
        invocation_sha256: [2; 32],
        checkpoint: 1,
        checkpoint_sha256: [3; 32],
        decision: Decision::Continue,
    };
    write_frame(&mut caller, &ack.encode().unwrap());
    assert_eq!(control.wait(until).unwrap(), Decision::Continue);
    assert!(
        control.expect(1, [3; 32], until).is_err(),
        "a completed checkpoint cannot rearm"
    );
    control.expect(2, [4; 32], until).unwrap();
    ack.checkpoint = 2;
    ack.checkpoint_sha256 = [4; 32];
    ack.invocation_sha256 = [9; 32];
    write_frame(&mut caller, &ack.encode().unwrap());
    stopped(&context);
    assert!(control.cancelled.load(Ordering::Acquire));
    assert!(control.wait(until).is_err());
    assert!(control.expect(3, [5; 32], until).is_err());
    assert!(control.finish().is_err());
    assert!(control.observation().unwrap().2.is_some());
}

#[test]
fn actual_compiler_deadline_stops_queue_but_retired_phase_does_not_truncate_checkpoint_budget() {
    let (mut control, context, _caller) = control();
    control
        .begin_compile(Instant::now() + Duration::from_millis(50))
        .unwrap();
    stopped(&context);
    assert!(control.cancelled.load(Ordering::Acquire));
    assert!(control.finish().is_err());
    let (mut control, _context, mut caller) = self::control();
    control
        .begin_compile(Instant::now() + Duration::from_millis(50))
        .unwrap();
    control.compiler_retired().unwrap();
    assert!(
        control
            .begin_compile(Instant::now() + Duration::from_secs(1))
            .is_err()
    );
    std::thread::sleep(Duration::from_millis(100));
    let until = Instant::now() + Duration::from_secs(5);
    control.expect(1, [3; 32], until).unwrap();
    write_frame(
        &mut caller,
        &Continuation {
            root_attempt: [1; 16],
            invocation_sha256: [2; 32],
            checkpoint: 1,
            checkpoint_sha256: [3; 32],
            decision: Decision::Continue,
        }
        .encode()
        .unwrap(),
    );
    assert_eq!(control.wait(until).unwrap(), Decision::Continue);
    control.finish().unwrap();
}

#[test]
fn explicit_stop_and_partial_control_eof_are_cancellation_never_retirement() {
    let (mut control, context, mut caller) = control();
    write_frame(&mut caller, &Stop { binding: binding() }.encode().unwrap());
    stopped(&context);
    assert!(control.cancelled.load(Ordering::Acquire));
    assert!(control.observation().unwrap().3);
    control.finish().unwrap();
    let (mut control, context, mut caller) = self::control();
    let actual = b"\0\0\0\x20partial\0\xff";
    caller.write_all(actual).unwrap();
    drop(caller);
    stopped(&context);
    assert!(control.finish().is_err());
    let (prefix, seen, failure, stopped) = control.observation().unwrap();
    assert_eq!(prefix, actual);
    assert_eq!(seen, actual.len() as u64);
    assert!(failure.is_some() && !stopped);
}

#[test]
fn finalization_retains_a_still_open_partial_control_frame_and_refuses_completion() {
    let (mut control, context, mut caller, monitor) = control_with_monitor();
    let actual = b"\0\0\0\x20live-partial\xff";
    caller.write_all(actual).unwrap();
    // Observe actual kernel consumption without requiring physical EOF.
    let until = Instant::now() + Duration::from_secs(5);
    loop {
        let mut remaining: libc::c_int = 0;
        assert_eq!(
            unsafe { libc::ioctl(monitor.as_raw_fd(), libc::FIONREAD, &mut remaining) },
            0
        );
        if remaining == 0 {
            break;
        }
        assert!(Instant::now() < until);
        std::thread::sleep(Duration::from_millis(1));
    }
    assert!(control.finish().is_err());
    let (prefix, seen, failure, _) = control.observation().unwrap();
    assert_eq!(prefix, actual);
    assert_eq!(seen, actual.len() as u64);
    assert!(failure.is_some());
    stopped(&context);
}

#[test]
fn original_stop_interrupts_real_output_backpressure_before_the_whole_root_deadline() {
    let (writer, _reader) = UnixStream::pair().unwrap();
    let size: libc::c_int = 4096;
    assert_eq!(
        unsafe {
            libc::setsockopt(
                writer.as_raw_fd(),
                libc::SOL_SOCKET,
                libc::SO_SNDBUF,
                (&raw const size).cast(),
                std::mem::size_of_val(&size) as _,
            )
        },
        0
    );
    let until = Instant::now() + Duration::from_secs(30);
    let output = Output::from_stream(writer, until);
    let writing = output.clone();
    let thread = std::thread::spawn(move || {
        writing.frame(&vec![b'x'; trust_resource_controller::MAX_PAYLOAD], until)
    });
    std::thread::sleep(Duration::from_millis(50));
    let stopped = Instant::now();
    output.cancelled.store(true, Ordering::Release);
    assert!(thread.join().unwrap().is_err());
    assert!(stopped.elapsed() < Duration::from_secs(5));
    assert!(output.failed.load(Ordering::Acquire));
}

#[test]
fn original_framed_output_preserves_binary_bytes_and_rejects_unbounded_length_before_allocation() {
    let (writer, reader) = UnixStream::pair().unwrap();
    let until = Instant::now() + Duration::from_secs(5);
    let output = Output::from_stream(writer, until);
    let mut input = Input::from_stream(reader);
    let bytes = b"actual\0framed\xffbytes";
    output.frame(bytes, until).unwrap();
    assert_eq!(input.frame(until, None).unwrap(), bytes);
    assert_eq!(input.seen, bytes.len() as u64 + 4);
    assert_eq!(&input.prefix[..4], &(bytes.len() as u32).to_be_bytes());
    let (root, mut caller) = UnixStream::pair().unwrap();
    let mut input = Input::from_stream(root);
    caller.write_all(&u32::MAX.to_be_bytes()).unwrap();
    assert!(input.frame(until, None).is_err());
    assert_eq!(input.prefix, u32::MAX.to_be_bytes());
    assert_eq!(input.seen, 4);
}

#[test]
fn real_output_backpressure_obeys_original_deadline_and_never_retries_a_partial_frame() {
    let (writer, reader) = UnixStream::pair().unwrap();
    let size: libc::c_int = 4096;
    // SAFETY: actual owned socket and initialized SO_SNDBUF value; no shared
    // resource/CPU/GNU description or transport flags are changed.
    assert_eq!(
        unsafe {
            libc::setsockopt(
                writer.as_raw_fd(),
                libc::SOL_SOCKET,
                libc::SO_SNDBUF,
                (&raw const size).cast(),
                std::mem::size_of_val(&size) as _,
            )
        },
        0
    );
    let begin = Instant::now();
    let until = begin + Duration::from_millis(100);
    let output = Output::from_stream(writer, until);
    assert!(
        output
            .frame(&vec![b'x'; trust_resource_controller::MAX_PAYLOAD], until)
            .is_err()
    );
    assert!(begin.elapsed() < Duration::from_secs(5));
    assert!(output.failed.load(Ordering::Acquire));
    assert!(
        output
            .frame(b"must never retry", Instant::now() + Duration::from_secs(5))
            .is_err()
    );
    let mut input = Input::from_stream(reader);
    let stop = AtomicBool::new(false);
    assert!(
        input
            .frame(Instant::now() + Duration::from_millis(100), Some(&stop))
            .is_err()
    );
    assert!(input.seen > 4 && input.seen < (trust_resource_controller::MAX_PAYLOAD as u64 + 4));
}
