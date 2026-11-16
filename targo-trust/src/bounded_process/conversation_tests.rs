//! Real original process/stream mechanics, without a managed SDK, native
//! target admission, resource grant or source/proof authority fixture.
use std::io::Write as _;
use std::os::fd::OwnedFd;
use std::os::unix::net::UnixStream;
use std::sync::Mutex;

use super::*;

#[test]
fn interactive_original_input_stays_open_for_ack_and_all_bytes_precede_the_prefix_result() {
    let (input, writer) = UnixStream::pair().unwrap();
    writer.set_write_timeout(Some(Duration::from_secs(5))).unwrap();
    let writer = Arc::new(Mutex::new(writer));
    let raw = Arc::new(Mutex::new(Vec::new()));
    let stdout_eof = Arc::new(AtomicBool::new(false));
    let observed = raw.clone();
    let eof = stdout_eof.clone();
    let replied = AtomicBool::new(false);
    let observer = Arc::new(move |stream, bytes: &[u8]| {
        if stream != 0 {
            return Ok(());
        }
        if bytes.is_empty() {
            eof.store(true, Ordering::Release);
            return Ok(());
        }
        let mut original = observed.lock().unwrap();
        original.extend_from_slice(bytes);
        if original.len() >= 7 && !replied.swap(true, Ordering::AcqRel) {
            writer.lock().unwrap().write_all(b"continue\n")?;
        }
        Ok(())
    });
    let mut command = Command::new("/bin/sh");
    command.args(["-c", "printf 'one\\000two'; IFS= read -r ack; [ \"$ack\" = continue ] || exit 7; printf finished; exit 9"]);
    let captured = output_with_checked_conversation(
        &mut command,
        File::from(OwnedFd::from(input)),
        "owned interactive mechanics",
        [64, 64],
        Instant::now() + Duration::from_secs(5),
        &|_, _| Ok(()),
        Conversation::new(observer, Arc::new(AtomicBool::new(false)), 3),
    );
    assert!(captured.validation.is_ok());
    let actual = captured.captured.unwrap();
    assert_eq!(actual.status.code(), Some(9));
    assert_eq!(captured.exit_observation, Some(actual.status));
    assert_eq!(actual.stdout, b"one"); // Explicit finite prefix, never complete raw bytes.
    assert_eq!(*raw.lock().unwrap(), b"one\0twofinished");
    assert!(stdout_eof.load(Ordering::Acquire));
    let streams = captured.conversation_output.unwrap();
    assert_eq!(streams.bytes_seen, [15, 0]);
    assert_eq!(streams.eof, [true, true]);
    assert_eq!(streams.bytes[0], b"one");
}

#[test]
fn observer_failure_retains_actual_prefix_and_same_owning_wait_before_returning() {
    let (input, _writer) = UnixStream::pair().unwrap();
    let mut command = Command::new("/bin/sh");
    command.args(["-c", "printf original-prefix; exec sleep 30"]);
    let observer = Arc::new(|stream, bytes: &[u8]| {
        if stream == 0 && !bytes.is_empty() {
            Err(io::Error::other("controlled original observer failure"))
        } else {
            Ok(())
        }
    });
    let started = Instant::now();
    let captured = output_with_checked_conversation(
        &mut command,
        File::from(OwnedFd::from(input)),
        "owned failed observer",
        [1024, 1024],
        started + Duration::from_secs(30),
        &|_, _| Ok(()),
        Conversation::new(observer, Arc::new(AtomicBool::new(false)), 4),
    );
    assert!(captured.captured.unwrap_err().contains("controlled original observer failure"));
    assert!(started.elapsed() < Duration::from_secs(5));
    assert!(captured.exit_observation.is_some(), "original outer child must actually be reaped");
    let failed = captured.failed_output.unwrap();
    assert_eq!(failed.bytes[0], b"orig");
    assert!(failed.bytes_seen[0] >= 4);
    // Observer failure does not fabricate physical EOF or hosted retirement.
    assert!(!failed.eof[0]);
}

#[test]
fn observer_panic_is_a_sticky_unknown_failure_and_stops_the_original_owned_child() {
    let (input, _writer) = UnixStream::pair().unwrap();
    let mut command = Command::new("/bin/sh");
    command.args(["-c", "printf actual; exec sleep 30"]);
    let observer = Arc::new(|stream, bytes: &[u8]| {
        if stream == 0 && !bytes.is_empty() {
            panic!("controlled observer panic");
        }
        Ok(())
    });
    let started = Instant::now();
    let captured = output_with_checked_conversation(
        &mut command,
        File::from(OwnedFd::from(input)),
        "owned panicked observer",
        [1024, 1024],
        started + Duration::from_secs(30),
        &|_, _| Ok(()),
        Conversation::new(observer, Arc::new(AtomicBool::new(false)), 6),
    );
    assert!(captured.captured.unwrap_err().contains("observer panicked"));
    assert!(started.elapsed() < Duration::from_secs(5));
    assert!(captured.exit_observation.is_some());
    assert_eq!(captured.failed_output.unwrap().bytes[0], b"actual");
}

#[test]
fn failed_stderr_observer_stops_and_joins_the_original_blocked_stdout_observer() {
    let (input, _writer) = UnixStream::pair().unwrap();
    let cancelled = Arc::new(AtomicBool::new(false));
    let active = Arc::new(AtomicBool::new(false));
    let release = Arc::new(AtomicBool::new(false));
    let observing = active.clone();
    let fallback = release.clone();
    let stopped = cancelled.clone();
    let observer = Arc::new(move |index, bytes: &[u8]| {
        if bytes.is_empty() {
            return Ok(());
        }
        let until = Instant::now() + Duration::from_secs(5);
        if index == 0 {
            observing.store(true, Ordering::Release);
            while !stopped.load(Ordering::Acquire)
                && !fallback.load(Ordering::Acquire)
                && Instant::now() < until
            {
                thread::sleep(Duration::from_millis(1));
            }
            observing.store(false, Ordering::Release);
            Ok(())
        } else {
            while !observing.load(Ordering::Acquire) && Instant::now() < until {
                thread::sleep(Duration::from_millis(1));
            }
            Err(io::Error::other("controlled second-stream failure"))
        }
    });
    let mut command = Command::new("/bin/sh");
    command.args(["-c", "printf actual-stdout; printf failed-stderr >&2; exec sleep 30"]);
    let captured = output_with_checked_conversation(
        &mut command,
        File::from(OwnedFd::from(input)),
        "blocked original observer",
        [1024, 1024],
        Instant::now() + Duration::from_secs(10),
        &|_, _| Ok(()),
        Conversation::new(observer, cancelled, 8),
    );
    let still_running = active.load(Ordering::Acquire);
    // Always release the original thread even on the expected pre-repair RED.
    release.store(true, Ordering::Release);
    let until = Instant::now() + Duration::from_secs(5);
    while active.load(Ordering::Acquire) && Instant::now() < until {
        thread::sleep(Duration::from_millis(1));
    }
    assert!(captured.captured.unwrap_err().contains("controlled second-stream failure"));
    assert!(captured.exit_observation.is_some());
    assert_eq!(captured.failed_output.unwrap().bytes[0], b"actual-s");
    assert!(
        !still_running,
        "capture returned while its original stdout observer was still running"
    );
}

#[test]
fn original_reader_cancellation_joins_without_waiting_for_or_inventing_pipe_eof() {
    use std::os::fd::AsRawFd as _;
    let (reader, mut held_writer) = std::io::pipe().unwrap();
    let fd = reader.as_raw_fd();
    let observed = Arc::new(Mutex::new(PartialCapture::default()));
    let mode =
        Conversation::new(Arc::new(|_, _: &[u8]| Ok(())), Arc::new(AtomicBool::new(false)), 8);
    let receiver = spawn_observed_reader(
        reader,
        1024,
        Arc::new(AtomicBool::new(false)),
        Some((observed.clone(), 0)),
        Some((mode.clone(), 0)),
        Some(fd),
    );
    // The original writer stays owned and open. No process/group stop can
    // make this descriptor produce EOF; only cancellation stops this read.
    held_writer.write_all(b"retained").unwrap();
    let until = Instant::now() + Duration::from_secs(5);
    while observed.lock().unwrap().bytes_seen[0] < 8 {
        assert!(Instant::now() < until);
        thread::sleep(Duration::from_millis(1));
    }
    let before = Instant::now();
    mode.finish_readers(true).unwrap();
    assert!(before.elapsed() < Duration::from_secs(1));
    assert!(receiver.recv_timeout(Duration::from_secs(1)).unwrap().is_err());
    let actual = observed.lock().unwrap();
    assert_eq!(actual.bytes[0], b"retained");
    assert!(!actual.eof[0]);
    assert!(actual.read_errors[0].as_ref().unwrap().contains("no physical EOF"));
    assert!(mode.readers.lock().unwrap().is_empty());
}

#[test]
fn actual_read_error_poisoning_reaches_the_original_capture_owner_without_an_exit() {
    let directory = tempfile::tempdir().unwrap();
    let mode = Conversation::new(
        Arc::new(|_, _: &[u8]| panic!("a read failure must not fabricate callback bytes or EOF")),
        Arc::new(AtomicBool::new(false)),
        8,
    );
    let original = Arc::new(Mutex::new(PartialCapture::default()));
    let mut reader = ObservedReader {
        inner: File::open(directory.path()).unwrap(),
        owner: Some((original.clone(), 0)),
        limit: 8,
        conversation: Some((mode.clone(), 0)),
        poll_fd: None,
    };
    assert!(reader.read(&mut [0; 8]).is_err());
    assert!(mode.failure().unwrap().contains("original conversation read failed"));
    let actual = original.lock().unwrap();
    assert!(!actual.eof[0]);
    assert!(actual.read_errors[0].is_some());
    assert_eq!(actual.bytes_seen, [0, 0]);
}

#[test]
fn already_stopped_interactive_owner_refuses_before_spawning_any_child() {
    let parent = tempfile::tempdir().unwrap();
    let marker = parent.path().join("must-not-exist");
    let (input, _writer) = UnixStream::pair().unwrap();
    let mut command = Command::new("/bin/sh");
    command.args(["-c", "printf touched > \"$1\"", "owned-marker"]).arg(&marker);
    let observer = Arc::new(|_, _: &[u8]| Ok(()));
    let captured = output_with_checked_conversation(
        &mut command,
        File::from(OwnedFd::from(input)),
        "prelaunch stop",
        [64, 64],
        Instant::now() + Duration::from_secs(5),
        &|_, _| Ok(()),
        Conversation::new(observer, Arc::new(AtomicBool::new(true)), 4),
    );
    assert!(captured.captured.unwrap_err().contains("before launch"));
    assert!(captured.exit_observation.is_none());
    assert!(!marker.exists());
}

#[test]
fn original_stop_interrupts_stream_drain_while_the_actual_exited_leader_stays_unreaped() {
    let mut command = Command::new("/bin/sh");
    command.args(["-c", "exit 0"]);
    let (mut child, _original) = process_lifecycle::spawn_owned(&mut command).unwrap();
    let until = Instant::now() + Duration::from_secs(5);
    while !exited_without_reaping(&mut child).unwrap() {
        assert!(Instant::now() < until);
        thread::sleep(Duration::from_millis(1));
    }
    let (out, held_writer) = std::io::pipe().unwrap();
    let stdout_writer = pipe_writer(&out);
    let stdout_watch = watch_of(&out);
    let exceeded = Arc::new(AtomicBool::new(false));
    let stdout = spawn_reader(out, 64, exceeded.clone());
    let (err, closed) = std::io::pipe().unwrap();
    let stderr_writer = pipe_writer(&err);
    let stderr_watch = watch_of(&err);
    drop(closed);
    let stderr = spawn_reader(err, 64, exceeded.clone());
    let mut streams = [
        Stream::new("stdout", stdout, stdout_writer, stdout_watch),
        Stream::new("stderr", stderr, stderr_writer, stderr_watch),
    ];
    let stop = Arc::new(AtomicBool::new(false));
    let signal = stop.clone();
    let signalling = thread::spawn(move || {
        thread::sleep(Duration::from_millis(20));
        signal.store(true, Ordering::Release);
    });
    let mode = Conversation::new(Arc::new(|_, _: &[u8]| Ok(())), stop, 4);
    let start = Instant::now();
    let bound = AfterExit {
        context: "actual exited original leader",
        child_pid: child.id(),
        max_stream_bytes: 64,
        stderr_limit: 64,
        output_exceeded: &exceeded,
        timeout: Duration::from_secs(30),
        grace_end: start + Duration::from_secs(10),
        deadline: start + Duration::from_secs(30),
    };
    assert!(
        receive_after_exit_with_control(&mut streams, &bound, Some(&mode))
            .unwrap_err()
            .contains("cancelled")
    );
    assert!(start.elapsed() < Duration::from_secs(5));
    signalling.join().unwrap();
    // Only now reap the same original leader; no later numeric signal is sent.
    assert!(child.wait().unwrap().success());
    drop(held_writer);
    for stream in &mut streams {
        stream.receive("original reader closure", Duration::from_secs(5)).unwrap();
    }
}
