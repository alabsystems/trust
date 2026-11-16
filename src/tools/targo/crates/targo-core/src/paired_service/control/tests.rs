use super::*;
use trust_resource_controller::paired_qualification::service::Node;

fn binding() -> Binding {
    Binding {
        root_attempt: [1; 16],
        invocation_sha256: [2; 32],
    }
}
fn checkpoint() -> Checkpoint {
    Checkpoint {
        binding: binding(),
        sequence: 1,
        node: Node::AyCompile,
        outcome_sha256: [3; 32],
    }
}
fn send(stream: &mut UnixStream, frame: &Frame) {
    let bytes = frame.encode(1).unwrap();
    stream
        .write_all(&(bytes.len() as u32).to_be_bytes())
        .unwrap();
    stream.write_all(&bytes).unwrap();
}
fn owner(root: RootControl) -> crate::util::GlobalContext {
    let mut context = crate::util::GlobalContext::new(
        cargo_util_terminal::Shell::new(),
        std::env::current_dir().unwrap(),
        std::env::current_dir().unwrap(),
    );
    context.install_root_control(root).unwrap();
    context
}
#[test]
fn actual_original_ack_continues_once_and_duplicate_poison_retains_received_bytes() {
    let (read, mut write) = UnixStream::pair().unwrap();
    let stop = Arc::new(AtomicBool::new(false));
    let until = Instant::now() + Duration::from_secs(5);
    let (mut control, root) =
        Control::start(binding(), 1, Input::from_stream(read), until, stop.clone()).unwrap();
    let context = owner(root);
    control.expect(checkpoint(), until).unwrap();
    send(&mut write, &Frame::Continue(checkpoint()));
    control.wait(until).unwrap();
    assert!(!stop.load(Ordering::Acquire));
    send(&mut write, &Frame::Continue(checkpoint()));
    drop(write);
    while !context.poll_root_cancellation() {
        assert!(Instant::now() < until);
        std::thread::sleep(Duration::from_millis(1));
    }
    assert!(control.finish().is_err());
    let (prefix, seen, failure, stopped) = control.observation().unwrap();
    assert_eq!(seen, prefix.len() as u64);
    assert!(seen > 0);
    assert!(failure.is_some());
    assert!(!stopped);
    assert!(stop.load(Ordering::Acquire));
    assert!(
        control
            .expect(
                Checkpoint {
                    sequence: 2,
                    ..checkpoint()
                },
                until
            )
            .is_err()
    );
}
#[test]
fn wrong_node_or_outcome_cannot_resume_the_actual_pending_graph() {
    for wrong in [
        Checkpoint {
            node: Node::Strict,
            ..checkpoint()
        },
        Checkpoint {
            outcome_sha256: [9; 32],
            ..checkpoint()
        },
    ] {
        let (read, mut write) = UnixStream::pair().unwrap();
        let stop = Arc::new(AtomicBool::new(false));
        let until = Instant::now() + Duration::from_secs(5);
        let (mut control, root) =
            Control::start(binding(), 1, Input::from_stream(read), until, stop.clone()).unwrap();
        let context = owner(root);
        control.expect(checkpoint(), until).unwrap();
        send(&mut write, &Frame::Continue(wrong));
        drop(write);
        assert!(control.wait(until).is_err());
        while !context.poll_root_cancellation() {
            assert!(Instant::now() < until);
            std::thread::sleep(Duration::from_millis(1));
        }
        assert!(control.finish().is_err());
        assert!(control.observation().unwrap().2.is_some());
        assert!(stop.load(Ordering::Acquire));
    }
}
#[test]
fn original_stop_and_eof_cancel_the_same_root_and_finished_reader_never_fabricates_eof() {
    let (read, mut write) = UnixStream::pair().unwrap();
    let stop = Arc::new(AtomicBool::new(false));
    let until = Instant::now() + Duration::from_secs(5);
    let (mut control, root) =
        Control::start(binding(), 1, Input::from_stream(read), until, stop.clone()).unwrap();
    let context = owner(root);
    control.begin_phase(until).unwrap();
    control.end_phase().unwrap();
    send(&mut write, &Frame::Stop(binding()));
    while !context.poll_root_cancellation() {
        assert!(Instant::now() < until);
        std::thread::sleep(Duration::from_millis(1));
    }
    assert!(control.begin_phase(until).is_err());
    drop(write);
    control.finish().unwrap();
    let (_, seen, failure, stopped) = control.observation().unwrap();
    assert!(seen > 0);
    assert!(failure.is_none());
    assert!(stopped);
    let (read, write) = UnixStream::pair().unwrap();
    let (mut control, _) = Control::start(
        binding(),
        1,
        Input::from_stream(read),
        until,
        Arc::new(AtomicBool::new(false)),
    )
    .unwrap();
    // The writer is still live: cancellation/join closes this logical reader,
    // never claims physical EOF or a target's positive retirement.
    control.finish().unwrap();
    assert_eq!(control.observation().unwrap(), (Vec::new(), 0, None, false));
    drop(write);
}
