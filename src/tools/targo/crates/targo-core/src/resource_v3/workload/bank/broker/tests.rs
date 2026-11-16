use super::*;
use crate::compiler::resource_fifo::PrivateFifo;
use std::collections::VecDeque;
use std::num::NonZeroU32;
use std::os::fd::AsRawFd;
use trust_build_cpu::{Owner, Pool};

struct Fixture {
    bank: Arc<RootCreditBank>,
    _directory: tempfile::TempDir,
}
impl Fixture {
    fn new() -> Self {
        Self::new_in(None)
    }
    fn new_in(parent: Option<&std::path::Path>) -> Self {
        // Actual private kernel guards exercise owner conservation, not an
        // authenticated managed SDK or production host grant.
        let directory = match parent {
            Some(parent) => tempfile::tempdir_in(parent).unwrap(),
            None => tempfile::tempdir().unwrap(),
        };
        let pool = Pool::open_in(directory.path(), NonZeroU32::new(4).unwrap()).unwrap();
        let mut originals = Vec::new();
        for _ in 0..4 {
            let lease = pool.try_acquire(Owner::current(None)).unwrap().unwrap();
            let meta = std::fs::File::from(lease.as_fd().try_clone_to_owned().unwrap())
                .metadata()
                .unwrap();
            originals.push(Original {
                lease: Arc::new(lease),
                backing: FileIdentity {
                    device: meta.dev(),
                    inode: meta.ino(),
                },
            });
        }
        let bank =
            RootCreditBank::retained(originals, [1; 16], [2; 32], 3, Arc::new(|_| 3)).unwrap();
        Self {
            _directory: directory,
            bank,
        }
    }
}

#[derive(Default)]
struct Observed {
    calls: Vec<(std::thread::ThreadId, phase::Request)>,
    polls: usize,
    polls_at_drain: Option<usize>,
    registrations: Vec<(std::thread::ThreadId, produced::Registration, i32)>,
}
struct TestControl {
    decisions: VecDeque<u8>,
    observed: Arc<Mutex<Observed>>,
    mutate_output: Option<std::path::PathBuf>,
}
impl TestControl {
    fn new(decisions: &[u8]) -> Self {
        Self {
            decisions: decisions.iter().copied().collect(),
            observed: Arc::new(Mutex::new(Observed::default())),
            mutate_output: None,
        }
    }
}
impl Control for TestControl {
    unsafe fn register(
        &mut self,
        request: &produced::Registration,
        original: BorrowedFd<'_>,
        _: Instant,
    ) -> Result<RegisteredOutput, WorkloadControlError> {
        self.observed.lock().unwrap().registrations.push((
            std::thread::current().id(),
            request.clone(),
            original.as_raw_fd(),
        ));
        if let Some(path) = self.mutate_output.take() {
            std::fs::write(path, b"changed actual original input during registration").unwrap();
        }
        Err(WorkloadControlError::BeforeRequest(
            io::ErrorKind::Unsupported.into(),
        ))
    }
    unsafe fn output(
        &mut self,
        _: &output::Request,
        _: &[BorrowedFd<'_>],
        _: Instant,
    ) -> Result<RetainedOutputLocks, WorkloadControlError> {
        Err(WorkloadControlError::BeforeRequest(
            io::ErrorKind::Unsupported.into(),
        ))
    }
    fn poll_bank(
        &mut self,
        _bank: &RootCreditBank,
        _deadline: Instant,
    ) -> io::Result<Option<bank::Request>> {
        let mut observed = self.observed.lock().unwrap();
        assert!(
            observed.polls_at_drain.is_none(),
            "no bank poll after host Drained"
        );
        observed.polls += 1;
        Ok(None)
    }
    fn reply_bank(&mut self, _answer: &Answer, _deadline: Instant) -> io::Result<()> {
        panic!("no synthetic bank requests in this phase actor")
    }
    fn phase(
        &mut self,
        request: &phase::Request,
        fds: Option<[BorrowedFd<'_>; 2]>,
        _deadline: Instant,
    ) -> io::Result<phase::Reply> {
        let mut observed = self.observed.lock().unwrap();
        observed
            .calls
            .push((std::thread::current().id(), request.clone()));
        if let phase::Operation::Enter { gnu, .. } = request.operation {
            let fds = fds.expect("actual original witnesses");
            for fd in fds {
                let meta = std::fs::File::from(fd.try_clone_to_owned().unwrap())
                    .metadata()
                    .unwrap();
                assert_eq!((meta.dev(), meta.ino()), (gnu.device, gnu.inode));
            }
            let mut available: libc::c_int = -1;
            // SAFETY: observe the same retained read description, no read or
            // flag mutation. Positive controls retain actual Acquired guards.
            assert_eq!(
                unsafe { libc::ioctl(fds[0].as_raw_fd(), libc::FIONREAD, &mut available) },
                0
            );
            assert_eq!(available, 0);
        } else {
            assert!(fds.is_none());
        }
        let decision = match self.decisions.pop_front().unwrap() {
            0 => phase::Decision::Busy,
            1 => {
                let phase::Operation::Enter { phase, gnu, .. } = request.operation else {
                    panic!("Enter expected")
                };
                phase::Decision::Ready {
                    phase,
                    reserved_domain: 4,
                    gnu,
                }
            }
            2 => {
                let phase::Operation::Leave { phase } = request.operation else {
                    panic!("Leave expected")
                };
                phase::Decision::Left { phase }
            }
            3 => {
                assert_eq!(request.operation, phase::Operation::Drained);
                observed.polls_at_drain = Some(observed.polls);
                phase::Decision::Drained
            }
            4 => phase::Decision::Refused {
                reason: "known unavailable phase".into(),
            },
            5 => {
                let phase::Operation::Enter { phase, gnu, .. } = request.operation else {
                    panic!("Enter expected")
                };
                phase::Decision::Ready {
                    phase,
                    reserved_domain: 3,
                    gnu,
                }
            }
            _ => unreachable!(),
        };
        Ok(phase::Reply {
            key: request.key.clone(),
            decision,
        })
    }
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[test]
fn intermediate_script_retains_one_original_image_and_cannot_resume_from_registration_refusal() {
    use crate::ops::cargo_test::workload::{Materialization, actual_input_fixture};
    let directory = tempfile::tempdir().unwrap();
    let original = actual_input_fixture(directory.path(), Materialization::Warm);
    let mut fixture = Fixture::new();
    Arc::get_mut(&mut fixture.bank).unwrap().invocation_sha256 = original.invocation_sha256();
    fixture.bank.park().unwrap();
    let fifo = PrivateFifo::fixture(2);
    let mut phases = state();
    // Private kernel/input/control mechanics only: this test does not create
    // a managed SDK, successful compiler product or actual host admission.
    let mut control = TestControl::new(&[1, 2]);
    let until = Instant::now() + Duration::from_secs(60);
    let phase = phases
        .enter(
            &fixture.bank,
            &mut control,
            [8; 16],
            phase::Kind::BuildScript,
            fifo.try_escrow().unwrap().unwrap(),
            until,
        )
        .unwrap();
    assert!(
        phases
            .register(&fixture.bank, &mut control, phase, original.clone(), until)
            .is_err()
    );
    assert_eq!(control.observed.lock().unwrap().registrations.len(), 1);
    // Even a before-request refusal retains its exact offered input. A
    // second output cannot shrink/replace this phase's one-script population.
    assert!(
        phases
            .register(&fixture.bank, &mut control, phase, original.clone(), until)
            .is_err()
    );
    assert_eq!(control.observed.lock().unwrap().registrations.len(), 1);
    assert!(fixture.bank.try_primary().unwrap().is_none());
    let weak = Arc::downgrade(&original);
    drop(original);
    assert!(weak.upgrade().is_some());
    assert_eq!(fifo.available(), 0);
    phases
        .leave(&fixture.bank, &mut control, phase, until)
        .unwrap();
    assert!(weak.upgrade().is_none());
    assert_eq!(fifo.available(), 1);
    let actual = fixture
        .bank
        .try_primary()
        .unwrap()
        .expect("same original table resumes only after positive Leave");
    drop(actual); // Unexposed primary: no target/member was created by this fixture.
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[test]
fn registration_outcome_drift_keeps_inputs_through_cleanup_and_never_resumes_dispatch() {
    use crate::ops::cargo_test::workload::{Materialization, actual_input_fixture};
    let directory = tempfile::tempdir().unwrap();
    let original = actual_input_fixture(directory.path(), Materialization::Warm);
    let mut fixture = Fixture::new();
    Arc::get_mut(&mut fixture.bank).unwrap().invocation_sha256 = original.invocation_sha256();
    fixture.bank.park().unwrap();
    let fifo = PrivateFifo::fixture(2);
    let mut phases = state();
    let mut control = TestControl::new(&[1, 2, 3]);
    control.mutate_output = Some(original.image().program().to_owned());
    let deadline = Instant::now() + Duration::from_secs(60);
    let phase = phases
        .enter(
            &fixture.bank,
            &mut control,
            [8; 16],
            phase::Kind::Harnesses,
            fifo.try_escrow().unwrap().unwrap(),
            deadline,
        )
        .unwrap();
    let outcome = phases.register(
        &fixture.bank,
        &mut control,
        phase,
        original.clone(),
        deadline,
    );
    assert!(
        matches!(outcome, Err(ref error) if error.kind() != io::ErrorKind::Unsupported),
        "post-outcome original-input validation must fail independently of the known refusal"
    );
    let weak = Arc::downgrade(&original);
    drop(original);
    assert!(weak.upgrade().is_some());
    assert!(
        phases
            .leave(&fixture.bank, &mut control, phase, deadline)
            .is_err()
    );
    assert!(
        phases.active.is_none(),
        "actual positive Left still closes the failed phase"
    );
    assert!(weak.upgrade().is_none());
    assert_eq!(
        fifo.available(),
        1,
        "only positively retired original GNU bytes return"
    );
    assert!(fixture.bank.is_drained().unwrap());
    assert!(
        fixture.bank.try_primary().unwrap().is_none(),
        "failed input never resumes this graph"
    );
    phases.drain(&fixture.bank, &mut control, deadline).unwrap();
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[test]
fn actual_native_output_registration_retains_same_image_and_guards_until_positive_leave() {
    use crate::ops::cargo_test::workload::{Materialization, actual_input_fixture};
    let directory = tempfile::tempdir().unwrap();
    let original = actual_input_fixture(
        directory.path(),
        Materialization::Compiled { member: [3; 16] },
    );
    let mut fixture = Fixture::new();
    Arc::get_mut(&mut fixture.bank).unwrap().invocation_sha256 = original.invocation_sha256();
    fixture.bank.park().unwrap();
    let fifo = PrivateFifo::fixture(2);
    let mut phases = state();
    let mut control = TestControl::new(&[1, 2]);
    let deadline = Instant::now() + Duration::from_secs(60);
    let phase = phases
        .enter(
            &fixture.bank,
            &mut control,
            [8; 16],
            phase::Kind::Harnesses,
            fifo.try_escrow().unwrap().unwrap(),
            deadline,
        )
        .unwrap();
    let same = original
        .image()
        .executable_descriptor(deadline)
        .unwrap()
        .as_raw_fd();
    let result = phases.register(
        &fixture.bank,
        &mut control,
        phase,
        original.clone(),
        deadline,
    );
    assert!(matches!(result, Err(ref error) if error.kind() == io::ErrorKind::Unsupported));
    assert_eq!(phases.active.as_ref().unwrap().outputs.len(), 1);
    let weak = Arc::downgrade(&original);
    let observations = control.observed.lock().unwrap();
    let (_, request, offered) = observations.registrations.last().unwrap();
    assert_eq!(
        *offered, same,
        "borrow only the SAME original held readonly description"
    );
    assert_eq!(request.producer_attempt, Some([3; 16]));
    assert_eq!(request.key.phase, phase.nonce);
    assert_eq!(request.key.ordinal, phase.ordinal);
    drop(observations);
    drop(original);
    assert!(
        weak.upgrade().is_some(),
        "caller drop cannot release an offered image"
    );
    assert_eq!(fifo.available(), 0);
    phases
        .leave(&fixture.bank, &mut control, phase, deadline)
        .unwrap();
    assert!(
        weak.upgrade().is_none(),
        "positive phase closure releases its image owner"
    );
    assert_eq!(fifo.available(), 1);
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[test]
fn changed_original_native_output_or_wrong_phase_refuses_before_descriptor_delivery() {
    use crate::ops::cargo_test::workload::{Materialization, actual_input_fixture};
    let directory = tempfile::tempdir().unwrap();
    let original = actual_input_fixture(directory.path(), Materialization::Warm);
    let mut fixture = Fixture::new();
    Arc::get_mut(&mut fixture.bank).unwrap().invocation_sha256 = original.invocation_sha256();
    fixture.bank.park().unwrap();
    let fifo = PrivateFifo::fixture(2);
    let mut phases = state();
    let mut control = TestControl::new(&[1, 2]);
    let deadline = Instant::now() + Duration::from_secs(60);
    let phase = phases
        .enter(
            &fixture.bank,
            &mut control,
            [8; 16],
            phase::Kind::Harnesses,
            fifo.try_escrow().unwrap().unwrap(),
            deadline,
        )
        .unwrap();
    let mut wrong = phase;
    wrong.ordinal += 1;
    assert!(
        phases
            .register(
                &fixture.bank,
                &mut control,
                wrong,
                original.clone(),
                deadline
            )
            .is_err()
    );
    let request = original
        .registration(
            produced::Key {
                root_attempt: [1; 16],
                invocation_sha256: original.invocation_sha256(),
                phase: phase.nonce,
                ordinal: phase.ordinal,
                output: [9; 16],
            },
            deadline,
        )
        .unwrap()
        .0;
    assert_eq!(
        request.producer_attempt, None,
        "only actual recorded warm materialization omits a compiler"
    );
    std::fs::write(
        original.image().program(),
        b"actual drift after retained native capture",
    )
    .unwrap();
    assert!(
        phases
            .register(&fixture.bank, &mut control, phase, original, deadline)
            .is_err()
    );
    assert!(control.observed.lock().unwrap().registrations.is_empty());
    phases
        .leave(&fixture.bank, &mut control, phase, deadline)
        .unwrap();
}

#[test]
#[expect(
    clippy::disallowed_methods,
    reason = "isolated native broker actor selects its checked failure before config"
)]
fn native_wrong_domain_and_refused_leave_abort_without_returning_original_gnu() {
    const CASE: &str = "TARGO_PHASE_ABORT_CASE";
    const PARENT: &str = "TARGO_PHASE_ABORT_PARENT";
    if let Ok(case) = std::env::var(CASE) {
        use std::os::unix::ffi::OsStrExt;
        let parent = std::path::PathBuf::from(std::env::var_os(PARENT).unwrap());
        let fixture = Fixture::new_in(Some(&parent));
        fixture.bank.park().unwrap();
        let fifo = PrivateFifo::fixture_in(2, &parent);
        let escrow = fifo.try_escrow().unwrap().unwrap();
        assert_eq!(fifo.available(), 0);
        let mut phases = state();
        let mut control = TestControl::new(if case == "wrong-domain" {
            &[5]
        } else {
            assert_eq!(case, "refused-leave");
            &[1, 4]
        });
        std::fs::write(
            parent.join("checked-fifo"),
            fifo.fixture_path().as_os_str().as_bytes(),
        )
        .unwrap();
        let deadline = Instant::now() + Duration::from_secs(3);
        let active = phases
            .enter(
                &fixture.bank,
                &mut control,
                [8; 16],
                phase::Kind::BuildScript,
                escrow,
                deadline,
            )
            .unwrap();
        phases
            .leave(&fixture.bank, &mut control, active, deadline)
            .unwrap();
        unreachable!("uncertain original phase escaped abort");
    }
    let module = module_path!().split_once("::").unwrap().1;
    let exact = format!(
        "{module}::native_wrong_domain_and_refused_leave_abort_without_returning_original_gnu"
    );
    for case in ["wrong-domain", "refused-leave"] {
        let parent = tempfile::tempdir().unwrap();
        let status = std::process::Command::new(std::env::current_exe().unwrap())
            .args(["--exact", &exact])
            .env(CASE, case)
            .env(PARENT, parent.path())
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null())
            .status()
            .unwrap();
        assert_eq!(status.code(), Some(75), "{case}");
        use std::os::unix::ffi::OsStringExt;
        let path = std::path::PathBuf::from(std::ffi::OsString::from_vec(
            std::fs::read(parent.path().join("checked-fifo")).unwrap(),
        ));
        let original = jobserver_utils::Jobserver::from_fifo(&path).unwrap();
        assert_eq!(
            original.client().available().unwrap(),
            0,
            "{case}: offered Acquired guards never returned"
        );
    }
}

fn state() -> Phases {
    Phases {
        sequence: 0,
        active: None,
        drained: false,
    }
}

#[test]
fn original_guards_stay_escrowed_until_exact_positive_leave_and_busy_changes_ordinal() {
    let fixture = Fixture::new();
    fixture.bank.park().unwrap();
    let fifo = PrivateFifo::fixture(3);
    let mut phases = state();
    let mut control = TestControl::new(&[0, 1, 0, 2, 3]);
    let deadline = Instant::now() + Duration::from_secs(3);
    let phase = phases
        .enter(
            &fixture.bank,
            &mut control,
            [8; 16],
            phase::Kind::BuildScript,
            fifo.try_escrow().unwrap().unwrap(),
            deadline,
        )
        .unwrap();
    assert_eq!(
        phase.ordinal, 2,
        "accepted Enter sequence, including prior Busy"
    );
    assert_eq!(fifo.available(), 0);
    assert!(fixture.bank.try_primary().unwrap().is_none());
    let mut stale = phase;
    stale.ordinal = 1;
    assert!(
        phases
            .leave(&fixture.bank, &mut control, stale, deadline)
            .is_err()
    );
    assert_eq!(
        control.observed.lock().unwrap().calls.len(),
        2,
        "stale local observation never delivered"
    );
    assert_eq!(fifo.available(), 0);
    phases
        .leave(&fixture.bank, &mut control, phase, deadline)
        .unwrap();
    assert_eq!(fifo.available(), 2);
    assert!(
        fixture.bank.try_primary().unwrap().is_some(),
        "original local dispatch resumes only after tokens return"
    );
    fixture.bank.park().unwrap();
    phases.drain(&fixture.bank, &mut control, deadline).unwrap();
    assert!(phases.drained);
    assert_eq!(
        control
            .observed
            .lock()
            .unwrap()
            .calls
            .iter()
            .map(|(_, r)| r.key.sequence)
            .collect::<Vec<_>>(),
        [1, 2, 3, 4, 5]
    );
}

#[test]
fn real_unretired_loan_blocks_enter_and_known_refusal_returns_only_original_tokens() {
    let fixture = Fixture::new();
    let primary = fixture.bank.try_primary().unwrap().unwrap();
    fixture.bank.park().unwrap();
    let fifo = PrivateFifo::fixture(2);
    let mut phases = state();
    let mut control = TestControl::new(&[4, 3]);
    let deadline = Instant::now() + Duration::from_secs(3);
    assert!(
        phases
            .enter(
                &fixture.bank,
                &mut control,
                [8; 16],
                phase::Kind::Harnesses,
                fifo.try_escrow().unwrap().unwrap(),
                deadline
            )
            .is_err()
    );
    assert!(control.observed.lock().unwrap().calls.is_empty());
    assert_eq!(fifo.available(), 1);
    drop(primary); // never bound/delivered; safe actual local return.
    assert!(
        phases
            .enter(
                &fixture.bank,
                &mut control,
                [0; 16],
                phase::Kind::Harnesses,
                fifo.try_escrow().unwrap().unwrap(),
                deadline
            )
            .is_err()
    );
    assert_eq!(
        phases.sequence, 0,
        "before-delivery malformed nonce consumes no wire sequence"
    );
    let error = phases
        .enter(
            &fixture.bank,
            &mut control,
            [8; 16],
            phase::Kind::Harnesses,
            fifo.try_escrow().unwrap().unwrap(),
            deadline,
        )
        .unwrap_err();
    assert_eq!(error.kind(), io::ErrorKind::PermissionDenied);
    assert_eq!(fifo.available(), 1);
    assert!(
        fixture.bank.is_drained().unwrap(),
        "refusal cannot silently resume dispatch"
    );
    phases.drain(&fixture.bank, &mut control, deadline).unwrap();
    assert!(phases.drained);
}

#[test]
fn one_original_broker_thread_owns_phase_control_and_stops_bank_polling_after_drained() {
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    let (_directory, output, fixture) = {
        use crate::ops::cargo_test::workload::{Materialization, actual_input_fixture};
        let directory = tempfile::tempdir().unwrap();
        let output = actual_input_fixture(directory.path(), Materialization::Warm);
        let mut fixture = Fixture::new();
        Arc::get_mut(&mut fixture.bank).unwrap().invocation_sha256 = output.invocation_sha256();
        (directory, output, fixture)
    };
    #[cfg(not(all(target_os = "macos", target_arch = "aarch64")))]
    let fixture = Fixture::new();
    fixture.bank.park().unwrap();
    let fifo = PrivateFifo::fixture(2);
    let control = TestControl::new(&[1, 2, 3]);
    let observed = control.observed.clone();
    let (commands, receiver) = mpsc::sync_channel(1);
    let original = fixture.bank.clone();
    let deadline = Instant::now() + Duration::from_secs(60);
    let thread = std::thread::spawn(move || run(original, control, receiver, None, deadline));
    let (reply, response) = mpsc::sync_channel(1);
    commands
        .send(Command::Enter {
            nonce: [8; 16],
            kind: phase::Kind::Harnesses,
            escrow: fifo.try_escrow().unwrap().unwrap(),
            reply,
        })
        .unwrap();
    let phase = response
        .recv_timeout(Duration::from_secs(2))
        .unwrap()
        .unwrap();
    assert_eq!(fifo.available(), 0);
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    {
        let (reply, response) = mpsc::sync_channel(1);
        commands
            .send(Command::Register {
                phase,
                original: output,
                reply,
            })
            .unwrap();
        let result = response.recv_timeout(Duration::from_secs(30)).unwrap();
        assert!(matches!(result, Err(error) if error.kind() == io::ErrorKind::Unsupported));
    }
    let (reply, response) = mpsc::sync_channel(1);
    commands.send(Command::Leave { phase, reply }).unwrap();
    response
        .recv_timeout(Duration::from_secs(2))
        .unwrap()
        .unwrap();
    assert_eq!(fifo.available(), 1);
    fixture.bank.park().unwrap();
    let (reply, response) = mpsc::sync_channel(1);
    commands.send(Command::Drained { reply }).unwrap();
    response
        .recv_timeout(Duration::from_secs(2))
        .unwrap()
        .unwrap();
    commands.send(Command::Finish).unwrap();
    let control = thread.join().unwrap();
    assert!(control.decisions.is_empty());
    let observed = observed.lock().unwrap();
    let owner = observed.calls[0].0;
    assert_ne!(owner, std::thread::current().id());
    assert!(observed.calls.iter().all(|(thread, _)| *thread == owner));
    assert!(
        observed
            .registrations
            .iter()
            .all(|(thread, _, _)| *thread == owner)
    );
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    assert_eq!(observed.registrations.len(), 1);
    assert_eq!(Some(observed.polls), observed.polls_at_drain);
}

#[test]
fn original_broker_captures_its_bound_fifo_only_after_actual_credits_return() {
    let fixture = Fixture::new();
    fixture.bank.park().unwrap();
    let fifo = PrivateFifo::fixture(2);
    let original = jobserver_utils::Jobserver::from_fifo(&fifo.fixture_path()).unwrap();
    let worker = original.client().try_acquire().unwrap().unwrap();
    let control = TestControl::new(&[1, 2, 3]);
    let (commands, receiver) = mpsc::sync_channel(1);
    let bank = fixture.bank.clone();
    let thread = std::thread::spawn(move || {
        run(
            bank,
            control,
            receiver,
            None,
            Instant::now() + Duration::from_secs(60),
        )
    });
    let (reply, answer) = mpsc::sync_channel(1);
    commands
        .send(Command::BindFifo {
            fifo: fifo.clone(),
            reply,
        })
        .unwrap();
    answer
        .recv_timeout(Duration::from_secs(5))
        .unwrap()
        .unwrap();
    let (reply, answer) = mpsc::sync_channel(1);
    commands
        .send(Command::TryEnter {
            nonce: [8; 16],
            kind: phase::Kind::Harnesses,
            reply,
        })
        .unwrap();
    assert!(
        answer
            .recv_timeout(Duration::from_secs(5))
            .unwrap()
            .unwrap()
            .is_none()
    );
    drop(worker);
    let (reply, answer) = mpsc::sync_channel(1);
    commands
        .send(Command::TryEnter {
            nonce: [8; 16],
            kind: phase::Kind::Harnesses,
            reply,
        })
        .unwrap();
    let phase = answer
        .recv_timeout(Duration::from_secs(5))
        .unwrap()
        .unwrap()
        .unwrap();
    assert_eq!(fifo.available(), 0);
    let (reply, answer) = mpsc::sync_channel(1);
    commands.send(Command::Leave { phase, reply }).unwrap();
    answer
        .recv_timeout(Duration::from_secs(5))
        .unwrap()
        .unwrap();
    assert_eq!(fifo.available(), 1);
    fixture.bank.park().unwrap();
    let (reply, answer) = mpsc::sync_channel(1);
    commands.send(Command::Drained { reply }).unwrap();
    assert!(
        answer
            .recv_timeout(Duration::from_secs(5))
            .unwrap()
            .unwrap()
    );
    commands.send(Command::Finish).unwrap();
    assert!(thread.join().unwrap().decisions.is_empty());
    // Only actual private FIFO/bank custody was exercised, never a fabricated
    // authenticated Host/SDK or a production execution grant.
}
