use super::*;

fn sample() -> io::Result<Sample> {
    Ok(Sample { available: Some(100), load: 0.0, compilers: 0 })
}

fn window(now: Instant) -> QuietWindow {
    QuietWindow {
        since: None,
        last: None,
        deadline: now + Duration::from_secs(60),
        waiting: String::new(),
    }
}

fn observe(
    window: &mut QuietWindow,
    base: Instant,
    millis: u64,
    sample: io::Result<Sample>,
) -> bool {
    let now = base + Duration::from_millis(millis);
    window.observe(sample, now, now, NonZeroU32::new(4).unwrap(), 100)
}

#[test]
fn readiness_requires_the_complete_unbroken_measured_interval() {
    let base = Instant::now();
    let mut quiet = window(base);
    for millis in (0..10_000).step_by(500) {
        assert!(!observe(&mut quiet, base, millis, sample()));
    }
    assert!(observe(&mut quiet, base, 10_000, sample()));
    assert!(observe(&mut quiet, base, 10_500, sample()));
    // An unobserved gap cannot be filled by an old start timestamp.
    assert!(!observe(&mut quiet, base, 13_000, sample()));
}

#[test]
fn unknown_busy_malformed_and_short_memory_samples_erase_prior_quietness() {
    for bad in [
        Ok(Sample { available: None, load: 0.0, compilers: 0 }),
        Ok(Sample { available: Some(99), load: 0.0, compilers: 0 }),
        Ok(Sample { available: Some(100), load: f64::NAN, compilers: 0 }),
        Ok(Sample { available: Some(100), load: f64::INFINITY, compilers: 0 }),
        Ok(Sample { available: Some(100), load: -1.0, compilers: 0 }),
        Ok(Sample { available: Some(100), load: 1.401, compilers: 0 }),
        Ok(Sample { available: Some(100), load: 0.0, compilers: 1 }),
        Err(io::Error::from(io::ErrorKind::PermissionDenied)),
    ] {
        let base = Instant::now();
        let mut quiet = window(base);
        for millis in (0..10_000).step_by(500) {
            assert!(!observe(&mut quiet, base, millis, sample()));
        }
        assert!(!observe(&mut quiet, base, 10_000, bad));
        assert!(!observe(&mut quiet, base, 10_500, sample()));
        assert_eq!(quiet.since, Some(base + Duration::from_millis(10_500)));
    }
}

#[test]
fn slow_census_and_expired_deadline_cannot_complete_readiness() {
    let base = Instant::now();
    let mut quiet = window(base);
    for millis in (0..10_000).step_by(500) {
        observe(&mut quiet, base, millis, sample());
    }
    assert!(!quiet.observe(
        sample(),
        base + Duration::from_secs(9),
        base + Duration::from_secs(11),
        NonZeroU32::new(4).unwrap(),
        100,
    ));
    quiet.deadline = base;
    assert!(!observe(&mut quiet, base, 0, sample()));
}

#[test]
fn exact_native_names_are_conservative_without_argv_or_substring_matching() {
    for name in ["cargo", "targo", "rustc", "trustc"] {
        assert!(is_compiler(name.as_ref()));
    }
    for name in ["my-targo-helper", "cargo-build-log", "rustdoc", "trustc-worker-log", ""] {
        assert!(!is_compiler(name.as_ref()));
    }
}

#[test]
fn actual_system_census_contains_the_current_kernel_observer() {
    let pids = process::system_pids().unwrap();
    assert!(pids.contains(&std::process::id()));
    let current = process::read(std::process::id()).unwrap();
    assert_eq!(current.pid, std::process::id());
    assert!(!current.zombie);
}

#[test]
fn actual_host_readiness_sampler_observes_all_required_native_inputs() {
    let cpus =
        NonZeroU32::new(std::thread::available_parallelism().unwrap().get().try_into().unwrap())
            .unwrap();
    let sample = retry_foreign_exits(&[], || measure(cpus))
        .expect("complete native readiness observation must be available");
    assert!(sample.available.is_some(), "native memory unavailable");
    assert!(sample.load.is_finite() && sample.load >= 0.0, "native load unavailable");
}

#[cfg(target_os = "macos")]
#[test]
fn transient_readiness_failure_requires_a_real_fresh_same_pid_kernel_observation() {
    let pid = std::process::id();
    let expected = process::read(pid).unwrap();
    let _fault = process::readiness_fault(pid, 2, libc::ESRCH);
    let (name, zombie) = process::readiness_name(pid).unwrap();
    assert_eq!(name, expected.name);
    assert_eq!(zombie, expected.zombie);
    assert!(process::present(pid).unwrap());
}

#[cfg(target_os = "macos")]
#[test]
fn persistent_readiness_failure_never_becomes_a_name_or_a_quiet_sample() {
    let pid = std::process::id();
    let _fault = process::readiness_fault(pid, 3, libc::ESRCH);
    assert_eq!(process::readiness_name(pid).unwrap_err().raw_os_error(), Some(libc::ESRCH));
    assert!(process::present(pid).unwrap());
    let base = Instant::now();
    let mut quiet = window(base);
    for millis in (0..10_000).step_by(500) {
        observe(&mut quiet, base, millis, sample());
    }
    assert!(!observe(&mut quiet, base, 10_000, Err(io::Error::from_raw_os_error(libc::ESRCH))));
    assert!(quiet.since.is_none());
}

/// How many censuses a test runs before another process's exit is its answer.
const ATTEMPTS: usize = 5;

/// Whether `error` is a census refusal of a system PID other than `ours`. The
/// readiness census covers every process on the machine, so another one's exit
/// can outlast the census's budget; a test retries only that.
fn foreign_refusal(error: &str, ours: &[u32]) -> bool {
    error.contains("cannot observe system PID ")
        && !ours.iter().any(|pid| error.contains(&format!("cannot observe system PID {pid}: ")))
}

/// Runs `census` until its result is not another process's refusal, at most
/// `ATTEMPTS` times; the last result stands.
fn retry_foreign_exits<T>(
    ours: &[u32],
    mut census: impl FnMut() -> io::Result<T>,
) -> io::Result<T> {
    let mut attempts = 0;
    loop {
        attempts += 1;
        match census() {
            Err(error) if attempts < ATTEMPTS && foreign_refusal(&error.to_string(), ours) => {}
            result => return result,
        }
    }
}

/// A live process this test owns until it drops.
#[cfg(all(target_os = "macos", target_pointer_width = "64"))]
struct Owned(std::process::Child);

#[cfg(all(target_os = "macos", target_pointer_width = "64"))]
impl Owned {
    fn cat() -> Self {
        Self(
            std::process::Command::new("/bin/cat")
                .stdin(std::process::Stdio::piped())
                .stdout(std::process::Stdio::null())
                .spawn()
                .unwrap(),
        )
    }
}

#[cfg(all(target_os = "macos", target_pointer_width = "64"))]
impl Drop for Owned {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}

/// Trust (LAND-GATE-EW1-FOLLOWUP-REVIEW-4 (12)): the readiness census meets a
/// PID whose name read fails while Darwin reports it exiting, then a zombie:
/// it waits and skips it, where `writer_gone` alone failed the sample.
#[cfg(all(target_os = "macos", target_pointer_width = "64"))]
#[test]
fn readiness_census_waits_out_an_exit_and_skips_only_its_zombie() {
    let child = Owned::cat();
    let pid = child.0.id();
    retry_foreign_exits(&[pid], || {
        let _name = process::readiness_fault(pid, 3, libc::ESRCH);
        let _exiting = process::exiting_fault(pid, Some(3));
        compiler_processes()
    })
    .unwrap();
    {
        // A refusal that is not an exit still fails the sample.
        let error = retry_foreign_exits(&[pid], || {
            let _name = process::readiness_fault(pid, 3, libc::ESRCH);
            compiler_processes()
        })
        .unwrap_err()
        .to_string();
        assert!(error.contains(&format!("cannot observe system PID {pid}: ")), "{error}");
        assert!(error.contains(&io::Error::from_raw_os_error(libc::ESRCH).to_string()), "{error}");
    }
}

/// Trust (LAND-GATE-EW1-FOLLOWUP-REVIEW-4 (12)): the readiness census spends one
/// exit wait across all its PIDs, and that budget leaves a waited sample inside
/// its time bound. Two PIDs' name reads fail while Darwin reports each exiting
/// for 300 ms, then a zombie. The budget (EXIT_SETTLE) covers the first exit
/// but not the second, which fails the sample; a budget per PID skips both.
#[cfg(all(target_os = "macos", target_pointer_width = "64"))]
#[test]
fn readiness_census_spends_one_exit_wait_under_its_sample_bound() {
    const SPAN: Duration = Duration::from_millis(300);
    const {
        assert!(EXIT_SETTLE.as_nanos() < MAX_SAMPLE.as_nanos());
        assert!(SPAN.as_nanos() < EXIT_SETTLE.as_nanos());
        assert!(2 * SPAN.as_nanos() > EXIT_SETTLE.as_nanos());
    }
    let children = [Owned::cat(), Owned::cat()];
    let pids = children.each_ref().map(|child| child.0.id());
    // A budget per PID would wait out both exits and succeed, so the error
    // alone refutes it; the wall clock bounds only a hang, and the const block
    // above keeps the budget inside the sample bound.
    let mut attempts = 0;
    let (error, elapsed) = loop {
        attempts += 1;
        let (sender, receiver) = std::sync::mpsc::channel();
        std::thread::spawn(move || {
            let _faults = pids.map(|pid| {
                (process::readiness_fault(pid, 3, libc::ESRCH), process::exiting_for(pid, SPAN))
            });
            let started = Instant::now();
            let result = compiler_processes().map_err(|error| error.to_string());
            let _ = sender.send((result, started.elapsed()));
        });
        let (result, elapsed) =
            receiver.recv_timeout(Duration::from_secs(60)).expect("the census hung");
        let error = result.expect_err("the second exit outlasts the census's budget");
        if !foreign_refusal(&error, &pids) || attempts == ATTEMPTS {
            break (error, elapsed);
        }
    };
    assert!(
        pids.iter().any(|pid| error.contains(&format!("cannot observe system PID {pid}: "))),
        "{error}"
    );
    assert!(elapsed >= EXIT_SETTLE, "it spent its budget: {elapsed:?}");
}
