use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Duration;

use super::*;

const SYS: &str = r#"{"schema":1,"kind":"sys.overview","as_of":{"state":"fresh","age_ms":100,"window_ms":1000},"machine":{"cpus":28},"global":{"cpu_mc":20000,"mem_available_bytes":64000,"mem_available_basis":"free_plus_reclaimable_cache","mem_pressure":"normal","thermal":"nominal"}}"#;

fn fixture(body: &str) -> (tempfile::TempDir, PathBuf) {
    let dir = crate::tests::private_tempdir();
    let program = dir.path().join("probe");
    crate::tests::private_file(&program, format!("#!/bin/sh\n{body}\n"));
    fs::set_permissions(&program, fs::Permissions::from_mode(0o700)).unwrap();
    (dir, program)
}

/// Probe time that moves only when the test stores into it. A probe under a
/// still clock ends by its own output or bound, or by the test's hang detector.
fn probe_clock() -> (Arc<AtomicU64>, impl Fn() -> Duration + Send + 'static) {
    let millis = Arc::new(AtomicU64::new(0));
    let read = Arc::clone(&millis);
    (millis, move || Duration::from_millis(read.load(Ordering::SeqCst)))
}

fn wait_for<T>(label: &str, mut read: impl FnMut() -> Option<T>) -> T {
    let start = Instant::now();
    loop {
        if let Some(value) = read() {
            return value;
        }
        assert!(start.elapsed() < Duration::from_secs(60), "test hang detector: {label}");
        thread::sleep(Duration::from_millis(5));
    }
}

fn good_body() -> String {
    format!(
        "printf x >> \"$0.calls\"\nif [ -f \"$0.bad\" ]; then printf bad; exit 0; fi\ncase \"$1\" in\nctl) printf '%s\\n' '{SYS}' ;;\npkg) printf '%s\\n' '{{\"available\":32000}}' ;;\n*) exit 3 ;;\nesac"
    )
}

#[test]
fn successful_round_preserves_cache_age_and_does_not_probe_on_reads() {
    // Each monitor round spawns a probe child, which holds a copy of every
    // descriptor of this process, other tests' leases included, until its
    // exec. Hold the crate's kernel fixture for the monitor's whole life.
    let _fixture = crate::tests::kernel_fixture();
    let (_dir, program) = fixture(&good_body());
    let (still, probe_time) = probe_clock();
    // Probe time already reads 10 s, past the 2 s timeout, when this probe
    // starts. A probe's time counts from its own start, so it still answers.
    still.store(10_000, Ordering::SeqCst);
    let monitor = Monitor::spawn_with(
        program.clone(),
        Duration::from_secs(60),
        Duration::from_secs(2),
        probe_time,
    )
    .unwrap();
    let first = wait_for("first observation", || monitor.latest());
    assert_eq!(first.1, 32000);
    let again = monitor.latest().unwrap();
    assert_eq!(format!("{:?}", first.0), format!("{:?}", again.0));
    assert_eq!(fs::read(program.with_extension("calls")).unwrap(), b"xx");
    assert_eq!(
        again.0.admission_limit(
            Instant::now() + Duration::from_secs(4),
            1,
            again.1,
            std::num::NonZeroU64::new(1000).unwrap(),
            0
        ),
        0
    );
}

#[test]
fn a_failed_round_clears_the_previous_observation() {
    let _fixture = crate::tests::kernel_fixture();
    let (_dir, program) = fixture(&good_body());
    let (_still, probe_time) = probe_clock();
    let monitor = Monitor::spawn_with(
        program.clone(),
        Duration::from_millis(20),
        Duration::from_secs(2),
        probe_time,
    )
    .unwrap();
    wait_for("first observation", || monitor.latest());
    crate::tests::private_file(&program.with_extension("bad"), b"bad");
    wait_for("malformed observation", || monitor.unavailable());
    assert!(monitor.latest().is_none());
}

fn pid(program: &Path) -> u32 {
    wait_for("probe pid", || fs::read_to_string(program.with_extension("pid")).ok()?.parse().ok())
}

fn assert_reaped(pid: u32) {
    // SAFETY: signal zero only observes whether the fixture's recorded process exists.
    assert_eq!(unsafe { libc::kill(pid as libc::pid_t, 0) }, -1);
    assert_eq!(io::Error::last_os_error().raw_os_error(), Some(libc::ESRCH));
}

#[test]
fn timeout_reaps_only_the_owned_probe() {
    let _fixture = crate::tests::kernel_fixture();
    let (_dir, program) = fixture("printf '%s' \"$$\" > \"$0.pid\"\nexec /bin/sleep 60");
    let (now, probe_time) = probe_clock();
    let monitor = Monitor::spawn_with(
        program.clone(),
        Duration::from_secs(60),
        Duration::from_millis(1_000),
        probe_time,
    )
    .unwrap();
    // However slowly its shell starts, the probe reports itself running before
    // its time runs out: that time moves only here.
    let child = pid(&program);
    now.store(1_000, Ordering::SeqCst);
    assert!(wait_for("probe timeout", || monitor.unavailable()).contains("timed out"));
    assert!(monitor.latest().is_none());
    assert_reaped(child);
}

#[test]
fn monotonic_probe_time_ends_a_silent_probe() {
    let _fixture = crate::tests::kernel_fixture();
    // However late this probe starts, it has said nothing when its time ends.
    let (_dir, program) = fixture("exec /bin/sleep 60");
    let monitor = Monitor::spawn(program, Duration::from_secs(60), Duration::from_secs(1)).unwrap();
    assert!(wait_for("probe timeout", || monitor.unavailable()).contains("timed out"));
    assert!(monitor.latest().is_none());
}

#[test]
fn cancellation_interrupts_a_probe_and_reaps_it() {
    let _fixture = crate::tests::kernel_fixture();
    let (_dir, program) = fixture("printf '%s' \"$$\" > \"$0.pid\"\nexec /bin/sleep 120");
    let monitor =
        Monitor::spawn(program.clone(), Duration::from_secs(120), Duration::from_secs(120))
            .unwrap();
    let child = pid(&program);
    let (done, receiver) = std::sync::mpsc::channel();
    thread::spawn(move || {
        drop(monitor);
        done.send(()).unwrap();
    });
    receiver.recv_timeout(Duration::from_secs(60)).expect("cancellation hang detector");
    assert_reaped(child);
}

#[test]
fn output_is_bounded_and_invalid_configuration_is_refused() {
    let _fixture = crate::tests::kernel_fixture();
    let (_dir, program) = fixture("while :; do printf '%1024s' x; done");
    let (_still, probe_time) = probe_clock();
    let monitor = Monitor::spawn_with(
        program.clone(),
        Duration::from_secs(60),
        Duration::from_secs(2),
        probe_time,
    )
    .unwrap();
    assert!(wait_for("output limit", || monitor.unavailable()).contains("size bound"));
    assert!(monitor.latest().is_none());
    assert!(Monitor::spawn(program, Duration::ZERO, Duration::from_secs(1)).is_err());
    assert!(
        Monitor::spawn("relative".into(), Duration::from_secs(1), Duration::from_secs(1)).is_err()
    );
}
