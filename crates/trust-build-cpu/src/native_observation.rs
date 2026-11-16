//! One native-process cache backed by the actual independent custodian.
//! No GUI probes, admission-lock RPC or receipt-time freshness reset.
use std::sync::{Arc, Condvar, Mutex};
use std::thread::{self, JoinHandle};
use std::time::{Duration, Instant};

use trust_resource_controller::client::{Client, Delivery, HostLifeline, ReceivedTelemetry};
use trust_resource_controller::{
    Context, ContextQuery, JobBinding, Pressure, Snapshot, TelemetryQuery, Thermal,
};

use crate::{
    Measurements, MemoryPressure, NativeUsage, Observation, ObservationSource, ThermalPressure,
};

#[derive(Default)]
struct State {
    stop: bool,
    latest: Option<(Observation, Option<u64>)>,
    observed: bool,
}
#[derive(Default)]
struct Shared {
    state: Mutex<State>,
    wake: Condvar,
}
/// Cached authenticated host observations for a managed native process.
/// The retained lifeline terminates this process on actual custodian loss.
pub struct NativeHostObservation {
    shared: Arc<Shared>,
    memory: Arc<NativeUsage>,
    thread: Option<JoinHandle<()>>,
    _lifeline: HostLifeline,
}
/// Loss of actual retained-memory supervision cannot leave managed native work
/// running. This is process termination, never debt settlement or target kill.
#[derive(Clone, Copy)]
struct AbortObservation {
    deadline: Instant,
    observe: fn(Instant) -> std::io::Result<()>,
}
fn custodian_lost(observation: Option<AbortObservation>) -> ! {
    if let Some(observation) = observation {
        // The trusted owner may synchronize existing bounded raw prefixes;
        // it must use try-locks and this original deadline, never delivery,
        // callback retries, fresh grants or a renewed wait. Even a caught
        // observer panic/failure cannot skip the existing unconditional exit.
        let deadline = observation.deadline.min(Instant::now() + Duration::from_millis(250));
        let _ = std::panic::catch_unwind(|| (observation.observe)(deadline));
    }
    // SAFETY: terminate only this managed process without application locks
    // or pretending that the host execution debt has been settled.
    unsafe { libc::_exit(75) }
}
fn observation(snapshot: Snapshot, received: Instant) -> std::io::Result<Observation> {
    Observation::from_measurements(Measurements {
        received,
        age: Duration::from_nanos(snapshot.sample_age_ns),
        window: Duration::from_nanos(snapshot.window_ns),
        cpus: snapshot.cpus,
        busy_millicores: snapshot.busy_millicores,
        available_memory: snapshot.available_memory_bytes,
        pressure: match snapshot.pressure {
            Pressure::Unknown => MemoryPressure::Unknown,
            Pressure::Normal => MemoryPressure::Normal,
            Pressure::Warn => MemoryPressure::Warn,
            Pressure::Critical => MemoryPressure::Critical,
        },
        thermal: match snapshot.thermal {
            Thermal::Unknown => ThermalPressure::Unknown,
            Thermal::Nominal => ThermalPressure::Nominal,
            Thermal::Fair => ThermalPressure::Fair,
            Thermal::Serious => ThermalPressure::Serious,
            Thermal::Critical => ThermalPressure::Critical,
        },
    })
}
fn update(shared: &Shared, snapshot: Snapshot, received: Instant, kernel: Option<u64>) {
    let latest = observation(snapshot, received).ok().map(|observation| (observation, kernel));
    if let Ok(mut state) = shared.state.lock() {
        state.observed |= latest.is_some();
        state.latest = latest;
    }
}
fn bounded(
    latest: Option<(Observation, Option<u64>)>,
    current: Option<u64>,
) -> Option<(Observation, u64)> {
    let (observation, captured) = latest?;
    let current = current?;
    Some((observation, captured.map_or(current, |memory| memory.min(current))))
}
impl NativeHostObservation {
    /// Start after authenticated Context and SDK validation, before CPU admission.
    /// Observations are cached without GUI probes or allocation under pool locks.
    pub fn start(
        client: Client,
        binding: JobBinding,
        expected: Context,
        usage: Arc<NativeUsage>,
        initial: ReceivedTelemetry,
    ) -> std::io::Result<Arc<Self>> {
        Self::start_inner(client, binding, expected, usage, initial, None)
    }

    /// Start with a trusted bounded abort observer for the SAME original
    /// execution owner. The observer may synchronize already-owned evidence,
    /// using try-locks against the supplied original deadline; it may not
    /// perform another execution, admission or unbounded application wait.
    /// Observer failure/panic still unconditionally terminates this process.
    /// Ordinary `start` keeps its original immediate no-observer behavior.
    pub fn start_with_abort_observer(
        client: Client,
        binding: JobBinding,
        expected: Context,
        usage: Arc<NativeUsage>,
        initial: ReceivedTelemetry,
        deadline: Instant,
        observe: fn(Instant) -> std::io::Result<()>,
    ) -> std::io::Result<Arc<Self>> {
        if deadline <= Instant::now() {
            return Err(std::io::ErrorKind::TimedOut.into());
        }
        Self::start_inner(
            client,
            binding,
            expected,
            usage,
            initial,
            Some(AbortObservation { deadline, observe }),
        )
    }

    fn start_inner(
        client: Client,
        binding: JobBinding,
        expected: Context,
        usage: Arc<NativeUsage>,
        initial: ReceivedTelemetry,
        termination: Option<AbortObservation>,
    ) -> std::io::Result<Arc<Self>> {
        binding.validate()?;
        if expected.session != binding.session
            || expected.root_attempt != binding.root_attempt
            || initial.reply.context.context != expected
        {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                "native observation context does not match its authenticated job",
            ));
        }
        let shared = Arc::new(Shared::default());
        update(&shared, initial.reply.snapshot, initial.received_at, usage.available_memory());
        let lifeline = HostLifeline::spawn(initial.lifeline, move || custodian_lost(termination))?;
        let worker = shared.clone();
        let memory = usage.clone();
        let thread = thread::Builder::new()
            .name("trust-native-resource-observation".into())
            .spawn(move || {
                loop {
                    let Ok(state) = worker.state.lock() else {
                        return;
                    };
                    let Ok((state, _)) =
                        worker
                            .wake
                            .wait_timeout_while(state, Duration::from_secs(1), |state| !state.stop)
                    else {
                        return;
                    };
                    if state.stop {
                        return;
                    }
                    drop(state);
                    // All native RPC and OS/cache sampling happens outside both
                    // the shared pool transaction and this observation mutex.
                    let result = call_attempt(binding.root_attempt).and_then(|call_attempt| {
                        client
                            .telemetry(
                                &TelemetryQuery {
                                    query: ContextQuery { binding: binding.clone(), call_attempt },
                                },
                                Instant::now() + Duration::from_millis(750),
                            )
                            .map_err(|error| {
                                if error.delivery == Delivery::ContextUnavailable {
                                    custodian_lost(termination);
                                }
                                error.error
                            })
                    });
                    match result {
                        Ok(value) => {
                            if value.reply.context.context != expected {
                                custodian_lost(termination);
                            }
                            update(
                                &worker,
                                value.reply.snapshot,
                                value.received_at,
                                usage.available_memory(),
                            );
                            // Original host identity is pinned across reconnects.
                            // The first authenticated lifeline remains held; this
                            // extra read copy creates no writer or fresh grant.
                        }
                        Err(_) => {
                            if let Ok(mut state) = worker.state.lock() {
                                state.latest = None;
                            }
                        }
                    }
                }
            })?;
        Ok(Arc::new(Self { shared, memory, thread: Some(thread), _lifeline: lifeline }))
    }
}
impl ObservationSource for NativeHostObservation {
    fn latest(&self) -> Option<(Observation, u64)> {
        let latest = self.shared.state.lock().ok()?.latest.clone();
        bounded(latest, self.memory.available_memory())
    }
    fn ever_observed(&self) -> bool {
        self.shared.state.lock().is_ok_and(|state| state.observed)
    }
}
impl Drop for NativeHostObservation {
    fn drop(&mut self) {
        if let Ok(mut state) = self.shared.state.lock() {
            state.stop = true;
            self.shared.wake.notify_all();
        }
        if let Some(thread) = self.thread.take() {
            let _ = thread.join();
        }
    }
}

fn call_attempt(root: [u8; 16]) -> std::io::Result<[u8; 16]> {
    use std::io::Read;
    let mut random = std::fs::File::open("/dev/urandom")?;
    loop {
        let mut value = [0; 16];
        random.read_exact(&mut value)?;
        if value != [0; 16] && value != root {
            return Ok(value);
        }
    }
}

#[cfg(test)]
mod tests {
    use std::num::NonZeroU64;

    use super::*;

    fn record_abort_observer(deadline: Instant) -> std::io::Result<()> {
        assert!(deadline <= Instant::now() + Duration::from_millis(250));
        // The isolated native abort actor owns this fixed output path before
        // native context exists.
        let path = std::env::var_os("TRUST_NATIVE_ABORT_OBSERVER_MARKER").unwrap();
        std::fs::write(path, b"original-bounded-abort-observed\n")?;
        Ok(())
    }

    fn failing_abort_observer(deadline: Instant) -> std::io::Result<()> {
        record_abort_observer(deadline)?;
        Err(std::io::Error::other("controlled abort observer failure"))
    }

    fn panicking_abort_observer(deadline: Instant) -> std::io::Result<()> {
        record_abort_observer(deadline)?;
        panic!("controlled abort observer unwind")
    }

    fn expired_abort_observer(deadline: Instant) -> std::io::Result<()> {
        assert!(deadline < Instant::now(), "original expired deadline was renewed");
        record_abort_observer(deadline)
    }

    // The native actor selects its actual termination case from the
    // environment before native context exists.
    #[test]
    fn native_abort_observation_cannot_replace_termination_on_success_failure_or_panic() {
        const MODE: &str = "TRUST_NATIVE_ABORT_OBSERVER_MODE";
        const MARKER: &str = "TRUST_NATIVE_ABORT_OBSERVER_MARKER";
        if let Ok(mode) = std::env::var(MODE) {
            let original = Instant::now() + Duration::from_secs(5);
            let observation = match mode.as_str() {
                "none" => None,
                "success" => {
                    Some(AbortObservation { deadline: original, observe: record_abort_observer })
                }
                "failure" => {
                    Some(AbortObservation { deadline: original, observe: failing_abort_observer })
                }
                "panic" => {
                    Some(AbortObservation { deadline: original, observe: panicking_abort_observer })
                }
                "expired" => Some(AbortObservation {
                    deadline: Instant::now() - Duration::from_secs(1),
                    observe: expired_abort_observer,
                }),
                _ => panic!("unknown actual abort actor mode"),
            };
            custodian_lost(observation);
        }
        // Each actor child holds a copy of every descriptor of this process,
        // other tests' leases included, until its exec.
        let _fixture = crate::tests::kernel_fixture();
        let directory = crate::tests::private_tempdir();
        let module = module_path!().split_once("::").unwrap().1;
        let exact = format!(
            "{module}::native_abort_observation_cannot_replace_termination_on_success_failure_or_panic"
        );
        for mode in ["none", "success", "failure", "panic", "expired"] {
            let marker = directory.path().join(mode);
            let mut child = std::process::Command::new(std::env::current_exe().unwrap())
                .args(["--exact", &exact])
                .env(MODE, mode)
                .env(MARKER, &marker)
                .stdout(std::process::Stdio::null())
                .stderr(std::process::Stdio::null())
                .spawn()
                .unwrap();
            let deadline = Instant::now() + Duration::from_secs(10);
            let status = loop {
                if let Some(status) = child.try_wait().unwrap() {
                    break status;
                }
                if Instant::now() >= deadline {
                    // SAME unreaped child anchors the PID until its sole wait.
                    let _ = child.kill();
                    let _ = child.wait();
                    panic!("native abort actor failed to terminate: {mode}");
                }
                std::thread::sleep(Duration::from_millis(5));
            };
            assert_eq!(status.code(), Some(75), "{mode}");
            if mode == "none" {
                assert!(!marker.exists(), "ordinary abort has no observer");
            } else {
                assert_eq!(std::fs::read(marker).unwrap(), b"original-bounded-abort-observed\n");
            }
        }
    }

    #[test]
    fn kernel_warmup_keeps_host_receipt_without_admission_or_freshness_fallback() {
        let shared = Shared::default();
        let received = Instant::now();
        let mut snapshot = Snapshot {
            cpus: 8,
            busy_millicores: Some(0),
            available_memory_bytes: Some(100),
            pressure: Pressure::Normal,
            thermal: Thermal::Nominal,
            sample_age_ns: 200_000_000,
            window_ns: 1_000_000_000,
        };
        update(&shared, snapshot, received, None);
        let latest = shared.state.lock().unwrap().latest.clone();
        assert!(bounded(latest.clone(), None).is_none());
        // A valid kernel cache can warm before the next host RPC. Keep the
        // original host receipt rather than losing it for a whole cadence.
        let (observation, memory) = bounded(latest, Some(4)).unwrap();
        assert_eq!(memory, 4);
        let per_worker = NonZeroU64::new(1).unwrap();
        assert_eq!(observation.admission_limit(received, 0, memory, per_worker, 0), 4);
        assert_eq!(
            observation.admission_limit(
                received + Duration::from_secs(4),
                0,
                memory,
                per_worker,
                0
            ),
            0
        );
        update(&shared, snapshot, received, Some(2));
        let latest = shared.state.lock().unwrap().latest.clone();
        assert_eq!(bounded(latest.clone(), Some(4)).unwrap().1, 2);
        assert_eq!(bounded(latest, Some(1)).unwrap().1, 1);
        snapshot.pressure = Pressure::Unknown;
        update(&shared, snapshot, received, Some(4));
        assert!(shared.state.lock().unwrap().latest.is_none());
    }
}
