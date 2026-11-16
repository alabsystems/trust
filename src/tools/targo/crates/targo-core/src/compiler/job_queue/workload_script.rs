//! Intermediate foreign phases retain the same pending compiler DAG. The
//! original current workers must actually return before image registration.
use std::thread;

pub(super) fn join_current_workers<'s>(
    workers: &mut Vec<thread::ScopedJoinHandle<'s, ()>>,
) -> usize {
    let mut failures = 0;
    for worker in workers.drain(..) {
        failures += usize::from(worker.join().is_err());
    }
    failures
}

#[cfg(any(target_os = "linux", target_os = "macos"))]
use super::*;

#[cfg(any(target_os = "linux", target_os = "macos"))]
pub(super) struct Script {
    unit: Unit,
    entered: bool,
    dispatched: bool,
}
#[cfg(any(target_os = "linux", target_os = "macos"))]
impl Script {
    pub(super) fn waiting(unit: Unit) -> Self {
        Self {
            unit,
            entered: false,
            dispatched: false,
        }
    }
    pub(super) fn permits(&self, node: &QueueNode) -> bool {
        self.entered
            && !self.dispatched
            && matches!(node, QueueNode::Compile(unit) if unit == &self.unit)
    }
    pub(super) fn dispatched(&mut self, unit: &Unit) -> CargoResult<()> {
        anyhow::ensure!(
            self.entered && !self.dispatched && unit == &self.unit,
            "original script phase cannot dispatch another queue unit"
        );
        self.dispatched = true;
        Ok(())
    }
}

#[cfg(any(target_os = "linux", target_os = "macos"))]
impl DrainState<'_> {
    pub(super) fn advance_workload_script<'s>(
        &mut self,
        build_runner: &mut BuildRunner<'_, '_>,
        workers: &mut Vec<thread::ScopedJoinHandle<'s, ()>>,
        admitting: bool,
    ) -> CargoResult<bool> {
        anyhow::ensure!(
            self.active.is_empty(),
            "script transition while current workers remain active"
        );
        let Some(mut script) = self.workload_script.take() else {
            return Ok(false);
        };
        if script.entered && !script.dispatched && admitting {
            self.workload_script = Some(script);
            return Ok(false);
        }
        anyhow::ensure!(
            join_current_workers(workers) == 0,
            "current compiler/script worker panicked before actual ownership retirement"
        );
        let runtime = build_runner
            .resource_runtime
            .as_ref()
            .context("native workload script lost original runtime")?;
        if script.entered {
            // Scope return, not Finish, establishes the local busy/RootContext
            // retirement prerequisite. The SAME host phase checks its native
            // member before returning the SAME escrowed GNU descriptions.
            runtime.finish_workload_build_script()?;
            return Ok(true);
        }
        if !admitting {
            return Ok(true);
        }
        let inputs = self
            .workload_inputs()
            .context("ready native script lost its original workload inputs")?;
        let original = build_runner.capture_workload_build_script(&script.unit, inputs)?;
        runtime.enter_workload_build_script(original)?;
        script.entered = true;
        self.workload_script = Some(script);
        Ok(true)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::{
        Arc,
        atomic::{AtomicBool, Ordering},
        mpsc,
    };
    use std::time::Duration;

    #[test]
    fn finish_observation_never_replaces_current_worker_return_at_either_barrier() {
        let returned = Arc::new(AtomicBool::new(false));
        thread::scope(|scope| {
            let (finished, observed) = mpsc::channel();
            let (release, retirement) = mpsc::channel();
            let actual = returned.clone();
            let worker = scope.spawn(move || {
                finished.send(()).unwrap();
                retirement.recv_timeout(Duration::from_secs(5)).unwrap();
                actual.store(true, Ordering::Release);
            });
            observed.recv_timeout(Duration::from_secs(5)).unwrap();
            assert!(!returned.load(Ordering::Acquire));
            let releaser = scope.spawn(move || release.send(()).unwrap());
            let mut originals = vec![worker];
            assert_eq!(join_current_workers(&mut originals), 0);
            assert!(originals.is_empty() && returned.load(Ordering::Acquire));
            releaser.join().unwrap();
        });
    }

    #[test]
    fn panicked_current_worker_does_not_skip_joining_other_original_workers() {
        let returned = Arc::new(AtomicBool::new(false));
        thread::scope(|scope| {
            let actual = returned.clone();
            let mut originals = vec![
                scope.spawn(|| panic!("controlled original worker panic")),
                scope.spawn(|| panic!("second controlled original worker panic")),
                scope.spawn(move || actual.store(true, Ordering::Release)),
            ];
            assert_eq!(join_current_workers(&mut originals), 2);
            assert!(originals.is_empty() && returned.load(Ordering::Acquire));
        });
    }
}
