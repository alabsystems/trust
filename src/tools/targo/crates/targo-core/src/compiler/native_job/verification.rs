//! Original compile-command predecessor for general native verification.
//! Only the maintained queue's actual materialization callback can populate
//! this recorder. An empty recorder, failed command or saved command DATA
//! cannot construct a verification command, session or favorable proof result.
use crate::compiler::qualification_command::{FailedCommand, Observer, OriginalUnitCommand};
use crate::util::CargoResult;
use anyhow::Context as _;
use std::sync::{Arc, Mutex};

enum Recorded {
    Completed(Arc<OriginalUnitCommand>),
    Failed(Arc<FailedCommand>),
}
#[derive(Default)]
struct State {
    original: Option<Recorded>,
    duplicate: Option<Recorded>,
    failed: bool,
}

/// Custody of one actual selected compiler outcome, not proof authority.
/// Keep the same recorder on a failed Attempt as well as a retained Artifact.
pub(crate) struct Recorder(Mutex<State>);
impl Recorder {
    pub(crate) fn new() -> Arc<Self> {
        Arc::new(Self(Mutex::new(State::default())))
    }
    fn record(&self, outcome: Recorded) -> CargoResult<()> {
        let mut state = match self.0.lock() {
            Ok(state) => state,
            Err(_) => {
                // Poison is an unavailable recorder, never permission to
                // dispose this callback's actual original input capsule.
                // Keep it whole without restoring a usable outcome or lock.
                std::mem::forget(outcome);
                anyhow::bail!("native original verification command recorder is poisoned");
            }
        };
        if state.original.is_some() {
            state.failed = true;
            if state.duplicate.is_none() {
                state.duplicate = Some(outcome);
            } else {
                // A third callback for a sole selected compile unit is a
                // producer defect. Retain its real owners rather than letting
                // that defect dispose uncertain original input custody.
                std::mem::forget(outcome);
            }
            anyhow::bail!("native selected compiler command completed more than once");
        }
        state.original = Some(outcome);
        Ok(())
    }
    pub(crate) fn original(&self) -> CargoResult<Arc<OriginalUnitCommand>> {
        let command = {
            let state = self.0.lock().map_err(|_| {
                anyhow::anyhow!("native original verification command recorder is poisoned")
            })?;
            anyhow::ensure!(
                !state.failed && state.duplicate.is_none(),
                "native original compiler command has an ambiguous outcome"
            );
            match state.original.as_ref() {
                Some(Recorded::Completed(command)) => command.clone(),
                Some(Recorded::Failed(command)) => {
                    anyhow::bail!("native compiler prerequisite failed: {}", command.reason())
                }
                None => {
                    anyhow::bail!("native selected compiler omitted its original command owner")
                }
            }
        };
        // The owner is retained before any fallible post-bookend. A command
        // without an actual native producer is never upgraded from freshness.
        command.validate()?;
        command
            .producer_attempt()
            .context("native verification requires the actual compiler materialization attempt")?;
        Ok(command)
    }
    #[cfg(all(test, target_os = "macos", target_arch = "aarch64"))]
    pub(crate) fn failed(&self) -> Option<Arc<FailedCommand>> {
        let state = self.0.lock().ok()?;
        match state.original.as_ref() {
            Some(Recorded::Failed(command)) => Some(command.clone()),
            _ => None,
        }
    }
}
impl Observer for Recorder {
    fn completed(&self, command: Arc<OriginalUnitCommand>) -> CargoResult<()> {
        self.record(Recorded::Completed(command.clone()))?;
        // Keep the actual returned command even if its current inputs refuse.
        // The queue receives that error, never a recreated success record.
        command.validate()
    }
    fn failed(&self, command: FailedCommand) -> CargoResult<()> {
        self.record(Recorded::Failed(Arc::new(command)))
    }
}

#[cfg(all(test, target_os = "macos", target_arch = "aarch64"))]
mod tests {
    use super::*;
    use crate::compiler::qualification_command::{self, Observation};

    #[test]
    fn failed_actual_command_remains_failed_after_namespace_restoration() {
        let recorder = Recorder::new();
        assert!(recorder.original().is_err());
        let root = tempfile::tempdir().unwrap();
        let (capture, command, file) =
            qualification_command::command_fixture(root.path(), recorder.clone());
        let pending = capture.pending(&command).unwrap();
        let added = file.parent().unwrap().join("new-negative-lookup.rs");
        std::fs::write(&added, b"unadmitted input").unwrap();
        let observed = Observation::finish(
            capture,
            pending,
            Err("actual compiler prerequisite refused".into()),
        );
        observed.notify().unwrap();
        let failed = recorder.failed().expect("retain original failed command");
        assert_eq!(failed.original().get_program(), command.get_program());
        assert!(
            failed
                .reason()
                .contains("actual compiler prerequisite refused")
        );
        assert!(
            failed
                .reason()
                .contains("original command inputs also changed")
        );
        std::fs::remove_file(added).unwrap();
        assert!(
            recorder.original().is_err(),
            "restoring names cannot create materialization"
        );
        assert!(Arc::ptr_eq(&failed, &recorder.failed().unwrap()));
    }

    #[test]
    fn duplicate_native_failure_keeps_both_outcomes_without_creating_a_command() {
        let recorder = Recorder::new();
        for number in 0..2 {
            let root = tempfile::tempdir().unwrap();
            let (capture, command, _) =
                qualification_command::command_fixture(root.path(), recorder.clone());
            let pending = capture.pending(&command).unwrap();
            let observed =
                Observation::finish(capture, pending, Err(format!("actual refusal {number}")));
            if number == 0 {
                observed.notify().unwrap();
            } else {
                assert!(observed.notify().is_err());
            }
            // Keep fixture paths through the actual callback and refused
            // getter. No successful compilation/SDK owner is fabricated.
            assert!(recorder.original().is_err());
        }
        assert!(
            recorder
                .failed()
                .unwrap()
                .reason()
                .contains("actual refusal 0")
        );
        let state = recorder.0.lock().unwrap();
        assert!(state.failed && state.duplicate.is_some());
    }

    #[test]
    fn poisoned_recorder_keeps_actual_incoming_failure_without_restoring_usability() {
        let source = Recorder::new();
        let root = tempfile::tempdir().unwrap();
        let (capture, command, _) =
            qualification_command::command_fixture(root.path(), source.clone());
        let pending = capture.pending(&command).unwrap();
        Observation::finish(capture, pending, Err("actual native input refusal".into()))
            .notify()
            .unwrap();
        let failed = source.failed().unwrap();
        let original = Arc::downgrade(&failed);
        drop(source);

        let poisoned = Recorder::new();
        assert!(
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                let _held = poisoned.0.lock().unwrap();
                panic!("deterministic native recorder poison");
            }))
            .is_err()
        );
        assert!(poisoned.record(Recorded::Failed(failed)).is_err());
        // Actual native source/SDK/output input owners remain in this precise
        // failed capsule after the only caller's strong reference moved away.
        // No successful materialization, functional SDK or Root is fabricated.
        let retained = original
            .upgrade()
            .expect("poison must retain incoming actual custody");
        assert!(retained.reason().contains("actual native input refusal"));
        assert_eq!(retained.original().get_program(), command.get_program());
        assert!(
            poisoned.original().is_err(),
            "poison never restores a usable compiler prerequisite"
        );
        assert!(
            poisoned.failed().is_none(),
            "unavailable recorder is not a decoded failed owner"
        );
    }
}
