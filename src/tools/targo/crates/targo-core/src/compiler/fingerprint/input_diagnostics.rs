//! Bounded, transient explanations for an unavailable input snapshot.
//!
//! These tracing events never enter a fingerprint, persisted snapshot or the
//! existing input-work wire protocol. They do not change an admission decision.

use std::fmt::{self, Write as _};
use std::io;

use super::{InputWorkPhase, UnitIndex};

const ERROR_BYTES: usize = 512;

struct ErrorSummary<'a>(&'a anyhow::Error);

impl fmt::Display for ErrorSummary<'_> {
    fn fmt(&self, output: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut bounded = Bounded {
            output,
            remaining: ERROR_BYTES - 3,
            truncated: false,
        };
        let result = write!(&mut bounded, "{:#}", self.0);
        if bounded.truncated {
            bounded.output.write_str("...")
        } else {
            result
        }
    }
}

struct Bounded<'a, 'b> {
    output: &'a mut fmt::Formatter<'b>,
    remaining: usize,
    truncated: bool,
}

impl fmt::Write for Bounded<'_, '_> {
    fn write_str(&mut self, text: &str) -> fmt::Result {
        for character in text.chars().flat_map(char::escape_debug) {
            let bytes = character.len_utf8();
            if bytes > self.remaining {
                self.truncated = true;
                return Err(fmt::Error);
            }
            self.output.write_char(character)?;
            self.remaining -= bytes;
        }
        Ok(())
    }
}

pub(super) fn observation_failed(
    index: UnitIndex,
    phase: InputWorkPhase,
    capture: Option<u64>,
    error: &anyhow::Error,
) {
    tracing::debug!(
        target: "targo::compiler::fingerprint::build_script_inputs",
        unit = index.0,
        phase = ?phase,
        capture = ?capture,
        refusal = "observation-error",
        io_kind = ?error.downcast_ref::<io::Error>().map(io::Error::kind),
        error = %ErrorSummary(error),
        "build-script input observation unavailable"
    );
}

pub(super) fn window_not_covered(
    index: UnitIndex,
    phase: InputWorkPhase,
    available_windows: usize,
) {
    tracing::debug!(
        target: "targo::compiler::fingerprint::build_script_inputs",
        unit = index.0,
        phase = ?phase,
        refusal = "execution-window-not-covered",
        available_windows,
        "build-script input snapshot unavailable"
    );
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::RefCell;
    use std::fs;
    use std::path::{Path, PathBuf};
    use std::sync::{Arc, Mutex, OnceLock};

    use super::super::{
        InputWorkContext, InputWorkReporter, LocalFingerprint, build_script_inputs,
        content_input_snapshot,
    };
    use crate::util::log_message::{InputWorkOutcome, LogMessage};

    #[derive(Clone)]
    struct Writer(Arc<Mutex<Vec<u8>>>);

    impl io::Write for Writer {
        fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
            self.0.lock().unwrap().write(bytes)
        }

        fn flush(&mut self) -> io::Result<()> {
            Ok(())
        }
    }

    fn events<T>(body: impl FnOnce() -> T) -> (T, String) {
        let output = Arc::new(Mutex::new(Vec::new()));
        let writer = Writer(Arc::clone(&output));
        let subscriber = tracing_subscriber::fmt()
            .without_time()
            .with_ansi(false)
            .with_max_level(tracing::Level::DEBUG)
            .with_writer(move || writer.clone())
            .finish();
        let result = tracing::subscriber::with_default(subscriber, body);
        let text = String::from_utf8(output.lock().unwrap().clone()).unwrap();
        (result, text)
    }

    fn world<T>(body: impl FnOnce(&Path) -> T) -> T {
        static TURN: Mutex<()> = Mutex::new(());
        static WORLDS: OnceLock<PathBuf> = OnceLock::new();
        let _turn = TURN.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
        let worlds = WORLDS.get_or_init(|| {
            let executable = std::env::current_exe().unwrap();
            let worlds = executable
                .parent()
                .unwrap()
                .parent()
                .unwrap()
                .join("snapshot-diagnostic-worlds");
            fs::create_dir_all(&worlds).unwrap();
            worlds.canonicalize().unwrap()
        });
        // Keep our worlds out of the shared temporary directory and serialize their creation.
        // Observe every real ancestor stamp; any remaining interference fails this one attempt.
        // No retry, changed-stamp waiver or substitute observer can turn a refusal into a pass.
        let world = tempfile::tempdir_in(worlds).unwrap();
        body(&world.path().canonicalize().unwrap())
    }

    #[test]
    fn error_summary_is_bounded_utf8_and_control_safe() {
        let error = anyhow::anyhow!("\0\n\r\t\x1b🦀{}", "é".repeat(10_000));
        let text = ErrorSummary(&error).to_string();
        assert!(text.len() <= ERROR_BYTES);
        assert!(text.ends_with("..."));
        assert!(!text.chars().any(char::is_control));
        assert!(text.contains("\\0\\n\\r\\t\\u{1b}"));
        assert_eq!(ErrorSummary(&anyhow::anyhow!("short")).to_string(), "short");
    }

    #[test]
    fn real_io_failure_is_distinct_from_execution_window_refusal() {
        world(|root| {
            let messages = RefCell::new(Vec::new());
            let emit = |message| messages.borrow_mut().push(message);
            let context = InputWorkContext {
                index: UnitIndex(7),
                capture_ids: None,
            };
            let report = InputWorkReporter {
                context: &context,
                phase: InputWorkPhase::Freshness,
                emit: &emit,
            };
            let (snapshot, diagnostics) = events(|| {
                content_input_snapshot(root, &[PathBuf::from("invalid\0path")], true, None, &report)
            });
            assert!(snapshot.is_none());
            assert!(diagnostics.contains("observation-error"), "{diagnostics}");
            assert!(diagnostics.contains("InvalidInput"), "{diagnostics}");
            assert!(!diagnostics.contains("execution-window-not-covered"));
            assert!(messages.borrow().is_empty());
        });
    }

    #[cfg(unix)]
    #[test]
    fn changed_original_window_stays_uncacheable_with_its_existing_work_pair() {
        world(|root| {
            fs::write(root.join("value"), b"before").unwrap();
            let paths = [PathBuf::from("value")];
            let before = build_script_inputs::window(&root, &paths, true).unwrap();
            fs::write(root.join("value"), b"changed-after-window").unwrap();
            let messages = RefCell::new(Vec::new());
            let emit = |message| messages.borrow_mut().push(message);
            let context = InputWorkContext {
                index: UnitIndex(9),
                capture_ids: Some(Arc::new(portable_atomic::AtomicU64::new(0))),
            };
            let report = InputWorkReporter {
                context: &context,
                phase: InputWorkPhase::Publication,
                emit: &emit,
            };
            let (snapshot, diagnostics) = events(|| {
                content_input_snapshot(root, &paths, true, Some(&[Some(before), None]), &report)
            });
            assert!(snapshot.is_none());
            assert!(
                diagnostics.contains("execution-window-not-covered"),
                "{diagnostics}"
            );
            assert!(diagnostics.contains("available_windows=1"), "{diagnostics}");
            assert!(!diagnostics.contains("observation-error"));
            assert!(matches!(
                messages.borrow().as_slice(),
                [
                    LogMessage::InputWorkStarted {
                        capture: 0,
                        index: UnitIndex(9),
                        phase: InputWorkPhase::Publication
                    },
                    LogMessage::InputWorkFinished {
                        capture: 0,
                        index: UnitIndex(9),
                        phase: InputWorkPhase::Publication,
                        outcome: InputWorkOutcome::Uncacheable,
                        ..
                    }
                ]
            ));
        });
    }

    #[cfg(unix)]
    #[test]
    fn admitted_snapshot_keeps_identical_wire_and_fingerprint_authority() {
        world(|root| {
            fs::write(root.join("value"), b"unchanged").unwrap();
            let paths = [PathBuf::from("value")];
            let expected = build_script_inputs::capture(&root, &paths, true).unwrap();
            let before = build_script_inputs::window(&root, &paths, true).unwrap();
            let context = InputWorkContext {
                index: UnitIndex(11),
                capture_ids: None,
            };
            let report = InputWorkReporter {
                context: &context,
                phase: InputWorkPhase::Publication,
                emit: &|_| panic!("disabled work logger must stay disabled"),
            };
            let (snapshot, diagnostics) = events(|| {
                content_input_snapshot(root, &paths, true, Some(&[Some(before), None]), &report)
            });
            assert!(!diagnostics.contains("refusal="), "{diagnostics}");
            let actual =
                snapshot.expect("an unchanged original window must admit its full observation");
            assert_eq!(actual, expected);
            let local = |snapshot| LocalFingerprint::RerunIfChangedContent {
                output: PathBuf::from("run/stdout"),
                paths: paths.to_vec(),
                snapshot: Some(snapshot),
            };
            let before = local(expected);
            let after = local(actual);
            assert_eq!(
                serde_json::to_value(&before).unwrap(),
                serde_json::to_value(&after).unwrap()
            );
            assert_eq!(
                crate::util::hash_u64(&before),
                crate::util::hash_u64(&after)
            );
        });
    }
}
