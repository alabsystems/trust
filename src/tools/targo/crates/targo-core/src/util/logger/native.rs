//! Optional native observer of the SAME compiler log messages. The observer
//! owns its bounded original sink; this adds no child, pool or metric sampler.
use super::*;
use std::sync::Arc;

pub(crate) trait Observer: Send + Sync {
    fn message(&self, run_id: &str, message: &LogMessage) -> std::io::Result<()>;
    /// Synchronize the actual received prefix, including after an earlier
    /// error. Successful flush never repairs missing or partial records.
    fn synchronize(&self) -> std::io::Result<()>;
}

#[derive(Debug)]
pub(crate) struct Failure(String);
impl std::fmt::Display for Failure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "original native compiler report incomplete: {}", self.0)
    }
}
impl std::error::Error for Failure {}
struct State {
    started: u64,
    finished: u64,
    failure: Option<String>,
    closed: bool,
}
pub(super) struct NativeLogger {
    observer: Arc<dyn Observer>,
    state: RefCell<State>,
}
impl NativeLogger {
    pub(super) fn new(observer: Arc<dyn Observer>, run_id: &str) -> Result<Self, Failure> {
        let logger = Self {
            observer,
            state: RefCell::new(State {
                started: 0,
                finished: 0,
                failure: None,
                closed: false,
            }),
        };
        logger.log(
            run_id,
            &LogMessage::InputWorkEnabled {
                version: INPUT_WORK_VERSION,
            },
        );
        if let Some(error) = logger.state.borrow().failure.clone() {
            let _ = logger.observer.synchronize();
            return Err(Failure(error));
        }
        Ok(logger)
    }
    pub(super) fn log(&self, run_id: &str, message: &LogMessage) {
        {
            let mut state = self.state.borrow_mut();
            if state.closed {
                state
                    .failure
                    .get_or_insert("message after actual report closure".into());
                return;
            }
            if state.failure.is_some() {
                return;
            }
            let counter = match message {
                LogMessage::InputWorkStarted { .. } => Some(&mut state.started),
                LogMessage::InputWorkFinished { .. } => Some(&mut state.finished),
                _ => None,
            };
            if let Some(counter) = counter {
                match counter.checked_add(1) {
                    Some(value) => *counter = value,
                    None => {
                        state.failure = Some("input-work count overflow".into());
                        return;
                    }
                }
            }
        }
        // No state/capture lock is retained through the owned sink callback.
        if let Err(error) = self.observer.message(run_id, message) {
            self.state
                .borrow_mut()
                .failure
                .get_or_insert_with(|| error.to_string());
        }
    }
    pub(super) fn finish(&self, run_id: &str) -> Result<(), Failure> {
        let terminal = {
            let mut state = self.state.borrow_mut();
            if state.closed {
                return Err(Failure("report finalized twice".into()));
            }
            state.closed = true;
            state
                .failure
                .is_none()
                .then_some(LogMessage::InputWorkClosed {
                    version: INPUT_WORK_VERSION,
                    started: state.started,
                    finished: state.finished,
                })
        };
        // Synchronize the complete body BEFORE authoring its terminal. On a
        // failed/short original sink, retain its prefix but never emit Closed.
        if let Err(error) = self.observer.synchronize() {
            self.state
                .borrow_mut()
                .failure
                .get_or_insert_with(|| error.to_string());
        }
        let clean = self.state.borrow().failure.is_none();
        if clean
            && let Some(terminal) = terminal
            && let Err(error) = self.observer.message(run_id, &terminal)
        {
            self.state
                .borrow_mut()
                .failure
                .get_or_insert_with(|| error.to_string());
        }
        if let Err(error) = self.observer.synchronize() {
            self.state
                .borrow_mut()
                .failure
                .get_or_insert_with(|| error.to_string());
        }
        match self.state.borrow().failure.clone() {
            Some(error) => Err(Failure(error)),
            None => Ok(()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::{
        Mutex,
        atomic::{AtomicBool, Ordering},
    };
    struct Sink {
        bytes: Mutex<Vec<u8>>,
        limit: usize,
        fail_flush: AtomicBool,
    }
    impl Observer for Sink {
        fn message(&self, run_id: &str, message: &LogMessage) -> std::io::Result<()> {
            struct Bounded<'a>(&'a mut Vec<u8>, usize);
            impl Write for Bounded<'_> {
                fn write(&mut self, bytes: &[u8]) -> std::io::Result<usize> {
                    let keep = bytes.len().min(self.1.saturating_sub(self.0.len()));
                    self.0.extend_from_slice(&bytes[..keep]);
                    if keep == 0 {
                        return Err(std::io::ErrorKind::WriteZero.into());
                    }
                    Ok(keep)
                }
                fn flush(&mut self) -> std::io::Result<()> {
                    Ok(())
                }
            }
            message.write_json_log(
                &mut Bounded(&mut self.bytes.lock().unwrap(), self.limit),
                run_id,
            )
        }
        fn synchronize(&self) -> std::io::Result<()> {
            if self.fail_flush.load(Ordering::Acquire) {
                Err(std::io::ErrorKind::Other.into())
            } else {
                Ok(())
            }
        }
    }
    fn new_sink(limit: usize) -> Arc<Sink> {
        Arc::new(Sink {
            bytes: Mutex::new(Vec::new()),
            limit,
            fail_flush: AtomicBool::new(false),
        })
    }
    #[test]
    fn actual_serialized_messages_close_only_after_the_original_body_synchronizes() {
        let sink = new_sink(64 * 1024);
        let log = NativeLogger::new(sink.clone(), "actual-run").unwrap();
        log.log(
            "actual-run",
            &LogMessage::ExecutionEnabled {
                version: crate::util::log_message::EXECUTION_VERSION,
            },
        );
        log.log(
            "actual-run",
            &LogMessage::CompilerObservationsEnabled {
                version: crate::util::log_message::COMPILER_OBSERVATION_VERSION,
                rusage_requested: true,
            },
        );
        log.finish("actual-run").unwrap();
        let bytes = sink.bytes.lock().unwrap();
        let values = bytes
            .split(|b| *b == b'\n')
            .filter(|b| !b.is_empty())
            .map(|b| serde_json::from_slice::<serde_json::Value>(b).unwrap())
            .collect::<Vec<_>>();
        assert_eq!(values.len(), 4);
        assert!(values.iter().all(|value| value["run_id"] == "actual-run"));
        let text = String::from_utf8_lossy(&bytes);
        assert!(text.contains("compiler-observations-enabled"));
        assert!(text.contains("input-work-closed"));
        drop(bytes);
        assert!(log.finish("actual-run").is_err());
    }
    #[test]
    fn short_original_sink_retains_prefix_without_a_synthetic_terminal_or_retry() {
        let sink = new_sink(170);
        let log = NativeLogger::new(sink.clone(), "actual-run").unwrap();
        log.log(
            "actual-run",
            &LogMessage::CompilerObservationsEnabled {
                version: crate::util::log_message::COMPILER_OBSERVATION_VERSION,
                rusage_requested: true,
            },
        );
        let prefix = sink.bytes.lock().unwrap().clone();
        assert_eq!(prefix.len(), 170);
        assert!(log.finish("actual-run").is_err());
        assert_eq!(*sink.bytes.lock().unwrap(), prefix);
        assert!(!String::from_utf8_lossy(&prefix).contains("input-work-closed"));
        let sink = new_sink(64 * 1024);
        let log = NativeLogger::new(sink.clone(), "actual-run").unwrap();
        sink.fail_flush.store(true, Ordering::Release);
        assert!(log.finish("actual-run").is_err());
        assert!(
            !String::from_utf8_lossy(&sink.bytes.lock().unwrap()).contains("input-work-closed")
        );
    }
}
