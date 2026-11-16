// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Monitor the actual custodian's sole-writer pipe independently of GUI life.
use std::io;
use std::os::fd::{AsRawFd, OwnedFd};
use std::sync::Arc;
use std::sync::atomic::{AtomicU8, Ordering};
use std::thread::{self, JoinHandle};

/// No target/process identity is inferred from this pipe. Its owner must stop
/// managed work on loss of the authenticated memory supervisor.
pub struct HostLifeline {
    state: Arc<AtomicU8>,
    thread: Option<JoinHandle<()>>,
}
impl HostLifeline {
    /// `lost` runs at most once after an atomic loss commitment. Dropping the
    /// watch first prevents that commitment; it cannot revoke an existing one.
    /// Pipe must be the authenticated read-only descriptor received by Client.
    pub fn spawn(fd: OwnedFd, lost: impl FnOnce() + Send + 'static) -> io::Result<Self> {
        let state = Arc::new(AtomicU8::new(0));
        let worker = state.clone();
        let thread =
            thread::Builder::new().name("trust-custodian-lifeline".into()).spawn(move || {
                while worker.load(Ordering::Acquire) == 0 {
                    let mut event =
                        libc::pollfd { fd: fd.as_raw_fd(), events: libc::POLLIN, revents: 0 };
                    // SAFETY: one held live read-only pipe, bounded cancellation poll.
                    let result = unsafe { libc::poll(&mut event, 1, 100) };
                    if result < 0 && io::Error::last_os_error().kind() == io::ErrorKind::Interrupted
                    {
                        continue;
                    }
                    // The actual host never writes bytes. HUP/ERR/invalid/readable
                    // all mean loss or protocol failure; no potentially blocking
                    // read can race another holder of the same read description.
                    if result != 0 {
                        if worker
                            .compare_exchange(0, 2, Ordering::AcqRel, Ordering::Acquire)
                            .is_ok()
                        {
                            lost();
                        }
                        return;
                    }
                }
            })?;
        Ok(Self { state, thread: Some(thread) })
    }
}
impl Drop for HostLifeline {
    fn drop(&mut self) {
        let _ = self.state.compare_exchange(0, 1, Ordering::AcqRel, Ordering::Acquire);
        if let Some(thread) = self.thread.take() {
            let _ = thread.join();
        }
    }
}

#[cfg(test)]
mod tests {
    use std::sync::mpsc;
    use std::time::Duration;

    use super::*;
    #[test]
    fn actual_host_pipe_loss_is_reported_once_and_explicit_watch_drop_is_cancelled() {
        let (reader, writer) = std::io::pipe().unwrap();
        let (send, receive) = mpsc::channel();
        let watch = HostLifeline::spawn(reader.into(), move || {
            send.send(()).unwrap();
        })
        .unwrap();
        drop(writer);
        receive.recv_timeout(Duration::from_secs(2)).unwrap();
        drop(watch);
        assert!(matches!(receive.try_recv(), Err(mpsc::TryRecvError::Disconnected)));
        let (reader, _writer) = std::io::pipe().unwrap();
        let (send, receive) = mpsc::channel();
        drop(
            HostLifeline::spawn(reader.into(), move || {
                send.send(()).unwrap();
            })
            .unwrap(),
        );
        assert!(matches!(
            receive.recv_timeout(Duration::from_secs(2)),
            Err(mpsc::RecvTimeoutError::Disconnected)
        ));
    }
}
