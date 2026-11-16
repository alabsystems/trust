//! One original-pool credit requested only for a ready dispatch.
//!
//! Imported GNU pipes cannot be made nonblocking safely on macOS. Reuse the
//! jobserver's interruptible waiter for those transports, without prefetching
//! credits or retaining a request across frontend proof qualification.

use std::io;
use std::sync::{Arc, Mutex};

use jobserver::{Acquired, Client, HelperThread};

#[derive(Default)]
pub struct ReadyTokenAdmission {
    waiter: Option<ReadyWaiter>,
    original: Option<Client>,
}

impl ReadyTokenAdmission {
    pub fn try_acquire(&mut self, client: &Client) -> io::Result<Option<Acquired>> {
        if let Some(original) = &self.original {
            if !original.same_origin(client) {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    "ready GNU admission belongs to another original client",
                ));
            }
        } else {
            self.original = Some(client.clone());
        }
        if let Some(waiter) = self.waiter.as_mut() {
            return waiter.poll();
        }
        match client.try_acquire() {
            Err(error) if error.kind() == io::ErrorKind::Unsupported => {
                let mut waiter = ReadyWaiter::new(client)?;
                let result = waiter.poll();
                self.waiter = Some(waiter);
                result
            }
            result => result,
        }
    }

    pub fn retire_stopped_tests(&mut self, stopped: bool, pending_compiler: bool) {
        if stopped && !pending_compiler {
            self.retire();
        }
    }

    /// Cancel and join the one outstanding acquisition, then return any credit
    /// already delivered. No callback writes into the coordinator event queue.
    pub fn retire(&mut self) {
        drop(self.waiter.take());
    }

    /// Restrict an original retained owner to the real helper join, including
    /// any fetched-but-unpublished guard. This creates no scheduling credit.
    pub fn retire_joined(&mut self) -> io::Result<()> {
        if let Some(mut waiter) = self.waiter.take() {
            if let Some(helper) = waiter.helper.take() {
                helper.shutdown_blocking()?;
            }
            drop(
                waiter
                    .result
                    .lock()
                    .map_err(|_| io::Error::other("ready GNU result poisoned"))?
                    .take(),
            );
        }
        Ok(())
    }
}

struct ReadyWaiter {
    helper: Option<HelperThread>,
    result: Arc<Mutex<Option<io::Result<Acquired>>>>,
    outstanding: bool,
}

impl ReadyWaiter {
    fn new(client: &Client) -> io::Result<Self> {
        let result = Arc::new(Mutex::new(None));
        let delivered = Arc::clone(&result);
        let helper = client.clone().into_helper_thread(move |credit| {
            // Exactly one request is outstanding. This slot never blocks on a
            // full coordinator queue while retire() joins the actual waiter.
            let old = delivered.lock().unwrap().replace(credit);
            assert!(old.is_none(), "ready jobserver credit delivered twice");
        })?;
        Ok(Self { helper: Some(helper), result, outstanding: false })
    }

    fn poll(&mut self) -> io::Result<Option<Acquired>> {
        if let Some(result) = self.result.lock().unwrap().take() {
            self.outstanding = false;
            return result.map(Some);
        }
        if !self.outstanding {
            self.helper.as_ref().expect("live ready waiter").request_token();
            self.outstanding = true;
        }
        Ok(None)
    }
}

impl Drop for ReadyWaiter {
    fn drop(&mut self) {
        // The callback retains its result slot. Join first, then drop a token
        // that raced cancellation, before implicit-credit reuse/qualification.
        if let Some(helper) = self.helper.take()
            && let Err(error) = helper.shutdown_blocking()
        {
            eprintln!("original GNU ready helper did not retire: {error}");
            // End only this process without unwinding or releasing a credit
            // whose helper did not establish its actual owning completion.
            #[cfg(unix)]
            // SAFETY: _exit affects only this process; it accesses no memory
            // or foreign process/descriptor and performs no Rust unwinding.
            unsafe {
                libc::_exit(75)
            }
            #[cfg(not(unix))]
            std::process::exit(75);
        }
        drop(self.result.lock().unwrap().take());
    }
}

#[cfg(all(test, unix))]
mod tests;

#[cfg(all(test, unix))]
#[path = "ready/tests/client_binding_controls.rs"]
mod client_binding_controls;
