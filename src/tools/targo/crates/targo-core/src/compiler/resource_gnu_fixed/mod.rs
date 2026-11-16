//! Transfer actual inherited supplementary credits into a restricted server.
//! The executing root's implicit credit remains separate. No CPU, SDK or Host
//! authority follows from this transport; the fixed caller retains its claim.

use std::io;
use std::sync::{Arc, Mutex};

use jobserver::{Acquired, HelperThread};
use jobserver_utils::Jobserver;

use super::resource_fifo::PrivateFifo;

struct Ledger {
    original: Vec<Acquired>,
    refunds: Vec<Acquired>,
    closed: bool,
    helper_closed: bool,
    burned: bool,
    retired: bool,
    error: Option<String>,
}

struct Shared {
    fifo: PrivateFifo,
    ledger: Mutex<Ledger>,
    // Production passes the SAME original fixed-claim Arc. Unknown Drop must
    // retain its actual resources together with the outstanding GNU guards.
    _custody: Arc<dyn Send + Sync>,
}

pub(super) struct FixedGnuBridge {
    shared: Arc<Shared>,
    helper: Option<HelperThread>,
}

/// Trust: a direct target's same-original scheduling and physical custody.
/// This owner is retired explicitly after the target's actual owning wait;
/// supervisor process exit must never substitute for returning GNU guards.
pub(crate) struct FixedTargetJobserver {
    bridge: FixedGnuBridge,
    claim: Arc<trust_build_tree::admission::InheritedFixedClaim>,
}

impl FixedTargetJobserver {
    pub(super) fn new(
        inherited: &Jobserver,
        ceiling: u32,
        claim: Arc<trust_build_tree::admission::InheritedFixedClaim>,
    ) -> anyhow::Result<Self> {
        claim.check_budget(std::num::NonZeroU32::new(ceiling).ok_or_else(|| {
            io::Error::new(io::ErrorKind::InvalidInput, "fixed target ceiling is zero")
        })?)?;
        let bridge = FixedGnuBridge::new(inherited, ceiling, claim.clone())?;
        Ok(Self { bridge, claim })
    }

    pub(crate) fn jobserver(&self) -> Jobserver {
        self.bridge.jobserver()
    }

    pub(crate) fn retire(&mut self) -> anyhow::Result<()> {
        self.claim.check_current()?;
        anyhow::ensure!(
            self.bridge.try_retire()?,
            "fixed target GNU credits remain outstanding after the target's owning wait"
        );
        self.bridge.check()?;
        self.claim.check_current()?;
        Ok(())
    }
}

impl FixedGnuBridge {
    pub(super) fn new(
        inherited: &Jobserver,
        ceiling: u32,
        custody: Arc<dyn Send + Sync>,
    ) -> anyhow::Result<Self> {
        anyhow::ensure!(
            ceiling > 0 && ceiling <= 65_536,
            "invalid fixed GNU ceiling"
        );
        let mut fifo = PrivateFifo::unseeded(ceiling)?;
        fifo.jobserver.propagate_make_flags();
        let shared = Arc::new(Shared {
            fifo,
            ledger: Mutex::new(Ledger {
                original: Vec::new(),
                refunds: Vec::new(),
                closed: false,
                helper_closed: ceiling == 1,
                burned: false,
                retired: false,
                error: None,
            }),
            _custody: custody,
        });
        let helper = if ceiling > 1 {
            let state = shared.clone();
            let helper = inherited
                .client()
                .clone()
                .into_helper_thread(move |result| {
                    let mut ledger = state.ledger.lock().unwrap_or_else(|e| e.into_inner());
                    match result {
                        Ok(original) if ledger.closed || ledger.error.is_some() => {
                            // No restricted byte was issued. Report failure
                            // and preserve its actual guard if refund fails.
                            drop(ledger);
                            refund(&state, original);
                        }
                        Ok(original) => {
                            // Retain the actual original BEFORE exposing its one
                            // restricted byte. Never infer funding from a count.
                            ledger.original.push(original);
                            if let Err(error) = state.fifo.jobserver.client().release_raw() {
                                let unissued =
                                    ledger.original.pop().expect("just retained original");
                                ledger.error = Some(error.to_string());
                                drop(ledger);
                                refund(&state, unissued);
                            }
                        }
                        Err(error) => ledger.error = Some(error.to_string()),
                    }
                })?;
            for _ in 1..ceiling {
                helper.request_token();
            }
            Some(helper)
        } else {
            None
        };
        Ok(Self { shared, helper })
    }

    pub(super) fn jobserver(&self) -> Jobserver {
        self.shared.fifo.jobserver.clone()
    }

    pub(super) fn check(&self) -> anyhow::Result<()> {
        let ledger = self.shared.ledger.lock().unwrap_or_else(|e| e.into_inner());
        match &ledger.error {
            Some(error) => anyhow::bail!("inherited GNU credit transfer failed: {error}"),
            None => Ok(()),
        }
    }

    /// Permanently stop issuance, then retire only after acquiring EVERY
    /// actual restricted byte. Future readers cannot acquire burned credits.
    /// Pending retirement preserves all originals and restores partial reads.
    pub(super) fn try_retire(&mut self) -> io::Result<bool> {
        {
            let mut ledger = self.shared.ledger.lock().unwrap_or_else(|e| e.into_inner());
            if ledger.retired {
                return Ok(true);
            }
            ledger.closed = true;
        }
        // The inherited helper can be blocked on an anonymous pipe. Its
        // existing interruption/join path never changes shared O_NONBLOCK.
        // Do not hold the callback's ledger mutex while joining it.
        if let Some(helper) = self.helper.take() {
            let stopped = helper.shutdown();
            let mut ledger = self.shared.ledger.lock().unwrap_or_else(|e| e.into_inner());
            ledger.helper_closed = stopped.is_ok();
            if let Err(error) = stopped {
                ledger.error.get_or_insert_with(|| error.to_string());
                return Err(error);
            }
        }
        let mut ledger = self.shared.ledger.lock().unwrap_or_else(|e| e.into_inner());
        if !ledger.helper_closed {
            return Err(io::Error::other(
                "original GNU helper retirement remains unknown",
            ));
        }
        if !ledger.burned {
            let mut returned = Vec::with_capacity(ledger.original.len());
            for _ in 0..ledger.original.len() {
                let Some(token) = self.shared.fifo.jobserver.client().try_acquire()? else {
                    return Ok(false);
                };
                returned.push(token);
            }
            if self.shared.fifo.jobserver.client().available()? != 0 {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "restricted GNU transport contains an unfunded credit",
                ));
            }
            // Burn only actual restricted bytes. No future reader can borrow
            // them, including through a surviving clone of this local client.
            for token in returned {
                token.drop_without_releasing();
            }
            ledger.burned = true;
        }
        // A destructor's best-effort write is not positive refund evidence.
        // Failure retains each still-armed original for an explicit retry.
        let refunds = std::mem::take(&mut ledger.refunds);
        ledger.original.extend(refunds);
        while let Some(original) = ledger.original.pop() {
            if let Err((original, error)) = original.return_to_server() {
                ledger.original.push(original);
                return Err(error);
            }
        }
        ledger.retired = true;
        ledger.original.clear();
        ledger.refunds.clear();
        Ok(true)
    }
}

fn refund(state: &Shared, original: Acquired) {
    if let Err((original, error)) = original.return_to_server() {
        let mut ledger = state.ledger.lock().unwrap_or_else(|e| e.into_inner());
        ledger.error.get_or_insert_with(|| error.to_string());
        ledger.refunds.push(original);
    }
}

impl Drop for FixedGnuBridge {
    fn drop(&mut self) {
        if !matches!(self.try_retire(), Ok(true)) {
            // Preserve original guards, FIFO namespace and actual fixed claim
            // when a restricted credit is missing. No unknown exit refunds it.
            std::mem::forget(self.shared.clone());
        }
    }
}

#[cfg(test)]
mod tests;
