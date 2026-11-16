//! Withhold actual idle credits from one original GNU server.
//!
//! This is scheduling custody, never machine admission. The machine owner must
//! retain backing until acquisition succeeds, and reacquire backing before an
//! explicit return. Drop burns the withheld bytes instead of refunding capacity
//! which may no longer be funded. An unsupported nonblocking transport refuses;
//! it must not be repaired by changing shared descriptor flags.

use std::io;

use jobserver::{Acquired, Client};

pub struct IdleTokenEscrow {
    original: Client,
    tokens: Vec<Acquired>,
    maximum: usize,
}

impl IdleTokenEscrow {
    /// Reserve metadata before acquiring any credit. `maximum` restricts this
    /// escrow; it neither creates tokens nor proves any machine grant.
    pub fn new(original: &crate::Jobserver, maximum: usize) -> io::Result<Self> {
        let mut tokens = Vec::new();
        tokens.try_reserve_exact(maximum).map_err(io::Error::other)?;
        Ok(Self { original: original.client().clone(), tokens, maximum })
    }

    pub fn held(&self) -> usize {
        self.tokens.len()
    }

    /// Acquire only bytes actually available now. Partial acquisition remains
    /// in escrow on Pending/error, with machine backing still caller-owned.
    pub fn try_withhold(&mut self, total: usize) -> io::Result<bool> {
        if total > self.maximum {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "escrow exceeds reserved metadata",
            ));
        }
        while self.tokens.len() < total {
            let Some(token) = self.original.try_acquire()? else { return Ok(false) };
            self.tokens.push(token);
        }
        Ok(true)
    }

    /// Return actual captured bytes to the SAME server, only after the caller
    /// has retained their genuine backing. A failed write retains the armed
    /// original guard for retry; successful writes are never retried.
    pub fn return_backed(&mut self, total: usize) -> io::Result<()> {
        if total > self.tokens.len() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "escrow refund exceeds actual custody",
            ));
        }
        for _ in 0..total {
            let token = self.tokens.pop().ok_or_else(|| io::Error::other("lost escrow credit"))?;
            if let Err((token, error)) = token.return_to_server() {
                self.tokens.push(token);
                return Err(error);
            }
        }
        Ok(())
    }
}

impl Drop for IdleTokenEscrow {
    fn drop(&mut self) {
        for token in self.tokens.drain(..) {
            token.drop_without_releasing();
        }
    }
}
