//! Restrict a borrowed implicit root when its inherited pipe cannot be polled.

use std::io;
use std::sync::Arc;

use anyhow::Context as _;
use jobserver_utils::Jobserver;
use trust_build_cpu::Lease;

use super::resource_fifo::PrivateFifo;

enum Transport {
    Inherited,
    BorrowedSerial,
}

fn transport(probe: io::Result<()>, borrowed: Option<&Lease>) -> io::Result<Transport> {
    match probe {
        Ok(()) => Ok(Transport::Inherited),
        Err(error) if error.kind() == io::ErrorKind::Unsupported && borrowed.is_some() => {
            Ok(Transport::BorrowedSerial)
        }
        Err(error) => Err(error),
    }
}

/// Borrow only the already-validated implicit global lease. Unsupported
/// anonymous pipes cannot be modified while other processes use them; an
/// empty private FIFO restricts this nested context to ONE existing credit.
/// No other inherited error or unbacked context can create a replacement.
pub(super) fn scheduler(
    inherited: &Jobserver,
    borrowed: Option<&Lease>,
) -> anyhow::Result<(Jobserver, Option<Arc<PrivateFifo>>)> {
    match transport(inherited.client().try_acquire().map(drop), borrowed)
        .context("native CPU admission needs a nonblocking inherited jobserver")?
    {
        Transport::Inherited => Ok((inherited.clone(), None)),
        Transport::BorrowedSerial => {
            let fifo = Arc::new(PrivateFifo::new(1)?);
            Ok((fifo.jobserver.clone(), Some(fifo)))
        }
    }
}

#[cfg(test)]
mod tests;
