//! GNU-compatible transport for one already-admitted external phase.

use std::io;

use jobserver_utils::Jobserver;

/// The external phase already owns its implicit global CPU credit. An empty
/// legacy pipe exposes ZERO additional credits and works with old GNU make;
/// a named FIFO would be misread as numeric --jobserver-fds by GNU make3.81.
pub(super) fn jobserver() -> io::Result<Jobserver> {
    let mut server = Jobserver::new(0)?;
    server.enable_descendant_handoff()?;
    Ok(server)
}

#[cfg(test)]
mod tests;
