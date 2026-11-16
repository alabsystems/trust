//! Trust: command selection DATA from the maintained Bootstrap wrapper. This
//! projection creates no native execution, input ownership or completion.
use std::io;
use std::process::Command;

use crate::utils::exec::OriginalCommandInputs;

/// The actual wrapper's command and otherwise unobservable environment mode.
/// This initial profile supports inherited stdin only. An imported raw Command
/// or opaque explicit Stdio cannot silently acquire different I/O semantics.
pub struct OriginalCommand<'a> {
    command: &'a Command,
    environment_cleared: bool,
}

impl<'a> OriginalCommand<'a> {
    pub(crate) fn capture(command: &'a Command, inputs: OriginalCommandInputs) -> io::Result<Self> {
        let environment_cleared = inputs.environment_cleared.ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::Unsupported,
                "Full command has no actual wrapper environment projection",
            )
        })?;
        if !inputs.inherited_stdin {
            return Err(io::Error::new(
                io::ErrorKind::Unsupported,
                "Full command's explicit or imported stdin is not projected",
            ));
        }
        Ok(Self { command, environment_cleared })
    }

    /// Immutable original program/arguments, cwd and environment edits. The
    /// in-process parser must also apply environment_cleared(), and keep stdin
    /// inherited. This borrow supplies no authority to spawn the raw command.
    pub fn command(&self) -> &Command {
        self.command
    }

    pub fn environment_cleared(&self) -> bool {
        self.environment_cleared
    }
}
