//! Built-in Cargo credential providers

#![allow(clippy::print_stderr)]

pub mod adaptor;
pub mod process;
pub mod token;

/// External credential protocols still use interactive std child pipes, which
/// have no supported ProcessExecutor ownership contract. A mandatory executor
/// installed BEFORE configuration must therefore refuse these routes before
/// native birth. This observation creates no owner and cannot relax NoFork.
/// Ordinary CLI execution without such an owner retains its existing behavior.
fn require_local_process(program: &std::ffi::OsStr) -> Result<(), cargo_credential::Error> {
    if cargo_util::ProcessBuilder::new(program).has_process_executor() {
        Err("external credential processes are unsupported by the mandatory execution owner".into())
    } else {
        Ok(())
    }
}

#[cfg(all(test, unix))]
mod tests;
