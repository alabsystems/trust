//! Trust: each case child borrows the same original execution as fixed
//! queries. The entry owner serializes actual children, retains their GNU/SDK
//! descriptions, and reaps on reader failure or unwind before the next borrow.
//! No test thread count or environment marker creates a scheduling credit.

use std::io;
use std::process::{Command, Output, Stdio};

#[cfg(any(target_os = "linux", target_os = "macos"))]
pub(crate) type CaseChild = trust_resource_controller::client::probe_scheduler::InheritedChild;
#[cfg(not(any(target_os = "linux", target_os = "macos")))]
pub(crate) type CaseChild = std::process::Child;

pub(crate) fn run<T>(
    command: &mut Command,
    consume: impl FnOnce(&mut CaseChild) -> io::Result<T>,
) -> io::Result<T> {
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    {
        crate::QUERY_SCHEDULER
            .get()
            .ok_or_else(|| io::Error::other("compiletest case requires original entry capture"))?
            .run_inherited_child(command, consume)
    }
    #[cfg(not(any(target_os = "linux", target_os = "macos")))]
    {
        consume(&mut command.spawn()?)
    }
}

pub(crate) fn output(command: &mut Command) -> io::Result<Output> {
    // Preserve Command::output's null stdin and exact, untruncated streams.
    command.stdin(Stdio::null()).stdout(Stdio::piped()).stderr(Stdio::piped());
    run(command, crate::read2::read2_output)
}
