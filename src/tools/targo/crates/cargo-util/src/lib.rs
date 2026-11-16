//! Miscellaneous support code used by Cargo.
//!
//! > This crate is maintained by the Cargo team, primarily for use by Cargo
//! > and not intended for external use (except as a transitive dependency). This
//! > crate may make major changes to its APIs or be deprecated without warning.

#![allow(clippy::disallowed_methods)]

// Trust: one retained scheduler and owned transport for nested subprocesses.
pub use jobserver_utils::{DESCENDANT_HANDOFF_ENV, FIXED_CLAIM_HANDOFF_ENV, Jobserver};

pub use self::read2::read2;
#[cfg(unix)]
pub use self::read2::{Read2Action, Read2Control, read2_controlled, read2_controlled_with_eof};
pub use du::du;
// Trust: `StreamingOutputLimits` is exported so Cargo can opt individual child
// processes into bounded reads; see `process_builder/mod.rs`.
pub use action_sandbox::ActionSandbox;
pub use environment_inputs::EnvironmentInputs;
pub use platform_inputs::{PLATFORM_READ_DIRECTORIES, PLATFORM_READ_FILES, PlatformInputs};
pub use process_builder::{
    CaptureCompletionCause, CaptureOwnerObservation, CaptureStreamEnd, CapturedProcess, CpuTimes,
    ExecStats, ProcessBuilder, Stdio, StreamingOutputLimits, StreamingProcessScope,
};
#[cfg(any(target_os = "linux", target_os = "macos"))]
pub use process_builder::{OwnedIsolatedChild, PreparedIsolatedChild};
pub use process_error::{
    ProcessError, TargetExecutionError, exit_status_to_string, is_simple_exit_code,
};
pub use sha256::Sha256;

mod action_sandbox;
mod environment_inputs;
mod platform_inputs;

mod du;
pub mod paths;
mod process_builder;
mod process_executor;
pub use process_executor::{ProcessExecutor, install_process_executor, installed_process_executor};
mod process_error;
mod read2;
pub mod registry;
mod sha256;

/// Whether or not this running in a Continuous Integration environment.
pub fn is_ci() -> bool {
    std::env::var("CI").is_ok() || std::env::var("TF_BUILD").is_ok()
}
