#![cfg(target_os = "linux")]
#![deny(unsafe_op_in_unsafe_fn)]

mod control;
mod filter;
pub mod launcher;
pub mod native;
mod restriction;

pub use control::RetainedControl;
pub use restriction::{Installed, KernelLimits, PinnedInput, Profile, install};
#[doc(hidden)]
pub use restriction::{install_checker_resources, install_checker_threads};

#[derive(Debug)]
pub enum Error {
    Contract(&'static str),
    System(&'static str, std::io::Error),
    Budget(trust_process_isolation::Error),
}
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Contract(message) => write!(f, "worker contract refused: {message}"),
            Self::System(operation, error) => write!(f, "{operation}: {error}"),
            Self::Budget(error) => write!(f, "{error}"),
        }
    }
}
impl std::error::Error for Error {}

fn system(operation: &'static str) -> Error {
    Error::System(operation, std::io::Error::last_os_error())
}
