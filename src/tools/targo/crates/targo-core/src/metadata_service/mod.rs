//! Native metadata service façade with explicit unsupported Unix behavior.
//! The native transport implementation retains its existing platform boundary.

#[cfg(any(target_os = "linux", target_os = "macos"))]
mod supported;
#[cfg(any(target_os = "linux", target_os = "macos"))]
pub use supported::{capabilities, capture_sdk_lease, execute, requested, run, snapshot_sdk_lease};

#[cfg(any(test, not(any(target_os = "linux", target_os = "macos"))))]
mod unsupported;
#[cfg(not(any(target_os = "linux", target_os = "macos")))]
pub use unsupported::{capabilities, requested, run};
