//! Native ownership of Trust's existing build and output namespaces.
//!
//! These actual guards exclude participating actors during live ownership.
//! They do not freeze source bytes, establish child settlement or survive
//! process death as a general cleanup quarantine.

pub mod bootstrap_protocol;
pub mod trust_build_lock;
pub mod trust_output_lock;
pub mod trust_repo_lock;

#[cfg(any(target_os = "macos", target_os = "linux"))]
pub mod admission;

// Only the refusals of admission and trust_repo_lock's management use it.
#[cfg(any(target_os = "macos", target_os = "linux"))]
mod shell_word;

#[cfg(all(test, unix))]
mod owner_only;

#[cfg(all(test, any(target_os = "macos", target_os = "linux")))]
mod launcher_file;
