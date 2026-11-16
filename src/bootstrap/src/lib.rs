//! Implementation of bootstrap, the Rust build system.
//!
//! This module, and its descendants, are the implementation of the Rust build
//! system. Most of this build system is backed by Cargo but the outer layer
//! here serves as the ability to orchestrate calling Cargo, sequencing Cargo
//! builds, building artifacts like LLVM, etc. The goals of bootstrap are:
//!
//! * To be an easily understandable, easily extensible, and maintainable build
//!   system.
//! * Leverage standard tools in the Rust ecosystem to build the compiler, aka
//!   crates.io and Cargo.
//! * A standard interface to build across all platforms, including MSVC
//!
//! ## Further information
//!
//! More documentation can be found in each respective module below, and you can
//! also check out the `src/bootstrap/README.md` file for more information.

// Trust: capture the original owner before libtest can open descriptors or start threads.
#![cfg_attr(test, feature(test, custom_test_frameworks, exitcode_exit_method))]
#![cfg_attr(test, test_runner(crate::test_entry::run))]
// tidy-alphabetical-start
#![allow(clippy::assertions_on_constants, reason = "false positive for `assert!(cfg!(..))`")]
#![allow(clippy::map_clone, reason = "false positive for `|x: &&Foo| Foo::clone(x)`")]
// tidy-alphabetical-end

// Trust: native manual cache maintenance shares Bootstrap's own judge.
#[cfg(any(target_os = "macos", target_os = "linux"))]
pub mod cache;
pub mod cli_main;
mod core;
pub mod engine;
pub mod native_entry;
mod utils;

// Trust: the native entry captures scheduler descriptors before any file opens.
// Trust: `crate::exit!` is used by the Trust refusal paths (carried in
// build_helper since the 1.101 port; upstream removed it there).
pub(crate) use build_helper::exit;
#[cfg(any(target_os = "macos", target_os = "linux"))]
pub use utils::fixed_admission::{
    capture_at_entry as capture_fixed_at_entry, snapshot_at_entry as snapshot_fixed_at_entry,
};
pub use utils::metadata_scheduler::capture_at_entry as capture_scheduler_at_entry;

#[cfg(test)]
extern crate test;
#[cfg(test)]
#[path = "test_entry.rs"]
mod test_entry;
