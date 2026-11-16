//! Types and functions shared across tools in this workspace.

pub mod ci;
pub mod drop_bomb;
pub mod fs;
pub mod git;
#[cfg(feature = "metrics")]
pub mod metrics;
pub mod npm;
pub mod stage0_parser;
pub mod targets;
// Trust: share the canonical leaf implementation with native toolchain hosts.
#[cfg(any(target_os = "macos", target_os = "linux"))]
pub use trust_build_tree::admission;
pub use trust_build_tree::{
    bootstrap_protocol, trust_build_lock, trust_output_lock, trust_repo_lock,
};
pub mod util;

/// The default set of crates for opt-dist to collect backend (LLVM, Cranelift) profiles.
pub const BACKEND_PGO_CRATES: &[&str] = &[
    "syn-2.0.101",
    "cargo-0.87.1",
    "serde-1.0.219",
    "ripgrep-14.1.1",
    "regex-automata-0.4.8",
    "clap_derive-4.5.32",
    "hyper-1.6.0",
];

/// The default set of crates for opt-dist to collect rustc profiles.
pub const RUSTC_PGO_CRATES: &[&str] = &[
    "externs",
    "ctfe-stress-5",
    "cargo-0.87.1",
    "token-stream-stress",
    "enum-stress",
    "tuple-stress",
    "diesel-2.2.10",
    "bitmaps-3.2.1",
    "serde-1.0.219-new-solver",
];
