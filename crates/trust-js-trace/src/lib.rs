// trust-js-trace: the TrustJS ObservableTrace projection — schema + driver.
//
// See Cargo.toml for the crate charter. Module structure is an internal
// detail: consumers get a flat API of the trace schema, the embedded in-JS
// driver, sentinel parsing, and trace diffing.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

mod diff;
mod driver;
mod parse;
mod trace;

pub use diff::{explain_divergence, traces_equal};
pub use driver::{trace_driver_sha256, TRACE_DRIVER_SOURCE};
pub use parse::{extract_trace, TraceParseError};
pub use trace::{
    normalize_async_completion_markers, Completion, HostEvent, ObservableTrace, ProjectedValue,
    ProjectionCaps, PropKey, ThrownProjection, ASYNC_FAILURE_MARKER_PREFIX, SCHEMA_VERSION,
    TRACE_SENTINEL,
};

/// Lowercase-hex SHA-256, used to pin the driver bytes and harness payloads
/// into evidence identities.
#[must_use]
pub fn sha256_hex(bytes: &[u8]) -> String {
    use sha2::{Digest, Sha256};
    let mut hasher = Sha256::new();
    hasher.update(bytes);
    let digest = hasher.finalize();
    let mut out = String::with_capacity(64);
    for byte in digest {
        use std::fmt::Write;
        let _ = write!(out, "{byte:02x}");
    }
    out
}
