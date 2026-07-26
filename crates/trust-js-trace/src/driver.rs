// The embedded in-JS trace driver. Embedding the bytes here (rather than
// shipping a loose file) makes the driver part of the crate's evidence
// identity: every scorecard records trace_driver_sha256(), so a scorecard is
// only comparable to another produced by byte-identical projection code.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

/// The trace driver source, spawned as `<engine> trace_driver.mjs <case.json>`.
pub const TRACE_DRIVER_SOURCE: &str = include_str!("../js/trace_driver.mjs");

/// Lowercase-hex SHA-256 of the embedded driver bytes — the projection's
/// evidence identity.
#[must_use]
pub fn trace_driver_sha256() -> String {
    crate::sha256_hex(TRACE_DRIVER_SOURCE.as_bytes())
}
