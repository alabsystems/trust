// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates
//! Boundary fixture for `targo trust temporal` / `targo trust build`.
//!
//! This package has an active canonical `trust-spec-temporal` dependency and a
//! linkable library target, which is exactly the automatic-route opt-in signal
//! the live gates must reject fail-closed (exit 2, unbound build evidence): no
//! second compilation can authenticate the source bytes rustc read or the final
//! build artifact. The retired Rust model macros are intentionally absent.

/// Force the canonical temporal engine into the linked crate graph without
/// introducing a second, hand-authored model surface.
pub fn canonical_temporal_prelude() -> &'static str {
    trust_spec_temporal::CLEAN_TEMPORAL_PRELUDE
}
