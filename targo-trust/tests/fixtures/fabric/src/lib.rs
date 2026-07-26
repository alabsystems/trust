// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates
//! Boundary fixture for `targo trust temporal` / `targo trust build`.
//!
//! This package has an active canonical `trust-spec-temporal` dependency and a
//! linkable library target, which is exactly the automatic-route opt-in signal
//! the live gates must REJECT fail-closed (exit 2, unbound build evidence): no
//! linked-code registry, generated harness, or second compilation can
//! authenticate the source bytes rustc read or the final build artifact. The
//! `temporal_model!` items below expand to plain model-constructor fns; new
//! user models belong in Clean `ScalarModel` source.

// This fixture deliberately exercises the legacy macro surface (that is what
// the boundary gate must reject), so the D1+ advisory nudge is acknowledged.
#![allow(deprecated)]

use trust_spec_temporal::temporal_model;

temporal_model! {
    EdgeGate {
        const Buggy = 0;
        var granted = 0;
        var decision = 0;
        action Grant when (granted <= 0) {
            granted = 1;
            decision = if 1 + Buggy > 0 { 1 } else { 0 };
        }
        action Revoke when (granted > 0) {
            granted = 0;
            decision = if 0 + Buggy > 0 { 1 } else { 0 };
        }
        invariant FailClosed: decision <= granted;
    }
}

temporal_model! {
    SinkNoLoss {
        const Frame = 4;
        const Buggy = 0;
        var written = 0;
        var lost = 0;
        action Step when (written + lost <= Frame - 1) {
            written = written + 1;
            lost = if Buggy > 0 { Frame - written } else { lost };
        }
        invariant NoLoss: lost <= 0;
        invariant Accounted: written + lost <= Frame;
    }
}
