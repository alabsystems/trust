// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! The actual pause eligibility decision. The caller derives all three facts
//! while holding the original gate mutex; this leaf does not establish them.

pub fn may_pause_extra_workers(running: bool, acquiring_zero: bool, credits_zero: bool) -> bool {
    running && acquiring_zero && credits_zero
}
