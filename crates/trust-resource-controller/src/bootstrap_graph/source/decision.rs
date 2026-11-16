// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Permission DATA for the actual retained-input close guard. The caller must
//! derive both inputs from its original handler and authentic ClosedRoot;
//! this Boolean does not construct settlement, ownership or release authority.

pub fn may_close_source_descriptions(handler_active: bool, closed_root_matches: bool) -> bool {
    !handler_active && closed_root_matches
}
