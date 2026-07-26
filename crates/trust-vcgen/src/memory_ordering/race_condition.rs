// trust_vcgen/memory_ordering/race_condition.rs: RaceCondition data race descriptor
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};
use trust_types::SourceSpan;

use crate::data_race::AccessKind;

/// A detected data race between two memory accesses.
///
/// Captures the two conflicting accesses with enough context for diagnostics
/// and VC generation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RaceCondition {
    /// Index of the first access in the access log.
    pub first_access: usize,
    /// Index of the second access in the access log.
    pub second_access: usize,
    /// The memory location involved.
    pub location: String,
    /// Thread performing the first access.
    pub first_thread: String,
    /// Thread performing the second access.
    pub second_thread: String,
    /// Kind of the first access.
    pub first_kind: AccessKind,
    /// Kind of the second access.
    pub second_kind: AccessKind,
    /// Source span of the first access (for diagnostics).
    pub first_span: SourceSpan,
    /// Source span of the second access (for diagnostics).
    pub second_span: SourceSpan,
}

impl RaceCondition {
    /// Human-readable description of this race.
    #[must_use]
    pub fn describe(&self) -> String {
        let first_op = if self.first_kind.is_write() { "write" } else { "read" };
        let second_op = if self.second_kind.is_write() { "write" } else { "read" };
        format!(
            "Data race on `{}`: {} by thread `{}` vs {} by thread `{}`",
            self.location, first_op, self.first_thread, second_op, self.second_thread,
        )
    }

    /// Returns `true` if both accesses are writes (write-write race).
    #[must_use]
    pub fn is_write_write(&self) -> bool {
        self.first_kind.is_write() && self.second_kind.is_write()
    }
}
