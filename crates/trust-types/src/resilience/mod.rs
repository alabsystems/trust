// trust-types/resilience: External dependency failure modeling and resilience analysis
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

mod analysis;
mod external_patterns;
mod helpers;
mod types;

#[cfg(test)]
mod tests;

pub use analysis::ResilienceAnalysis;
pub use external_patterns::{EXTERNAL_CALL_PATTERNS, extract_failure_model, match_external_call};
pub use types::*;
