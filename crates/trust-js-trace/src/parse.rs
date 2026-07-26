// Sentinel extraction: pull the single `__TRUST_JS_TRACE_V1__{...}` line out
// of an engine run's captured stdout. The driver writes the sentinel line
// last, after suppressing all user console output, so any preceding stdout
// bytes are engine noise (e.g. a warning an engine prints unconditionally) —
// tolerated here, judged by calibration.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::trace::{ObservableTrace, SCHEMA_VERSION, TRACE_SENTINEL};

#[derive(Debug, thiserror::Error)]
pub enum TraceParseError {
    /// No sentinel line in stdout: the engine crashed, was killed, or never
    /// reached emission. Carries a bounded stdout tail for triage.
    #[error("no trace sentinel in engine stdout (tail: {stdout_tail:?})")]
    NoSentinel { stdout_tail: String },
    #[error("trace JSON failed to parse: {source} (line tail: {line_tail:?})")]
    Json {
        source: serde_json::Error,
        line_tail: String,
    },
    #[error("trace schema mismatch: got {got:?}, want {want}")]
    SchemaMismatch { got: String, want: &'static str },
}

/// Extract and validate the trace from raw engine stdout bytes. The LAST
/// sentinel line wins (user code cannot forge one: the driver suppresses
/// user stdout, and the driver's own line is written at exit).
pub fn extract_trace(stdout: &[u8]) -> Result<ObservableTrace, TraceParseError> {
    let text = String::from_utf8_lossy(stdout);
    let line = text
        .lines()
        .rev()
        .find_map(|l| l.trim_start().strip_prefix(TRACE_SENTINEL))
        .ok_or_else(|| TraceParseError::NoSentinel {
            stdout_tail: tail(&text, 512),
        })?;
    let trace: ObservableTrace =
        serde_json::from_str(line).map_err(|source| TraceParseError::Json {
            source,
            line_tail: tail(line, 512),
        })?;
    if trace.schema != SCHEMA_VERSION {
        return Err(TraceParseError::SchemaMismatch {
            got: trace.schema,
            want: SCHEMA_VERSION,
        });
    }
    Ok(trace)
}

fn tail(s: &str, n: usize) -> String {
    if s.len() <= n {
        return s.to_string();
    }
    let mut start = s.len() - n;
    while !s.is_char_boundary(start) {
        start += 1;
    }
    s[start..].to_string()
}
