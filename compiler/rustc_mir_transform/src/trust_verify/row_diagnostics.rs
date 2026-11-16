// Trust: optional, one-public-row-per-line diagnostics. Never proof transport.
// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0 OR MIT.

use std::io::{self, Write};

use trust_types::TransportObligationResult;

pub(super) const PREFIX: &str = "TRUST_ROW_DIAGNOSTIC:";

/// Reuse the canonical public row serializer, with its function identity on the
/// same line. The distinct diagnostic prefix is never a transport envelope or
/// proof authority. Disabled output performs no serialization or writes.
pub(super) fn write_rows(
    enabled: bool,
    output: &mut impl Write,
    function: &str,
    rows: &[TransportObligationResult],
) -> io::Result<()> {
    if !enabled {
        return Ok(());
    }
    let function = serde_json::to_string(function).map_err(io::Error::other)?;
    for row in rows {
        let row = serde_json::to_string(row).map_err(io::Error::other)?;
        writeln!(output, "{PREFIX}{{\"function\":{function},\"row\":{row}}}")?;
    }
    Ok(())
}

#[cfg(test)]
#[path = "row_diagnostics/tests.rs"]
mod tests;
