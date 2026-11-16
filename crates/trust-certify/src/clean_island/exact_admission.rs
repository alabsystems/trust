// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Exact stored declaration identity for a completed local certification audit.
//! This does not check a term, serialize the audit's dependency closure, or
//! attest native checker callbacks. The caller must re-audit the current
//! environment even when the resulting declaration digest equals a cached one.

use std::io::{self, Write};

use bincode::Options;
use clean_kernel::{ConstantInfo, Name};
use trust_symbols::TermDigest;

const MAX_DECLARATION_BYTES: usize = 16 * 1024 * 1024;

struct BoundedBytes(Vec<u8>);

impl Write for BoundedBytes {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        if trust_types::audit_ledger::cap_hit_if(
            bytes.len() > MAX_DECLARATION_BYTES.saturating_sub(self.0.len()),
            "crates/trust-certify/src/clean_island/exact_admission.rs:MAX_DECLARATION_BYTES",
        ) {
            return Err(io::Error::other("exact island declaration exceeds 16 MiB encoding limit"));
        }
        self.0.extend_from_slice(bytes);
        Ok(bytes.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

pub(super) fn definition_digest(name: &Name, info: &ConstantInfo) -> Result<TermDigest, String> {
    let mut bytes = BoundedBytes(Vec::new());
    // All Name/Expr/Level constructors, binder/let/metadata fields and the
    // declaration header are structural serde, not Display or cached hashes.
    bincode::DefaultOptions::new()
        .with_fixint_encoding()
        .with_little_endian()
        .serialize_into(
            &mut bytes,
            &("trust.clean-island.checked-definition/v2/bincode1-fixed-le", name, info),
        )
        .map_err(|error| {
            format!(
                "island definition `{name}` cannot bind its complete checked declaration: {error}; \
             options: inspect unexpectedly large metadata or extend the measured encoder; \
             no partial digest or new facet admission is produced"
            )
        })?;
    Ok(TermDigest::of_bytes(&bytes.0))
}
