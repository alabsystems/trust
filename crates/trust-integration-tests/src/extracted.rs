//! Loader for COMMITTED extracted-MIR artifacts (`fixtures/extracted/*.json`).
//!
//! These artifacts are the LITERAL output of trust-mir-extract's in-process
//! fixture extraction runs, serialized as pretty JSON maps of
//! `name -> VerifiableFunction`. This crate cannot run the in-process rustc,
//! so the lane e2e tests consume the extractor's output through these files
//! instead of hand-transcribing the extracted shapes.
//!
//! TRUSTWORTHINESS — the drift gate: the artifacts are REGENERATED, never
//! hand-edited. trust-mir-extract's `extracted_*_artifact_matches_committed`
//! lib tests re-extract each fixture in-process, serialize it, and compare
//! byte-for-byte against the committed file — any divergence between the live
//! extractor and these artifacts fails that suite. Regenerate with
//! `TRUST_UPDATE_EXTRACTED_FIXTURES=1` on those tests and commit the JSON.
//!
//! The serialization is pipeline plumbing, NOT TCB: the artifact is the
//! post-conversion `VerifiableFunction` form (no rustc-internal handles
//! survive extraction), and the clean-kernel check downstream remains the
//! authority on every proof obligation.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;
use std::path::Path;

use trust_types::VerifiableFunction;

/// Load a committed extracted-MIR artifact by file name (e.g.
/// `"mirror_fixture_functions.json"`).
///
/// # Panics
///
/// Panics when the artifact is missing or fails to deserialize — both mean
/// the extraction/serialization hand-off is broken, which the consuming test
/// must surface loudly rather than skip.
#[must_use]
pub fn load_extracted_functions(artifact: &str) -> BTreeMap<String, VerifiableFunction> {
    let path =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures/extracted").join(artifact);
    let json = std::fs::read_to_string(&path).unwrap_or_else(|e| {
        panic!(
            "missing committed extracted artifact {} ({e}); regenerate via \
             trust-mir-extract's drift-gate tests with \
             TRUST_UPDATE_EXTRACTED_FIXTURES=1",
            path.display()
        )
    });
    serde_json::from_str(&json).unwrap_or_else(|e| {
        panic!("corrupt extracted artifact {}: {e}", path.display())
    })
}
