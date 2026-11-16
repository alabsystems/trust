// Copyright 2026 Andrew Yates | Apache-2.0
//! Configuration/source association only, never source-to-IR refinement.
//! A historical fixed cohort must not silently follow a changed selected model.
use std::collections::BTreeMap;

use serde::Deserialize;

// Separately owned canonical mathematical source extension. Existing selected
// model/SOURCE_REVISION stays exact; this does not claim the selected base commit
// already contained this new file or move any dependency selector.
use super::source_contract::{
    FOUNDATION_IR, PRODUCER_CLEAN, PROFILE_IR, PROFILE_SHA256 as CANONICAL_PROFILE_SHA256,
};
use crate::object_replay::artifact_digest;
const PROFILE_SOURCE: &[u8] = include_bytes!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/tests/fixtures/canonical_scalar_profile_source/U64ScalarProfile.lean"
));
const REVISION: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../first-party/clean/crates/clean-olean/tests/fixtures/lean/v4.30.0-rc2/semr/SOURCE_REVISION"
));
const CONSUMER: &[u8] = include_bytes!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../first-party/clean/crates/clean-olean/tests/fixtures/lean/v4.30.0-rc2/semr/U64AdditionConsumer.lean"
));
macro_rules! source {
    ($name:literal) => {
        (
            $name,
            include_bytes!(concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/../../first-party/trust-ir/lean/semr/",
                $name
            )),
        )
    };
}
// The maintained Clean reader's complete shared canonical-source set, not just
// the scalar theorem file. These are compile-time bytes of the selected source
// checkout; public callers cannot supply a model, path, revision or hash.
const SOURCES: [(&str, &[u8]); 9] = [
    source!("SemR.lean"),
    source!("MiniRust.lean"),
    source!("SemRMiniRust.lean"),
    source!("SemRMemory.lean"),
    source!("ClosureConstruction.lean"),
    source!("MetadataCheck.lean"),
    source!("ClosureAxiomAudit.lean"),
    source!("U64Addition.lean"),
    source!("U64AdditionAudit.lean"),
];

#[derive(Deserialize)]
struct SourceBinding {
    ir_commit: String,
    source_sha256: BTreeMap<String, String>,
}

// Independently bound published canonical profile, NOT a manifest-chosen
// digest. Scalar and program consumers share this exact source copy; selected
// IR model and Clean reader pins do not move for a separate profile extension.
fn check_canonical_profile(copy: &[u8], declared: Option<&String>) -> Result<(), String> {
    if artifact_digest(copy) != CANONICAL_PROFILE_SHA256
        || declared.map(String::as_str) != Some(CANONICAL_PROFILE_SHA256)
    {
        return Err(
            "fixed profile copy/manifest differs from independently bound canonical profile source"
                .into(),
        );
    }
    Ok(())
}

pub(super) fn check(manifest: &str) -> Result<(), String> {
    let binding: SourceBinding = serde_json::from_str(manifest).map_err(|e| e.to_string())?;
    if binding.ir_commit.len() != 40
        || binding.ir_commit != FOUNDATION_IR
        || binding.ir_commit != REVISION.trim()
    {
        return Err("fixed scalar cohort differs from selected canonical source revision".into());
    }
    check_foundation(&binding.source_sha256)
}

// Check only the explicitly named selected foundation. A separately labelled
// mathematical extension must additionally check its own exact revision/source;
// this helper never relabels the extension as the old selected revision.
pub(super) fn check_foundation(source_sha256: &BTreeMap<String, String>) -> Result<(), String> {
    if REVISION.trim() != FOUNDATION_IR {
        return Err("selected canonical source revision differs from fixed foundation".into());
    }
    for (file, bytes) in SOURCES {
        let key = format!("ir@{}/lean/semr/{file}", REVISION.trim());
        if source_sha256.get(&key) != Some(&artifact_digest(bytes)) {
            return Err(format!(
                "fixed scalar cohort differs from compiled canonical source {file}"
            ));
        }
    }
    let profile = format!("ir@{PROFILE_IR}/lean/semr/U64ScalarProfile.lean");
    check_canonical_profile(PROFILE_SOURCE, source_sha256.get(&profile))?;
    let consumer = format!("clean@{PRODUCER_CLEAN}/semr/U64AdditionConsumer.lean");
    if source_sha256.get(&consumer) != Some(&artifact_digest(CONSUMER)) {
        return Err("fixed scalar cohort differs from compiled canonical consumer source".into());
    }
    let revision = format!("clean@{PRODUCER_CLEAN}/semr/SOURCE_REVISION");
    if source_sha256.get(&revision) != Some(&artifact_digest(REVISION.as_bytes())) {
        return Err("fixed scalar cohort source-revision bytes differ".into());
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fixed_scalar_model_matches_compiled_canonical_source_only() {
        const MANIFEST: &str = include_str!("cohort.json");
        check(MANIFEST).unwrap();
        let original: serde_json::Value = serde_json::from_str(MANIFEST).unwrap();
        for case in 0..4 {
            let mut changed = original.clone();
            match case {
                0 => changed["ir_commit"] = "0".repeat(40).into(),
                1 => {
                    let key = format!("ir@{}/lean/semr/SemR.lean", REVISION.trim());
                    changed["source_sha256"][key] = "0".repeat(64).into();
                }
                2 => {
                    let key = format!("clean@{PRODUCER_CLEAN}/semr/U64AdditionConsumer.lean");
                    changed["source_sha256"][key] = "0".repeat(64).into();
                }
                _ => {
                    let key = format!("ir@{PROFILE_IR}/lean/semr/U64ScalarProfile.lean");
                    changed["source_sha256"][key] = "0".repeat(64).into();
                }
            }
            assert!(check(&serde_json::to_string(&changed).unwrap()).is_err());
        }
        println!(
            "CANONICAL_SCALAR_SOURCE fixed_current=1 wrong_revision=1 wrong_model=1 wrong_consumer=1 wrong_generic_profile=1; source association only, no source-refinement theorem"
        );
    }
}

#[cfg(test)]
mod canonical_copy_controls {
    use super::*;

    #[test]
    fn copy_and_matching_manifest_cannot_redefine_canonical_profile() {
        let correct = CANONICAL_PROFILE_SHA256.to_string();
        check_canonical_profile(PROFILE_SOURCE, Some(&correct)).unwrap();
        let mut changed = PROFILE_SOURCE.to_vec();
        changed[0] ^= 1;
        let matching_forgery = artifact_digest(&changed);
        assert_ne!(matching_forgery, correct);
        assert!(check_canonical_profile(&changed, Some(&matching_forgery)).is_err());
        assert!(check_canonical_profile(PROFILE_SOURCE, Some(&matching_forgery)).is_err());
        assert!(check_canonical_profile(&changed, Some(&correct)).is_err());
        assert!(check_canonical_profile(PROFILE_SOURCE, None).is_err());
        println!(
            "CANONICAL_PROFILE_COPY positive=1 co_mutated_copy_and_manifest=1 copy_only=1 manifest_only=1 missing=1; independent canonical source binding only,no proofgrade"
        );
    }
}
