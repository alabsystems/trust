//! Explicit, bounded transport conversion of untrusted capture DATA.
//!
//! The original bytes remain the caller's immutable record. No solver,
//! compiler, replay, source agreement, ABI token or admission is produced here.
//! In particular, migration is not authentication: canonical altered data may
//! migrate and must still fail the independent `replay_original` comparison.

use serde::Serialize;
use trust_ir::Module;

use super::{
    CompilerInputCapture, MAX_PART_BYTES, MAX_WIRE_BYTES, MODULE_TRANSPORT_PROFILE, ModuleBytes,
};
use crate::object_replay::{artifact_digest, encode};

/// A closed, explicitly selected historical DATA transport, not a claim about
/// which compiler produced the bytes or which IR semantics they are licensed to use.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HistoricalModuleTransportProfile {
    /// Complete serde JSON with the empty, formerly trailing closure-layout
    /// table omitted. The later blob table must also be empty. No other field,
    /// at any depth, may differ from the freshly serialized complete Module.
    OmittedEmptyTrailingClosureLayouts,
    /// Already strictly current-canonical Module JSON, in an older capture
    /// without a transport-profile tag. Only the explicit tag is added.
    CompleteUnprofiled,
}
impl HistoricalModuleTransportProfile {
    fn label(self) -> &'static str {
        match self {
            Self::OmittedEmptyTrailingClosureLayouts => {
                "trust.ir.module.serde-json.omitted-empty-trailing-closure-layouts.v1"
            }
            Self::CompleteUnprofiled => "trust.ir.module.complete-serde-json.unprofiled.v1",
        }
    }
    fn added_default_field(self) -> Option<&'static str> {
        match self {
            Self::OmittedEmptyTrailingClosureLayouts => Some("closure_layouts"),
            Self::CompleteUnprofiled => None,
        }
    }
}

/// Serializable observations only. A self hash is not provenance or a proof.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CompilerModuleMigrationReceipt {
    pub site: String,
    pub input_sha256: String,
    pub input_bytes: usize,
    pub output_sha256: String,
    pub output_bytes: usize,
}

/// DATA receipt, with no checked source/ABI/proof/admission capability.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CompilerCaptureMigrationReceipt {
    pub schema: String,
    pub scope: String,
    pub input_capture_schema: String,
    pub output_capture_schema: String,
    pub input_module_profile: String,
    pub output_module_profile: String,
    pub input_capture_sha256: String,
    pub output_capture_sha256: String,
    pub input_capture_bytes: usize,
    pub output_capture_bytes: usize,
    pub object_sha256: String,
    pub object_bytes: usize,
    pub added_default_field: Option<String>,
    pub modules: Vec<CompilerModuleMigrationReceipt>,
}

/// A newly encoded DATA capture and its descriptive receipt. This does not
/// rename, overwrite or reauthenticate the original capture or its sidecar.
#[derive(Debug, Clone)]
pub struct CompilerCaptureDataMigration {
    pub capture: CompilerInputCapture,
    pub receipt: CompilerCaptureMigrationReceipt,
}

// This is deletion from the freshly emitted COMPLETE Module's exact final
// root field, never search/replace in supplied input and never a JSON Value
// roundtrip (which could collapse duplicate keys). If the writer no longer
// has this exact suffix, this historical profile is unavailable.
fn omitted_empty_trailing_closure_layouts(current: &[u8]) -> Result<Vec<u8>, String> {
    let prefix = current
        .strip_suffix(b",\"closure_layouts\":[]}")
        .ok_or("historical Module profile differs from complete writer")?;
    let mut historical = prefix.to_vec();
    historical.push(b'}');
    Ok(historical)
}

fn migrate_module(
    original: &ModuleBytes,
    profile: HistoricalModuleTransportProfile,
) -> Result<(ModuleBytes, Module), String> {
    if original.transport_profile.is_some() {
        return Err("historical Module migration requires an unprofiled input".into());
    }
    if original.bytes.is_empty()
        || original.bytes.len() > MAX_PART_BYTES
        || artifact_digest(&original.bytes) != original.sha256
    {
        return Err("historical Module migration size/digest mismatch".into());
    }
    let module: Module = serde_json::from_slice(&original.bytes).map_err(|e| e.to_string())?;
    let current = ModuleBytes::capture(&module)?;
    let historical = match profile {
        HistoricalModuleTransportProfile::OmittedEmptyTrailingClosureLayouts => {
            if !module.closure_layouts.is_empty() || !module.blobs.is_empty() {
                return Err(
                    "historical Module migration requires empty closure_layouts and blobs".into()
                );
            }
            omitted_empty_trailing_closure_layouts(&current.bytes)?
        }
        HistoricalModuleTransportProfile::CompleteUnprofiled => current.bytes.clone(),
    };
    // Full-byte equality enforces ALL fields, duplicates, unknown fields,
    // ordering, numeric/string spelling and whitespace at every depth. The
    // ordinary current decoder remains strict and has no historical fallback.
    if historical != original.bytes {
        return Err("historical Module transport is noncanonical for its explicit profile".into());
    }
    if current.decode()? != module {
        return Err("historical Module migration changed complete Module DATA".into());
    }
    Ok((current, module))
}

/// Convert a bounded historical capture to current transport DATA explicitly.
///
/// The input must be canonical under the selected closed profile, with no
/// profile tag on ANY Module. Every producer and the main Module is checked.
/// All other fields and the exact object bytes are retained. The output must
/// pass the ordinary strict current reader; it grants no proof/source grade.
///
/// This function is not an alternative authentication reference for replay.
/// Keep the original bytes and sidecar, independently select current inputs,
/// and retain the unchanged full equality guard in `replay_original`.
pub fn migrate_historical_capture_data(
    bytes: &[u8],
    profile: HistoricalModuleTransportProfile,
) -> Result<CompilerCaptureDataMigration, String> {
    if bytes.is_empty() || bytes.len() > MAX_WIRE_BYTES {
        return Err("historical compiler capture wire budget".into());
    }
    let original: CompilerInputCapture =
        serde_json::from_slice(bytes).map_err(|e| e.to_string())?;
    // This checks outer unknown/duplicate/order/whitespace integrity WITHOUT
    // asking the strict current Module decoder to accept historical bytes.
    if original.to_bytes()? != bytes {
        return Err("historical compiler capture outer wire is noncanonical".into());
    }
    // Bound before visiting Module payloads. Full schema/scope/config/object/
    // symbol/body/population checks are unchanged in the final strict reader.
    if original.producers.is_empty() || original.producers.len() > super::MAX_FUNCTIONS {
        return Err("historical compiler capture producer population budget".into());
    }
    let mut capture = original.clone();
    let mut modules = Vec::with_capacity(1 + original.producers.len());
    let (main, main_data) = migrate_module(&original.m_cg, profile)?;
    modules.push(receipt("m_cg".into(), &original.m_cg, &main));
    capture.m_cg = main;
    let mut producer_data = Vec::with_capacity(original.producers.len());
    for (index, (old, new)) in original.producers.iter().zip(&mut capture.producers).enumerate() {
        let (module, data) = migrate_module(&old.module, profile)?;
        modules.push(receipt(format!("producers[{index}].module"), &old.module, &module));
        new.module = module;
        producer_data.push(data);
    }
    // Explicitly check that the WHOLE capture differs only at ModuleBytes;
    // this includes any future outer fields and every producer symbol row.
    let mut preserved = capture.clone();
    preserved.m_cg = original.m_cg.clone();
    for (old, new) in original.producers.iter().zip(&mut preserved.producers) {
        new.module = old.module.clone();
    }
    if preserved != original {
        return Err("historical compiler capture migration changed non-Module DATA".into());
    }
    let output = capture.to_bytes()?;
    let checked = CompilerInputCapture::from_bytes(&output)?;
    let data = checked.decode_inputs()?;
    if data.m_cg != main_data
        || data.producers.len() != producer_data.len()
        || data.producers.iter().zip(&producer_data).any(|(row, module)| &*row.module != module)
    {
        return Err("historical compiler capture migration changed decoded Module DATA".into());
    }
    let receipt = CompilerCaptureMigrationReceipt {
        schema: "trust.compiler-cer-input-data-migration.v1".into(),
        scope: "untrusted-transport-DATA-only; no-source-ABI-proof-or-admission-authority".into(),
        input_capture_schema: original.schema.clone(),
        output_capture_schema: checked.schema.clone(),
        input_module_profile: profile.label().into(),
        output_module_profile: MODULE_TRANSPORT_PROFILE.into(),
        input_capture_sha256: artifact_digest(bytes),
        output_capture_sha256: artifact_digest(&output),
        input_capture_bytes: bytes.len(),
        output_capture_bytes: output.len(),
        object_sha256: original.object_sha256.clone(),
        object_bytes: original.object.len(),
        added_default_field: profile.added_default_field().map(str::to_owned),
        modules,
    };
    // Receipt size/depth are bounded too; it remains serializable DATA only.
    encode(&receipt, MAX_PART_BYTES)?;
    Ok(CompilerCaptureDataMigration { capture: checked, receipt })
}

fn receipt(
    site: String,
    original: &ModuleBytes,
    current: &ModuleBytes,
) -> CompilerModuleMigrationReceipt {
    CompilerModuleMigrationReceipt {
        site,
        input_sha256: original.sha256.clone(),
        input_bytes: original.bytes.len(),
        output_sha256: current.sha256.clone(),
        output_bytes: current.bytes.len(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn historical_suffix_profile_fails_closed_when_complete_writer_shape_differs() {
        assert!(
            omitted_empty_trailing_closure_layouts(b"{\"closure_layouts\":[],\"new\":[]}").is_err()
        );
        assert!(omitted_empty_trailing_closure_layouts(b"{\"closure_layouts\":[0]}").is_err());
        assert!(
            omitted_empty_trailing_closure_layouts(b"{\"closure_layouts\":[],\"blobs\":[]}")
                .is_err()
        );
    }
}
