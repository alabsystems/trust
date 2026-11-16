//! Exact diagnostic inputs for independent verifier replay.
//!
//! This codec never issues proof authority or validates a claim as true. It
//! preserves even inputs that admission will reject, so a failed request can
//! be reproduced through the normal verifier boundary. Callers own opt-in I/O.

use serde::{Deserialize, Serialize};
use trust_ir_bridge::NativeVerificationBundle;
use trust_verifier_api::{TrustContractBundle, TrustObligation};

/// Reserved subdirectory below the existing native-bundle dump sink.
pub const VERIFIER_INPUT_PAIRED_SUBDIRECTORY: &str = "paired-inputs";

const SCHEMA: &str = "trust.verifier-input-pair.v1";
const MAX_BYTES: usize = 128 * 1024 * 1024;

/// One immutable, content-addressed JSON file. Existing identical files may be
/// reused; a caller must never overwrite different bytes at the same name.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifierInputCaptureFile {
    pub filename: String,
    pub bytes: Vec<u8>,
}

/// Write the three objects first and the correlation record last. Shared
/// public/native inputs keep the same names across different requested subsets.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifierInputCapture {
    pub public: VerifierInputCaptureFile,
    pub requested: VerifierInputCaptureFile,
    pub native: VerifierInputCaptureFile,
    pub record: VerifierInputCaptureFile,
}

impl VerifierInputCapture {
    /// Publish the correlation record only after all referenced objects.
    pub fn files(&self) -> impl Iterator<Item = &VerifierInputCaptureFile> {
        [&self.public, &self.requested, &self.native, &self.record].into_iter()
    }
}

/// Ordinary untrusted inputs. Loading these never restores a live receipt or
/// bypasses public/native validation, proof replay, or any verifier budget.
#[derive(Clone, Debug)]
pub struct CapturedVerifierInputs {
    pub public: TrustContractBundle,
    pub requested: Vec<TrustObligation>,
    pub native: NativeVerificationBundle,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct ObjectRef {
    sha256: String,
    bytes: usize,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Record {
    schema: String,
    public: ObjectRef,
    requested: ObjectRef,
    native: ObjectRef,
}

fn filename(role: &str, digest: &str) -> String {
    format!("trust-verifier-input-{role}-{digest}.json")
}

fn object<T: Serialize + ?Sized>(
    role: &str,
    value: &T,
) -> Result<(VerifierInputCaptureFile, ObjectRef), String> {
    let bytes = trust_types::canonical_json_bytes(value).map_err(|error| error.to_string())?;
    if bytes.len() > MAX_BYTES {
        return Err(format!("verifier input {role} exceeds the diagnostic object limit"));
    }
    let sha256 = trust_types::stable_sha256_hex(&bytes);
    let len = bytes.len();
    Ok((
        VerifierInputCaptureFile { filename: filename(role, &sha256), bytes },
        ObjectRef { sha256, bytes: len },
    ))
}

/// Serialize the exact values supplied to a native verifier dispatch. No
/// source metadata, obligation subset, or native identity is reconstructed.
/// This performs no writes and must be called only for requested diagnostics.
pub fn encode_verifier_input_pair(
    public: &TrustContractBundle,
    requested: &[TrustObligation],
    native: &NativeVerificationBundle,
) -> Result<VerifierInputCapture, String> {
    let (public_file, public) = object("public", public)?;
    let (requested_file, requested) = object("requested", requested)?;
    let (native_file, native) = object("native", native)?;
    let (record, _) = object("pair", &Record { schema: SCHEMA.into(), public, requested, native })?;
    Ok(VerifierInputCapture {
        public: public_file,
        requested: requested_file,
        native: native_file,
        record,
    })
}

fn checked_bytes(role: &str, reference: &ObjectRef, bytes: Vec<u8>) -> Result<Vec<u8>, String> {
    if !trust_types::is_stable_sha256_hex(&reference.sha256)
        || reference.bytes == 0
        || reference.bytes > MAX_BYTES
        || bytes.len() != reference.bytes
        || trust_types::stable_sha256_hex(&bytes) != reference.sha256
    {
        return Err(format!("verifier input {role} content does not match its exact reference"));
    }
    Ok(bytes)
}

fn decode<T: serde::de::DeserializeOwned + Serialize>(
    role: &str,
    bytes: &[u8],
) -> Result<T, String> {
    let value: T =
        serde_json::from_slice(bytes).map_err(|error| format!("invalid {role} input: {error}"))?;
    if trust_types::canonical_json_bytes(&value).map_err(|error| error.to_string())? != bytes {
        return Err(format!("verifier input {role} is not its exact typed canonical encoding"));
    }
    Ok(value)
}

/// Load a captured triple through the existing typed codecs. The callback
/// receives only flat names derived from checked SHA-256 references; callers
/// still own bounded, non-symlink file reads from their selected capture root.
/// Integrity is not proof authority: the returned inputs require normal
/// verifier admission and replay, including when a caller rewrites all files.
pub fn decode_verifier_input_pair(
    record_filename: &str,
    record_bytes: &[u8],
    mut read_object: impl FnMut(&str) -> Result<Vec<u8>, String>,
) -> Result<CapturedVerifierInputs, String> {
    if record_bytes.is_empty()
        || record_bytes.len() > MAX_BYTES
        || record_filename != filename("pair", &trust_types::stable_sha256_hex(record_bytes))
    {
        return Err("verifier input pair filename does not match its exact contents".into());
    }
    let record: Record = decode("pair", record_bytes)?;
    if record.schema != SCHEMA {
        return Err("unsupported verifier input pair schema".into());
    }
    let mut load = |role: &str, reference: &ObjectRef| {
        if !trust_types::is_stable_sha256_hex(&reference.sha256)
            || reference.bytes == 0
            || reference.bytes > MAX_BYTES
        {
            return Err(format!("invalid verifier input {role} reference"));
        }
        checked_bytes(role, reference, read_object(&filename(role, &reference.sha256))?)
    };
    let public = decode("public", &load("public", &record.public)?)?;
    let requested = decode("requested", &load("requested", &record.requested)?)?;
    let native = decode("native", &load("native", &record.native)?)?;
    Ok(CapturedVerifierInputs { public, requested, native })
}
