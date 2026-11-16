// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Retain exact fixed-canary requests before invoking the kernel.

use std::error::Error;
use std::fs;
use std::path::Path;

use trust_spec_temporal::{
    CleanAutomaticScalarProof, InvariantModelProgramPropertyCertificate,
    ModelProgramRefinementError,
};

use super::super::reuse;

pub(super) fn begin(
    directory: &Path,
    module: &[u8],
    request: &serde_json::Value,
    model_proof: &CleanAutomaticScalarProof,
) -> Result<(), Box<dyn Error>> {
    // Each attempt owns a fresh namespace. A partial capture is retained, and
    // failure stops the caller before any proof attempt can count as a control.
    fs::create_dir(directory)?;
    reuse::write_new(&directory.join("module.trust-ir.bin"), module)?;
    reuse::write_new(
        &directory.join("model-safety-certificate.json"),
        &serde_json::to_vec(model_proof)?,
    )?;
    reuse::write_new(&directory.join("request.json"), &serde_json::to_vec_pretty(request)?)?;
    Ok(())
}

pub(super) fn accepted(
    directory: &Path,
    certificate: &InvariantModelProgramPropertyCertificate,
    schema: &str,
) -> Result<(), Box<dyn Error>> {
    reuse::write_new(&directory.join("certificate.json"), &serde_json::to_vec(certificate)?)?;
    reuse::write_new(
        &directory.join("outcome.json"),
        format!(r#"{{"schema":"{schema}","outcome":"certificate-produced"}}"#).as_bytes(),
    )?;
    Ok(())
}

pub(super) fn rejected(
    directory: &Path,
    error: &ModelProgramRefinementError,
    schema: &str,
) -> Result<(), Box<dyn Error>> {
    reuse::write_new(
        &directory.join("outcome.json"),
        &serde_json::to_vec_pretty(&serde_json::json!({
            "schema": schema,
            "outcome": "rejected",
            "message": error.to_string(),
            "detail": format!("{error:?}"),
        }))?,
    )?;
    Ok(())
}

pub(super) fn replayed(directory: &Path, schema: &str) -> Result<(), Box<dyn Error>> {
    reuse::write_new(
        &directory.join("outcome.json"),
        format!(r#"{{"schema":"{schema}","outcome":"candidate-freshly-replayed"}}"#).as_bytes(),
    )?;
    Ok(())
}

pub(super) fn decode_rejected(
    directory: &Path,
    error: &serde_json::Error,
    schema: &str,
) -> Result<(), Box<dyn Error>> {
    reuse::write_new(
        &directory.join("outcome.json"),
        &serde_json::to_vec_pretty(&serde_json::json!({
            "schema": schema,
            "outcome": "candidate-decode-rejected",
            "message": error.to_string(),
        }))?,
    )?;
    Ok(())
}
