//! Create-only diagnostics for actual Compiler-lane CER input data.
//! Publication or decoding confers no source, ABI, metadata or shipping authority.

use std::fs::{self, OpenOptions};
use std::io::Write;
use std::path::{Path, PathBuf};

use trust_cg_bridge::compiler_input_capture::{CaptureIncomplete, CompilerInputCapture};
use trust_cg_bridge::object_replay::artifact_digest;

pub(super) fn persist(
    directory: &Path,
    codegen_unit: &str,
    capture: &Result<CompilerInputCapture, CaptureIncomplete>,
) -> Result<PathBuf, String> {
    let bytes = match capture {
        Ok(capture) => capture.to_bytes()?,
        Err(reason) => reason.to_bytes()?,
    };
    publish(directory, codegen_unit, &bytes)
}

fn publish(directory: &Path, codegen_unit: &str, bytes: &[u8]) -> Result<PathBuf, String> {
    fs::create_dir_all(directory).map_err(|e| e.to_string())?;
    let path = directory.join(format!(
        "{}.{}.{}.trust-compiler-cer-input.json",
        artifact_digest(codegen_unit.as_bytes()),
        artifact_digest(bytes),
        std::process::id()
    ));
    let mut file =
        OpenOptions::new().write(true).create_new(true).open(&path).map_err(|e| {
            format!("cannot create Compiler CER input data {}: {e}", path.display())
        })?;
    file.write_all(bytes).and_then(|()| file.sync_all()).map_err(|e| {
        format!("Compiler input write failed (partial diagnostic retained) {}: {e}", path.display())
    })?;
    Ok(path)
}

#[cfg(test)]
mod tests;
