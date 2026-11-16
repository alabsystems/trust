//! Create-only persistence for the existing explicit `-Ztrust-dump=ir` sink.
//! Neither publication nor decoding this diagnostic grants executable authority.

use std::fs::{self, OpenOptions};
use std::io::Write;
use std::path::{Path, PathBuf};

pub(super) fn persist(
    directory: &Path,
    codegen_unit: &str,
    object: &[u8],
    source_count: usize,
    artifact: Result<&trust_cg_bridge::object_replay::ObjectReplayArtifact, &str>,
) -> Result<PathBuf, String> {
    let bytes = match artifact {
        Ok(artifact) => artifact.to_bytes()?,
        Err(reason) => trust_cg_bridge::object_replay::capture_refusal_bytes(
            reason,
            codegen_unit,
            object,
            source_count,
        )?,
    };
    publish(directory, codegen_unit, &bytes)
}

fn publish(directory: &Path, codegen_unit: &str, bytes: &[u8]) -> Result<PathBuf, String> {
    fs::create_dir_all(directory).map_err(|error| error.to_string())?;
    // No source name/path is interpreted as a filesystem component. The actual
    // caller writes each CGU once; repeat publication refuses rather than
    // overwriting an earlier complete or partial diagnostic.
    let path = directory.join(format!(
        "{}.{}.{}.trust-object-replay.json",
        trust_cg_bridge::object_replay::artifact_digest(codegen_unit.as_bytes()),
        trust_cg_bridge::object_replay::artifact_digest(bytes),
        std::process::id()
    ));
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&path)
        .map_err(|error| format!("cannot create object replay {}: {error}", path.display()))?;
    file.write_all(bytes).and_then(|()| file.sync_all()).map_err(|error| {
        format!("object replay write failed (partial file retained) {}: {error}", path.display())
    })?;
    Ok(path)
}

#[cfg(test)]
mod tests;
