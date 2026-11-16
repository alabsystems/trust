// Trust: output-only request consumption by Targo's authenticated session.
// Filesystem guards and wire types are shared with the frontend producer.
use std::path::Path;
use std::{fs, io};

mod protocol;
pub(crate) use protocol::{ExportRequest, ExportUnit};
use protocol::{
    PAIRED_INPUTS, REQUEST_FILE, SCHEMA, create_private_directory, digest, invalid,
    private_directory, publish_new, read_bounded,
};

/// Read only the output request inside the already-authenticated session root.
/// No environment variable, Cargo configuration or external artifact imports it.
pub(crate) fn request(artifact_root: &Path, session: &str) -> io::Result<Option<ExportRequest>> {
    let path = artifact_root.join(REQUEST_FILE);
    match fs::symlink_metadata(&path) {
        Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(None),
        Err(e) => return Err(e),
        Ok(_) => {}
    }
    private_directory(artifact_root)?;
    let request: ExportRequest =
        serde_json::from_slice(&read_bounded(&path, 16 * 1024)?).map_err(invalid)?;
    if request.schema != SCHEMA || !digest(session) || request.session != session {
        return Err(invalid(
            "verifier input export request differs from the current session",
        ));
    }
    private_directory(&request.directory)?;
    private_directory(&request.directory.join("units"))?;
    Ok(Some(request))
}

/// Exact unit identity comes from Targo's graph, never from a user crate name.
pub(crate) fn unit_args(request: &ExportRequest, unit: &ExportUnit) -> io::Result<Vec<String>> {
    if unit.session != request.session
        || !digest(&unit.unit_sha256)
        || !digest(&unit.semantics_sha256)
        || !matches!(
            unit.graph_role.as_str(),
            "primary" | "dependency" | "test-execution" | "control"
        )
        || if unit.role == "excluded" {
            unit.verification_enabled
                || unit
                    .exclusion_reason
                    .as_ref()
                    .is_none_or(|reason| reason.is_empty())
        } else {
            !unit.verification_enabled
                || unit.role != unit.graph_role
                || !matches!(
                    unit.role.as_str(),
                    "primary" | "dependency" | "test-execution"
                )
                || unit.exclusion_reason.is_some()
        }
    {
        return Err(invalid(
            "invalid verifier input export unit identity or role",
        ));
    }
    private_directory(&request.directory)?;
    let dir = request.directory.join("units").join(&unit.unit_sha256);
    match create_private_directory(&dir) {
        Ok(()) => publish_new(&dir.join("unit.json"), unit)?,
        Err(e) if e.kind() == io::ErrorKind::AlreadyExists => {
            private_directory(&dir)?;
            let existing: ExportUnit =
                serde_json::from_slice(&read_bounded(&dir.join("unit.json"), 64 * 1024)?)
                    .map_err(invalid)?;
            if &existing != unit {
                return Err(invalid("verifier input export unit identity collision"));
            }
        }
        Err(e) => return Err(e),
    }
    if unit.role != "primary" || !unit.verification_enabled {
        return Ok(Vec::new());
    }
    let mut args = Vec::new();
    for sink in ["mir", "native-bundle"] {
        let path = dir.join(sink);
        match create_private_directory(&path) {
            Ok(()) => {}
            Err(e) if e.kind() == io::ErrorKind::AlreadyExists => private_directory(&path)?,
            Err(e) => return Err(e),
        }
        if sink == "native-bundle" {
            let paired = path.join(PAIRED_INPUTS);
            match create_private_directory(&paired) {
                Ok(()) => {}
                Err(e) if e.kind() == io::ErrorKind::AlreadyExists => private_directory(&paired)?,
                Err(e) => return Err(e),
            }
        }
        args.extend([
            "-Z".to_owned(),
            format!("trust-dump={sink}:{}", path.display()),
        ]);
    }
    Ok(args)
}
