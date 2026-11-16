// Trust: output-only verifier input export shared by the protected frontend and Targo.
// Nothing in this module imports evidence or changes a verification decision.
use std::fs::{self, OpenOptions};
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};

pub(super) const SCHEMA: u32 = 1;
pub(super) const REQUEST_FILE: &str = "verifier-input-export-request-v1.json";
pub(super) const PAIRED_INPUTS: &str = "paired-inputs";

pub(super) fn invalid(message: impl std::fmt::Display) -> io::Error {
    io::Error::other(message.to_string())
}

pub(super) fn private_directory(path: &Path) -> io::Result<()> {
    let meta = fs::symlink_metadata(path)?;
    if !meta.is_dir() || meta.file_type().is_symlink() {
        return Err(invalid(
            "verifier input export directory must not be a symlink",
        ));
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        // SAFETY: geteuid has no preconditions and does not mutate memory.
        if meta.mode() & 0o777 != 0o700 || meta.uid() != unsafe { libc::geteuid() } {
            return Err(invalid(
                "verifier input export directory must be owned and mode 0700",
            ));
        }
    }
    if !path.is_absolute() || fs::canonicalize(path)? != path {
        return Err(invalid(
            "verifier input export directory must be canonical and absolute",
        ));
    }
    Ok(())
}

pub(super) fn create_private_directory(path: &Path) -> io::Result<()> {
    let mut builder = fs::DirBuilder::new();
    #[cfg(unix)]
    {
        use std::os::unix::fs::DirBuilderExt;
        builder.mode(0o700);
    }
    builder.create(path)?;
    private_directory(path)
}

pub(super) fn read_bounded(path: &Path, limit: u64) -> io::Result<Vec<u8>> {
    let meta = fs::symlink_metadata(path)?;
    if !meta.is_file() || meta.file_type().is_symlink() || meta.len() > limit {
        return Err(invalid(format!(
            "invalid or oversized export file `{}`",
            path.display()
        )));
    }
    let mut bytes = Vec::new();
    let mut options = OpenOptions::new();
    options.read(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.custom_flags(libc::O_NOFOLLOW);
    }
    let file = options.open(path)?;
    let opened = file.metadata()?;
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        if meta.dev() != opened.dev() || meta.ino() != opened.ino() {
            return Err(invalid("export file changed while it was opened"));
        }
    }
    if !opened.is_file() {
        return Err(invalid("export file is not regular"));
    }
    file.take(limit + 1).read_to_end(&mut bytes)?;
    if bytes.len() as u64 > limit {
        return Err(invalid("export file grew beyond its size limit"));
    }
    Ok(bytes)
}

pub(super) fn publish_new(path: &Path, value: &impl Serialize) -> io::Result<()> {
    let bytes = serde_json::to_vec_pretty(value).map_err(invalid)?;
    let mut options = OpenOptions::new();
    options.write(true).create_new(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.mode(0o600);
    }
    let mut file = options.open(path)?;
    file.write_all(&bytes)?;
    file.write_all(b"\n")?;
    file.sync_all()
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct ExportRequest {
    pub(super) schema: u32,
    pub(super) session: String,
    pub(super) directory: PathBuf,
}

pub(super) fn digest(value: &str) -> bool {
    value.len() == 64
        && value
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct ExportUnit {
    pub(crate) session: String,
    pub(crate) unit_sha256: String,
    pub(crate) semantics_sha256: String,
    pub(crate) package_name: String,
    pub(crate) role: String,
    pub(crate) graph_role: String,
    pub(crate) exclusion_reason: Option<String>,
    pub(crate) mode: String,
    pub(crate) verification_enabled: bool,
}
