//! Trust: retain the resolved static native dependency in the local/development SDK.

use std::collections::BTreeMap;
use std::ffi::OsString;
use std::fs;
use std::io::{Read, Write};
use std::path::{Path, PathBuf};

use sha2::{Digest, Sha256};

use super::llvm_native_link::{LinkKind, StaticZstd};

pub(crate) fn applies(target: &str, host: &str, external: bool, shared: bool) -> bool {
    target.contains("apple-darwin") && target == host && external && !shared
}

/// Preserve the static inventory for a separate rustc-private tool without
/// exposing unrelated runtime libraries beside the selected LLVM archives.
pub(crate) fn isolated_tool_search(
    quoted_files: &str,
    target: &str,
    output: &Path,
) -> Result<PathBuf, String> {
    let files = shlex::split(quoted_files).ok_or("invalid quoted LLVM file inventory")?;
    if files.is_empty() || files.iter().any(|file| !Path::new(file).is_absolute()) {
        return Err("LLVM tool inventory must contain absolute archive paths".into());
    }
    let libraries = super::llvm_native_link::selected_libraries(
        files.into_iter().map(PathBuf::from),
        target,
        false,
    )?;
    let mut identity = Sha256::new();
    identity.update(b"bootstrap-llvm-tool-search-v1\0");
    identity.update((target.len() as u64).to_le_bytes());
    identity.update(target.as_bytes());
    let mut expected = BTreeMap::new();
    for library in libraries.values() {
        let source = library.path.canonicalize().map_err(|error| error.to_string())?;
        let name = library.path.file_name().ok_or("LLVM archive filename is absent")?.to_owned();
        let digest = archive_digest(&source)?;
        for bytes in [source.as_os_str().as_encoded_bytes(), name.as_encoded_bytes(), &digest] {
            identity.update((bytes.len() as u64).to_le_bytes());
            identity.update(bytes);
        }
        if expected.insert(name, digest).is_some() {
            return Err("LLVM tool inventory has duplicate archive names".into());
        }
    }
    fs::create_dir_all(output).map_err(|error| error.to_string())?;
    let directory = output.join(format!("tool-llvm-{:x}", identity.finalize()));
    match fs::symlink_metadata(&directory) {
        Ok(_) => {
            validate_tool_search(&directory, &expected)?;
            return Ok(directory);
        }
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
        Err(error) => return Err(error.to_string()),
    }
    let fresh = super::llvm_native_link::isolate_static_search(&libraries, output)?.directory;
    validate_tool_search(&fresh, &expected)?;
    if let Err(error) = fs::rename(&fresh, &directory) {
        // A concurrent publication supplies no evidence until its complete
        // inventory is checked against these original selected bytes.
        validate_tool_search(&directory, &expected)
            .map_err(|validation| format!("LLVM search publish failed: {error}; {validation}"))?;
        fs::remove_dir_all(&fresh).map_err(|error| error.to_string())?;
    }
    validate_tool_search(&directory, &expected)?;
    Ok(directory)
}

fn archive_digest(path: &Path) -> Result<[u8; 32], String> {
    let mut file = fs::File::open(path).map_err(|error| error.to_string())?;
    let mut digest = Sha256::new();
    let mut buffer = [0_u8; 64 * 1024];
    loop {
        let length = file.read(&mut buffer).map_err(|error| error.to_string())?;
        if length == 0 {
            break;
        }
        digest.update(&buffer[..length]);
    }
    Ok(digest.finalize().into())
}

fn validate_tool_search(
    directory: &Path,
    expected: &BTreeMap<OsString, [u8; 32]>,
) -> Result<(), String> {
    let original = fs::symlink_metadata(directory).map_err(|error| error.to_string())?;
    if !original.file_type().is_dir() {
        return Err("LLVM tool search is not a regular directory".into());
    }
    let mut count = 0;
    for entry in fs::read_dir(directory).map_err(|error| error.to_string())? {
        let entry = entry.map_err(|error| error.to_string())?;
        count += 1;
        let digest = expected.get(&entry.file_name()).ok_or("unselected LLVM tool search entry")?;
        if !entry.file_type().map_err(|error| error.to_string())?.is_file()
            || &archive_digest(&entry.path())? != digest
        {
            return Err("LLVM tool search archive changed or is indirect".into());
        }
    }
    if count != expected.len() {
        return Err("LLVM tool search is missing selected archives".into());
    }
    let current = fs::symlink_metadata(directory).map_err(|error| error.to_string())?;
    if !current.file_type().is_dir() {
        return Err("LLVM tool search directory was replaced".into());
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt as _;
        if (original.dev(), original.ino()) != (current.dev(), current.ino()) {
            return Err("LLVM tool search directory identity changed".into());
        }
    }
    Ok(())
}

pub(crate) fn stage_static_zstd(input: &StaticZstd, destination: &Path) -> Result<(), String> {
    if input.library.name != "zstd" || input.library.kind != LinkKind::Static {
        return Err("native development staging requires the declared static zstd archive".into());
    }
    let source = input.library.path.canonicalize().map_err(|error| error.to_string())?;
    let bytes = fs::read(&source).map_err(|error| error.to_string())?;
    let metadata = fs::read(&input.metadata).map_err(|error| error.to_string())?;
    let provider = fs::read(&input.provider).map_err(|error| error.to_string())?;
    fs::create_dir_all(destination).map_err(|error| error.to_string())?;
    // Publish a new inode, so a previous link or symlink in this build-tree
    // destination cannot overwrite either the provider or another SDK.
    let mut output =
        tempfile::NamedTempFile::new_in(destination).map_err(|error| error.to_string())?;
    output.write_all(&bytes).map_err(|error| error.to_string())?;
    output.as_file().sync_all().map_err(|error| error.to_string())?;
    fs::set_permissions(
        output.path(),
        fs::metadata(&source).map_err(|error| error.to_string())?.permissions(),
    )
    .map_err(|error| error.to_string())?;
    output.persist(destination.join("libzstd.a")).map_err(|error| error.to_string())?;

    let receipt = serde_json::json!({
        "schema": "trust.llvm-static-native-dev.v1",
        "library": "zstd",
        "kind": "static",
        "version": input.version,
        "source": source,
        "sha256": format!("{:x}", Sha256::digest(&bytes)),
        "pkg_config_metadata": input.metadata,
        "pkg_config_metadata_sha256": format!("{:x}", Sha256::digest(&metadata)),
        "pkg_config_provider": input.provider,
        "pkg_config_provider_sha256": format!("{:x}", Sha256::digest(&provider)),
        "watched_provider_aliases": input.watch_paths,
    });
    let mut output =
        tempfile::NamedTempFile::new_in(destination).map_err(|error| error.to_string())?;
    serde_json::to_writer_pretty(&mut output, &receipt).map_err(|error| error.to_string())?;
    // Like the archive, this component metadata must be readable by SDK users.
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        fs::set_permissions(output.path(), fs::Permissions::from_mode(0o644))
            .map_err(|error| error.to_string())?;
    }
    output.as_file().sync_all().map_err(|error| error.to_string())?;
    output
        .persist(destination.join("trust-llvm-native-dev.json"))
        .map_err(|error| error.to_string())?;
    Ok(())
}

#[cfg(test)]
mod tests;
