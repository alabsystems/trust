//! Native invocation inputs observed by the maintained OpenSSL producer.
//!
//! This is deliberately not a cache acceptance receipt. The Rust wrapper's
//! fingerprint cannot stand in for a closed native toolchain/SDK identity.
//! Source copies and process environments are owned here; external runtime and
//! SDK closure ownership remains an explicit prerequisite for artifact reuse.

use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use std::env;
use std::ffi::{OsStr, OsString};
use std::fs::{self, File, OpenOptions};
use std::io::{Read, Write};
use std::path::Path;
use std::process::Command;

/// A reason an observed native invocation cannot authorize artifact reuse.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ReuseBlocker {
    /// OpenSSL's mkbuildinf.pl reads the live clock without SOURCE_DATE_EPOCH.
    LiveBuildClock,
    /// The advertised epoch is not a nonnegative integer understood by OpenSSL.
    InvalidBuildEpoch,
    /// No owner freezes the compiler/interpreter/make runtime and SDK closure.
    UnownedNativeToolchain,
    /// The install prefix is still owned by a Rust build-script unit.
    WrapperOwnedOutputRoot,
}

impl ReuseBlocker {
    pub fn code(&self) -> &'static str {
        match self {
            Self::LiveBuildClock => "live-build-clock",
            Self::InvalidBuildEpoch => "invalid-build-epoch",
            Self::UnownedNativeToolchain => "unowned-native-toolchain-sdk-closure",
            Self::WrapperOwnedOutputRoot => "wrapper-owned-output-root",
        }
    }
}

/// Diagnostic observation, never serialized proof or native-cache authority.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NativeRecipeObservation {
    pub source_sha256: String,
    pub invocation_sha256: String,
    pub commands: usize,
    pub reuse_blockers: Vec<ReuseBlocker>,
}

/// Preserve the exact ambient inputs once. Commands apply their existing
/// explicit overrides afterwards, including the startup-owned jobserver.
pub(crate) struct Invocation {
    environment: BTreeMap<OsString, OsString>,
    hash: Sha256,
    commands: usize,
    source_sha256: String,
    blockers: Vec<ReuseBlocker>,
}

impl Invocation {
    pub(crate) fn new(target: &str, host: &str, source_sha256: String) -> Self {
        let environment = env::vars_os().collect::<BTreeMap<_, _>>();
        Self::from_environment(target, host, source_sha256, environment)
    }

    fn from_environment(
        target: &str,
        host: &str,
        source_sha256: String,
        environment: BTreeMap<OsString, OsString>,
    ) -> Self {
        let mut hash = Sha256::new();
        field(&mut hash, b"trust.openssl-native-invocation.v1");
        field(&mut hash, target.as_bytes());
        field(&mut hash, host.as_bytes());
        field(&mut hash, source_sha256.as_bytes());
        let mut blockers = Vec::new();
        match environment.get(OsStr::new("SOURCE_DATE_EPOCH")) {
            None => blockers.push(ReuseBlocker::LiveBuildClock),
            Some(value)
                if value.to_str().is_some_and(|value| {
                    !value.is_empty()
                        && value.bytes().all(|b| b.is_ascii_digit())
                        && value.parse::<u64>().is_ok()
                }) => {}
            Some(_) => blockers.push(ReuseBlocker::InvalidBuildEpoch),
        }
        blockers.extend([
            ReuseBlocker::UnownedNativeToolchain,
            ReuseBlocker::WrapperOwnedOutputRoot,
        ]);
        Self {
            environment,
            hash,
            commands: 0,
            source_sha256,
            blockers,
        }
    }

    /// Hash and freeze the actual command, preserving all semantic paths and
    /// every environment value. No textual path or descriptor normalization
    /// manufactures an equivalence that the native producer has not proved.
    pub(crate) fn freeze(&mut self, command: &mut Command) {
        let mut environment = self.environment.clone();
        for (name, value) in command.get_envs() {
            match value {
                Some(value) => {
                    environment.insert(name.to_owned(), value.to_owned());
                }
                None => {
                    environment.remove(name);
                }
            }
        }
        field(&mut self.hash, b"command");
        os_field(&mut self.hash, command.get_program());
        for arg in command.get_args() {
            field(&mut self.hash, b"arg");
            os_field(&mut self.hash, arg);
        }
        field(&mut self.hash, b"cwd");
        if let Some(cwd) = command.get_current_dir() {
            os_field(&mut self.hash, cwd.as_os_str());
        }
        for (name, value) in &environment {
            field(&mut self.hash, b"env");
            os_field(&mut self.hash, name);
            os_field(&mut self.hash, value);
        }
        field(&mut self.hash, b"end-command");
        command.env_clear().envs(environment);
        self.commands += 1;
    }

    pub(crate) fn finish(self) -> NativeRecipeObservation {
        NativeRecipeObservation {
            source_sha256: self.source_sha256,
            invocation_sha256: hex(self.hash.finalize()),
            commands: self.commands,
            reuse_blockers: self.blockers,
        }
    }
}

fn field(hash: &mut Sha256, value: &[u8]) {
    hash.update((value.len() as u64).to_le_bytes());
    hash.update(value);
}

fn os_field(hash: &mut Sha256, value: &OsStr) {
    // as_encoded_bytes is lossless on this native host. Host and target are
    // independently bound; this observation is not portable across hosts.
    field(hash, value.as_encoded_bytes());
}

fn hex(value: impl AsRef<[u8]>) -> String {
    value
        .as_ref()
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

/// Copy each source leaf through one checked handle while hashing those exact
/// bytes. A read-dir error, substituted leaf or short copy cannot silently
/// become the source identity of a successful native build.
pub(crate) fn copy_source(source: &Path, destination: &Path) -> Result<String, String> {
    let mut hash = Sha256::new();
    field(&mut hash, b"trust.openssl-source-copy.v1");
    copy_directory(
        source,
        destination,
        Path::new(""),
        &mut hash,
        true,
        &mut (0, 0),
        0,
    )?;
    Ok(hex(hash.finalize()))
}

/// Complete checked materialization of native outputs. Unlike the upstream
/// source recipe, no .git or unused-source exceptions apply to artifacts.
pub(crate) fn copy_outputs(source: &Path, destination: &Path) -> Result<String, String> {
    let mut hash = Sha256::new();
    field(&mut hash, b"trust.openssl-output-copy.v1");
    copy_directory(
        source,
        destination,
        Path::new(""),
        &mut hash,
        false,
        &mut (0, 0),
        0,
    )?;
    Ok(hex(hash.finalize()))
}

fn copy_directory(
    source: &Path,
    destination: &Path,
    relative: &Path,
    hash: &mut Sha256,
    source_exclusions: bool,
    budget: &mut (u64, usize),
    depth: usize,
) -> Result<(), String> {
    if depth > 64 {
        return Err("native tree copy depth exceeds64".into());
    }
    let before = fs::symlink_metadata(source).map_err(|e| e.to_string())?;
    if !before.is_dir() || before.file_type().is_symlink() {
        return Err(format!(
            "source directory is redirected: {}",
            source.display()
        ));
    }
    // Directories retain the producer's normal create_dir/umask semantics.
    // Bind the mode of that actual copied namespace, not a guessed source mode.
    permissions_field(hash, &fs::metadata(destination).map_err(|e| e.to_string())?);
    let mut entries = Vec::new();
    for entry in fs::read_dir(source).map_err(|e| e.to_string())? {
        budget.1 += 1;
        if budget.1 > 100_000 {
            return Err("native tree copy census exceeds100000".into());
        }
        entries.push(entry.map_err(|e| e.to_string())?);
    }
    entries.sort_by_key(|entry| entry.file_name());
    for entry in entries {
        let name = entry.file_name();
        if source_exclusions && name == ".git" {
            continue;
        }
        let path = entry.path();
        let relative = relative.join(&name);
        let target = destination.join(&name);
        let metadata = fs::symlink_metadata(&path).map_err(|e| e.to_string())?;
        field(hash, b"entry");
        os_field(hash, relative.as_os_str());
        if source_exclusions
            && metadata.file_type().is_symlink()
            && path.iter().any(|part| part == "cloudflare-quiche")
        {
            // Preserve the upstream recipe's explicit unused-source exclusion.
            field(hash, b"excluded-quiche-link");
            os_field(
                hash,
                fs::read_link(&path).map_err(|e| e.to_string())?.as_os_str(),
            );
        } else if metadata.is_dir() && !metadata.file_type().is_symlink() {
            field(hash, b"directory");
            fs::create_dir(&target).map_err(|e| e.to_string())?;
            copy_directory(
                &path,
                &target,
                &relative,
                hash,
                source_exclusions,
                budget,
                depth + 1,
            )?;
        } else {
            budget.0 = budget
                .0
                .checked_add(metadata.len())
                .ok_or("native tree size overflow")?;
            if budget.0 > 2 * 1024 * 1024 * 1024 {
                return Err("native tree copy exceeds twoGiB".into());
            }
            field(hash, b"file");
            copy_leaf(&path, &target, &metadata, hash)?;
        }
    }
    let after = fs::symlink_metadata(source).map_err(|e| e.to_string())?;
    if !same_snapshot(&before, &after) {
        return Err(format!(
            "source directory changed during copy: {}",
            source.display()
        ));
    }
    Ok(())
}

fn copy_leaf(
    source: &Path,
    destination: &Path,
    before: &fs::Metadata,
    hash: &mut Sha256,
) -> Result<(), String> {
    copy_leaf_with_hooks(source, destination, before, hash, || {}, || {})
}

fn copy_leaf_with_hooks(
    source: &Path,
    destination: &Path,
    before: &fs::Metadata,
    hash: &mut Sha256,
    before_open: impl FnOnce(),
    after_read: impl FnOnce(),
) -> Result<(), String> {
    if !before.is_file() || before.file_type().is_symlink() {
        return Err(format!(
            "source leaf is not a regular file: {}",
            source.display()
        ));
    }
    before_open();
    let mut options = OpenOptions::new();
    options.read(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK);
    }
    let mut input = options.open(source).map_err(|e| e.to_string())?;
    let opened = input.metadata().map_err(|e| e.to_string())?;
    if !opened.is_file() || !same_snapshot(before, &opened) {
        return Err(format!("source leaf was substituted: {}", source.display()));
    }
    let mut output = File::options()
        .write(true)
        .create_new(true)
        .open(destination)
        .map_err(|e| e.to_string())?;
    let mut bytes = 0_u64;
    let mut buffer = [0_u8; 65536];
    let mut leaf = Sha256::new();
    loop {
        let count = input.read(&mut buffer).map_err(|e| e.to_string())?;
        if count == 0 {
            break;
        }
        bytes = bytes
            .checked_add(count as u64)
            .ok_or("source size overflow")?;
        if bytes > before.len() {
            return Err("source grew during copy".into());
        }
        leaf.update(&buffer[..count]);
        output
            .write_all(&buffer[..count])
            .map_err(|e| e.to_string())?;
    }
    after_read();
    let after = fs::symlink_metadata(source).map_err(|e| e.to_string())?;
    if bytes != before.len()
        || !same_snapshot(before, &after)
        || !same_snapshot(before, &input.metadata().map_err(|e| e.to_string())?)
    {
        return Err(format!(
            "source leaf changed during copy: {}",
            source.display()
        ));
    }
    output
        .set_permissions(before.permissions())
        .map_err(|e| e.to_string())?;
    permissions_field(hash, before);
    field(hash, &bytes.to_le_bytes());
    field(hash, &leaf.finalize());
    Ok(())
}

fn permissions_field(hash: &mut Sha256, metadata: &fs::Metadata) {
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        field(hash, &metadata.permissions().mode().to_le_bytes());
    }
    #[cfg(not(unix))]
    field(hash, &[u8::from(metadata.permissions().readonly())]);
}

fn same_snapshot(left: &fs::Metadata, right: &fs::Metadata) -> bool {
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        left.dev() == right.dev()
            && left.ino() == right.ino()
            && left.mode() == right.mode()
            && left.len() == right.len()
            && left.mtime() == right.mtime()
            && left.mtime_nsec() == right.mtime_nsec()
            && left.ctime() == right.ctime()
            && left.ctime_nsec() == right.ctime_nsec()
    }
    #[cfg(not(unix))]
    {
        left.file_type() == right.file_type()
            && left.len() == right.len()
            && left.permissions() == right.permissions()
            && left.modified().ok() == right.modified().ok()
            && left.created().ok() == right.created().ok()
    }
}

#[cfg(test)]
mod tests;
