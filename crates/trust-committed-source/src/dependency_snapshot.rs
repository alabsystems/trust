// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! The maintained conservative dependency-source capture, shared unchanged by
//! Bootstrap and native semantic-owner wrappers. This passive observation owns
//! actual committed/physical reads; it grants no Graph, source, native, Seed,
//! SDK, selector-execution, complete-envelope or retirement authority.

use std::collections::BTreeSet;
use std::ffi::OsStr;
use std::os::fd::AsFd;
use std::path::PathBuf;

use serde_json::{Value, json};
use sha2::{Digest as _, Sha256};

use super::*;
use trust_resource_provenance::program::{HeldSourceReadSet, SourceEntryKind, SourceRead};

const CODE: [&str; 6] = [
    "scripts/seed_custody_source.py",
    "scripts/bootstrap_dependency_preparation.py",
    "scripts/seed_input_archives.py",
    "scripts/seed_input_records.py",
    "scripts/bootstrap_dependency_closure.py",
    "scripts/recreate_bootstrap.py",
];
const RECIPE: [&str; 4] = [
    "src/bootstrap/src/core/metadata.rs",
    "src/bootstrap/src/core/build_steps/compile.rs",
    "src/bootstrap/src/core/build_steps/vendor.rs",
    "src/bootstrap/src/core/build_steps/tool.rs",
];
// Packet membership accounting is distinct from the shared Git census bound.
const MAX_MEMBERSHIP_BYTES: usize = 256 * 1024 * 1024;
const MAX_SELECTED_BYTES: usize = 64 * 1024 * 1024;
const MAX_PACKET_BYTES: usize = 256 * 1024 * 1024;

/// Opaque passive committed-selection and physical-read observation. No caller
/// rows, JSON, digest, pathname alone or completed-role constructor exists.
pub struct CommittedDependencySnapshot {
    directory: Option<File>,
    root: PathBuf,
    deadline: Instant,
    creator: u32,
    repositories: Vec<Arc<CommittedRepositoryObservation>>,
    selected: Option<HeldSourceReadSet>,
    packet: Value,
    revoked: AtomicBool,
}

/// Retains every partially observed description on capture refusal. The caller
/// must keep its actual semantic original beside this passive refusal.
pub struct CommittedDependencyRefusal {
    error: io::Error,
    original: Box<CommittedDependencySnapshot>,
}
impl CommittedDependencyRefusal {
    pub fn into_parts(self) -> (io::Error, Box<CommittedDependencySnapshot>) {
        (self.error, self.original)
    }
}

fn text(bytes: &[u8]) -> io::Result<&str> {
    std::str::from_utf8(bytes).map_err(error)
}
fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}
// Use the existing serializer, bounding each emitted chunk before allocation.
// Packet bytes remain DATA; this sink grants no source or native authority.
struct PacketWriter {
    bytes: Vec<u8>,
    limit: usize,
}
impl io::Write for PacketWriter {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        let needed = self
            .bytes
            .len()
            .checked_add(bytes.len())
            .filter(|needed| *needed <= self.limit)
            .ok_or_else(|| invalid("dependency source packet exceeds bound"))?;
        if needed > self.bytes.capacity() {
            let capacity = self.bytes.capacity().saturating_mul(2).max(needed).min(self.limit);
            self.bytes.try_reserve_exact(capacity - self.bytes.len()).map_err(error)?;
        }
        self.bytes.extend_from_slice(bytes);
        Ok(bytes.len())
    }
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}
/// The SAME bounded JSON encoder, for DATA only. Encoding creates no snapshot
/// or source owner, and cannot authenticate caller-provided rows.
pub fn encode_dependency_packet(value: &Value, limit: usize) -> io::Result<Vec<u8>> {
    let mut writer = PacketWriter { bytes: Vec::new(), limit };
    serde_json::to_writer(&mut writer, value).map_err(error)?;
    Ok(writer.bytes)
}

/// The maintained final rows/physical-read bookend. Inputs are already opaque
/// observations and an actual directory; success grants no native/local join.
pub fn check_committed_reads(
    rows: &[&Arc<CommittedRepositoryObservation>],
    selected: &HeldSourceReadSet,
    directory: BorrowedFd<'_>,
    deadline: Instant,
) -> io::Result<()> {
    time(deadline)?;
    for rows in rows {
        rows.check(deadline)?;
    }
    selected.check_current(directory)?;
    for rows in rows {
        rows.check(deadline)?;
    }
    time(deadline)
}

impl CommittedDependencySnapshot {
    fn record_result<T>(&self, result: io::Result<T>) -> io::Result<T> {
        if result.is_err() {
            self.revoked.store(true, Ordering::Release);
        }
        result
    }

    fn original_directory(&self) -> io::Result<BorrowedFd<'_>> {
        self.directory
            .as_ref()
            .map(AsFd::as_fd)
            .ok_or_else(|| invalid("dependency original directory capture is absent"))
    }

    /// Original DATA only; the semantic source owner remains with the caller.
    pub fn root(&self) -> &Path {
        &self.root
    }

    /// Original endpoint DATA. All later operations can only restrict it.
    pub fn original_deadline(&self) -> Instant {
        self.deadline
    }

    pub fn check_current(&self, directory: BorrowedFd<'_>, deadline: Instant) -> io::Result<()> {
        let result = (|| {
            if self.revoked.load(Ordering::Acquire)
                || self.creator != std::process::id()
                || deadline > self.deadline
            {
                return Err(invalid("dependency capture is quarantined, foreign or extended"));
            }
            time(deadline)?;
            self.original_directory()?;
            if self.repositories.is_empty() {
                return Err(invalid("dependency source has no original committed root"));
            }
            let rows = self.repositories.iter().collect::<Vec<_>>();
            check_committed_reads(
                &rows,
                self.selected
                    .as_ref()
                    .ok_or_else(|| invalid("dependency physical capture is absent"))?,
                directory,
                deadline,
            )
        })();
        self.record_result(result)
    }

    pub fn capture_glob_directories(
        &mut self,
        directory: BorrowedFd<'_>,
        paths: &[PathBuf],
        deadline: Instant,
    ) -> io::Result<()> {
        let result = (|| {
            self.check_current(directory, deadline)?;
            if paths.len() > 8192 {
                return Err(invalid("glob listing population exceeds bound"));
            }
            let root = self.repositories[0].root().to_owned();
            for path in paths {
                let name = text(path.as_os_str().as_bytes())?;
                let full = root.join(path);
                let present = if path == Path::new(".") {
                    true
                } else {
                    let repository = self
                        .repositories
                        .iter()
                        .filter(|repository| full.starts_with(repository.root()))
                        .max_by_key(|repository| repository.root().components().count())
                        .ok_or_else(|| invalid("glob path has no original repository"))?;
                    let relative = full.strip_prefix(repository.root()).map_err(error)?;
                    if full == repository.root() {
                        true
                    } else {
                        match repository.lookup(relative.as_os_str().as_bytes(), deadline)? {
                            CommittedLookup::Present(entry) if entry.mode == 0o040000 => true,
                            CommittedLookup::Absent => false,
                            _ => {
                                return Err(invalid(
                                    "glob directory crosses an unresolved literal boundary",
                                ));
                            }
                        }
                    }
                };
                let selected = self.selected.as_mut().expect("same captured source guard");
                let value = if present {
                    let entries = selected.directory_entries(directory, path)?;
                    let mut rows = Vec::with_capacity(entries.len());
                    for entry in entries {
                        let kind = match entry.kind {
                            SourceEntryKind::File => "file",
                            SourceEntryKind::Directory => "directory",
                            SourceEntryKind::Link => "symlink",
                            SourceEntryKind::Other => "other",
                        };
                        rows.push(json!({"name":text(&entry.name)?, "kind":kind}));
                    }
                    Value::Array(rows)
                } else {
                    selected.observe(directory, path, SourceRead::Absent)?;
                    Value::Null
                };
                self.packet["listings"][name] = value;
            }
            self.check_current(directory, deadline)
        })();
        self.record_result(result)
    }

    /// Encode this SAME observed packet; never accept a caller snapshot value.
    pub fn packet(&self, directory: BorrowedFd<'_>, deadline: Instant) -> io::Result<Vec<u8>> {
        let result = (|| {
            self.check_current(directory, deadline)?;
            let bytes = encode_dependency_packet(&self.packet, MAX_PACKET_BYTES)?;
            self.check_current(directory, deadline)?;
            Ok(bytes)
        })();
        self.record_result(result)
    }

    /// Reuse the maintained complete conservative capture on the supplied real
    /// original directory, exact canonical root and original endpoint. The
    /// caller retains/checks its own semantic source/Graph around this read.
    pub fn capture(
        directory: BorrowedFd<'_>,
        root: &Path,
        deadline: Instant,
    ) -> Result<Self, CommittedDependencyRefusal> {
        let mut snapshot = Self {
            directory: None,
            root: root.to_owned(),
            deadline,
            creator: std::process::id(),
            repositories: Vec::new(),
            selected: None,
            packet: Value::Null,
            revoked: AtomicBool::new(false),
        };
        let captured = (|| {
            time(deadline)?;
            snapshot.directory = Some(File::from(directory.try_clone_to_owned()?));
            let root_repository = Arc::new(CommittedRepositoryObservation::capture(
                snapshot.original_directory()?,
                root,
                deadline,
            )?);
            snapshot.selected =
                Some(HeldSourceReadSet::capture(snapshot.original_directory()?, deadline)?);
            snapshot.repositories.push(Arc::clone(&root_repository));
            let root = root_repository.root();
            let mut at = 0;
            while at < snapshot.repositories.len() {
                let repository = Arc::clone(&snapshot.repositories[at]);
                let links = repository
                    .entries(deadline)?
                    .iter()
                    .filter(|entry| entry.mode == 0o160000)
                    .map(|entry| entry.path.clone())
                    .collect::<Vec<_>>();
                for link in links {
                    if snapshot.repositories.len() >= 128 {
                        return Err(invalid("dependency repository population exceeds bound"));
                    }
                    let child = Arc::new(repository.submodule(&link, deadline)?);
                    snapshot.repositories.push(child);
                }
                at += 1;
            }
            let mut selected = BTreeSet::<PathBuf>::new();
            let mut repositories = serde_json::Map::new();
            let mut population = 0usize;
            for repo in &snapshot.repositories {
                let prefix = repo.root().strip_prefix(root).map_err(error)?;
                let mut rows = Vec::new();
                for entry in repo.entries(deadline)? {
                    let path = prefix.join(OsStr::from_bytes(&entry.path));
                    population = population
                        .checked_add(path.as_os_str().as_bytes().len() + 256)
                        .ok_or_else(|| invalid("dependency membership accounting overflow"))?;
                    if population > MAX_MEMBERSHIP_BYTES {
                        return Err(invalid("dependency membership population exceeds bound"));
                    }
                    let kind = match entry.mode {
                        0o040000 => "dir",
                        0o120000 => "symlink",
                        0o160000 => "gitlink",
                        _ => "file",
                    };
                    rows.push(json!({"path":text(&entry.path)?, "kind":kind,
                        "mode":entry.mode & 0o777, "object":entry.object.to_string(),
                        "bytes":null, "sha256":null}));
                    if entry.mode == 0o120000 {
                        selected.insert(path.clone());
                    }
                    if path.file_name().is_some_and(|name| {
                        name == "Cargo.lock"
                            || ((name == "config" || name == "config.toml")
                                && path.parent().and_then(|parent| parent.file_name())
                                    == Some(OsStr::new(".cargo")))
                    }) {
                        selected.insert(path.clone());
                    }
                    if path.file_name().is_some_and(|name| name == "Cargo.toml") {
                        let mut directory = path.parent();
                        while let Some(parent) = directory {
                            for name in
                                ["Cargo.toml", "Cargo.lock", ".cargo/config", ".cargo/config.toml"]
                            {
                                selected.insert(parent.join(name));
                            }
                            directory = parent.parent();
                        }
                    }
                }
                let label = if prefix.as_os_str().is_empty() {
                    "."
                } else {
                    text(prefix.as_os_str().as_bytes())?
                };
                if repositories.insert(label.into(), Value::Array(rows)).is_some() {
                    return Err(invalid("dependency repository is repeated"));
                }
            }
            selected.extend(CODE.into_iter().chain(RECIPE).map(PathBuf::from));
            let mut batch = Vec::<(PathBuf, SourceRead)>::new();
            let mut captured_reads = serde_json::Map::new();
            let mut total = 0usize;
            for path in selected {
                let full = root.join(&path);
                let repository = snapshot
                    .repositories
                    .iter()
                    .filter(|repository| full.starts_with(repository.root()))
                    .max_by_key(|repository| repository.root().components().count())
                    .ok_or_else(|| invalid("dependency path has no original repository"))?;
                let relative = full.strip_prefix(repository.root()).map_err(error)?;
                let expected = match repository.lookup(relative.as_os_str().as_bytes(), deadline)? {
                    CommittedLookup::Present(entry) => match entry.mode {
                        0o100644 | 0o100755 => SourceRead::File {
                            mode: entry.mode,
                            bytes: repository.blob(entry.object, deadline)?,
                        },
                        0o120000 => {
                            SourceRead::Link { target: repository.blob(entry.object, deadline)? }
                        }
                        0o040000 => SourceRead::Directory,
                        _ => return Err(invalid("dependency read reached an unresolved gitlink")),
                    },
                    CommittedLookup::Absent => SourceRead::Absent,
                    // The SAME maintained view resolves aliases. A required
                    // uncaptured target later refuses instead of reopening it.
                    CommittedLookup::Unresolved(_) => continue,
                };
                let data = match &expected {
                    SourceRead::File { mode, bytes } => {
                        total = total
                            .checked_add(bytes.len())
                            .ok_or_else(|| invalid("dependency bytes overflow"))?;
                        if bytes.len() > 4 * 1024 * 1024 || total > MAX_SELECTED_BYTES {
                            return Err(invalid("dependency source bytes exceed bound"));
                        }
                        json!({"kind":"file", "mode":mode & 0o777, "bytes":bytes.len(),
                            "sha256":hex(&Sha256::digest(bytes)), "hex":hex(bytes)})
                    }
                    SourceRead::Link { target } => json!({"kind":"symlink", "mode":0o777,
                        "target":text(target)?}),
                    SourceRead::Absent => json!({"kind":"absent"}),
                    SourceRead::Directory => continue,
                };
                captured_reads.insert(text(path.as_os_str().as_bytes())?.into(), data);
                batch.push((path, expected));
            }
            let directory = snapshot.directory.as_ref().expect("captured original root").as_fd();
            snapshot
                .selected
                .as_mut()
                .expect("captured original root")
                .observe_batch(directory, &batch)?;
            for (prefix, rows) in &mut repositories {
                for row in rows.as_array_mut().expect("constructed membership array") {
                    let path = if prefix == "." {
                        row["path"].as_str().unwrap().to_owned()
                    } else {
                        format!("{prefix}/{}", row["path"].as_str().unwrap())
                    };
                    if let Some(read) = captured_reads.get(&path) {
                        for key in ["mode", "bytes", "sha256", "target"] {
                            if let Some(value) = read.get(key) {
                                row[key] = value.clone();
                            }
                        }
                    }
                }
            }
            snapshot.packet = json!({"schema":"trust-native-dependency-source-v1",
                "root":text(root.as_os_str().as_bytes())?, "repositories":repositories,
                "reads":captured_reads, "listings":{}});
            snapshot.check_current(snapshot.original_directory()?, deadline)
        })();
        match snapshot.record_result(captured) {
            Ok(()) => Ok(snapshot),
            Err(error) => Err(CommittedDependencyRefusal { error, original: Box::new(snapshot) }),
        }
    }
}

#[cfg(test)]
mod tests;
