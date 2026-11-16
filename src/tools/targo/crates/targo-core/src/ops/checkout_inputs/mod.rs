//! Live physical tracked-input comparisons. No result or stat key survives a batch.
//!
//! HEAD/index/tree/sparse/gitlink/history selection remains the caller's job.
//! This reader compares the supplied committed blob identities with every byte
//! read now. Definite physical refusals remain refusals. Only captured regular
//! digest mismatches may enter the original exact committed-attribute CRLF check.
// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

use std::fs::{self, Metadata, OpenOptions};
use std::io::{BufRead, Read, Write};
use std::path::{Component, Path, PathBuf};
use std::sync::Arc;
use std::time::{Duration, Instant};

use anyhow::{Context as _, ensure};
use base64::Engine as _;
use hmac::{Hmac, KeyInit as _, Mac as _};
use serde::{Deserialize, Serialize};
use sha2::{Digest as _, Sha256};

use crate::CargoResult;

const SCHEMA: &str = "trust-tracked-inputs-v1";
const MAX_FRAME: u64 = 32 * 1024 * 1024;
const MAX_ITEMS: usize = 4096;
const MAX_JOBS: usize = 64;

/// Compatibility data, not executable authentication or a source-to-binary proof.
pub fn tracked_input_reader_identity() -> String {
    hex::encode(Sha256::digest(include_bytes!("mod.rs")))
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Start {
    schema: String,
    reader: String,
    key: String,
    root: String,
    executable: String,
    image_sha256: String,
    jobs: usize,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Batch {
    schema: String,
    nonce: String,
    repo: String,
    items: Vec<Item>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Item {
    path: String,
    mode: String,
    oid: String,
}

#[derive(Serialize)]
struct Ready<'a> {
    schema: &'a str,
    reader: String,
    runtime_policy: &'a str,
    runtime_identity: String,
}

#[derive(Serialize)]
struct Answer<'a> {
    schema: &'a str,
    nonce: &'a str,
    request_sha256: String,
    checked: usize,
    bytes: u64,
    failures: Vec<IndexedFailure>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
struct Snapshot {
    dev: u64,
    ino: u64,
    mode: u32,
    bytes: u64,
    mtime_sec: i64,
    mtime_nsec: i64,
    ctime_sec: i64,
    ctime_nsec: i64,
}

#[derive(Debug, Serialize)]
struct FileFailure {
    kind: &'static str,
    digest: Option<String>,
    stat: Option<Snapshot>,
}

impl FileFailure {
    fn new(kind: &'static str) -> Self {
        Self {
            kind,
            digest: None,
            stat: None,
        }
    }
}

#[derive(Debug, Serialize)]
struct IndexedFailure {
    index: usize,
    #[serde(flatten)]
    failure: FileFailure,
}

fn shaped(value: &str, bytes: usize) -> bool {
    value.len() == bytes * 2
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

fn path(value: &str) -> CargoResult<PathBuf> {
    let bytes = base64::engine::general_purpose::STANDARD
        .decode(value)
        .map_err(|_| anyhow::anyhow!("invalid tracked-input path encoding"))?;
    ensure!(!bytes.contains(&0), "tracked-input path contains NUL");
    #[cfg(unix)]
    {
        use std::os::unix::ffi::OsStringExt as _;
        Ok(std::ffi::OsString::from_vec(bytes).into())
    }
    #[cfg(not(unix))]
    {
        let _ = bytes;
        anyhow::bail!("native tracked-input paths are unsupported on this host")
    }
}

fn frame(input: &mut dyn BufRead) -> CargoResult<Option<Vec<u8>>> {
    let mut bytes = Vec::new();
    let read = (&mut *input)
        .take(MAX_FRAME + 1)
        .read_until(b'\n', &mut bytes)?;
    if read == 0 {
        return Ok(None);
    }
    ensure!(
        bytes.len() as u64 <= MAX_FRAME && bytes.last() == Some(&b'\n'),
        "tracked-input frame is incomplete or exceeds its bound"
    );
    bytes.pop();
    Ok(Some(bytes))
}

fn signed(output: &mut dyn Write, key: &[u8], bytes: &[u8]) -> CargoResult<()> {
    let mut mac = Hmac::<Sha256>::new_from_slice(key)
        .map_err(|_| anyhow::anyhow!("invalid tracked-input channel key"))?;
    mac.update(bytes);
    let envelope = serde_json::json!({
        "body": base64::engine::general_purpose::STANDARD.encode(bytes),
        "mac": hex::encode(mac.finalize().into_bytes()),
    });
    serde_json::to_writer(&mut *output, &envelope)?;
    output.write_all(b"\n")?;
    output.flush()?;
    Ok(())
}

#[inline(never)]
fn parse_batch(bytes: &[u8]) -> CargoResult<Batch> {
    let batch: Batch = serde_json::from_slice(bytes)
        .map_err(|_| anyhow::anyhow!("malformed tracked-input batch"))?;
    ensure!(
        batch.schema == SCHEMA && shaped(&batch.nonce, 32),
        "invalid tracked-input batch identity"
    );
    ensure!(
        !batch.items.is_empty() && batch.items.len() <= MAX_ITEMS,
        "tracked-input batch population exceeds its bound"
    );
    for item in &batch.items {
        let relative = path(&item.path)?;
        ensure!(
            !relative.as_os_str().is_empty()
                && relative
                    .components()
                    .all(|part| matches!(part, Component::Normal(_))),
            "tracked-input filename is not confined relative syntax"
        );
        ensure!(
            matches!(item.mode.as_str(), "100644" | "100755" | "120000")
                && (shaped(&item.oid, 20) || shaped(&item.oid, 32)),
            "unsupported tracked-input mode or object identity"
        );
    }
    Ok(batch)
}

enum BlobHash {
    Sha1(sha1::Sha1),
    Sha256(Sha256),
}

impl BlobHash {
    fn new(oid: &str, size: u64) -> Self {
        let mut hash = if oid.len() == 40 {
            Self::Sha1(sha1::Sha1::new())
        } else {
            Self::Sha256(Sha256::new())
        };
        hash_update(&mut hash, format!("blob {size}\0").as_bytes());
        hash
    }

    fn finish(self) -> String {
        match self {
            Self::Sha1(hash) => hex::encode(hash.finalize()),
            Self::Sha256(hash) => hex::encode(hash.finalize()),
        }
    }
}

#[inline(never)]
fn hash_update(hash: &mut BlobHash, bytes: &[u8]) {
    match hash {
        BlobHash::Sha1(hash) => hash.update(bytes),
        BlobHash::Sha256(hash) => hash.update(bytes),
    }
}

#[cfg(unix)]
fn key(metadata: &Metadata) -> Snapshot {
    use std::os::unix::fs::MetadataExt as _;
    Snapshot {
        dev: metadata.dev(),
        ino: metadata.ino(),
        mode: metadata.mode(),
        bytes: metadata.len(),
        mtime_sec: metadata.mtime(),
        mtime_nsec: metadata.mtime_nsec(),
        ctime_sec: metadata.ctime(),
        ctime_nsec: metadata.ctime_nsec(),
    }
}

/// The exact physical comparison used by the native production batch handler.
/// Timestamps only detect a change during this one read; they never replace it.
#[cfg(unix)]
#[inline(never)]
fn check_file(repo: &Path, item: &Item, buffer: &mut [u8]) -> Result<u64, FileFailure> {
    use std::os::unix::ffi::OsStrExt as _;
    use std::os::unix::fs::{MetadataExt as _, OpenOptionsExt as _};

    let inspect = |_| FileFailure::new("inspect");
    let source = repo.join(path(&item.path).map_err(|_| FileFailure::new("inspect"))?);
    let parent = source
        .parent()
        .ok_or_else(|| FileFailure::new("inspect"))?
        .canonicalize()
        .map_err(inspect)?;
    if !parent.starts_with(repo) {
        return Err(FileFailure::new("parent-escape"));
    }
    let before = fs::symlink_metadata(&source).map_err(inspect)?;
    let (hash, bytes) = if item.mode == "120000" {
        if !before.file_type().is_symlink() {
            return Err(FileFailure::new("symlink-type"));
        }
        let target = fs::read_link(&source).map_err(inspect)?;
        let bytes = target.as_os_str().as_bytes();
        let mut hash = BlobHash::new(&item.oid, bytes.len() as u64);
        hash_update(&mut hash, bytes);
        (hash, bytes.len() as u64)
    } else {
        if !before.is_file() {
            return Err(FileFailure::new("regular-type"));
        }
        if (before.mode() & 0o100 != 0) != (item.mode == "100755") {
            return Err(FileFailure::new("executable-mode"));
        }
        let mut file = OpenOptions::new()
            .read(true)
            .custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK | libc::O_CLOEXEC)
            .open(&source)
            .map_err(inspect)?;
        if key(&file.metadata().map_err(inspect)?) != key(&before) {
            return Err(FileFailure::new("opening-change"));
        }
        let mut hash = BlobHash::new(&item.oid, before.len());
        let mut bytes = 0_u64;
        loop {
            let count = file.read(buffer).map_err(inspect)?;
            if count == 0 {
                break;
            }
            hash_update(&mut hash, &buffer[..count]);
            bytes = bytes
                .checked_add(count as u64)
                .ok_or_else(|| FileFailure::new("inspect"))?;
        }
        if key(&file.metadata().map_err(inspect)?) != key(&before) {
            return Err(FileFailure::new("reading-change"));
        }
        (hash, bytes)
    };
    if key(&fs::symlink_metadata(&source).map_err(inspect)?) != key(&before) {
        return Err(FileFailure::new("inspection-change"));
    }
    let digest = hash.finish();
    if digest != item.oid {
        return Err(if item.mode == "120000" {
            FileFailure::new("link-bytes")
        } else {
            FileFailure {
                kind: "regular-bytes",
                digest: Some(digest),
                stat: Some(key(&before)),
            }
        });
    }
    Ok(bytes)
}

#[cfg(not(unix))]
fn check_file(_: &Path, _: &Item, _: &mut [u8]) -> Result<u64, FileFailure> {
    Err(FileFailure::new("inspect"))
}

#[inline(never)]
fn check_batch(batch: &Batch, jobs: usize) -> CargoResult<(usize, u64, Vec<IndexedFailure>)> {
    let repo = path(&batch.repo)?;
    if !repo.is_absolute() || repo.canonicalize().ok().as_ref() != Some(&repo) {
        return Ok((
            batch.items.len(),
            0,
            vec![IndexedFailure {
                index: 0,
                failure: FileFailure::new("root-change"),
            }],
        ));
    }
    let width = jobs.min(batch.items.len());
    let size = batch.items.len().div_ceil(width);
    let results = std::thread::scope(|scope| {
        let threads = batch
            .items
            .chunks(size)
            .map(|items| {
                let repo = &repo;
                scope.spawn(move || {
                    let mut buffer = [0; 64 * 1024];
                    items
                        .iter()
                        .map(|item| check_file(repo, item, &mut buffer))
                        .collect::<Vec<_>>()
                })
            })
            .collect::<Vec<_>>();
        threads
            .into_iter()
            .map(|thread| thread.join())
            .collect::<Vec<_>>()
    });
    let mut checked = 0;
    let mut bytes = 0_u64;
    let mut failures = Vec::new();
    for group in results {
        for result in group.map_err(|_| anyhow::anyhow!("tracked-input reader thread failed"))? {
            match result {
                Ok(count) => {
                    bytes = bytes
                        .checked_add(count)
                        .context("tracked-input batch byte count overflow")?;
                }
                Err(failure) => failures.push(IndexedFailure {
                    index: checked,
                    failure,
                }),
            }
            checked += 1;
        }
    }
    Ok((checked, bytes, failures))
}

/// Serve one original, bounded reader lifetime. No automatic restart or saved
/// response is a capability. Package/image admission belongs to the caller;
/// these source IDs and signed responses only bind compatibility and messages.
pub fn serve_tracked_inputs(input: &mut dyn BufRead, output: &mut dyn Write) -> CargoResult<()> {
    use trust_resource_provenance::program::{CURRENT_CODE_POLICY, HeldProgram};

    let first = frame(input)?.context("missing tracked-input start frame")?;
    let start: Start = serde_json::from_slice(&first)
        .map_err(|_| anyhow::anyhow!("malformed tracked-input start frame"))?;
    ensure!(
        start.schema == SCHEMA
            && start.reader == tracked_input_reader_identity()
            && shaped(&start.key, 32)
            && shaped(&start.image_sha256, 32)
            && (1..=MAX_JOBS).contains(&start.jobs),
        "unsupported tracked-input start profile"
    );
    let key = hex::decode(&start.key).map_err(|_| anyhow::anyhow!("invalid channel key"))?;
    let expected: [u8; 32] = hex::decode(&start.image_sha256)
        .map_err(|_| anyhow::anyhow!("invalid image digest"))?
        .try_into()
        .map_err(|_| anyhow::anyhow!("invalid image digest width"))?;
    let root = path(&start.root)?;
    let executable = path(&start.executable)?;
    let deadline = Instant::now() + Duration::from_secs(6 * 60 * 60);
    let program = Arc::new(HeldProgram::open(&root, &executable, &expected, deadline)?);
    let current = program.bind_current_code(
        &[
            serve_tracked_inputs as *const (),
            parse_batch as *const (),
            check_batch as *const (),
            check_file as *const (),
            hash_update as *const (),
        ],
        deadline,
    )?;
    let ready = serde_json::to_vec(&Ready {
        schema: SCHEMA,
        reader: tracked_input_reader_identity(),
        runtime_policy: CURRENT_CODE_POLICY,
        runtime_identity: hex::encode(current.content_identity()),
    })?;
    signed(output, &key, &ready)?;
    while let Some(bytes) = frame(input)? {
        current.validate(deadline)?;
        let batch = parse_batch(&bytes)?;
        let (checked, count, failures) = check_batch(&batch, start.jobs)?;
        current.validate(deadline)?;
        let answer = serde_json::to_vec(&Answer {
            schema: SCHEMA,
            nonce: &batch.nonce,
            request_sha256: hex::encode(Sha256::digest(&bytes)),
            checked,
            bytes: count,
            failures,
        })?;
        signed(output, &key, &answer)?;
    }
    current.validate(deadline)?;
    Ok(())
}

#[cfg(test)]
mod tests;
