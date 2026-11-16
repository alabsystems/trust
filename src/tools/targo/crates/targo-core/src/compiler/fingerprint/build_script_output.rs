//! Trust: byte integrity for cached build-script output.
//!
//! Directives and relocation describe original process bytes. The generated
//! tree is a stable post-success filesystem observation, captured only by the
//! dirty producer path. This is cache consistency, not hermetic execution,
//! proof evidence or input-completeness authority.

use std::fs::{self, Metadata, OpenOptions};
use std::io::{Read as _, Write as _};
use std::path::{Path, PathBuf};

use anyhow::{Context as _, bail};
use cargo_util::Sha256;
use serde::{Deserialize, Serialize};

use super::build_script_generation::{RetiredGeneration, reset};
use super::build_script_inputs::{Snapshot, capture_tree};
use crate::CargoResult;
use crate::util::file_identity::{metadata_is_plain_file, opened_file_identity};

const SCHEMA: u32 = 2;
const MAX_RECEIPT: u64 = 16 * 1024;
const MAX_STDOUT: u64 = 16 * 1024 * 1024;
const MAX_ROOT: u64 = 32 * 1024;

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Receipt {
    schema: u32,
    unit: String,
    outputs: [Output; 2],
    generated: Generated,
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Generated {
    path_sha256: String,
    snapshot: Snapshot,
}

#[derive(Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct Output {
    path_sha256: String,
    size: u64,
    sha256: String,
}

// Trust: this key binds planning data to the exact receipt checked at the
// final freshness gate. It is never persisted or generation authority.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::compiler) struct ReceiptKey(String);

/// Verified control bytes for dependency planning, not generated-tree reuse.
pub(in crate::compiler) struct Controls {
    stdout: Vec<u8>,
    root_output: Vec<u8>,
    receipt: Receipt,
    key: ReceiptKey,
}

impl Controls {
    pub(in crate::compiler) fn into_parts(self) -> (Vec<u8>, Vec<u8>, ReceiptKey) {
        (self.stdout, self.root_output, self.key)
    }
}

/// The final gate must validate the receipt that supplied dependency planning.
#[derive(Clone)]
pub(in crate::compiler) struct PlannedOutput {
    output: CachedOutput,
    key: Option<ReceiptKey>,
}

impl PlannedOutput {
    pub(in crate::compiler) fn receipt_path(&self) -> &Path {
        self.output.receipt_path()
    }

    pub(in crate::compiler) fn read(&self) -> CargoResult<()> {
        let key = self
            .key
            .as_ref()
            .context("no verified build-script planning receipt")?;
        self.output.read_matching(key).map(|_| ())
    }
}

fn path_digest(path: &Path) -> String {
    Sha256::new()
        .update(path.as_os_str().as_encoded_bytes())
        .finish_hex()
}

fn output(path: &Path, bytes: &[u8]) -> Output {
    Output {
        path_sha256: path_digest(path),
        size: bytes.len() as u64,
        sha256: Sha256::new().update(bytes).finish_hex(),
    }
}

fn unchanged(before: &Metadata, after: &Metadata) -> bool {
    if !metadata_is_plain_file(after)
        || before.len() != after.len()
        || !matches!((before.modified(),after.modified()),(Ok(a),Ok(b)) if a==b)
    {
        return false;
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt as _;
        before.dev() == after.dev()
            && before.ino() == after.ino()
            && before.mode() == after.mode()
            && before.uid() == after.uid()
            && before.gid() == after.gid()
            && before.ctime() == after.ctime()
            && before.ctime_nsec() == after.ctime_nsec()
    }
    #[cfg(not(unix))]
    {
        before.permissions().readonly() == after.permissions().readonly()
    }
}

fn read_stable(path: &Path, limit: u64) -> CargoResult<Vec<u8>> {
    let named = fs::symlink_metadata(path)?;
    if !metadata_is_plain_file(&named) || named.len() > limit {
        bail!("invalid cached build-script file");
    }
    let mut options = OpenOptions::new();
    options.read(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt as _;
        options.custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK | libc::O_CLOEXEC);
    }
    let mut file = options.open(path)?;
    let before = file.metadata()?;
    if !unchanged(&named, &before) {
        bail!("cached build-script file changed before reading");
    }
    let identity = opened_file_identity(&file)?;
    let mut bytes = Vec::new();
    (&mut file).take(limit + 1).read_to_end(&mut bytes)?;
    if bytes.len() as u64 != before.len()
        || bytes.len() as u64 > limit
        || !unchanged(&before, &file.metadata()?)
        || !unchanged(&before, &fs::symlink_metadata(path)?)
        || identity != opened_file_identity(&options.open(path)?)?
    {
        bail!("cached build-script file changed while reading");
    }
    Ok(bytes)
}

/// Replace a cache leaf without following a corrupt destination symlink.
pub(in crate::compiler) fn write_atomic(path: &Path, bytes: &[u8]) -> CargoResult<()> {
    let parent = path
        .parent()
        .context("build-script cache file has no parent")?;
    let mut temporary = tempfile::NamedTempFile::new_in(parent)?;
    temporary.write_all(bytes)?;
    temporary.as_file().sync_all()?;
    temporary.persist(path).map_err(|error| error.error)?;
    Ok(())
}

#[derive(Clone)]
pub(in crate::compiler) struct CachedOutput {
    receipt: PathBuf,
    unit: String,
    stdout: PathBuf,
    root_output: PathBuf,
    generated: PathBuf,
}

impl CachedOutput {
    pub(in crate::compiler) fn planned(self, key: Option<ReceiptKey>) -> PlannedOutput {
        PlannedOutput { output: self, key }
    }

    pub(in crate::compiler) fn new(
        root: &Path,
        unit: String,
        stdout: &Path,
        root_output: &Path,
        generated: &Path,
    ) -> Self {
        Self {
            receipt: root.join("output-integrity-v2.json"),
            unit,
            stdout: stdout.to_owned(),
            root_output: root_output.to_owned(),
            generated: generated.to_owned(),
        }
    }

    pub(in crate::compiler) fn receipt_path(&self) -> &Path {
        &self.receipt
    }

    pub(in crate::compiler) fn invalidate(&self) -> CargoResult<()> {
        match fs::remove_file(&self.receipt) {
            Ok(()) => Ok(()),
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(()),
            Err(error) => Err(error.into()),
        }
    }

    // Trust: a write-once/incremental script must never inherit unreceipted
    // generated bytes and bless them merely by returning successfully again.
    // Keep a valid prior tree for ordinary input-driven rebuilds, but isolate
    // any invalid generation at the actual execution boundary.
    pub(in crate::compiler) fn prepare(&self) -> CargoResult<Option<RetiredGeneration>> {
        let valid = self.read().is_ok();
        self.invalidate()?;
        if valid {
            Ok(None)
        } else {
            reset(&self.generated).map(Some)
        }
    }

    pub(in crate::compiler) fn publish(
        &self,
        stdout: &[u8],
        root_output: &[u8],
    ) -> CargoResult<()> {
        if stdout.len() as u64 > MAX_STDOUT || root_output.len() as u64 > MAX_ROOT {
            bail!("build-script output is too large to cache");
        }
        let receipt = Receipt {
            schema: SCHEMA,
            unit: self.unit.clone(),
            outputs: [
                output(&self.stdout, stdout),
                output(&self.root_output, root_output),
            ],
            generated: Generated {
                path_sha256: path_digest(&self.generated),
                snapshot: capture_tree(&self.generated)?,
            },
        };
        let bytes = serde_json::to_vec(&receipt)?;
        if bytes.len() as u64 > MAX_RECEIPT {
            bail!("build-script output receipt exceeds bound");
        }
        write_atomic(&self.receipt, &bytes)
    }

    pub(in crate::compiler) fn read(&self) -> CargoResult<(Vec<u8>, Vec<u8>)> {
        self.read_full(None)
    }

    pub(in crate::compiler) fn read_matching(
        &self,
        key: &ReceiptKey,
    ) -> CargoResult<(Vec<u8>, Vec<u8>)> {
        self.read_full(Some(key))
    }

    fn read_full(&self, expected: Option<&ReceiptKey>) -> CargoResult<(Vec<u8>, Vec<u8>)> {
        let controls = self.read_controls()?;
        if expected.is_some_and(|key| key != &controls.key) {
            bail!("build-script receipt changed after dependency planning");
        }
        if controls.receipt.generated.snapshot != capture_tree(&self.generated)? {
            bail!("cached build-script generated tree changed");
        }
        Ok((controls.stdout, controls.root_output))
    }

    // Trust: dependency planning needs original directives, not admission of
    // generated files. The full tree remains checked at the final freshness
    // gate and the actual dirty/reset boundary.
    pub(in crate::compiler) fn read_controls(&self) -> CargoResult<Controls> {
        let bytes = read_stable(&self.receipt, MAX_RECEIPT)?;
        let key = ReceiptKey(Sha256::new().update(&bytes).finish_hex());
        let receipt: Receipt = serde_json::from_slice(&bytes)?;
        if receipt.schema != SCHEMA
            || receipt.unit != self.unit
            || receipt.outputs[0].path_sha256 != path_digest(&self.stdout)
            || receipt.outputs[1].path_sha256 != path_digest(&self.root_output)
            || receipt.outputs[0].size > MAX_STDOUT
            || receipt.outputs[1].size > MAX_ROOT
            || receipt.generated.path_sha256 != path_digest(&self.generated)
            || !receipt.generated.snapshot.valid()
        {
            bail!("build-script output receipt does not match this unit and inventory");
        }
        let stdout = read_stable(&self.stdout, MAX_STDOUT)?;
        let root_output = read_stable(&self.root_output, MAX_ROOT)?;
        if receipt.outputs
            != [
                output(&self.stdout, &stdout),
                output(&self.root_output, &root_output),
            ]
        {
            bail!("cached build-script bytes changed");
        }
        Ok(Controls {
            stdout,
            root_output,
            receipt,
            key,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn planning_controls_cannot_admit_changed_generated_bytes() {
        let world = tempfile::tempdir().unwrap();
        let stdout = world.path().join("output");
        let root = world.path().join("root-output");
        let generated = world.path().join("out");
        fs::create_dir(&generated).unwrap();
        let file = generated.join("generated.rs");
        fs::write(&file, b"const VALUE:u32=111;").unwrap();
        write_atomic(&stdout, b"original").unwrap();
        write_atomic(&root, b"out").unwrap();
        let guard = CachedOutput::new(world.path(), "unit".into(), &stdout, &root, &generated);
        guard.publish(b"original", b"out").unwrap();
        let (bytes, _, key) = guard.read_controls().unwrap().into_parts();
        assert_eq!(bytes, b"original");
        let planned = guard.clone().planned(Some(key.clone()));
        assert!(planned.read().is_ok());
        let mtime = filetime::FileTime::from_last_modification_time(&fs::metadata(&file).unwrap());
        fs::write(&file, b"const VALUE:u32=222;").unwrap();
        filetime::set_file_mtime(&file, mtime).unwrap();
        assert_eq!(guard.read_controls().unwrap().into_parts().2, key);
        assert!(
            planned.read().is_err(),
            "planning is not generation authority"
        );
        assert!(guard.clone().planned(None).read().is_err());
    }

    #[test]
    fn final_generation_admission_binds_the_original_planning_receipt() {
        let world = tempfile::tempdir().unwrap();
        let stdout = world.path().join("output");
        let root = world.path().join("root-output");
        let generated = world.path().join("out");
        fs::create_dir(&generated).unwrap();
        write_atomic(&stdout, b"VALUE=111").unwrap();
        write_atomic(&root, b"out").unwrap();
        let guard = CachedOutput::new(world.path(), "unit".into(), &stdout, &root, &generated);
        guard.publish(b"VALUE=111", b"out").unwrap();
        let (original, _, key) = guard.read_controls().unwrap().into_parts();
        write_atomic(&stdout, b"VALUE=222").unwrap();
        guard.publish(b"VALUE=222", b"out").unwrap();
        let changed = guard.read_controls().unwrap().into_parts().2;
        assert_ne!(key, changed);
        assert_eq!(original, b"VALUE=111");
        assert!(guard.read_matching(&key).is_err());
        assert!(guard.clone().planned(Some(key)).read().is_err());
        assert_eq!(guard.read_matching(&changed).unwrap().0, b"VALUE=222");
    }

    #[test]
    fn only_original_bytes_are_receipted_and_read_buffers_are_verified() {
        let world = tempfile::tempdir().unwrap();
        let stdout = world.path().join("output");
        let root = world.path().join("root-output");
        let generated = world.path().join("out");
        fs::create_dir(&generated).unwrap();
        let guard = CachedOutput::new(
            world.path(),
            "1234567890abcdef".into(),
            &stdout,
            &root,
            &generated,
        );
        write_atomic(&stdout, b"VALUE=222").unwrap();
        write_atomic(&root, b"original/out").unwrap();
        guard.publish(b"VALUE=111", b"original/out").unwrap();
        assert!(
            guard.read().is_err(),
            "post-hoc disk mutation must not be blessed"
        );
        write_atomic(&stdout, b"VALUE=111").unwrap();
        assert_eq!(
            guard.read().unwrap(),
            (b"VALUE=111".to_vec(), b"original/out".to_vec())
        );
        let modified =
            filetime::FileTime::from_last_modification_time(&fs::metadata(&stdout).unwrap());
        fs::write(&stdout, b"VALUE=222").unwrap();
        filetime::set_file_mtime(&stdout, modified).unwrap();
        assert!(guard.read().is_err());
        write_atomic(&stdout, b"VALUE=111").unwrap();
        write_atomic(&root, b"tampered/out").unwrap();
        assert!(guard.read().is_err());
    }

    #[test]
    fn missing_old_malformed_and_oversized_receipts_are_misses() {
        let world = tempfile::tempdir().unwrap();
        let stdout = world.path().join("output");
        let root = world.path().join("root-output");
        let generated = world.path().join("out");
        fs::create_dir(&generated).unwrap();
        let guard = CachedOutput::new(
            world.path(),
            "1234567890abcdef".into(),
            &stdout,
            &root,
            &generated,
        );
        write_atomic(&stdout, b"original").unwrap();
        write_atomic(&root, b"out").unwrap();
        assert!(guard.read().is_err());
        for bytes in [b"{".as_slice(), b"{}".as_slice()] {
            fs::write(guard.receipt_path(), bytes).unwrap();
            assert!(guard.read().is_err());
        }
        guard.publish(b"original", b"out").unwrap();
        let mut receipt: Receipt =
            serde_json::from_slice(&fs::read(guard.receipt_path()).unwrap()).unwrap();
        receipt.schema = 0;
        fs::write(guard.receipt_path(), serde_json::to_vec(&receipt).unwrap()).unwrap();
        assert!(guard.read().is_err());
        fs::File::create(guard.receipt_path())
            .unwrap()
            .set_len(MAX_RECEIPT + 1)
            .unwrap();
        assert!(guard.read().is_err());
    }

    #[test]
    fn generated_inventory_checks_content_membership_and_selected_path() {
        let world = tempfile::tempdir().unwrap();
        let stdout = world.path().join("output");
        let root = world.path().join("root-output");
        let generated = world.path().join("out");
        fs::create_dir(&generated).unwrap();
        let guard = CachedOutput::new(
            world.path(),
            "1234567890abcdef".into(),
            &stdout,
            &root,
            &generated,
        );
        write_atomic(&stdout, b"original").unwrap();
        write_atomic(&root, b"out").unwrap();
        let file = generated.join("generated.rs");
        fs::write(&file, b"const VALUE:u32=111;").unwrap();
        guard.publish(b"original", b"out").unwrap();
        assert!(guard.read().is_ok());
        let mtime = filetime::FileTime::from_last_modification_time(&fs::metadata(&file).unwrap());
        fs::write(&file, b"const VALUE:u32=222;").unwrap();
        filetime::set_file_mtime(&file, mtime).unwrap();
        assert!(guard.read().is_err());
        fs::write(&file, b"const VALUE:u32=111;").unwrap();
        assert!(guard.read().is_ok(), "content restoration is a valid hit");
        let extra = generated.join("extra");
        fs::create_dir(&extra).unwrap();
        assert!(guard.read().is_err(), "empty directory membership matters");
        fs::remove_dir(&extra).unwrap();
        fs::rename(&file, generated.join("renamed.rs")).unwrap();
        assert!(guard.read().is_err(), "relative names matter");
        fs::rename(generated.join("renamed.rs"), &file).unwrap();
        fs::remove_file(&file).unwrap();
        assert!(guard.read().is_err(), "deleted outputs cannot be reused");
        let mut other = guard.clone();
        other.generated = world.path().join("other-out");
        fs::create_dir(&other.generated).unwrap();
        fs::write(
            other.generated.join("generated.rs"),
            b"const VALUE:u32=111;",
        )
        .unwrap();
        assert!(
            other.read().is_err(),
            "the selected path is independently bound"
        );
        fs::remove_dir(&generated).unwrap();
        assert!(guard.read().is_err(), "a missing root is not an empty tree");
    }

    #[cfg(unix)]
    #[test]
    fn unsupported_generated_trees_cannot_publish_a_receipt_or_touch_a_victim() {
        let world = tempfile::tempdir().unwrap();
        let generated = world.path().join("out");
        let victim = world.path().join("victim");
        fs::create_dir(&victim).unwrap();
        fs::write(victim.join("value"), b"untouched").unwrap();
        let guard = CachedOutput::new(
            world.path(),
            "1234567890abcdef".into(),
            &world.path().join("output"),
            &world.path().join("root-output"),
            &generated,
        );
        std::os::unix::fs::symlink(&victim, &generated).unwrap();
        assert!(guard.publish(b"stdout", b"out").is_err());
        assert!(!guard.receipt_path().exists());
        fs::remove_file(&generated).unwrap();
        fs::create_dir(&generated).unwrap();
        std::os::unix::fs::symlink(victim.join("value"), generated.join("link")).unwrap();
        assert!(guard.publish(b"stdout", b"out").is_err());
        assert!(!guard.receipt_path().exists());
        fs::remove_file(generated.join("link")).unwrap();
        fs::File::create(generated.join("oversized"))
            .unwrap()
            .set_len(512 * 1024 * 1024 + 1)
            .unwrap();
        assert!(guard.publish(b"stdout", b"out").is_err());
        assert!(!guard.receipt_path().exists());
        assert_eq!(fs::read(victim.join("value")).unwrap(), b"untouched");
    }

    #[test]
    fn dirty_execution_keeps_valid_state_but_isolates_invalid_generated_bytes() {
        let world = tempfile::tempdir().unwrap();
        let stdout = world.path().join("output");
        let root = world.path().join("root-output");
        let generated = world.path().join("out");
        fs::create_dir(&generated).unwrap();
        let file = generated.join("generated.rs");
        fs::write(&file, b"const VALUE:u32=111;").unwrap();
        fs::write(generated.join("incremental-state"), b"keep").unwrap();
        write_atomic(&stdout, b"original").unwrap();
        write_atomic(&root, b"out").unwrap();
        let guard = CachedOutput::new(
            world.path(),
            "1234567890abcdef".into(),
            &stdout,
            &root,
            &generated,
        );
        guard.publish(b"original", b"out").unwrap();
        assert!(guard.prepare().unwrap().is_none());
        assert_eq!(
            fs::read(generated.join("incremental-state")).unwrap(),
            b"keep"
        );
        assert!(
            !guard.receipt_path().exists(),
            "dirty execution invalidates the fact"
        );
        guard.publish(b"original", b"out").unwrap();
        let mtime = filetime::FileTime::from_last_modification_time(&fs::metadata(&file).unwrap());
        fs::write(&file, b"const VALUE:u32=222;").unwrap();
        filetime::set_file_mtime(&file, mtime).unwrap();
        let retired = guard.prepare().unwrap();
        assert!(retired.is_some());
        assert!(fs::read_dir(&generated).unwrap().next().is_none());
        assert!(!guard.receipt_path().exists());
        // A write-once producer now sees an absent file rather than inherited
        // poisoned bytes. Its next successful publication records fresh data.
        fs::write(&file, b"const VALUE:u32=111;").unwrap();
        guard.publish(b"original", b"out").unwrap();
        drop(retired);
        assert!(guard.read().is_ok());
    }

    #[cfg(unix)]
    #[test]
    fn symlink_cache_leaves_are_replaced_without_writing_the_victim() {
        let world = tempfile::tempdir().unwrap();
        let victim = world.path().join("victim");
        let stdout = world.path().join("output");
        write_atomic(&victim, b"untouched").unwrap();
        std::os::unix::fs::symlink(&victim, &stdout).unwrap();
        assert!(read_stable(&stdout, MAX_STDOUT).is_err());
        write_atomic(&stdout, b"actual output").unwrap();
        assert_eq!(fs::read(&victim).unwrap(), b"untouched");
        assert_eq!(read_stable(&stdout, MAX_STDOUT).unwrap(), b"actual output");
    }
}
