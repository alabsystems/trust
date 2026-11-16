// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

//! All-candidate readsets for a qualified local Unix native-tool transport.
//!
//! This module does not resolve an execvp winner, change argv0, execute a tool,
//! or establish successful compilation. It observes every candidate, including
//! denied/missing entries and entries after a possible match. Present candidates
//! must be regular native-header files; scripts/interpreters are unsupported.
//! Either set-ID mode bit refuses the entire recipe, including lower-priority
//! candidates, rather than assuming their execution retains parent credentials.
//! Consumers retain their actual command and owning wait, and publish these
//! DATA records only after that execution succeeds. Decoding cannot create a
//! live window or prove that a compiler reported a complete tool inventory.
//!
//! The host, mount/MAC policy, security namespaces, credentials and capabilities
//! must remain fixed. Linux overridden fsuid/fsgid profiles are excluded unless
//! independently captured/held fixed, as required by `effective_access`. Tool
//! subcommands, loaded libraries and execution-time system policy are outside
//! this readset. Parent matching is conditional on unchanged compiler identity
//! and semantic command profile, not a proof of child-environment derivation.

use std::ffi::OsStr;
#[cfg(unix)]
use std::ffi::OsString;
use std::fs::OpenOptions;
use std::io::{self, Read as _};
use std::path::{Path, PathBuf};

use anyhow::{Context as _, Result, ensure};
use serde::{Deserialize, Serialize};
use trust_sha2::Digest as _;

use crate::effective_access;
use crate::observation::{self, Snapshot, Window};

pub const MAX_RECORD_BYTES: usize = 16 * 1024 * 1024;
pub const MAX_RECORDS: usize = 64;
pub const DEP_INFO_PREFIX: &str = "# trust-tool-inputs-v1:";
pub const UNAVAILABLE: &str = "unavailable";
const RECORD_SCHEMA: &str = "trust-tool-lookup-v1";
const INPUTS_SCHEMA: &str = "trust-tool-inputs-v1";

/// Explicitly selected by the actual local command owner. This is a supported
/// observation profile, not transport authentication or an execution grant.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum Profile {
    LocalUnixNativeV1,
    /// The local std::process::Command path with resource-v2 FD custody and
    /// owning waits. FD retention changes neither PATH, cwd nor credentials;
    /// the compiler's mode may still choose a different paired linker.
    LocalUnixNativeResourceV2,
}

/// Exact requested command context and its complete ordered candidate list.
/// Raw bytes are retained without canonicalization or changing argv0.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Context {
    program: Vec<u8>,
    cwd: Vec<u8>,
    child_path: Option<Vec<u8>>,
    parent_path: Option<Vec<u8>>,
    profile: Profile,
    candidates: Vec<Vec<u8>>,
}

impl Context {
    pub fn new(
        program: &OsStr,
        cwd: &Path,
        child_path: Option<&OsStr>,
        parent_path: Option<&OsStr>,
        profile: Profile,
    ) -> Result<Self> {
        let mut context = Self {
            program: raw(program)?,
            cwd: raw(cwd.as_os_str())?,
            child_path: child_path.map(raw).transpose()?,
            parent_path: parent_path.map(raw).transpose()?,
            profile,
            candidates: Vec::new(),
        };
        context.candidates = context.derive_candidates()?;
        context.validate()?;
        Ok(context)
    }

    pub fn program_bytes(&self) -> &[u8] {
        &self.program
    }
    pub fn cwd_bytes(&self) -> &[u8] {
        &self.cwd
    }
    pub fn child_path_bytes(&self) -> Option<&[u8]> {
        self.child_path.as_deref()
    }
    pub fn parent_path_bytes(&self) -> Option<&[u8]> {
        self.parent_path.as_deref()
    }
    pub fn profile(&self) -> Profile {
        self.profile
    }
    pub fn candidates(&self) -> &[Vec<u8>] {
        &self.candidates
    }

    pub fn matches_parent(
        &self,
        cwd: &Path,
        parent_path: Option<&OsStr>,
        profile: Profile,
    ) -> bool {
        let Ok(cwd) = raw(cwd.as_os_str()) else {
            return false;
        };
        let Ok(parent_path) = parent_path.map(raw).transpose() else {
            return false;
        };
        self.validate().is_ok()
            && self.cwd == cwd
            && self.parent_path == parent_path
            && self.profile == profile
    }

    pub fn begin(&self) -> Result<Pending> {
        self.validate()?;
        let paths = self.paths()?;
        let before = observation::observe_attempt(Path::new("/"), &paths, false).result?;
        let (filesystem, window) = before.into_parts();
        let access = capture_access(&paths)?;
        // Header reads and access checks belong to the original window too.
        // No after-the-fact window can replace those initial stamps.
        let after = observation::observe_attempt(Path::new("/"), &paths, false).result?;
        ensure!(
            window.covers(&after),
            "tool namespace changed during admission"
        );
        ensure!(
            after.into_snapshot() == filesystem,
            "tool content changed during admission"
        );
        let record = Record {
            schema: RECORD_SCHEMA.into(),
            context: self.clone(),
            filesystem,
            access,
        };
        record.validate()?;
        Ok(Pending { record, window })
    }

    fn paths(&self) -> Result<Vec<PathBuf>> {
        self.candidates
            .iter()
            .map(|path| path_from_raw(path))
            .collect()
    }

    fn derive_candidates(&self) -> Result<Vec<Vec<u8>>> {
        ensure!(
            matches!(std::env::consts::OS, "macos" | "linux"),
            "unsupported tool host"
        );
        bounded_bytes(&self.program, effective_access::MAX_PATH_BYTES, false)?;
        absolute(&self.cwd)?;
        for value in [&self.child_path, &self.parent_path].into_iter().flatten() {
            bounded_bytes(value, effective_access::MAX_TOTAL_PATH_BYTES, true)?;
        }
        if self.program.starts_with(b"/") {
            absolute(&self.program)?;
            return Ok(vec![self.program.clone()]);
        }
        ensure!(
            !self.program.contains(&b'/'),
            "relative tool program is unsupported"
        );
        let path = self
            .child_path
            .as_ref()
            .context("bare tool has no final child PATH")?;
        let mut candidates = Vec::new();
        let mut total = 0_usize;
        for directory in path.split(|byte| *byte == b':') {
            ensure!(
                candidates.len() < effective_access::MAX_PATHS,
                "too many tool candidates"
            );
            absolute(directory)?;
            let length = directory
                .len()
                .checked_add(1)
                .and_then(|n| n.checked_add(self.program.len()))
                .context("tool path length overflow")?;
            ensure!(
                length <= effective_access::MAX_PATH_BYTES,
                "tool candidate is too long"
            );
            total = total
                .checked_add(length)
                .context("tool path sum overflow")?;
            ensure!(
                total <= effective_access::MAX_TOTAL_PATH_BYTES,
                "tool path sum is too large"
            );
            let mut candidate = Vec::new();
            candidate.try_reserve_exact(length)?;
            candidate.extend_from_slice(directory);
            candidate.push(b'/');
            candidate.extend_from_slice(&self.program);
            candidates.push(candidate);
        }
        Ok(candidates)
    }

    fn validate(&self) -> Result<()> {
        ensure!(
            self.candidates == self.derive_candidates()?,
            "derived tool candidates differ"
        );
        Ok(())
    }
}

/// Factory-only original stamps held across the actual owner's external wait.
/// It cannot be decoded, cloned, or constructed from a saved record.
pub struct Pending {
    record: Record,
    window: Window,
}

impl Pending {
    /// Consume after the real owning wait. The caller separately enforces real
    /// child success and its full compilation/input/output publication policy.
    pub fn finish(self) -> Result<Record> {
        self.finish_with(capture_access)
    }

    fn finish_with(
        self,
        capture: impl FnOnce(&[PathBuf]) -> Result<effective_access::Snapshot>,
    ) -> Result<Record> {
        let paths = self.record.context.paths()?;
        let access = capture(&paths)?;
        // Keep the original admission window open through every final header
        // read and access/credential query. A replacement window here could
        // accept content or namespace changes restored during those reads.
        let after = observation::observe_attempt(Path::new("/"), &paths, false).result?;
        ensure!(
            self.window.covers(&after),
            "tool namespace changed during execution"
        );
        ensure!(
            after.into_snapshot() == self.record.filesystem,
            "tool content changed during execution"
        );
        ensure!(
            access == self.record.access,
            "tool access or credentials changed during execution"
        );
        self.record.validate()?;
        Ok(self.record)
    }
}

/// Persistable observation DATA, with no live window or successful-exec claim.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Record {
    schema: String,
    context: Context,
    filesystem: Snapshot,
    access: effective_access::Snapshot,
}

impl Record {
    pub fn context(&self) -> &Context {
        &self.context
    }

    pub fn encode(&self) -> Result<Vec<u8>> {
        self.validate()?;
        encode_bounded(self)
    }

    pub fn decode(bytes: &[u8]) -> Result<Self> {
        let record: Self = decode_bounded(bytes)?;
        record.validate()?;
        ensure!(record.encode()? == bytes, "noncanonical tool record");
        Ok(record)
    }

    pub fn binding(&self) -> Result<[u8; 32]> {
        Ok(binding(b"trust-native-tool-readset-v1", &self.encode()?))
    }

    pub fn current(&self, context: &Context) -> Result<bool> {
        self.validate()?;
        context.validate()?;
        if &self.context != context {
            return Ok(false);
        }
        let current = context.begin()?.finish()?;
        Ok(current == *self)
    }

    fn validate(&self) -> Result<()> {
        ensure!(
            self.schema == RECORD_SCHEMA,
            "unsupported tool record schema"
        );
        self.context.validate()?;
        ensure!(self.filesystem.valid(), "invalid filesystem snapshot");
        ensure!(self.access.valid(), "invalid effective-access snapshot");
        ensure!(
            self.access.entries().len() == self.context.candidates.len(),
            "tool access count differs"
        );
        ensure!(
            self.access
                .entries()
                .iter()
                .zip(&self.context.candidates)
                .all(|(entry, path)| entry.path_bytes() == path),
            "tool access paths differ"
        );
        Ok(())
    }
}

/// Terminal DATA for one successfully completed compiler unit. Empty records
/// explicitly mean no observed native links; missing/unavailable is not empty.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ToolInputs {
    schema: String,
    records: Vec<Record>,
}

/// Transient point-freshness observations for this invocation only. These
/// factory-held windows cannot be decoded, cloned, or restored from records.
/// They confer no child-execution, receipt-publication or proof authority.
pub struct CurrentToolInputs {
    binding: [u8; 32],
    observations: Vec<CurrentToolInput>,
}

struct CurrentToolInput {
    window: Window,
    access: effective_access::Snapshot,
    paths: Vec<PathBuf>,
}

impl CurrentToolInputs {
    /// Binding of the complete, freshly compared stored envelope.
    pub fn binding(&self) -> [u8; 32] {
        self.binding
    }

    /// Check current access/credentials, then the original namespace and file
    /// stamps. No native headers or file contents are reread. The supported
    /// host/credential/security profile must remain fixed as documented above.
    pub fn is_current(&self) -> Result<bool> {
        self.is_current_with(effective_access::capture)
    }

    fn is_current_with(
        &self,
        mut capture: impl FnMut(&[PathBuf]) -> Result<effective_access::Snapshot>,
    ) -> Result<bool> {
        for observation in &self.observations {
            if capture(&observation.paths)? != observation.access {
                return Ok(false);
            }
        }
        // All access queries must precede these original-window checks,
        // including when later records share paths with earlier records.
        Ok(self
            .observations
            .iter()
            .all(|observation| observation.window.is_current()))
    }
}

impl ToolInputs {
    pub fn from_records(records: Vec<Record>) -> Result<Self> {
        let inputs = Self {
            schema: INPUTS_SCHEMA.into(),
            records,
        };
        inputs.encode()?;
        Ok(inputs)
    }

    pub fn records(&self) -> &[Record] {
        &self.records
    }

    pub fn encode(&self) -> Result<Vec<u8>> {
        ensure!(
            self.schema == INPUTS_SCHEMA,
            "unsupported tool-input schema"
        );
        ensure!(self.records.len() <= MAX_RECORDS, "too many tool records");
        for record in &self.records {
            record.validate()?;
        }
        encode_bounded(self)
    }

    pub fn decode(bytes: &[u8]) -> Result<Self> {
        let inputs: Self = decode_bounded(bytes)?;
        ensure!(
            inputs.encode()? == bytes,
            "noncanonical tool-input envelope"
        );
        Ok(inputs)
    }

    pub fn binding(&self) -> Result<[u8; 32]> {
        Ok(binding(b"trust-native-tool-inputs-v1", &self.encode()?))
    }

    pub fn current(&self, contexts: &[Context]) -> Result<bool> {
        self.encode()?;
        if self.records.len() != contexts.len() {
            return Ok(false);
        }
        for (record, context) in self.records.iter().zip(contexts) {
            if !record.current(context)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// Compare decoded DATA with fresh complete observations and retain their
    /// original live windows for cheap point-freshness checks in this process.
    /// An unfinished Pending is never converted into a published Record.
    pub fn check_current(&self, contexts: &[Context]) -> Result<CurrentToolInputs> {
        let binding = self.binding()?;
        ensure!(
            self.records.len() == contexts.len(),
            "tool context count differs"
        );
        let mut observations = Vec::new();
        observations.try_reserve_exact(self.records.len())?;
        for (record, context) in self.records.iter().zip(contexts) {
            context.validate()?;
            ensure!(&record.context == context, "tool context differs");
            let pending = context.begin()?;
            ensure!(pending.record == *record, "tool observation differs");
            observations.push(CurrentToolInput {
                window: pending.window,
                access: pending.record.access,
                paths: context.paths()?,
            });
        }
        let current = CurrentToolInputs {
            binding,
            observations,
        };
        ensure!(
            current.is_current()?,
            "tool observations changed during check"
        );
        Ok(current)
    }
}

fn bounded_bytes(bytes: &[u8], maximum: usize, empty: bool) -> Result<()> {
    ensure!(
        (empty || !bytes.is_empty()) && bytes.len() <= maximum && !bytes.contains(&0),
        "unbounded, empty or NUL-bearing tool context"
    );
    Ok(())
}

fn absolute(bytes: &[u8]) -> Result<()> {
    bounded_bytes(bytes, effective_access::MAX_PATH_BYTES, false)?;
    ensure!(bytes.starts_with(b"/"), "tool path is not absolute");
    Ok(())
}

fn raw(value: &OsStr) -> Result<Vec<u8>> {
    #[cfg(unix)]
    {
        use std::os::unix::ffi::OsStrExt as _;
        bounded_bytes(
            value.as_bytes(),
            effective_access::MAX_TOTAL_PATH_BYTES,
            true,
        )?;
        Ok(value.as_bytes().to_vec())
    }
    #[cfg(not(unix))]
    {
        let _ = value;
        anyhow::bail!("native Unix tool context is unavailable")
    }
}

fn path_from_raw(bytes: &[u8]) -> Result<PathBuf> {
    #[cfg(unix)]
    {
        use std::os::unix::ffi::OsStringExt as _;
        Ok(PathBuf::from(OsString::from_vec(bytes.to_vec())))
    }
    #[cfg(not(unix))]
    {
        let _ = bytes;
        anyhow::bail!("native Unix tool path is unavailable")
    }
}

fn capture_access(paths: &[PathBuf]) -> Result<effective_access::Snapshot> {
    for path in paths {
        native_header(path)?;
    }
    effective_access::capture(paths)
}

fn native_header(path: &Path) -> Result<()> {
    let mut options = OpenOptions::new();
    options.read(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt as _;
        options.custom_flags(libc::O_NONBLOCK | libc::O_CLOEXEC);
    }
    let mut file = match options.open(path) {
        Ok(file) => file,
        Err(error) if error.raw_os_error() == Some(libc_enoent()) => return Ok(()),
        Err(error) => return Err(error).context("native tool header unavailable"),
    };
    let metadata = file.metadata()?;
    ensure!(metadata.is_file(), "tool candidate is not a regular file");
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt as _;
        // Parent credential admission does not establish a candidate's exec
        // credentials. Refuse both bits, including same-owner or denied/tail
        // candidates, instead of guessing whether a host will honor them.
        ensure!(
            metadata.mode() & 0o6000 == 0,
            "set-ID native tool candidate is unsupported"
        );
    }
    let mut header = [0_u8; 32];
    let length = file.read(&mut header)?;
    let native = match std::env::consts::OS {
        "linux" => {
            length >= 16
                && &header[..4] == b"\x7fELF"
                && matches!(header[4], 1 | 2)
                && matches!(header[5], 1 | 2)
                && header[6] == 1
        }
        "macos" => match header[..4] {
            [0xfe, 0xed, 0xfa, 0xce] | [0xce, 0xfa, 0xed, 0xfe] => length >= 28,
            [0xfe, 0xed, 0xfa, 0xcf] | [0xcf, 0xfa, 0xed, 0xfe] => length == 32,
            [0xca, 0xfe, 0xba, 0xbe]
            | [0xca, 0xfe, 0xba, 0xbf]
            | [0xbe, 0xba, 0xfe, 0xca]
            | [0xbf, 0xba, 0xfe, 0xca] => {
                let count = if header[0] == 0xca {
                    u32::from_be_bytes(header[4..8].try_into()?)
                } else {
                    u32::from_le_bytes(header[4..8].try_into()?)
                };
                let entry_bytes = if header[3] == 0xbf || header[0] == 0xbf {
                    32
                } else {
                    20
                };
                length >= 8
                    && (1..=64).contains(&count)
                    && metadata.len() >= 8 + u64::from(count) * entry_bytes
            }
            _ => false,
        },
        _ => false,
    };
    ensure!(native, "script or unsupported native tool header");
    Ok(())
}

fn libc_enoent() -> i32 {
    #[cfg(unix)]
    {
        libc::ENOENT
    }
    #[cfg(not(unix))]
    {
        -1
    }
}

fn binding(domain: &[u8], encoded: &[u8]) -> [u8; 32] {
    let mut hash = trust_sha2::Sha256::new();
    hash.update((domain.len() as u64).to_le_bytes());
    hash.update(domain);
    hash.update((encoded.len() as u64).to_le_bytes());
    hash.update(encoded);
    let mut bytes = [0; 32];
    bytes.copy_from_slice(&hash.finalize());
    bytes
}

struct BoundedWriter(Vec<u8>);

impl io::Write for BoundedWriter {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        let required = self
            .0
            .len()
            .checked_add(bytes.len())
            .filter(|n| *n <= MAX_RECORD_BYTES)
            .ok_or_else(|| io::Error::other("tool record exceeds byte bound"))?;
        if self.0.capacity() < required {
            let capacity = self
                .0
                .capacity()
                .saturating_mul(2)
                .max(1024)
                .max(required)
                .min(MAX_RECORD_BYTES);
            self.0
                .try_reserve_exact(capacity - self.0.len())
                .map_err(io::Error::other)?;
        }
        self.0.extend_from_slice(bytes);
        Ok(bytes.len())
    }
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

fn encode_bounded(value: &impl Serialize) -> Result<Vec<u8>> {
    let mut writer = BoundedWriter(Vec::new());
    serde_json::to_writer(&mut writer, value)?;
    Ok(writer.0)
}

fn decode_bounded<T: serde::de::DeserializeOwned>(bytes: &[u8]) -> Result<T> {
    ensure!(
        bytes.len() <= MAX_RECORD_BYTES,
        "tool record exceeds byte bound"
    );
    ensure!(
        !bytes.contains(&b'\n') && !bytes.contains(&b'\r'),
        "multiline tool record"
    );
    Ok(serde_json::from_slice(bytes)?)
}

#[cfg(all(test, any(target_os = "macos", target_os = "linux")))]
mod tests {
    use std::fs;
    use std::os::unix::ffi::OsStrExt as _;
    use std::os::unix::fs::PermissionsExt as _;

    use super::*;

    // Header-shaped owned DATA files only. No file is executed or installed as
    // a compiler/linker; the real command owner's wait is a separate obligation.
    fn native(path: &Path, value: u8) {
        let mut bytes = vec![0; 64];
        if cfg!(target_os = "macos") {
            bytes[..4].copy_from_slice(&[0xcf, 0xfa, 0xed, 0xfe]);
        } else {
            bytes[..7].copy_from_slice(&[0x7f, b'E', b'L', b'F', 2, 1, 1]);
        }
        bytes[63] = value;
        fs::write(path, bytes).unwrap();
        fs::set_permissions(path, fs::Permissions::from_mode(0o700)).unwrap();
    }

    fn context(root: &Path, directories: &[&str]) -> Context {
        let path = directories
            .iter()
            .map(|name| root.join(name))
            .map(|path| raw(path.as_os_str()).unwrap())
            .reduce(|mut path, next| {
                path.push(b':');
                path.extend_from_slice(&next);
                path
            })
            .unwrap();
        Context::new(
            OsStr::new("tool"),
            root,
            Some(OsStr::from_bytes(&path)),
            Some(OsStr::new("/parent/bin")),
            Profile::LocalUnixNativeV1,
        )
        .unwrap()
    }

    #[test]
    fn same_path_content_and_same_path_shadow_change_full_binding() {
        observation::settled(|world| {
            let root = world.path().canonicalize().unwrap();
            for name in ["first", "last", "tail"] {
                fs::create_dir(root.join(name)).unwrap();
            }
            let selected = root.join("last/tool");
            native(&selected, 1);
            let context = context(&root, &["first", "last", "tail"]);
            let record = context.begin().unwrap().finish().unwrap();
            assert_eq!(
                record.access.entries()[0].outcome(),
                effective_access::Outcome::Missing
            );
            assert!(record.current(&context).unwrap());
            let old_tool = fs::read(&selected).unwrap();
            native(&root.join("first/tool"), 2);
            assert_eq!(fs::read(&selected).unwrap(), old_tool);
            assert!(!record.current(&context).unwrap());
            let shadow = context.begin().unwrap().finish().unwrap();
            assert_ne!(record.binding().unwrap(), shadow.binding().unwrap());
            native(&root.join("tail/tool"), 3);
            assert!(
                !shadow.current(&context).unwrap(),
                "tail candidates must be retained"
            );
            let tail = context.begin().unwrap().finish().unwrap();
            native(&selected, 4);
            assert!(!tail.current(&context).unwrap());
        });
    }

    #[test]
    fn denied_missing_and_duplicate_candidates_remain_ordered() {
        observation::settled(|world| {
            let root = world.path().canonicalize().unwrap();
            for name in ["missing", "denied", "allowed"] {
                fs::create_dir(root.join(name)).unwrap();
            }
            native(&root.join("denied/tool"), 1);
            fs::set_permissions(root.join("denied/tool"), fs::Permissions::from_mode(0o600))
                .unwrap();
            native(&root.join("allowed/tool"), 2);
            let context = context(&root, &["missing", "denied", "allowed", "missing"]);
            let record = context.begin().unwrap().finish().unwrap();
            let outcomes: Vec<_> = record
                .access
                .entries()
                .iter()
                .map(|entry| entry.outcome())
                .collect();
            assert_eq!(
                outcomes,
                [
                    effective_access::Outcome::Missing,
                    effective_access::Outcome::Denied,
                    effective_access::Outcome::Allowed,
                    effective_access::Outcome::Missing
                ]
            );
            assert_eq!(context.candidates[0], context.candidates[3]);
            assert!(record.context().matches_parent(
                &root,
                Some(OsStr::new("/parent/bin")),
                context.profile()
            ));
            assert!(
                !record
                    .context()
                    .matches_parent(&root, None, context.profile())
            );
            let other = Context::new(
                OsStr::new("tool"),
                &root,
                context.child_path.as_deref().map(OsStr::from_bytes),
                None,
                context.profile(),
            )
            .unwrap();
            assert!(!record.current(&other).unwrap());
        });
    }

    #[test]
    fn local_resource_v2_is_a_distinct_strictly_encoded_lookup_profile() {
        observation::settled(|world| {
            let root = world.path().canonicalize().unwrap();
            let tool = root.join("tool");
            native(&tool, 1);
            let ordinary = Context::new(
                tool.as_os_str(),
                &root,
                None,
                None,
                Profile::LocalUnixNativeV1,
            )
            .unwrap();
            let resource_v2 = Context::new(
                tool.as_os_str(),
                &root,
                None,
                None,
                Profile::LocalUnixNativeResourceV2,
            )
            .unwrap();
            assert_eq!(ordinary.candidates(), resource_v2.candidates());
            let ordinary_record = ordinary.begin().unwrap().finish().unwrap();
            let resource_record = resource_v2.begin().unwrap().finish().unwrap();
            assert!(resource_record.current(&resource_v2).unwrap());
            assert!(!resource_record.current(&ordinary).unwrap());
            assert!(!ordinary_record.current(&resource_v2).unwrap());
            assert!(!resource_record.context().matches_parent(
                &root,
                None,
                Profile::LocalUnixNativeV1
            ));
            assert!(resource_record.context().matches_parent(
                &root,
                None,
                Profile::LocalUnixNativeResourceV2
            ));
            assert_ne!(
                ordinary_record.binding().unwrap(),
                resource_record.binding().unwrap()
            );
            let inputs = ToolInputs::from_records(vec![resource_record]).unwrap();
            let encoded = inputs.encode().unwrap();
            let decoded = ToolInputs::decode(&encoded).unwrap();
            assert!(decoded.current(std::slice::from_ref(&resource_v2)).unwrap());
            assert!(decoded.check_current(&[ordinary]).is_err());
            for unsupported in [
                "local-unix-native-resource-v3",
                "hosted-v3",
                "future-profile",
            ] {
                let mut bad = serde_json::to_value(&inputs).unwrap();
                bad["records"][0]["context"]["profile"] = serde_json::json!(unsupported);
                assert!(ToolInputs::decode(&serde_json::to_vec(&bad).unwrap()).is_err());
            }
            native(&tool, 2);
            assert!(!decoded.current(&[resource_v2]).unwrap());
        });
    }

    #[test]
    fn original_window_rejects_content_and_namespace_edit_restore() {
        observation::settled(|world| {
            let root = world.path().canonicalize().unwrap();
            let tool = root.join("tool");
            native(&tool, 1);
            let context = Context::new(
                tool.as_os_str(),
                &root,
                None,
                None,
                Profile::LocalUnixNativeV1,
            )
            .unwrap();
            let pending = context.begin().unwrap();
            native(&tool, 2);
            native(&tool, 1);
            assert!(pending.finish().is_err());
            let pending = context.begin().unwrap();
            let moved = root.join("moved");
            fs::rename(&tool, &moved).unwrap();
            fs::rename(&moved, &tool).unwrap();
            assert!(pending.finish().is_err());
            assert!(context.begin().unwrap().finish().is_ok());
        });
    }

    #[test]
    fn final_access_reads_remain_inside_original_window() {
        observation::settled(|world| {
            let root = world.path().canonicalize().unwrap();
            for name in ["first", "last"] {
                fs::create_dir(root.join(name)).unwrap();
            }
            let tool = root.join("last/tool");
            native(&tool, 1);
            let context = context(&root, &["first", "last"]);
            let pending = context.begin().unwrap();
            assert!(
                pending
                    .finish_with(|paths| {
                        let access = capture_access(paths)?;
                        native(&tool, 2);
                        Ok(access)
                    })
                    .is_err(),
                "a content edit during the final access capture must be refused"
            );
            let pending = context.begin().unwrap();
            assert!(
                pending
                    .finish_with(|paths| {
                        let access = capture_access(paths)?;
                        native(&root.join("first/tool"), 3);
                        Ok(access)
                    })
                    .is_err(),
                "a missing candidate appearing during final access capture must be refused"
            );
            let pending = context.begin().unwrap();
            assert!(
                pending
                    .finish_with(|paths| {
                        let access = capture_access(paths)?;
                        native(&tool, 4);
                        native(&tool, 2);
                        Ok(access)
                    })
                    .is_err(),
                "restored content must retain the original window's change stamps"
            );
            assert!(context.begin().unwrap().finish().is_ok());
        });
    }

    #[test]
    fn current_factory_compares_full_data_and_preserves_its_binding() {
        observation::settled(|world| {
            let root = world.path().canonicalize().unwrap();
            let tool = root.join("tool");
            native(&tool, 1);
            let context = Context::new(
                tool.as_os_str(),
                &root,
                None,
                None,
                Profile::LocalUnixNativeV1,
            )
            .unwrap();
            let inputs =
                ToolInputs::from_records(vec![context.begin().unwrap().finish().unwrap()]).unwrap();
            let decoded = ToolInputs::decode(&inputs.encode().unwrap()).unwrap();
            let current = decoded
                .check_current(std::slice::from_ref(&context))
                .unwrap();
            assert_eq!(current.binding(), decoded.binding().unwrap());
            for _ in 0..3 {
                assert!(current.is_current().unwrap());
            }
            assert!(decoded.check_current(&[]).is_err());
            let different = Context::new(
                tool.as_os_str(),
                &root,
                None,
                Some(OsStr::new("/different/parent")),
                Profile::LocalUnixNativeV1,
            )
            .unwrap();
            assert!(decoded.check_current(&[different]).is_err());
            native(&tool, 2);
            assert!(!current.is_current().unwrap());
            assert!(
                decoded
                    .check_current(std::slice::from_ref(&context))
                    .is_err()
            );
            native(&tool, 1);
            assert!(!current.is_current().unwrap());
            // Reacquiring from decoded DATA always performs a fresh full
            // observation; it cannot replace the older handle's stamps.
            let reacquired = decoded.check_current(&[context]).unwrap();
            assert!(reacquired.is_current().unwrap());
            assert!(!current.is_current().unwrap());
            let empty = ToolInputs::from_records(vec![]).unwrap();
            let current = empty.check_current(&[]).unwrap();
            assert_eq!(current.binding(), empty.binding().unwrap());
            assert!(current.is_current().unwrap());
        });
    }

    #[test]
    fn current_handle_retains_symlink_namespace_edit_restore() {
        observation::settled(|world| {
            let root = world.path().canonicalize().unwrap();
            for name in ["first", "second"] {
                native(&root.join(name), 1);
            }
            let alias = root.join("tool");
            std::os::unix::fs::symlink("first", &alias).unwrap();
            let context = Context::new(
                alias.as_os_str(),
                &root,
                None,
                None,
                Profile::LocalUnixNativeV1,
            )
            .unwrap();
            let inputs =
                ToolInputs::from_records(vec![context.begin().unwrap().finish().unwrap()]).unwrap();
            let current = inputs.check_current(&[context]).unwrap();
            fs::remove_file(&alias).unwrap();
            std::os::unix::fs::symlink("second", &alias).unwrap();
            assert!(!current.is_current().unwrap());
            fs::remove_file(&alias).unwrap();
            std::os::unix::fs::symlink("first", &alias).unwrap();
            assert!(!current.is_current().unwrap());
        });
    }

    #[test]
    fn current_access_errors_credentials_and_cross_record_mutations_refuse() {
        observation::settled(|world| {
            let root = world.path().canonicalize().unwrap();
            let contexts: Vec<_> = ["first", "second"]
                .iter()
                .map(|name| {
                    let tool = root.join(name);
                    native(&tool, 1);
                    Context::new(
                        tool.as_os_str(),
                        &root,
                        None,
                        None,
                        Profile::LocalUnixNativeV1,
                    )
                    .unwrap()
                })
                .collect();
            let inputs = ToolInputs::from_records(
                contexts
                    .iter()
                    .map(|context| context.begin().unwrap().finish().unwrap())
                    .collect(),
            )
            .unwrap();
            let current = inputs.check_current(&contexts).unwrap();
            assert!(
                current
                    .is_current_with(|_| anyhow::bail!("access query unavailable"))
                    .is_err()
            );
            let mut changed = serde_json::to_value(&current.observations[0].access).unwrap();
            let uid = changed["credentials"]["uid"].as_u64().unwrap() ^ 1;
            changed["credentials"]["uid"] = serde_json::json!(uid);
            changed["credentials"]["euid"] = serde_json::json!(uid);
            let changed: effective_access::Snapshot = serde_json::from_value(changed).unwrap();
            assert!(!current.is_current_with(|_| Ok(changed.clone())).unwrap());
            let mut index = 0;
            assert!(
                !current
                    .is_current_with(|paths| {
                        let access = effective_access::capture(paths)?;
                        if index == 1 {
                            native(&root.join("first"), 2);
                            native(&root.join("first"), 1);
                        }
                        index += 1;
                        Ok(access)
                    })
                    .unwrap(),
                "later access queries must precede earlier records' window checks"
            );
        });
    }

    #[test]
    fn context_bounds_and_unsupported_candidates_refuse() {
        let root = tempfile::tempdir().unwrap();
        let root = root.path().canonicalize().unwrap();
        for (program, path) in [
            ("relative/tool", Some("/bin")),
            ("tool", None),
            ("tool", Some("")),
            ("tool", Some("/bin:")),
            ("tool", Some("relative")),
            ("", Some("/bin")),
        ] {
            assert!(
                Context::new(
                    OsStr::new(program),
                    &root,
                    path.map(OsStr::new),
                    None,
                    Profile::LocalUnixNativeV1
                )
                .is_err()
            );
        }
        assert!(
            Context::new(
                OsStr::new("/tool"),
                Path::new("relative"),
                None,
                None,
                Profile::LocalUnixNativeV1
            )
            .is_err()
        );
        let nul = OsStr::from_bytes(b"bad\0tool");
        assert!(Context::new(nul, &root, None, None, Profile::LocalUnixNativeV1).is_err());
        let many = vec!["/bin"; effective_access::MAX_PATHS + 1].join(":");
        assert!(
            Context::new(
                OsStr::new("tool"),
                &root,
                Some(OsStr::new(&many)),
                None,
                Profile::LocalUnixNativeV1
            )
            .is_err()
        );
        let long = format!("/{}", "x".repeat(effective_access::MAX_PATH_BYTES));
        assert!(
            Context::new(
                OsStr::new(&long),
                &root,
                None,
                None,
                Profile::LocalUnixNativeV1
            )
            .is_err()
        );
        let script = root.join("script");
        fs::write(&script, b"#!/bin/sh\n").unwrap();
        let c = Context::new(
            script.as_os_str(),
            &root,
            None,
            None,
            Profile::LocalUnixNativeV1,
        )
        .unwrap();
        assert!(c.begin().is_err());
        let c = Context::new(
            root.as_os_str(),
            &root,
            None,
            None,
            Profile::LocalUnixNativeV1,
        )
        .unwrap();
        assert!(c.begin().is_err());
    }

    #[test]
    fn strict_codec_validates_derived_paths_schema_host_and_aggregate_limits() {
        observation::settled(|world| {
            let root = world.path().canonicalize().unwrap();
            let tool = root.join("tool");
            native(&tool, 1);
            let context = Context::new(
                tool.as_os_str(),
                &root,
                None,
                None,
                Profile::LocalUnixNativeV1,
            )
            .unwrap();
            let record = context.begin().unwrap().finish().unwrap();
            let encoded = record.encode().unwrap();
            assert_eq!(Record::decode(&encoded).unwrap(), record);
            for (field, value) in [
                ("schema", serde_json::json!("old")),
                ("extra", serde_json::json!(true)),
            ] {
                let mut bad = serde_json::to_value(&record).unwrap();
                bad[field] = value;
                assert!(Record::decode(&serde_json::to_vec(&bad).unwrap()).is_err());
            }
            let mut bad = serde_json::to_value(&record).unwrap();
            bad["context"]["candidates"][0] = serde_json::json!([47, 120]);
            assert!(Record::decode(&serde_json::to_vec(&bad).unwrap()).is_err());
            let mut bad = serde_json::to_value(&record).unwrap();
            bad["access"]["host_os"] = serde_json::json!("other");
            assert!(Record::decode(&serde_json::to_vec(&bad).unwrap()).is_err());
            let empty = ToolInputs::from_records(vec![]).unwrap();
            assert_eq!(
                empty.encode().unwrap(),
                br#"{"schema":"trust-tool-inputs-v1","records":[]}"#
            );
            assert_eq!(ToolInputs::decode(&empty.encode().unwrap()).unwrap(), empty);
            assert!(
                ToolInputs::decode(br#"{"schema": "trust-tool-inputs-v1","records":[]}"#).is_err()
            );
            assert!(ToolInputs::decode(b"unavailable").is_err());
            assert!(ToolInputs::decode(&vec![b' '; MAX_RECORD_BYTES + 1]).is_err());
            let inputs = ToolInputs::from_records(vec![record.clone()]).unwrap();
            assert!(inputs.current(std::slice::from_ref(&context)).unwrap());
            assert_ne!(inputs.binding().unwrap(), empty.binding().unwrap());
            assert!(ToolInputs::from_records(vec![record.clone(); MAX_RECORDS + 1]).is_err());
            let mut large = record;
            large.context.parent_path = Some(vec![b'x'; effective_access::MAX_TOTAL_PATH_BYTES]);
            assert!(large.encode().is_ok());
            assert!(ToolInputs::from_records(vec![large; 6]).is_err());
        });
    }

    #[test]
    fn set_id_native_image_is_outside_each_local_profile() {
        observation::settled(|world| {
            let root = world.path().canonicalize().unwrap();
            let path = root.join("native-input-data");
            // DATA from this genuinely compiled test image, never executed,
            // installed or presented as a compiler/linker fixture role.
            let image = fs::read(std::env::current_exe().unwrap()).unwrap();
            fs::write(&path, image).unwrap();
            for profile in [
                Profile::LocalUnixNativeV1,
                Profile::LocalUnixNativeResourceV2,
            ] {
                fs::set_permissions(&path, fs::Permissions::from_mode(0o700)).unwrap();
                let context = Context::new(path.as_os_str(), &root, None, None, profile).unwrap();
                assert!(context.begin().unwrap().finish().is_ok());
                for bits in [0o4000, 0o2000, 0o6000] {
                    fs::set_permissions(&path, fs::Permissions::from_mode(0o700 | bits)).unwrap();
                    assert_eq!(
                        fs::metadata(&path).unwrap().permissions().mode() & 0o6000,
                        bits
                    );
                    assert!(context.begin().is_err(), "set-ID {bits:o} in {profile:?}");
                }
            }
            fs::set_permissions(&path, fs::Permissions::from_mode(0o700)).unwrap();
        });
    }

    #[test]
    fn set_id_lower_priority_candidate_refuses_the_entire_recipe() {
        observation::settled(|world| {
            let root = world.path().canonicalize().unwrap();
            let image = fs::read(std::env::current_exe().unwrap()).unwrap();
            for directory in ["first", "tail"] {
                let directory = root.join(directory);
                fs::create_dir(&directory).unwrap();
                let path = directory.join("tool");
                fs::write(&path, &image).unwrap();
                fs::set_permissions(&path, fs::Permissions::from_mode(0o700)).unwrap();
            }
            let tail = root.join("tail/tool");
            for profile in [
                Profile::LocalUnixNativeV1,
                Profile::LocalUnixNativeResourceV2,
            ] {
                fs::set_permissions(&tail, fs::Permissions::from_mode(0o700)).unwrap();
                let mut context = context(&root, &["first", "tail"]);
                context.profile = profile;
                assert!(context.begin().unwrap().finish().is_ok());
                for bits in [0o4000, 0o2000, 0o6000] {
                    fs::set_permissions(&tail, fs::Permissions::from_mode(0o700 | bits)).unwrap();
                    assert_eq!(
                        fs::metadata(&tail).unwrap().permissions().mode() & 0o6000,
                        bits
                    );
                    assert!(
                        context.begin().is_err(),
                        "tail set-ID {bits:o} in {profile:?}"
                    );
                }
                fs::set_permissions(&tail, fs::Permissions::from_mode(0o4600)).unwrap();
                assert_eq!(
                    fs::metadata(&tail).unwrap().permissions().mode() & 0o6000,
                    0o4000
                );
                assert_eq!(
                    effective_access::capture(std::slice::from_ref(&tail))
                        .unwrap()
                        .entries()[0]
                        .outcome(),
                    effective_access::Outcome::Denied
                );
                assert!(context.begin().is_err(), "denied tail in {profile:?}");
            }
            fs::set_permissions(&tail, fs::Permissions::from_mode(0o700)).unwrap();
        });
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn acl_change_is_bound_and_original_window_rejects_restoration() {
        observation::settled(|world| {
            let root = world.path().canonicalize().unwrap();
            let tool = root.join("tool");
            native(&tool, 1);
            let context = Context::new(
                tool.as_os_str(),
                &root,
                None,
                None,
                Profile::LocalUnixNativeV1,
            )
            .unwrap();
            let record = context.begin().unwrap().finish().unwrap();
            let inputs = ToolInputs::from_records(vec![record.clone()]).unwrap();
            let current = inputs
                .check_current(std::slice::from_ref(&context))
                .unwrap();
            let pending = context.begin().unwrap();
            let mode = fs::metadata(&tool).unwrap().permissions().mode();
            let bytes = fs::read(&tool).unwrap();
            for action in ["+a", "-a"] {
                assert!(
                    std::process::Command::new("/bin/chmod")
                        .args([action, "everyone deny execute"])
                        .arg(&tool)
                        .status()
                        .unwrap()
                        .success()
                );
                assert_eq!(fs::metadata(&tool).unwrap().permissions().mode(), mode);
                assert_eq!(fs::read(&tool).unwrap(), bytes);
                if action == "+a" {
                    assert!(!record.current(&context).unwrap());
                    assert!(!current.is_current().unwrap());
                }
            }
            assert!(record.current(&context).unwrap());
            assert!(!current.is_current().unwrap());
            assert!(pending.finish().is_err());
        });
    }
}
