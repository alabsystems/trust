// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Distinct whole-envelope OFFLINE preparation DATA. No decoder or pathname
//! creates a source/config/cache owner, private seed, control SDK, GNU loan,
//! original deadline, native child, availability seal or retirement proof.
//!
//! No transport/entry is advertised here. A connected issuer must independently
//! retain every actual owner before dispatch and derive the envelope from the
//! original maintained source reader. The caller cannot submit an envelope or
//! arbitrary argv in Request. Existing query/object profiles remain unchanged.
use std::collections::BTreeSet;
use std::io;

use super::query::OperationKey;
use super::{GnuIdentity, absolute, read_file, write_file};
use crate::wire::{Encoder, header, invalid};
use crate::{FileIdentity, MAX_FIELD, MAX_ITEMS};

mod compiler_query;
pub use compiler_query::CompilerQuery;
mod intent;
pub use intent::{
    ConfigurationSelection, ConfiguredIntentSelection, INTENT_PURPOSE, Intent, IntentQuery,
    IntentReply, IntentSelection,
};
mod cache;
pub use cache::PreparationCacheReply;
mod source;
pub use source::{ArchiveCandidate, MAX_ARCHIVE_CANDIDATES, SourceCapture, SourceCaptureAccepted};

mod output;
pub use output::{PreparationOutputAttachment, PreparationOutputReply, RIGHTS_MARKER as PREPARATION_OUTPUT_RIGHTS_MARKER};

mod staged_intent;
pub use staged_intent::{
    PROGRAM_PURPOSE, ProgramSelection, ProgramSelectionQuery, ProgramSelectionReply,
    ReservedPrograms, STAGED_INTENT_PURPOSE, StagedIntent, StagedIntentQuery, StagedIntentReply,
    StagedSelection,
};

pub const PURPOSE: &str = "native-bootstrap-offline-preparation-v1";
/// Distinct before-configuration Root purpose. These bytes declare support;
/// only the actual Host's retained program, original owners and admission may
/// start it. Existing Bootstrap query/object purposes remain separate.
pub const ROOT_ARGUMENT_PREFIX: [&str; 3] =
    ["--unverified", "resource", "bootstrap-offline-runtime"];
pub const ROOT_ARGUMENT: &str = "--native-offline-preparation-v1";
/// One original control Root, one actual private Targo fetch child and its
/// brokered compiler metadata child. No waiting/paused process transfers its
/// implicit unit. The full cold route must fund all three simultaneously.
pub const ROOT_MIN_CPU_UNITS: u32 = 3;
pub const ROOT_PROTOCOL_MARKER: [u8; 64] = {
    let mut bytes = [0; 64];
    let magic = *b"TRUSTBPREP000001";
    let mut index = 0;
    while index < magic.len() {
        bytes[index] = magic[index];
        index += 1;
    }
    // SAME maintained held-image declaration format: six complete BE64
    // fields. This is a distinct section/profile, not a second graph marker.
    let fields = [1u64, 19, ROOT_MIN_CPU_UNITS as u64, 114, 115, 1];
    index = 0;
    while index < fields.len() {
        let field = fields[index].to_be_bytes();
        let mut byte = 0;
        while byte < field.len() {
            bytes[16 + index * 8 + byte] = field[byte];
            byte += 1;
        }
        index += 1;
    }
    bytes
};
pub const MAX_BUDGET_NS: u64 = 900_000_000_000;
pub const MAX_MANIFESTS: usize = 256;
pub const MAX_INPUT_PATHS: usize = 8192;
/// Fixed native probes used by the maintained seed validator. Selection is
/// DATA only: no enum/arguments/output constructs a native or semantic owner.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum SeedProbe {
    CompilerVersion,
    CompilerSysroot,
    TargoVersion,
    FormatterVersion,
}
pub const SEED_PROBES: [SeedProbe; 4] = [
    SeedProbe::CompilerVersion,
    SeedProbe::CompilerSysroot,
    SeedProbe::TargoVersion,
    SeedProbe::FormatterVersion,
];
impl SeedProbe {
    pub const fn program(self) -> &'static str {
        match self {
            Self::CompilerVersion | Self::CompilerSysroot => "trustc",
            Self::TargoVersion => "targo",
            Self::FormatterVersion => "trustfmt",
        }
    }
    pub const fn arguments(self) -> &'static [&'static str] {
        match self {
            Self::CompilerVersion => &["-vV"],
            Self::CompilerSysroot => &["--print", "sysroot"],
            Self::TargoVersion => &["--version", "--verbose"],
            Self::FormatterVersion => &["--version"],
        }
    }
}
const DOMAIN: &[u8] = b"trust-bootstrap-offline-preparation-v1\0";

fn joined(root: &[u8], relative: &[u8]) -> Vec<u8> {
    let mut path = root.to_vec();
    path.push(b'/');
    path.extend(relative);
    path
}

fn manifest(path: &[u8]) -> bool {
    !path.is_empty()
        && path.len() <= 4096
        && !path.contains(&0)
        && path
            .split(|byte| *byte == b'/')
            .all(|part| !part.is_empty() && part != b"." && part != b"..")
        && (path == b"Cargo.toml" || path.ends_with(b"/Cargo.toml"))
}

fn environment(entries: &[(Vec<u8>, Vec<u8>)]) -> io::Result<()> {
    environment_entries(entries)?;
    if entries.iter().any(|(name, value)| name == b"CARGO_NET_OFFLINE" && value == b"true") {
        Ok(())
    } else {
        Err(invalid())
    }
}

fn environment_entries(entries: &[(Vec<u8>, Vec<u8>)]) -> io::Result<()> {
    if entries.len() > MAX_ITEMS {
        return Err(invalid());
    }
    let mut names = BTreeSet::new();
    for (name, value) in entries {
        if name.is_empty()
            || name.len() > MAX_FIELD
            || value.len() > MAX_FIELD
            || name.contains(&0)
            || name.contains(&b'=')
            || value.contains(&0)
            || !names.insert(name)
        {
            return Err(invalid());
        }
    }
    Ok(())
}

/// Equality expectations for one original attempt, not transferable custody.
/// All environment presence/values, including empty warning overrides and
/// credential/network configuration, remain caller DATA; only canonical check
/// mode's existing OFFLINE override is required. Never print this private frame.
#[derive(Clone, PartialEq, Eq)]
pub struct Request {
    pub key: OperationKey,
    pub gnu: GnuIdentity,
    pub control_sdk_root: Vec<u8>,
    pub source_root: Vec<u8>,
    pub source_directory: FileIdentity,
    pub output_root: Vec<u8>,
    pub output_directory: FileIdentity,
    pub output_lock: FileIdentity,
    pub configured_targo: Vec<u8>,
    pub configured_compiler: Vec<u8>,
    pub cargo_home: Vec<u8>,
    pub environment: Vec<(Vec<u8>, Vec<u8>)>,
    /// Restricts the actual owner's ALREADY held original endpoint; decoding
    /// cannot start/reset a budget. Reconnect reuses the same attempt/deadline.
    pub budget_ns: u64,
}
impl Request {
    pub fn validate(&self) -> io::Result<()> {
        self.key.validate()?;
        self.gnu.write(&mut Encoder::new(0))?;
        environment(&self.environment)?;
        for path in [
            &self.control_sdk_root,
            &self.source_root,
            &self.output_root,
            &self.configured_targo,
            &self.configured_compiler,
            &self.cargo_home,
        ] {
            if !absolute(path) {
                return Err(invalid());
            }
        }
        if self.source_root == self.output_root
            || self.source_directory == self.output_directory
            || self.source_directory == self.output_lock
            || self.output_directory == self.output_lock
            || !matches!(self.budget_ns, 1..=MAX_BUDGET_NS)
        {
            return Err(invalid());
        }
        for file in [self.source_directory, self.output_directory, self.output_lock] {
            write_file(&mut Encoder::new(0), file)?;
        }
        Ok(())
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        let mut e = Encoder::new(114);
        e.number(1);
        self.key.write(&mut e)?;
        self.gnu.write(&mut e)?;
        e.bytes(&self.control_sdk_root)?;
        e.bytes(&self.source_root)?;
        write_file(&mut e, self.source_directory)?;
        e.bytes(&self.output_root)?;
        write_file(&mut e, self.output_directory)?;
        write_file(&mut e, self.output_lock)?;
        e.bytes(&self.configured_targo)?;
        e.bytes(&self.configured_compiler)?;
        e.bytes(&self.cargo_home)?;
        e.number(self.environment.len() as u64);
        for (name, value) in &self.environment {
            e.bytes(name)?;
            e.bytes(value)?;
        }
        e.number(self.budget_ns);
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 114)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let key = OperationKey::read(&mut d)?;
        let gnu = GnuIdentity::read(&mut d)?;
        let control_sdk_root = d.bytes()?;
        let source_root = d.bytes()?;
        let source_directory = read_file(&mut d)?;
        let output_root = d.bytes()?;
        let output_directory = read_file(&mut d)?;
        let output_lock = read_file(&mut d)?;
        let configured_targo = d.bytes()?;
        let configured_compiler = d.bytes()?;
        let cargo_home = d.bytes()?;
        let count = d.count(MAX_ITEMS)?;
        let mut environment = Vec::with_capacity(count);
        for _ in 0..count {
            environment.push((d.bytes()?, d.bytes()?));
        }
        let value = Self {
            key,
            gnu,
            control_sdk_root,
            source_root,
            source_directory,
            output_root,
            output_directory,
            output_lock,
            configured_targo,
            configured_compiler,
            cargo_home,
            environment,
            budget_ns: d.number()?,
        };
        d.done()?;
        value.validate()?;
        Ok(value)
    }
    pub fn hello(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        self.key.graph.hello(PURPOSE)
    }
    pub fn binding_preimage(&self) -> io::Result<Vec<u8>> {
        let frame = self.encode()?;
        let mut bytes = Vec::from(DOMAIN);
        bytes.extend((frame.len() as u64).to_be_bytes());
        bytes.extend(frame);
        Ok(bytes)
    }
}

/// The source reader's complete result DATA, not a proof of completeness or
/// successful availability. Only the actual original issuer may bind this
/// output after its real source-read operation/postchecks; Request has no field
/// through which a caller can nominate these rows as admission authority.
#[derive(Clone, PartialEq, Eq)]
pub struct Envelope {
    pub manifests: Vec<Vec<u8>>,
    /// Full declared read/discovery paths, including prospectively absent
    /// configs. The issuer must retain real physical guards/absence anchors;
    /// this list constructs none, and contains no portable readiness seal.
    pub input_paths: Vec<Vec<u8>>,
}
impl Envelope {
    pub fn validate(&self) -> io::Result<()> {
        if !(3..=MAX_MANIFESTS).contains(&self.manifests.len())
            || self.manifests.iter().any(|path| !manifest(path))
            || self.manifests.windows(2).any(|pair| pair[0] >= pair[1])
            || [b"Cargo.toml".as_slice(), b"library/Cargo.toml", b"src/bootstrap/Cargo.toml"]
                .iter()
                .any(|base| !self.manifests.iter().any(|path| path.as_slice() == *base))
            || self.input_paths.is_empty()
            || self.input_paths.len() > MAX_INPUT_PATHS
            || self.input_paths.iter().any(|path| !absolute(path))
            || self.input_paths.windows(2).any(|pair| pair[0] >= pair[1])
        {
            return Err(invalid());
        }
        Ok(())
    }
    /// Only the canonical non-compiling locked offline verb, for every source
    /// row in order. The genuine configured Targo spelling stays in Request.
    pub fn fetch_arguments(&self, request: &Request, index: usize) -> io::Result<Vec<Vec<u8>>> {
        request.validate()?;
        self.validate()?;
        let relative = self.manifests.get(index).ok_or_else(invalid)?;
        Ok(vec![
            b"fetch".to_vec(),
            b"--locked".to_vec(),
            b"--offline".to_vec(),
            b"--manifest-path".to_vec(),
            joined(&request.source_root, relative),
        ])
    }
    pub fn encode(&self, request: &Request, request_sha256: [u8; 32]) -> io::Result<Vec<u8>> {
        request.validate()?;
        self.validate()?;
        let mut e = Encoder::new(115);
        e.number(1);
        request.key.write(&mut e)?;
        e.0.extend(request_sha256);
        e.number(self.manifests.len() as u64);
        for path in &self.manifests {
            e.bytes(path)?;
        }
        e.number(self.input_paths.len() as u64);
        for path in &self.input_paths {
            e.bytes(path)?;
        }
        e.finish()
    }
    pub fn decode(bytes: &[u8], request: &Request, expected_sha256: [u8; 32]) -> io::Result<Self> {
        request.validate()?;
        let mut d = header(bytes, 115)?;
        if d.number()? != 1
            || OperationKey::read(&mut d)? != request.key
            || d.array::<32>()? != expected_sha256
        {
            return Err(invalid());
        }
        let count = d.count(MAX_MANIFESTS)?;
        let mut manifests = Vec::with_capacity(count);
        for _ in 0..count {
            manifests.push(d.bytes()?);
        }
        let count = d.count(MAX_INPUT_PATHS)?;
        let mut input_paths = Vec::with_capacity(count);
        for _ in 0..count {
            input_paths.push(d.bytes()?);
        }
        d.done()?;
        let value = Self { manifests, input_paths };
        value.validate()?;
        Ok(value)
    }
}

#[cfg(test)]
mod tests;
#[cfg(test)]
pub(crate) use tests::request as test_request;
