// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Binding DATA for the original fixed-root Bootstrap graph. Neither decoding,
//! support nor enrollment creates CPU, GNU, SDK, output, launch or release rights.
//! The Host must retain the actual original Job/resources and offered descriptions.

use std::io;

use crate::wire::{Decoder, Encoder, header, invalid};
use crate::{ContextQuery, ContextReply, Cpu, FileIdentity, Subject};

pub const PURPOSE: &str = "native-bootstrap-graph-v1";
pub const SUPPORT_PURPOSE: &str = "native-bootstrap-graph-support-v1";
/// Exact original Targo purpose prefix, before project aliases/configuration.
/// The Host independently selects and validates its managed held root image;
/// these argv bytes grant no resources, enrollment or execution authority.
pub const ROOT_ARGUMENT_PREFIX: [&str; 3] = ["--unverified", "resource", "bootstrap-runtime"];
/// Native member/subgroup protocol flags before the purpose prefix. They do
/// not substitute for original Host custody or a held-image declaration.
pub const ROOT_WORKER_ARGUMENT_PREFIX: [&str; 2] =
    ["--resource-worker-v3", "--resource-subgroups-v3"];
pub const GNU_RIGHTS_MARKER: u8 = 0x72;
pub const OUTPUT_RIGHTS_MARKER: u8 = 0x73;
pub const DESCRIPTION_COUNT: usize = 2;
/// Native Host-owned discovery locator only. No plan/path/FD number selects
/// CPU, SDK, graph or execution authority. GNU3/4 and SDK5 remain disjoint.
pub const HOST_STORE_FD_ENV: &str = "ATERM_BOOTSTRAP_GRAPH_HOST_STORE_FD_V1";
pub const HOST_STORE_TARGET_FD: u32 = 7;
/// Support DATA in the SAME held Targo image, not a readiness, resource,
/// completed-runtime, SDK, launch or graph-retirement authority. The actual
/// declaration is emitted only by the integrated native entry/client.
pub const BOOTSTRAP_GRAPH_PROTOCOL_MARKER: [u8; 64] = marker();
pub mod compilation;
pub mod configuration;
pub use configuration::{ConfigurationAttachment, ConfigurationReply};
pub mod materialization;
pub use materialization::{MaterializationPreparation, MaterializationReply};
pub mod object;
pub mod offline_preparation;
pub mod preparation;
pub mod query;
pub mod source;
pub use source::{SourceAttachment, SourceRecord, SourceReply};
const fn marker() -> [u8; 64] {
    let mut bytes = [0; 64];
    let magic = *b"TRUSTBGRAPH00002";
    let mut index = 0;
    while index < 16 {
        bytes[index] = magic[index];
        index += 1;
    }
    let fields = [3_u64, 71, 72, 73, 74, 2];
    let mut field = 0;
    while field < fields.len() {
        let value = fields[field].to_be_bytes();
        let mut byte = 0;
        while byte < 8 {
            bytes[16 + field * 8 + byte] = value[byte];
            byte += 1;
        }
        field += 1;
    }
    bytes
}

#[cfg(all(feature = "channel", any(target_os = "macos", target_os = "linux")))]
pub mod transport;

/// A nonce binds one live attempted graph; it never serializes ScopeIdentity or
/// reconstructs its actual withheld manager owner. Do not log the private query.
#[derive(Clone, PartialEq, Eq)]
pub struct Key {
    pub query: ContextQuery,
    pub graph: [u8; 16],
}
impl Key {
    pub fn validate(&self) -> io::Result<()> {
        self.query.validate()?;
        if self.graph == [0; 16]
            || self.graph == self.query.call_attempt
            || self.graph == self.query.binding.root_attempt
        {
            return Err(invalid());
        }
        Ok(())
    }
    fn write(&self, e: &mut Encoder) -> io::Result<()> {
        self.validate()?;
        e.frame_bytes(&self.query.encode()?)?;
        e.0.extend(self.graph);
        Ok(())
    }
    fn read(d: &mut Decoder<'_>) -> io::Result<Self> {
        let value = Self { query: ContextQuery::decode(&d.frame_bytes()?)?, graph: d.array()? };
        value.validate()?;
        Ok(value)
    }
    fn hello(&self, purpose: &str) -> io::Result<Vec<u8>> {
        self.validate()?;
        purpose_hello(&self.query, purpose)
    }
}

pub(super) fn purpose_hello(query: &ContextQuery, purpose: &str) -> io::Result<Vec<u8>> {
    query.validate()?;
    let attempt: String =
        query.binding.root_attempt.iter().map(|byte| format!("{byte:02x}")).collect();
    Ok(format!(
        "{{\"version\":3,\"role\":\"{purpose}\",\"session\":\"{}\",\"attempt\":\"{attempt}\"}}",
        query.binding.session
    )
    .into_bytes())
}

fn absolute(path: &[u8]) -> bool {
    path.len() > 1
        && path.len() <= crate::MAX_FIELD
        && path[0] == b'/'
        && !path.contains(&0)
        && path[1..].split(|b| *b == b'/').all(|p| !p.is_empty() && p != b"." && p != b"..")
}
fn write_file(e: &mut Encoder, file: FileIdentity) -> io::Result<()> {
    if file.inode == 0 {
        return Err(invalid());
    }
    e.number(file.device);
    e.number(file.inode);
    Ok(())
}
fn read_file(d: &mut Decoder<'_>) -> io::Result<FileIdentity> {
    let value = FileIdentity { device: d.number()?, inode: d.number()? };
    write_file(&mut Encoder::new(0), value)?;
    Ok(value)
}

/// Numeric pipe ends need not have the same inode on Darwin. Offered rights
/// are always ordered read, write; their actual access/transport is checked by
/// native code against the SAME original Root GNU owner, never by these bytes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GnuIdentity {
    NumericPipe { read: FileIdentity, write: FileIdentity },
    NamedFifo { path: Vec<u8>, backing: FileIdentity },
}
impl GnuIdentity {
    fn write(&self, e: &mut Encoder) -> io::Result<()> {
        match self {
            Self::NumericPipe { read, write } => {
                e.number(0);
                write_file(e, *read)?;
                write_file(e, *write)?;
            }
            Self::NamedFifo { path, backing } => {
                if !absolute(path) {
                    return Err(invalid());
                }
                e.number(1);
                e.bytes(path)?;
                write_file(e, *backing)?;
            }
        }
        Ok(())
    }
    fn read(d: &mut Decoder<'_>) -> io::Result<Self> {
        let value = match d.number()? {
            0 => Self::NumericPipe { read: read_file(d)?, write: read_file(d)? },
            1 => Self::NamedFifo { path: d.bytes()?, backing: read_file(d)? },
            _ => return Err(invalid()),
        };
        value.write(&mut Encoder::new(0))?;
        Ok(value)
    }
}

/// Separate short-lived connection BEFORE costly Steps or withholding. Support
/// observes live original-root eligibility; it reserves no future enrollment.
#[derive(Clone, PartialEq, Eq)]
pub struct SupportQuery {
    pub key: Key,
}
impl SupportQuery {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        let mut e = Encoder::new(71);
        e.number(0);
        self.key.write(&mut e)?;
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 71)?;
        if d.number()? != 0 {
            return Err(invalid());
        }
        let value = Self { key: Key::read(&mut d)? };
        d.done()?;
        Ok(value)
    }
    pub fn hello(&self) -> io::Result<Vec<u8>> {
        self.key.hello(SUPPORT_PURPOSE)
    }
}

/// Source/output are the actual parsed plan's observations. Output rights do
/// NOT exist at Preparation: they are attached only after actual acquisition.
#[derive(Clone, PartialEq, Eq)]
pub struct Enrollment {
    pub key: Key,
    pub source: Vec<u8>,
    pub output: Vec<u8>,
    pub gnu: GnuIdentity,
}
impl Enrollment {
    pub fn validate(&self) -> io::Result<()> {
        self.key.validate()?;
        if !absolute(&self.source) || !absolute(&self.output) || self.source == self.output {
            return Err(invalid());
        }
        self.gnu.write(&mut Encoder::new(0))
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        let mut e = Encoder::new(71);
        e.number(1);
        self.key.write(&mut e)?;
        e.bytes(&self.source)?;
        e.bytes(&self.output)?;
        self.gnu.write(&mut e)?;
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 71)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let value = Self {
            key: Key::read(&mut d)?,
            source: d.bytes()?,
            output: d.bytes()?,
            gnu: GnuIdentity::read(&mut d)?,
        };
        d.done()?;
        value.validate()?;
        Ok(value)
    }
    pub fn hello(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        self.key.hello(PURPOSE)
    }
    pub fn binding_preimage(&self) -> io::Result<Vec<u8>> {
        Ok(binding(b"trust-bootstrap-graph-enrollment/v1\0", self.encode()?))
    }
}

fn fixed_context(context: &ContextReply, key: &Key) -> io::Result<()> {
    // Syntax/equality only. The client separately authenticates actual pinned
    // Host, native peer, live Root and SAME original SDK/GNU/resource custody.
    ContextReply::decode(&context.encode()?, &key.query)?;
    if context.context.subject != (Subject::Root { identity: context.context.original_root })
        || !matches!(context.context.cpu, Cpu::RetainedFixed { .. })
        || context.context.sdk.is_none()
    {
        return Err(invalid());
    }
    Ok(())
}
fn binding(domain: &[u8], frame: Vec<u8>) -> Vec<u8> {
    let mut bytes = Vec::with_capacity(domain.len() + 8 + frame.len());
    bytes.extend(domain);
    bytes.extend((frame.len() as u64).to_be_bytes());
    bytes.extend(frame);
    bytes
}
fn refusal(e: &mut Encoder, reason: &str) -> io::Result<()> {
    if reason.is_empty() || reason.as_bytes().contains(&0) {
        return Err(invalid());
    }
    e.bytes(reason.as_bytes())
}

#[derive(Clone, PartialEq, Eq)]
pub enum SupportReply {
    Supported {
        key: Key,
        /// SAME actual Job's remaining lifetime, sampled immediately before
        /// reply. The client anchors it BEFORE sending, never at receipt.
        remaining_root_ns: u64,
        context: Box<ContextReply>,
    },
    Refused {
        key: Key,
        reason: String,
    },
}
impl SupportReply {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        let mut e = Encoder::new(72);
        e.number(0);
        match self {
            Self::Supported { key, remaining_root_ns, context } => {
                if *remaining_root_ns == 0 {
                    return Err(invalid());
                }
                e.number(0);
                key.write(&mut e)?;
                e.number(*remaining_root_ns);
                fixed_context(context, key)?;
                e.frame_bytes(&context.encode()?)?;
            }
            Self::Refused { key, reason } => {
                e.number(1);
                key.write(&mut e)?;
                refusal(&mut e, reason)?;
            }
        }
        e.finish()
    }
    pub fn decode(bytes: &[u8], query: &SupportQuery) -> io::Result<Self> {
        let mut d = header(bytes, 72)?;
        if d.number()? != 0 {
            return Err(invalid());
        }
        let kind = d.number()?;
        let key = Key::read(&mut d)?;
        if key != query.key {
            return Err(invalid());
        }
        let value = match kind {
            0 => Self::Supported {
                remaining_root_ns: d.number()?,
                context: Box::new(ContextReply::decode(&d.frame_bytes()?, &key.query)?),
                key,
            },
            1 => Self::Refused { key, reason: d.text()? },
            _ => return Err(invalid()),
        };
        d.done()?;
        value.encode()?;
        Ok(value)
    }
}

/// Prepared authorizes only receiving two descriptions. Enrolled follows the
/// Host's actual GNU validation/retention. Neither is child GO or retirement.
#[derive(Clone, PartialEq, Eq)]
pub enum EnrollmentReply {
    Prepared { key: Key, enrollment_sha256: [u8; 32], context: ContextReply },
    Enrolled { key: Key, enrollment_sha256: [u8; 32], context: ContextReply },
    Refused { key: Key, reason: String },
}
impl EnrollmentReply {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        let mut e = Encoder::new(72);
        e.number(1);
        match self {
            Self::Prepared { key, enrollment_sha256, context }
            | Self::Enrolled { key, enrollment_sha256, context } => {
                e.number(u64::from(matches!(self, Self::Enrolled { .. })));
                key.write(&mut e)?;
                e.0.extend(enrollment_sha256);
                fixed_context(context, key)?;
                e.frame_bytes(&context.encode()?)?;
            }
            Self::Refused { key, reason } => {
                e.number(2);
                key.write(&mut e)?;
                refusal(&mut e, reason)?;
            }
        }
        e.finish()
    }
    pub fn decode(
        bytes: &[u8],
        request: &Enrollment,
        expected_sha256: [u8; 32],
    ) -> io::Result<Self> {
        request.validate()?;
        let mut d = header(bytes, 72)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let kind = d.number()?;
        let key = Key::read(&mut d)?;
        if key != request.key {
            return Err(invalid());
        }
        let value = match kind {
            0 | 1 => {
                let enrollment_sha256 = d.array()?;
                if enrollment_sha256 != expected_sha256 {
                    return Err(invalid());
                }
                let context = ContextReply::decode(&d.frame_bytes()?, &key.query)?;
                if kind == 0 {
                    Self::Prepared { key, enrollment_sha256, context }
                } else {
                    Self::Enrolled { key, enrollment_sha256, context }
                }
            }
            2 => Self::Refused { key, reason: d.text()? },
            _ => return Err(invalid()),
        };
        d.done()?;
        value.encode()?;
        Ok(value)
    }
}

/// The SAME real OutputLock switches to close-only before rights are offered.
/// Root and lock descriptions are ordered as written here. Metadata, path and
/// received descriptors alone cannot reconstruct that original lock lineage.
#[derive(Clone, PartialEq, Eq)]
pub struct OutputAttachment {
    pub key: Key,
    pub root: FileIdentity,
    pub lock: FileIdentity,
}
impl OutputAttachment {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        let mut e = Encoder::new(73);
        e.number(1);
        self.key.write(&mut e)?;
        write_file(&mut e, self.root)?;
        write_file(&mut e, self.lock)?;
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 73)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let value =
            Self { key: Key::read(&mut d)?, root: read_file(&mut d)?, lock: read_file(&mut d)? };
        d.done()?;
        Ok(value)
    }
    pub fn binding_preimage(&self) -> io::Result<Vec<u8>> {
        Ok(binding(b"trust-bootstrap-graph-output/v1\0", self.encode()?))
    }
}

#[derive(Clone, PartialEq, Eq)]
pub enum OutputReply {
    Prepared { key: Key, attachment_sha256: [u8; 32], context: ContextReply },
    Attached { key: Key, attachment_sha256: [u8; 32], context: ContextReply },
    Refused { key: Key, reason: String },
}
impl OutputReply {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        let mut e = Encoder::new(74);
        e.number(1);
        match self {
            Self::Prepared { key, attachment_sha256, context }
            | Self::Attached { key, attachment_sha256, context } => {
                e.number(u64::from(matches!(self, Self::Attached { .. })));
                key.write(&mut e)?;
                e.0.extend(attachment_sha256);
                fixed_context(context, key)?;
                e.frame_bytes(&context.encode()?)?;
            }
            Self::Refused { key, reason } => {
                e.number(2);
                key.write(&mut e)?;
                refusal(&mut e, reason)?;
            }
        }
        e.finish()
    }
    pub fn decode(
        bytes: &[u8],
        request: &OutputAttachment,
        expected_sha256: [u8; 32],
    ) -> io::Result<Self> {
        request.encode()?;
        let mut d = header(bytes, 74)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let kind = d.number()?;
        let key = Key::read(&mut d)?;
        if key != request.key {
            return Err(invalid());
        }
        let value = match kind {
            0 | 1 => {
                let attachment_sha256 = d.array()?;
                if attachment_sha256 != expected_sha256 {
                    return Err(invalid());
                }
                let context = ContextReply::decode(&d.frame_bytes()?, &key.query)?;
                if kind == 0 {
                    Self::Prepared { key, attachment_sha256, context }
                } else {
                    Self::Attached { key, attachment_sha256, context }
                }
            }
            2 => Self::Refused { key, reason: d.text()? },
            _ => return Err(invalid()),
        };
        d.done()?;
        value.encode()?;
        Ok(value)
    }
}

#[cfg(test)]
mod tests;
#[cfg(test)]
pub(crate) use tests::context as test_context;
