// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Configuration-offer binding DATA for an already source-bound graph.
//! A decoded frame supplies neither the original issuing scope nor file custody.
//! The receiver must retain the actual offered description in its original Job.
use std::io;

use super::{Key, binding, fixed_context, read_file, refusal, write_file};
use crate::wire::{Decoder, Encoder, header, invalid};
use crate::{ContextReply, FileIdentity};

pub const MAX_BYTES: u64 = 4 * 1024 * 1024;
pub const MAX_FILES: usize = 64;
pub const MAX_COMPONENTS: usize = 64;
pub const MAX_COMPONENT_BYTES: usize = 255;
pub const RIGHTS_MARKER: u8 = 0x7a;
pub const MAX_INPUT_NS: u64 = 24 * 60 * 60 * 1_000_000_000;

/// Restrictive ordered-frame accounting, never input or resource ownership.
/// Reserve declared bytes before content validation; refusal never refunds a
/// prior accepted declaration or permits replaying a received description.
#[derive(Clone, Copy, Default)]
pub struct ConfigurationBudget {
    files: usize,
    bytes: u64,
}
impl ConfigurationBudget {
    pub fn remaining_files(&self) -> usize {
        MAX_FILES - self.files
    }
    pub fn remaining_bytes(&self) -> u64 {
        MAX_BYTES - self.bytes
    }
    pub fn reserve(&mut self, request: &ConfigurationAttachment) -> io::Result<()> {
        request.validate()?;
        if self.remaining_files() == 0
            || self.remaining_bytes() == 0
            || request.sequence != self.files as u64 + 1
            || request.bytes > self.remaining_bytes()
        {
            return Err(invalid());
        }
        self.files += 1;
        self.bytes += request.bytes;
        Ok(())
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Timestamp {
    pub seconds: i64,
    pub nanoseconds: u32,
}
impl Timestamp {
    fn write(self, e: &mut Encoder) -> io::Result<()> {
        if self.nanoseconds >= 1_000_000_000 {
            return Err(invalid());
        }
        e.number(self.seconds as u64);
        e.number(u64::from(self.nanoseconds));
        Ok(())
    }
    fn read(d: &mut Decoder<'_>) -> io::Result<Self> {
        let value = Self {
            seconds: d.number()? as i64,
            nanoseconds: d.number()?.try_into().map_err(|_| invalid())?,
        };
        value.write(&mut Encoder::new(0))?;
        Ok(value)
    }
}

/// A canonical root-relative selector, not permission to open another source.
pub fn relative(path: &[u8]) -> bool {
    if path.is_empty()
        || path.len() > MAX_COMPONENTS * (MAX_COMPONENT_BYTES + 1)
        || path.contains(&0)
    {
        return false;
    }
    let mut count = 0;
    for component in path.split(|byte| *byte == b'/') {
        count += 1;
        if count > MAX_COMPONENTS
            || component.is_empty()
            || component.len() > MAX_COMPONENT_BYTES
            || component == b"."
            || component == b".."
        {
            return false;
        }
    }
    true
}

/// Expectations about the actual retained file. No field grants access,
/// reconstructs a producer or extends the original graph's endpoint.
#[derive(Clone, PartialEq, Eq)]
pub struct ConfigurationAttachment {
    pub key: Key,
    /// Exact next attachment in this same graph; not an idempotent replay key.
    pub sequence: u64,
    pub relative: Vec<u8>,
    pub file: FileIdentity,
    pub bytes: u64,
    pub sha256: [u8; 32],
    pub modified: Timestamp,
    pub changed: Timestamp,
    /// Restrictive remaining time captured by the actual issuer before request.
    /// The native slot anchors it to its earlier original enrollment instant.
    pub input_remaining_ns: u64,
}

impl ConfigurationAttachment {
    pub fn validate(&self) -> io::Result<()> {
        self.key.validate()?;
        if !relative(&self.relative)
            || self.sequence == 0
            || self.sequence > MAX_FILES as u64
            || self.bytes > MAX_BYTES
            || !matches!(self.input_remaining_ns, 1..=MAX_INPUT_NS)
        {
            return Err(invalid());
        }
        let mut e = Encoder::new(0);
        write_file(&mut e, self.file)?;
        self.modified.write(&mut e)?;
        self.changed.write(&mut e)
    }

    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        let mut e = Encoder::new(114);
        e.number(2);
        self.key.write(&mut e)?;
        e.number(self.sequence);
        e.bytes(&self.relative)?;
        write_file(&mut e, self.file)?;
        e.number(self.bytes);
        e.0.extend(self.sha256);
        self.modified.write(&mut e)?;
        self.changed.write(&mut e)?;
        e.number(self.input_remaining_ns);
        e.finish()
    }

    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 114)?;
        if d.number()? != 2 {
            return Err(invalid());
        }
        let value = Self {
            key: Key::read(&mut d)?,
            sequence: d.number()?,
            relative: d.bytes()?,
            file: read_file(&mut d)?,
            bytes: d.number()?,
            sha256: d.array()?,
            modified: Timestamp::read(&mut d)?,
            changed: Timestamp::read(&mut d)?,
            input_remaining_ns: d.number()?,
        };
        d.done()?;
        value.validate()?;
        Ok(value)
    }

    pub fn binding_preimage(&self) -> io::Result<Vec<u8>> {
        Ok(binding(b"trust-bootstrap-graph-configuration/v2\0", self.encode()?))
    }
}

#[derive(Clone, PartialEq, Eq)]
pub enum ConfigurationReply {
    Prepared {
        key: Key,
        attachment_sha256: [u8; 32],
        remaining_input_ns: u64,
        context: ContextReply,
    },
    Attached {
        key: Key,
        attachment_sha256: [u8; 32],
        remaining_input_ns: u64,
        context: ContextReply,
    },
    Refused {
        key: Key,
        reason: String,
    },
}
impl ConfigurationReply {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        let mut e = Encoder::new(115);
        e.number(2);
        match self {
            Self::Prepared { key, attachment_sha256, remaining_input_ns, context }
            | Self::Attached { key, attachment_sha256, remaining_input_ns, context } => {
                if !matches!(*remaining_input_ns, 1..=MAX_INPUT_NS) {
                    return Err(invalid());
                }
                e.number(u64::from(matches!(self, Self::Attached { .. })));
                key.write(&mut e)?;
                e.0.extend(attachment_sha256);
                e.number(*remaining_input_ns);
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
        request: &ConfigurationAttachment,
        digest: [u8; 32],
    ) -> io::Result<Self> {
        request.validate()?;
        let mut d = header(bytes, 115)?;
        if d.number()? != 2 {
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
                if attachment_sha256 != digest {
                    return Err(invalid());
                }
                let remaining_input_ns = d.number()?;
                let context = ContextReply::decode(&d.frame_bytes()?, &key.query)?;
                if kind == 0 {
                    Self::Prepared { key, attachment_sha256, remaining_input_ns, context }
                } else {
                    Self::Attached { key, attachment_sha256, remaining_input_ns, context }
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
