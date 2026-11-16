//! Close-only source-custody binding DATA. These frames never reconstruct a
//! Manager, ProtectedWorkScope, lease, release operation or source-tree freeze.
use std::io;

use super::{Key, binding, fixed_context, read_file, refusal, write_file};
use crate::wire::{Decoder, Encoder, header, invalid};
use crate::{ContextReply, FileIdentity};

pub mod decision;

pub const RECORD_LIMIT: u64 = 16 * 1024;
pub const ATTACHMENT_LIMIT: usize = 8192;
pub const HOLDER_NAME: &[u8] = b".trust-build-lock";
pub const RIGHTS_MARKER: u8 = 0x79;
pub const DESCRIPTION_COUNT: usize = 4;

/// Only length/hash DATA leaves the original producer; private record text,
/// including lease tokens, is neither serialized nor exposed by Debug.
#[derive(Clone, PartialEq, Eq)]
pub struct SourceRecord {
    pub identity: FileIdentity,
    pub bytes: u64,
    pub sha256: [u8; 32],
}
impl SourceRecord {
    fn write(&self, e: &mut Encoder) -> io::Result<()> {
        if self.bytes == 0 || self.bytes > RECORD_LIMIT {
            return Err(invalid());
        }
        write_file(e, self.identity)?;
        e.number(self.bytes);
        e.0.extend(self.sha256);
        Ok(())
    }
    fn read(d: &mut Decoder<'_>) -> io::Result<Self> {
        let value = Self { identity: read_file(d)?, bytes: d.number()?, sha256: d.array()? };
        value.write(&mut Encoder::new(0))?;
        Ok(value)
    }
}

/// Ordered descriptions are the same original source root, holder directory,
/// acquired record (possibly unlinked), and current published WITHHELD record.
#[derive(Clone, PartialEq, Eq)]
pub struct SourceAttachment {
    pub key: Key,
    pub source_directory: FileIdentity,
    pub holder_directory: FileIdentity,
    pub holder_name: Vec<u8>,
    pub original_record: SourceRecord,
    pub withheld_record: SourceRecord,
}
impl SourceAttachment {
    pub fn validate(&self) -> io::Result<()> {
        self.key.validate()?;
        if self.holder_name != HOLDER_NAME
            || self.source_directory == self.holder_directory
            || self.original_record.identity == self.withheld_record.identity
        {
            return Err(invalid());
        }
        let mut e = Encoder::new(0);
        write_file(&mut e, self.source_directory)?;
        write_file(&mut e, self.holder_directory)?;
        self.original_record.write(&mut e)?;
        self.withheld_record.write(&mut e)
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        let mut e = Encoder::new(106);
        e.number(1);
        self.key.write(&mut e)?;
        write_file(&mut e, self.source_directory)?;
        write_file(&mut e, self.holder_directory)?;
        e.bytes(&self.holder_name)?;
        self.original_record.write(&mut e)?;
        self.withheld_record.write(&mut e)?;
        let bytes = e.finish()?;
        if bytes.len() > ATTACHMENT_LIMIT { Err(invalid()) } else { Ok(bytes) }
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        if bytes.len() > ATTACHMENT_LIMIT {
            return Err(invalid());
        }
        let mut d = header(bytes, 106)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let value = Self {
            key: Key::read(&mut d)?,
            source_directory: read_file(&mut d)?,
            holder_directory: read_file(&mut d)?,
            holder_name: d.bytes()?,
            original_record: SourceRecord::read(&mut d)?,
            withheld_record: SourceRecord::read(&mut d)?,
        };
        d.done()?;
        value.validate()?;
        Ok(value)
    }
    pub fn binding_preimage(&self) -> io::Result<Vec<u8>> {
        Ok(binding(b"trust-bootstrap-graph-source/v1\0", self.encode()?))
    }
}

#[derive(Clone, PartialEq, Eq)]
pub enum SourceReply {
    Prepared { key: Key, attachment_sha256: [u8; 32], context: ContextReply },
    Attached { key: Key, attachment_sha256: [u8; 32], context: ContextReply },
    Refused { key: Key, reason: String },
}
impl SourceReply {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        let mut e = Encoder::new(107);
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
        request: &SourceAttachment,
        expected_sha256: [u8; 32],
    ) -> io::Result<Self> {
        request.validate()?;
        let mut d = header(bytes, 107)?;
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
