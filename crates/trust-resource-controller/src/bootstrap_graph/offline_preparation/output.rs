// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Distinct physical output custody DATA before Configuration. These frames
//! do not seal a configuration set, instantiate OutputLock, or issue a Seed,
//! SDK, producer, native completion or permission to replace original guards.
use super::*;
use crate::ContextReply;
use crate::bootstrap_graph::{OutputAttachment, fixed_context};

pub const RIGHTS_MARKER: u8 = 0x7b;

#[derive(Clone, PartialEq, Eq)]
pub struct PreparationOutputAttachment {
    pub key: OperationKey,
    pub root: FileIdentity,
    pub lock: FileIdentity,
}
impl PreparationOutputAttachment {
    pub fn validate(&self) -> io::Result<()> {
        self.key.validate()?;
        if self.key.sequence != 1 || self.root == self.lock {
            return Err(invalid());
        }
        self.physical_binding().encode().map(|_| ())
    }
    /// Equality DATA for the existing descriptor checker, never an accepted
    /// final-output offer or a configured bundle/lock owner.
    pub fn physical_binding(&self) -> OutputAttachment {
        OutputAttachment {
            key: self.key.graph.clone(),
            root: self.root,
            lock: self.lock,
        }
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        let mut e = Encoder::new(135);
        e.number(1);
        self.key.write(&mut e)?;
        write_file(&mut e, self.root)?;
        write_file(&mut e, self.lock)?;
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 135)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let value = Self {
            key: OperationKey::read(&mut d)?,
            root: read_file(&mut d)?,
            lock: read_file(&mut d)?,
        };
        d.done()?;
        value.validate()?;
        Ok(value)
    }
    pub fn binding_preimage(&self) -> io::Result<Vec<u8>> {
        Ok(crate::bootstrap_graph::binding(
            b"trust-bootstrap-preparation-output-custody/v1\0",
            self.encode()?,
        ))
    }
}

#[derive(Clone, PartialEq, Eq)]
pub enum PreparationOutputReply {
    Prepared {
        request: PreparationOutputAttachment,
        attachment_sha256: [u8; 32],
        remaining_input_ns: u64,
        context: ContextReply,
    },
    Custodied {
        request: PreparationOutputAttachment,
        attachment_sha256: [u8; 32],
        remaining_input_ns: u64,
        context: ContextReply,
    },
}
impl PreparationOutputReply {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        let mut e = Encoder::new(136);
        e.number(1);
        let (request, digest, remaining, context) = match self {
            Self::Prepared {
                request,
                attachment_sha256,
                remaining_input_ns,
                context,
            }
            | Self::Custodied {
                request,
                attachment_sha256,
                remaining_input_ns,
                context,
            } => (request, attachment_sha256, remaining_input_ns, context),
        };
        if !matches!(*remaining, 1..=MAX_BUDGET_NS) {
            return Err(invalid());
        }
        e.number(u64::from(matches!(self, Self::Custodied { .. })));
        e.frame_bytes(&request.encode()?)?;
        e.0.extend(digest);
        e.number(*remaining);
        fixed_context(context, &request.key.graph)?;
        e.frame_bytes(&context.encode()?)?;
        e.finish()
    }
    pub fn decode(
        bytes: &[u8],
        original: &PreparationOutputAttachment,
        expected_sha256: [u8; 32],
    ) -> io::Result<Self> {
        original.validate()?;
        let mut d = header(bytes, 136)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let kind = d.number()?;
        let request = PreparationOutputAttachment::decode(&d.frame_bytes()?)?;
        let attachment_sha256 = d.array()?;
        if request != *original || attachment_sha256 != expected_sha256 {
            return Err(invalid());
        }
        let remaining_input_ns = d.number()?;
        let context = ContextReply::decode(&d.frame_bytes()?, &request.key.graph.query)?;
        d.done()?;
        let value = match kind {
            0 => Self::Prepared {
                request,
                attachment_sha256,
                remaining_input_ns,
                context,
            },
            1 => Self::Custodied {
                request,
                attachment_sha256,
                remaining_input_ns,
                context,
            },
            _ => return Err(invalid()),
        };
        value.encode()?;
        Ok(value)
    }
}

#[cfg(test)]
mod tests;
