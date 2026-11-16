// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Preparation binding DATA; only the resident Job can own a fresh workspace.
use std::io;

use super::{Key, binding, fixed_context, refusal};
use crate::wire::{Encoder, header, invalid};
use crate::{ContextReply, FileIdentity};

#[derive(Clone, PartialEq, Eq)]
pub struct MaterializationPreparation {
    pub key: Key,
    pub input_remaining_ns: u64,
}
impl MaterializationPreparation {
    pub fn validate(&self) -> io::Result<()> {
        self.key.validate()?;
        if !matches!(self.input_remaining_ns, 1..=super::configuration::MAX_INPUT_NS) {
            return Err(invalid());
        }
        Ok(())
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        let mut e = Encoder::new(116);
        e.number(1);
        self.key.write(&mut e)?;
        e.number(self.input_remaining_ns);
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 116)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let value = Self { key: Key::read(&mut d)?, input_remaining_ns: d.number()? };
        d.done()?;
        value.validate()?;
        Ok(value)
    }
    pub fn binding_preimage(&self) -> io::Result<Vec<u8>> {
        Ok(binding(b"trust-bootstrap-graph-materialization-preparation/v1\0", self.encode()?))
    }
}

#[derive(Clone, PartialEq, Eq)]
pub enum MaterializationReply {
    Prepared {
        key: Key,
        preparation_sha256: [u8; 32],
        remaining_input_ns: u64,
        /// Actual resident workspace observation, never a directory/owner grant.
        contents_directory: FileIdentity,
        context: Box<ContextReply>,
    },
    Refused {
        key: Key,
        reason: String,
    },
}
impl MaterializationReply {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        let mut e = Encoder::new(117);
        e.number(2);
        match self {
            Self::Prepared {
                key,
                preparation_sha256,
                remaining_input_ns,
                contents_directory,
                context,
            } => {
                if !matches!(*remaining_input_ns, 1..=super::configuration::MAX_INPUT_NS) {
                    return Err(invalid());
                }
                e.number(0);
                key.write(&mut e)?;
                e.0.extend(preparation_sha256);
                e.number(*remaining_input_ns);
                super::write_file(&mut e, *contents_directory)?;
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
    pub fn decode(
        bytes: &[u8],
        request: &MaterializationPreparation,
        digest: [u8; 32],
    ) -> io::Result<Self> {
        request.validate()?;
        let mut d = header(bytes, 117)?;
        if d.number()? != 2 {
            return Err(invalid());
        }
        let kind = d.number()?;
        let key = Key::read(&mut d)?;
        if key != request.key {
            return Err(invalid());
        }
        let value = match kind {
            0 => {
                let preparation_sha256 = d.array()?;
                if preparation_sha256 != digest {
                    return Err(invalid());
                }
                let remaining_input_ns = d.number()?;
                let contents_directory = super::read_file(&mut d)?;
                let context = Box::new(ContextReply::decode(&d.frame_bytes()?, &key.query)?);
                Self::Prepared {
                    key,
                    preparation_sha256,
                    remaining_input_ns,
                    contents_directory,
                    context,
                }
            }
            1 => Self::Refused { key, reason: d.text()? },
            _ => return Err(invalid()),
        };
        d.done()?;
        value.encode()?;
        Ok(value)
    }
}

#[cfg(test)]
mod tests;
