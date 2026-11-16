// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Equality data for a separately negotiated contained produced operation.
//! These bytes cannot construct its live client owner or native retirement.

use std::io;

use super::Completion as ProducedCompletion;
use super::produced::ProducedRequest;
use crate::FileIdentity;
use crate::wire::{Encoder, header, invalid};

pub const PURPOSE: &str = "sealed-workload-contained-produced-v1";
const BINDING_DOMAIN: &[u8] = b"trust-contained-produced-operation-v1\0";

#[derive(Clone, PartialEq, Eq)]
pub struct Request {
    pub operation: [u8; 16],
    /// Observation of the SAME original named FIFO held by the actual phase.
    pub gnu: FileIdentity,
    pub produced: ProducedRequest,
}
impl Request {
    pub fn validate(&self) -> io::Result<()> {
        self.produced.validate()?;
        if self.operation == [0; 16]
            || self.operation == self.produced.member.member_attempt
            || self.operation == self.produced.key.root_attempt
            || self.operation == self.produced.key.phase
            || self.operation == self.produced.key.output
            || self.gnu.inode == 0
        {
            return Err(invalid());
        }
        Ok(())
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        let mut e = Encoder::new(52);
        e.number(4);
        e.0.extend(self.operation);
        e.number(self.gnu.device);
        e.number(self.gnu.inode);
        e.frame_bytes(&self.produced.encode()?)?;
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 52)?;
        if d.number()? != 4 {
            return Err(invalid());
        }
        let value = Self {
            operation: d.array()?,
            gnu: FileIdentity { device: d.number()?, inode: d.number()? },
            produced: ProducedRequest::decode(&d.frame_bytes()?)?,
        };
        d.done()?;
        value.validate()?;
        Ok(value)
    }
    pub fn binding_preimage(&self) -> io::Result<Vec<u8>> {
        let frame = self.encode()?;
        let mut bytes = Vec::with_capacity(BINDING_DOMAIN.len() + 8 + frame.len());
        bytes.extend(BINDING_DOMAIN);
        bytes.extend((frame.len() as u64).to_be_bytes());
        bytes.extend(frame);
        Ok(bytes)
    }
    pub fn hello(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        let attempt: String =
            self.produced.key.root_attempt.iter().map(|byte| format!("{byte:02x}")).collect();
        Ok(format!(
            "{{\"version\":3,\"role\":\"{PURPOSE}\",\"session\":\"{}\",\"attempt\":\"{attempt}\"}}",
            self.produced.member.binding.session
        )
        .into_bytes())
    }
}

/// DATA only. The client can accept this solely on its original negotiated
/// operation after native preparation/start, actual streams EOF and pin checks.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Completion {
    pub operation: [u8; 16],
    pub request_sha256: [u8; 32],
    pub gnu: FileIdentity,
    pub completion: ProducedCompletion,
}
impl Completion {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        if self.operation == [0; 16] || self.gnu.inode == 0 {
            return Err(invalid());
        }
        let mut e = Encoder::new(55);
        e.number(3);
        e.0.extend(self.operation);
        e.0.extend(self.request_sha256);
        e.number(self.gnu.device);
        e.number(self.gnu.inode);
        e.frame_bytes(&self.completion.encode()?)?;
        e.finish()
    }
    pub fn decode(bytes: &[u8], request: &Request, digest: [u8; 32]) -> io::Result<Self> {
        request.validate()?;
        let mut d = header(bytes, 55)?;
        if d.number()? != 3 {
            return Err(invalid());
        }
        let value = Self {
            operation: d.array()?,
            request_sha256: d.array()?,
            gnu: FileIdentity { device: d.number()?, inode: d.number()? },
            completion: ProducedCompletion::decode(
                &d.frame_bytes()?,
                request.produced.key.root_attempt,
                request.produced.member.member_attempt,
            )?,
        };
        d.done()?;
        if value.operation != request.operation
            || value.request_sha256 != digest
            || value.gnu != request.gnu
            || value.completion.phase != request.produced.key.ordinal
            || value.completion.kind != request.produced.kind
        {
            return Err(invalid());
        }
        value.encode()?;
        Ok(value)
    }
}

#[cfg(test)]
pub(crate) mod tests;
