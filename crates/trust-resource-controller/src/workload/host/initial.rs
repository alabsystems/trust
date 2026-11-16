// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Distinct initial-pair equality DATA. Only the live pinned Host and the
//! original inherited/SCM descriptions construct authenticated startup custody.
use std::io;

use super::{MAX_CPU_SET, PrimaryCpu};
use crate::wire::{Encoder, header, invalid};
use crate::workload::WorkloadInvocation;
use crate::{ContextQuery, ContextReply, Cpu};

pub const STARTUP_ARGUMENT: &str = "--resource-workload-v2";
pub const READY_ROLE: &str = "native-workload-initial-ready-v2";
pub const READY_CAPABILITIES_JSON: &str = r#"{"version":3,"purpose":"sealed-workload-initial-pair-v2","ready_version":5,"cpu_mode":"cooperative-shared","cpu_custody":"original-initial-pair-v2","phase_custody":"original-partial-v2","context_sdk":"inherited-sdk-keeper-v1","output_custody":"original-output-root-v1"}"#;
/// Installed by the SAME original Initial launcher, disjoint from native6,
/// SDK5, store3 and stdio. These numbers are locators, never a grant.
pub const SHADOW_FD: i32 = 7;
pub const MEMORY_GUARD_FD: i32 = 8;
pub const PRIMARY_FD: i32 = 6;

#[derive(Clone, PartialEq, Eq)]
pub struct ReadyRequest {
    pub query: ContextQuery,
    pub invocation: WorkloadInvocation,
    pub phase: [u8; 16],
}
impl ReadyRequest {
    pub fn validate(&self) -> io::Result<()> {
        self.query.validate()?;
        self.invocation.validate()?;
        if self.phase == [0; 16] || self.phase == self.query.binding.root_attempt {
            return Err(invalid());
        }
        Ok(())
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        let mut e = Encoder::new(48);
        e.number(5);
        e.frame_bytes(&self.query.encode()?)?;
        e.frame_bytes(&self.invocation.encode()?)?;
        e.0.extend(self.phase);
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 48)?;
        if d.number()? != 5 {
            return Err(invalid());
        }
        let value = Self {
            query: ContextQuery::decode(&d.frame_bytes()?)?,
            invocation: WorkloadInvocation::decode(&d.frame_bytes()?)?,
            phase: d.array()?,
        };
        d.done()?;
        value.validate()?;
        Ok(value)
    }
}

/// Maximum N remains in the original context; exactly ONE actual initial
/// description is reported here. This is never a V1 all-domain ReadyReply.
#[derive(Clone, PartialEq, Eq)]
pub struct ReadyReply {
    pub context: ContextReply,
    /// SHA256 of the WHOLE ReadyRequest, including its distinct phase/query.
    pub invocation_sha256: [u8; 32],
    pub phase: [u8; 16],
    pub primary: PrimaryCpu,
    /// Authenticated equality binding for the actual installed originals.
    /// This record alone constructs no resource or worker authority.
    pub keeper: super::keeper::Request,
}
impl ReadyReply {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        let Cpu::CooperativeShared { ceiling, .. } = self.context.context.cpu else {
            return Err(invalid());
        };
        if ceiling == 0
            || ceiling as usize > MAX_CPU_SET
            || self.context.context.sdk.is_none()
            || !matches!(self.context.context.subject, crate::Subject::Root { identity }
                if identity == self.context.context.original_root)
            || self.phase == [0; 16]
            || self.phase == self.context.context.root_attempt
            || self.primary.inherited_fd != PRIMARY_FD as u32
            || self.primary.slot >= ceiling
            || self.primary.backing.inode == 0
            || self.keeper.root_attempt != self.context.context.root_attempt
            || self.keeper.invocation_sha256 != self.invocation_sha256
            || self.keeper.phase != self.phase
            || self.keeper.native_slot != self.primary.slot
            || self.keeper.native != self.primary.backing
            || self.keeper.memory_guard != self.context.context.memory.guard
            || self.keeper.memory_epoch != self.context.context.memory.epoch
        {
            return Err(invalid());
        }
        let mut e = Encoder::new(49);
        e.number(5);
        e.frame_bytes(&self.context.encode()?)?;
        e.0.extend(self.invocation_sha256);
        e.0.extend(self.phase);
        e.number(self.primary.inherited_fd.into());
        e.number(self.primary.slot.into());
        e.number(self.primary.backing.device);
        e.number(self.primary.backing.inode);
        e.frame_bytes(&self.keeper.encode()?)?;
        e.finish()
    }
    pub fn decode(bytes: &[u8], request: &ReadyRequest) -> io::Result<Self> {
        let mut d = header(bytes, 49)?;
        if d.number()? != 5 {
            return Err(invalid());
        }
        let value = Self {
            context: ContextReply::decode(&d.frame_bytes()?, &request.query)?,
            invocation_sha256: d.array()?,
            phase: d.array()?,
            primary: PrimaryCpu {
                inherited_fd: d.narrow()?,
                slot: d.narrow()?,
                backing: crate::FileIdentity { device: d.number()?, inode: d.number()? },
            },
            keeper: super::keeper::Request::decode(&d.frame_bytes()?)?,
        };
        d.done()?;
        value.encode()?;
        if value.phase != request.phase {
            return Err(invalid());
        }
        Ok(value)
    }
}
