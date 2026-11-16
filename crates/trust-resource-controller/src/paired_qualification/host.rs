// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Distinct paired Ready48/49-v2 equality data. These frames never construct
//! original CPU/SDK/output custody, a startup owner, or an execution grant.
use std::io;

use super::PairedInvocation;
use crate::wire::{Encoder, header, invalid};
use crate::workload::host::{MAX_CPU_SET, PrimaryCpu};
use crate::{ContextQuery, ContextReply};

/// A separate original-store ingress, never an expansion of workload-v1.
pub const ORIGINAL_STORE_EXPECTATION_ARGUMENT: &str = "--expect-paired-original-store-fd";
pub const ORIGINAL_STORE_CAPABILITY: &str = "paired-qualification-original-store-fd-v1";
pub const READY_CAPABILITIES_JSON: &str = r#"{"version":3,"purpose":"sealed-paired-qualification-v1","invocation_kind":60,"ready_version":2,"query_purpose":"sealed-paired-qualification-query-v1","query_role":6,"query_version":2,"cpu_mode":"cooperative-shared","cpu_custody":"original-all-domain-descriptions-v1","crash_exclusion":"original-recoverable-domain-v1","context_sdk":"inherited-sdk-keeper-v1","output_custody":"original-output-root-v1","member_purpose":"sealed-workload-member-v1","member_role":7,"output_registration":"original-live-unit-output-v1","produced_preparation":"mixed-original-output-sdk-v1","output_lock_custody":"original-layout-ofd-close-only-v1","compiler_proxy":"original-store-fd-v1","root_store_expectation":"paired-qualification-original-store-fd-v1"}"#;

#[derive(Clone, PartialEq, Eq)]
pub struct ReadyRequest {
    pub query: ContextQuery,
    pub invocation: PairedInvocation,
}
impl ReadyRequest {
    pub fn validate(&self) -> io::Result<()> {
        self.query.validate()?;
        self.invocation.validate()
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        let mut e = Encoder::new(48);
        e.number(2);
        e.frame_bytes(&self.query.encode()?)?;
        e.frame_bytes(&self.invocation.encode()?)?;
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 48)?;
        if d.number()? != 2 {
            return Err(invalid());
        }
        let value = Self {
            query: ContextQuery::decode(&d.frame_bytes()?)?,
            invocation: PairedInvocation::decode(&d.frame_bytes()?)?,
        };
        d.done()?;
        value.validate()?;
        Ok(value)
    }
}

/// Plain observations of the same original host. The digest is SHA256 of
/// PairedInvocation::binding_preimage(), including the entire 60 frame. It must
/// never be the digest of the consumer 40 subplan. Authentication/adoption must
/// independently match this digest and the actual inherited SCM descriptions.
#[derive(Clone, PartialEq, Eq)]
pub struct ReadyReply {
    pub context: ContextReply,
    pub invocation_sha256: [u8; 32],
    pub primary: PrimaryCpu,
    pub supplementary: Vec<PrimaryCpu>,
}
impl ReadyReply {
    pub fn cpu_set(&self) -> impl Iterator<Item = &PrimaryCpu> {
        std::iter::once(&self.primary).chain(&self.supplementary)
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        if self.invocation_sha256 == [0; 32]
            || !matches!(self.context.context.cpu, crate::Cpu::CooperativeShared { .. })
            || self.context.context.sdk.is_none()
        {
            return Err(invalid());
        }
        let set: Vec<_> = self.cpu_set().collect();
        if set.is_empty() || set.len() > MAX_CPU_SET {
            return Err(invalid());
        }
        let mut e = Encoder::new(49);
        e.number(2);
        e.frame_bytes(&self.context.encode()?)?;
        e.0.extend(self.invocation_sha256);
        e.number(set.len() as u64);
        for (index, cpu) in set.iter().enumerate() {
            if cpu.inherited_fd < 6
                || cpu.inherited_fd > i32::MAX as u32
                || cpu.backing.inode == 0
                || set[..index].iter().any(|other| {
                    other.inherited_fd == cpu.inherited_fd
                        || other.slot == cpu.slot
                        || other.backing == cpu.backing
                })
            {
                return Err(invalid());
            }
            e.number(cpu.inherited_fd.into());
            e.number(cpu.slot.into());
            e.number(cpu.backing.device);
            e.number(cpu.backing.inode);
        }
        e.finish()
    }
    pub fn decode(bytes: &[u8], request: &ReadyRequest) -> io::Result<Self> {
        request.validate()?;
        let mut d = header(bytes, 49)?;
        if d.number()? != 2 {
            return Err(invalid());
        }
        let context = ContextReply::decode(&d.frame_bytes()?, &request.query)?;
        let invocation_sha256 = d.array()?;
        let count = usize::try_from(d.number()?).map_err(|_| invalid())?;
        if count == 0 || count > MAX_CPU_SET {
            return Err(invalid());
        }
        let mut set = Vec::with_capacity(count);
        for _ in 0..count {
            set.push(PrimaryCpu {
                inherited_fd: d.narrow()?,
                slot: d.narrow()?,
                backing: crate::FileIdentity { device: d.number()?, inode: d.number()? },
            });
        }
        let primary = set.remove(0);
        let value = Self { context, invocation_sha256, primary, supplementary: set };
        d.done()?;
        value.encode()?;
        Ok(value)
    }
}

#[cfg(test)]
mod tests;
