// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! The distinct live workload-owner boundary. Decoding these bounded equality
//! inputs creates no original root, SDK/output owner, scheduling lease or GO.

use std::io;

use super::{WorkloadInvocation, path};

pub mod bank;
pub mod census;
pub mod contained;
pub mod coordinator;
pub mod initial;
pub mod keeper;
pub mod output;
pub mod partial;
pub mod phase;
pub mod produced;
pub mod publication;
pub mod worker;
use crate::wire::{Encoder, header, invalid};
use crate::{ContextQuery, ContextReply, GnuTransport, MetadataPrepared, Request, Role};

pub const QUERY_ROLE: u64 = 6;
pub const QUERY_PURPOSE: &str = "sealed-workload-query-v1";
pub const MAX_QUERY_NS: u64 = 30_000_000_000;
pub const MAX_QUERY_OUTPUT: usize = 64 * 1024;
pub const MAX_QUERIES: usize = 16;
pub const MAX_CPU_SET: usize = 128;
pub use super::budget::MAX_ROOT_TIMEOUT_MS;
/// Locator only; actual custody comes from the original native owner.
pub const CPU_SET_FDS_ENV: &str = "ATERM_WORKLOAD_CPU_FDS_V1";
/// Read-only discovery locator only. Original live context/SCM authenticates
/// every resource; a store directory or environment value grants none.
pub const HOST_STORE_FD_ENV: &str = "ATERM_WORKLOAD_HOST_STORE_FD_V1";
pub const CONTROL_FDS_ENV: &str = "ATERM_WORKLOAD_HOST_CONTROL_FDS_V1";
pub const CONTROL_ORIGINALS: usize = 9;
pub const CONTROL_TARGETS: [i32; CONTROL_ORIGINALS] = [10, 11, 12, 13, 14, 15, 16, 17, 18];
pub const CONTROL_ADVERTISEMENT: &str = "10,11,12,13,14,15,16,17,18";
pub const CPU_SET_MARKER: u8 = 0x57;
pub const MEMBER_ORIGINAL_PURPOSE: &str = "native-workload-member-original-v1";
pub const READY_CAPABILITIES_JSON: &str = r#"{"version":3,"purpose":"sealed-workload-v1","query_purpose":"sealed-workload-query-v1","query_role":6,"cpu_mode":"cooperative-shared","cpu_custody":"original-all-domain-descriptions-v1","crash_exclusion":"original-recoverable-domain-v1","context_sdk":"inherited-sdk-keeper-v1","output_custody":"original-output-root-v1","member_purpose":"sealed-workload-member-v1","member_role":7,"output_registration":"original-live-unit-output-v1","produced_preparation":"mixed-original-output-sdk-v1","output_lock_custody":"original-layout-ofd-close-only-v1","compiler_proxy":"original-store-fd-v1"}"#;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MemberKind {
    CompilerQuery,
    BuildScript,
    Inventory,
    Sample,
    /// Distinct produced Targo coordinator; never a libtest/build-script alias.
    Coordinator,
}

/// A bound terminal from the same owning wait, after native scope retirement
/// and input revalidation. It confers no output eligibility or execution right.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Completion {
    pub phase: u64,
    pub kind: MemberKind,
    pub completed: crate::MetadataCompletion,
    pub observation: crate::accounting::Observation,
}
impl Completion {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        if (self.phase == 0) != (self.kind == MemberKind::CompilerQuery) {
            return Err(invalid());
        }
        let mut e = Encoder::new(55);
        e.number(1);
        e.number(self.phase);
        e.number(match self.kind {
            MemberKind::CompilerQuery => 0,
            MemberKind::BuildScript => 1,
            MemberKind::Inventory => 2,
            MemberKind::Sample => 3,
            MemberKind::Coordinator => 4,
        });
        e.frame_bytes(&self.completed.encode()?)?;
        e.frame_bytes(&self.observation.encode()?)?;
        e.finish()
    }
    pub fn decode(bytes: &[u8], root: [u8; 16], member: [u8; 16]) -> io::Result<Self> {
        let mut d = header(bytes, 55)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let phase = d.number()?;
        let kind = match d.number()? {
            0 => MemberKind::CompilerQuery,
            1 => MemberKind::BuildScript,
            2 => MemberKind::Inventory,
            3 => MemberKind::Sample,
            4 => MemberKind::Coordinator,
            _ => return Err(invalid()),
        };
        let value = Self {
            phase,
            kind,
            completed: crate::MetadataCompletion::decode(&d.frame_bytes()?, root, member)?,
            observation: crate::accounting::Observation::decode(&d.frame_bytes()?)?,
        };
        d.done()?;
        value.encode()?;
        Ok(value)
    }
}

/// The SAME authenticated root supplies its initial invocation before Cargo
/// config, target discovery or compiler execution. The host independently
/// checks its original managed selection and opens the actual output owner.
#[derive(Clone, PartialEq, Eq)]
pub struct ReadyRequest {
    pub query: ContextQuery,
    pub invocation: WorkloadInvocation,
}
impl ReadyRequest {
    pub fn validate(&self) -> io::Result<()> {
        self.query.validate()?;
        self.invocation.validate()
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        let mut e = Encoder::new(48);
        e.number(1);
        e.frame_bytes(&self.query.encode()?)?;
        e.frame_bytes(&self.invocation.encode()?)?;
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 48)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let value = Self {
            query: ContextQuery::decode(&d.frame_bytes()?)?,
            invocation: WorkloadInvocation::decode(&d.frame_bytes()?)?,
        };
        d.done()?;
        value.validate()?;
        Ok(value)
    }
}

/// Observations from the original live owner, never a serialized root or
/// produced-program permit. The client still validates its inherited SDK and
/// real canonical CPU transport independently before any compiler query.
#[derive(Clone, PartialEq, Eq)]
pub struct ReadyReply {
    pub context: ContextReply,
    pub invocation_sha256: [u8; 32],
    pub primary: PrimaryCpu,
    pub supplementary: Vec<PrimaryCpu>,
}
/// Equality observation of the original inherited kernel-backed description.
/// Only actual inherited-file adoption can yield a native execution unit.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrimaryCpu {
    pub inherited_fd: u32,
    pub slot: u32,
    pub backing: crate::FileIdentity,
}

/// Bootstrap for an already registered compiler. Neither a decoded context
/// nor this request can create a CPU owner or select another member's slot.
#[derive(Clone, PartialEq, Eq)]
pub struct MemberOriginalRequest {
    pub query: ContextQuery,
    pub member_attempt: [u8; 16],
}
impl MemberOriginalRequest {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.query.validate()?;
        if self.member_attempt == [0; 16] || self.member_attempt == self.query.binding.root_attempt
        {
            return Err(invalid());
        }
        let mut e = Encoder::new(50);
        e.number(2);
        e.frame_bytes(&self.query.encode()?)?;
        e.0.extend(self.member_attempt);
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 50)?;
        if d.number()? != 2 {
            return Err(invalid());
        }
        let value =
            Self { query: ContextQuery::decode(&d.frame_bytes()?)?, member_attempt: d.array()? };
        d.done()?;
        value.encode()?;
        Ok(value)
    }
    pub fn hello(&self) -> io::Result<Vec<u8>> {
        self.encode()?;
        let attempt: String =
            self.query.binding.root_attempt.iter().map(|byte| format!("{byte:02x}")).collect();
        Ok(format!("{{\"version\":3,\"role\":\"{MEMBER_ORIGINAL_PURPOSE}\",\"session\":\"{}\",\"attempt\":\"{attempt}\"}}",self.query.binding.session).into_bytes())
    }
}
#[derive(Clone, PartialEq, Eq)]
pub struct MemberOriginalReply {
    pub context: ContextReply,
    pub cpu: PrimaryCpu,
}
impl MemberOriginalReply {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        if !matches!(self.context.context.subject, crate::Subject::RegisteredMember { .. })
            || !matches!(self.context.context.cpu, crate::Cpu::CooperativeShared { .. })
            || self.context.context.sdk.is_none()
            || self.cpu.inherited_fd < 6
            || self.cpu.inherited_fd > i32::MAX as u32
            || self.cpu.slot >= MAX_CPU_SET as u32
            || self.cpu.backing.inode == 0
        {
            return Err(invalid());
        }
        let mut e = Encoder::new(49);
        e.number(2);
        e.frame_bytes(&self.context.encode()?)?;
        e.number(self.cpu.inherited_fd.into());
        e.number(self.cpu.slot.into());
        e.number(self.cpu.backing.device);
        e.number(self.cpu.backing.inode);
        e.finish()
    }
    pub fn decode(bytes: &[u8], request: &MemberOriginalRequest) -> io::Result<Self> {
        let mut d = header(bytes, 49)?;
        if d.number()? != 2 {
            return Err(invalid());
        }
        let value = Self {
            context: ContextReply::decode(&d.frame_bytes()?, &request.query)?,
            cpu: PrimaryCpu {
                inherited_fd: d.narrow()?,
                slot: d.narrow()?,
                backing: crate::FileIdentity { device: d.number()?, inode: d.number()? },
            },
        };
        d.done()?;
        value.encode()?;
        if !matches!(value.context.context.subject,crate::Subject::RegisteredMember{attempt,..} if attempt==request.member_attempt)
        {
            return Err(invalid());
        }
        Ok(value)
    }
}
impl ReadyReply {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        let mut e = Encoder::new(49);
        e.number(1);
        e.frame_bytes(&self.context.encode()?)?;
        e.0.extend(self.invocation_sha256);
        if !matches!(self.context.context.cpu, crate::Cpu::CooperativeShared { .. })
            || self.context.context.sdk.is_none()
        {
            return Err(invalid());
        }
        let set: Vec<_> = self.cpu_set().collect();
        if set.is_empty() || set.len() > MAX_CPU_SET {
            return Err(invalid());
        }
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
        let mut d = header(bytes, 49)?;
        if d.number()? != 1 {
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
    pub fn cpu_set(&self) -> impl Iterator<Item = &PrimaryCpu> {
        std::iter::once(&self.primary).chain(&self.supplementary)
    }
}

/// One non-producing, host-only compiler query under the separately ready
/// cooperative workload root. A live borrowed canonical CPU is mandatory;
/// there is no numeric GNU context, new credit or resolver-role conversion.
#[derive(Clone, PartialEq, Eq)]
pub struct CompilerQuery {
    pub member: Request,
    pub root: Vec<u8>,
    pub program_sha256: [u8; 32],
}

pub(crate) fn validate_query_member(member: &Request) -> io::Result<()> {
    crate::resolver::classify_resolver_query(&member.command.args)?;
    if !matches!(member.timeout_ns, Some(1..=MAX_QUERY_NS))
        || member.command.arg0.is_some()
        || member.delegations.cpu.is_none()
        || !matches!(member.delegations.gnu, GnuTransport::None)
        || !member.delegations.fences.is_empty()
        || member.command.environment.len() != 6
        || member.command.environment.iter().any(|(name, value)| match name.as_slice() {
            b"LANG" | b"LC_ALL" => value != b"C",
            b"CARGO" | b"CARGO_HOME" => !path(value),
            b"RUSTC" => value != &member.command.program,
            b"CARGO_CACHE_RUSTC_INFO" => value != b"0",
            _ => true,
        })
    {
        return Err(invalid());
    }
    Ok(())
}

impl CompilerQuery {
    pub fn validate(&self) -> io::Result<()> {
        self.member.validate()?;
        let mut compiler = self.root.clone();
        compiler.extend_from_slice(b"/bin/trustc");
        let mut targo = self.root.clone();
        targo.extend_from_slice(b"/bin/targo");
        if self.member.role != Role::WorkloadQuery
            || !path(&self.root)
            || self.member.command.program != compiler
            || self
                .member
                .command
                .environment
                .iter()
                .any(|(name, value)| name == b"CARGO" && value != &targo)
        {
            return Err(invalid());
        }
        Ok(())
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        let mut e = Encoder::new(50);
        e.number(1);
        e.frame_bytes(&self.member.encode()?)?;
        e.bytes(&self.root)?;
        e.0.extend(self.program_sha256);
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 50)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let value = Self {
            member: Request::decode(&d.frame_bytes()?)?,
            root: d.bytes()?,
            program_sha256: d.array()?,
        };
        d.done()?;
        value.validate()?;
        Ok(value)
    }
    pub fn hello(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        let attempt = self
            .member
            .binding
            .root_attempt
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect::<String>();
        Ok(format!(
            "{{\"version\":3,\"role\":\"{QUERY_PURPOSE}\",\"session\":\"{}\",\"attempt\":\"{attempt}\"}}",
            self.member.binding.session,
        ).into_bytes())
    }
    pub fn validate_prepared(&self, prepared: &MetadataPrepared) -> io::Result<()> {
        prepared.validate_for_workload_query(self)
    }
}

#[cfg(test)]
mod tests;
