// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Selected serial produced-toolchain work. These are equality/request bytes;
//! only the live original Host can lend its actual parent-bank primary and
//! original Layout descriptions to the separately held produced coordinator.
use std::collections::BTreeSet;
use std::io;

use super::{MemberKind, PrimaryCpu, contained, output};
use crate::wire::{Encoder, header, invalid};
use crate::workload::{InputFile, contains, path};
use crate::{ContextQuery, ContextReply, Descriptor};

pub const PURPOSE: &str = "native-produced-coordinator-v1";
pub const ORIGINAL_PURPOSE: &str = "native-produced-coordinator-original-v1";
pub const STARTUP_ARGUMENT: &str = "--resource-candidate-coordinator-v1";
pub const COMPILER_ROLE: u64 = 8;
pub const MARKER: u8 = 0x5c;
pub const MAX_SOURCES: usize = 32;
pub const MAX_PLAN_BYTES: usize = crate::MAX_FIELD / 2;
mod broker;
pub(crate) use broker::{command_read, command_write};
mod compiler;
mod scope;
#[cfg(all(feature = "client", any(target_os = "linux", target_os = "macos")))]
pub(crate) use broker::BrokerEvent;
pub use compiler::{
    CompilerPrepared, CompilerSelection, TRANSPORT_MARKER, TRANSPORT_ORIGINALS, TRANSPORT_PURPOSE,
    TransportReply, TransportRequest, compiler_producing_command, compiler_query_command,
    compiler_transport_environment_name,
};
pub use scope::{
    MAX_SCOPE_FILES, SCOPE_MARKER, SCOPE_PURPOSE, ScopeFile, ScopeReply, ScopeRequest,
};
#[cfg(test)]
mod tests;
pub use broker::{BrokerCaptureData, BrokerLimits, BrokerRequest, PublicationSelection, StreamEnd};

/// Actual prepared target observations, accepted only on the original owning
/// member stream. Decoding this neither creates its owner nor sends target GO.
#[derive(Clone, PartialEq, Eq)]
pub struct Prepared {
    pub produced: super::produced::ProducedPrepared,
    pub command: crate::CommandSpec,
}
impl Prepared {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        let mut e = Encoder::new(85);
        e.number(1);
        e.frame_bytes(&self.produced.encode()?)?;
        broker::command_write(&self.command, &mut e)?;
        e.finish()
    }
    pub fn decode(bytes: &[u8], request: &Request) -> io::Result<Self> {
        let mut d = header(bytes, 85)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let produced = super::produced::ProducedPrepared::decode(
            &d.frame_bytes()?,
            &request.contained.produced,
        )?;
        let command = broker::command_read(&mut d)?;
        d.done()?;
        let original = &request.contained.produced.member.command;
        if command.program != original.program
            || command.arg0 != original.arg0
            || command.cwd != original.cwd
            || command.args != original.args
        {
            return Err(invalid());
        }
        let value = Self { produced, command };
        value.encode()?;
        Ok(value)
    }
}
/// Parent's one-shot expected semantic binding, DATA only. The actual original
/// member, source/SDK/output/resources and native target preparation authorize
/// execution; these hashes confer no validation, qualification or proof grade.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SemanticSelection {
    pub root_attempt: [u8; 16],
    pub member_attempt: [u8; 16],
    pub prepared_sha256: [u8; 32],
    pub configuration_sha256: [u8; 32],
    pub coverage_sha256: [u8; 32],
}
impl SemanticSelection {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        if self.root_attempt == [0; 16]
            || self.member_attempt == [0; 16]
            || self.root_attempt == self.member_attempt
            || self.prepared_sha256 == [0; 32]
            || self.configuration_sha256 == [0; 32]
            || self.coverage_sha256 == [0; 32]
        {
            return Err(invalid());
        }
        let mut e = Encoder::new(86);
        e.number(1);
        e.0.extend(self.root_attempt);
        e.0.extend(self.member_attempt);
        e.0.extend(self.prepared_sha256);
        e.0.extend(self.configuration_sha256);
        e.0.extend(self.coverage_sha256);
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 86)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let value = Self {
            root_attempt: d.array()?,
            member_attempt: d.array()?,
            prepared_sha256: d.array()?,
            configuration_sha256: d.array()?,
            coverage_sha256: d.array()?,
        };
        d.done()?;
        value.encode()?;
        Ok(value)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mode {
    Build,
    Check,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Source {
    /// Finite selected package namespace, never arbitrary Rust closure.
    pub root: Vec<u8>,
    pub sha256: [u8; 32],
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Plan {
    pub sources: Vec<Source>,
    pub manifest: InputFile,
    pub package: String,
    pub binary: String,
    pub features: Vec<String>,
    pub output_root: Vec<u8>,
    pub cargo_home: Vec<u8>,
    pub sdk_root: Vec<u8>,
    pub compiler: InputFile,
    pub mode: Mode,
    pub timeout_ns: u64,
}
fn name(value: &str) -> bool {
    !value.is_empty()
        && value.len() <= 128
        && value.bytes().all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'-' | b'_'))
}
impl Plan {
    pub fn validate(&self) -> io::Result<()> {
        if self.sources.is_empty()
            || self.sources.len() > MAX_SOURCES
            || !name(&self.package)
            || !name(&self.binary)
            || !path(&self.manifest.path)
            || !self.manifest.path.ends_with(b"/Cargo.toml")
            || self.manifest.sha256 == [0; 32]
            || !path(&self.output_root)
            || !path(&self.cargo_home)
            || !path(&self.sdk_root)
            || self.compiler.path != [self.sdk_root.as_slice(), b"/bin/trustc"].concat()
            || self.compiler.sha256 == [0; 32]
            || self.timeout_ns == 0
            || self.timeout_ns > 86_400_000_000_000
            || self.features.len() > 128
            || self.features.iter().any(|feature| !name(feature))
            || self.features.iter().collect::<BTreeSet<_>>().len() != self.features.len()
        {
            return Err(invalid());
        }
        let mut roots = BTreeSet::new();
        for source in &self.sources {
            if !path(&source.root)
                || source.sha256 == [0; 32]
                || !roots.insert(&source.root)
                || [&self.output_root, &self.cargo_home, &self.sdk_root]
                    .iter()
                    .any(|other| contains(&source.root, other) || contains(other, &source.root))
            {
                return Err(invalid());
            }
        }
        if !self.sources.iter().any(|source| contains(&source.root, &self.manifest.path))
            || contains(&self.output_root, &self.sdk_root)
            || contains(&self.sdk_root, &self.output_root)
            || contains(&self.output_root, &self.cargo_home)
            || contains(&self.cargo_home, &self.output_root)
        {
            return Err(invalid());
        }
        Ok(())
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        let mut e = Encoder::new(81);
        e.number(1);
        e.number(self.sources.len() as u64);
        for source in &self.sources {
            e.bytes(&source.root)?;
            e.0.extend(source.sha256);
        }
        for file in [&self.manifest, &self.compiler] {
            e.bytes(&file.path)?;
            e.0.extend(file.sha256);
        }
        for value in [
            self.package.as_bytes(),
            self.binary.as_bytes(),
            &self.output_root,
            &self.cargo_home,
            &self.sdk_root,
        ] {
            e.bytes(value)?;
        }
        e.number(match self.mode {
            Mode::Build => 0,
            Mode::Check => 1,
        });
        e.number(self.timeout_ns);
        e.number(self.features.len() as u64);
        for feature in &self.features {
            e.bytes(feature.as_bytes())?;
        }
        let bytes = e.finish()?;
        if bytes.len() > MAX_PLAN_BYTES {
            return Err(invalid());
        }
        Ok(bytes)
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        if bytes.len() > MAX_PLAN_BYTES {
            return Err(invalid());
        }
        let mut d = header(bytes, 81)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let mut sources = Vec::new();
        for _ in 0..d.count(MAX_SOURCES)? {
            sources.push(Source { root: d.bytes()?, sha256: d.array()? });
        }
        let manifest = InputFile { path: d.bytes()?, sha256: d.array()? };
        let compiler = InputFile { path: d.bytes()?, sha256: d.array()? };
        let value = Self {
            sources,
            manifest,
            compiler,
            package: d.text()?,
            binary: d.text()?,
            output_root: d.bytes()?,
            cargo_home: d.bytes()?,
            sdk_root: d.bytes()?,
            mode: match d.number()? {
                0 => Mode::Build,
                1 => Mode::Check,
                _ => return Err(invalid()),
            },
            timeout_ns: d.number()?,
            features: {
                let mut features = Vec::new();
                for _ in 0..d.count(128)? {
                    features.push(d.text()?);
                }
                features
            },
        };
        d.done()?;
        value.validate()?;
        Ok(value)
    }
    /// Lossless private early-entry arguments. They negotiate no execution.
    pub fn startup_args(&self) -> io::Result<Vec<Vec<u8>>> {
        const HEX: &[u8; 16] = b"0123456789abcdef";
        let bytes = self.encode()?;
        let mut hex = Vec::with_capacity(bytes.len() * 2);
        for byte in bytes {
            hex.push(HEX[(byte >> 4) as usize]);
            hex.push(HEX[(byte & 15) as usize]);
        }
        Ok(vec![STARTUP_ARGUMENT.as_bytes().to_vec(), hex])
    }
    pub fn from_startup_args(args: &[Vec<u8>]) -> io::Result<Self> {
        let [verb, hex] = args else {
            return Err(invalid());
        };
        if verb != STARTUP_ARGUMENT.as_bytes()
            || hex.len() % 2 != 0
            || hex.len() > MAX_PLAN_BYTES * 2
        {
            return Err(invalid());
        }
        let digit = |byte: u8| match byte {
            b'0'..=b'9' => Ok(byte - b'0'),
            b'a'..=b'f' => Ok(byte - b'a' + 10),
            _ => Err(invalid()),
        };
        let bytes = hex
            .as_chunks::<2>()
            .0
            .iter()
            .map(|pair| Ok((digit(pair[0])? << 4) | digit(pair[1])?))
            .collect::<io::Result<Vec<_>>>()?;
        Self::decode(&bytes)
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct Request {
    pub contained: contained::Request,
    pub plan: Plan,
    pub primary: Descriptor,
    pub broker: Descriptor,
    pub cpu_slot: u32,
    pub outputs: output::Request,
}
impl Request {
    pub fn validate(&self) -> io::Result<()> {
        self.contained.validate()?;
        self.plan.validate()?;
        self.outputs.validate()?;
        let produced = &self.contained.produced;
        if produced.kind != MemberKind::Coordinator
            || produced.member.command.args != self.plan.startup_args()?
            || produced.member.timeout_ns != Some(self.plan.timeout_ns)
            || self.primary.source < 5
            || self.primary.source > i32::MAX as u32
            || self.primary.target != 6
            || self.cpu_slot >= super::MAX_CPU_SET as u32
            || self.broker.target != 8
            || self.broker.source < 5
            || self.broker.source > i32::MAX as u32
            || self.broker.source == self.primary.source
            || self.outputs.key.root_attempt != produced.key.root_attempt
            || self.outputs.key.invocation_sha256 != produced.key.invocation_sha256
            || self.outputs.output_root != self.plan.output_root
        {
            return Err(invalid());
        }
        Ok(())
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        let mut e = Encoder::new(82);
        e.number(1);
        e.frame_bytes(&self.contained.encode()?)?;
        e.frame_bytes(&self.plan.encode()?)?;
        e.number(self.primary.source.into());
        e.number(self.primary.target.into());
        e.number(self.cpu_slot.into());
        e.number(self.broker.source.into());
        e.number(self.broker.target.into());
        e.frame_bytes(&self.outputs.encode()?)?;
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 82)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let value = Self {
            contained: contained::Request::decode(&d.frame_bytes()?)?,
            plan: Plan::decode(&d.frame_bytes()?)?,
            primary: Descriptor { source: d.narrow()?, target: d.narrow()? },
            cpu_slot: d.narrow()?,
            broker: Descriptor { source: d.narrow()?, target: d.narrow()? },
            outputs: output::Request::decode(&d.frame_bytes()?)?,
        };
        d.done()?;
        value.validate()?;
        Ok(value)
    }
    pub fn hello(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        let mut hello = self.contained.hello()?;
        // Both purposes are static protocol spellings, not user text.
        let text =
            String::from_utf8(hello).map_err(|_| invalid())?.replace(contained::PURPOSE, PURPOSE);
        hello = text.into_bytes();
        Ok(hello)
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct OriginalRequest {
    pub query: ContextQuery,
    pub member_attempt: [u8; 16],
}
impl OriginalRequest {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.query.validate()?;
        if self.member_attempt == [0; 16] || self.member_attempt == self.query.binding.root_attempt
        {
            return Err(invalid());
        }
        let mut e = Encoder::new(83);
        e.number(1);
        e.frame_bytes(&self.query.encode()?)?;
        e.0.extend(self.member_attempt);
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 83)?;
        if d.number()? != 1 {
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
            self.query.binding.root_attempt.iter().map(|b| format!("{b:02x}")).collect();
        Ok(format!("{{\"version\":3,\"role\":\"{ORIGINAL_PURPOSE}\",\"session\":\"{}\",\"attempt\":\"{attempt}\"}}", self.query.binding.session).into_bytes())
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct OriginalReply {
    pub context: ContextReply,
    pub plan: Plan,
    pub primary: PrimaryCpu,
    pub broker_fd: u32,
    pub parent_program: crate::MetadataFile,
    pub prepared_sha256: [u8; 32],
    pub configuration_sha256: [u8; 32],
    pub coverage_sha256: [u8; 32],
    pub outputs: output::Request,
    /// SAME original Root deadline, sampled immediately before reply.
    pub remaining_root_ns: u64,
}
impl OriginalReply {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.plan.validate()?;
        self.outputs.validate()?;
        self.parent_program.validate(&self.plan.sdk_root)?;
        if !matches!(self.context.context.subject, crate::Subject::RegisteredMember { .. })
            || !matches!(self.context.context.cpu, crate::Cpu::CooperativeShared { .. })
            || self
                .context
                .context
                .sdk
                .as_ref()
                .is_none_or(|sdk| sdk.execution != self.plan.sdk_root)
            || self.primary.inherited_fd != 6
            || self.primary.slot >= super::MAX_CPU_SET as u32
            || self.primary.backing.inode == 0
            || self.outputs.output_root != self.plan.output_root
            || self.outputs.key.root_attempt != self.context.context.root_attempt
            || self.remaining_root_ns == 0
            || self.broker_fd != 8
            || self.parent_program.path != [self.plan.sdk_root.as_slice(), b"/bin/targo"].concat()
            || self.prepared_sha256 == [0; 32]
            || self.configuration_sha256 == [0; 32]
            || self.coverage_sha256 == [0; 32]
        {
            return Err(invalid());
        }
        let mut e = Encoder::new(84);
        e.number(1);
        e.frame_bytes(&self.context.encode()?)?;
        e.frame_bytes(&self.plan.encode()?)?;
        e.number(self.primary.inherited_fd.into());
        e.number(self.primary.slot.into());
        e.number(self.primary.backing.device);
        e.number(self.primary.backing.inode);
        e.frame_bytes(&self.outputs.encode()?)?;
        e.number(self.remaining_root_ns);
        e.number(self.broker_fd.into());
        self.parent_program.encode(&mut e)?;
        e.0.extend(self.prepared_sha256);
        e.0.extend(self.configuration_sha256);
        e.0.extend(self.coverage_sha256);
        e.finish()
    }
    pub fn decode(bytes: &[u8], request: &OriginalRequest) -> io::Result<Self> {
        request.encode()?;
        let mut d = header(bytes, 84)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let value = Self {
            context: ContextReply::decode(&d.frame_bytes()?, &request.query)?,
            plan: Plan::decode(&d.frame_bytes()?)?,
            primary: PrimaryCpu {
                inherited_fd: d.narrow()?,
                slot: d.narrow()?,
                backing: crate::FileIdentity { device: d.number()?, inode: d.number()? },
            },
            outputs: output::Request::decode(&d.frame_bytes()?)?,
            remaining_root_ns: d.number()?,
            broker_fd: d.narrow()?,
            parent_program: crate::MetadataFile::decode(&mut d)?,
            prepared_sha256: d.array()?,
            configuration_sha256: d.array()?,
            coverage_sha256: d.array()?,
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
