// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! SAME original fixed Root compilation binding DATA. Decoding never issues a
//! Root, source/output, seed, queue credit, member, artifact or retirement owner.
//! Only the original native Host can advance its completed input subgraph and
//! issue members through that SAME Fixed cohort; public query guards stay closed.
use std::collections::BTreeSet;
use std::io;

use super::preparation::work::RetainedCompilerQuery;
use super::preparation::{self};
use super::{GnuIdentity, OutputAttachment, SourceAttachment, absolute};
use crate::wire::{Decoder, Encoder, header, invalid};
use crate::workload::host::coordinator::{command_read, command_write};
use crate::{CommandSpec, MetadataFile, Status, StatusFrame};

#[cfg(all(feature = "channel", any(target_os = "macos", target_os = "linux")))]
pub mod transport;

pub mod compiler;
pub mod finish;

pub const ADVANCE_PURPOSE: &str = "native-bootstrap-compilation-advance-v1";
pub const MEMBER_PURPOSE: &str = "native-bootstrap-compilation-member-v1";
pub const RETIRE_PURPOSE: &str = "native-bootstrap-compilation-retire-v1";
pub const RIGHTS_MARKER: u8 = 0x75;
pub const DESCRIPTION_COUNT: usize = 5;
pub const MAX_MEMBERS: u64 = 1_048_576;
pub const MAX_MEMBER_NS: u64 = 86_400_000_000_000;

#[derive(Clone, PartialEq, Eq)]
pub struct AdvanceRequest {
    pub attempt: preparation::Request,
    /// Complete original arguments, without normalization or a recipe subset.
    pub original_arguments: Vec<Vec<u8>>,
}
impl AdvanceRequest {
    pub fn validate(&self) -> io::Result<()> {
        self.attempt.validate()?;
        if self.original_arguments.is_empty() || self.original_arguments.len() > 1024 {
            return Err(invalid());
        }
        let mut total = 0usize;
        for word in &self.original_arguments {
            total = total.checked_add(word.len()).ok_or_else(invalid)?;
            if word.len() > crate::MAX_FIELD || word.contains(&0) || total > crate::MAX_PAYLOAD {
                return Err(invalid());
            }
        }
        Ok(())
    }
    pub fn hello(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        self.attempt.key.graph.hello(ADVANCE_PURPOSE)
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        let mut e = Encoder::new(160);
        e.number(1);
        e.frame_bytes(&self.attempt.encode()?)?;
        e.number(self.original_arguments.len() as u64);
        for word in &self.original_arguments {
            e.bytes(word)?;
        }
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 160)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let attempt = preparation::Request::decode(&d.frame_bytes()?)?;
        let mut original_arguments = Vec::new();
        for _ in 0..d.count(1024)? {
            original_arguments.push(d.bytes()?);
        }
        d.done()?;
        let value = Self { attempt, original_arguments };
        value.validate()?;
        Ok(value)
    }
}

/// The nonce is issued by the native owner, but these decoded bytes are only
/// equality DATA. They cannot recreate the actual accepted connection/owners.
#[derive(Clone, PartialEq, Eq)]
pub struct Key {
    pub attempt: preparation::Request,
    pub compilation: [u8; 16],
}
impl Key {
    pub fn validate(&self) -> io::Result<()> {
        self.attempt.validate()?;
        let operation = &self.attempt.key;
        if [
            [0; 16],
            operation.operation,
            operation.graph.graph,
            operation.graph.query.call_attempt,
            operation.graph.query.binding.root_attempt,
        ]
        .contains(&self.compilation)
        {
            return Err(invalid());
        }
        Ok(())
    }
    fn write(&self, e: &mut Encoder) -> io::Result<()> {
        self.validate()?;
        e.frame_bytes(&self.attempt.encode()?)?;
        e.0.extend(self.compilation);
        Ok(())
    }
    fn read(d: &mut Decoder<'_>) -> io::Result<Self> {
        let value = Self {
            attempt: preparation::Request::decode(&d.frame_bytes()?)?,
            compilation: d.array()?,
        };
        value.validate()?;
        Ok(value)
    }
}

/// Descriptions of the SAME native-held validated seed and actual retained
/// query outputs. No pathname or this value constructs PrivateBootstrapSeed.
#[derive(Clone, PartialEq, Eq)]
pub struct SeedInputs {
    pub root: Vec<u8>,
    pub compiler: MetadataFile,
    pub targo: MetadataFile,
    pub formatter: MetadataFile,
    pub compiler_queries: Vec<RetainedCompilerQuery>,
}
impl SeedInputs {
    fn validate(&self, key: &Key, gnu: &GnuIdentity) -> io::Result<()> {
        if !absolute(&self.root) || self.compiler_queries.len() != 2 {
            return Err(invalid());
        }
        for (program, name) in [
            (&self.compiler, b"/bin/trustc".as_slice()),
            (&self.targo, b"/bin/targo".as_slice()),
            (&self.formatter, b"/bin/trustfmt".as_slice()),
        ] {
            program.validate(&self.root)?;
            if program.path != [self.root.as_slice(), name].concat() || program.sha256 == [0; 32] {
                return Err(invalid());
            }
        }
        let mut forms = [false; 2];
        let mut operations = BTreeSet::new();
        let mut previous_sequence = None;
        for issued in &self.compiler_queries {
            issued.write(&mut Encoder::new(0))?;
            let index = if issued.request.arguments == [b"-vV".to_vec()] {
                0
            } else if issued.request.arguments == [b"--print=sysroot".to_vec()] {
                1
            } else {
                return Err(invalid());
            };
            if std::mem::replace(&mut forms[index], true)
                || issued.request.key.graph != key.attempt.key.graph
                || issued.request.key.sequence <= key.attempt.key.sequence
                || previous_sequence.is_some_and(|last| last >= issued.request.key.sequence)
                || !operations.insert(issued.request.key.operation)
                || [key.compilation, key.attempt.key.operation]
                    .contains(&issued.request.key.operation)
                || issued.request.program != self.compiler
                || issued.request.sdk_root != self.root
                || &issued.request.gnu != gnu
                || issued.stdout.is_empty()
            {
                return Err(invalid());
            }
            previous_sequence = Some(issued.request.key.sequence);
        }
        if self.compiler_queries[0].request.cwd != self.compiler_queries[1].request.cwd
            || self.compiler_queries[0].request.environment
                != self.compiler_queries[1].request.environment
        {
            return Err(invalid());
        }
        Ok(())
    }
    fn write(&self, e: &mut Encoder) -> io::Result<()> {
        e.bytes(&self.root)?;
        for file in [&self.compiler, &self.targo, &self.formatter] {
            file.encode(e)?;
        }
        e.number(self.compiler_queries.len() as u64);
        for query in &self.compiler_queries {
            query.write(e)?;
        }
        Ok(())
    }
    fn read(d: &mut Decoder<'_>) -> io::Result<Self> {
        let root = d.bytes()?;
        let compiler = MetadataFile::decode(d)?;
        let targo = MetadataFile::decode(d)?;
        let formatter = MetadataFile::decode(d)?;
        let mut compiler_queries = Vec::new();
        for _ in 0..d.count(2)? {
            compiler_queries.push(RetainedCompilerQuery::read(d)?);
        }
        Ok(Self { root, compiler, targo, formatter, compiler_queries })
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct Advanced {
    pub key: Key,
    pub source: SourceAttachment,
    pub output: OutputAttachment,
    pub gnu: GnuIdentity,
    pub seed: SeedInputs,
}
impl Advanced {
    pub fn validate(&self) -> io::Result<()> {
        self.key.validate()?;
        self.source.validate()?;
        self.output.encode()?;
        if self.source.key != self.key.attempt.key.graph || self.output.key != self.source.key {
            return Err(invalid());
        }
        self.gnu.write(&mut Encoder::new(0))?;
        self.seed.validate(&self.key, &self.gnu)
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        let mut e = Encoder::new(161);
        e.number(1);
        self.key.write(&mut e)?;
        e.frame_bytes(&self.source.encode()?)?;
        e.frame_bytes(&self.output.encode()?)?;
        self.gnu.write(&mut e)?;
        self.seed.write(&mut e)?;
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 161)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let value = Self {
            key: Key::read(&mut d)?,
            source: SourceAttachment::decode(&d.frame_bytes()?)?,
            output: OutputAttachment::decode(&d.frame_bytes()?)?,
            gnu: GnuIdentity::read(&mut d)?,
            seed: SeedInputs::read(&mut d)?,
        };
        d.done()?;
        value.validate()?;
        Ok(value)
    }
}

/// IssuedProgram refers only to a native retained successful producer/runtime.
/// A syntactically valid reference MUST refuse without that actual owner.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProgramRole {
    SeedCompiler,
    SeedTargo,
    SeedFormatter,
    IssuedProgram { producer: [u8; 16], artifact: u32 },
}
impl ProgramRole {
    fn write(self, e: &mut Encoder) -> io::Result<()> {
        e.number(match self {
            Self::SeedCompiler => 0,
            Self::SeedTargo => 1,
            Self::SeedFormatter => 2,
            Self::IssuedProgram { .. } => 3,
        });
        if let Self::IssuedProgram { producer, artifact } = self {
            if producer == [0; 16] {
                return Err(invalid());
            }
            e.0.extend(producer);
            e.number(artifact.into());
        }
        Ok(())
    }
    fn read(d: &mut Decoder<'_>) -> io::Result<Self> {
        Ok(match d.number()? {
            0 => Self::SeedCompiler,
            1 => Self::SeedTargo,
            2 => Self::SeedFormatter,
            3 => Self::IssuedProgram { producer: d.array()?, artifact: d.narrow()? },
            _ => return Err(invalid()),
        })
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct MemberRequest {
    pub key: Key,
    pub sequence: u64,
    pub member: [u8; 16],
    pub program: ProgramRole,
    pub command: CommandSpec,
    pub gnu: GnuIdentity,
    /// Subbudget DATA under the existing Fixed cohort, never a CPU grant.
    pub fixed_units: u32,
    pub timeout_ns: u64,
}
impl MemberRequest {
    pub fn validate(&self) -> io::Result<()> {
        self.key.validate()?;
        let operation = &self.key.attempt.key;
        if !(1..=MAX_MEMBERS).contains(&self.sequence)
            || [
                [0; 16],
                self.key.compilation,
                operation.operation,
                operation.graph.graph,
                operation.graph.query.call_attempt,
                operation.graph.query.binding.root_attempt,
            ]
            .contains(&self.member)
            || self.fixed_units == 0
            || self.fixed_units as usize > crate::workload::host::MAX_CPU_SET
            || !(1..=MAX_MEMBER_NS).contains(&self.timeout_ns)
            || matches!(self.program, ProgramRole::IssuedProgram { producer, .. } if producer == self.member)
        {
            return Err(invalid());
        }
        self.program.write(&mut Encoder::new(0))?;
        self.gnu.write(&mut Encoder::new(0))?;
        command_write(&self.command, &mut Encoder::new(0))
    }
    pub fn hello(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        self.key.attempt.key.graph.hello(MEMBER_PURPOSE)
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        let mut e = Encoder::new(162);
        e.number(1);
        self.key.write(&mut e)?;
        e.number(self.sequence);
        e.0.extend(self.member);
        self.program.write(&mut e)?;
        command_write(&self.command, &mut e)?;
        self.gnu.write(&mut e)?;
        e.number(self.fixed_units.into());
        e.number(self.timeout_ns);
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 162)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let value = Self {
            key: Key::read(&mut d)?,
            sequence: d.number()?,
            member: d.array()?,
            program: ProgramRole::read(&mut d)?,
            command: command_read(&mut d)?,
            gnu: GnuIdentity::read(&mut d)?,
            fixed_units: d.narrow()?,
            timeout_ns: d.number()?,
        };
        d.done()?;
        value.validate()?;
        Ok(value)
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct RetireRequest {
    pub key: Key,
    pub sequence: u64,
    pub member: [u8; 16],
}
impl RetireRequest {
    pub fn validate(&self) -> io::Result<()> {
        self.key.validate()?;
        if !(1..=MAX_MEMBERS).contains(&self.sequence)
            || [
                [0; 16],
                self.key.compilation,
                self.key.attempt.key.operation,
                self.key.attempt.key.graph.graph,
                self.key.attempt.key.graph.query.call_attempt,
                self.key.attempt.key.graph.query.binding.root_attempt,
            ]
            .contains(&self.member)
        {
            return Err(invalid());
        }
        Ok(())
    }
    pub fn hello(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        self.key.attempt.key.graph.hello(RETIRE_PURPOSE)
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        let mut e = Encoder::new(163);
        e.number(1);
        self.key.write(&mut e)?;
        e.number(self.sequence);
        e.0.extend(self.member);
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 163)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let value = Self { key: Key::read(&mut d)?, sequence: d.number()?, member: d.array()? };
        d.done()?;
        value.validate()?;
        Ok(value)
    }
}

/// Native retirement observation DATA. Only a pinned owning exchange may
/// accept it as the actual native issuer; decoding/status/EOF cannot do so.
#[derive(Clone, PartialEq, Eq)]
pub struct Retired {
    pub request: RetireRequest,
    pub status: Status,
}
impl Retired {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.request.validate()?;
        if !matches!(self.status, Status::Finished { .. } | Status::Refused { .. }) {
            return Err(invalid());
        }
        let status = StatusFrame {
            root_attempt: self.request.key.attempt.key.graph.query.binding.root_attempt,
            member_attempt: self.request.member,
            status: self.status.clone(),
        };
        let mut e = Encoder::new(164);
        e.number(1);
        e.frame_bytes(&self.request.encode()?)?;
        e.frame_bytes(&status.encode()?)?;
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 164)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let request = RetireRequest::decode(&d.frame_bytes()?)?;
        let status = StatusFrame::decode(
            &d.frame_bytes()?,
            request.key.attempt.key.graph.query.binding.root_attempt,
            request.member,
        )?
        .status;
        d.done()?;
        let value = Self { request, status };
        value.encode()?;
        Ok(value)
    }
}

#[cfg(test)]
pub(crate) mod tests;
