// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

use std::io;

use crate::*;

const MAGIC: &[u8; 8] = b"TRPCV003";
pub(crate) fn invalid() -> io::Error {
    io::Error::new(
        io::ErrorKind::InvalidData,
        "invalid private resource controller frame",
    )
}
pub(crate) struct Encoder(pub(crate) Vec<u8>, usize);
impl Encoder {
    pub(crate) fn new(kind: u64) -> Self {
        let mut e = Self(MAGIC.to_vec(), MAX_PAYLOAD);
        e.number(kind);
        e
    }
    pub(crate) fn metadata_report() -> Self {
        let mut e = Self::new(16);
        e.1 = crate::METADATA_REPORT_MAX_BYTES;
        e
    }
    pub(crate) fn resolver_report() -> Self {
        let mut e = Self::new(34);
        e.1 = crate::resolver::RESOLVER_REPORT_MAX_BYTES;
        e
    }
    pub(crate) fn resolver_metadata(&mut self, bytes: &[u8]) -> io::Result<()> {
        self.bounded_bytes(bytes, crate::resolver::RESOLVER_MAX_METADATA)
    }
    pub(crate) fn number(&mut self, n: u64) {
        self.0.extend_from_slice(&n.to_be_bytes());
    }
    pub(crate) fn bytes(&mut self, b: &[u8]) -> io::Result<()> {
        self.bounded_bytes(b, MAX_FIELD)
    }
    pub(crate) fn frame_bytes(&mut self, b: &[u8]) -> io::Result<()> {
        self.bounded_bytes(b, MAX_PAYLOAD)
    }
    fn bounded_bytes(&mut self, b: &[u8], bound: usize) -> io::Result<()> {
        if b.len() > bound {
            return Err(invalid());
        }
        self.number(b.len() as u64);
        self.0.extend_from_slice(b);
        if self.0.len() > self.1 {
            return Err(invalid());
        }
        Ok(())
    }
    fn descriptor(&mut self, d: Descriptor) {
        self.number(d.source.into());
        self.number(d.target.into());
    }
    pub(crate) fn finish(self) -> io::Result<Vec<u8>> {
        if self.0.len() > self.1 {
            Err(invalid())
        } else {
            Ok(self.0)
        }
    }
}
pub(crate) struct Decoder<'a>(&'a [u8]);
impl<'a> Decoder<'a> {
    pub(crate) fn take(&mut self, n: usize) -> io::Result<&'a [u8]> {
        let value = self.0.get(..n).ok_or_else(invalid)?;
        self.0 = &self.0[n..];
        Ok(value)
    }
    pub(crate) fn number(&mut self) -> io::Result<u64> {
        Ok(u64::from_be_bytes(
            self.take(8)?.try_into().map_err(|_| invalid())?,
        ))
    }
    pub(crate) fn narrow(&mut self) -> io::Result<u32> {
        self.number()?.try_into().map_err(|_| invalid())
    }
    pub(crate) fn count(&mut self, bound: usize) -> io::Result<usize> {
        let n: usize = self.number()?.try_into().map_err(|_| invalid())?;
        if n > bound {
            return Err(invalid());
        }
        Ok(n)
    }
    pub(crate) fn bytes(&mut self) -> io::Result<Vec<u8>> {
        let n = self.count(MAX_FIELD)?;
        Ok(self.take(n)?.to_vec())
    }
    pub(crate) fn frame_bytes(&mut self) -> io::Result<Vec<u8>> {
        let n = self.count(MAX_PAYLOAD)?;
        Ok(self.take(n)?.to_vec())
    }
    pub(crate) fn resolver_metadata(&mut self) -> io::Result<Vec<u8>> {
        let n = self.count(crate::resolver::RESOLVER_MAX_METADATA)?;
        Ok(self.take(n)?.to_vec())
    }
    pub(crate) fn remaining(&self) -> &'a [u8] {
        self.0
    }
    pub(crate) fn text(&mut self) -> io::Result<String> {
        String::from_utf8(self.bytes()?).map_err(|_| invalid())
    }
    pub(crate) fn array<const N: usize>(&mut self) -> io::Result<[u8; N]> {
        self.take(N)?.try_into().map_err(|_| invalid())
    }
    fn descriptor(&mut self) -> io::Result<Descriptor> {
        Ok(Descriptor {
            source: self.narrow()?,
            target: self.narrow()?,
        })
    }
    pub(crate) fn done(self) -> io::Result<()> {
        if self.0.is_empty() {
            Ok(())
        } else {
            Err(invalid())
        }
    }
}
pub(crate) fn header(bytes: &[u8], kind: u64) -> io::Result<Decoder<'_>> {
    bounded_header(bytes, kind, MAX_PAYLOAD)
}
pub(crate) fn metadata_report_header(bytes: &[u8]) -> io::Result<Decoder<'_>> {
    bounded_header(bytes, 16, crate::METADATA_REPORT_MAX_BYTES)
}
fn bounded_header(bytes: &[u8], kind: u64, bound: usize) -> io::Result<Decoder<'_>> {
    if bytes.len() > bound {
        return Err(invalid());
    }
    let mut d = Decoder(bytes);
    if d.take(8)? != MAGIC || d.number()? != kind {
        return Err(invalid());
    }
    Ok(d)
}
impl Request {
    /// Encode for one explicit private control exchange. Never log the result.
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        self.encode_validated()
    }
    pub(crate) fn encode_paired_query(&self) -> io::Result<Vec<u8>> {
        self.validate_paired_query()?;
        self.encode_validated()
    }
    fn encode_validated(&self) -> io::Result<Vec<u8>> {
        let mut e = Encoder::new(1);
        e.bytes(self.binding.session.as_bytes())?;
        e.0.extend(self.binding.root_attempt);
        e.0.extend(self.binding.capability);
        e.0.extend(self.member_attempt);
        e.number(match self.role {
            Role::MetadataVersion => 0,
            Role::Compile => 1,
            Role::MetadataProbe => 2,
            Role::SealedMetadata => METADATA_REQUEST_ROLE,
            Role::MachOLinker(_) => MACHO_LINKER_REQUEST_ROLE,
            Role::ResolverQuery => crate::resolver::RESOLVER_REQUEST_ROLE,
            Role::WorkloadQuery => crate::workload::host::QUERY_ROLE,
            Role::WorkloadProduced => crate::workload::host::produced::ROLE,
            Role::CoordinatorCompiler(_) => crate::workload::host::coordinator::COMPILER_ROLE,
        });
        if let Role::CoordinatorCompiler(coordinator) = self.role {
            e.0.extend(coordinator);
        }
        if let Role::MachOLinker(loan) = self.role {
            e.0.extend(loan.parent_attempt);
            e.0.extend(loan.nonce);
            e.number(u64::from(loan.cpu_slot));
        }
        e.number(self.timeout_ns.unwrap_or(0));
        e.bytes(&self.command.program)?;
        e.number(u64::from(self.command.arg0.is_some()));
        if let Some(arg0) = &self.command.arg0 {
            e.bytes(arg0)?;
        }
        e.bytes(&self.command.cwd)?;
        e.number(self.command.args.len() as u64);
        for arg in &self.command.args {
            e.bytes(arg)?;
        }
        e.number(self.command.environment.len() as u64);
        for (key, value) in &self.command.environment {
            e.bytes(key)?;
            e.bytes(value)?;
        }
        e.number(u64::from(self.delegations.cpu.is_some()));
        if let Some(cpu) = self.delegations.cpu {
            e.descriptor(cpu);
        }
        match &self.delegations.gnu {
            GnuTransport::None => e.number(0),
            GnuTransport::NumericPipe { read, write } => {
                e.number(1);
                e.descriptor(*read);
                e.descriptor(*write);
            }
            GnuTransport::NamedFifo {
                locator,
                device,
                inode,
                read,
                write,
            } => {
                e.number(2);
                e.bytes(locator)?;
                e.number(*device);
                e.number(*inode);
                e.descriptor(*read);
                e.descriptor(*write);
            }
        }
        e.number(self.delegations.fences.len() as u64);
        for fd in &self.delegations.fences {
            e.descriptor(*fd);
        }
        e.finish()
    }
    /// Decode bounded untrusted bytes, rejecting extra fields and invalid shapes.
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        Self::decode_profile(bytes, false)
    }
    pub(crate) fn decode_paired_query(bytes: &[u8]) -> io::Result<Self> {
        Self::decode_profile(bytes, true)
    }
    fn decode_profile(bytes: &[u8], paired_query: bool) -> io::Result<Self> {
        let mut d = header(bytes, 1)?;
        let binding = JobBinding {
            session: d.text()?,
            root_attempt: d.array()?,
            capability: d.array()?,
        };
        let member_attempt = d.array()?;
        let role = match d.number()? {
            0 => Role::MetadataVersion,
            1 => Role::Compile,
            2 => Role::MetadataProbe,
            METADATA_REQUEST_ROLE => Role::SealedMetadata,
            MACHO_LINKER_REQUEST_ROLE => Role::MachOLinker(Loan {
                parent_attempt: d.array()?,
                nonce: d.array()?,
                cpu_slot: u32::try_from(d.number()?).map_err(|_| invalid())?,
            }),
            crate::resolver::RESOLVER_REQUEST_ROLE => Role::ResolverQuery,
            crate::workload::host::QUERY_ROLE => Role::WorkloadQuery,
            crate::workload::host::produced::ROLE => Role::WorkloadProduced,
            crate::workload::host::coordinator::COMPILER_ROLE => {
                Role::CoordinatorCompiler(d.array()?)
            }
            _ => return Err(invalid()),
        };
        let timeout = d.number()?;
        let program = d.bytes()?;
        let arg0 = match d.number()? {
            0 => None,
            1 => Some(d.bytes()?),
            _ => return Err(invalid()),
        };
        let cwd = d.bytes()?;
        let mut args = Vec::new();
        for _ in 0..d.count(MAX_ITEMS)? {
            args.push(d.bytes()?);
        }
        let mut environment = Vec::new();
        for _ in 0..d.count(MAX_ITEMS)? {
            environment.push((d.bytes()?, d.bytes()?));
        }
        let cpu = match d.number()? {
            0 => None,
            1 => Some(d.descriptor()?),
            _ => return Err(invalid()),
        };
        let gnu = match d.number()? {
            0 => GnuTransport::None,
            1 => GnuTransport::NumericPipe {
                read: d.descriptor()?,
                write: d.descriptor()?,
            },
            2 => GnuTransport::NamedFifo {
                locator: d.bytes()?,
                device: d.number()?,
                inode: d.number()?,
                read: d.descriptor()?,
                write: d.descriptor()?,
            },
            _ => return Err(invalid()),
        };
        let mut fences = Vec::new();
        for _ in 0..d.count(MAX_FENCES)? {
            fences.push(d.descriptor()?);
        }
        d.done()?;
        let request = Self {
            binding,
            member_attempt,
            role,
            command: CommandSpec {
                program,
                arg0,
                args,
                environment,
                cwd,
            },
            delegations: Delegations { cpu, gnu, fences },
            timeout_ns: (timeout != 0).then_some(timeout),
        };
        if paired_query {
            request.validate_paired_query()?;
        } else {
            request.validate()?;
        }
        Ok(request)
    }
}

fn started_encode(e: &mut Encoder, s: Started) -> io::Result<()> {
    if s.identity.pid <= 1 || s.identity.birth == 0 || s.monotonic_ns == 0 || s.unix_ns == 0 {
        return Err(invalid());
    }
    e.number(s.identity.pid.into());
    e.number(s.identity.birth);
    e.number(match s.identity.birth_kind {
        BirthKind::MacosWallMicroseconds => 0,
        BirthKind::LinuxStartTicks => 1,
    });
    e.number(s.monotonic_ns);
    e.number(s.unix_ns);
    Ok(())
}
fn started_decode(d: &mut Decoder<'_>) -> io::Result<Started> {
    let pid = d.narrow()?;
    let birth = d.number()?;
    let birth_kind = match d.number()? {
        0 => BirthKind::MacosWallMicroseconds,
        1 => BirthKind::LinuxStartTicks,
        _ => return Err(invalid()),
    };
    let s = Started {
        identity: Identity {
            pid,
            birth,
            birth_kind,
        },
        monotonic_ns: d.number()?,
        unix_ns: d.number()?,
    };
    started_encode(&mut Encoder::new(0), s)?;
    Ok(s)
}
impl StatusFrame {
    /// Encode lifecycle facts for the exact original/member attempt.
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        if self.root_attempt == [0; 16]
            || self.member_attempt == [0; 16]
            || self.root_attempt == self.member_attempt
        {
            return Err(invalid());
        }
        let mut e = Encoder::new(2);
        e.0.extend(self.root_attempt);
        e.0.extend(self.member_attempt);
        match &self.status {
            Status::Attached => e.number(0),
            Status::Started(s) => {
                e.number(1);
                started_encode(&mut e, *s)?;
            }
            Status::Finished {
                outcome,
                cause,
                runtime_ns,
            } => {
                e.number(2);
                match outcome {
                    Outcome::Exit(code) => {
                        e.number(0);
                        e.number(*code as u32 as u64);
                    }
                    Outcome::Signal(signal) => {
                        if *signal <= 0 {
                            return Err(invalid());
                        }
                        e.number(1);
                        e.number(*signal as u64);
                    }
                }
                e.number(match cause {
                    CompletionCause::Exited => 0,
                    CompletionCause::Timeout => 1,
                    CompletionCause::Cancelled => 2,
                    CompletionCause::ResourceLimit => 3,
                    CompletionCause::HostFault => 4,
                });
                e.number(*runtime_ns);
            }
            Status::Refused { reason } => {
                e.number(3);
                if reason.is_empty() {
                    return Err(invalid());
                }
                e.bytes(reason.as_bytes())?;
            }
            Status::Unknown { reason, started } => {
                e.number(4);
                if reason.is_empty() {
                    return Err(invalid());
                }
                e.bytes(reason.as_bytes())?;
                e.number(u64::from(started.is_some()));
                if let Some(s) = started {
                    started_encode(&mut e, *s)?;
                }
            }
        }
        e.finish()
    }
    /// Decode only facts matching the caller's existing one-shot request.
    pub fn decode(
        bytes: &[u8],
        root_attempt: [u8; 16],
        member_attempt: [u8; 16],
    ) -> io::Result<Self> {
        let mut d = header(bytes, 2)?;
        if d.array::<16>()? != root_attempt || d.array::<16>()? != member_attempt {
            return Err(invalid());
        }
        let status = match d.number()? {
            0 => Status::Attached,
            1 => Status::Started(started_decode(&mut d)?),
            2 => {
                let outcome = match d.number()? {
                    0 => Outcome::Exit(d.narrow()? as i32),
                    1 => Outcome::Signal(d.narrow()?.try_into().map_err(|_| invalid())?),
                    _ => return Err(invalid()),
                };
                let cause = match d.number()? {
                    0 => CompletionCause::Exited,
                    1 => CompletionCause::Timeout,
                    2 => CompletionCause::Cancelled,
                    3 => CompletionCause::ResourceLimit,
                    4 => CompletionCause::HostFault,
                    _ => return Err(invalid()),
                };
                Status::Finished {
                    outcome,
                    cause,
                    runtime_ns: d.number()?,
                }
            }
            3 => Status::Refused { reason: d.text()? },
            4 => {
                let reason = d.text()?;
                let started = match d.number()? {
                    0 => None,
                    1 => Some(started_decode(&mut d)?),
                    _ => return Err(invalid()),
                };
                Status::Unknown { reason, started }
            }
            _ => return Err(invalid()),
        };
        d.done()?;
        let frame = Self {
            root_attempt,
            member_attempt,
            status,
        };
        frame.encode()?;
        Ok(frame)
    }
}

/// Cancellation selects only the existing member attempt, never a PID or grant.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Cancel {
    pub root_attempt: [u8; 16],
    pub member_attempt: [u8; 16],
}
impl Cancel {
    pub fn encode(self) -> io::Result<Vec<u8>> {
        if self.root_attempt == [0; 16]
            || self.member_attempt == [0; 16]
            || self.root_attempt == self.member_attempt
        {
            return Err(invalid());
        }
        let mut e = Encoder::new(3);
        e.0.extend(self.root_attempt);
        e.0.extend(self.member_attempt);
        e.finish()
    }
    pub fn decode(bytes: &[u8], expected: Self) -> io::Result<Self> {
        let mut d = header(bytes, 3)?;
        let value = Self {
            root_attempt: d.array()?,
            member_attempt: d.array()?,
        };
        d.done()?;
        if value != expected {
            return Err(invalid());
        }
        value.encode()?;
        Ok(value)
    }
}

/// One host challenge for one pending producer call. The receiver must match
/// its actual helper child and existing request before answering; bytes alone
/// establish neither native identity nor resource entitlement.
#[derive(Clone, PartialEq, Eq)]
pub struct ProducerChallenge {
    pub root_attempt: [u8; 16],
    pub member_attempt: [u8; 16],
    pub helper: Identity,
    pub nonce: [u8; 32],
}
impl ProducerChallenge {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.encode_kind(4)
    }
    pub fn answer(&self) -> io::Result<Vec<u8>> {
        self.encode_kind(5)
    }
    fn encode_kind(&self, kind: u64) -> io::Result<Vec<u8>> {
        if self.root_attempt == [0; 16]
            || self.member_attempt == [0; 16]
            || self.root_attempt == self.member_attempt
            || self.helper.pid <= 1
            || self.helper.birth == 0
            || self.nonce == [0; 32]
        {
            return Err(invalid());
        }
        let mut e = Encoder::new(kind);
        e.0.extend(self.root_attempt);
        e.0.extend(self.member_attempt);
        e.number(self.helper.pid.into());
        e.number(self.helper.birth);
        e.number(match self.helper.birth_kind {
            BirthKind::MacosWallMicroseconds => 0,
            BirthKind::LinuxStartTicks => 1,
        });
        e.0.extend(self.nonce);
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        Self::decode_kind(bytes, 4)
    }
    pub fn verify_answer(&self, bytes: &[u8]) -> io::Result<()> {
        if Self::decode_kind(bytes, 5)? != *self {
            return Err(invalid());
        }
        Ok(())
    }
    fn decode_kind(bytes: &[u8], kind: u64) -> io::Result<Self> {
        let mut d = header(bytes, kind)?;
        let root_attempt = d.array()?;
        let member_attempt = d.array()?;
        let pid = d.narrow()?;
        let birth = d.number()?;
        let birth_kind = match d.number()? {
            0 => BirthKind::MacosWallMicroseconds,
            1 => BirthKind::LinuxStartTicks,
            _ => return Err(invalid()),
        };
        let value = Self {
            root_attempt,
            member_attempt,
            helper: Identity {
                pid,
                birth,
                birth_kind,
            },
            nonce: d.array()?,
        };
        d.done()?;
        value.encode_kind(kind)?;
        Ok(value)
    }
}

/// A separately bounded root report; never a socket/native command frame.
pub(crate) fn resolver_report_header(bytes: &[u8]) -> io::Result<Decoder<'_>> {
    if bytes.len() > crate::resolver::RESOLVER_REPORT_MAX_BYTES
        || bytes.len() < 16
        || &bytes[..8] != MAGIC
        || u64::from_be_bytes(bytes[8..16].try_into().map_err(|_| invalid())?) != 34
    {
        return Err(invalid());
    }
    Ok(Decoder(&bytes[16..]))
}
