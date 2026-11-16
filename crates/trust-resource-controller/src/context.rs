// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

use std::io;

use crate::wire::{Decoder, Encoder, header, invalid};
use crate::*;

/// One private observation call before choosing initial-vs-borrowed CPU. This
/// carries no command and creates no root, subgroup, memory or CPU grant.
#[derive(Clone, PartialEq, Eq)]
pub struct ContextQuery {
    pub binding: JobBinding,
    pub call_attempt: [u8; 16],
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FileIdentity {
    pub device: u64,
    pub inode: u64,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Subject {
    Root { identity: Identity },
    RegisteredMember { identity: Identity, attempt: [u8; 16] },
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Cpu {
    CooperativeShared { ceiling: u32, native_manifest: FileIdentity },
    RetainedFixed { units: u32, native_manifest: FileIdentity },
}
/// The ONE original shared memory claim, not a separate budget for each member.
/// These identities are observations, never closure or release capabilities.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Memory {
    pub bytes: u64,
    pub namespace: [u8; 16],
    pub marker: String,
    pub epoch: [u8; 16],
    pub guard: FileIdentity,
}
/// Observation of the original managed SDK GC lease actually copied by the
/// custodian into this subject. Paths/numbers never reconstruct lease authority.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SdkCustody {
    pub execution: Vec<u8>,
    pub build: u64,
    pub lease_path: Vec<u8>,
    pub lease: FileIdentity,
    pub inherited_fd: u32,
}
impl SdkCustody {
    fn validate(&self) -> io::Result<()> {
        let path = |path: &[u8]| {
            !path.is_empty()
                && path.len() <= MAX_FIELD
                && path.starts_with(b"/")
                && !path.contains(&0)
                && !path.split(|b| *b == b'/').any(|part| part == b"." || part == b"..")
        };
        if self.build == 0
            || self.lease.inode == 0
            || self.inherited_fd < 3
            || self.inherited_fd > i32::MAX as u32
            || !path(&self.execution)
            || !path(&self.lease_path)
        {
            return Err(invalid());
        }
        Ok(())
    }
}

/// Authenticated host code converts its actual current Inspection to this
/// shape. Decoding does not authenticate that code or establish custody.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Context {
    pub session: String,
    pub root_attempt: [u8; 16],
    pub host: String,
    pub boot: String,
    pub original_root: Identity,
    pub subject: Subject,
    pub cpu: Cpu,
    pub memory: Memory,
    pub sdk: Option<SdkCustody>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ContextReply {
    pub call_attempt: [u8; 16],
    pub context: Context,
}

pub(crate) fn identity_encode(e: &mut Encoder, identity: Identity) -> io::Result<()> {
    if identity.pid <= 1 || identity.birth == 0 {
        return Err(invalid());
    }
    e.number(identity.pid.into());
    e.number(identity.birth);
    e.number(match identity.birth_kind {
        BirthKind::MacosWallMicroseconds => 0,
        BirthKind::LinuxStartTicks => 1,
    });
    Ok(())
}
pub(crate) fn identity_decode(d: &mut Decoder<'_>) -> io::Result<Identity> {
    let pid = d.narrow()?;
    let birth = d.number()?;
    let birth_kind = match d.number()? {
        0 => BirthKind::MacosWallMicroseconds,
        1 => BirthKind::LinuxStartTicks,
        _ => return Err(invalid()),
    };
    let identity = Identity { pid, birth, birth_kind };
    identity_encode(&mut Encoder::new(0), identity)?;
    Ok(identity)
}
fn file_encode(e: &mut Encoder, file: FileIdentity) -> io::Result<()> {
    if file.inode == 0 {
        return Err(invalid());
    }
    e.number(file.device);
    e.number(file.inode);
    Ok(())
}
fn file_decode(d: &mut Decoder<'_>) -> io::Result<FileIdentity> {
    let file = FileIdentity { device: d.number()?, inode: d.number()? };
    file_encode(&mut Encoder::new(0), file)?;
    Ok(file)
}
impl ContextQuery {
    pub fn validate(&self) -> io::Result<()> {
        self.binding.validate()?;
        if self.call_attempt == [0; 16] || self.call_attempt == self.binding.root_attempt {
            return Err(invalid());
        }
        Ok(())
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        let mut e = Encoder::new(6);
        e.bytes(self.binding.session.as_bytes())?;
        e.0.extend(self.binding.root_attempt);
        e.0.extend(self.binding.capability);
        e.0.extend(self.call_attempt);
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 6)?;
        let query = Self {
            binding: JobBinding {
                session: d.text()?,
                root_attempt: d.array()?,
                capability: d.array()?,
            },
            call_attempt: d.array()?,
        };
        d.done()?;
        query.validate()?;
        Ok(query)
    }
}
impl Context {
    /// Syntactic initial-CPU rule ONLY after live host/proof authentication and
    /// native manifest/debt validation. Nested roots and members must borrow.
    pub fn may_acquire_initial_cpu(&self, producer: Identity) -> bool {
        matches!(self.cpu, Cpu::CooperativeShared { .. })
            && self.subject == Subject::Root { identity: self.original_root }
            && producer == self.original_root
    }
    fn validate(&self) -> io::Result<()> {
        if let Some(sdk) = &self.sdk {
            sdk.validate()?;
        }
        let marker: Vec<_> = self.memory.marker.split('-').collect();
        if self.host.is_empty()
            || self.host.len() > 256
            || self.host.as_bytes().contains(&0)
            || self.boot.is_empty()
            || self.boot.len() > 128
            || !self.boot.bytes().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
            || self.memory.bytes == 0
            || self.memory.guard.inode == 0
            || marker.len() != 3
            || marker.iter().any(|part| {
                part.is_empty()
                    || !part.bytes().all(|b| b.is_ascii_digit())
                    || part.parse::<u64>().is_err()
            })
        {
            return Err(invalid());
        }
        match self.subject {
            Subject::Root { identity } if identity == self.original_root => {}
            Subject::RegisteredMember { identity, attempt }
                if identity.pid != self.original_root.pid
                    && identity.birth_kind == self.original_root.birth_kind
                    && attempt != [0; 16]
                    && attempt != self.root_attempt => {}
            _ => return Err(invalid()),
        }
        let (width, manifest) = match self.cpu {
            Cpu::CooperativeShared { ceiling, native_manifest } => (ceiling, native_manifest),
            Cpu::RetainedFixed { units, native_manifest } => (units, native_manifest),
        };
        if width == 0 || manifest.inode == 0 {
            return Err(invalid());
        }
        Ok(())
    }
}
impl ContextReply {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        let c = &self.context;
        c.validate()?;
        if self.call_attempt == [0; 16]
            || self.call_attempt == c.root_attempt
            || c.root_attempt == [0; 16]
        {
            return Err(invalid());
        }
        crate::validate::validate_session(&c.session)?;
        let mut e = Encoder::new(7);
        e.0.extend(self.call_attempt);
        e.bytes(c.session.as_bytes())?;
        e.0.extend(c.root_attempt);
        e.bytes(c.host.as_bytes())?;
        e.bytes(c.boot.as_bytes())?;
        identity_encode(&mut e, c.original_root)?;
        match c.subject {
            Subject::Root { identity } => {
                e.number(0);
                identity_encode(&mut e, identity)?;
            }
            Subject::RegisteredMember { identity, attempt } => {
                e.number(1);
                identity_encode(&mut e, identity)?;
                e.0.extend(attempt);
            }
        }
        match c.cpu {
            Cpu::CooperativeShared { ceiling, native_manifest } => {
                e.number(0);
                e.number(ceiling.into());
                file_encode(&mut e, native_manifest)?;
            }
            Cpu::RetainedFixed { units, native_manifest } => {
                e.number(1);
                e.number(units.into());
                file_encode(&mut e, native_manifest)?;
            }
        }
        e.number(c.memory.bytes);
        e.0.extend(c.memory.namespace);
        e.bytes(c.memory.marker.as_bytes())?;
        e.0.extend(c.memory.epoch);
        file_encode(&mut e, c.memory.guard)?;
        // Always append the optional marker: older unpublished generations
        // reject trailing data rather than silently dropping SDK custody.
        match &c.sdk {
            None => e.number(0),
            Some(sdk) => {
                e.number(1);
                e.bytes(&sdk.execution)?;
                e.number(sdk.build);
                e.bytes(&sdk.lease_path)?;
                file_encode(&mut e, sdk.lease)?;
                e.number(sdk.inherited_fd.into());
            }
        }
        e.finish()
    }
    pub fn decode(bytes: &[u8], query: &ContextQuery) -> io::Result<Self> {
        query.validate()?;
        let reply = Self::decode_observation(bytes)?;
        if reply.call_attempt != query.call_attempt
            || reply.context.session != query.binding.session
            || reply.context.root_attempt != query.binding.root_attempt
        {
            return Err(invalid());
        }
        Ok(reply)
    }
    /// Parse bounded saved/native reply DATA without constructing a resource
    /// binding/capability. No peer, original transfer, SDK keeper, CPU, memory,
    /// release or execution authority follows from decoding this observation.
    pub fn decode_observation(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 7)?;
        let call_attempt = d.array()?;
        let session = d.text()?;
        let root_attempt = d.array()?;
        let host = d.text()?;
        let boot = d.text()?;
        let original_root = identity_decode(&mut d)?;
        let subject = match d.number()? {
            0 => Subject::Root { identity: identity_decode(&mut d)? },
            1 => Subject::RegisteredMember {
                identity: identity_decode(&mut d)?,
                attempt: d.array()?,
            },
            _ => return Err(invalid()),
        };
        let mode = d.number()?;
        let width = d.narrow()?;
        let native_manifest = file_decode(&mut d)?;
        let cpu = match mode {
            0 => Cpu::CooperativeShared { ceiling: width, native_manifest },
            1 => Cpu::RetainedFixed { units: width, native_manifest },
            _ => return Err(invalid()),
        };
        let memory = Memory {
            bytes: d.number()?,
            namespace: d.array()?,
            marker: d.text()?,
            epoch: d.array()?,
            guard: file_decode(&mut d)?,
        };
        let sdk = match d.number()? {
            0 => None,
            1 => Some(SdkCustody {
                execution: d.bytes()?,
                build: d.number()?,
                lease_path: d.bytes()?,
                lease: file_decode(&mut d)?,
                inherited_fd: d.narrow()?,
            }),
            _ => return Err(invalid()),
        };
        d.done()?;
        let reply = Self {
            call_attempt,
            context: Context {
                session,
                root_attempt,
                host,
                boot,
                original_root,
                subject,
                cpu,
                memory,
                sdk,
            },
        };
        reply.encode()?;
        Ok(reply)
    }
}

/// First-frame classification; both complete shapes validate before any
/// producer proof or host operation. There is no fallback from an invalid
/// member request to an execution of another kind.
#[derive(Clone, PartialEq, Eq)]
pub enum Call {
    Member(Box<Request>),
    Context(ContextQuery),
}
impl Call {
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        if header(bytes, 1).is_ok() {
            let request = Request::decode(bytes)?;
            if !request.role.is_proxy_member() {
                return Err(invalid());
            }
            Ok(Self::Member(Box::new(request)))
        } else {
            ContextQuery::decode(bytes).map(Self::Context)
        }
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        match self {
            Self::Member(request) if request.role.is_proxy_member() => request.encode(),
            Self::Member(_) => Err(invalid()),
            Self::Context(query) => query.encode(),
        }
    }
}

/// No authenticated observation was supplied. This says nothing about whether
/// the original root has launched or whether any resources have been released.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ContextUnavailable {
    pub session: String,
    pub root_attempt: [u8; 16],
    pub call_attempt: [u8; 16],
    pub reason: String,
}
impl ContextUnavailable {
    pub fn for_query(query: &ContextQuery, reason: String) -> io::Result<Self> {
        query.validate()?;
        let value = Self {
            session: query.binding.session.clone(),
            root_attempt: query.binding.root_attempt,
            call_attempt: query.call_attempt,
            reason,
        };
        value.encode()?;
        Ok(value)
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        crate::validate::validate_session(&self.session)?;
        if self.root_attempt == [0; 16]
            || self.call_attempt == [0; 16]
            || self.call_attempt == self.root_attempt
            || self.reason.is_empty()
        {
            return Err(invalid());
        }
        let mut e = Encoder::new(8);
        e.bytes(self.session.as_bytes())?;
        e.0.extend(self.root_attempt);
        e.0.extend(self.call_attempt);
        e.bytes(self.reason.as_bytes())?;
        e.finish()
    }
    pub fn decode(bytes: &[u8], query: &ContextQuery) -> io::Result<Self> {
        query.validate()?;
        let mut d = header(bytes, 8)?;
        let value = Self {
            session: d.text()?,
            root_attempt: d.array()?,
            call_attempt: d.array()?,
            reason: d.text()?,
        };
        d.done()?;
        if value.session != query.binding.session
            || value.root_attempt != query.binding.root_attempt
            || value.call_attempt != query.call_attempt
        {
            return Err(invalid());
        }
        value.encode()?;
        Ok(value)
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ContextResponse {
    Ready(Box<ContextReply>),
    Unavailable(ContextUnavailable),
}
impl ContextResponse {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        match self {
            Self::Ready(value) => value.encode(),
            Self::Unavailable(value) => value.encode(),
        }
    }
    pub fn decode(bytes: &[u8], query: &ContextQuery) -> io::Result<Self> {
        if header(bytes, 7).is_ok() {
            ContextReply::decode(bytes, query).map(Box::new).map(Self::Ready)
        } else {
            ContextUnavailable::decode(bytes, query).map(Self::Unavailable)
        }
    }
}
