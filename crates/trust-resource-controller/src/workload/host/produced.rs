//! Live produced-input registration and member observations. Bytes here
//! cannot create compilation/output custody, an active phase or execution.
use std::collections::BTreeSet;
use std::io;

use super::MemberKind;
use crate::wire::{Decoder, Encoder, header, invalid};
use crate::workload::{InputFile, contains, path};
use crate::{BirthKind, GnuTransport, Identity, MetadataFile, Request, Role};

pub const ROLE: u64 = 7;
pub const PURPOSE: &str = "sealed-workload-member-v1";
pub const REGISTRATION_MARKER: u8 = 0x5a;
/// Distinct producing profile; metadata/resolver/query capture stays 64 KiB.
pub const MAX_OUTPUT_BYTES: usize = 64 * 1024 * 1024;
pub const MAX_RUNTIME_ROOTS: usize = 256;
/// Closed data labels; the client checks maintained native provenance uses
/// these same labels without making DTO-only users link a native dependency.
pub const INPUT_POLICY: &str = "native-produced/macho-arm64-original-output-sdk-v1";
pub const INPUT_SCOPE: &str =
    "held-load-command-input-observations/local-same-uid-no-name-writers/system-runtime-tcb";
const MAX_IMAGES: usize = 128;
const MAX_IMAGE_BYTES: u64 = 1024 * 1024 * 1024;
const MAX_TOTAL_BYTES: u64 = 4 * MAX_IMAGE_BYTES;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Key {
    pub root_attempt: [u8; 16],
    pub invocation_sha256: [u8; 32],
    pub phase: [u8; 16],
    /// Exact accepted Enter sequence, never a requested CPU count.
    pub ordinal: u64,
    pub output: [u8; 16],
}
impl Key {
    pub fn validate(&self) -> io::Result<()> {
        if self.root_attempt == [0; 16]
            || self.phase == [0; 16]
            || self.phase == self.root_attempt
            || self.ordinal == 0
            || self.output == [0; 16]
            || self.output == self.phase
            || self.output == self.root_attempt
        {
            return Err(invalid());
        }
        Ok(())
    }
    fn write(&self, e: &mut Encoder) -> io::Result<()> {
        self.validate()?;
        e.0.extend(self.root_attempt);
        e.0.extend(self.invocation_sha256);
        e.0.extend(self.phase);
        e.number(self.ordinal);
        e.0.extend(self.output);
        Ok(())
    }
    fn read(d: &mut Decoder<'_>) -> io::Result<Self> {
        let key = Self {
            root_attempt: d.array()?,
            invocation_sha256: d.array()?,
            phase: d.array()?,
            ordinal: d.number()?,
            output: d.array()?,
        };
        key.validate()?;
        Ok(key)
    }
}

/// Data accompanying an actual SAME original executable descriptor from a
/// trusted live SDK UnitOutput owner. Only unsafe live registration may use it;
/// decoding this record does not qualify a path or recreate its owner.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Registration {
    pub key: Key,
    pub program: InputFile,
    pub runtime_roots: Vec<Vec<u8>>,
    /// Cold output must name its actually retained matching compiler member.
    /// None is permitted only for trusted CURRENT warm materialization.
    pub producer_attempt: Option<[u8; 16]>,
}
impl Registration {
    pub fn validate(&self) -> io::Result<()> {
        self.key.validate()?;
        if !path(&self.program.path)
            || self
                .producer_attempt
                .is_some_and(|attempt| attempt == [0; 16] || attempt == self.key.root_attempt)
        {
            return Err(invalid());
        }
        roots(&self.runtime_roots)
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        let mut e = Encoder::new(54);
        e.number(1);
        self.key.write(&mut e)?;
        e.bytes(&self.program.path)?;
        e.0.extend(self.program.sha256);
        paths_write(&mut e, &self.runtime_roots)?;
        e.number(u64::from(self.producer_attempt.is_some()));
        if let Some(attempt) = self.producer_attempt {
            e.0.extend(attempt);
        }
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 54)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let key = Key::read(&mut d)?;
        let program = InputFile {
            path: d.bytes()?,
            sha256: d.array()?,
        };
        let runtime_roots = paths_read(&mut d, MAX_RUNTIME_ROOTS)?;
        let producer_attempt = match d.number()? {
            0 => None,
            1 => Some(d.array()?),
            _ => return Err(invalid()),
        };
        d.done()?;
        let value = Self {
            key,
            program,
            runtime_roots,
            producer_attempt,
        };
        value.validate()?;
        Ok(value)
    }
}

/// Equality observation only. The actual private host registry retains the
/// original image/output/SDK owner and separately authorizes every member GO.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RegistrationAck {
    pub key: Key,
    pub executable: MetadataFile,
}
impl RegistrationAck {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        RegistrationReply::Registered(self.clone()).encode()
    }
    pub fn decode(bytes: &[u8], expected: &Registration) -> io::Result<Self> {
        match RegistrationReply::decode(bytes, expected)? {
            RegistrationReply::Registered(ack) => Ok(ack),
            RegistrationReply::Refused { reason, .. } => {
                Err(io::Error::new(io::ErrorKind::PermissionDenied, reason))
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RegistrationReply {
    Registered(RegistrationAck),
    Refused { key: Key, reason: String },
}
impl RegistrationReply {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        let mut e = Encoder::new(52);
        e.number(1);
        match self {
            Self::Registered(ack) => {
                e.number(0);
                ack.key.write(&mut e)?;
                file_valid(&ack.executable)?;
                file_write(&mut e, &ack.executable)?;
            }
            Self::Refused { key, reason } => {
                if !text(reason, 4096) {
                    return Err(invalid());
                }
                e.number(1);
                key.write(&mut e)?;
                e.bytes(reason.as_bytes())?;
            }
        }
        e.finish()
    }
    pub fn decode(bytes: &[u8], expected: &Registration) -> io::Result<Self> {
        expected.validate()?;
        let mut d = header(bytes, 52)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let decision = d.number()?;
        let key = Key::read(&mut d)?;
        if key != expected.key {
            return Err(invalid());
        }
        let value = match decision {
            0 => {
                let executable = file_read(&mut d)?;
                if executable.path != expected.program.path
                    || executable.sha256 != expected.program.sha256
                {
                    return Err(invalid());
                }
                Self::Registered(RegistrationAck { key, executable })
            }
            1 => Self::Refused {
                key,
                reason: d.text()?,
            },
            _ => return Err(invalid()),
        };
        d.done()?;
        value.encode()?;
        Ok(value)
    }
}

pub(crate) fn validate_member(member: &Request) -> io::Result<()> {
    if member.role != Role::WorkloadProduced
        || member.delegations.cpu.is_some()
        || !matches!(member.delegations.gnu, GnuTransport::None)
        || !member.delegations.fences.is_empty()
        || member.command.arg0.is_some()
        || member.timeout_ns.is_none()
        || member
            .command
            .environment
            .iter()
            .any(|(name, _)| protected_environment_name(name) || loader_override_name(name))
    {
        return Err(invalid());
    }
    Ok(())
}

/// These facts belong to the actual host/phase, never caller-supplied semantic
/// environment. The adapter records its actual ProcessBuilder observation
/// separately before omitting private transport values from a bound request.
pub fn protected_environment_name(name: &[u8]) -> bool {
    [
        b"MAKEFLAGS".as_slice(),
        b"MFLAGS",
        b"CARGO_MAKEFLAGS",
        b"CARGO_JOBSERVER_HANDOFF",
        b"PARENT_SESSION_ID",
    ]
    .iter()
    .any(|key| name.eq_ignore_ascii_case(key))
        || [
            b"ATERM_".as_slice(),
            b"BUILD_SLOT_",
            b"TRUST_CPU_",
            b"TRUST_JOBSERVER_",
            b"TRUST_RESOURCE_",
        ]
        .iter()
        .any(|prefix| {
            name.get(..prefix.len())
                .is_some_and(|start| start.eq_ignore_ascii_case(prefix))
        })
}
/// Dynamic loader input must come from the separately held exact runtime
/// agreement. Unknown/project overrides refuse, rather than silently changing
/// the request's semantics when the host injects its held runtime paths.
pub fn loader_override_name(name: &[u8]) -> bool {
    [b"DYLD_".as_slice(), b"LD_"].iter().any(|prefix| {
        name.get(..prefix.len())
            .is_some_and(|start| start.eq_ignore_ascii_case(prefix))
    })
}
fn kind_number(kind: MemberKind) -> io::Result<u64> {
    match kind {
        MemberKind::BuildScript => Ok(1),
        MemberKind::Inventory => Ok(2),
        MemberKind::Sample => Ok(3),
        MemberKind::Coordinator => Ok(4),
        MemberKind::CompilerQuery => Err(invalid()),
    }
}
fn kind_read(number: u64) -> io::Result<MemberKind> {
    match number {
        1 => Ok(MemberKind::BuildScript),
        2 => Ok(MemberKind::Inventory),
        3 => Ok(MemberKind::Sample),
        4 => Ok(MemberKind::Coordinator),
        _ => Err(invalid()),
    }
}

/// Mandatory new role7 envelope. Generic Call/AccountedRequest still refuse
/// this role. No caller supplies another CPU/GNU/SDK grant or legacy budget.
#[derive(Clone, PartialEq, Eq)]
pub struct ProducedRequest {
    pub member: Request,
    pub key: Key,
    pub kind: MemberKind,
    pub program_sha256: [u8; 32],
    pub runtime_roots: Vec<Vec<u8>>,
}
impl ProducedRequest {
    pub fn validate(&self) -> io::Result<()> {
        self.member.validate()?;
        validate_member(&self.member)?;
        self.key.validate()?;
        kind_number(self.kind)?;
        roots(&self.runtime_roots)?;
        let args = &self.member.command.args;
        let supported = match self.kind {
            MemberKind::BuildScript => args.is_empty(),
            MemberKind::Inventory => matches!(args.as_slice(),[arg] if arg==b"--list"),
            MemberKind::Sample => matches!(args.as_slice(),[arg] if arg==b"--test-threads=1"),
            MemberKind::Coordinator => super::coordinator::Plan::from_startup_args(args).is_ok(),
            MemberKind::CompilerQuery => false,
        };
        if !supported || self.member.binding.root_attempt != self.key.root_attempt {
            return Err(invalid());
        }
        Ok(())
    }
    pub fn validate_registered(&self, registration: &Registration) -> io::Result<()> {
        self.validate()?;
        registration.validate()?;
        if self.key != registration.key
            || self.member.command.program != registration.program.path
            || self.program_sha256 != registration.program.sha256
            || self.runtime_roots != registration.runtime_roots
        {
            return Err(invalid());
        }
        Ok(())
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        let mut e = Encoder::new(52);
        e.number(2);
        e.frame_bytes(&self.member.encode()?)?;
        self.key.write(&mut e)?;
        e.number(kind_number(self.kind)?);
        e.0.extend(self.program_sha256);
        paths_write(&mut e, &self.runtime_roots)?;
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 52)?;
        if d.number()? != 2 {
            return Err(invalid());
        }
        let value = Self {
            member: Request::decode(&d.frame_bytes()?)?,
            key: Key::read(&mut d)?,
            kind: kind_read(d.number()?)?,
            program_sha256: d.array()?,
            runtime_roots: paths_read(&mut d, MAX_RUNTIME_ROOTS)?,
        };
        d.done()?;
        value.validate()?;
        Ok(value)
    }
    pub fn hello(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        let attempt: String = self
            .key
            .root_attempt
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect();
        Ok(format!(
            "{{\"version\":3,\"role\":\"{PURPOSE}\",\"session\":\"{}\",\"attempt\":\"{attempt}\"}}",
            self.member.binding.session
        )
        .into_bytes())
    }
}

/// Actual mixed-root image inventory observed after suspended birth and the
/// second held-image check, before GO. Unlike MetadataPrepared13, dependencies
/// may reside in EITHER the original output OR the original SDK, never elsewhere.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProducedPrepared {
    pub key: Key,
    pub member_attempt: [u8; 16],
    pub identity: Identity,
    pub output_root: Vec<u8>,
    pub sdk_root: Vec<u8>,
    pub policy: String,
    pub scope: String,
    pub executable: MetadataFile,
    pub runtime: Vec<MetadataFile>,
    pub loader_paths: Vec<Vec<u8>>,
    pub system_dependencies: Vec<String>,
    pub host: String,
    pub boot: String,
}
impl ProducedPrepared {
    pub fn validate(&self) -> io::Result<()> {
        self.key.validate()?;
        if self.member_attempt == [0; 16]
            || self.member_attempt == self.key.root_attempt
            || self.identity.pid <= 1
            || self.identity.birth == 0
            || !path(&self.output_root)
            || !path(&self.sdk_root)
            || contains(&self.output_root, &self.sdk_root)
            || contains(&self.sdk_root, &self.output_root)
            || self.policy != INPUT_POLICY
            || self.scope != INPUT_SCOPE
            || !text(&self.host, 256)
            || !text(&self.boot, 128)
            || self.runtime.len() > MAX_IMAGES
            || self.loader_paths.len() > MAX_RUNTIME_ROOTS + 3
            || self.system_dependencies.len() > MAX_IMAGES
        {
            return Err(invalid());
        }
        if !under(&self.output_root, &self.executable.path) {
            return Err(invalid());
        }
        let mut names = BTreeSet::new();
        let mut ids = BTreeSet::new();
        let mut total = 0u64;
        for file in std::iter::once(&self.executable).chain(&self.runtime) {
            file_valid(file)?;
            total = total.checked_add(file.bytes).ok_or_else(invalid)?;
            if (!under(&self.output_root, &file.path) && !under(&self.sdk_root, &file.path))
                || !names.insert(&file.path)
                || !ids.insert((file.device, file.inode))
                || total > MAX_TOTAL_BYTES
            {
                return Err(invalid());
            }
        }
        names.clear();
        for candidate in &self.loader_paths {
            if !path(candidate)
                || (!under(&self.output_root, candidate) && !under(&self.sdk_root, candidate))
                || !names.insert(candidate)
            {
                return Err(invalid());
            }
        }
        let mut system = BTreeSet::new();
        for candidate in &self.system_dependencies {
            if !text(candidate, 4096)
                || !path(candidate.as_bytes())
                || !(candidate.starts_with("/usr/lib/")
                    || candidate.starts_with("/System/Library/"))
                || !system.insert(candidate)
            {
                return Err(invalid());
            }
        }
        Ok(())
    }
    pub fn validate_for(&self, request: &ProducedRequest) -> io::Result<()> {
        self.validate()?;
        request.validate()?;
        if self.key != request.key
            || self.member_attempt != request.member.member_attempt
            || self.executable.path != request.member.command.program
            || self.executable.sha256 != request.program_sha256
        {
            return Err(invalid());
        }
        let parent_end = request
            .member
            .command
            .program
            .iter()
            .rposition(|byte| *byte == b'/')
            .ok_or_else(invalid)?;
        let mut expected = vec![request.member.command.program[..parent_end].to_vec()];
        expected.extend(request.runtime_roots.iter().cloned());
        if !self.loader_paths.starts_with(&expected) {
            return Err(invalid());
        }
        let defaults = [
            [&self.sdk_root[..], b"/lib"].concat(),
            [&self.sdk_root[..], b"/lib/rustlib/aarch64-apple-darwin/lib"].concat(),
        ];
        let mut next = 0;
        for actual in &self.loader_paths[expected.len()..] {
            let relative = defaults[next..]
                .iter()
                .position(|candidate| candidate == actual)
                .ok_or_else(invalid)?;
            next += relative + 1;
        }
        Ok(())
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        let mut e = Encoder::new(54);
        e.number(2);
        self.key.write(&mut e)?;
        e.0.extend(self.member_attempt);
        e.number(self.identity.pid.into());
        e.number(self.identity.birth);
        e.number(match self.identity.birth_kind {
            BirthKind::MacosWallMicroseconds => 0,
            BirthKind::LinuxStartTicks => 1,
        });
        for value in [
            &self.output_root[..],
            &self.sdk_root[..],
            self.policy.as_bytes(),
            self.scope.as_bytes(),
            self.host.as_bytes(),
            self.boot.as_bytes(),
        ] {
            e.bytes(value)?;
        }
        file_write(&mut e, &self.executable)?;
        e.number(self.runtime.len() as u64);
        for file in &self.runtime {
            file_write(&mut e, file)?;
        }
        paths_write(&mut e, &self.loader_paths)?;
        e.number(self.system_dependencies.len() as u64);
        for value in &self.system_dependencies {
            e.bytes(value.as_bytes())?;
        }
        e.finish()
    }
    pub fn decode(bytes: &[u8], request: &ProducedRequest) -> io::Result<Self> {
        let mut d = header(bytes, 54)?;
        if d.number()? != 2 {
            return Err(invalid());
        }
        let key = Key::read(&mut d)?;
        let member_attempt = d.array()?;
        let identity = Identity {
            pid: d.narrow()?,
            birth: d.number()?,
            birth_kind: match d.number()? {
                0 => BirthKind::MacosWallMicroseconds,
                1 => BirthKind::LinuxStartTicks,
                _ => return Err(invalid()),
            },
        };
        let output_root = d.bytes()?;
        let sdk_root = d.bytes()?;
        let policy = d.text()?;
        let scope = d.text()?;
        let host = d.text()?;
        let boot = d.text()?;
        let executable = file_read(&mut d)?;
        let mut runtime = Vec::new();
        for _ in 0..d.count(MAX_IMAGES)? {
            runtime.push(file_read(&mut d)?);
        }
        let loader_paths = paths_read(&mut d, MAX_RUNTIME_ROOTS + 3)?;
        let mut system_dependencies = Vec::new();
        for _ in 0..d.count(MAX_IMAGES)? {
            system_dependencies.push(d.text()?);
        }
        d.done()?;
        let value = Self {
            key,
            member_attempt,
            identity,
            output_root,
            sdk_root,
            policy,
            scope,
            executable,
            runtime,
            loader_paths,
            system_dependencies,
            host,
            boot,
        };
        value.validate_for(request)?;
        Ok(value)
    }
}

fn text(value: &str, max: usize) -> bool {
    !value.is_empty() && value.len() <= max && !value.chars().any(char::is_control)
}
fn under(root: &[u8], value: &[u8]) -> bool {
    contains(root, value) && root != value
}
fn roots(values: &[Vec<u8>]) -> io::Result<()> {
    if values.len() > MAX_RUNTIME_ROOTS {
        return Err(invalid());
    }
    let mut seen = BTreeSet::new();
    for value in values {
        if !path(value) || value.contains(&b':') || !seen.insert(value) {
            return Err(invalid());
        }
    }
    Ok(())
}
fn paths_write(e: &mut Encoder, values: &[Vec<u8>]) -> io::Result<()> {
    e.number(values.len() as u64);
    for value in values {
        e.bytes(value)?;
    }
    Ok(())
}
fn paths_read(d: &mut Decoder<'_>, max: usize) -> io::Result<Vec<Vec<u8>>> {
    let mut values = Vec::new();
    for _ in 0..d.count(max)? {
        values.push(d.bytes()?);
    }
    Ok(values)
}
fn file_valid(file: &MetadataFile) -> io::Result<()> {
    if !path(&file.path) || file.bytes == 0 || file.bytes > MAX_IMAGE_BYTES || file.inode == 0 {
        Err(invalid())
    } else {
        Ok(())
    }
}
fn file_write(e: &mut Encoder, file: &MetadataFile) -> io::Result<()> {
    file_valid(file)?;
    e.bytes(&file.path)?;
    e.0.extend(file.sha256);
    e.number(file.bytes);
    e.number(file.device);
    e.number(file.inode);
    Ok(())
}
fn file_read(d: &mut Decoder<'_>) -> io::Result<MetadataFile> {
    Ok(MetadataFile {
        path: d.bytes()?,
        sha256: d.array()?,
        bytes: d.number()?,
        device: d.number()?,
        inode: d.number()?,
    })
}

#[cfg(test)]
pub(crate) mod tests;
