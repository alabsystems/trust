//! Fixed trusted Root-local IO. These frames select DATA only: actual original
//! bank/SDK/output custody and native writer exclusion precede admission.
//! Local lexical completion is never hosted target/group retirement or proof.
use std::io;

use crate::wire::{Decoder, Encoder, header, invalid};
use crate::{BirthKind, FileIdentity, Identity};

pub const MAX_INTENTS: usize = 4096;
pub const MAX_PROTECTED_FILES: usize = 1024;
pub const MAX_PROTECTED_DIRECTORIES: usize = 1024;
pub const MAX_PROTECTED_TREES: usize = 256;
pub const MAX_INTENT_BYTES: usize = 1024 * 1024;
pub const MAX_TOTAL_BYTES: u64 = 16 * 1024 * 1024 * 1024;
pub const MAX_TIMEOUT_NS: u64 = 600_000_000_000;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    PrepareOutputs,
    MaterializeAndPublish,
    PublishFresh,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Intent {
    Directory { path: Vec<u8> },
    CaptureFile { path: Vec<u8> },
    VerifyFile { path: Vec<u8> },
    PublishFile { source: Vec<u8>, destination: Vec<u8> },
}
impl Intent {
    pub fn paths(&self) -> impl Iterator<Item = &[u8]> {
        let (first, second) = match self {
            Self::Directory { path } | Self::CaptureFile { path } | Self::VerifyFile { path } => {
                (path.as_slice(), None)
            }
            Self::PublishFile { source, destination } => {
                (source.as_slice(), Some(destination.as_slice()))
            }
        };
        std::iter::once(first).chain(second)
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Key {
    pub root_attempt: [u8; 16],
    pub invocation_sha256: [u8; 32],
    pub sequence: u64,
    pub phase: [u8; 16],
    pub ordinal: u64,
    pub coordinator: [u8; 16],
    pub operation: [u8; 16],
}
impl Key {
    fn validate(&self) -> io::Result<()> {
        if self.root_attempt == [0; 16]
            || self.invocation_sha256 == [0; 32]
            || self.sequence == 0
            || self.phase == [0; 16]
            || self.ordinal == 0
            || self.coordinator == [0; 16]
            || self.operation == [0; 16]
            || self.coordinator == self.root_attempt
            || self.operation == self.root_attempt
            || self.operation == self.coordinator
        {
            return Err(invalid());
        }
        Ok(())
    }
    fn write(&self, e: &mut Encoder) -> io::Result<()> {
        self.validate()?;
        e.0.extend(self.root_attempt);
        e.0.extend(self.invocation_sha256);
        e.number(self.sequence);
        e.0.extend(self.phase);
        e.number(self.ordinal);
        e.0.extend(self.coordinator);
        e.0.extend(self.operation);
        Ok(())
    }
    fn read(d: &mut Decoder<'_>) -> io::Result<Self> {
        let value = Self {
            root_attempt: d.array()?,
            invocation_sha256: d.array()?,
            sequence: d.number()?,
            phase: d.array()?,
            ordinal: d.number()?,
            coordinator: d.array()?,
            operation: d.array()?,
        };
        value.validate()?;
        Ok(value)
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CpuOriginal {
    pub loan: [u8; 16],
    pub slot: u32,
    pub backing: FileIdentity,
}
impl CpuOriginal {
    fn write(&self, e: &mut Encoder) -> io::Result<()> {
        if self.loan == [0; 16] || self.slot >= super::MAX_CPU_SET as u32 || self.backing.inode == 0
        {
            return Err(invalid());
        }
        e.0.extend(self.loan);
        e.number(self.slot.into());
        e.number(self.backing.device);
        e.number(self.backing.inode);
        Ok(())
    }
    fn read(d: &mut Decoder<'_>) -> io::Result<Self> {
        Ok(Self {
            loan: d.array()?,
            slot: d.narrow()?,
            backing: FileIdentity { device: d.number()?, inode: d.number()? },
        })
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Begin {
    pub kind: Kind,
    pub cpu: CpuOriginal,
    pub owner: Identity,
    pub output_root: Vec<u8>,
    pub timeout_ns: u64,
    pub producer: Option<[u8; 16]>,
    pub intents: Vec<Intent>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Outcome {
    Succeeded { operations: u64, bytes: u64 },
    Failed { reason: String },
}
impl Outcome {
    fn write(&self, e: &mut Encoder) -> io::Result<()> {
        match self {
            Self::Succeeded { operations, bytes }
                if *operations <= MAX_INTENTS as u64 && *bytes <= MAX_TOTAL_BYTES =>
            {
                e.number(0);
                e.number(*operations);
                e.number(*bytes);
            }
            Self::Failed { reason }
                if !reason.is_empty() && reason.len() <= 4096 && !reason.contains('\0') =>
            {
                e.number(1);
                e.bytes(reason.as_bytes())?;
            }
            _ => return Err(invalid()),
        }
        Ok(())
    }
    fn read(d: &mut Decoder<'_>) -> io::Result<Self> {
        Ok(match d.number()? {
            0 => Self::Succeeded { operations: d.number()?, bytes: d.number()? },
            1 => Self::Failed { reason: String::from_utf8(d.bytes()?).map_err(|_| invalid())? },
            _ => return Err(invalid()),
        })
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Operation {
    Begin(Begin),
    Complete { begun_sequence: u64, outcome: Outcome },
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Request {
    pub key: Key,
    pub operation: Operation,
}
fn path(value: &[u8]) -> bool {
    value.len() > 1
        && value.len() <= 4096
        && value[0] == b'/'
        && !value.contains(&0)
        && value[1..]
            .split(|byte| *byte == b'/')
            .all(|part| !part.is_empty() && part != b"." && part != b"..")
}
fn child(root: &[u8], value: &[u8]) -> bool {
    value.starts_with(root) && value.get(root.len()) == Some(&b'/')
}
fn identity_write(value: Identity, e: &mut Encoder) -> io::Result<()> {
    if value.pid <= 1 || value.birth == 0 {
        return Err(invalid());
    }
    e.number(value.pid.into());
    e.number(value.birth);
    e.number(match value.birth_kind {
        BirthKind::MacosWallMicroseconds => 0,
        BirthKind::LinuxStartTicks => 1,
    });
    Ok(())
}
fn identity_read(d: &mut Decoder<'_>) -> io::Result<Identity> {
    Ok(Identity {
        pid: d.narrow()?,
        birth: d.number()?,
        birth_kind: match d.number()? {
            0 => BirthKind::MacosWallMicroseconds,
            1 => BirthKind::LinuxStartTicks,
            _ => return Err(invalid()),
        },
    })
}
impl Begin {
    pub fn validate(&self) -> io::Result<()> {
        if !path(&self.output_root)
            || self.timeout_ns == 0
            || self.timeout_ns > MAX_TIMEOUT_NS
            || self.intents.is_empty()
            || self.intents.len() > MAX_INTENTS
        {
            return Err(invalid());
        }
        match (self.kind, self.producer) {
            (Kind::MaterializeAndPublish, Some(value)) if value != [0; 16] => {}
            (Kind::PrepareOutputs | Kind::PublishFresh, None) => {}
            _ => return Err(invalid()),
        }
        let mut bytes = 0usize;
        for intent in &self.intents {
            if matches!(
                (self.kind, intent),
                (Kind::PrepareOutputs, Intent::CaptureFile { .. } | Intent::PublishFile { .. })
                    | (Kind::PublishFresh, Intent::CaptureFile { .. })
            ) {
                return Err(invalid());
            }
            for value in intent.paths() {
                bytes = bytes.checked_add(value.len()).ok_or_else(invalid)?;
                if bytes > MAX_INTENT_BYTES || !path(value) || !child(&self.output_root, value) {
                    return Err(invalid());
                }
            }
            if let Intent::PublishFile { source, destination } = intent
                && source == destination
            {
                return Err(invalid());
            }
        }
        Ok(())
    }
    fn write(&self, e: &mut Encoder) -> io::Result<()> {
        self.validate()?;
        e.number(match self.kind {
            Kind::PrepareOutputs => 0,
            Kind::MaterializeAndPublish => 1,
            Kind::PublishFresh => 2,
        });
        self.cpu.write(e)?;
        identity_write(self.owner, e)?;
        e.bytes(&self.output_root)?;
        e.number(self.timeout_ns);
        e.number(u64::from(self.producer.is_some()));
        if let Some(value) = self.producer {
            e.0.extend(value)
        }
        e.number(self.intents.len() as u64);
        for intent in &self.intents {
            match intent {
                Intent::Directory { path } => {
                    e.number(0);
                    e.bytes(path)?
                }
                Intent::CaptureFile { path } => {
                    e.number(1);
                    e.bytes(path)?
                }
                Intent::VerifyFile { path } => {
                    e.number(2);
                    e.bytes(path)?
                }
                Intent::PublishFile { source, destination } => {
                    e.number(3);
                    e.bytes(source)?;
                    e.bytes(destination)?
                }
            }
        }
        Ok(())
    }
    fn read(d: &mut Decoder<'_>) -> io::Result<Self> {
        let kind = match d.number()? {
            0 => Kind::PrepareOutputs,
            1 => Kind::MaterializeAndPublish,
            2 => Kind::PublishFresh,
            _ => return Err(invalid()),
        };
        let cpu = CpuOriginal::read(d)?;
        let owner = identity_read(d)?;
        let output_root = d.bytes()?;
        let timeout_ns = d.number()?;
        let producer = match d.number()? {
            0 => None,
            1 => Some(d.array()?),
            _ => return Err(invalid()),
        };
        let count = d.count(MAX_INTENTS)?;
        if count == 0 {
            return Err(invalid());
        }
        let mut intents = Vec::with_capacity(count);
        let mut bytes = 0usize;
        for _ in 0..count {
            let value = match d.number()? {
                0 => Intent::Directory { path: d.bytes()? },
                1 => Intent::CaptureFile { path: d.bytes()? },
                2 => Intent::VerifyFile { path: d.bytes()? },
                3 => Intent::PublishFile { source: d.bytes()?, destination: d.bytes()? },
                _ => return Err(invalid()),
            };
            for path in value.paths() {
                bytes = bytes.checked_add(path.len()).ok_or_else(invalid)?;
                if bytes > MAX_INTENT_BYTES {
                    return Err(invalid());
                }
            }
            intents.push(value);
        }
        let value = Self { kind, cpu, owner, output_root, timeout_ns, producer, intents };
        value.validate()?;
        Ok(value)
    }
}
impl Request {
    /// Conservative owned representation only; no native owner or admission
    /// is reconstructed from this size/equality observation.
    pub fn retained_bytes(&self) -> Option<usize> {
        let mut bytes = std::mem::size_of::<Self>();
        match &self.operation {
            Operation::Begin(begin) => {
                bytes = bytes.checked_add(begin.output_root.capacity())?.checked_add(
                    begin.intents.capacity().checked_mul(std::mem::size_of::<Intent>())?,
                )?;
                for intent in &begin.intents {
                    let add = match intent {
                        Intent::Directory { path }
                        | Intent::CaptureFile { path }
                        | Intent::VerifyFile { path } => path.capacity(),
                        Intent::PublishFile { source, destination } => {
                            source.capacity().checked_add(destination.capacity())?
                        }
                    };
                    bytes = bytes.checked_add(add)?;
                }
            }
            Operation::Complete { outcome: Outcome::Failed { reason }, .. } => {
                bytes = bytes.checked_add(reason.capacity())?
            }
            Operation::Complete { .. } => {}
        }
        Some(bytes)
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        let mut e = Encoder::new(100);
        e.number(1);
        self.key.write(&mut e)?;
        match &self.operation {
            Operation::Begin(value) => {
                e.number(0);
                value.write(&mut e)?
            }
            Operation::Complete { begun_sequence, outcome } => {
                if *begun_sequence == 0 || *begun_sequence >= self.key.sequence {
                    return Err(invalid());
                }
                e.number(1);
                e.number(*begun_sequence);
                outcome.write(&mut e)?
            }
        }
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 100)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let key = Key::read(&mut d)?;
        let operation = match d.number()? {
            0 => Operation::Begin(Begin::read(&mut d)?),
            1 => {
                Operation::Complete { begun_sequence: d.number()?, outcome: Outcome::read(&mut d)? }
            }
            _ => return Err(invalid()),
        };
        d.done()?;
        let value = Self { key, operation };
        value.encode()?;
        Ok(value)
    }
}
/// Negative native identity DATA; it can veto IO, never authorize it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Exclusions {
    pub files: Vec<FileIdentity>,
    pub directories: Vec<FileIdentity>,
    pub trees: Vec<FileIdentity>,
}
impl Exclusions {
    fn write(&self, e: &mut Encoder) -> io::Result<()> {
        for (values, limit) in [
            (&self.files, MAX_PROTECTED_FILES),
            (&self.directories, MAX_PROTECTED_DIRECTORIES),
            (&self.trees, MAX_PROTECTED_TREES),
        ] {
            if values.len() > limit || values.iter().any(|id| id.inode == 0) {
                return Err(invalid());
            }
            e.number(values.len() as u64);
            for id in values {
                e.number(id.device);
                e.number(id.inode);
            }
        }
        Ok(())
    }
    fn read(d: &mut Decoder<'_>) -> io::Result<Self> {
        fn list(d: &mut Decoder<'_>, limit: usize) -> io::Result<Vec<FileIdentity>> {
            let count = d.count(limit)?;
            let mut values = Vec::new();
            values.try_reserve_exact(count).map_err(|_| invalid())?;
            for _ in 0..count {
                values.push(FileIdentity { device: d.number()?, inode: d.number()? });
            }
            Ok(values)
        }
        Ok(Self {
            files: list(d, MAX_PROTECTED_FILES)?,
            directories: list(d, MAX_PROTECTED_DIRECTORIES)?,
            trees: list(d, MAX_PROTECTED_TREES)?,
        })
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Decision {
    Ready { cpu: CpuOriginal, exclusions: Exclusions },
    Busy,
    Refused { reason: String },
    Completed { outcome: Outcome },
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Reply {
    pub key: Key,
    pub decision: Decision,
}
impl Reply {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        let mut e = Encoder::new(101);
        e.number(1);
        self.key.write(&mut e)?;
        match &self.decision {
            Decision::Ready { cpu, exclusions } => {
                e.number(0);
                cpu.write(&mut e)?;
                exclusions.write(&mut e)?
            }
            Decision::Busy => e.number(1),
            Decision::Refused { reason } => {
                e.number(2);
                Outcome::Failed { reason: reason.clone() }.write(&mut e)?
            }
            Decision::Completed { outcome } => {
                e.number(3);
                outcome.write(&mut e)?
            }
        }
        e.finish()
    }
    pub fn decode(bytes: &[u8], request: &Request) -> io::Result<Self> {
        let mut d = header(bytes, 101)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let key = Key::read(&mut d)?;
        if key != request.key {
            return Err(invalid());
        }
        let decision = match d.number()? {
            0 => Decision::Ready {
                cpu: CpuOriginal::read(&mut d)?,
                exclusions: Exclusions::read(&mut d)?,
            },
            1 => Decision::Busy,
            2 => {
                let Outcome::Failed { reason } = Outcome::read(&mut d)? else {
                    return Err(invalid());
                };
                Decision::Refused { reason }
            }
            3 => Decision::Completed { outcome: Outcome::read(&mut d)? },
            _ => return Err(invalid()),
        };
        d.done()?;
        let value = Self { key, decision };
        value.encode()?;
        match (&request.operation, &value.decision) {
            (Operation::Begin(begin), Decision::Ready { cpu, .. }) if begin.cpu == *cpu => {}
            (Operation::Begin(_), Decision::Busy | Decision::Refused { .. }) => {}
            (Operation::Complete { outcome: expected, .. }, Decision::Completed { outcome })
                if expected == outcome || matches!(outcome, Outcome::Failed { .. }) => {}
            _ => return Err(invalid()),
        }
        Ok(value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    // Wire DATA only. No SDK, CPU lease, LocalIoScope or Ready owner exists.
    fn request() -> Request {
        Request {
            key: Key {
                root_attempt: [1; 16],
                invocation_sha256: [2; 32],
                sequence: 1,
                phase: [3; 16],
                ordinal: 1,
                coordinator: [4; 16],
                operation: [5; 16],
            },
            operation: Operation::Begin(Begin {
                kind: Kind::PrepareOutputs,
                cpu: CpuOriginal {
                    loan: [5; 16],
                    slot: 1,
                    backing: FileIdentity { device: 6, inode: 7 },
                },
                owner: Identity {
                    pid: 123,
                    birth: 456,
                    birth_kind: BirthKind::MacosWallMicroseconds,
                },
                output_root: b"/selected".to_vec(),
                timeout_ns: 1000,
                producer: None,
                intents: vec![Intent::Directory { path: b"/selected/private_\xff/unit".to_vec() }],
            }),
        }
    }
    #[test]
    fn local_wire_preserves_raw_paths_and_rejects_every_incomplete_prefix() {
        let request = request();
        let bytes = request.encode().unwrap();
        assert_eq!(Request::decode(&bytes).unwrap(), request);
        for length in 0..bytes.len() {
            assert!(Request::decode(&bytes[..length]).is_err(), "prefix {length}");
        }
        let mut extra = bytes;
        extra.push(0);
        assert!(Request::decode(&extra).is_err());
        let mut escaping = request.clone();
        let Operation::Begin(begin) = &mut escaping.operation else { unreachable!() };
        begin.intents = vec![Intent::Directory { path: b"/selected/private/../source".to_vec() }];
        assert!(escaping.encode().is_err());
    }
    #[test]
    fn reply_cannot_change_original_cpu_or_upgrade_a_failed_local_return() {
        let request = request();
        let Operation::Begin(begin) = &request.operation else { unreachable!() };
        let mut changed = begin.cpu;
        changed.slot += 1;
        let reply = Reply {
            key: request.key,
            decision: Decision::Ready {
                cpu: changed,
                exclusions: Exclusions {
                    files: Vec::new(),
                    directories: Vec::new(),
                    trees: Vec::new(),
                },
            },
        };
        assert!(Reply::decode(&reply.encode().unwrap(), &request).is_err());
        let complete = Request {
            key: Key { sequence: 2, ..request.key },
            operation: Operation::Complete {
                begun_sequence: 1,
                outcome: Outcome::Failed { reason: "actual IO failed".into() },
            },
        };
        let upgraded = Reply {
            key: complete.key,
            decision: Decision::Completed {
                outcome: Outcome::Succeeded { operations: 1, bytes: 0 },
            },
        };
        assert!(Reply::decode(&upgraded.encode().unwrap(), &complete).is_err());
        let retained = Reply {
            key: complete.key,
            decision: Decision::Completed {
                outcome: Outcome::Failed { reason: "native failure retained".into() },
            },
        };
        assert!(Reply::decode(&retained.encode().unwrap(), &complete).is_ok());
    }
    #[test]
    fn local_manifest_retention_counts_reserved_capacity_beyond_wire_length() {
        let mut request = request();
        let before = request.retained_bytes().unwrap();
        let Operation::Begin(begin) = &mut request.operation else { unreachable!() };
        begin.output_root.reserve_exact(4096);
        begin.intents.reserve_exact(64);
        let Intent::Directory { path } = &mut begin.intents[0] else { unreachable!() };
        path.reserve_exact(8192);
        let after = request.retained_bytes().unwrap();
        assert!(after >= before + 4096 + 8192 + 64 * std::mem::size_of::<Intent>());
        assert!(
            request.encode().unwrap().len() < after,
            "encoding length cannot account for retained spare capacity"
        );
    }
}
