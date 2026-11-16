//! Paired graph observations and continuations. Full60 is the binding; none of
//! these bytes constructs native custody, an admitted action or a proof grade.
use std::io;

use crate::wire::{Decoder, Encoder, header, invalid};
pub use crate::workload::service::Stream;
pub use crate::workload::service::checkpoint::Capture;
use crate::{BirthKind, FileIdentity, Identity};

// Explicit service revision; original Ready61/v1 and full60/host meanings stay closed.
pub mod compiler_observation;

pub const MAX_CHUNK_BYTES: usize = 64 * 1024;
pub const MAX_STREAM_BYTES: u64 = 64 * 1024 * 1024;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Binding {
    pub root_attempt: [u8; 16],
    pub invocation_sha256: [u8; 32],
}
impl Binding {
    fn write(&self, e: &mut Encoder) -> io::Result<()> {
        if self.root_attempt == [0; 16] || self.invocation_sha256 == [0; 32] {
            return Err(invalid());
        }
        e.0.extend(self.root_attempt);
        e.0.extend(self.invocation_sha256);
        Ok(())
    }
    fn read(d: &mut Decoder<'_>) -> io::Result<Self> {
        let value = Self { root_attempt: d.array()?, invocation_sha256: d.array()? };
        value.write(&mut Encoder::new(0))?;
        Ok(value)
    }
    pub fn check(&self, expected: &Self) -> io::Result<()> {
        if self == expected { Ok(()) } else { Err(invalid()) }
    }
}

/// A phase index, never a compile UnitIndex. The original compile-unit census
/// and the two independent verification indices stay separately scoped.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Node {
    AyCompile,
    Advisory,
    Strict,
    ConsumerCompile,
    Inventory { target: u32 },
    Sample { target: u32, repetition: u32 },
}
impl Node {
    pub fn population(repetitions: u32) -> io::Result<Vec<Self>> {
        if !(1..=crate::workload::WORKLOAD_MAX_REPETITIONS).contains(&repetitions) {
            return Err(invalid());
        }
        let mut nodes = vec![Self::AyCompile, Self::Advisory, Self::Strict, Self::ConsumerCompile];
        nodes.extend((0..2).map(|target| Self::Inventory { target }));
        for target in 0..2 {
            nodes.extend((0..repetitions).map(|repetition| Self::Sample { target, repetition }));
        }
        Ok(nodes)
    }
    fn write(self, e: &mut Encoder, repetitions: u32) -> io::Result<()> {
        if !Self::population(repetitions)?.contains(&self) {
            return Err(invalid());
        }
        let (tag, target, repetition) = match self {
            Self::AyCompile => (0, 0, 0),
            Self::Advisory => (1, 0, 0),
            Self::Strict => (2, 0, 0),
            Self::ConsumerCompile => (3, 0, 0),
            Self::Inventory { target } => (4, target, 0),
            Self::Sample { target, repetition } => (5, target, repetition),
        };
        e.number(tag);
        e.number(target.into());
        e.number(repetition.into());
        Ok(())
    }
    fn read(d: &mut Decoder<'_>, repetitions: u32) -> io::Result<Self> {
        let (tag, target, repetition) = (d.number()?, d.narrow()?, d.narrow()?);
        let node = match (tag, target, repetition) {
            (0, 0, 0) => Self::AyCompile,
            (1, 0, 0) => Self::Advisory,
            (2, 0, 0) => Self::Strict,
            (3, 0, 0) => Self::ConsumerCompile,
            (4, target, 0) => Self::Inventory { target },
            (5, target, repetition) => Self::Sample { target, repetition },
            _ => return Err(invalid()),
        };
        node.write(&mut Encoder::new(0), repetitions)?;
        Ok(node)
    }
    pub fn is_compile(self) -> bool {
        matches!(self, Self::AyCompile | Self::ConsumerCompile)
    }
    pub fn is_verification(self) -> bool {
        matches!(self, Self::Advisory | Self::Strict)
    }
}
fn flag(d: &mut Decoder<'_>) -> io::Result<bool> {
    match d.number()? {
        0 => Ok(false),
        1 => Ok(true),
        _ => Err(invalid()),
    }
}
fn text(e: &mut Encoder, value: &str, bound: usize) -> io::Result<()> {
    if value.is_empty() || value.len() > bound || value.contains('\0') {
        return Err(invalid());
    }
    e.bytes(value.as_bytes())
}
fn optional_text(e: &mut Encoder, value: &Option<String>) -> io::Result<()> {
    e.number(u64::from(value.is_some()));
    if let Some(value) = value {
        text(e, value, 4096)?;
    }
    Ok(())
}
fn read_text(d: &mut Decoder<'_>) -> io::Result<Option<String>> {
    if flag(d)? { Ok(Some(d.text()?)) } else { Ok(None) }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ready {
    pub binding: Binding,
    pub original_root: Identity,
    pub native_manifest: FileIdentity,
    pub reserved_domain: u32,
    pub dispatch_ceiling: u32,
    pub memory_bytes: u64,
    pub repetitions: u32,
}
impl Ready {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        Node::population(self.repetitions)?;
        if self.original_root.pid <= 1
            || self.original_root.birth == 0
            || self.native_manifest.inode == 0
            || self.reserved_domain == 0
            || self.reserved_domain > crate::workload::host::MAX_CPU_SET as u32
            || self.dispatch_ceiling == 0
            || self.dispatch_ceiling > 7
            || self.dispatch_ceiling > self.reserved_domain
            || self.memory_bytes == 0
        {
            return Err(invalid());
        }
        let mut e = Encoder::new(61);
        e.number(1);
        self.binding.write(&mut e)?;
        e.number(self.original_root.pid.into());
        e.number(self.original_root.birth);
        e.number(match self.original_root.birth_kind {
            BirthKind::MacosWallMicroseconds => 0,
            BirthKind::LinuxStartTicks => 1,
        });
        e.number(self.native_manifest.device);
        e.number(self.native_manifest.inode);
        for value in [self.reserved_domain, self.dispatch_ceiling] {
            e.number(value.into());
        }
        e.number(self.memory_bytes);
        e.number(self.repetitions.into());
        e.finish()
    }
    pub fn decode(bytes: &[u8], digest: [u8; 32]) -> io::Result<Self> {
        let mut d = header(bytes, 61)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let value = Self {
            binding: Binding::read(&mut d)?,
            original_root: Identity {
                pid: d.narrow()?,
                birth: d.number()?,
                birth_kind: match d.number()? {
                    0 => BirthKind::MacosWallMicroseconds,
                    1 => BirthKind::LinuxStartTicks,
                    _ => return Err(invalid()),
                },
            },
            native_manifest: FileIdentity { device: d.number()?, inode: d.number()? },
            reserved_domain: d.narrow()?,
            dispatch_ceiling: d.narrow()?,
            memory_bytes: d.number()?,
            repetitions: d.narrow()?,
        };
        d.done()?;
        value.encode()?;
        if value.binding.invocation_sha256 != digest {
            return Err(invalid());
        }
        Ok(value)
    }
}

/// Actual selected original unit facts, separate from node/verification IDs.
/// The live BuildRunner command/input owner is required independently.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CompileUnit {
    pub index: u64,
    pub unit_hash: String,
    pub package: String,
    pub target: String,
    pub source: Vec<u8>,
}
impl CompileUnit {
    fn write(&self, e: &mut Encoder) -> io::Result<()> {
        e.number(self.index);
        text(e, &self.unit_hash, 128)?;
        text(e, &self.package, 4096)?;
        text(e, &self.target, 4096)?;
        if self.source.len() > 4096
            || self.source.first() != Some(&b'/')
            || self.source.contains(&0)
        {
            return Err(invalid());
        }
        e.bytes(&self.source)
    }
    fn read(d: &mut Decoder<'_>) -> io::Result<Self> {
        Ok(Self {
            index: d.number()?,
            unit_hash: d.text()?,
            package: d.text()?,
            target: d.text()?,
            source: d.bytes()?,
        })
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Registered {
    pub binding: Binding,
    pub node: Node,
    pub original_compile_unit: Option<CompileUnit>,
}
impl Registered {
    pub fn encode(&self, repetitions: u32) -> io::Result<Vec<u8>> {
        if self.original_compile_unit.is_some() && !self.node.is_verification() {
            return Err(invalid());
        }
        let mut e = Encoder::new(62);
        e.number(1);
        self.binding.write(&mut e)?;
        self.node.write(&mut e, repetitions)?;
        e.number(u64::from(self.original_compile_unit.is_some()));
        if let Some(unit) = &self.original_compile_unit {
            unit.write(&mut e)?;
        }
        e.finish()
    }
    pub fn decode(bytes: &[u8], expected: &Binding, repetitions: u32) -> io::Result<Self> {
        let mut d = header(bytes, 62)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let value = Self {
            binding: Binding::read(&mut d)?,
            node: Node::read(&mut d, repetitions)?,
            original_compile_unit: if flag(&mut d)? {
                Some(CompileUnit::read(&mut d)?)
            } else {
                None
            },
        };
        d.done()?;
        value.binding.check(expected)?;
        value.encode(repetitions)?;
        Ok(value)
    }
}

/// Actual selected output observation, never a serialized executable owner.
/// Original UnitOutput/Layout and the host registration/phase are independent.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Artifact {
    pub binding: Binding,
    pub target: u32,
    pub executable: crate::MetadataFile,
}
impl Artifact {
    pub fn encode(&self, original_output_root: &[u8]) -> io::Result<Vec<u8>> {
        if self.target >= 2 {
            return Err(invalid());
        }
        self.executable.validate(original_output_root)?;
        let mut e = Encoder::new(62);
        e.number(2);
        self.binding.write(&mut e)?;
        e.number(self.target.into());
        self.executable.encode(&mut e)?;
        e.finish()
    }
    pub fn decode(
        bytes: &[u8],
        binding: &Binding,
        original_output_root: &[u8],
    ) -> io::Result<Self> {
        let mut d = header(bytes, 62)?;
        if d.number()? != 2 {
            return Err(invalid());
        }
        let value = Self {
            binding: Binding::read(&mut d)?,
            target: d.narrow()?,
            executable: crate::MetadataFile::decode(&mut d)?,
        };
        d.done()?;
        value.binding.check(binding)?;
        value.encode(original_output_root)?;
        Ok(value)
    }
}

/// Root formatting and native primary-process reports are never raw member
/// output. A reader must keep both diagnostic scopes out of proof parsing.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OutputScope {
    Diagnostics,
    CompilerReport,
    NativeAction,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Chunk {
    pub binding: Binding,
    pub node: Node,
    pub scope: OutputScope,
    pub stream: Stream,
    pub offset: u64,
    pub bytes: Vec<u8>,
}
impl Chunk {
    pub fn encode(&self, repetitions: u32) -> io::Result<Vec<u8>> {
        if self.bytes.is_empty()
            || self.bytes.len() > MAX_CHUNK_BYTES
            || self.offset.checked_add(self.bytes.len() as u64).is_none_or(|n| n > MAX_STREAM_BYTES)
            || (self.scope == OutputScope::NativeAction) == self.node.is_compile()
            || (self.scope == OutputScope::CompilerReport && self.stream != Stream::Stdout)
        {
            return Err(invalid());
        }
        let mut e = Encoder::new(63);
        e.number(1);
        self.binding.write(&mut e)?;
        self.node.write(&mut e, repetitions)?;
        e.number(match self.scope {
            OutputScope::Diagnostics => 0,
            OutputScope::CompilerReport => 1,
            OutputScope::NativeAction => 2,
        });
        e.number(match self.stream {
            Stream::Stdout => 0,
            Stream::Stderr => 1,
        });
        e.number(self.offset);
        e.frame_bytes(&self.bytes)?;
        e.finish()
    }
    pub fn decode(bytes: &[u8], expected: &Binding, repetitions: u32) -> io::Result<Self> {
        let mut d = header(bytes, 63)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let value = Self {
            binding: Binding::read(&mut d)?,
            node: Node::read(&mut d, repetitions)?,
            scope: match d.number()? {
                0 => OutputScope::Diagnostics,
                1 => OutputScope::CompilerReport,
                2 => OutputScope::NativeAction,
                _ => return Err(invalid()),
            },
            stream: match d.number()? {
                0 => Stream::Stdout,
                1 => Stream::Stderr,
                _ => return Err(invalid()),
            },
            offset: d.number()?,
            bytes: d.frame_bytes()?,
        };
        d.done()?;
        value.binding.check(expected)?;
        value.encode(repetitions)?;
        Ok(value)
    }
}

/// Logical diagnostic-writer closure, distinct from a native target pipe EOF.
/// Compilation can retire before later verification diagnostics finish; a
/// compile checkpoint may not invent this final stream length or closure.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DiagnosticEnd {
    pub binding: Binding,
    pub node: Node,
    pub scope: OutputScope,
    pub stream: Stream,
    pub length: u64,
    pub writer_closed: bool,
    pub truncated: bool,
}
impl DiagnosticEnd {
    pub fn encode(&self, repetitions: u32) -> io::Result<Vec<u8>> {
        if !self.node.is_compile()
            || self.scope == OutputScope::NativeAction
            || self.length > MAX_STREAM_BYTES
            || (self.scope == OutputScope::CompilerReport && self.stream != Stream::Stdout)
        {
            return Err(invalid());
        }
        let mut e = Encoder::new(63);
        e.number(2);
        self.binding.write(&mut e)?;
        self.node.write(&mut e, repetitions)?;
        e.number(match self.scope {
            OutputScope::Diagnostics => 0,
            OutputScope::CompilerReport => 1,
            OutputScope::NativeAction => return Err(invalid()),
        });
        e.number(match self.stream {
            Stream::Stdout => 0,
            Stream::Stderr => 1,
        });
        e.number(self.length);
        e.number(u64::from(self.writer_closed));
        e.number(u64::from(self.truncated));
        e.finish()
    }
    pub fn decode(bytes: &[u8], binding: &Binding, repetitions: u32) -> io::Result<Self> {
        let mut d = header(bytes, 63)?;
        if d.number()? != 2 {
            return Err(invalid());
        }
        let value = Self {
            binding: Binding::read(&mut d)?,
            node: Node::read(&mut d, repetitions)?,
            scope: match d.number()? {
                0 => OutputScope::Diagnostics,
                1 => OutputScope::CompilerReport,
                _ => return Err(invalid()),
            },
            stream: match d.number()? {
                0 => Stream::Stdout,
                1 => Stream::Stderr,
                _ => return Err(invalid()),
            },
            length: d.number()?,
            writer_closed: flag(&mut d)?,
            truncated: flag(&mut d)?,
        };
        d.done()?;
        value.binding.check(binding)?;
        value.encode(repetitions)?;
        Ok(value)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StreamEnd {
    Unobserved,
    WriterClosed,
    Eof,
    RetiredDrain,
    ReadError,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Result {
    Compiled { succeeded: bool, local_workers_joined: bool, failure: Option<String> },
    Captured { capture: Capture, elapsed_ns: u64, input_failure: Option<String> },
    Blocked { reason: String },
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Finished {
    pub binding: Binding,
    pub node: Node,
    pub result: Result,
    pub lengths: [u64; 2],
    pub ends: [StreamEnd; 2],
    pub truncated: [bool; 2],
}
impl Finished {
    pub fn encode(&self, repetitions: u32) -> io::Result<Vec<u8>> {
        if self.lengths.iter().any(|length| *length > MAX_STREAM_BYTES)
            || self.ends.iter().any(|end| match end {
                StreamEnd::WriterClosed => !self.node.is_compile(),
                StreamEnd::Eof | StreamEnd::RetiredDrain => self.node.is_compile(),
                _ => false,
            })
        {
            return Err(invalid());
        }
        let mut e = Encoder::new(64);
        e.number(1);
        self.binding.write(&mut e)?;
        self.node.write(&mut e, repetitions)?;
        for length in self.lengths {
            e.number(length);
        }
        for end in self.ends {
            e.number(match end {
                StreamEnd::Unobserved => 0,
                StreamEnd::WriterClosed => 1,
                StreamEnd::Eof => 2,
                StreamEnd::RetiredDrain => 3,
                StreamEnd::ReadError => 4,
            });
        }
        for truncated in self.truncated {
            e.number(u64::from(truncated));
        }
        match &self.result {
            Result::Compiled { succeeded, local_workers_joined, failure } => {
                if !self.node.is_compile()
                    || (*succeeded && (!local_workers_joined || failure.is_some()))
                {
                    return Err(invalid());
                }
                e.number(0);
                e.number(u64::from(*succeeded));
                e.number(u64::from(*local_workers_joined));
                optional_text(&mut e, failure)?;
            }
            Result::Captured { capture, elapsed_ns, input_failure } => {
                if self.node.is_compile() {
                    return Err(invalid());
                }
                e.number(1);
                capture.write(&mut e, self.binding.root_attempt)?;
                e.number(*elapsed_ns);
                optional_text(&mut e, input_failure)?;
            }
            Result::Blocked { reason } => {
                if self.lengths != [0, 0]
                    || self.ends != [StreamEnd::Unobserved; 2]
                    || self.truncated != [false; 2]
                {
                    return Err(invalid());
                }
                e.number(2);
                text(&mut e, reason, 4096)?;
            }
        }
        e.finish()
    }
    pub fn decode(bytes: &[u8], expected: &Binding, repetitions: u32) -> io::Result<Self> {
        let mut d = header(bytes, 64)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let binding = Binding::read(&mut d)?;
        let node = Node::read(&mut d, repetitions)?;
        let lengths = [d.number()?, d.number()?];
        let mut end = || match d.number()? {
            0 => Ok(StreamEnd::Unobserved),
            1 => Ok(StreamEnd::WriterClosed),
            2 => Ok(StreamEnd::Eof),
            3 => Ok(StreamEnd::RetiredDrain),
            4 => Ok(StreamEnd::ReadError),
            _ => Err(invalid()),
        };
        let ends = [end()?, end()?];
        let truncated = [flag(&mut d)?, flag(&mut d)?];
        let result = match d.number()? {
            0 => Result::Compiled {
                succeeded: flag(&mut d)?,
                local_workers_joined: flag(&mut d)?,
                failure: read_text(&mut d)?,
            },
            1 => Result::Captured {
                capture: Capture::read(&mut d)?,
                elapsed_ns: d.number()?,
                input_failure: read_text(&mut d)?,
            },
            2 => Result::Blocked { reason: d.text()? },
            _ => return Err(invalid()),
        };
        let value = Self { binding, node, result, lengths, ends, truncated };
        d.done()?;
        value.binding.check(expected)?;
        value.encode(repetitions)?;
        Ok(value)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Checkpoint {
    pub binding: Binding,
    pub sequence: u64,
    pub node: Node,
    pub outcome_sha256: [u8; 32],
}
impl Checkpoint {
    fn write(&self, e: &mut Encoder, repetitions: u32) -> io::Result<()> {
        if self.sequence == 0
            || self.sequence > Node::population(repetitions)?.len() as u64
            || self.outcome_sha256 == [0; 32]
        {
            return Err(invalid());
        }
        self.binding.write(e)?;
        e.number(self.sequence);
        self.node.write(e, repetitions)?;
        e.0.extend(self.outcome_sha256);
        Ok(())
    }
    fn read(d: &mut Decoder<'_>, repetitions: u32) -> io::Result<Self> {
        Ok(Self {
            binding: Binding::read(d)?,
            sequence: d.number()?,
            node: Node::read(d, repetitions)?,
            outcome_sha256: d.array()?,
        })
    }
    pub fn encode(&self, repetitions: u32) -> io::Result<Vec<u8>> {
        let mut e = Encoder::new(65);
        e.number(1);
        self.write(&mut e, repetitions)?;
        e.finish()
    }
    pub fn decode(bytes: &[u8], binding: &Binding, repetitions: u32) -> io::Result<Self> {
        let mut d = header(bytes, 65)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let value = Self::read(&mut d, repetitions)?;
        d.done()?;
        value.binding.check(binding)?;
        value.encode(repetitions)?;
        Ok(value)
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Control {
    Continue(Checkpoint),
    Stop(Binding),
}
impl Control {
    pub fn encode(&self, repetitions: u32) -> io::Result<Vec<u8>> {
        let mut e = Encoder::new(66);
        e.number(1);
        match self {
            Self::Continue(value) => {
                e.number(0);
                value.write(&mut e, repetitions)?
            }
            Self::Stop(value) => {
                e.number(1);
                value.write(&mut e)?
            }
        }
        e.finish()
    }
    pub fn decode(bytes: &[u8], binding: &Binding, repetitions: u32) -> io::Result<Self> {
        let mut d = header(bytes, 66)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let value = match d.number()? {
            0 => Self::Continue(Checkpoint::read(&mut d, repetitions)?),
            1 => Self::Stop(Binding::read(&mut d)?),
            _ => return Err(invalid()),
        };
        d.done()?;
        match &value {
            Self::Continue(value) => value.binding.check(binding)?,
            Self::Stop(value) => value.check(binding)?,
        };
        value.encode(repetitions)?;
        Ok(value)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Final {
    pub binding: Binding,
    pub repetitions: u32,
    pub finished: u32,
    pub blocked: u32,
    pub inputs_unchanged: bool,
    pub snapshot: [u8; 16],
    pub members: u32,
}
impl Final {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        if self.finished.checked_add(self.blocked)
            != Some(Node::population(self.repetitions)?.len() as u32)
            || self.snapshot == [0; 16]
            || self.members > crate::workload::host::census::MAX_ENTRIES
        {
            return Err(invalid());
        }
        let mut e = Encoder::new(67);
        e.number(1);
        self.binding.write(&mut e)?;
        e.number(self.repetitions.into());
        e.number(self.finished.into());
        e.number(self.blocked.into());
        e.number(u64::from(self.inputs_unchanged));
        e.0.extend(self.snapshot);
        e.number(self.members.into());
        e.finish()
    }
    pub fn decode(bytes: &[u8], binding: &Binding) -> io::Result<Self> {
        let mut d = header(bytes, 67)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let value = Self {
            binding: Binding::read(&mut d)?,
            repetitions: d.narrow()?,
            finished: d.narrow()?,
            blocked: d.narrow()?,
            inputs_unchanged: flag(&mut d)?,
            snapshot: d.array()?,
            members: d.narrow()?,
        };
        d.done()?;
        value.binding.check(binding)?;
        value.encode()?;
        Ok(value)
    }
}

pub fn encode_census(page: &crate::workload::host::census::Page) -> io::Result<Vec<u8>> {
    let binding = Binding {
        root_attempt: page.request.root_attempt,
        invocation_sha256: page.request.invocation_sha256,
    };
    let mut e = Encoder::new(67);
    e.number(2);
    binding.write(&mut e)?;
    e.0.extend(page.request.snapshot);
    e.number(page.request.offset.into());
    e.frame_bytes(&crate::workload::host::census::Reply::Page(page.clone()).encode()?)?;
    e.finish()
}
pub fn decode_census(
    bytes: &[u8],
    binding: &Binding,
) -> io::Result<crate::workload::host::census::Page> {
    use crate::workload::host::census;
    let mut d = header(bytes, 67)?;
    if d.number()? != 2 {
        return Err(invalid());
    }
    Binding::read(&mut d)?.check(binding)?;
    let request = census::Request {
        root_attempt: binding.root_attempt,
        invocation_sha256: binding.invocation_sha256,
        snapshot: d.array()?,
        offset: d.narrow()?,
    };
    let frame = d.frame_bytes()?;
    d.done()?;
    match census::Reply::decode(&frame, &request)? {
        census::Reply::Page(page) => Ok(page),
        _ => Err(invalid()),
    }
}

#[cfg(test)]
mod tests;
