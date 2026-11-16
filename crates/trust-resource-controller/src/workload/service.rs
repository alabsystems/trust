//! Bounded service observations and continuations. These bytes create no
//! native root, SDK, output owner, execution grant or positive retirement.
use std::io;

use super::{WORKLOAD_MAX_CHECKPOINTS, WorkloadInvocation};
use crate::wire::{Decoder, Encoder, header, invalid};
use crate::{BirthKind, FileIdentity, Identity, MetadataFile};

pub mod checkpoint;
pub mod finish;

pub const MAX_CHUNK_BYTES: usize = 64 * 1024;
pub const MAX_STREAM_BYTES: u64 = 64 * 1024 * 1024;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Binding {
    pub root_attempt: [u8; 16],
    pub invocation_sha256: [u8; 32],
}
impl Binding {
    pub(super) fn write(&self, e: &mut Encoder) -> io::Result<()> {
        if self.root_attempt == [0; 16] {
            return Err(invalid());
        }
        e.0.extend(self.root_attempt);
        e.0.extend(self.invocation_sha256);
        Ok(())
    }
    pub(super) fn read(d: &mut Decoder<'_>) -> io::Result<Self> {
        let value = Self { root_attempt: d.array()?, invocation_sha256: d.array()? };
        value.write(&mut Encoder::new(0))?;
        Ok(value)
    }
    pub fn check(&self, expected: &Self) -> io::Result<()> {
        if self == expected { Ok(()) } else { Err(invalid()) }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ready {
    pub binding: Binding,
    pub original_root: Identity,
    pub native_manifest: FileIdentity,
    pub reserved_domain: u32,
    /// Initial closed dispatch ceiling; actual normal BuildConfig jobs are
    /// recorded at the compilation checkpoint, separately from reserved N.
    pub dispatch_ceiling: u32,
    pub memory_bytes: u64,
}
impl Ready {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        if self.original_root.pid <= 1
            || self.original_root.birth == 0
            || self.native_manifest.inode == 0
            || self.reserved_domain == 0
            || self.reserved_domain > super::host::MAX_CPU_SET as u32
            || self.dispatch_ceiling == 0
            || self.dispatch_ceiling > 7
            || self.dispatch_ceiling > self.reserved_domain
            || self.memory_bytes == 0
        {
            return Err(invalid());
        }
        let mut e = Encoder::new(41);
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
        e.number(self.reserved_domain.into());
        e.number(self.dispatch_ceiling.into());
        e.number(self.memory_bytes);
        e.finish()
    }
    pub fn decode(bytes: &[u8], invocation_sha256: [u8; 32]) -> io::Result<Self> {
        let mut d = header(bytes, 41)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let binding = Binding::read(&mut d)?;
        let original_root = Identity {
            pid: d.narrow()?,
            birth: d.number()?,
            birth_kind: match d.number()? {
                0 => BirthKind::MacosWallMicroseconds,
                1 => BirthKind::LinuxStartTicks,
                _ => return Err(invalid()),
            },
        };
        let value = Self {
            binding,
            original_root,
            native_manifest: FileIdentity { device: d.number()?, inode: d.number()? },
            reserved_domain: d.narrow()?,
            dispatch_ceiling: d.narrow()?,
            memory_bytes: d.number()?,
        };
        d.done()?;
        value.encode()?;
        if value.binding.invocation_sha256 != invocation_sha256 {
            return Err(invalid());
        }
        Ok(value)
    }
}

/// Distinct initial-share observation. `funded` records only actual current
/// custody; the maximum is an original restriction, never runnable capacity.
/// Old Ready41/V1 readers reject this outer version.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InitialReady {
    pub funded: Ready,
    pub original_ceiling: u32,
    pub maximum_dispatch: u32,
}
impl InitialReady {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        if self.funded.reserved_domain != 1
            || self.funded.dispatch_ceiling != 1
            || self.original_ceiling == 0
            || self.original_ceiling > super::host::MAX_CPU_SET as u32
            || self.maximum_dispatch == 0
            || self.maximum_dispatch > 7
            || self.maximum_dispatch > self.original_ceiling
        {
            return Err(invalid());
        }
        let current = self.funded.encode()?;
        let mut e = Encoder::new(41);
        e.number(2);
        e.frame_bytes(&current)?;
        e.number(self.original_ceiling.into());
        e.number(self.maximum_dispatch.into());
        e.finish()
    }
    pub fn decode(bytes: &[u8], invocation_sha256: [u8; 32]) -> io::Result<Self> {
        let mut d = header(bytes, 41)?;
        if d.number()? != 2 {
            return Err(invalid());
        }
        let value = Self {
            funded: Ready::decode(&d.frame_bytes()?, invocation_sha256)?,
            original_ceiling: d.narrow()?,
            maximum_dispatch: d.narrow()?,
        };
        d.done()?;
        value.encode()?;
        Ok(value)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Stream {
    Stdout,
    Stderr,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Chunk {
    pub binding: Binding,
    pub checkpoint: u64,
    pub stream: Stream,
    pub offset: u64,
    pub bytes: Vec<u8>,
}
impl Chunk {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        if !(1..=WORKLOAD_MAX_CHECKPOINTS).contains(&self.checkpoint)
            || self.bytes.is_empty()
            || self.bytes.len() > MAX_CHUNK_BYTES
            || self.offset.checked_add(self.bytes.len() as u64).is_none_or(|n| n > MAX_STREAM_BYTES)
        {
            return Err(invalid());
        }
        let mut e = Encoder::new(44);
        e.number(1);
        self.binding.write(&mut e)?;
        e.number(self.checkpoint);
        e.number(match self.stream {
            Stream::Stdout => 0,
            Stream::Stderr => 1,
        });
        e.number(self.offset);
        e.frame_bytes(&self.bytes)?;
        e.finish()
    }
    pub fn decode(bytes: &[u8], expected: &Binding) -> io::Result<Self> {
        let mut d = header(bytes, 44)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let value = Self {
            binding: Binding::read(&mut d)?,
            checkpoint: d.number()?,
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
        value.encode()?;
        Ok(value)
    }
}

/// Scope of these stream facts. A compiler diagnostic writer closure is not a
/// kernel pipe EOF or target exit, even when every original worker joined.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OutputScope {
    CompilerGraph,
    NativeAction,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OutputEnd {
    pub binding: Binding,
    pub checkpoint: u64,
    pub scope: OutputScope,
    pub lengths: [u64; 2],
    pub closed: [bool; 2],
    pub truncated: [bool; 2],
}
impl OutputEnd {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        if !(1..=WORKLOAD_MAX_CHECKPOINTS).contains(&self.checkpoint)
            || self.lengths.iter().any(|n| *n > MAX_STREAM_BYTES)
            || (self.checkpoint == 1) != (self.scope == OutputScope::CompilerGraph)
        {
            return Err(invalid());
        }
        let mut e = Encoder::new(45);
        e.number(1);
        self.binding.write(&mut e)?;
        e.number(self.checkpoint);
        e.number(match self.scope {
            OutputScope::CompilerGraph => 0,
            OutputScope::NativeAction => 1,
        });
        for n in self.lengths {
            e.number(n);
        }
        for flag in self.closed.into_iter().chain(self.truncated) {
            e.number(u64::from(flag));
        }
        e.finish()
    }
    pub fn decode(bytes: &[u8], expected: &Binding) -> io::Result<Self> {
        let mut d = header(bytes, 45)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let binding = Binding::read(&mut d)?;
        let checkpoint = d.number()?;
        let scope = match d.number()? {
            0 => OutputScope::CompilerGraph,
            1 => OutputScope::NativeAction,
            _ => return Err(invalid()),
        };
        let lengths = [d.number()?, d.number()?];
        let mut flag = || match d.number()? {
            0 => Ok(false),
            1 => Ok(true),
            _ => Err(invalid()),
        };
        let value = Self {
            binding,
            checkpoint,
            scope,
            lengths,
            closed: [flag()?, flag()?],
            truncated: [flag()?, flag()?],
        };
        d.done()?;
        value.binding.check(expected)?;
        value.encode()?;
        Ok(value)
    }
}

/// An explicit stop request is cancellation intent for the SAME original
/// graph. It is never completion, retirement or an authorization to retry.
pub struct Stop {
    pub binding: Binding,
}
impl Stop {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        let mut e = Encoder::new(47);
        e.number(1);
        self.binding.write(&mut e)?;
        e.finish()
    }
    pub fn decode(bytes: &[u8], expected: &Binding) -> io::Result<Self> {
        let mut d = header(bytes, 47)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let value = Self { binding: Binding::read(&mut d)? };
        d.done()?;
        value.binding.check(expected)?;
        Ok(value)
    }
}

/// Bounded reader state for one original checkpoint's exact raw prefixes.
/// Closure is supplied separately by the real producer; this state cannot
/// infer native EOF, Started, retirement or an outcome from successful bytes.
pub struct Output {
    binding: Binding,
    checkpoint: u64,
    bytes: [Vec<u8>; 2],
    end: Option<OutputEnd>,
    failed: bool,
}
impl Output {
    pub fn new(binding: Binding, checkpoint: u64) -> io::Result<Self> {
        if !(1..=WORKLOAD_MAX_CHECKPOINTS).contains(&checkpoint) {
            return Err(invalid());
        }
        binding.write(&mut Encoder::new(0))?;
        Ok(Self { binding, checkpoint, bytes: [Vec::new(), Vec::new()], end: None, failed: false })
    }
    pub fn append(&mut self, chunk: Chunk) -> io::Result<()> {
        let result = (|| {
            if self.failed || self.end.is_some() || chunk.checkpoint != self.checkpoint {
                return Err(invalid());
            }
            chunk.binding.check(&self.binding)?;
            chunk.encode()?;
            let bytes = &mut self.bytes[usize::from(chunk.stream == Stream::Stderr)];
            if chunk.offset != bytes.len() as u64 {
                return Err(invalid());
            }
            bytes.try_reserve(chunk.bytes.len()).map_err(io::Error::other)?;
            bytes.extend(chunk.bytes);
            Ok(())
        })();
        if result.is_err() {
            self.failed = true;
        }
        result
    }
    pub fn close(&mut self, end: OutputEnd) -> io::Result<()> {
        let result = (|| {
            if self.failed || self.end.is_some() || end.checkpoint != self.checkpoint {
                return Err(invalid());
            }
            end.binding.check(&self.binding)?;
            end.encode()?;
            if end.lengths != self.bytes.each_ref().map(|bytes| bytes.len() as u64) {
                return Err(invalid());
            }
            self.end = Some(end);
            Ok(())
        })();
        if result.is_err() {
            self.failed = true;
        }
        result
    }
    pub fn parts(&self) -> (&[u8], &[u8], Option<&OutputEnd>, bool) {
        (&self.bytes[0], &self.bytes[1], self.end.as_ref(), self.failed)
    }
    /// Consume these same observed bytes without duplicating a full native
    /// sample in memory. Moving data supplies no completion or execution owner.
    pub fn into_parts(self) -> (Vec<u8>, Vec<u8>, Option<OutputEnd>, bool) {
        let [stdout, stderr] = self.bytes;
        (stdout, stderr, self.end, self.failed)
    }
}

pub(super) fn file_write(e: &mut Encoder, file: &MetadataFile) -> io::Result<()> {
    file.encode(e)
}
pub(super) fn file_read(
    d: &mut Decoder<'_>,
    invocation: &WorkloadInvocation,
) -> io::Result<MetadataFile> {
    let value = MetadataFile::decode(d)?;
    value.validate(&invocation.output_root)?;
    Ok(value)
}

#[cfg(test)]
mod tests;
