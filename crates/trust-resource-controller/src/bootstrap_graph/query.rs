// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Closed pre-configuration SDK queries under an original Bootstrap graph.
//! Codecs carry equality data, never a child, original GNU borrower or retirement.

use std::collections::BTreeSet;
use std::io;

use super::{GnuIdentity, Key, absolute};
use crate::wire::{Decoder, Encoder, header, invalid};
use crate::{MetadataCompletion, MetadataFile, MetadataPrepared, Started, Status, StatusFrame};

pub const PURPOSE: &str = "native-bootstrap-sdk-query-v1";
pub const PREPARED_POLICY: &str = "bootstrap-sdk-query-v1";
pub const PREPARED_SCOPE: &str = "native-no-fork-target-v1";
pub const MAX_QUERY_NS: u64 = 60_000_000_000;
pub const MAX_OUTPUT: u64 = 64 * 1024;
pub const MAX_CHUNK: usize = 4096;
const DOMAIN: &[u8] = b"trust-bootstrap-sdk-query-v1\0";

#[derive(Clone, PartialEq, Eq)]
pub struct OperationKey {
    pub graph: Key,
    pub sequence: u64,
    pub operation: [u8; 16],
}
impl OperationKey {
    pub fn validate(&self) -> io::Result<()> {
        self.graph.validate()?;
        if self.sequence == 0
            || self.operation == [0; 16]
            || self.operation == self.graph.graph
            || self.operation == self.graph.query.call_attempt
            || self.operation == self.graph.query.binding.root_attempt
        {
            return Err(invalid());
        }
        Ok(())
    }
    pub(super) fn write(&self, e: &mut Encoder) -> io::Result<()> {
        self.validate()?;
        self.graph.write(e)?;
        e.number(self.sequence);
        e.0.extend(self.operation);
        Ok(())
    }
    pub(super) fn read(d: &mut Decoder<'_>) -> io::Result<Self> {
        let value = Self { graph: Key::read(d)?, sequence: d.number()?, operation: d.array()? };
        value.validate()?;
        Ok(value)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Tool {
    Compiler,
    Targo,
    Formatter,
    DependencyPlanner,
}

/// Exact Bootstrap forms, independently closed from resolver/metadata roles.
/// In particular a print flag does not admit source inputs, argfiles, custom
/// targets/backends, output paths, git or arbitrary configured stage0 tools.
pub fn classify(tool: Tool, arguments: &[Vec<u8>]) -> io::Result<()> {
    let equal = |expected: &[&[u8]]| {
        arguments.len() == expected.len() && arguments.iter().zip(expected).all(|(a, b)| a == b)
    };
    let accepted = match tool {
        Tool::Compiler => {
            equal(&[b"-vV"])
                || equal(&[b"--version"])
                || equal(&[b"--version", b"--verbose"])
                || equal(&[b"--print=sysroot"])
                || equal(&[b"--print", b"sysroot"])
                || equal(&[b"--print", b"target-libdir"])
                || equal(&[b"--print", b"sysroot", b"--print", b"target-libdir"])
        }
        Tool::Targo => equal(&[b"--version"]) || equal(&[b"--unverified", b"--version"]),
        Tool::Formatter => equal(&[b"--version"]),
        Tool::DependencyPlanner => {
            arguments.len() == 7
                && arguments[0] == b"-I"
                && arguments[1] == b"-S"
                && arguments[2] == b"-B"
                && absolute(&arguments[3])
                && arguments[3].ends_with(b"/scripts/bootstrap_dependency_closure.py")
                && arguments[4] == b"plan"
                && arguments[5] == b"--repo-root"
                && absolute(&arguments[6])
        }
    };
    if accepted {
        Ok(())
    } else {
        Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "outside closed Bootstrap SDK query profile",
        ))
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct Request {
    pub key: OperationKey,
    pub gnu: GnuIdentity,
    pub tool: Tool,
    pub sdk_root: Vec<u8>,
    pub program: MetadataFile,
    pub cwd: Vec<u8>,
    pub arguments: Vec<Vec<u8>>,
    pub environment: Vec<(Vec<u8>, Vec<u8>)>,
    pub timeout_ns: u64,
}
impl Request {
    pub fn validate(&self) -> io::Result<()> {
        self.key.validate()?;
        self.gnu.write(&mut Encoder::new(0))?;
        classify(self.tool, &self.arguments)?;
        self.program.validate(&self.sdk_root)?;
        if !absolute(&self.sdk_root)
            || !absolute(&self.cwd)
            || !matches!(self.timeout_ns, 1..=MAX_QUERY_NS)
        {
            return Err(invalid());
        }
        let mut compiler = self.sdk_root.clone();
        compiler.extend(b"/bin/trustc");
        let mut targo = self.sdk_root.clone();
        targo.extend(b"/bin/targo");
        let mut formatter = self.sdk_root.clone();
        formatter.extend(b"/bin/trustfmt");
        let expected = match self.tool {
            Tool::Compiler => &compiler,
            Tool::Targo => &targo,
            Tool::Formatter => &formatter,
            Tool::DependencyPlanner => {
                let mut python = self.sdk_root.clone();
                python.extend(b"/bin/python3.14");
                return self.validate_planner(&python);
            }
        };
        if &self.program.path != expected
            || self.environment.len() != 6
            || self.environment.iter().map(|(key, _)| key).collect::<BTreeSet<_>>().len() != 6
            || self.environment.iter().any(|(key, value)| match key.as_slice() {
                b"LANG" | b"LC_ALL" => value != b"C",
                b"CARGO" => value != &targo,
                b"RUSTC" => value != &compiler,
                b"CARGO_HOME" => !absolute(value),
                b"CARGO_CACHE_RUSTC_INFO" => value != b"0",
                _ => true,
            })
        {
            return Err(invalid());
        }
        Ok(())
    }
    fn validate_planner(&self, python: &[u8]) -> io::Result<()> {
        let mut script = self.cwd.clone();
        script.extend(b"/scripts/bootstrap_dependency_closure.py");
        if self.program.path != python
            || self.arguments[3] != script
            || self.arguments[6] != self.cwd
            || self.environment.len() != 3
            || self.environment.iter().map(|(key, _)| key).collect::<BTreeSet<_>>().len() != 3
            || self.environment.iter().any(|(key, value)| match key.as_slice() {
                b"LANG" | b"LC_ALL" => value != b"C",
                b"CARGO_HOME" => !absolute(value),
                _ => true,
            })
        {
            return Err(invalid());
        }
        Ok(())
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        let mut e = Encoder::new(75);
        e.number(0);
        self.key.write(&mut e)?;
        self.gnu.write(&mut e)?;
        e.number(match self.tool {
            Tool::Compiler => 0,
            Tool::Targo => 1,
            Tool::Formatter => 2,
            Tool::DependencyPlanner => 3,
        });
        e.bytes(&self.sdk_root)?;
        self.program.encode(&mut e)?;
        e.bytes(&self.cwd)?;
        e.number(self.arguments.len() as u64);
        for value in &self.arguments {
            e.bytes(value)?;
        }
        e.number(self.environment.len() as u64);
        for (key, value) in &self.environment {
            e.bytes(key)?;
            e.bytes(value)?;
        }
        e.number(self.timeout_ns);
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 75)?;
        if d.number()? != 0 {
            return Err(invalid());
        }
        let key = OperationKey::read(&mut d)?;
        let gnu = GnuIdentity::read(&mut d)?;
        let tool = match d.number()? {
            0 => Tool::Compiler,
            1 => Tool::Targo,
            2 => Tool::Formatter,
            3 => Tool::DependencyPlanner,
            _ => return Err(invalid()),
        };
        let sdk_root = d.bytes()?;
        let program = MetadataFile::decode(&mut d)?;
        let cwd = d.bytes()?;
        let mut arguments = Vec::new();
        for _ in 0..d.count(7)? {
            arguments.push(d.bytes()?);
        }
        let mut environment = Vec::new();
        for _ in 0..d.count(6)? {
            environment.push((d.bytes()?, d.bytes()?));
        }
        let value = Self {
            key,
            gnu,
            tool,
            sdk_root,
            program,
            cwd,
            arguments,
            environment,
            timeout_ns: d.number()?,
        };
        d.done()?;
        value.validate()?;
        Ok(value)
    }
    pub fn hello(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        self.key.graph.hello(PURPOSE)
    }
    pub fn binding_preimage(&self) -> io::Result<Vec<u8>> {
        let frame = self.encode()?;
        let mut bytes = Vec::with_capacity(DOMAIN.len() + 8 + frame.len());
        bytes.extend(DOMAIN);
        bytes.extend((frame.len() as u64).to_be_bytes());
        bytes.extend(frame);
        Ok(bytes)
    }
    pub fn validate_prepared(&self, prepared: &MetadataPrepared) -> io::Result<()> {
        self.validate()?;
        prepared.encode()?;
        if prepared.root_attempt != self.key.graph.query.binding.root_attempt
            || prepared.member_attempt != self.key.operation
            || prepared.root != self.sdk_root
            || prepared.executable != self.program
            || prepared.policy != PREPARED_POLICY
            || prepared.scope != PREPARED_SCOPE
        {
            return Err(invalid());
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Stream {
    Stdout,
    Stderr,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Event {
    Prepared(Box<MetadataPrepared>),
    Started(Started),
    Output { stream: Stream, offset: u64, bytes: Vec<u8> },
    Eof { stream: Stream, bytes: u64 },
}
fn stream_write(e: &mut Encoder, stream: Stream) {
    e.number(match stream {
        Stream::Stdout => 0,
        Stream::Stderr => 1,
    });
}
fn stream_read(d: &mut Decoder<'_>) -> io::Result<Stream> {
    match d.number()? {
        0 => Ok(Stream::Stdout),
        1 => Ok(Stream::Stderr),
        _ => Err(invalid()),
    }
}
fn write_binding(e: &mut Encoder, request: &Request, digest: [u8; 32]) -> io::Result<()> {
    request.key.write(e)?;
    e.0.extend(digest);
    Ok(())
}
fn read_binding(d: &mut Decoder<'_>, request: &Request, digest: [u8; 32]) -> io::Result<()> {
    if OperationKey::read(d)? != request.key || d.array::<32>()? != digest {
        return Err(invalid());
    }
    Ok(())
}
impl Event {
    pub fn encode(&self, request: &Request, digest: [u8; 32]) -> io::Result<Vec<u8>> {
        request.validate()?;
        let mut e = Encoder::new(76);
        e.number(0);
        write_binding(&mut e, request, digest)?;
        match self {
            Self::Prepared(prepared) => {
                request.validate_prepared(prepared)?;
                e.number(0);
                e.frame_bytes(&prepared.encode()?)?;
            }
            Self::Started(started) => {
                e.number(1);
                e.frame_bytes(
                    &StatusFrame {
                        root_attempt: request.key.graph.query.binding.root_attempt,
                        member_attempt: request.key.operation,
                        status: Status::Started(*started),
                    }
                    .encode()?,
                )?;
            }
            Self::Output { stream, offset, bytes } => {
                if bytes.is_empty()
                    || bytes.len() > MAX_CHUNK
                    || offset.checked_add(bytes.len() as u64).is_none_or(|end| end > MAX_OUTPUT)
                {
                    return Err(invalid());
                }
                e.number(2);
                stream_write(&mut e, *stream);
                e.number(*offset);
                e.bytes(bytes)?;
            }
            Self::Eof { stream, bytes } => {
                if *bytes > MAX_OUTPUT {
                    return Err(invalid());
                }
                e.number(3);
                stream_write(&mut e, *stream);
                e.number(*bytes);
            }
        }
        e.finish()
    }
    pub fn decode(bytes: &[u8], request: &Request, digest: [u8; 32]) -> io::Result<Self> {
        let mut d = header(bytes, 76)?;
        if d.number()? != 0 {
            return Err(invalid());
        }
        read_binding(&mut d, request, digest)?;
        let value = match d.number()? {
            0 => Self::Prepared(Box::new(MetadataPrepared::decode(
                &d.frame_bytes()?,
                request.key.graph.query.binding.root_attempt,
                request.key.operation,
            )?)),
            1 => match StatusFrame::decode(
                &d.frame_bytes()?,
                request.key.graph.query.binding.root_attempt,
                request.key.operation,
            )?
            .status
            {
                Status::Started(started) => Self::Started(started),
                _ => return Err(invalid()),
            },
            2 => Self::Output {
                stream: stream_read(&mut d)?,
                offset: d.number()?,
                bytes: d.bytes()?,
            },
            3 => Self::Eof { stream: stream_read(&mut d)?, bytes: d.number()? },
            _ => return Err(invalid()),
        };
        d.done()?;
        value.encode(request, digest)?;
        Ok(value)
    }
}

/// Data emitted only by the actual Host operation after same native target
/// retirement and journal settlement. Decoding alone creates no completed owner.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Terminal {
    Completed { completion: MetadataCompletion, observation: crate::accounting::Observation },
    Refused { reason: String },
    Unknown { reason: String },
}
impl Terminal {
    pub fn encode(&self, request: &Request, digest: [u8; 32]) -> io::Result<Vec<u8>> {
        request.validate()?;
        let mut e = Encoder::new(77);
        e.number(0);
        write_binding(&mut e, request, digest)?;
        request.gnu.write(&mut e)?;
        match self {
            Self::Completed { completion, observation } => {
                let bytes = completion.encode()?;
                MetadataCompletion::decode(
                    &bytes,
                    request.key.graph.query.binding.root_attempt,
                    request.key.operation,
                )?;
                e.number(0);
                e.frame_bytes(&bytes)?;
                e.frame_bytes(&observation.encode()?)?;
            }
            Self::Refused { reason } | Self::Unknown { reason } => {
                if reason.is_empty() || reason.chars().any(char::is_control) {
                    return Err(invalid());
                }
                e.number(if matches!(self, Self::Refused { .. }) { 1 } else { 2 });
                e.bytes(reason.as_bytes())?;
            }
        }
        e.finish()
    }
    pub fn decode(bytes: &[u8], request: &Request, digest: [u8; 32]) -> io::Result<Self> {
        let mut d = header(bytes, 77)?;
        if d.number()? != 0 {
            return Err(invalid());
        }
        read_binding(&mut d, request, digest)?;
        if GnuIdentity::read(&mut d)? != request.gnu {
            return Err(invalid());
        }
        let value = match d.number()? {
            0 => Self::Completed {
                completion: MetadataCompletion::decode(
                    &d.frame_bytes()?,
                    request.key.graph.query.binding.root_attempt,
                    request.key.operation,
                )?,
                observation: crate::accounting::Observation::decode(&d.frame_bytes()?)?,
            },
            1 => Self::Refused { reason: d.text()? },
            2 => Self::Unknown { reason: d.text()? },
            _ => return Err(invalid()),
        };
        d.done()?;
        value.encode(request, digest)?;
        Ok(value)
    }
}

#[cfg(test)]
pub(crate) mod tests;
