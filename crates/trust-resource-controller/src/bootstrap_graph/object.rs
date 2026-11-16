// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! One explicit no-core object-producing operation. This DATA never creates
//! source/output custody, an SDK, GNU loan, native retirement or graph closure.
use std::io;

use super::query::OperationKey;
use super::{GnuIdentity, absolute};
use crate::wire::{Decoder, Encoder, header, invalid};
use crate::{
    FileIdentity, MetadataCompletion, MetadataFile, MetadataPrepared, Outcome, Started, Status,
    StatusFrame,
};

pub const PURPOSE: &str = "native-bootstrap-object-compile-v1";
pub const PREPARED_POLICY: &str = "bootstrap-object-compile-v1";
pub const PREPARED_SCOPE: &str = "native-no-fork-target-v1";
pub const SOURCE_MARKER: u8 = 0x78;
pub const MAX_COMPILE_NS: u64 = 3_600_000_000_000;
pub const MAX_OUTPUT: u64 = 64 * 1024;
pub const MAX_CHUNK: usize = 4096;
pub const MAX_OBJECT_BYTES: u64 = 256 * 1024 * 1024;
pub const SOURCE_RELATIVE_PATH: &[u8] = b"src/bootstrap/native_object.rs";
pub const SOURCE_BYTES: &[u8] = br#"#![feature(no_core, lang_items, auto_traits)]
#![no_core]
#![allow(internal_features)]
#[lang = "pointee_sized"] pub trait PointeeSized {}
#[lang = "meta_sized"] pub trait MetaSized: PointeeSized {}
#[lang = "sized"] pub trait Sized: MetaSized {}
#[lang = "copy"] pub trait Copy {}
#[lang = "freeze"] pub auto trait Freeze {}
impl Copy for u64 {}
#[unsafe(no_mangle)]
pub extern "C" fn trust_bootstrap_native_object() -> u64 { 42u64 }
"#;
pub const SOURCE_SHA256: [u8; 32] = [
    0x06, 0x23, 0x43, 0x25, 0xec, 0x16, 0x88, 0x0e, 0x40, 0x1e, 0x42, 0x0c, 0xc3, 0x85, 0xb3, 0x78,
    0x27, 0x41, 0xfb, 0xa1, 0xee, 0x24, 0xb0, 0x53, 0x1a, 0x6e, 0xd3, 0x4a, 0xf1, 0xa8, 0xcc, 0x20,
];
const DOMAIN: &[u8] = b"trust-bootstrap-object-compile-v1\0";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SourceKind {
    NativeLeafV1,
}

#[derive(Clone, PartialEq, Eq)]
pub struct Request {
    pub key: OperationKey,
    pub gnu: GnuIdentity,
    pub sdk_root: Vec<u8>,
    pub driver: MetadataFile,
    pub compiler: MetadataFile,
    pub source_kind: SourceKind,
    pub source_root: Vec<u8>,
    pub source_directory: FileIdentity,
    pub source: MetadataFile,
    pub output_root: Vec<u8>,
    pub output_directory: FileIdentity,
    pub output_lock: FileIdentity,
    pub destination: Vec<u8>,
    pub timeout_ns: u64,
}
fn join(root: &[u8], tail: &[u8]) -> Vec<u8> {
    let mut out = root.to_vec();
    out.push(b'/');
    out.extend(tail);
    out
}
pub fn destination(value: &[u8]) -> bool {
    value.len() > 2
        && value.len() <= 128
        && value.ends_with(b".o")
        && value[..value.len() - 2]
            .iter()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b'-'))
}
impl Request {
    pub fn validate(&self) -> io::Result<()> {
        self.key.validate()?;
        self.gnu.write(&mut Encoder::new(0))?;
        self.driver.validate(&self.sdk_root)?;
        self.compiler.validate(&self.sdk_root)?;
        self.source.validate(&self.source_root)?;
        if !absolute(&self.sdk_root)
            || !absolute(&self.source_root)
            || !absolute(&self.output_root)
            || self.source_root == self.output_root
            || self.driver.path != join(&self.sdk_root, b"bin/tippy-driver")
            || self.compiler.path != join(&self.sdk_root, b"bin/trustc")
            || self.source.path != join(&self.source_root, SOURCE_RELATIVE_PATH)
            || self.source.bytes != SOURCE_BYTES.len() as u64
            || self.source.sha256 != SOURCE_SHA256
            || !destination(&self.destination)
            || !matches!(self.timeout_ns, 1..=MAX_COMPILE_NS)
            || [self.source_directory, self.output_directory, self.output_lock]
                .iter()
                .any(|file| file.inode == 0)
            || self.output_directory == self.output_lock
            || self.source_directory == self.output_directory
        {
            return Err(invalid());
        }
        Ok(())
    }
    pub fn output_path(&self) -> Vec<u8> {
        join(&self.output_root, &self.destination)
    }
    pub fn staging_valid(&self, staging: &[u8]) -> bool {
        let op: String = self.key.operation.iter().map(|byte| format!("{byte:02x}")).collect();
        let prefix = format!(".trust-object-{op}-");
        staging.strip_prefix(prefix.as_bytes()).is_some_and(|rest| {
            rest.len() == 34
                && rest.ends_with(b".o")
                && rest[..32].iter().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(b))
        })
    }
    /// The exact measured evidence-inert argv. No argfile, backend, target,
    /// external crate, lint configuration or caller flag channel is accepted.
    pub fn arguments(&self, staging: &[u8]) -> io::Result<Vec<Vec<u8>>> {
        self.validate()?;
        if !self.staging_valid(staging) {
            return Err(invalid());
        }
        Ok(vec![
            b"--cap-lints=allow".to_vec(),
            b"--crate-name".to_vec(),
            b"trust_bootstrap_native_object".to_vec(),
            b"--crate-type=rlib".to_vec(),
            b"--emit=obj".to_vec(),
            b"-o".to_vec(),
            join(&self.output_root, staging),
            self.source.path.clone(),
        ])
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        let mut e = Encoder::new(78);
        e.number(1);
        self.key.write(&mut e)?;
        self.gnu.write(&mut e)?;
        e.bytes(&self.sdk_root)?;
        self.driver.encode(&mut e)?;
        self.compiler.encode(&mut e)?;
        e.number(0);
        e.bytes(&self.source_root)?;
        super::write_file(&mut e, self.source_directory)?;
        self.source.encode(&mut e)?;
        e.bytes(&self.output_root)?;
        super::write_file(&mut e, self.output_directory)?;
        super::write_file(&mut e, self.output_lock)?;
        e.bytes(&self.destination)?;
        e.number(self.timeout_ns);
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 78)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let key = OperationKey::read(&mut d)?;
        let gnu = GnuIdentity::read(&mut d)?;
        let sdk_root = d.bytes()?;
        let driver = MetadataFile::decode(&mut d)?;
        let compiler = MetadataFile::decode(&mut d)?;
        let source_kind = match d.number()? {
            0 => SourceKind::NativeLeafV1,
            _ => return Err(invalid()),
        };
        let source_root = d.bytes()?;
        let source_directory = super::read_file(&mut d)?;
        let source = MetadataFile::decode(&mut d)?;
        let output_root = d.bytes()?;
        let output_directory = super::read_file(&mut d)?;
        let output_lock = super::read_file(&mut d)?;
        let destination = d.bytes()?;
        let timeout_ns = d.number()?;
        d.done()?;
        let value = Self {
            key,
            gnu,
            sdk_root,
            driver,
            compiler,
            source_kind,
            source_root,
            source_directory,
            source,
            output_root,
            output_directory,
            output_lock,
            destination,
            timeout_ns,
        };
        value.validate()?;
        Ok(value)
    }
    pub fn hello(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        self.key.graph.hello(PURPOSE)
    }
    pub fn binding_preimage(&self) -> io::Result<Vec<u8>> {
        let frame = self.encode()?;
        let mut bytes = Vec::from(DOMAIN);
        bytes.extend((frame.len() as u64).to_be_bytes());
        bytes.extend(frame);
        Ok(bytes)
    }
    pub fn validate_prepared(&self, prepared: &Prepared) -> io::Result<()> {
        self.validate()?;
        prepared.inventory.encode()?;
        let inventory = &prepared.inventory;
        if inventory.root_attempt != self.key.graph.query.binding.root_attempt
            || inventory.member_attempt != self.key.operation
            || inventory.root != self.sdk_root
            || inventory.executable != self.driver
            || inventory.policy != PREPARED_POLICY
            || inventory.scope != PREPARED_SCOPE
            || !inventory.runtime.iter().any(|file| file == &self.compiler)
            || !self.staging_valid(&prepared.staging)
        {
            return Err(invalid());
        }
        Ok(())
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Prepared {
    pub inventory: MetadataPrepared,
    pub staging: Vec<u8>,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Stream {
    Stdout,
    Stderr,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Event {
    Prepared(Box<Prepared>),
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
        let mut e = Encoder::new(79);
        e.number(1);
        write_binding(&mut e, request, digest)?;
        match self {
            Self::Prepared(prepared) => {
                request.validate_prepared(prepared)?;
                e.number(0);
                e.frame_bytes(&prepared.inventory.encode()?)?;
                e.bytes(&prepared.staging)?;
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
        let mut d = header(bytes, 79)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        read_binding(&mut d, request, digest)?;
        let value = match d.number()? {
            0 => Self::Prepared(Box::new(Prepared {
                inventory: MetadataPrepared::decode(
                    &d.frame_bytes()?,
                    request.key.graph.query.binding.root_attempt,
                    request.key.operation,
                )?,
                staging: d.bytes()?,
            })),
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
    Completed {
        completion: Box<MetadataCompletion>,
        observation: crate::accounting::Observation,
        artifact: Option<MetadataFile>,
    },
    Refused {
        reason: String,
    },
    Unknown {
        reason: String,
    },
}
impl Terminal {
    pub fn encode(&self, request: &Request, digest: [u8; 32]) -> io::Result<Vec<u8>> {
        request.validate()?;
        let mut e = Encoder::new(80);
        e.number(1);
        write_binding(&mut e, request, digest)?;
        request.gnu.write(&mut e)?;
        match self {
            Self::Completed { completion, observation, artifact } => {
                let bytes = completion.encode()?;
                MetadataCompletion::decode(
                    &bytes,
                    request.key.graph.query.binding.root_attempt,
                    request.key.operation,
                )?;
                e.number(0);
                e.frame_bytes(&bytes)?;
                e.frame_bytes(&observation.encode()?)?;
                validate_artifact(request, completion, artifact.as_ref())?;
                match artifact {
                    None => e.number(0),
                    Some(file) => {
                        e.number(1);
                        file.encode(&mut e)?;
                    }
                }
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
        let mut d = header(bytes, 80)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        read_binding(&mut d, request, digest)?;
        if GnuIdentity::read(&mut d)? != request.gnu {
            return Err(invalid());
        }
        let value = match d.number()? {
            0 => Self::Completed {
                completion: Box::new(MetadataCompletion::decode(
                    &d.frame_bytes()?,
                    request.key.graph.query.binding.root_attempt,
                    request.key.operation,
                )?),
                observation: crate::accounting::Observation::decode(&d.frame_bytes()?)?,
                artifact: match d.number()? {
                    0 => None,
                    1 => Some(MetadataFile::decode(&mut d)?),
                    _ => return Err(invalid()),
                },
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

fn validate_artifact(
    request: &Request,
    completion: &MetadataCompletion,
    artifact: Option<&MetadataFile>,
) -> io::Result<()> {
    let success =
        matches!(completion.finished.status, Status::Finished { outcome: Outcome::Exit(0), .. })
            && completion.inputs_unchanged.is_ok();
    match artifact {
        Some(file) if success => {
            file.validate(&request.output_root)?;
            if file.path != request.output_path() || !(32..=MAX_OBJECT_BYTES).contains(&file.bytes)
            {
                return Err(invalid());
            }
        }
        None if !success => {}
        _ => return Err(invalid()),
    };
    Ok(())
}
#[cfg(all(feature = "channel", any(target_os = "macos", target_os = "linux")))]
pub mod transport;
