//! Bounded retention observations for existing runtime/output descriptions.
//! These data never construct completion, SDK, CPU, execution or release rights.
use std::collections::BTreeSet;
use std::io;

use crate::wire::{Decoder, Encoder, header, invalid};
use crate::{ContextQuery, ContextReply, FileIdentity};

pub const PURPOSE: &str = "runtime-input-retention-v1";
pub const SUPPORT_ROLE: &str = "runtime-input-retention-support-v1";
pub const MAX_INPUTS: usize = 4096;
pub const CHUNK_INPUTS: usize = 128;
pub const RIGHTS_MARKER: u8 = 0x71;
pub const CAPABILITIES_JSON: &str = "{\"runtime_input_retention\":\"runtime-input-retention-v1\",\"max_inputs\":4096,\"chunk_inputs\":128}";

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Kind {
    RuntimeRoot,
    RuntimeDirectory,
    RuntimeFile,
    OutputRoot,
    OutputLock,
}
impl Kind {
    fn number(self) -> u64 {
        self as u64
    }
    fn read(d: &mut Decoder<'_>) -> io::Result<Self> {
        match d.number()? {
            0 => Ok(Self::RuntimeRoot),
            1 => Ok(Self::RuntimeDirectory),
            2 => Ok(Self::RuntimeFile),
            3 => Ok(Self::OutputRoot),
            4 => Ok(Self::OutputLock),
            _ => Err(invalid()),
        }
    }
    pub fn directory(self) -> bool {
        matches!(self, Self::RuntimeRoot | Self::RuntimeDirectory | Self::OutputRoot)
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Input {
    pub kind: Kind,
    /// Empty only for the two distinct roots. Inventory paths are relative.
    pub logical_path: Vec<u8>,
    pub target: Vec<u8>,
    /// Exact read_link payload. Opaque data, including any relative `..`.
    pub alias: Option<Vec<u8>>,
    pub backing: FileIdentity,
    pub size: Option<u64>,
    pub sha256: Option<[u8; 32]>,
    pub executable: bool,
}
fn absolute(path: &[u8]) -> bool {
    path.len() > 1
        && path.len() <= crate::MAX_FIELD
        && path[0] == b'/'
        && path[1..].split(|b| *b == b'/').all(|p| !p.is_empty() && p != b"." && p != b"..")
        && !path.contains(&0)
}
fn relative(path: &[u8]) -> bool {
    !path.is_empty()
        && path.len() <= crate::MAX_FIELD
        && path[0] != b'/'
        && path.split(|b| *b == b'/').all(|p| !p.is_empty() && p != b"." && p != b"..")
        && !path.contains(&0)
}
fn inside(root: &[u8], target: &[u8]) -> bool {
    target.starts_with(root) && target.get(root.len()) == Some(&b'/')
}
impl Input {
    fn validate(&self) -> io::Result<()> {
        // Directory traversal permission is not an executable-file declaration.
        if self.kind.directory() && self.executable {
            return Err(invalid());
        }
        if !absolute(&self.target)
            || self.backing.inode == 0
            || self
                .alias
                .as_ref()
                .is_some_and(|v| v.is_empty() || v.len() > crate::MAX_FIELD || v.contains(&0))
        {
            return Err(invalid());
        }
        match self.kind {
            Kind::RuntimeRoot | Kind::OutputRoot
                if !self.logical_path.is_empty() || self.alias.is_some() =>
            {
                return Err(invalid());
            }
            Kind::RuntimeDirectory | Kind::RuntimeFile if !relative(&self.logical_path) => {
                return Err(invalid());
            }
            Kind::OutputLock
                if self.logical_path != b"lock" || self.alias.is_some() || self.executable =>
            {
                return Err(invalid());
            }
            _ => {}
        }
        match self.kind {
            Kind::RuntimeFile if self.size.is_none() || self.sha256.is_none() => {
                return Err(invalid());
            }
            Kind::RuntimeRoot | Kind::RuntimeDirectory | Kind::OutputRoot | Kind::OutputLock
                if self.size.is_some() || self.sha256.is_some() =>
            {
                return Err(invalid());
            }
            _ => {}
        }
        Ok(())
    }
    fn write(&self, e: &mut Encoder) -> io::Result<()> {
        self.validate()?;
        e.number(self.kind.number());
        e.bytes(&self.logical_path)?;
        e.bytes(&self.target)?;
        match &self.alias {
            None => e.number(0),
            Some(v) => {
                e.number(1);
                e.bytes(v)?;
            }
        }
        e.number(self.backing.device);
        e.number(self.backing.inode);
        match self.size {
            None => e.number(0),
            Some(v) => {
                e.number(1);
                e.number(v);
            }
        }
        match self.sha256 {
            None => e.number(0),
            Some(v) => {
                e.number(1);
                e.0.extend(v);
            }
        }
        e.number(u64::from(self.executable));
        Ok(())
    }
    fn read(d: &mut Decoder<'_>) -> io::Result<Self> {
        let kind = Kind::read(d)?;
        let logical_path = d.bytes()?;
        let target = d.bytes()?;
        let alias = match d.number()? {
            0 => None,
            1 => Some(d.bytes()?),
            _ => return Err(invalid()),
        };
        let backing = FileIdentity { device: d.number()?, inode: d.number()? };
        let size = match d.number()? {
            0 => None,
            1 => Some(d.number()?),
            _ => return Err(invalid()),
        };
        let sha256 = match d.number()? {
            0 => None,
            1 => Some(d.array()?),
            _ => return Err(invalid()),
        };
        let executable = match d.number()? {
            0 => false,
            1 => true,
            _ => return Err(invalid()),
        };
        let value = Self { kind, logical_path, target, alias, backing, size, sha256, executable };
        value.validate()?;
        Ok(value)
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Key {
    pub root_attempt: [u8; 16],
    pub call_attempt: [u8; 16],
    pub transfer: [u8; 16],
}
impl Key {
    fn write(&self, e: &mut Encoder) -> io::Result<()> {
        if self.root_attempt == [0; 16]
            || self.call_attempt == [0; 16]
            || self.transfer == [0; 16]
            || self.root_attempt == self.call_attempt
            || self.transfer == self.root_attempt
            || self.transfer == self.call_attempt
        {
            return Err(invalid());
        }
        e.0.extend(self.root_attempt);
        e.0.extend(self.call_attempt);
        e.0.extend(self.transfer);
        Ok(())
    }
    fn read(d: &mut Decoder<'_>) -> io::Result<Self> {
        let key = Self { root_attempt: d.array()?, call_attempt: d.array()?, transfer: d.array()? };
        key.write(&mut Encoder::new(0))?;
        Ok(key)
    }
}
#[derive(Clone, PartialEq, Eq)]
pub struct Request {
    pub query: ContextQuery,
    pub transfer: [u8; 16],
    pub inputs: Vec<Input>,
}
impl Request {
    pub fn key(&self) -> Key {
        Key {
            root_attempt: self.query.binding.root_attempt,
            call_attempt: self.query.call_attempt,
            transfer: self.transfer,
        }
    }
    pub fn validate(&self) -> io::Result<()> {
        self.query.validate()?;
        self.key().write(&mut Encoder::new(0))?;
        if !(4..=MAX_INPUTS).contains(&self.inputs.len()) {
            return Err(invalid());
        }
        let mut unique = BTreeSet::new();
        for input in &self.inputs {
            input.validate()?;
            if !unique.insert((input.kind, &input.logical_path)) {
                return Err(invalid());
            }
        }
        let runtime =
            self.inputs.iter().find(|v| v.kind == Kind::RuntimeRoot).ok_or_else(invalid)?;
        let output = self.inputs.iter().find(|v| v.kind == Kind::OutputRoot).ok_or_else(invalid)?;
        if !self.inputs.iter().any(|v| v.kind == Kind::RuntimeFile) {
            return Err(invalid());
        }
        let lock = self.inputs.iter().find(|v| v.kind == Kind::OutputLock).ok_or_else(invalid)?;
        if lock.target.strip_prefix(output.target.as_slice()) != Some(b"/lock".as_slice()) {
            return Err(invalid());
        }
        for input in &self.inputs {
            if matches!(input.kind, Kind::RuntimeDirectory | Kind::RuntimeFile)
                && !inside(&runtime.target, &input.target)
            {
                return Err(invalid());
            }
        }
        Ok(())
    }
    pub fn hello(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        Ok(format!("{{\"version\":3,\"role\":\"{PURPOSE}\",\"session\":\"{}\",\"capabilities\":{CAPABILITIES_JSON}}}", self.query.binding.session).into_bytes())
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        let mut e = Encoder::new(68);
        e.number(1);
        e.frame_bytes(&self.query.encode()?)?;
        e.0.extend(self.transfer);
        e.number(self.inputs.len() as u64);
        for input in &self.inputs {
            input.write(&mut e)?;
        }
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 68)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let query = ContextQuery::decode(&d.frame_bytes()?)?;
        let transfer = d.array()?;
        let mut inputs = Vec::new();
        for _ in 0..d.count(MAX_INPUTS)? {
            inputs.push(Input::read(&mut d)?);
        }
        d.done()?;
        let value = Self { query, transfer, inputs };
        value.validate()?;
        Ok(value)
    }
}
/// A separate pre-Steps observation connection. Support promises no future
/// retention/admission; actual transfer must reauthenticate original membership.
#[derive(Clone, PartialEq, Eq)]
pub struct SupportQuery {
    pub query: ContextQuery,
}
impl SupportQuery {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        let mut e = Encoder::new(68);
        e.number(2);
        e.frame_bytes(&self.query.encode()?)?;
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 68)?;
        if d.number()? != 2 {
            return Err(invalid());
        }
        let query = ContextQuery::decode(&d.frame_bytes()?)?;
        d.done()?;
        Ok(Self { query })
    }
    pub fn hello(&self) -> io::Result<Vec<u8>> {
        self.query.validate()?;
        Ok(format!("{{\"version\":3,\"role\":\"{SUPPORT_ROLE}\",\"session\":\"{}\",\"capabilities\":{CAPABILITIES_JSON}}}", self.query.binding.session).into_bytes())
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SupportReply {
    Supported { context: Box<ContextReply> },
    Refused { root_attempt: [u8; 16], call_attempt: [u8; 16], reason: String },
}
impl SupportReply {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        let mut e = Encoder::new(69);
        e.number(2);
        match self {
            Self::Supported { context } => {
                e.number(0);
                e.frame_bytes(&context.encode()?)?;
            }
            Self::Refused { root_attempt, call_attempt, reason } => {
                if *root_attempt == [0; 16]
                    || *call_attempt == [0; 16]
                    || root_attempt == call_attempt
                    || reason.is_empty()
                    || reason.len() > 4096
                    || reason.contains('\0')
                {
                    return Err(invalid());
                }
                e.number(1);
                e.0.extend(root_attempt);
                e.0.extend(call_attempt);
                e.bytes(reason.as_bytes())?;
            }
        }
        e.finish()
    }
    pub fn decode(bytes: &[u8], query: &SupportQuery) -> io::Result<Self> {
        query.query.validate()?;
        let mut d = header(bytes, 69)?;
        if d.number()? != 2 {
            return Err(invalid());
        }
        let value = match d.number()? {
            0 => Self::Supported {
                context: Box::new(ContextReply::decode(&d.frame_bytes()?, &query.query)?),
            },
            1 => Self::Refused {
                root_attempt: d.array()?,
                call_attempt: d.array()?,
                reason: d.text()?,
            },
            _ => return Err(invalid()),
        };
        d.done()?;
        value.encode()?;
        if let Self::Refused { root_attempt, call_attempt, .. } = &value
            && (*root_attempt != query.query.binding.root_attempt
                || *call_attempt != query.query.call_attempt)
        {
            return Err(invalid());
        }
        Ok(value)
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Reply {
    Accepted { key: Key, context: ContextReply },
    Retained { key: Key, context: ContextReply },
    Refused { key: Key, reason: String },
}
impl Reply {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        let mut e = Encoder::new(69);
        e.number(1);
        match self {
            Self::Accepted { key, context } | Self::Retained { key, context } => {
                e.number(if matches!(self, Self::Accepted { .. }) { 0 } else { 1 });
                key.write(&mut e)?;
                e.frame_bytes(&context.encode()?)?;
            }
            Self::Refused { key, reason } => {
                if reason.is_empty() || reason.len() > 4096 || reason.contains('\0') {
                    return Err(invalid());
                }
                e.number(2);
                key.write(&mut e)?;
                e.bytes(reason.as_bytes())?;
            }
        }
        e.finish()
    }
    pub fn decode(bytes: &[u8], request: &Request) -> io::Result<Self> {
        request.validate()?;
        let mut d = header(bytes, 69)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let kind = d.number()?;
        let key = Key::read(&mut d)?;
        if key != request.key() {
            return Err(invalid());
        }
        let value = match kind {
            0 | 1 => {
                let context = ContextReply::decode(&d.frame_bytes()?, &request.query)?;
                if kind == 0 {
                    Self::Accepted { key, context }
                } else {
                    Self::Retained { key, context }
                }
            }
            2 => {
                let reason = d.text()?;
                if reason.is_empty() || reason.len() > 4096 || reason.contains('\0') {
                    return Err(invalid());
                }
                Self::Refused { key, reason }
            }
            _ => return Err(invalid()),
        };
        d.done()?;
        Ok(value)
    }
}
/// Private transfer frames, not another RPC role or admission command.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Transfer {
    Chunk { key: Key, offset: usize, count: usize },
    End { key: Key, count: usize },
}
impl Transfer {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        let mut e = Encoder::new(70);
        e.number(1);
        match self {
            Self::Chunk { key, offset, count } => {
                if *count == 0
                    || *count > CHUNK_INPUTS
                    || offset.checked_add(*count).is_none_or(|n| n > MAX_INPUTS)
                {
                    return Err(invalid());
                }
                e.number(0);
                key.write(&mut e)?;
                e.number(*offset as u64);
                e.number(*count as u64);
            }
            Self::End { key, count } => {
                if *count == 0 || *count > MAX_INPUTS {
                    return Err(invalid());
                }
                e.number(1);
                key.write(&mut e)?;
                e.number(*count as u64);
            }
        }
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 70)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let kind = d.number()?;
        let key = Key::read(&mut d)?;
        let value = match kind {
            0 => Self::Chunk { key, offset: d.count(MAX_INPUTS)?, count: d.count(CHUNK_INPUTS)? },
            1 => Self::End { key, count: d.count(MAX_INPUTS)? },
            _ => return Err(invalid()),
        };
        d.done()?;
        value.encode()?;
        Ok(value)
    }
}

#[cfg(test)]
mod tests;
#[cfg(all(feature = "channel", any(target_os = "linux", target_os = "macos")))]
pub mod transport;
