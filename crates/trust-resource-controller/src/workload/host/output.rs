//! Graph-wide original Layout lock observations. Only the live trusted SDK
//! capsule's actual descriptions can satisfy the separately unsafe handoff;
//! decoding this data never opens/acquires/reconstructs an output lock.
use std::collections::BTreeSet;
use std::io;

use crate::FileIdentity;
use crate::wire::{Decoder, Encoder, header, invalid};
use crate::workload::{contains, path};

pub const MARKER: u8 = 0x5b;
pub const MAX_LOCKS: usize = 64;
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Key {
    pub root_attempt: [u8; 16],
    pub invocation_sha256: [u8; 32],
    pub attempt: [u8; 16],
}
impl Key {
    fn write(&self, e: &mut Encoder) -> io::Result<()> {
        if self.root_attempt == [0; 16]
            || self.attempt == [0; 16]
            || self.attempt == self.root_attempt
        {
            return Err(invalid());
        }
        e.0.extend(self.root_attempt);
        e.0.extend(self.invocation_sha256);
        e.0.extend(self.attempt);
        Ok(())
    }
    fn read(d: &mut Decoder<'_>) -> io::Result<Self> {
        let key = Self {
            root_attempt: d.array()?,
            invocation_sha256: d.array()?,
            attempt: d.array()?,
        };
        key.write(&mut Encoder::new(0))?;
        Ok(key)
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Lock {
    pub path: Vec<u8>,
    pub backing: FileIdentity,
}
impl Lock {
    fn write(&self, e: &mut Encoder) -> io::Result<()> {
        if !path(&self.path)
            || self.backing.inode == 0
            || !matches!(
                self.path.rsplit(|byte| *byte == b'/').next(),
                Some(b".cargo-lock" | b".cargo-build-lock" | b".cargo-artifact-lock")
            )
        {
            return Err(invalid());
        }
        e.bytes(&self.path)?;
        e.number(self.backing.device);
        e.number(self.backing.inode);
        Ok(())
    }
    fn read(d: &mut Decoder<'_>) -> io::Result<Self> {
        let lock = Self {
            path: d.bytes()?,
            backing: FileIdentity {
                device: d.number()?,
                inode: d.number()?,
            },
        };
        lock.write(&mut Encoder::new(0))?;
        Ok(lock)
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Request {
    pub key: Key,
    pub output_root: Vec<u8>,
    pub locks: Vec<Lock>,
}
impl Request {
    pub fn validate(&self) -> io::Result<()> {
        self.key.write(&mut Encoder::new(0))?;
        if !path(&self.output_root) || self.locks.is_empty() || self.locks.len() > MAX_LOCKS {
            return Err(invalid());
        }
        let mut paths = BTreeSet::new();
        let mut ids = BTreeSet::new();
        for lock in &self.locks {
            lock.write(&mut Encoder::new(0))?;
            if !contains(&self.output_root, &lock.path)
                || lock.path == self.output_root
                || !paths.insert(&lock.path)
                || !ids.insert((lock.backing.device, lock.backing.inode))
            {
                return Err(invalid());
            }
        }
        Ok(())
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        let mut e = Encoder::new(54);
        e.number(3);
        self.key.write(&mut e)?;
        e.bytes(&self.output_root)?;
        e.number(self.locks.len() as u64);
        for lock in &self.locks {
            lock.write(&mut e)?;
        }
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 54)?;
        if d.number()? != 3 {
            return Err(invalid());
        }
        let key = Key::read(&mut d)?;
        let output_root = d.bytes()?;
        let mut locks = Vec::new();
        for _ in 0..d.count(MAX_LOCKS)? {
            locks.push(Lock::read(&mut d)?);
        }
        d.done()?;
        let value = Self {
            key,
            output_root,
            locks,
        };
        value.validate()?;
        Ok(value)
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Reply {
    Retained { key: Key, locks: Vec<Lock> },
    Refused { key: Key, reason: String },
}
impl Reply {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        let mut e = Encoder::new(52);
        e.number(3);
        match self {
            Self::Retained { key, locks } => {
                if locks.is_empty() || locks.len() > MAX_LOCKS {
                    return Err(invalid());
                }
                e.number(0);
                key.write(&mut e)?;
                e.number(locks.len() as u64);
                for lock in locks {
                    lock.write(&mut e)?;
                }
            }
            Self::Refused { key, reason } => {
                if reason.is_empty() || reason.len() > 4096 || reason.contains('\0') {
                    return Err(invalid());
                }
                e.number(1);
                key.write(&mut e)?;
                e.bytes(reason.as_bytes())?;
            }
        }
        e.finish()
    }
    pub fn decode(bytes: &[u8], expected: &Request) -> io::Result<Self> {
        expected.validate()?;
        let mut d = header(bytes, 52)?;
        if d.number()? != 3 {
            return Err(invalid());
        }
        let decision = d.number()?;
        let key = Key::read(&mut d)?;
        if key != expected.key {
            return Err(invalid());
        }
        let value = match decision {
            0 => {
                let mut locks = Vec::new();
                for _ in 0..d.count(MAX_LOCKS)? {
                    locks.push(Lock::read(&mut d)?);
                }
                if locks != expected.locks {
                    return Err(invalid());
                }
                Self::Retained { key, locks }
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

/// Selection DATA for a previously authenticated retained original handoff.
/// No descriptions, path opens or re-lock operations accompany this frame.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Selection {
    pub retained: Request,
    pub sequence: u64,
    pub attempt: [u8; 16],
}
impl Selection {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.retained.validate()?;
        if self.sequence == 0
            || self.attempt == [0; 16]
            || self.attempt == self.retained.key.root_attempt
            || self.attempt == self.retained.key.attempt
        {
            return Err(invalid());
        }
        let mut e = Encoder::new(112);
        e.number(1);
        e.number(self.sequence);
        e.0.extend(self.attempt);
        e.bytes(&self.retained.encode()?)?;
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 112)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let value = Self {
            sequence: d.number()?,
            attempt: d.array()?,
            retained: Request::decode(&d.bytes()?)?,
        };
        d.done()?;
        value.encode()?;
        Ok(value)
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SelectionDecision {
    Selected,
    Refused { reason: String },
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SelectionReply {
    pub selection: Selection,
    pub decision: SelectionDecision,
}
impl SelectionReply {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        let mut e = Encoder::new(113);
        e.number(1);
        e.bytes(&self.selection.encode()?)?;
        match &self.decision {
            SelectionDecision::Selected => e.number(0),
            SelectionDecision::Refused { reason } => {
                if reason.is_empty() || reason.len() > 4096 || reason.contains('\0') {
                    return Err(invalid());
                }
                e.number(1);
                e.bytes(reason.as_bytes())?;
            }
        }
        e.finish()
    }
    pub fn decode(bytes: &[u8], expected: &Selection) -> io::Result<Self> {
        expected.encode()?;
        let mut d = header(bytes, 113)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let selection = Selection::decode(&d.bytes()?)?;
        if selection != *expected {
            return Err(invalid());
        }
        let decision = match d.number()? {
            0 => SelectionDecision::Selected,
            1 => SelectionDecision::Refused { reason: d.text()? },
            _ => return Err(invalid()),
        };
        d.done()?;
        let value = Self {
            selection,
            decision,
        };
        value.encode()?;
        Ok(value)
    }
}

#[cfg(test)]
mod tests;
