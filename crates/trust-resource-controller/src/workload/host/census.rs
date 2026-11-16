// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Complete bounded observations of actual original registered members. These
//! bytes create no root, target, SDK, CPU, completion or retirement authority.

use std::collections::BTreeSet;
use std::io;

use crate::accounting::Observation;
use crate::wire::{Decoder, Encoder, header, invalid};
use crate::{BirthKind, Identity, Started, Status, StatusFrame};

pub const MAX_ENTRIES: u32 = 4096;
pub const MAX_PAGE_ENTRIES: usize = 128;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SourceKind {
    Compiler,
    Linker,
    Query,
    BuildScript,
    Inventory,
    Sample,
    Coordinator,
}
impl SourceKind {
    fn number(self) -> u64 {
        match self {
            Self::Compiler => 0,
            Self::Linker => 1,
            Self::Query => 2,
            Self::BuildScript => 3,
            Self::Inventory => 4,
            Self::Sample => 5,
            Self::Coordinator => 6,
        }
    }
    fn decode(value: u64) -> io::Result<Self> {
        match value {
            0 => Ok(Self::Compiler),
            1 => Ok(Self::Linker),
            2 => Ok(Self::Query),
            3 => Ok(Self::BuildScript),
            4 => Ok(Self::Inventory),
            5 => Ok(Self::Sample),
            6 => Ok(Self::Coordinator),
            _ => Err(invalid()),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Entry {
    pub member_attempt: [u8; 16],
    pub kind: SourceKind,
    /// Actual prepared child identity, including a child refused before GO.
    pub identity: Option<Identity>,
    /// The original OwnedAttempt::start observation; never sampled anew.
    pub started: Option<Started>,
    pub terminal: Status,
    /// Original owning-wait scope; missing/Unknown never becomes measured zero.
    pub accounting: Observation,
    pub retired: bool,
    pub drained: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Request {
    pub root_attempt: [u8; 16],
    pub invocation_sha256: [u8; 32],
    pub snapshot: [u8; 16],
    pub offset: u32,
}
impl Request {
    fn write(&self, e: &mut Encoder) -> io::Result<()> {
        if self.root_attempt == [0; 16] || self.snapshot == [0; 16] || self.offset > MAX_ENTRIES {
            return Err(invalid());
        }
        e.0.extend(self.root_attempt);
        e.0.extend(self.invocation_sha256);
        e.0.extend(self.snapshot);
        e.number(self.offset.into());
        Ok(())
    }
    fn read(d: &mut Decoder<'_>) -> io::Result<Self> {
        let value = Self {
            root_attempt: d.array()?,
            invocation_sha256: d.array()?,
            snapshot: d.array()?,
            offset: d.narrow()?,
        };
        value.write(&mut Encoder::new(0))?;
        Ok(value)
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        let mut e = Encoder::new(51);
        e.number(3);
        self.write(&mut e)?;
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 51)?;
        if d.number()? != 3 {
            return Err(invalid());
        }
        let value = Self::read(&mut d)?;
        d.done()?;
        Ok(value)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Page {
    pub request: Request,
    pub total: u32,
    pub entries: Vec<Entry>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Reply {
    Page(Page),
    Busy { request: Request },
    Refused { request: Request, reason: String },
}
impl Reply {
    pub fn request(&self) -> &Request {
        match self {
            Self::Page(page) => &page.request,
            Self::Busy { request } | Self::Refused { request, .. } => request,
        }
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        let mut e = Encoder::new(53);
        e.number(3);
        self.request().write(&mut e)?;
        match self {
            Self::Page(page) => {
                if page.total > MAX_ENTRIES
                    || page.entries.len() > MAX_PAGE_ENTRIES
                    || page.request.offset > page.total
                    || page.entries.len() as u32 > page.total - page.request.offset
                    || (page.entries.is_empty() && (page.total != 0 || page.request.offset != 0))
                {
                    return Err(invalid());
                }
                e.number(0);
                e.number(page.total.into());
                e.number(page.entries.len() as u64);
                let mut attempts = BTreeSet::new();
                for entry in &page.entries {
                    if !attempts.insert(entry.member_attempt) {
                        return Err(invalid());
                    }
                    entry.write(&mut e, page.request.root_attempt)?;
                }
            }
            Self::Busy { .. } => e.number(1),
            Self::Refused { reason, .. } => {
                if reason.is_empty() || reason.len() > 4096 || reason.contains('\0') {
                    return Err(invalid());
                }
                e.number(2);
                e.bytes(reason.as_bytes())?;
            }
        }
        // The original frame bound applies in addition to the page population
        // bound. A large terminal reason requires a smaller actual page.
        e.finish()
    }
    pub fn decode(bytes: &[u8], expected: &Request) -> io::Result<Self> {
        let mut d = header(bytes, 53)?;
        if d.number()? != 3 {
            return Err(invalid());
        }
        let request = Request::read(&mut d)?;
        if &request != expected {
            return Err(invalid());
        }
        let value = match d.number()? {
            0 => {
                let total = d.narrow()?;
                let count = d.count(MAX_PAGE_ENTRIES)?;
                if total > MAX_ENTRIES
                    || request.offset > total
                    || count as u32 > total - request.offset
                    || (count == 0 && (total != 0 || request.offset != 0))
                {
                    return Err(invalid());
                }
                let mut entries = Vec::with_capacity(count);
                for _ in 0..count {
                    entries.push(Entry::read(&mut d, request.root_attempt)?);
                }
                Self::Page(Page {
                    request,
                    total,
                    entries,
                })
            }
            1 => Self::Busy { request },
            2 => Self::Refused {
                request,
                reason: String::from_utf8(d.bytes()?).map_err(|_| invalid())?,
            },
            _ => return Err(invalid()),
        };
        d.done()?;
        value.encode()?;
        Ok(value)
    }
}

fn write_identity(e: &mut Encoder, identity: Identity) -> io::Result<()> {
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
fn read_identity(d: &mut Decoder<'_>) -> io::Result<Identity> {
    let value = Identity {
        pid: d.narrow()?,
        birth: d.number()?,
        birth_kind: match d.number()? {
            0 => BirthKind::MacosWallMicroseconds,
            1 => BirthKind::LinuxStartTicks,
            _ => return Err(invalid()),
        },
    };
    write_identity(&mut Encoder::new(0), value)?;
    Ok(value)
}
fn boolean(d: &mut Decoder<'_>) -> io::Result<bool> {
    match d.number()? {
        0 => Ok(false),
        1 => Ok(true),
        _ => Err(invalid()),
    }
}
impl Entry {
    fn frame(&self, root_attempt: [u8; 16], status: Status) -> StatusFrame {
        StatusFrame {
            root_attempt,
            member_attempt: self.member_attempt,
            status,
        }
    }
    fn validate(&self) -> io::Result<()> {
        if self.member_attempt == [0; 16]
            || self
                .started
                .is_some_and(|start| self.identity != Some(start.identity))
        {
            return Err(invalid());
        }
        match &self.terminal {
            Status::Finished { .. } if self.started.is_some() => {}
            Status::Refused { .. } if self.started.is_none() => {}
            Status::Unknown { started, .. }
                if *started == self.started && self.accounting == Observation::uncollected() => {}
            _ => return Err(invalid()),
        }
        Ok(())
    }
    fn write(&self, e: &mut Encoder, root: [u8; 16]) -> io::Result<()> {
        self.validate()?;
        e.0.extend(self.member_attempt);
        e.number(self.kind.number());
        e.number(u64::from(self.identity.is_some()));
        if let Some(identity) = self.identity {
            write_identity(e, identity)?;
        }
        e.number(u64::from(self.started.is_some()));
        if let Some(started) = self.started {
            e.frame_bytes(&self.frame(root, Status::Started(started)).encode()?)?;
        }
        e.frame_bytes(&self.frame(root, self.terminal.clone()).encode()?)?;
        e.frame_bytes(&self.accounting.encode()?)?;
        e.number(u64::from(self.retired));
        e.number(u64::from(self.drained));
        Ok(())
    }
    fn read(d: &mut Decoder<'_>, root: [u8; 16]) -> io::Result<Self> {
        let member_attempt = d.array()?;
        let kind = SourceKind::decode(d.number()?)?;
        let identity = if boolean(d)? {
            Some(read_identity(d)?)
        } else {
            None
        };
        let started = if boolean(d)? {
            match StatusFrame::decode(&d.frame_bytes()?, root, member_attempt)?.status {
                Status::Started(started) => Some(started),
                _ => return Err(invalid()),
            }
        } else {
            None
        };
        let terminal = StatusFrame::decode(&d.frame_bytes()?, root, member_attempt)?.status;
        let value = Self {
            member_attempt,
            kind,
            identity,
            started,
            terminal,
            accounting: Observation::decode(&d.frame_bytes()?)?,
            retired: boolean(d)?,
            drained: boolean(d)?,
        };
        value.validate()?;
        Ok(value)
    }
}

#[cfg(test)]
mod tests;
