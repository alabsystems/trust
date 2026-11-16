// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Original transport observations, not a resource grant or completion.
use super::*;
pub const TRANSPORT_PURPOSE: &str = "native-coordinator-compiler-transport-v2";
pub const TRANSPORT_MARKER: u8 = 0x6d;
pub const TRANSPORT_ORIGINALS: usize = 5 + super::super::super::CONTROL_ORIGINALS;
#[derive(Clone)]
pub struct TransportRequest {
    pub query: crate::ContextQuery,
    pub selected: CompilerSelection,
}
impl TransportRequest {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.query.validate()?;
        self.selected.encode()?;
        if self.query.binding.root_attempt != self.selected.root_attempt {
            return Err(invalid());
        }
        let mut e = Encoder::new(104);
        e.number(2);
        e.frame_bytes(&self.query.encode()?)?;
        e.frame_bytes(&self.selected.encode()?)?;
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 104)?;
        if d.number()? != 2 {
            return Err(invalid());
        }
        let value = Self {
            query: crate::ContextQuery::decode(&d.frame_bytes()?)?,
            selected: CompilerSelection::decode(&d.frame_bytes()?)?,
        };
        d.done()?;
        value.encode()?;
        Ok(value)
    }
    pub fn hello(&self) -> io::Result<Vec<u8>> {
        self.encode()?;
        let attempt: String = self
            .selected
            .root_attempt
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect();
        Ok(format!("{{\"version\":3,\"role\":\"{TRANSPORT_PURPOSE}\",\"session\":\"{}\",\"attempt\":\"{attempt}\"}}",self.query.binding.session).into_bytes())
    }
}
/// CPU, GNU read/write, SDK lease, Store, then nine actual control originals.
/// The advertisement comes from the SAME live armed Host ScopedHandoff.
/// Only the private authenticated client can create its native owner.
pub struct TransportReply {
    pub selected: CompilerSelection,
    pub context: crate::ContextReply,
    pub target: Identity,
    pub advertisement: Vec<u8>,
    pub backings: [crate::FileIdentity; TRANSPORT_ORIGINALS],
}
impl TransportReply {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.selected.encode()?;
        if !matches!(self.context.context.subject, crate::Subject::Root { .. })
            || self.context.context.sdk.is_none()
            || self.context.context.root_attempt != self.selected.root_attempt
            || self.backings.iter().any(|file| file.inode == 0)
            || self.target.pid <= 1
            || self.target.birth == 0
            || self.target.pid == self.context.context.original_root.pid
            || self.target.birth_kind != self.context.context.original_root.birth_kind
            || self.advertisement.is_empty()
            || self.advertisement.len() > 4096
            || self.advertisement.contains(&0)
        {
            return Err(invalid());
        }
        let mut e = Encoder::new(105);
        e.number(2);
        e.frame_bytes(&self.selected.encode()?)?;
        e.frame_bytes(&self.context.encode()?)?;
        e.number(self.target.pid.into());
        e.number(self.target.birth);
        e.number(match self.target.birth_kind {
            BirthKind::MacosWallMicroseconds => 1,
            BirthKind::LinuxStartTicks => 2,
        });
        e.bytes(&self.advertisement)?;
        for file in &self.backings {
            e.number(file.device);
            e.number(file.inode);
        }
        e.finish()
    }
    pub fn decode(bytes: &[u8], request: &TransportRequest) -> io::Result<Self> {
        let mut d = header(bytes, 105)?;
        if d.number()? != 2 {
            return Err(invalid());
        }
        let selected = CompilerSelection::decode(&d.frame_bytes()?)?;
        let context = crate::ContextReply::decode(&d.frame_bytes()?, &request.query)?;
        let target = Identity {
            pid: d.narrow()?,
            birth: d.number()?,
            birth_kind: match d.number()? {
                1 => BirthKind::MacosWallMicroseconds,
                2 => BirthKind::LinuxStartTicks,
                _ => return Err(invalid()),
            },
        };
        let advertisement = d.bytes()?;
        let mut backings = [crate::FileIdentity {
            device: 0,
            inode: 0,
        }; TRANSPORT_ORIGINALS];
        for file in &mut backings {
            *file = crate::FileIdentity {
                device: d.number()?,
                inode: d.number()?,
            };
        }
        d.done()?;
        let value = Self {
            selected,
            context,
            target,
            advertisement,
            backings,
        };
        value.encode()?;
        if value.selected != request.selected {
            return Err(invalid());
        }
        Ok(value)
    }
}
#[cfg(test)]
mod tests;
