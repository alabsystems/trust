// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Bounded original-description attachment DATA, never an input/CPU grant.
use super::*;
pub const SCOPE_PURPOSE: &str = "native-coordinator-compiler-scope-v1";
pub const SCOPE_MARKER: u8 = 0x6c;
pub const MAX_SCOPE_FILES: usize = 128;
#[derive(Clone, PartialEq, Eq)]
pub struct ScopeFile {
    pub path: Vec<u8>,
    /// Equality against the parent's retained native producer only.
    pub producer: [u8; 16],
}
#[derive(Clone, PartialEq, Eq)]
pub struct ScopeRequest {
    pub query: ContextQuery,
    pub coordinator: [u8; 16],
    pub member: [u8; 16],
    pub directory: Vec<u8>,
    pub files: Vec<ScopeFile>,
}
impl ScopeRequest {
    /// Retained DATA capacity only, never an original-description or grant.
    pub fn retained_bytes(&self) -> Option<usize> {
        let mut bytes = std::mem::size_of::<Self>()
            .checked_add(self.query.binding.session.capacity())?
            .checked_add(self.directory.capacity())?
            .checked_add(
                self.files
                    .capacity()
                    .checked_mul(std::mem::size_of::<ScopeFile>())?,
            )?;
        for file in &self.files {
            bytes = bytes.checked_add(file.path.capacity())?;
        }
        Some(bytes)
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.query.validate()?;
        if !path(&self.directory)
            || [self.coordinator, self.member].contains(&[0; 16])
            || self.coordinator == self.member
            || [self.coordinator, self.member].contains(&self.query.binding.root_attempt)
            || self.files.len() > MAX_SCOPE_FILES
        {
            return Err(invalid());
        }
        let mut names = std::collections::BTreeSet::new();
        let mut e = Encoder::new(102);
        e.number(1);
        e.frame_bytes(&self.query.encode()?)?;
        e.0.extend(self.coordinator);
        e.0.extend(self.member);
        e.bytes(&self.directory)?;
        e.number(self.files.len() as u64);
        for file in &self.files {
            if !path(&file.path)
                || !names.insert(&file.path)
                || [
                    self.query.binding.root_attempt,
                    self.coordinator,
                    self.member,
                    [0; 16],
                ]
                .contains(&file.producer)
            {
                return Err(invalid());
            }
            e.bytes(&file.path)?;
            e.0.extend(file.producer);
        }
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 102)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let query = ContextQuery::decode(&d.frame_bytes()?)?;
        let coordinator = d.array()?;
        let member = d.array()?;
        let directory = d.bytes()?;
        let mut files = Vec::new();
        for _ in 0..d.count(MAX_SCOPE_FILES)? {
            files.push(ScopeFile {
                path: d.bytes()?,
                producer: d.array()?,
            });
        }
        d.done()?;
        let value = Self {
            query,
            coordinator,
            member,
            directory,
            files,
        };
        value.encode()?;
        Ok(value)
    }
    pub fn hello(&self) -> io::Result<Vec<u8>> {
        self.encode()?;
        let attempt: String = self
            .query
            .binding
            .root_attempt
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect();
        Ok(format!("{{\"version\":3,\"role\":\"{SCOPE_PURPOSE}\",\"session\":\"{}\",\"attempt\":\"{attempt}\"}}",self.query.binding.session).into_bytes())
    }
}
/// Equality observation after genuine descriptor attachment. No decoder makes
/// the opaque client/Host original owners or grants later compiler execution.
pub struct ScopeReply {
    pub member: [u8; 16],
}
impl ScopeReply {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        if self.member == [0; 16] {
            return Err(invalid());
        }
        let mut e = Encoder::new(103);
        e.number(1);
        e.0.extend(self.member);
        e.finish()
    }
    pub fn decode(bytes: &[u8], request: &ScopeRequest) -> io::Result<Self> {
        let mut d = header(bytes, 103)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let member = d.array()?;
        d.done()?;
        let value = Self { member };
        value.encode()?;
        if value.member != request.member {
            return Err(invalid());
        }
        Ok(value)
    }
}
#[cfg(test)]
mod tests;
