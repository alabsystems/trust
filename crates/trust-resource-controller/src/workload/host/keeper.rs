// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Pending-pair keeper DATA on the SAME original root channel. No frame,
//! acknowledgement or declared identity constructs funding, an adopted claim,
//! a writer or worker closure. Actual native/shadow/common-M descriptions must
//! travel together and remain with the original owning SDK/worker scope.

use std::io;

use crate::FileIdentity;
use crate::wire::{Encoder, header, invalid};

/// Native, shadow, read-only common-M guard, in that order.
pub const ORIGINALS_MARKER: u8 = 0x5e;

/// Canonical bytes of the existing v3 claim-reference projection. This is
/// equality DATA, not a current claim, release proof or installed authority.
/// Explicit key order keeps the fingerprint independent of JSON-map features.
pub fn memory_scope_bytes(
    namespace: [u8; 16],
    marker: &str,
    epoch: [u8; 16],
    guard: FileIdentity,
) -> io::Result<Vec<u8>> {
    let mut count = 0;
    for part in marker.split('-') {
        if count == 3 {
            return Err(invalid());
        }
        count += 1;
        if part.is_empty()
            || !part.bytes().all(|byte| byte.is_ascii_digit())
            || part.parse::<u64>().is_err()
        {
            return Err(invalid());
        }
    }
    if count != 3 || guard.inode == 0 {
        return Err(invalid());
    }
    fn hex(bytes: [u8; 16]) -> String {
        const DIGITS: &[u8; 16] = b"0123456789abcdef";
        let mut text = String::with_capacity(32);
        for byte in bytes {
            text.push(DIGITS[(byte >> 4) as usize] as char);
            text.push(DIGITS[(byte & 15) as usize] as char);
        }
        text
    }
    Ok(format!(
        "{{\"epoch\":\"{}\",\"guard\":{{\"device\":{},\"inode\":{}}},\"marker\":\"{}\",\"namespace\":\"{}\",\"v\":3}}",
        hex(epoch), guard.device, guard.inode, marker, hex(namespace),
    ).into_bytes())
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Request {
    pub root_attempt: [u8; 16],
    pub invocation_sha256: [u8; 32],
    pub phase: [u8; 16],
    pub nonce: [u8; 16],
    pub native_slot: u32,
    pub native: FileIdentity,
    pub shadow: FileIdentity,
    pub memory_guard: FileIdentity,
    /// Exact immutable common-M epoch, not release or new admission authority.
    pub memory_epoch: [u8; 16],
    /// SHA256 of the original canonical cohort reference; binding DATA only.
    pub memory_scope_sha256: [u8; 32],
}

impl Request {
    pub fn validate(&self) -> io::Result<()> {
        if self.root_attempt == [0; 16]
            || self.phase == [0; 16]
            || self.phase == self.root_attempt
            || self.nonce == [0; 16]
            || self.native_slot >= super::MAX_CPU_SET as u32
            || self.native.inode == 0
            || self.shadow.inode == 0
            || self.memory_guard.inode == 0
            || self.native == self.shadow
            || self.native == self.memory_guard
            || self.shadow == self.memory_guard
            || self.memory_epoch == [0; 16]
            || self.memory_scope_sha256 == [0; 32]
        {
            return Err(invalid());
        }
        Ok(())
    }

    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        let mut e = Encoder::new(137);
        e.number(1);
        e.0.extend(self.root_attempt);
        e.0.extend(self.invocation_sha256);
        e.0.extend(self.phase);
        e.0.extend(self.nonce);
        e.number(self.native_slot.into());
        for identity in [self.native, self.shadow, self.memory_guard] {
            e.number(identity.device);
            e.number(identity.inode);
        }
        e.0.extend(self.memory_epoch);
        e.0.extend(self.memory_scope_sha256);
        e.finish()
    }

    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 137)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let value = Self {
            root_attempt: d.array()?,
            invocation_sha256: d.array()?,
            phase: d.array()?,
            nonce: d.array()?,
            native_slot: d.narrow()?,
            native: FileIdentity { device: d.number()?, inode: d.number()? },
            shadow: FileIdentity { device: d.number()?, inode: d.number()? },
            memory_guard: FileIdentity { device: d.number()?, inode: d.number()? },
            memory_epoch: d.array()?,
            memory_scope_sha256: d.array()?,
        };
        d.done()?;
        value.validate()?;
        Ok(value)
    }
}

/// Equality acknowledgement only. The original sender must still retain its
/// actual pair/common-M/SDK and original worker closure owners; this creates no
/// execution or commit capability.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Retained {
    pub request: Request,
}
impl Retained {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        let mut e = Encoder::new(138);
        e.number(1);
        e.frame_bytes(&self.request.encode()?)?;
        e.finish()
    }
    pub fn decode(bytes: &[u8], original: &Request) -> io::Result<Self> {
        let mut d = header(bytes, 138)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let request = Request::decode(&d.frame_bytes()?)?;
        d.done()?;
        if &request != original {
            return Err(invalid());
        }
        Ok(Self { request })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn request() -> Request {
        Request {
            root_attempt: [1; 16],
            invocation_sha256: [2; 32],
            phase: [3; 16],
            nonce: [4; 16],
            native_slot: 0,
            native: FileIdentity { device: 1, inode: 2 },
            shadow: FileIdentity { device: 1, inode: 3 },
            memory_guard: FileIdentity { device: 1, inode: 4 },
            memory_epoch: [5; 16],
            memory_scope_sha256: [6; 32],
        }
    }
    #[test]
    fn pending_keeper_frames_bind_all_originals_without_reinterpreting_old_grants() {
        let original = request();
        let frame = original.encode().unwrap();
        assert_eq!(Request::decode(&frame).unwrap(), original);
        assert!(super::super::bank::Request::decode(&frame).is_err());
        let receipt = Retained { request: original }.encode().unwrap();
        for change in 0..7 {
            let mut foreign = original;
            match change {
                0 => foreign.root_attempt = [7; 16],
                1 => foreign.invocation_sha256 = [7; 32],
                2 => foreign.phase = [7; 16],
                3 => foreign.nonce = [7; 16],
                4 => foreign.native_slot = 1,
                5 => foreign.memory_epoch = [7; 16],
                _ => foreign.memory_scope_sha256 = [7; 32],
            }
            assert!(Retained::decode(&receipt, &foreign).is_err());
        }
        for len in 0..frame.len() {
            assert!(Request::decode(&frame[..len]).is_err());
        }
        let mut aliases = original;
        aliases.shadow = aliases.memory_guard;
        assert!(aliases.encode().is_err());
    }
}
