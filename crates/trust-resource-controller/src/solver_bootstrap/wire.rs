// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Fixed private bootstrap records. Bytes never construct admission authority.
use std::io;

pub(crate) const LEN: usize = 104;
const MAGIC: &[u8; 8] = b"ASBV0001";

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Frame {
    pub kind: u64,
    pub attempt: [u8; 16],
    pub challenge: [u8; 32],
    pub pid: u32,
    pub birth: u64,
    pub footprint_mib: u32,
    pub units: u32,
    pub monotonic_ns: u64,
}

pub(crate) fn invalid() -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, "private solver bootstrap refused")
}

impl Frame {
    pub fn encode(self) -> [u8; LEN] {
        let mut bytes = [0; LEN];
        bytes[..8].copy_from_slice(MAGIC);
        bytes[8..16].copy_from_slice(&self.kind.to_be_bytes());
        bytes[16..32].copy_from_slice(&self.attempt);
        bytes[32..64].copy_from_slice(&self.challenge);
        for (index, value) in [
            u64::from(self.pid),
            self.birth,
            u64::from(self.footprint_mib),
            u64::from(self.units),
            self.monotonic_ns,
        ]
        .into_iter()
        .enumerate()
        {
            bytes[64 + 8 * index..72 + 8 * index].copy_from_slice(&value.to_be_bytes());
        }
        bytes
    }

    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        if bytes.len() != LEN || &bytes[..8] != MAGIC {
            return Err(invalid());
        }
        let number = |offset| {
            let mut word = [0; 8];
            word.copy_from_slice(&bytes[offset..offset + 8]);
            u64::from_be_bytes(word)
        };
        let mut attempt = [0; 16];
        attempt.copy_from_slice(&bytes[16..32]);
        let mut challenge = [0; 32];
        challenge.copy_from_slice(&bytes[32..64]);
        let frame = Self {
            kind: number(8),
            attempt,
            challenge,
            pid: u32::try_from(number(64)).map_err(|_| invalid())?,
            birth: number(72),
            footprint_mib: u32::try_from(number(80)).map_err(|_| invalid())?,
            units: u32::try_from(number(88)).map_err(|_| invalid())?,
            monotonic_ns: number(96),
        };
        if !matches!(frame.kind, 1..=3)
            || frame.attempt == [0; 16]
            || frame.challenge == [0; 32]
            || frame.pid <= 1
            || frame.pid > i32::MAX as u32
            || frame.birth == 0
            || frame.units == 0
            || frame.footprint_mib == 0
            || frame.footprint_mib > i32::MAX as u32
            || (frame.kind == 3) != (frame.monotonic_ns > 0)
        {
            return Err(invalid());
        }
        Ok(frame)
    }

    pub fn response(self, kind: u64, monotonic_ns: u64) -> Self {
        Self { kind, monotonic_ns, ..self }
    }
}
