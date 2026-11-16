// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Partial CPU handoff on the SAME original workload control stream.
//!
//! These bounded frames are observations. Only the authenticated live channel,
//! actual original SDK phase owner and transferred unit descriptions supply
//! custody. V1 phase frames remain full-width and do not convert to this path.
use std::io;

use super::MAX_CPU_SET;
use super::bank::Key;
use crate::FileIdentity;
use crate::wire::{Encoder, header, invalid};

pub const CPU_MARKER: u8 = 0x5d;

/// Equality DATA for a freshly transferred original, with no guessed inherited
/// target FD. Actual custody travels only on the authenticated SCM channel.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CpuUnit {
    pub slot: u32,
    pub backing: FileIdentity,
}
impl From<&super::PrimaryCpu> for CpuUnit {
    fn from(cpu: &super::PrimaryCpu) -> Self {
        Self { slot: cpu.slot, backing: cpu.backing }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Operation {
    /// No unit is returned yet. Host binds its original SDK/current scope.
    Prepare { gnu: FileIdentity, implicit: CpuUnit },
    /// Bind captive GNU only after distinct authenticated initial-pair startup.
    PrepareInitial { gnu: FileIdentity, implicit: CpuUnit },
    /// Root has closed supplementary descriptions while retaining GNU escrow.
    Release,
    /// Request real funded backing under the original retained scope/deadline.
    Restore,
    /// Root installed the actual returned descriptions; GNU remains escrowed.
    Commit,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Request {
    pub key: Key,
    pub phase: [u8; 16],
    pub operation: Operation,
}
fn valid(key: &Key, phase: [u8; 16]) -> bool {
    key.root_attempt != [0; 16]
        && key.invocation_sha256 != [0; 32]
        && key.sequence != 0
        && phase != [0; 16]
        && phase != key.root_attempt
}
fn write_key(e: &mut Encoder, key: &Key, phase: [u8; 16]) -> io::Result<()> {
    if !valid(key, phase) {
        return Err(invalid());
    }
    e.number(2);
    e.0.extend(key.root_attempt);
    e.0.extend(key.invocation_sha256);
    e.number(key.sequence);
    e.0.extend(phase);
    Ok(())
}
fn write_cpu(e: &mut Encoder, cpu: &CpuUnit) -> io::Result<()> {
    if cpu.backing.inode == 0 {
        return Err(invalid());
    }
    e.number(cpu.slot.into());
    e.number(cpu.backing.device);
    e.number(cpu.backing.inode);
    Ok(())
}
impl Request {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        let mut e = Encoder::new(51);
        write_key(&mut e, &self.key, self.phase)?;
        match self.operation {
            Operation::Prepare { gnu, implicit } => {
                if gnu.inode == 0 {
                    return Err(invalid());
                }
                e.number(0);
                e.number(gnu.device);
                e.number(gnu.inode);
                write_cpu(&mut e, &implicit)?;
            }
            Operation::Release => e.number(1),
            Operation::Restore => e.number(2),
            Operation::Commit => e.number(3),
            Operation::PrepareInitial { gnu, implicit } => {
                if gnu.inode == 0 {
                    return Err(invalid());
                }
                e.number(4);
                e.number(gnu.device);
                e.number(gnu.inode);
                write_cpu(&mut e, &implicit)?;
            }
        }
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 51)?;
        if d.number()? != 2 {
            return Err(invalid());
        }
        let key =
            Key { root_attempt: d.array()?, invocation_sha256: d.array()?, sequence: d.number()? };
        let phase = d.array()?;
        let operation = match d.number()? {
            0 => Operation::Prepare {
                gnu: FileIdentity { device: d.number()?, inode: d.number()? },
                implicit: CpuUnit {
                    slot: d.narrow()?,
                    backing: FileIdentity { device: d.number()?, inode: d.number()? },
                },
            },
            1 => Operation::Release,
            2 => Operation::Restore,
            3 => Operation::Commit,
            4 => Operation::PrepareInitial {
                gnu: FileIdentity { device: d.number()?, inode: d.number()? },
                implicit: CpuUnit {
                    slot: d.narrow()?,
                    backing: FileIdentity { device: d.number()?, inode: d.number()? },
                },
            },
            _ => return Err(invalid()),
        };
        d.done()?;
        let request = Self { key, phase, operation };
        request.encode()?;
        Ok(request)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Decision {
    Prepared,
    Released,
    /// Exactly these SAME original Host units follow on the authenticated
    /// channel. Their metadata alone cannot restore Root dispatch/GNU tokens.
    Funded {
        supplementary: Vec<CpuUnit>,
    },
    Committed,
    Busy,
    Refused,
    /// Selected immutable SDK lacks this additive protocol. No release began.
    Unsupported,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Reply {
    pub key: Key,
    pub phase: [u8; 16],
    pub decision: Decision,
}
impl Reply {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        let mut e = Encoder::new(53);
        write_key(&mut e, &self.key, self.phase)?;
        match &self.decision {
            Decision::Prepared => e.number(0),
            Decision::Released => e.number(1),
            Decision::Funded { supplementary } => {
                if supplementary.is_empty() || supplementary.len() >= MAX_CPU_SET {
                    return Err(invalid());
                }
                e.number(2);
                e.number(supplementary.len() as u64);
                for (index, cpu) in supplementary.iter().enumerate() {
                    if supplementary[..index]
                        .iter()
                        .any(|other| other.slot == cpu.slot || other.backing == cpu.backing)
                    {
                        return Err(invalid());
                    }
                    write_cpu(&mut e, cpu)?;
                }
            }
            Decision::Committed => e.number(3),
            Decision::Busy => e.number(4),
            Decision::Refused => e.number(5),
            Decision::Unsupported => e.number(6),
        }
        e.finish()
    }
    pub fn decode(bytes: &[u8], request: &Request) -> io::Result<Self> {
        let mut d = header(bytes, 53)?;
        if d.number()? != 2 {
            return Err(invalid());
        }
        let key =
            Key { root_attempt: d.array()?, invocation_sha256: d.array()?, sequence: d.number()? };
        let phase = d.array()?;
        if key != request.key || phase != request.phase {
            return Err(invalid());
        }
        let decision = match d.number()? {
            0 => Decision::Prepared,
            1 => Decision::Released,
            2 => {
                let count = usize::try_from(d.narrow()?).map_err(|_| invalid())?;
                if count == 0 || count >= MAX_CPU_SET {
                    return Err(invalid());
                }
                let mut supplementary = Vec::new();
                supplementary.try_reserve_exact(count).map_err(io::Error::other)?;
                for _ in 0..count {
                    supplementary.push(CpuUnit {
                        slot: d.narrow()?,
                        backing: FileIdentity { device: d.number()?, inode: d.number()? },
                    });
                }
                Decision::Funded { supplementary }
            }
            3 => Decision::Committed,
            4 => Decision::Busy,
            5 => Decision::Refused,
            6 => Decision::Unsupported,
            _ => return Err(invalid()),
        };
        d.done()?;
        if !matches!(
            (&request.operation, &decision),
            (Operation::Prepare { .. }, Decision::Prepared)
                | (Operation::PrepareInitial { .. }, Decision::Prepared)
                | (Operation::Release, Decision::Released)
                | (Operation::Restore, Decision::Funded { .. })
                | (Operation::Commit, Decision::Committed)
                | (Operation::Prepare { .. }, Decision::Unsupported)
                | (_, Decision::Busy | Decision::Refused)
        ) {
            return Err(invalid());
        }
        let reply = Self { key, phase, decision };
        reply.encode()?;
        Ok(reply)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn partial_cpu_frames_bind_original_phase_direction_and_actual_unit_identity() {
        let key = Key { root_attempt: [1; 16], invocation_sha256: [2; 32], sequence: 7 };
        let prepare = Request {
            key,
            phase: [3; 16],
            operation: Operation::Prepare {
                gnu: FileIdentity { device: 4, inode: 5 },
                implicit: CpuUnit { slot: 0, backing: FileIdentity { device: 6, inode: 7 } },
            },
        };
        assert_eq!(Request::decode(&prepare.encode().unwrap()).unwrap(), prepare);
        assert!(
            super::super::phase::Request::decode(&prepare.encode().unwrap()).is_err(),
            "V1 cannot consume a V2 partial handoff"
        );
        let restore = Request { operation: Operation::Restore, ..prepare };
        let funded = Reply {
            key,
            phase: prepare.phase,
            decision: Decision::Funded {
                supplementary: vec![CpuUnit {
                    slot: 1,
                    backing: FileIdentity { device: 6, inode: 8 },
                }],
            },
        };
        assert_eq!(Reply::decode(&funded.encode().unwrap(), &restore).unwrap(), funded);
        assert!(
            Reply::decode(&funded.encode().unwrap(), &prepare).is_err(),
            "metadata cannot turn preparation into funded capacity"
        );
        assert!(
            Reply::decode(&funded.encode().unwrap(), &Request { phase: [9; 16], ..restore })
                .is_err()
        );
        let mut duplicate = funded.clone();
        let Decision::Funded { supplementary } = &mut duplicate.decision else { unreachable!() };
        supplementary.push(supplementary[0]);
        assert!(
            duplicate.encode().is_err(),
            "duplicate actual unit metadata is not additional funding"
        );
        let mut truncated = funded.encode().unwrap();
        truncated.pop();
        assert!(Reply::decode(&truncated, &restore).is_err());
        let mut oversized = Encoder::new(53);
        write_key(&mut oversized, &key, prepare.phase).unwrap();
        oversized.number(2);
        oversized.number(MAX_CPU_SET as u64);
        assert!(
            Reply::decode(&oversized.finish().unwrap(), &restore).is_err(),
            "reject count before allocating or receiving FDs"
        );
        let unsupported = Reply { key, phase: prepare.phase, decision: Decision::Unsupported };
        assert!(Reply::decode(&unsupported.encode().unwrap(), &prepare).is_ok());
        assert!(
            Reply::decode(&unsupported.encode().unwrap(), &restore).is_err(),
            "unsupported cannot cancel an already returned phase"
        );
    }
}
