//! Same-root foreign phase coordination on the original root control stream.
//! These frames bind requests and observations only. The live host's original
//! resources, retired members, GNU escrow and produced-input owner authorize GO.
use std::io;

use super::MAX_CPU_SET;
use super::bank::Key;
use crate::FileIdentity;
use crate::wire::{Encoder, header, invalid};

/// Enter transfers the SAME original FIFO's read/write descriptions in order.
pub const GNU_MARKER: u8 = 0x59;
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    BuildScript,
    Harnesses,
    /// A serial produced coordinator lends its actual one original primary.
    Coordinator,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Operation {
    Enter {
        phase: [u8; 16],
        kind: Kind,
        gnu: FileIdentity,
    },
    Leave {
        phase: [u8; 16],
    },
    /// Command/queue settlement, never an ExitStatus or native retirement proof.
    Drained,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Request {
    pub key: Key,
    pub operation: Operation,
}
fn key_valid(key: &Key) -> bool {
    key.root_attempt != [0; 16] && key.sequence != 0
}
fn phase_valid(key: &Key, phase: [u8; 16]) -> bool {
    phase != [0; 16] && phase != key.root_attempt
}
impl Request {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        if !key_valid(&self.key) {
            return Err(invalid());
        }
        let mut e = Encoder::new(51);
        e.number(1);
        e.0.extend(self.key.root_attempt);
        e.0.extend(self.key.invocation_sha256);
        e.number(self.key.sequence);
        match self.operation {
            Operation::Enter { phase, kind, gnu } => {
                if !phase_valid(&self.key, phase) || gnu.inode == 0 {
                    return Err(invalid());
                }
                e.number(0);
                e.0.extend(phase);
                e.number(match kind {
                    Kind::BuildScript => 0,
                    Kind::Harnesses => 1,
                    Kind::Coordinator => 2,
                });
                e.number(gnu.device);
                e.number(gnu.inode);
            }
            Operation::Leave { phase } => {
                if !phase_valid(&self.key, phase) {
                    return Err(invalid());
                }
                e.number(1);
                e.0.extend(phase);
            }
            Operation::Drained => e.number(2),
        }
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 51)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let key =
            Key { root_attempt: d.array()?, invocation_sha256: d.array()?, sequence: d.number()? };
        let operation = match d.number()? {
            0 => Operation::Enter {
                phase: d.array()?,
                kind: match d.number()? {
                    0 => Kind::BuildScript,
                    1 => Kind::Harnesses,
                    2 => Kind::Coordinator,
                    _ => return Err(invalid()),
                },
                gnu: FileIdentity { device: d.number()?, inode: d.number()? },
            },
            1 => Operation::Leave { phase: d.array()? },
            2 => Operation::Drained,
            _ => return Err(invalid()),
        };
        d.done()?;
        let value = Self { key, operation };
        value.encode()?;
        Ok(value)
    }
    pub fn description_count(&self) -> usize {
        usize::from(matches!(self.operation, Operation::Enter { .. })) * 2
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Decision {
    Ready { phase: [u8; 16], reserved_domain: u32, gnu: FileIdentity },
    Busy,
    Refused { reason: String },
    Left { phase: [u8; 16] },
    Drained,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Reply {
    pub key: Key,
    pub decision: Decision,
}
impl Reply {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        if !key_valid(&self.key) {
            return Err(invalid());
        }
        let mut e = Encoder::new(53);
        e.number(1);
        e.0.extend(self.key.root_attempt);
        e.0.extend(self.key.invocation_sha256);
        e.number(self.key.sequence);
        match &self.decision {
            Decision::Ready { phase, reserved_domain, gnu } => {
                if !phase_valid(&self.key, *phase)
                    || !(1..=MAX_CPU_SET as u32).contains(reserved_domain)
                    || gnu.inode == 0
                {
                    return Err(invalid());
                }
                e.number(0);
                e.0.extend(phase);
                e.number((*reserved_domain).into());
                e.number(gnu.device);
                e.number(gnu.inode);
            }
            Decision::Busy => e.number(1),
            Decision::Refused { reason } => {
                if reason.is_empty() || reason.len() > 4096 || reason.contains('\0') {
                    return Err(invalid());
                }
                e.number(2);
                e.bytes(reason.as_bytes())?;
            }
            Decision::Left { phase } => {
                if !phase_valid(&self.key, *phase) {
                    return Err(invalid());
                }
                e.number(3);
                e.0.extend(phase);
            }
            Decision::Drained => e.number(4),
        }
        e.finish()
    }
    pub fn decode(bytes: &[u8], request: &Request) -> io::Result<Self> {
        let mut d = header(bytes, 53)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let key =
            Key { root_attempt: d.array()?, invocation_sha256: d.array()?, sequence: d.number()? };
        if key != request.key {
            return Err(invalid());
        }
        let decision = match d.number()? {
            0 => Decision::Ready {
                phase: d.array()?,
                reserved_domain: d.narrow()?,
                gnu: FileIdentity { device: d.number()?, inode: d.number()? },
            },
            1 => Decision::Busy,
            2 => {
                Decision::Refused { reason: String::from_utf8(d.bytes()?).map_err(|_| invalid())? }
            }
            3 => Decision::Left { phase: d.array()? },
            4 => Decision::Drained,
            _ => return Err(invalid()),
        };
        d.done()?;
        let value = Self { key, decision };
        value.encode()?;
        match (&request.operation, &value.decision) {
            (
                Operation::Enter { phase, gnu, .. },
                Decision::Ready { phase: got, gnu: backing, .. },
            ) if phase == got && gnu == backing => {}
            (Operation::Leave { phase }, Decision::Left { phase: got }) if phase == got => {}
            (Operation::Drained, Decision::Drained) => {}
            (_, Decision::Busy | Decision::Refused { .. }) => {}
            _ => return Err(invalid()),
        }
        Ok(value)
    }
}
/// Distinct current-share transport. Only the mathematical operation fields
/// reuse the closed V1 DATA codec; neither V1 endpoint nor full-domain custody
/// accepts this outer version. Actual current Root/SDK/FD/M owners are required.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CurrentShareRequest {
    pub key: Key,
    pub operation: Operation,
}
impl CurrentShareRequest {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        let data = Request { key: self.key, operation: self.operation }.encode()?;
        let mut e = Encoder::new(51);
        e.number(3);
        e.frame_bytes(&data)?;
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 51)?;
        if d.number()? != 3 {
            return Err(invalid());
        }
        let data = Request::decode(&d.frame_bytes()?)?;
        d.done()?;
        Ok(Self { key: data.key, operation: data.operation })
    }
    pub fn description_count(&self) -> usize {
        Request { key: self.key, operation: self.operation }.description_count()
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CurrentShareReply {
    pub key: Key,
    pub decision: Decision,
}
impl CurrentShareReply {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        let data = Reply { key: self.key, decision: self.decision.clone() }.encode()?;
        let mut e = Encoder::new(53);
        e.number(3);
        e.frame_bytes(&data)?;
        e.finish()
    }
    pub fn decode(bytes: &[u8], request: &CurrentShareRequest) -> io::Result<Self> {
        let mut d = header(bytes, 53)?;
        if d.number()? != 3 {
            return Err(invalid());
        }
        let data = Reply::decode(
            &d.frame_bytes()?,
            &Request { key: request.key, operation: request.operation },
        )?;
        d.done()?;
        Ok(Self { key: data.key, decision: data.decision })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn current_share_frames_are_distinct_and_bound_to_the_original_phase() {
        let request = CurrentShareRequest {
            key: Key { root_attempt: [1; 16], invocation_sha256: [2; 32], sequence: 1 },
            operation: Operation::Enter {
                phase: [3; 16],
                kind: Kind::Harnesses,
                gnu: FileIdentity { device: 4, inode: 5 },
            },
        };
        let bytes = request.encode().unwrap();
        assert_eq!(CurrentShareRequest::decode(&bytes).unwrap(), request);
        assert!(Request::decode(&bytes).is_err());
        let legacy = Request { key: request.key, operation: request.operation };
        assert!(CurrentShareRequest::decode(&legacy.encode().unwrap()).is_err());
        let reply = CurrentShareReply {
            key: request.key,
            decision: Decision::Ready {
                phase: [3; 16],
                reserved_domain: 1,
                gnu: FileIdentity { device: 4, inode: 5 },
            },
        };
        let bytes = reply.encode().unwrap();
        assert_eq!(CurrentShareReply::decode(&bytes, &request).unwrap(), reply);
        assert!(Reply::decode(&bytes, &legacy).is_err());
        for end in 0..bytes.len() {
            assert!(CurrentShareReply::decode(&bytes[..end], &request).is_err());
        }
        let mut other = request.clone();
        other.key.sequence += 1;
        assert!(CurrentShareReply::decode(&bytes, &other).is_err());
        other = request.clone();
        other.operation = Operation::Leave { phase: [3; 16] };
        assert!(CurrentShareReply::decode(&bytes, &other).is_err());
    }
    #[test]
    fn phase_direction_version_bindings_and_terminals_do_not_convert_to_bank_authority() {
        let key = Key { root_attempt: [1; 16], invocation_sha256: [2; 32], sequence: 1 };
        let request = Request {
            key,
            operation: Operation::Enter {
                phase: [3; 16],
                kind: Kind::BuildScript,
                gnu: FileIdentity { device: 4, inode: 5 },
            },
        };
        let bytes = request.encode().unwrap();
        assert_eq!(Request::decode(&bytes).unwrap(), request);
        assert!(
            super::super::bank::Reply::decode(
                &bytes,
                &super::super::bank::Request {
                    key,
                    operation: super::super::bank::Operation::Primary {
                        member_attempt: [3; 16],
                        slot: 0
                    }
                }
            )
            .is_err()
        );
        assert_eq!(request.description_count(), 2);
        let reply = Reply {
            key,
            decision: Decision::Ready {
                phase: [3; 16],
                reserved_domain: 7,
                gnu: FileIdentity { device: 4, inode: 5 },
            },
        };
        let bytes = reply.encode().unwrap();
        assert_eq!(Reply::decode(&bytes, &request).unwrap(), reply);
        for index in 0..bytes.len() {
            assert!(Reply::decode(&bytes[..index], &request).is_err());
        }
        for change in 0..5 {
            let mut other = request.clone();
            match change {
                0 => other.key.root_attempt = [4; 16],
                1 => other.key.invocation_sha256 = [4; 32],
                2 => other.key.sequence = 2,
                3 => other.operation = Operation::Leave { phase: [3; 16] },
                _ => other.operation = Operation::Drained,
            };
            assert!(Reply::decode(&bytes, &other).is_err());
        }
        let drained = Request { key, operation: Operation::Drained };
        assert_eq!(drained.description_count(), 0);
        let terminal = Reply { key, decision: Decision::Drained }.encode().unwrap();
        assert!(Reply::decode(&terminal, &drained).is_ok());
        assert!(Reply::decode(&terminal, &request).is_err());
    }
}
