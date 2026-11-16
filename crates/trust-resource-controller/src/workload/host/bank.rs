//! Closed requests to the ONE retained-root bank. These frames select no CPU
//! and carry no lease; a grant additionally transfers an actual original fd.
use std::io;

use crate::wire::{Decoder, Encoder, header, invalid};
use crate::{BirthKind, FileIdentity, Identity};

pub const ORIGINAL_MARKER: u8 = 0x58;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Key {
    pub root_attempt: [u8; 16],
    pub invocation_sha256: [u8; 32],
    pub sequence: u64,
}
impl Key {
    fn encode(&self, e: &mut Encoder) -> io::Result<()> {
        if self.root_attempt == [0; 16] || self.sequence == 0 {
            return Err(invalid());
        }
        e.0.extend(self.root_attempt);
        e.0.extend(self.invocation_sha256);
        e.number(self.sequence);
        Ok(())
    }
    fn decode(d: &mut Decoder<'_>) -> io::Result<Self> {
        Ok(Self { root_attempt: d.array()?, invocation_sha256: d.array()?, sequence: d.number()? })
    }
    fn member(&self, member: [u8; 16]) -> io::Result<()> {
        if member == [0; 16] || member == self.root_attempt { Err(invalid()) } else { Ok(()) }
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Operation {
    Primary {
        member_attempt: [u8; 16],
        slot: u32,
    },
    Extra {
        member_attempt: [u8; 16],
        worker_request: [u8; 16],
        producer: Identity,
    },
    /// Sent only after positive native member settlement or the trusted SDK's
    /// actual joined/quiescent worker settlement. Drop/EOF is never a return.
    Returned {
        member_attempt: [u8; 16],
        loan: [u8; 16],
        slot: u32,
    },
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Request {
    pub key: Key,
    pub operation: Operation,
}
impl Request {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        let mut e = Encoder::new(53);
        e.number(2);
        self.key.encode(&mut e)?;
        match self.operation {
            Operation::Primary { member_attempt, slot } => {
                self.key.member(member_attempt)?;
                if slot >= super::MAX_CPU_SET as u32 {
                    return Err(invalid());
                }
                e.number(0);
                e.0.extend(member_attempt);
                e.number(slot.into());
            }
            Operation::Extra { member_attempt, worker_request, producer } => {
                self.key.member(member_attempt)?;
                if worker_request == [0; 16] || producer.pid <= 1 || producer.birth == 0 {
                    return Err(invalid());
                }
                e.number(1);
                e.0.extend(member_attempt);
                e.0.extend(worker_request);
                e.number(producer.pid.into());
                e.number(producer.birth);
                e.number(match producer.birth_kind {
                    BirthKind::MacosWallMicroseconds => 0,
                    BirthKind::LinuxStartTicks => 1,
                });
            }
            Operation::Returned { member_attempt, loan, slot } => {
                self.key.member(member_attempt)?;
                if loan == [0; 16] || slot >= super::MAX_CPU_SET as u32 {
                    return Err(invalid());
                }
                e.number(2);
                e.0.extend(member_attempt);
                e.0.extend(loan);
                e.number(slot.into());
            }
        }
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 53)?;
        if d.number()? != 2 {
            return Err(invalid());
        }
        let key = Key::decode(&mut d)?;
        let operation = match d.number()? {
            0 => Operation::Primary { member_attempt: d.array()?, slot: d.narrow()? },
            1 => Operation::Extra {
                member_attempt: d.array()?,
                worker_request: d.array()?,
                producer: Identity {
                    pid: d.narrow()?,
                    birth: d.number()?,
                    birth_kind: match d.number()? {
                        0 => BirthKind::MacosWallMicroseconds,
                        1 => BirthKind::LinuxStartTicks,
                        _ => return Err(invalid()),
                    },
                },
            },
            2 => Operation::Returned {
                member_attempt: d.array()?,
                loan: d.array()?,
                slot: d.narrow()?,
            },
            _ => return Err(invalid()),
        };
        d.done()?;
        let value = Self { key, operation };
        value.encode()?;
        Ok(value)
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Decision {
    Granted { member_attempt: [u8; 16], loan: [u8; 16], slot: u32, backing: FileIdentity },
    Busy,
    Refused { reason: String },
    Returned,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Reply {
    pub key: Key,
    pub decision: Decision,
}
impl Reply {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        let mut e = Encoder::new(51);
        e.number(2);
        self.key.encode(&mut e)?;
        match &self.decision {
            Decision::Granted { member_attempt, loan, slot, backing } => {
                self.key.member(*member_attempt)?;
                if *loan == [0; 16] || *slot >= super::MAX_CPU_SET as u32 || backing.inode == 0 {
                    return Err(invalid());
                }
                e.number(0);
                e.0.extend(member_attempt);
                e.0.extend(loan);
                e.number((*slot).into());
                e.number(backing.device);
                e.number(backing.inode);
            }
            Decision::Busy => e.number(1),
            Decision::Refused { reason } => {
                if reason.is_empty() || reason.len() > 4096 || reason.contains('\0') {
                    return Err(invalid());
                }
                e.number(2);
                e.bytes(reason.as_bytes())?;
            }
            Decision::Returned => e.number(3),
        }
        e.finish()
    }
    pub fn decode(bytes: &[u8], request: &Request) -> io::Result<Self> {
        let mut d = header(bytes, 51)?;
        if d.number()? != 2 {
            return Err(invalid());
        }
        let key = Key::decode(&mut d)?;
        if key != request.key {
            return Err(invalid());
        }
        let decision = match d.number()? {
            0 => Decision::Granted {
                member_attempt: d.array()?,
                loan: d.array()?,
                slot: d.narrow()?,
                backing: FileIdentity { device: d.number()?, inode: d.number()? },
            },
            1 => Decision::Busy,
            2 => {
                Decision::Refused { reason: String::from_utf8(d.bytes()?).map_err(|_| invalid())? }
            }
            3 => Decision::Returned,
            _ => return Err(invalid()),
        };
        d.done()?;
        let value = Self { key, decision };
        value.encode()?;
        match (&request.operation, &value.decision) {
            (
                Operation::Primary { member_attempt, slot },
                Decision::Granted { member_attempt: got, slot: actual, .. },
            ) if member_attempt == got && slot == actual => {}
            (
                Operation::Extra { member_attempt, .. },
                Decision::Granted { member_attempt: got, .. },
            ) if member_attempt == got => {}
            (Operation::Returned { .. }, Decision::Returned) => {}
            (_, Decision::Refused { .. }) => {}
            (Operation::Primary { .. } | Operation::Extra { .. }, Decision::Busy) => {}
            _ => return Err(invalid()),
        }
        Ok(value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn bank_reply_binds_original_root_invocation_sequence_member_and_selected_slot() {
        let request = Request {
            key: Key { root_attempt: [1; 16], invocation_sha256: [2; 32], sequence: 1 },
            operation: Operation::Primary { member_attempt: [3; 16], slot: 2 },
        };
        let encoded = request.encode().unwrap();
        assert_eq!(Request::decode(&encoded).unwrap(), request);
        let reply = Reply {
            key: request.key,
            decision: Decision::Granted {
                member_attempt: [3; 16],
                loan: [4; 16],
                slot: 2,
                backing: FileIdentity { device: 5, inode: 6 },
            },
        };
        let bytes = reply.encode().unwrap();
        assert_eq!(Reply::decode(&bytes, &request).unwrap(), reply);
        for change in 0..5 {
            let mut other = request.clone();
            match change {
                0 => other.key.root_attempt = [7; 16],
                1 => other.key.invocation_sha256 = [7; 32],
                2 => other.key.sequence = 2,
                3 => other.operation = Operation::Primary { member_attempt: [7; 16], slot: 2 },
                4 => other.operation = Operation::Primary { member_attempt: [3; 16], slot: 3 },
                _ => unreachable!(),
            };
            assert!(Reply::decode(&bytes, &other).is_err());
        }
        for count in 0..bytes.len() {
            assert!(Reply::decode(&bytes[..count], &request).is_err());
        }
    }
    #[test]
    fn worker_return_cannot_be_a_grant_busy_or_plain_legacy_terminal() {
        let request = Request {
            key: Key { root_attempt: [1; 16], invocation_sha256: [2; 32], sequence: 2 },
            operation: Operation::Returned { member_attempt: [3; 16], loan: [4; 16], slot: 1 },
        };
        let good = Reply { key: request.key, decision: Decision::Returned };
        assert_eq!(Reply::decode(&good.encode().unwrap(), &request).unwrap(), good);
        let busy = Reply { key: request.key, decision: Decision::Busy };
        assert!(Reply::decode(&busy.encode().unwrap(), &request).is_err());
        let mut zero = request.clone();
        zero.key.sequence = 0;
        assert!(zero.encode().is_err());
        assert!(Request::decode(&good.encode().unwrap()).is_err());
    }
}
