// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Reconnect DATA for one resident full-envelope dependency-input attempt.
//! No path, FD, PID, digest, reply or counter constructs an input/SDK owner,
//! launches work, refunds original GNU credit or retires the original graph.
use std::io;

use super::query::OperationKey;
use crate::wire::{Encoder, header, invalid};

pub mod work;

pub const PURPOSE: &str = "native-bootstrap-dependency-inputs-v1";
pub const MAX_WORK_NS: u64 = 900_000_000_000;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mode {
    /// The complete source-declared recipe envelope, locked and offline.
    Check,
    /// Caller-policy fetch followed by the same complete locked offline pass.
    Prepare,
}

/// The original enrolled source/output and actual Root SDK select all inputs.
/// In particular clients cannot submit a recipe subset, replacement Cargo home,
/// prepared seed path, borrowed GNU pair or a reconstructed absolute deadline.
#[derive(Clone, PartialEq, Eq)]
pub struct Request {
    pub key: OperationKey,
    pub mode: Mode,
    pub timeout_ns: u64,
}
impl Request {
    pub fn validate(&self) -> io::Result<()> {
        self.key.validate()?;
        if !matches!(self.timeout_ns, 1..=MAX_WORK_NS) {
            return Err(invalid());
        }
        Ok(())
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        let mut e = Encoder::new(150);
        e.number(1);
        self.key.write(&mut e)?;
        e.number(match self.mode {
            Mode::Check => 0,
            Mode::Prepare => 1,
        });
        e.number(self.timeout_ns);
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 150)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let key = OperationKey::read(&mut d)?;
        let mode = match d.number()? {
            0 => Mode::Check,
            1 => Mode::Prepare,
            _ => return Err(invalid()),
        };
        let value = Self { key, mode, timeout_ns: d.number()? };
        d.done()?;
        value.validate()?;
        Ok(value)
    }
    pub fn hello(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        self.key.graph.hello(PURPOSE)
    }
}

/// Progress only. A completed observation is not a portable readiness seal or
/// a resource-release witness; only the resident original operation owns those
/// transitions. Reconnection always names the same exact original Request.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Phase {
    Materializing,
    ValidatingSeed,
    Fetching,
    CheckingOffline,
    Complete,
    Quarantined,
}

#[derive(Clone, PartialEq, Eq)]
pub struct Observation {
    pub request: Request,
    pub revision: u64,
    pub phase: Phase,
    pub recipes_total: u32,
    pub recipes_finished: u32,
}
impl Observation {
    pub fn validate(&self) -> io::Result<()> {
        self.request.validate()?;
        if self.revision == 0
            || self.recipes_finished > self.recipes_total
            || (self.phase == Phase::Complete
                && (self.recipes_total == 0 || self.recipes_finished != self.recipes_total))
        {
            return Err(invalid());
        }
        Ok(())
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        let mut e = Encoder::new(151);
        e.number(1);
        e.frame_bytes(&self.request.encode()?)?;
        e.number(self.revision);
        e.number(match self.phase {
            Phase::Materializing => 0,
            Phase::ValidatingSeed => 1,
            Phase::Fetching => 2,
            Phase::CheckingOffline => 3,
            Phase::Complete => 4,
            Phase::Quarantined => 5,
        });
        e.number(self.recipes_total.into());
        e.number(self.recipes_finished.into());
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 151)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let request = Request::decode(&d.frame_bytes()?)?;
        let revision = d.number()?;
        let phase = match d.number()? {
            0 => Phase::Materializing,
            1 => Phase::ValidatingSeed,
            2 => Phase::Fetching,
            3 => Phase::CheckingOffline,
            4 => Phase::Complete,
            5 => Phase::Quarantined,
            _ => return Err(invalid()),
        };
        let value = Self {
            request,
            revision,
            phase,
            recipes_total: d.narrow()?,
            recipes_finished: d.narrow()?,
        };
        d.done()?;
        value.validate()?;
        Ok(value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ContextQuery, JobBinding};

    pub(super) fn request() -> Request {
        Request {
            key: OperationKey {
                graph: super::super::Key {
                    query: ContextQuery {
                        binding: JobBinding {
                            session: "s-abcd".into(),
                            root_attempt: [1; 16],
                            capability: [2; 32],
                        },
                        call_attempt: [3; 16],
                    },
                    graph: [4; 16],
                },
                sequence: 1,
                operation: [5; 16],
            },
            mode: Mode::Check,
            timeout_ns: MAX_WORK_NS,
        }
    }

    #[test]
    fn preparation_request_roundtrips_without_selected_paths_or_resource_handles() {
        let original = request();
        assert!(Request::decode(&original.encode().unwrap()).unwrap() == original);
        let hello = String::from_utf8(original.hello().unwrap()).unwrap();
        assert!(hello.contains(PURPOSE));
        for bytes in [0, 1, 8, 16, 32] {
            assert!(Request::decode(&original.encode().unwrap()[..bytes]).is_err());
        }
        let mut trailing = original.encode().unwrap();
        trailing.push(0);
        assert!(Request::decode(&trailing).is_err());
    }

    #[test]
    fn preparation_cannot_extend_work_budget_or_replace_original_attempt_identity() {
        let mut value = request();
        for timeout in [0, MAX_WORK_NS + 1, u64::MAX] {
            value.timeout_ns = timeout;
            assert!(value.encode().is_err());
        }
        value = request();
        value.key.operation = value.key.graph.query.binding.root_attempt;
        assert!(value.encode().is_err());
    }

    #[test]
    fn preparation_observations_keep_complete_envelope_counts_honest() {
        let mut value = Observation {
            request: request(),
            revision: 1,
            phase: Phase::Materializing,
            recipes_total: 0,
            recipes_finished: 0,
        };
        assert!(Observation::decode(&value.encode().unwrap()).unwrap() == value);
        value.phase = Phase::Complete;
        assert!(value.encode().is_err());
        value.recipes_total = 54;
        value.recipes_finished = 53;
        assert!(value.encode().is_err());
        value.recipes_finished = 54;
        assert!(Observation::decode(&value.encode().unwrap()).unwrap() == value);
        value.recipes_finished = 55;
        assert!(value.encode().is_err());
    }
}
