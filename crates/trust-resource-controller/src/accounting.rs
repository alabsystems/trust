// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Original owning-wait observations. Decoding creates no child, execution,
//! resource, retirement or measurement authority.
use std::io;

use crate::wire::{Encoder, header, invalid};
use crate::{Request, Status, StatusFrame};

pub const CAPABILITY: &str = "owning-wait-accounting-v1";
pub const PROXY_ROLE: &str = "proxy-member-accounted-v1";
pub const HELPER_ENTRY: &str = "__resource-member-accounted-v1";

/// The original child and the descendants it waited for. This excludes
/// arbitrary descendants, separate registered members and host preparation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Scope {
    ChildAndWaitedDescendantsV1,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CpuTimes {
    pub user_ns: u64,
    pub system_ns: u64,
}

/// Absent means uncollected, not zero. A collected zero remains Some(0).
/// Resident peak is the largest process's peak, never a sum of tree memory.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Observation {
    pub scope: Scope,
    pub cpu_times: Option<CpuTimes>,
    pub peak_rss_bytes: Option<u64>,
}
impl Observation {
    pub const fn uncollected() -> Self {
        Self { scope: Scope::ChildAndWaitedDescendantsV1, cpu_times: None, peak_rss_bytes: None }
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        let mut e = Encoder::new(35);
        e.number(1);
        e.number(match self.scope {
            Scope::ChildAndWaitedDescendantsV1 => 1,
        });
        match self.cpu_times {
            None => e.number(0),
            Some(cpu) => {
                e.number(1);
                e.number(cpu.user_ns);
                e.number(cpu.system_ns);
            }
        }
        match self.peak_rss_bytes {
            None => e.number(0),
            Some(bytes) => {
                e.number(1);
                e.number(bytes);
            }
        }
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 35)?;
        if d.number()? != 1 || d.number()? != 1 {
            return Err(invalid());
        }
        let cpu_times = match d.number()? {
            0 => None,
            1 => Some(CpuTimes { user_ns: d.number()?, system_ns: d.number()? }),
            _ => return Err(invalid()),
        };
        let peak_rss_bytes = match d.number()? {
            0 => None,
            1 => Some(d.number()?),
            _ => return Err(invalid()),
        };
        d.done()?;
        Ok(Self { scope: Scope::ChildAndWaitedDescendantsV1, cpu_times, peak_rss_bytes })
    }
}

/// A distinct request envelope opts into accounting without changing the
/// original command, proof binding, role or resource delegations.
#[derive(Clone, PartialEq, Eq)]
pub struct AccountedRequest {
    pub request: Request,
    pub scope: Scope,
}
impl AccountedRequest {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.request.validate()?;
        if !self.request.role.is_proxy_member() {
            return Err(invalid());
        }
        let mut e = Encoder::new(36);
        e.number(1);
        e.number(match self.scope {
            Scope::ChildAndWaitedDescendantsV1 => 1,
        });
        e.frame_bytes(&self.request.encode()?)?;
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 36)?;
        if d.number()? != 1 || d.number()? != 1 {
            return Err(invalid());
        }
        let request = Request::decode(&d.frame_bytes()?)?;
        d.done()?;
        let result = Self { request, scope: Scope::ChildAndWaitedDescendantsV1 };
        result.encode()?;
        Ok(result)
    }
}

/// A negotiated caller requires this terminal wrapper. Legacy plain Finished
/// is not an accounting result. Actual exit/signal/cause survives absent data.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TerminalFrame {
    pub finished: StatusFrame,
    pub observation: Observation,
}
impl TerminalFrame {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        match &self.finished.status {
            Status::Finished { .. } => {}
            Status::Refused { .. } if self.observation == Observation::uncollected() => {}
            _ => return Err(invalid()),
        }
        let mut e = Encoder::new(37);
        e.number(1);
        e.frame_bytes(&self.finished.encode()?)?;
        e.frame_bytes(&self.observation.encode()?)?;
        e.finish()
    }
    pub fn decode(bytes: &[u8], root: [u8; 16], member: [u8; 16]) -> io::Result<Self> {
        let mut d = header(bytes, 37)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let finished = StatusFrame::decode(&d.frame_bytes()?, root, member)?;
        let observation = Observation::decode(&d.frame_bytes()?)?;
        d.done()?;
        let result = Self { finished, observation };
        result.encode()?;
        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CompletionCause, Outcome};

    fn finished() -> StatusFrame {
        StatusFrame {
            root_attempt: [1; 16],
            member_attempt: [2; 16],
            status: Status::Finished {
                outcome: Outcome::Exit(7),
                cause: CompletionCause::Exited,
                runtime_ns: 123,
            },
        }
    }
    #[test]
    fn uncollected_and_observed_zero_remain_distinct_with_exact_scope() {
        let missing = Observation::uncollected();
        let zero = Observation {
            cpu_times: Some(CpuTimes { user_ns: 0, system_ns: 0 }),
            peak_rss_bytes: Some(0),
            ..missing
        };
        assert_ne!(missing.encode().unwrap(), zero.encode().unwrap());
        for observation in [missing, zero] {
            let bytes = observation.encode().unwrap();
            assert_eq!(Observation::decode(&bytes).unwrap(), observation);
            for end in 0..bytes.len() {
                assert!(Observation::decode(&bytes[..end]).is_err());
            }
            let mut unknown_scope = bytes.clone();
            unknown_scope[31] = 2;
            assert!(Observation::decode(&unknown_scope).is_err());
            let mut trailing = bytes;
            trailing.push(0);
            assert!(Observation::decode(&trailing).is_err());
        }
    }
    #[test]
    fn accounted_terminal_preserves_failure_and_rejects_legacy_or_misbound_frames() {
        let plain = finished();
        let terminal =
            TerminalFrame { finished: plain.clone(), observation: Observation::uncollected() };
        let bytes = terminal.encode().unwrap();
        assert_eq!(TerminalFrame::decode(&bytes, [1; 16], [2; 16]).unwrap(), terminal);
        assert!(StatusFrame::decode(&bytes, [1; 16], [2; 16]).is_err());
        assert!(TerminalFrame::decode(&plain.encode().unwrap(), [1; 16], [2; 16]).is_err());
        assert!(TerminalFrame::decode(&bytes, [1; 16], [3; 16]).is_err());
        let mut invented = terminal;
        invented.finished.status = Status::Refused { reason: "no child".into() };
        invented.observation.cpu_times = Some(CpuTimes { user_ns: 0, system_ns: 0 });
        assert!(invented.encode().is_err());
    }
}
