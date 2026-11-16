// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Bounded parent-broker DATA. Neither a frame nor a completion constructs a
//! compiler unit, native child, source validity, retirement or proof authority.
use super::*;
use crate::{CommandSpec, StatusFrame, accounting};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BrokerLimits {
    pub line_bytes: usize,
    pub stream_bytes: usize,
    pub timeout_ns: u64,
    pub capture_rusage: bool,
}
impl BrokerLimits {
    pub fn validate(&self) -> io::Result<()> {
        if self.line_bytes == 0
            || self.stream_bytes == 0
            || self.line_bytes > self.stream_bytes
            || self.stream_bytes > super::super::produced::MAX_OUTPUT_BYTES
            || self.timeout_ns == 0
            || self.timeout_ns > 86_400_000_000_000
        {
            return Err(invalid());
        }
        Ok(())
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StreamEnd {
    Pending,
    Eof,
    LeaderExitDrained,
    ReadFailed,
    LimitExceeded,
}
#[cfg(all(feature = "client", any(target_os = "linux", target_os = "macos")))]
impl StreamEnd {
    fn number(self) -> u64 {
        match self {
            Self::Pending => 0,
            Self::Eof => 1,
            Self::LeaderExitDrained => 2,
            Self::ReadFailed => 3,
            Self::LimitExceeded => 4,
        }
    }
    fn read(number: u64) -> io::Result<Self> {
        match number {
            0 => Ok(Self::Pending),
            1 => Ok(Self::Eof),
            2 => Ok(Self::LeaderExitDrained),
            3 => Ok(Self::ReadFailed),
            4 => Ok(Self::LimitExceeded),
            _ => Err(invalid()),
        }
    }
}
#[derive(Clone, Debug)]
pub struct BrokerCaptureData {
    pub started: bool,
    pub status: Option<StatusFrame>,
    pub accounting: accounting::Observation,
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
    pub stdout_end: StreamEnd,
    pub stderr_end: StreamEnd,
    pub truncated: bool,
    pub failure: Option<String>,
    pub elapsed_ns: u64,
}
/// Exact unit/output selection DATA. Only the original parent can match it
/// to its retained expected row and genuinely retired producer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PublicationSelection {
    pub unit_sha256: String,
    pub unit_id: String,
    pub destinations: Vec<Vec<u8>>,
}
impl PublicationSelection {
    pub fn retained_bytes(&self) -> Option<usize> {
        let mut bytes = std::mem::size_of::<Self>()
            .checked_add(self.unit_sha256.capacity())?
            .checked_add(self.unit_id.capacity())?
            .checked_add(
                self.destinations.capacity().checked_mul(std::mem::size_of::<Vec<u8>>())?,
            )?;
        for path in &self.destinations {
            bytes = bytes.checked_add(path.capacity())?;
        }
        Some(bytes)
    }
    fn write(&self, e: &mut Encoder) -> io::Result<()> {
        if self.unit_sha256.len() != 64
            || !self
                .unit_sha256
                .bytes()
                .all(|byte| byte.is_ascii_digit() || matches!(byte, b'a'..=b'f'))
            || self.unit_id.is_empty()
            || self.unit_id.len() > 128
            || self.unit_id.contains('\0')
            || self.destinations.len() > 4096
        {
            return Err(invalid());
        }
        let mut bytes = 0usize;
        let mut previous: Option<&Vec<u8>> = None;
        for path in &self.destinations {
            bytes = bytes.checked_add(path.len()).ok_or_else(invalid)?;
            if bytes > 1024 * 1024
                || path.len() > 4096
                || !path.starts_with(b"/")
                || path.contains(&0)
                || path
                    .split(|byte| *byte == b'/')
                    .skip(1)
                    .any(|part| part.is_empty() || matches!(part, b"." | b".."))
                || previous.is_some_and(|before| before >= path)
            {
                return Err(invalid());
            }
            previous = Some(path);
        }
        e.bytes(self.unit_sha256.as_bytes())?;
        e.bytes(self.unit_id.as_bytes())?;
        e.number(self.destinations.len() as u64);
        for path in &self.destinations {
            e.bytes(path)?;
        }
        Ok(())
    }
    fn read(d: &mut crate::wire::Decoder<'_>) -> io::Result<Self> {
        let unit_sha256 = d.text()?;
        let unit_id = d.text()?;
        let count = d.count(4096)?;
        let mut destinations = Vec::new();
        destinations.try_reserve_exact(count).map_err(|_| invalid())?;
        for _ in 0..count {
            destinations.push(d.bytes()?);
        }
        Ok(Self { unit_sha256, unit_id, destinations })
    }
    pub fn validate(&self) -> io::Result<()> {
        let mut e = Encoder::new(87);
        self.write(&mut e)?;
        e.finish().map(|_| ())
    }
}

pub enum BrokerRequest {
    FinishGraph { sequence: u64 },
    Publish { sequence: u64, selection: PublicationSelection },
    Execute { sequence: u64, command: CommandSpec, limits: BrokerLimits },
    Cancel { sequence: u64 },
}
pub(crate) fn command_write(command: &CommandSpec, e: &mut Encoder) -> io::Result<()> {
    if !command.program.starts_with(b"/")
        || !command.cwd.starts_with(b"/")
        || command.program.contains(&0)
        || command.cwd.contains(&0)
        || command.arg0.as_ref().is_some_and(|word| word.contains(&0))
        || command.args.len() > crate::MAX_ITEMS
        || command.environment.len() > crate::MAX_ITEMS
    {
        return Err(invalid());
    }
    // Bound the complete borrowed representation before the first allocation
    // or duplicate of caller-controlled command bytes.
    let mut size = 40usize;
    let mut add = |length: usize, overhead: usize| -> io::Result<()> {
        size =
            size.checked_add(length).and_then(|n| n.checked_add(overhead)).ok_or_else(invalid)?;
        if length > crate::MAX_FIELD || size > crate::MAX_PAYLOAD.saturating_sub(e.0.len()) {
            return Err(invalid());
        }
        Ok(())
    };
    add(command.program.len(), 0)?;
    add(command.cwd.len(), 0)?;
    if let Some(arg0) = &command.arg0 {
        add(arg0.len(), 8)?;
    }
    for arg in &command.args {
        add(arg.len(), 8)?;
    }
    for (key, value) in &command.environment {
        add(key.len(), 8)?;
        add(value.len(), 8)?;
    }
    e.bytes(&command.program)?;
    e.number(u64::from(command.arg0.is_some()));
    if let Some(arg0) = &command.arg0 {
        e.bytes(arg0)?;
    }
    e.bytes(&command.cwd)?;
    e.number(command.args.len() as u64);
    for arg in &command.args {
        if arg.contains(&0) {
            return Err(invalid());
        }
        e.bytes(arg)?;
    }
    let mut names = BTreeSet::new();
    e.number(command.environment.len() as u64);
    for (key, value) in &command.environment {
        if key.is_empty()
            || key.contains(&0)
            || key.contains(&b'=')
            || value.contains(&0)
            || !names.insert(key)
        {
            return Err(invalid());
        }
        e.bytes(key)?;
        e.bytes(value)?;
    }
    Ok(())
}
pub(crate) fn command_read(d: &mut crate::wire::Decoder<'_>) -> io::Result<CommandSpec> {
    let program = d.bytes()?;
    let arg0 = match d.number()? {
        0 => None,
        1 => Some(d.bytes()?),
        _ => return Err(invalid()),
    };
    let cwd = d.bytes()?;
    let mut args = Vec::new();
    for _ in 0..d.count(crate::MAX_ITEMS)? {
        args.push(d.bytes()?);
    }
    let mut environment = Vec::new();
    for _ in 0..d.count(crate::MAX_ITEMS)? {
        environment.push((d.bytes()?, d.bytes()?));
    }
    let value = CommandSpec { program, arg0, cwd, args, environment };
    command_write(&value, &mut Encoder::new(0))?;
    Ok(value)
}
impl BrokerRequest {
    pub fn encode_execute(
        sequence: u64,
        command: &CommandSpec,
        limits: BrokerLimits,
    ) -> io::Result<Vec<u8>> {
        if !(1..=65_536).contains(&sequence) {
            return Err(invalid());
        }
        limits.validate()?;
        let mut e = Encoder::new(87);
        e.number(1);
        e.number(sequence);
        e.number(0);
        command_write(command, &mut e)?;
        e.number(limits.line_bytes as u64);
        e.number(limits.stream_bytes as u64);
        e.number(limits.timeout_ns);
        e.number(u64::from(limits.capture_rusage));
        e.finish()
    }
    pub fn sequence(&self) -> u64 {
        match self {
            Self::Execute { sequence, .. }
            | Self::Cancel { sequence }
            | Self::Publish { sequence, .. }
            | Self::FinishGraph { sequence } => *sequence,
        }
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        if !(1..=65_536).contains(&self.sequence()) {
            return Err(invalid());
        }
        let mut e = Encoder::new(87);
        e.number(1);
        e.number(self.sequence());
        match self {
            Self::Execute { command, limits, .. } => {
                limits.validate()?;
                e.number(0);
                command_write(command, &mut e)?;
                e.number(limits.line_bytes as u64);
                e.number(limits.stream_bytes as u64);
                e.number(limits.timeout_ns);
                e.number(u64::from(limits.capture_rusage));
            }
            Self::Cancel { .. } => e.number(1),
            Self::FinishGraph { .. } => e.number(3),
            Self::Publish { selection, .. } => {
                e.number(2);
                selection.write(&mut e)?;
            }
        }
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 87)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let sequence = d.number()?;
        let value = match d.number()? {
            0 => Self::Execute {
                sequence,
                command: command_read(&mut d)?,
                limits: BrokerLimits {
                    line_bytes: usize::try_from(d.number()?).map_err(|_| invalid())?,
                    stream_bytes: usize::try_from(d.number()?).map_err(|_| invalid())?,
                    timeout_ns: d.number()?,
                    capture_rusage: match d.number()? {
                        0 => false,
                        1 => true,
                        _ => return Err(invalid()),
                    },
                },
            },
            1 => Self::Cancel { sequence },
            3 => Self::FinishGraph { sequence },
            2 => Self::Publish { sequence, selection: PublicationSelection::read(&mut d)? },
            _ => return Err(invalid()),
        };
        d.done()?;
        value.encode()?;
        Ok(value)
    }
}
#[cfg(all(feature = "client", any(target_os = "linux", target_os = "macos")))]
pub(crate) enum BrokerEvent {
    GraphFinished {
        sequence: u64,
        operation: [u8; 16],
        failure: Option<String>,
    },
    Published {
        sequence: u64,
        selection: PublicationSelection,
        operation: [u8; 16],
        failure: Option<String>,
    },
    Started {
        sequence: u64,
        started: bool,
    },
    Output {
        sequence: u64,
        stderr: bool,
        bytes: Vec<u8>,
    },
    Completed {
        sequence: u64,
        capture: BrokerCaptureData,
        stdout_len: u64,
        stderr_len: u64,
    },
}
#[cfg(all(feature = "client", any(target_os = "linux", target_os = "macos")))]
impl BrokerEvent {
    pub(crate) fn encode(&self) -> io::Result<Vec<u8>> {
        let mut e = Encoder::new(88);
        e.number(1);
        match self {
            Self::GraphFinished { sequence, operation, failure } => {
                if (*operation == [0; 16]) != failure.is_some()
                    || failure.as_ref().is_some_and(|text| {
                        text.is_empty() || text.len() > 4096 || text.contains('\0')
                    })
                {
                    return Err(invalid());
                }
                e.number(*sequence);
                e.number(5);
                e.0.extend(operation);
                e.number(u64::from(failure.is_some()));
                if let Some(text) = failure {
                    e.bytes(text.as_bytes())?;
                }
            }
            Self::Published { sequence, selection, operation, failure } => {
                if (*operation == [0; 16]) != failure.is_some()
                    || failure.as_ref().is_some_and(|text| {
                        text.is_empty() || text.len() > 4096 || text.contains('\0')
                    })
                {
                    return Err(invalid());
                }
                e.number(*sequence);
                e.number(4);
                selection.write(&mut e)?;
                e.0.extend(operation);
                e.number(u64::from(failure.is_some()));
                if let Some(text) = failure {
                    e.bytes(text.as_bytes())?;
                }
            }
            Self::Started { sequence, started } => {
                e.number(*sequence);
                e.number(3);
                e.number(u64::from(*started));
            }
            Self::Output { sequence, stderr, bytes } => {
                if bytes.len() > 64 * 1024 {
                    return Err(invalid());
                }
                e.number(*sequence);
                e.number(u64::from(*stderr));
                e.bytes(bytes)?;
            }
            Self::Completed { sequence, capture, stdout_len, stderr_len } => {
                e.number(*sequence);
                e.number(2);
                e.number(u64::from(capture.started));
                e.number(u64::from(capture.status.is_some()));
                if let Some(status) = &capture.status {
                    e.0.extend(status.root_attempt);
                    e.0.extend(status.member_attempt);
                    e.frame_bytes(&status.encode()?)?;
                }
                e.frame_bytes(&capture.accounting.encode()?)?;
                e.number(capture.stdout_end.number());
                e.number(capture.stderr_end.number());
                e.number(u64::from(capture.truncated));
                e.number(u64::from(capture.failure.is_some()));
                if let Some(reason) = &capture.failure {
                    e.bytes(reason.as_bytes())?;
                }
                e.number(capture.elapsed_ns);
                e.number(*stdout_len);
                e.number(*stderr_len);
            }
        }
        e.finish()
    }
    pub(crate) fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 88)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let sequence = d.number()?;
        let value = match d.number()? {
            5 => Self::GraphFinished {
                sequence,
                operation: d.array()?,
                failure: match d.number()? {
                    0 => None,
                    1 => Some(d.text()?),
                    _ => return Err(invalid()),
                },
            },
            4 => Self::Published {
                sequence,
                selection: PublicationSelection::read(&mut d)?,
                operation: d.array()?,
                failure: match d.number()? {
                    0 => None,
                    1 => Some(d.text()?),
                    _ => return Err(invalid()),
                },
            },
            3 => Self::Started {
                sequence,
                started: match d.number()? {
                    0 => false,
                    1 => true,
                    _ => return Err(invalid()),
                },
            },
            stream @ (0 | 1) => Self::Output { sequence, stderr: stream == 1, bytes: d.bytes()? },
            2 => {
                let started = match d.number()? {
                    0 => false,
                    1 => true,
                    _ => return Err(invalid()),
                };
                let status = match d.number()? {
                    0 => None,
                    1 => {
                        let root = d.array()?;
                        let member = d.array()?;
                        Some(StatusFrame::decode(&d.frame_bytes()?, root, member)?)
                    }
                    _ => return Err(invalid()),
                };
                let accounting = accounting::Observation::decode(&d.frame_bytes()?)?;
                let stdout_end = StreamEnd::read(d.number()?)?;
                let stderr_end = StreamEnd::read(d.number()?)?;
                let truncated = match d.number()? {
                    0 => false,
                    1 => true,
                    _ => return Err(invalid()),
                };
                let failure = match d.number()? {
                    0 => None,
                    1 => Some(d.text()?),
                    _ => return Err(invalid()),
                };
                let elapsed_ns = d.number()?;
                let stdout_len = d.number()?;
                let stderr_len = d.number()?;
                Self::Completed {
                    sequence,
                    capture: BrokerCaptureData {
                        started,
                        status,
                        accounting,
                        stdout: Vec::new(),
                        stderr: Vec::new(),
                        stdout_end,
                        stderr_end,
                        truncated,
                        failure,
                        elapsed_ns,
                    },
                    stdout_len,
                    stderr_len,
                }
            }
            _ => return Err(invalid()),
        };
        d.done()?;
        value.encode()?;
        Ok(value)
    }
}

#[cfg(test)]
mod publication_tests {
    use super::*;
    #[test]
    fn unit_publication_codec_binds_complete_unique_destination_set() {
        let selection = PublicationSelection {
            unit_sha256: "a".repeat(64),
            unit_id: "actual-unit-naming-data".into(),
            destinations: vec![b"/selected/debug/bin".to_vec(), b"/selected/export/bin".to_vec()],
        };
        let request = BrokerRequest::Publish { sequence: 1, selection: selection.clone() };
        let encoded = request.encode().unwrap();
        assert!(
            matches!(BrokerRequest::decode(&encoded).unwrap(),BrokerRequest::Publish{sequence:1,selection:actual}if actual==selection)
        );
        for length in 0..encoded.len() {
            assert!(BrokerRequest::decode(&encoded[..length]).is_err());
        }
        let mut duplicated = selection.clone();
        duplicated.destinations.push(duplicated.destinations[0].clone());
        assert!(duplicated.validate().is_err());
        let mut reordered = selection.clone();
        reordered.destinations.reverse();
        assert!(reordered.validate().is_err());
        let mut escaped = selection;
        escaped.destinations[0] = b"/selected/../foreign/bin".to_vec();
        assert!(escaped.validate().is_err());
    }
}
