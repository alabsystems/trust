use super::*;
use crate::wire::{Decoder, Encoder, header, invalid};

/// Maximum retained prefix of the original length-framed native event stream.
pub const METADATA_EVENT_PREFIX_MAX_BYTES: usize = 64 * 1024;

/// Bounded observations from a failed client exchange. The member remains
/// unusable and its original owner must fail/cancel and retire the real scope.
/// These bytes confer no Completed, exit, release, input or proof authority.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MetadataFailureObservation {
    pub root_attempt: [u8; 16],
    pub member_attempt: [u8; 16],
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
    pub stdout_eof: bool,
    pub stderr_eof: bool,
    pub output_limit_exceeded: bool,
    /// Exact bytes actually read, including length prefixes and malformed or
    /// partial frames. A short prefix never claims a complete native record.
    pub event_prefix: Vec<u8>,
    pub event_bytes_seen: u64,
    pub capture_error: Option<String>,
}

impl MetadataFailureObservation {
    pub fn validate(&self) -> io::Result<()> {
        if self.root_attempt == [0; 16]
            || self.member_attempt == [0; 16]
            || self.root_attempt == self.member_attempt
            || self
                .stdout
                .len()
                .checked_add(self.stderr.len())
                .is_none_or(|n| n > METADATA_MAX_OUTPUT)
            || self.event_prefix.len() > METADATA_EVENT_PREFIX_MAX_BYTES
            || self.event_bytes_seen < self.event_prefix.len() as u64
            || self.event_bytes_seen > 8 * (MAX_PAYLOAD as u64 + 4)
            || (self.event_prefix.len() < METADATA_EVENT_PREFIX_MAX_BYTES
                && self.event_bytes_seen != self.event_prefix.len() as u64)
            || self.capture_error.as_ref().is_some_and(|e| e.is_empty() || e.len() > 4096)
        {
            return Err(invalid());
        }
        Ok(())
    }
    #[must_use]
    pub fn event_prefix_truncated(&self) -> bool {
        self.event_bytes_seen > self.event_prefix.len() as u64
    }
    /// Versioned report-data annex, never an execution-protocol event.
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        let mut e = Encoder::new(17);
        e.number(1);
        e.0.extend(self.root_attempt);
        e.0.extend(self.member_attempt);
        e.bytes(&self.stdout)?;
        e.bytes(&self.stderr)?;
        for value in [self.stdout_eof, self.stderr_eof, self.output_limit_exceeded] {
            e.number(u64::from(value));
        }
        e.bytes(&self.event_prefix)?;
        e.number(self.event_bytes_seen);
        match &self.capture_error {
            None => e.number(0),
            Some(error) => {
                e.number(1);
                e.bytes(error.as_bytes())?;
            }
        }
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 17)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let root_attempt = d.array()?;
        let member_attempt = d.array()?;
        let stdout = d.bytes()?;
        let stderr = d.bytes()?;
        fn boolean(d: &mut Decoder<'_>) -> io::Result<bool> {
            match d.number()? {
                0 => Ok(false),
                1 => Ok(true),
                _ => Err(invalid()),
            }
        }
        let stdout_eof = boolean(&mut d)?;
        let stderr_eof = boolean(&mut d)?;
        let output_limit_exceeded = boolean(&mut d)?;
        let event_prefix = d.bytes()?;
        let event_bytes_seen = d.number()?;
        let capture_error = match d.number()? {
            0 => None,
            1 => Some(d.text()?),
            _ => return Err(invalid()),
        };
        d.done()?;
        let value = Self {
            root_attempt,
            member_attempt,
            stdout,
            stderr,
            stdout_eof,
            stderr_eof,
            output_limit_exceeded,
            event_prefix,
            event_bytes_seen,
            capture_error,
        };
        value.validate()?;
        Ok(value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn observation() -> MetadataFailureObservation {
        MetadataFailureObservation {
            root_attempt: [1; 16],
            member_attempt: [3; 16],
            stdout: b"retained\0stdout".to_vec(),
            stderr: vec![0xff],
            stdout_eof: false,
            stderr_eof: true,
            output_limit_exceeded: false,
            event_prefix: vec![0, 0, 0, 8, 1],
            event_bytes_seen: 5,
            capture_error: None,
        }
    }
    #[test]
    fn failure_data_is_bounded_versioned_and_never_a_native_execution_event() {
        let value = observation();
        let bytes = value.encode().unwrap();
        assert_eq!(MetadataFailureObservation::decode(&bytes).unwrap(), value);
        assert!(crate::MetadataEvent::decode(&bytes, [1; 16], [3; 16]).is_err());
        assert!(crate::Request::decode(&bytes).is_err());
        assert!(crate::Call::decode(&bytes).is_err());
        let mut changed = bytes.clone();
        changed[23] = 2;
        assert!(MetadataFailureObservation::decode(&changed).is_err());
        let mut trailing = bytes;
        trailing.push(0);
        assert!(MetadataFailureObservation::decode(&trailing).is_err());
        for change in 0..5 {
            let mut invalid = value.clone();
            match change {
                0 => invalid.member_attempt = invalid.root_attempt,
                1 => invalid.stdout.resize(METADATA_MAX_OUTPUT + 1, 0),
                2 => invalid.event_bytes_seen -= 1,
                3 => invalid.event_prefix.resize(METADATA_EVENT_PREFIX_MAX_BYTES + 1, 0),
                _ => invalid.capture_error = Some(String::new()),
            }
            assert!(invalid.encode().is_err());
        }
        let mut truncated = value;
        truncated.event_prefix.resize(METADATA_EVENT_PREFIX_MAX_BYTES, 0);
        truncated.event_bytes_seen = truncated.event_prefix.len() as u64 + 100;
        assert!(truncated.event_prefix_truncated());
        assert!(truncated.encode().is_ok());
    }
}
