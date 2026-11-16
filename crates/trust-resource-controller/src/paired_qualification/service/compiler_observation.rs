//! Checked compiler cost observations are DATA, never cache or proof authority.
//! Ready61/v2 declares the mandatory report projection62/v3 before project work.
use super::*;

pub const VERSION: u64 = 1;
pub const MAX_UNITS: u64 = 65_536;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ready {
    pub original: super::Ready,
}
impl Ready {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        let mut e = Encoder::new(61);
        e.number(2);
        e.number(VERSION);
        e.bytes(&self.original.encode()?)?;
        e.finish()
    }
    pub fn decode(bytes: &[u8], digest: [u8; 32]) -> io::Result<Self> {
        let mut d = header(bytes, 61)?;
        if d.number()? != 2 || d.number()? != VERSION {
            return Err(invalid());
        }
        let original = super::Ready::decode(&d.bytes()?, digest)?;
        d.done()?;
        Ok(Self { original })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GraphOutcome {
    Succeeded,
    Failed,
    Cancelled,
}

/// Original compilation-unit denominator, separate from verifier/test actions.
/// A dirty classification may become fresh under its lock; only physical
/// UnitStarted + owning-wait + full outcome evidence can count a process.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Counts {
    pub graph_outcome: GraphOutcome,
    pub registered: u64,
    pub scheduled: u64,
    pub scheduled_fresh: u64,
    pub completed: u64,
    pub succeeded: u64,
    pub failed: u64,
    pub tolerated_failure: u64,
    pub cancelled: u64,
    pub not_executed: u64,
    pub rusage_requested: Option<bool>,
    pub successful_primary_processes: Option<u64>,
    pub observed_successful_units: u64,
    pub unmeasured_starts: u64,
    pub completed_without_start: u64,
}
impl Counts {
    pub fn validate(&self) -> io::Result<()> {
        let summed = self
            .succeeded
            .checked_add(self.failed)
            .and_then(|n| n.checked_add(self.tolerated_failure))
            .and_then(|n| n.checked_add(self.cancelled));
        if self.registered > MAX_UNITS
            || self.scheduled.checked_add(self.not_executed) != Some(self.registered)
            || self.completed > self.scheduled
            || self.scheduled_fresh > self.scheduled
            || summed != Some(self.completed)
            || self.observed_successful_units > self.succeeded
            || self
                .observed_successful_units
                .checked_add(self.unmeasured_starts)
                .and_then(|n| n.checked_add(self.completed_without_start))
                .is_none_or(|n| n > self.scheduled)
            || self
                .observed_successful_units
                .checked_add(self.completed_without_start)
                .is_none_or(|n| n > self.succeeded)
            || (self.graph_outcome == GraphOutcome::Succeeded
                && (self.completed != self.scheduled || self.failed != 0 || self.cancelled != 0))
            || self.successful_primary_processes.is_some_and(|count| {
                count != self.observed_successful_units
                    || self.unmeasured_starts != 0
                    || self.graph_outcome != GraphOutcome::Succeeded
                    || self.rusage_requested.is_none()
            })
        {
            return Err(invalid());
        }
        Ok(())
    }
    fn write(&self, e: &mut Encoder) -> io::Result<()> {
        self.validate()?;
        e.number(match self.graph_outcome {
            GraphOutcome::Succeeded => 0,
            GraphOutcome::Failed => 1,
            GraphOutcome::Cancelled => 2,
        });
        for n in [
            self.registered,
            self.scheduled,
            self.scheduled_fresh,
            self.completed,
            self.succeeded,
            self.failed,
            self.tolerated_failure,
            self.cancelled,
            self.not_executed,
        ] {
            e.number(n);
        }
        e.number(match self.rusage_requested {
            None => 0,
            Some(false) => 1,
            Some(true) => 2,
        });
        e.number(u64::from(self.successful_primary_processes.is_some()));
        if let Some(n) = self.successful_primary_processes {
            e.number(n);
        }
        for n in
            [self.observed_successful_units, self.unmeasured_starts, self.completed_without_start]
        {
            e.number(n);
        }
        Ok(())
    }
    fn read(d: &mut Decoder<'_>) -> io::Result<Self> {
        let graph_outcome = match d.number()? {
            0 => GraphOutcome::Succeeded,
            1 => GraphOutcome::Failed,
            2 => GraphOutcome::Cancelled,
            _ => return Err(invalid()),
        };
        let mut n = [0; 9];
        for n in &mut n {
            *n = d.number()?;
        }
        let rusage_requested = match d.number()? {
            0 => None,
            1 => Some(false),
            2 => Some(true),
            _ => return Err(invalid()),
        };
        let successful_primary_processes = if flag(d)? { Some(d.number()?) } else { None };
        let value = Self {
            graph_outcome,
            registered: n[0],
            scheduled: n[1],
            scheduled_fresh: n[2],
            completed: n[3],
            succeeded: n[4],
            failed: n[5],
            tolerated_failure: n[6],
            cancelled: n[7],
            not_executed: n[8],
            rusage_requested,
            successful_primary_processes,
            observed_successful_units: d.number()?,
            unmeasured_starts: d.number()?,
            completed_without_start: d.number()?,
        };
        value.validate()?;
        Ok(value)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Observation {
    pub binding: Binding,
    pub node: Node,
    pub run_id: Option<String>,
    pub report_bytes: u64,
    pub report_sha256: [u8; 32],
    pub counts: Option<Counts>,
    pub unavailable: Option<String>,
}
impl Observation {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        if !self.node.is_compile()
            || self.report_bytes > MAX_STREAM_BYTES
            || self.counts.is_some() == self.unavailable.is_some()
            || (self.counts.is_some() && (self.run_id.is_none() || self.report_bytes == 0))
            || self
                .run_id
                .as_ref()
                .is_some_and(|s| s.is_empty() || s.len() > 512 || s.contains('\0'))
        {
            return Err(invalid());
        }
        let mut e = Encoder::new(62);
        e.number(3);
        self.binding.write(&mut e)?;
        self.node.write(&mut e, 1)?;
        optional_text(&mut e, &self.run_id)?;
        e.number(self.report_bytes);
        e.0.extend(self.report_sha256);
        e.number(u64::from(self.counts.is_some()));
        if let Some(counts) = &self.counts {
            counts.write(&mut e)?;
        }
        optional_text(&mut e, &self.unavailable)?;
        e.finish()
    }
    pub fn decode(bytes: &[u8], binding: &Binding) -> io::Result<Self> {
        let mut d = header(bytes, 62)?;
        if d.number()? != 3 {
            return Err(invalid());
        }
        let value = Self {
            binding: Binding::read(&mut d)?,
            node: Node::read(&mut d, 1)?,
            run_id: read_text(&mut d)?,
            report_bytes: d.number()?,
            report_sha256: d.array()?,
            counts: if flag(&mut d)? { Some(Counts::read(&mut d)?) } else { None },
            unavailable: read_text(&mut d)?,
        };
        d.done()?;
        value.binding.check(binding)?;
        value.encode()?;
        Ok(value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn observation() -> Observation {
        Observation {
            binding: Binding { root_attempt: [1; 16], invocation_sha256: [2; 32] },
            node: Node::AyCompile,
            run_id: Some("original-run".into()),
            report_bytes: 100,
            report_sha256: [3; 32],
            unavailable: None,
            counts: Some(Counts {
                graph_outcome: GraphOutcome::Succeeded,
                registered: 2,
                scheduled: 2,
                scheduled_fresh: 2,
                completed: 2,
                succeeded: 2,
                failed: 0,
                tolerated_failure: 0,
                cancelled: 0,
                not_executed: 0,
                rusage_requested: Some(true),
                successful_primary_processes: Some(0),
                observed_successful_units: 0,
                unmeasured_starts: 0,
                completed_without_start: 2,
            }),
        }
    }
    #[test]
    fn explicit_zero_is_distinct_from_unavailable_and_every_byte_is_bound() {
        let original = observation();
        let bytes = original.encode().unwrap();
        assert_eq!(Observation::decode(&bytes, &original.binding).unwrap(), original);
        for n in 0..bytes.len() {
            assert!(Observation::decode(&bytes[..n], &original.binding).is_err());
        }
        let mut extra = bytes.clone();
        extra.push(0);
        assert!(Observation::decode(&extra, &original.binding).is_err());
        let mut wrong = original.binding.clone();
        wrong.root_attempt[0] ^= 1;
        assert!(Observation::decode(&bytes, &wrong).is_err());
        assert!(Registered::decode(&bytes, &original.binding, 1).is_err());
        let mut unknown = original.clone();
        unknown.counts = None;
        unknown.unavailable = Some("original report incomplete".into());
        assert_eq!(
            Observation::decode(&unknown.encode().unwrap(), &unknown.binding).unwrap().counts,
            None
        );
    }
    #[test]
    fn wrong_denominators_and_noncompile_projection_refuse() {
        let mut value = observation();
        value.counts.as_mut().unwrap().scheduled = 1;
        assert!(value.encode().is_err());
        value = observation();
        value.counts.as_mut().unwrap().unmeasured_starts = 1;
        assert!(value.encode().is_err());
        value = observation();
        value.node = Node::Strict;
        assert!(value.encode().is_err());
        value = observation();
        value.counts.as_mut().unwrap().rusage_requested = None;
        assert!(value.encode().is_err());
        value = observation();
        value.counts.as_mut().unwrap().observed_successful_units = 1;
        value.counts.as_mut().unwrap().successful_primary_processes = Some(1);
        assert!(
            value.encode().is_err(),
            "the same scheduled denominator cannot also contain two no-start successes"
        );
        value = observation();
        value.counts.as_mut().unwrap().successful_primary_processes = None;
        value.counts.as_mut().unwrap().unmeasured_starts = 1;
        assert!(
            value.encode().is_err(),
            "unmeasured starts and no-start outcomes are disjoint too"
        );
    }
    #[test]
    fn ready_revision_is_explicit_and_old_meanings_stay_closed() {
        let old = super::super::Ready {
            binding: observation().binding,
            original_root: Identity {
                pid: 2,
                birth: 3,
                birth_kind: BirthKind::MacosWallMicroseconds,
            },
            native_manifest: FileIdentity { device: 4, inode: 5 },
            reserved_domain: 28,
            dispatch_ceiling: 7,
            memory_bytes: 100,
            repetitions: 1,
        };
        let new = Ready { original: old.clone() };
        assert!(Ready::decode(&old.encode().unwrap(), old.binding.invocation_sha256).is_err());
        assert!(
            super::super::Ready::decode(&new.encode().unwrap(), old.binding.invocation_sha256)
                .is_err()
        );
        assert_eq!(
            Ready::decode(&new.encode().unwrap(), old.binding.invocation_sha256).unwrap(),
            new
        );
    }
}
