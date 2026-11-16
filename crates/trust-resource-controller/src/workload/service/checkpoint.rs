//! One original live graph checkpoint. A matching ACK only continues that
//! graph; these data never qualify or reconstruct an executable/output owner.
use super::*;
use crate::accounting::Observation;
use crate::{CompletionCause, Outcome};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Action {
    Inventory,
    Sample { repetition: u32 },
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Artifact {
    pub target: u32,
    pub executable: MetadataFile,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Capture {
    pub started: bool,
    pub outcome: Option<Outcome>,
    pub cause: Option<CompletionCause>,
    pub runtime_ns: Option<u64>,
    pub retirement_confirmed: bool,
    pub accounting: Option<Observation>,
    /// Actual native member binding when the owner observed it. Absence is
    /// never inferred into a completed native action or measured zero.
    pub member_attempt: Option<[u8; 16]>,
    pub failure: Option<String>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Body {
    Compiled {
        succeeded: bool,
        workers_retired: bool,
        output_complete: bool,
        jobs: u32,
        artifacts: Vec<Artifact>,
        failure: Option<String>,
    },
    Harness {
        target: u32,
        action: Action,
        capture: Capture,
    },
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Checkpoint {
    pub binding: Binding,
    pub sequence: u64,
    pub body: Body,
}

fn flag(d: &mut Decoder<'_>) -> io::Result<bool> {
    match d.number()? {
        0 => Ok(false),
        1 => Ok(true),
        _ => Err(invalid()),
    }
}
fn text(e: &mut Encoder, value: &Option<String>) -> io::Result<()> {
    match value {
        None => e.number(0),
        Some(value) => {
            if value.is_empty() || value.len() > 4096 || value.contains('\0') {
                return Err(invalid());
            }
            e.number(1);
            e.bytes(value.as_bytes())?;
        }
    }
    Ok(())
}
fn text_read(d: &mut Decoder<'_>) -> io::Result<Option<String>> {
    match d.number()? {
        0 => Ok(None),
        1 => Ok(Some(d.text()?)),
        _ => Err(invalid()),
    }
}
fn optional(e: &mut Encoder, value: Option<u64>) {
    e.number(u64::from(value.is_some()));
    if let Some(value) = value {
        e.number(value);
    }
}
fn optional_read(d: &mut Decoder<'_>) -> io::Result<Option<u64>> {
    match d.number()? {
        0 => Ok(None),
        1 => Ok(Some(d.number()?)),
        _ => Err(invalid()),
    }
}
impl Capture {
    pub(crate) fn write(&self, e: &mut Encoder, root: [u8; 16]) -> io::Result<()> {
        e.number(u64::from(self.started));
        match self.outcome {
            None => e.number(0),
            Some(Outcome::Exit(code)) => {
                e.number(1);
                e.number(code as u32 as u64);
            }
            Some(Outcome::Signal(signal)) => {
                if signal <= 0 {
                    return Err(invalid());
                }
                e.number(2);
                e.number(signal as u64);
            }
        }
        e.number(match self.cause {
            None => 0,
            Some(CompletionCause::Exited) => 1,
            Some(CompletionCause::Timeout) => 2,
            Some(CompletionCause::Cancelled) => 3,
            Some(CompletionCause::ResourceLimit) => 4,
            Some(CompletionCause::HostFault) => 5,
        });
        optional(e, self.runtime_ns);
        e.number(u64::from(self.retirement_confirmed));
        match self.accounting {
            None => e.number(0),
            Some(value) => {
                e.number(1);
                e.frame_bytes(&value.encode()?)?;
            }
        }
        match self.member_attempt {
            None => e.number(0),
            Some(member) => {
                if member == [0; 16] || member == root {
                    return Err(invalid());
                }
                e.number(1);
                e.0.extend(member);
            }
        }
        text(e, &self.failure)
    }
    pub(crate) fn read(d: &mut Decoder<'_>) -> io::Result<Self> {
        let started = flag(d)?;
        let outcome = match d.number()? {
            0 => None,
            1 => Some(Outcome::Exit(d.narrow()? as i32)),
            2 => Some(Outcome::Signal(i32::try_from(d.number()?).map_err(|_| invalid())?)),
            _ => return Err(invalid()),
        };
        let cause = match d.number()? {
            0 => None,
            1 => Some(CompletionCause::Exited),
            2 => Some(CompletionCause::Timeout),
            3 => Some(CompletionCause::Cancelled),
            4 => Some(CompletionCause::ResourceLimit),
            5 => Some(CompletionCause::HostFault),
            _ => return Err(invalid()),
        };
        let runtime_ns = optional_read(d)?;
        let retirement_confirmed = flag(d)?;
        let accounting = match d.number()? {
            0 => None,
            1 => Some(Observation::decode(&d.frame_bytes()?)?),
            _ => return Err(invalid()),
        };
        let member_attempt = match d.number()? {
            0 => None,
            1 => Some(d.array()?),
            _ => return Err(invalid()),
        };
        Ok(Self {
            started,
            outcome,
            cause,
            runtime_ns,
            retirement_confirmed,
            accounting,
            member_attempt,
            failure: text_read(d)?,
        })
    }
}
impl Checkpoint {
    pub fn validate(&self, invocation: &WorkloadInvocation) -> io::Result<()> {
        invocation.validate()?;
        match &self.body {
            Body::Compiled {
                succeeded, workers_retired, output_complete, jobs, artifacts, ..
            } => {
                if self.sequence != 1 || *jobs == 0 || *jobs > 7 || artifacts.len() > 2 {
                    return Err(invalid());
                }
                let mut targets = std::collections::BTreeSet::new();
                for artifact in artifacts {
                    if artifact.target >= 2 || !targets.insert(artifact.target) {
                        return Err(invalid());
                    }
                    artifact.executable.validate(&invocation.output_root)?;
                }
                if *succeeded && (!workers_retired || !output_complete || targets.len() != 2) {
                    return Err(invalid());
                }
            }
            Body::Harness { target, action, .. } => {
                if *target >= 2 {
                    return Err(invalid());
                }
                let expected = match action {
                    Action::Inventory => 2 + u64::from(*target),
                    Action::Sample { repetition } => {
                        if !(1..=invocation.repetitions).contains(repetition) {
                            return Err(invalid());
                        }
                        3 + u64::from(*target) * u64::from(invocation.repetitions)
                            + u64::from(*repetition)
                    }
                };
                if self.sequence != expected {
                    return Err(invalid());
                }
            }
        }
        Ok(())
    }
    pub fn encode(&self, invocation: &WorkloadInvocation) -> io::Result<Vec<u8>> {
        self.validate(invocation)?;
        let mut e = Encoder::new(42);
        e.number(1);
        self.binding.write(&mut e)?;
        e.number(self.sequence);
        match &self.body {
            Body::Compiled {
                succeeded,
                workers_retired,
                output_complete,
                jobs,
                artifacts,
                failure,
            } => {
                e.number(0);
                for value in [*succeeded, *workers_retired, *output_complete] {
                    e.number(u64::from(value));
                }
                e.number((*jobs).into());
                e.number(artifacts.len() as u64);
                for artifact in artifacts {
                    e.number(artifact.target.into());
                    file_write(&mut e, &artifact.executable)?;
                }
                text(&mut e, failure)?;
            }
            Body::Harness { target, action, capture } => {
                e.number(1);
                e.number((*target).into());
                match action {
                    Action::Inventory => e.number(0),
                    Action::Sample { repetition } => {
                        e.number(1);
                        e.number((*repetition).into());
                    }
                }
                capture.write(&mut e, self.binding.root_attempt)?;
            }
        }
        e.finish()
    }
    pub fn decode(
        bytes: &[u8],
        expected: &Binding,
        invocation: &WorkloadInvocation,
    ) -> io::Result<Self> {
        let mut d = header(bytes, 42)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let binding = Binding::read(&mut d)?;
        let sequence = d.number()?;
        let body = match d.number()? {
            0 => {
                let succeeded = flag(&mut d)?;
                let workers_retired = flag(&mut d)?;
                let output_complete = flag(&mut d)?;
                let jobs = d.narrow()?;
                let mut artifacts = Vec::new();
                for _ in 0..d.count(2)? {
                    artifacts.push(Artifact {
                        target: d.narrow()?,
                        executable: file_read(&mut d, invocation)?,
                    });
                }
                Body::Compiled {
                    succeeded,
                    workers_retired,
                    output_complete,
                    jobs,
                    artifacts,
                    failure: text_read(&mut d)?,
                }
            }
            1 => {
                let target = d.narrow()?;
                let action = match d.number()? {
                    0 => Action::Inventory,
                    1 => Action::Sample { repetition: d.narrow()? },
                    _ => return Err(invalid()),
                };
                Body::Harness { target, action, capture: Capture::read(&mut d)? }
            }
            _ => return Err(invalid()),
        };
        d.done()?;
        let value = Self { binding, sequence, body };
        value.binding.check(expected)?;
        value.encode(invocation)?;
        Ok(value)
    }
}
