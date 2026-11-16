//! Finite root output DATA. Metadata JSON is an explicit semantic component;
//! the outer actual stdout/stderr/entry argv remain separate producer facts.
use super::*;
use crate::wire::{Decoder, resolver_report_header};
use crate::{
    CommandSpec, MetadataCompletion, MetadataFailureObservation, MetadataPrepared, MetadataResult,
    MetadataRunnerObservation, Status, StatusFrame,
};
pub const RESOLVER_REPORT_MAX_BYTES: usize = 96 * 1024 * 1024;

/// Actual attempted semantic command and its completed or incomplete evidence.
/// No private Request capability is serialized into this observation.
#[derive(Clone, PartialEq, Eq)]
pub struct ResolverQueryObservation {
    pub command: CommandSpec,
    pub member_attempt: [u8; 16],
    /// Intercepted ProcessBuilder effective environment, with named private
    /// channels omitted. This is distinct from the forwarded semantic env and
    /// never attests the host-injected kernel child custody environment.
    pub observed_environment: Vec<(Vec<u8>, Vec<u8>)>,
    pub omitted_environment: Vec<Vec<u8>>,
    pub result: Option<MetadataResult>,
    pub failure_started: Option<StatusFrame>,
    pub failure_observation: Option<MetadataFailureObservation>,
    pub failure: Option<String>,
}
#[derive(Clone, PartialEq, Eq)]
pub struct ResolverReport {
    pub invocation: ResolverInvocation,
    pub runner: Option<MetadataRunnerObservation>,
    pub queries: Vec<ResolverQueryObservation>,
    /// Exact normal full metadata JSON bytes, not the entry's envelope stdout.
    pub metadata: Option<Vec<u8>>,
    pub failure: Option<String>,
}
pub(crate) fn is_private_environment(name: &[u8]) -> bool {
    matches!(
        name,
        b"ATERM_RESOURCE_JOB_V3"
            | b"TRUST_JOBSERVER_HANDOFF"
            | b"TRUST_TARGO_NESTED_UNVERIFIED_ENDPOINT"
            | b"TRUST_TARGO_NESTED_UNVERIFIED_BROKER"
    )
}
fn text(value: &str) -> bool {
    !value.is_empty() && value.len() <= 4096 && !value.contains('\0')
}
fn flag(d: &mut Decoder<'_>) -> io::Result<bool> {
    match d.number()? {
        0 => Ok(false),
        1 => Ok(true),
        _ => Err(invalid()),
    }
}
fn optional_text(e: &mut Encoder, value: &Option<String>) -> io::Result<()> {
    match value {
        None => e.number(0),
        Some(s) => {
            if !text(s) {
                return Err(invalid());
            }
            e.number(1);
            e.bytes(s.as_bytes())?;
        }
    }
    Ok(())
}
fn read_text(d: &mut Decoder<'_>) -> io::Result<Option<String>> {
    if flag(d)? {
        let value = d.text()?;
        if !text(&value) {
            return Err(invalid());
        }
        Ok(Some(value))
    } else {
        Ok(None)
    }
}
fn command(e: &mut Encoder, c: &CommandSpec) -> io::Result<()> {
    if c.args.len() > 128
        || c.environment.len() > 128
        || c.program.is_empty()
        || c.program.len() > 4096
        || c.program.contains(&0)
        || !path(&c.cwd)
    {
        return Err(invalid());
    }
    e.bytes(&c.program)?;
    match &c.arg0 {
        None => e.number(0),
        Some(a) => {
            e.number(1);
            e.bytes(a)?;
        }
    }
    e.number(c.args.len() as u64);
    for a in &c.args {
        e.bytes(a)?;
    }
    e.number(c.environment.len() as u64);
    for (k, v) in &c.environment {
        e.bytes(k)?;
        e.bytes(v)?;
    }
    e.bytes(&c.cwd)
}
fn read_command(d: &mut Decoder<'_>) -> io::Result<CommandSpec> {
    let program = d.bytes()?;
    let arg0 = if flag(d)? { Some(d.bytes()?) } else { None };
    let mut args = Vec::new();
    for _ in 0..d.count(128)? {
        args.push(d.bytes()?);
    }
    let mut environment = Vec::new();
    for _ in 0..d.count(128)? {
        environment.push((d.bytes()?, d.bytes()?));
    }
    Ok(CommandSpec { program, arg0, args, environment, cwd: d.bytes()? })
}
impl ResolverQueryObservation {
    fn encode(&self) -> io::Result<Vec<u8>> {
        let mut e = Encoder::new(34);
        e.number(2);
        command(&mut e, &self.command)?;
        e.0.extend(self.member_attempt);
        if self.observed_environment.len() > 128 || self.omitted_environment.len() > 32 {
            return Err(invalid());
        }
        e.number(self.observed_environment.len() as u64);
        for (name, value) in &self.observed_environment {
            e.bytes(name)?;
            e.bytes(value)?;
        }
        e.number(self.omitted_environment.len() as u64);
        for name in &self.omitted_environment {
            e.bytes(name)?;
        }
        match &self.result {
            None => e.number(0),
            Some(result) => {
                e.number(1);
                e.0.extend(result.prepared.root_attempt);
                e.frame_bytes(&result.prepared.encode()?)?;
                e.bytes(
                    &StatusFrame {
                        root_attempt: result.prepared.root_attempt,
                        member_attempt: self.member_attempt,
                        status: Status::Started(result.started),
                    }
                    .encode()?,
                )?;
                e.bytes(&result.completion.encode()?)?;
                e.bytes(&result.stdout)?;
                e.bytes(&result.stderr)?;
                e.number(u64::from(result.output_limit_exceeded));
            }
        }
        match &self.failure_started {
            None => e.number(0),
            Some(started) => {
                e.number(1);
                e.0.extend(started.root_attempt);
                e.bytes(&started.encode()?)?;
            }
        }
        match &self.failure_observation {
            None => e.number(0),
            Some(failed) => {
                e.number(1);
                e.frame_bytes(&failed.encode()?)?;
            }
        }
        optional_text(&mut e, &self.failure)?;
        e.finish()
    }
    fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 34)?;
        if d.number()? != 2 {
            return Err(invalid());
        }
        let command = read_command(&mut d)?;
        let member_attempt = d.array()?;
        let mut observed_environment = Vec::new();
        for _ in 0..d.count(128)? {
            observed_environment.push((d.bytes()?, d.bytes()?));
        }
        let mut omitted_environment = Vec::new();
        for _ in 0..d.count(32)? {
            omitted_environment.push(d.bytes()?);
        }
        let result = if flag(&mut d)? {
            let root = d.array()?;
            let prepared = MetadataPrepared::decode(&d.frame_bytes()?, root, member_attempt)?;
            let started = StatusFrame::decode(&d.bytes()?, root, member_attempt)?;
            let Status::Started(started) = started.status else {
                return Err(invalid());
            };
            let completion = MetadataCompletion::decode(&d.bytes()?, root, member_attempt)?;
            Some(MetadataResult {
                prepared,
                started,
                completion,
                stdout: d.bytes()?,
                stderr: d.bytes()?,
                output_limit_exceeded: flag(&mut d)?,
            })
        } else {
            None
        };
        let failure_started = if flag(&mut d)? {
            let root = d.array()?;
            Some(StatusFrame::decode(&d.bytes()?, root, member_attempt)?)
        } else {
            None
        };
        let failure_observation = if flag(&mut d)? {
            Some(MetadataFailureObservation::decode(&d.frame_bytes()?)?)
        } else {
            None
        };
        let failure = read_text(&mut d)?;
        d.done()?;
        Ok(Self {
            command,
            member_attempt,
            observed_environment,
            omitted_environment,
            result,
            failure_started,
            failure_observation,
            failure,
        })
    }
}
impl ResolverReport {
    pub fn validate_for(&self, invocation: &ResolverInvocation) -> io::Result<()> {
        invocation.validate()?;
        if &self.invocation != invocation
            || self.queries.len() > RESOLVER_MAX_QUERIES
            || self.metadata.as_ref().is_some_and(|bytes| bytes.len() > RESOLVER_MAX_METADATA)
            || self.failure.as_ref().is_some_and(|s| !text(s))
        {
            return Err(invalid());
        }
        let root = if let Some(runner) = &self.runner {
            runner.validate_program(&invocation.program, &invocation.program_sha256)?;
            if runner.root != invocation.root {
                return Err(invalid());
            }
            Some(
                crate::ContextReply::decode_observation(&runner.context_frame)?
                    .context
                    .root_attempt,
            )
        } else {
            None
        };
        let mut members = std::collections::BTreeSet::new();
        let mut failed = false;
        for query in &self.queries {
            if failed
                || query.member_attempt == [0; 16]
                || !members.insert(query.member_attempt)
                || query.observed_environment.iter().any(|(name, _)| is_private_environment(name))
                || query.omitted_environment.iter().any(|name| !is_private_environment(name))
                || query.failure.as_ref().is_some_and(|s| !text(s))
            {
                return Err(invalid());
            }
            query.encode()?;
            if let Some(result) = &query.result {
                if root != Some(result.prepared.root_attempt)
                    || result.prepared.member_attempt != query.member_attempt
                    || result.completion.finished.root_attempt != result.prepared.root_attempt
                    || result.completion.finished.member_attempt != query.member_attempt
                    || result.prepared.root != invocation.root
                    || result.prepared.executable.path != invocation.compiler
                    || result.prepared.executable.sha256 != invocation.compiler_sha256
                    || query.command.program != invocation.compiler
                    || query.command.arg0.is_some()
                    || query.command.environment.len() != 6
                    || query
                        .command
                        .environment
                        .iter()
                        .map(|(key, _)| key)
                        .collect::<std::collections::BTreeSet<_>>()
                        .len()
                        != 6
                    || query.command.environment.iter().any(|(key, value)| match key.as_slice() {
                        b"LANG" | b"LC_ALL" => value != b"C",
                        b"CARGO" => value != &invocation.program,
                        b"RUSTC" => value != &invocation.compiler,
                        b"CARGO_HOME" => value != &invocation.cargo_home,
                        b"CARGO_CACHE_RUSTC_INFO" => value != b"0",
                        _ => true,
                    })
                    || classify_resolver_query(&query.command.args).is_err()
                    || result.stdout.len() + result.stderr.len() > RESOLVER_MAX_QUERY_OUTPUT
                    || query.failure_started.is_some()
                    || query.failure_observation.is_some()
                {
                    return Err(invalid());
                }
                failed = result.output_limit_exceeded
                    || result.completion.inputs_unchanged.is_err()
                    || !matches!(
                        result.completion.finished.status,
                        Status::Finished {
                            outcome: crate::Outcome::Exit(0),
                            cause: crate::CompletionCause::Exited,
                            ..
                        }
                    );
                if failed && query.failure.is_none() {
                    return Err(invalid());
                }
            } else {
                failed = true;
                if query.failure.is_none() {
                    return Err(invalid());
                }
            }
            for attempt in
                query.failure_started.iter().map(|s| (s.root_attempt, s.member_attempt)).chain(
                    query.failure_observation.iter().map(|s| (s.root_attempt, s.member_attempt)),
                )
            {
                if root != Some(attempt.0) || attempt.1 != query.member_attempt {
                    return Err(invalid());
                }
            }
            if query
                .failure_started
                .as_ref()
                .is_some_and(|s| !matches!(s.status, Status::Started(_)))
            {
                return Err(invalid());
            }
            failed |= query.failure.is_some();
        }
        if self.failure.is_none()
            && (root.is_none() || self.metadata.is_none() || self.queries.is_empty() || failed)
            || failed && self.failure.is_none()
        {
            return Err(invalid());
        }
        Ok(())
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.validate_for(&self.invocation)?;
        let mut e = Encoder::resolver_report();
        e.number(1);
        e.frame_bytes(&self.invocation.encode()?)?;
        match &self.runner {
            None => e.number(0),
            Some(runner) => {
                e.number(1);
                let mut nested = Encoder::new(34);
                nested.number(3);
                runner.encode(&mut nested)?;
                e.frame_bytes(&nested.finish()?)?;
            }
        }
        e.number(self.queries.len() as u64);
        for query in &self.queries {
            e.frame_bytes(&query.encode()?)?;
        }
        match &self.metadata {
            None => e.number(0),
            Some(bytes) => {
                e.number(1);
                e.resolver_metadata(bytes)?;
            }
        }
        optional_text(&mut e, &self.failure)?;
        e.finish()
    }
    pub fn decode(bytes: &[u8], invocation: &ResolverInvocation) -> io::Result<Self> {
        let mut d = resolver_report_header(bytes)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let observed = ResolverInvocation::decode(&d.frame_bytes()?)?;
        let runner = if flag(&mut d)? {
            let bytes = d.frame_bytes()?;
            let mut nested = header(&bytes, 34)?;
            if nested.number()? != 3 {
                return Err(invalid());
            }
            let runner = MetadataRunnerObservation::decode(&mut nested)?;
            nested.done()?;
            Some(runner)
        } else {
            None
        };
        let mut queries = Vec::new();
        for _ in 0..d.count(RESOLVER_MAX_QUERIES)? {
            queries.push(ResolverQueryObservation::decode(&d.frame_bytes()?)?);
        }
        let metadata = if flag(&mut d)? { Some(d.resolver_metadata()?) } else { None };
        let failure = read_text(&mut d)?;
        d.done()?;
        let report = Self { invocation: observed, runner, queries, metadata, failure };
        report.validate_for(invocation)?;
        Ok(report)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn invocation() -> ResolverInvocation {
        ResolverInvocation {
            host_store: None,
            root: b"/sealed".to_vec(),
            program: b"/sealed/bin/targo".to_vec(),
            program_sha256: [1; 32],
            compiler: b"/sealed/bin/trustc".to_vec(),
            compiler_sha256: [2; 32],
            cwd: b"/source".to_vec(),
            cargo_home: b"/cargo".to_vec(),
        }
    }
    #[test]
    fn root_metadata_component_is_lossless_above_socket_limit_without_broadening_native_frames() {
        let invocation = invocation();
        let metadata = vec![b'x'; 2 * crate::MAX_PAYLOAD];
        let report = ResolverReport {
            invocation: invocation.clone(),
            runner: None,
            queries: vec![],
            metadata: Some(metadata.clone()),
            failure: Some("partial metadata observed but root negotiation failed".into()),
        };
        let bytes = report.encode().unwrap();
        assert!(bytes.len() > crate::MAX_PAYLOAD);
        assert!(ResolverReport::decode(&bytes, &invocation).unwrap() == report);
        assert_eq!(
            ResolverReport::decode(&bytes, &invocation).unwrap().metadata.unwrap(),
            metadata
        );
        assert!(Request::decode(&bytes).is_err());
        assert!(crate::Call::decode(&bytes).is_err());
        assert!(crate::SealedMetadataRequest::decode(&bytes).is_err());
        assert_eq!(crate::MAX_PAYLOAD, 1024 * 1024);
        assert_eq!(crate::MAX_FIELD, 64 * 1024);
    }
    #[test]
    fn root_report_rejects_trailing_truncated_misbound_and_unfounded_success_data() {
        let invocation = invocation();
        let mut report = ResolverReport {
            invocation: invocation.clone(),
            runner: None,
            queries: vec![],
            metadata: None,
            failure: Some("not admitted".into()),
        };
        let bytes = report.encode().unwrap();
        for end in 0..bytes.len() {
            assert!(ResolverReport::decode(&bytes[..end], &invocation).is_err());
        }
        let mut trailing = bytes.clone();
        trailing.push(0);
        assert!(ResolverReport::decode(&trailing, &invocation).is_err());
        let mut other = invocation.clone();
        other.compiler_sha256[0] ^= 1;
        assert!(ResolverReport::decode(&bytes, &other).is_err());
        report.failure = None;
        assert!(report.encode().is_err());
        report.metadata = Some(b"{}".to_vec());
        assert!(report.encode().is_err());
    }
    #[test]
    fn failed_attempts_are_data_and_cannot_invent_terminal_retirement_or_hide_later_dispatch() {
        let invocation = invocation();
        let command = CommandSpec {
            program: invocation.compiler.clone(),
            args: vec![b"--custom".to_vec()],
            arg0: None,
            environment: vec![],
            cwd: invocation.cwd.clone(),
        };
        let failed = ResolverQueryObservation {
            command,
            member_attempt: [3; 16],
            observed_environment: vec![],
            omitted_environment: vec![],
            result: None,
            failure_started: None,
            failure_observation: None,
            failure: Some("unknown/rejected compiler query, never replay".into()),
        };
        let mut report = ResolverReport {
            invocation: invocation.clone(),
            runner: None,
            queries: vec![failed.clone()],
            metadata: None,
            failure: Some("resolver is poisoned".into()),
        };
        let bytes = report.encode().unwrap();
        assert!(ResolverReport::decode(&bytes, &invocation).unwrap() == report);
        report.queries.push(failed);
        assert!(report.encode().is_err());
        report.queries.pop();
        report.queries[0].observed_environment.push((
            b"ATERM_RESOURCE_JOB_V3".to_vec(),
            b"private authority must not be serialized".to_vec(),
        ));
        assert!(report.encode().is_err());
        report.queries[0].observed_environment.clear();
        report.queries[0].omitted_environment.push(b"UNDECLARED_OMISSION".to_vec());
        assert!(report.encode().is_err());
        report.queries[0].omitted_environment.clear();
        report.queries[0].omitted_environment.push(b"ATERM_RESOURCE_JOB_V3".to_vec());
        assert!(report.encode().is_ok());
        report.queries[0].failure = None;
        assert!(report.encode().is_err());
    }
}
