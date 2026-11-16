//! Stream actual target output while its custodian retains lifecycle ownership.
use super::*;

#[cfg(all(test, target_os = "macos", target_arch = "aarch64"))]
mod raw_evidence_tests {
    use super::*;
    use crate::ops::cargo_test::workload::evidence::tests::native::Fixture;

    #[test]
    fn partial_lines_and_synthetic_final_callback_preserve_each_raw_byte_once() {
        let directory = tempfile::tempdir().unwrap();
        let fixture = Fixture::at(directory.path());
        let evidence = fixture.action(4096);
        let mut lines = Vec::new();
        let mut callback = |line: &str| {
            lines.push(line.to_owned());
            Ok(())
        };
        let mut stream = Stream {
            callback: &mut callback,
            capture: false,
            output: Vec::new(),
            completed: 0,
            line_limit: 1024,
            stream_limit: 4096,
            failure: None,
            evidence: Some(evidence.clone()),
            is_stdout: true,
            buffered: 0,
        };
        let mut bytes = b"part".to_vec();
        assert_eq!(stream.accept(&mut bytes, false), Read2Action::Continue);
        assert_eq!(bytes, b"part");
        bytes.extend_from_slice(b"ial\nagain");
        assert_eq!(stream.accept(&mut bytes, false), Read2Action::Continue);
        assert_eq!(bytes, b"again");
        // Positive Drain may finalize the partial line without a physical
        // read(0); it must not duplicate its already-observed raw bytes.
        assert_eq!(stream.accept(&mut bytes, true), Read2Action::Continue);
        assert!(bytes.is_empty());
        assert_eq!(fixture.raw("stdout"), b"partial\nagain");
        assert_eq!(evidence.stdout.received(), 13);
        assert_eq!(evidence.stdout.persisted(), 13);
        assert_eq!(lines, ["partial", "again"]);
    }

    #[test]
    fn actual_received_prefix_precedes_utf8_or_callback_failure() {
        for utf8 in [false, true] {
            let directory = tempfile::tempdir().unwrap();
            let fixture = Fixture::at(directory.path());
            let evidence = fixture.action(4096);
            let mut callback = |_: &str| anyhow::bail!("controlled compiler observer error");
            let mut stream = Stream {
                callback: &mut callback,
                capture: true,
                output: Vec::new(),
                completed: 0,
                line_limit: 1024,
                stream_limit: 4096,
                failure: None,
                evidence: Some(evidence.clone()),
                is_stdout: true,
                buffered: 0,
            };
            let input: &[u8] = if utf8 {
                b"actual binary\xff\n"
            } else {
                b"actual callback\0line\n"
            };
            let mut bytes = input.to_vec();
            assert_eq!(stream.accept(&mut bytes, false), Read2Action::Stop);
            assert!(stream.failure.is_some());
            assert_eq!(fixture.raw("stdout"), input);
            assert_eq!(evidence.stdout.received(), input.len() as u64);
            assert_eq!(evidence.stdout.persisted(), input.len() as u64);
            assert!(
                stream.output.is_empty(),
                "observer failure is not accepted line output"
            );
        }
    }
}

struct Stream<'a> {
    callback: &'a mut dyn FnMut(&str) -> anyhow::Result<()>,
    capture: bool,
    output: Vec<u8>,
    completed: usize,
    line_limit: usize,
    stream_limit: usize,
    failure: Option<anyhow::Error>,
    evidence: Option<Arc<ActionEvidence>>,
    is_stdout: bool,
    buffered: usize,
}
impl Stream<'_> {
    fn accept(&mut self, data: &mut Vec<u8>, eof: bool) -> Read2Action {
        let result = (|| -> anyhow::Result<()> {
            if let Some(evidence) = &self.evidence {
                // read2 retains a partial line between callbacks. Observe only
                // the newly appended actual read, never its old buffered tail
                // or the synthetic final callback after positive Drain.
                anyhow::ensure!(
                    data.len() >= self.buffered,
                    "hosted raw stream buffer changed before observation"
                );
                let new = &data[self.buffered..];
                if !new.is_empty() {
                    let stream = if self.is_stdout {
                        &evidence.stdout
                    } else {
                        &evidence.stderr
                    };
                    stream.append(new)?;
                }
            }
            if self.completed.saturating_add(data.len()) > self.stream_limit {
                anyhow::bail!("hosted compiler output exceeds stream limit");
            }
            let mut consumed = 0;
            while consumed < data.len() {
                let tail = &data[consumed..];
                let length = match tail.iter().position(|byte| *byte == b'\n') {
                    Some(index) => index + 1,
                    None if eof => tail.len(),
                    None => break,
                };
                if length > self.line_limit {
                    anyhow::bail!("hosted compiler output exceeds line limit");
                }
                let line = &tail[..length];
                (self.callback)(
                    std::str::from_utf8(line)?
                        .trim_end_matches('\n')
                        .trim_end_matches('\r'),
                )?;
                if self.capture {
                    self.output.extend_from_slice(line);
                }
                consumed += length;
            }
            self.completed = self
                .completed
                .checked_add(consumed)
                .ok_or_else(|| anyhow::anyhow!("hosted compiler output length overflow"))?;
            data.drain(..consumed);
            if data.len() > self.line_limit {
                anyhow::bail!("hosted compiler partial output exceeds line limit");
            }
            Ok(())
        })();
        self.buffered = data.len();
        match result {
            Ok(()) => Read2Action::Continue,
            Err(error) => {
                self.failure = Some(error);
                Read2Action::Stop
            }
        }
    }
}

pub(super) fn run(
    executor: &OwnedExecutor,
    process: &ProcessBuilder,
    on_stdout: &mut dyn FnMut(&str) -> anyhow::Result<()>,
    on_stderr: &mut dyn FnMut(&str) -> anyhow::Result<()>,
    capture: bool,
    limits: Option<StreamingOutputLimits>,
    capture_rusage: bool,
) -> (ExecStats, anyhow::Result<Output>) {
    let mut stats = ExecStats::default();
    let result = run_inner(
        executor,
        process,
        on_stdout,
        on_stderr,
        RunSettings {
            capture,
            limits,
            capture_rusage,
        },
        &mut stats,
    );
    (stats, result)
}
struct RunSettings {
    capture: bool,
    limits: Option<StreamingOutputLimits>,
    capture_rusage: bool,
}
fn run_inner(
    executor: &OwnedExecutor,
    process: &ProcessBuilder,
    on_stdout: &mut dyn FnMut(&str) -> anyhow::Result<()>,
    on_stderr: &mut dyn FnMut(&str) -> anyhow::Result<()>,
    settings: RunSettings,
    stats: &mut ExecStats,
) -> anyhow::Result<Output> {
    let RunSettings {
        capture,
        limits,
        capture_rusage,
    } = settings;
    let metadata = matches!(executor.dispatch, Dispatch::Metadata);
    let line_limit = limits.map_or(usize::MAX, StreamingOutputLimits::line_bytes);
    let stream_limit = limits
        .map_or(usize::MAX, StreamingOutputLimits::stream_bytes)
        .min(if metadata { 65_536 } else { usize::MAX });
    let mut stdout = Stream {
        callback: on_stdout,
        capture,
        output: Vec::new(),
        completed: 0,
        line_limit,
        stream_limit,
        failure: None,
        evidence: None,
        is_stdout: true,
        buffered: 0,
    };
    let mut stderr = Stream {
        callback: on_stderr,
        capture,
        output: Vec::new(),
        completed: 0,
        line_limit,
        stream_limit,
        failure: None,
        evidence: None,
        is_stdout: false,
        buffered: 0,
    };
    let (mut child, mut backing) = executor.start(
        process,
        true,
        limits.and_then(StreamingOutputLimits::runtime_timeout),
        capture_rusage,
    )?;
    stdout.evidence = backing.evidence.clone();
    stderr.evidence = backing.evidence.clone();
    let (Some(out), Some(err)) = (child.take_stdout(), child.take_stderr()) else {
        super::super::monitor::custodian_lost();
    };
    let mut terminal = None;
    let mut cancelled = false;
    let cancellation = process.execution_cancellation();
    let workload_cancellation = executor
        .startup
        .workload_process
        .as_ref()
        .map(|inputs| inputs.cancelled.clone());
    let mut physical_eof = [false; 2];
    let read = cargo_util::read2_controlled_with_eof(
        out,
        err,
        None,
        &mut |is_out, bytes, eof| {
            if is_out {
                stdout.accept(bytes, eof)
            } else {
                stderr.accept(bytes, eof)
            }
        },
        &mut || {
            if !cancelled
                && (cancellation
                    .as_ref()
                    .is_some_and(|value| value.load(Ordering::Acquire))
                    || workload_cancellation
                        .as_ref()
                        .is_some_and(|value| value.load(Ordering::Acquire)))
            {
                child.cancel(Instant::now() + Duration::from_secs(1))?;
                cancelled = true;
            }
            if terminal.is_none() {
                if !cancelled {
                    backing.bind_prepared(&executor.startup, &mut child)?;
                }
                terminal = child.try_wait(Instant::now() + Duration::from_millis(250));
            }
            Ok(match terminal {
                Some(Status::Unknown { .. }) => Read2Control::Stop,
                Some(_) => Read2Control::Drain,
                None => Read2Control::Continue,
            })
        },
        &mut physical_eof,
    );
    let cleanup = if read.is_err() || stdout.failure.is_some() || stderr.failure.is_some() {
        child.cancel(Instant::now() + Duration::from_secs(1))
    } else {
        Ok(())
    };
    // Never reuse a loan after uncertain delivery or before positive retirement.
    let actual = terminal.unwrap_or_else(|| child.wait());
    let helper_observation = match (&executor.startup.workload_evidence, &backing.evidence) {
        (Some(sink), Some(action)) => {
            sink.publish_helper(action.member_attempt(), child.helper_observation())
        }
        _ => Ok(()),
    };
    // Settle the same original loan from the real terminal before judging
    // measurement availability or callback errors. Known failed/cancelled
    // executions retain their observed metrics; Unknown returns none.
    let result = backing.settle(&actual);
    if capture_rusage {
        *stats = observed_stats(child.accounting());
    }
    let status = result?;
    helper_observation?;
    cleanup?;
    if capture_rusage && (stats.cpu_times.is_none() || stats.peak_rss.is_none()) {
        return Err(ProcessError::new(
            "native owning-wait accounting unavailable",
            Some(status),
            None,
        )
        .into());
    }
    read?;
    if let Some(error) = stdout.failure.or(stderr.failure) {
        return Err(error);
    }
    anyhow::ensure!(
        physical_eof == [true; 2] && child.started().is_some(),
        "original compiler streams did not reach physical EOF"
    );
    backing.materialized(&actual);
    Ok(Output {
        status,
        stdout: stdout.output,
        stderr: stderr.output,
    })
}
