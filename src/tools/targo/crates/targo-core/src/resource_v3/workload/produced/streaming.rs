//! The actual produced member remains the sole execution owner. Observe raw
//! bytes in its original sink before interpreting normal Cargo script lines.
use super::*;

struct Lines<'a> {
    callback: &'a mut dyn FnMut(&str) -> anyhow::Result<()>,
    pending: Vec<u8>,
    line_limit: usize,
    failed: bool,
}
impl Lines<'_> {
    fn accept(&mut self, bytes: &[u8], eof: bool) -> io::Result<()> {
        if self.failed {
            return Err(error("original script line observer previously failed"));
        }
        let result = self.accept_inner(bytes, eof);
        self.failed |= result.is_err();
        result
    }
    fn accept_inner(&mut self, bytes: &[u8], eof: bool) -> io::Result<()> {
        for byte in bytes {
            if self.pending.len() >= self.line_limit {
                return Err(error(
                    "produced script output exceeds original finite line bound",
                ));
            }
            self.pending.push(*byte);
            if *byte == b'\n' {
                self.line()?;
            }
        }
        if eof && !self.pending.is_empty() {
            self.line()?;
        }
        Ok(())
    }
    fn line(&mut self) -> io::Result<()> {
        let line = std::str::from_utf8(&self.pending).map_err(io::Error::other)?;
        (self.callback)(line.trim_end_matches('\n').trim_end_matches('\r'))
            .map_err(io::Error::other)?;
        self.pending.clear();
        Ok(())
    }
}

pub(super) fn run(
    executor: &Executor,
    process: &ProcessBuilder,
    on_stdout: &mut dyn FnMut(&str) -> anyhow::Result<()>,
    on_stderr: &mut dyn FnMut(&str) -> anyhow::Result<()>,
    capture_output: bool,
    limits: Option<StreamingOutputLimits>,
) -> (ExecStats, anyhow::Result<Output>) {
    let (stats, result) = (|| -> anyhow::Result<_> {
        anyhow::ensure!(
            executor.artifact.phase().kind
                == trust_resource_controller::workload::host::phase::Kind::BuildScript,
            "native harness owner requires original structured capture"
        );
        let timeout = Duration::from_nanos(
            executor
                .startup
                .workload_process
                .as_ref()
                .ok_or_else(|| error("script lost its original process inputs"))?
                .invocation
                .header()
                .timeout_ns,
        );
        let limits =
            limits.unwrap_or_else(|| StreamingOutputLimits::new(1024 * 1024, 64 * 1024 * 1024));
        let limits = if limits.runtime_timeout().is_none() {
            limits.with_timeout(timeout)
        } else {
            limits
        };
        let mut stdout = Lines {
            callback: on_stdout,
            pending: Vec::new(),
            line_limit: limits.line_bytes(),
            failed: false,
        };
        let mut stderr = Lines {
            callback: on_stderr,
            pending: Vec::new(),
            line_limit: limits.line_bytes(),
            failed: false,
        };
        let mut observer = |stream, bytes: &[u8]| {
            if stream == MetadataOutputStream::Stdout {
                stdout.accept(bytes, false)
            } else {
                stderr.accept(bytes, false)
            }
        };
        // Workload accounting is mandatory data, independent of the ordinary
        // optional timing-display flag. Never sum Root/helper/target scopes.
        let (stats, mut actual) =
            executor.capture_inner(process, limits, true, Some(&mut observer));
        drop(observer);
        if actual.complete() {
            if let Err(error) = stdout
                .accept(&[], true)
                .and_then(|_| stderr.accept(&[], true))
            {
                actual.failure.get_or_insert_with(|| error.into());
            }
        }
        let result = (|| -> anyhow::Result<Output> {
            if let Some(error) = actual.failure.take() {
                return Err(error);
            }
            anyhow::ensure!(
                actual.complete()
                    && actual.started
                    && actual
                        .owner_observation
                        .is_some_and(|owner| owner.retirement_confirmed),
                "script has no original complete native member retirement"
            );
            Ok(Output {
                status: actual
                    .status
                    .ok_or_else(|| error("script has no actual original exit"))?,
                stdout: if capture_output {
                    actual.stdout
                } else {
                    Vec::new()
                },
                stderr: if capture_output {
                    actual.stderr
                } else {
                    Vec::new()
                },
            })
        })();
        Ok((stats, result))
    })()
    .unwrap_or_else(|error| (ExecStats::default(), Err(error)));
    (stats, result)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn original_build_script_and_harness_profiles_cannot_relabel_each_other() {
        use trust_resource_controller::workload::host::phase::Kind;
        assert_eq!(
            action_kind(Kind::BuildScript, &[]).unwrap(),
            MemberKind::BuildScript
        );
        assert!(action_kind(Kind::Harnesses, &[]).is_err());
        assert!(action_kind(Kind::BuildScript, &[b"--list".to_vec()]).is_err());
        assert!(action_kind(Kind::BuildScript, &[b"-c".to_vec()]).is_err());
    }

    #[test]
    fn script_line_observation_preserves_partial_utf8_crlf_and_callback_refusal() {
        let mut observed = Vec::new();
        let mut callback = |line: &str| {
            observed.push(line.to_owned());
            Ok(())
        };
        let mut lines = Lines {
            callback: &mut callback,
            pending: Vec::new(),
            line_limit: 32,
            failed: false,
        };
        lines.accept(b"cargo::key=\xc3", false).unwrap();
        lines.accept(b"\xa9\r\nlast", false).unwrap();
        lines.accept(&[], true).unwrap();
        drop(lines);
        assert_eq!(observed, ["cargo::key=é", "last"]);
        let mut refused = |_: &str| anyhow::bail!("controlled script callback refusal");
        let mut lines = Lines {
            callback: &mut refused,
            pending: Vec::new(),
            line_limit: 32,
            failed: false,
        };
        assert!(lines.accept(b"actual\n", false).is_err());
        assert_eq!(lines.pending, b"actual\n");
        assert!(lines.accept(b"must not retry\n", true).is_err());
        assert_eq!(lines.pending, b"actual\n");
        let mut ignored = |_: &str| Ok(());
        let mut lines = Lines {
            callback: &mut ignored,
            pending: Vec::new(),
            line_limit: 3,
            failed: false,
        };
        assert!(lines.accept(b"long", false).is_err());
        assert_eq!(lines.pending, b"lon");
        let mut lines = Lines {
            callback: &mut ignored,
            pending: Vec::new(),
            line_limit: 32,
            failed: false,
        };
        assert!(lines.accept(b"binary\xff\n", false).is_err());
    }
}
