//! Observe an existing same-account direct process and publish logical debt.
//! This entry assigns no CPU budget and starts or controls no target.

use super::*;
use trust_build_tree::admission::Adoption;

pub(super) fn cli() -> clap::Command {
    clap::Command::new("targo --unverified resource adopt")
        .about("Record an existing direct process as canonical legacy coordination debt")
        .after_help("No CPU budget, GNU credit, process control or release authority is granted. Mixed/retired domains and inherited admission profiles refuse.")
        .arg(Arg::new("pid").required(true).value_parser(clap::value_parser!(NonZeroU32)))
        .arg(Arg::new("exclusive").long("exclusive").action(ArgAction::SetTrue))
        .arg(Arg::new("memory-mib").long("memory-mib").default_value("8192").value_parser(clap::value_parser!(NonZeroU64)))
        .arg(Arg::new("wait-seconds").long("wait-seconds").value_parser(clap::value_parser!(NonZeroU64)))
}

struct Options {
    pid: u32,
    exclusive: bool,
    memory: NonZeroU64,
    timeout: Option<Duration>,
}
fn options(args: &[OsString]) -> Result<Options> {
    let matches = cli().try_get_matches_from(
        std::iter::once(OsString::from("resource adopt")).chain(args.iter().cloned()),
    )?;
    let pid = matches
        .get_one::<NonZeroU32>("pid")
        .expect("required pid")
        .get();
    ensure!(
        pid <= i32::MAX as u32,
        "adoption PID exceeds the native process range"
    );
    let memory = matches
        .get_one::<NonZeroU64>("memory-mib")
        .expect("default memory")
        .get()
        .checked_mul(1024 * 1024)
        .and_then(NonZeroU64::new)
        .context("adoption memory floor is unrepresentable")?;
    let timeout = matches
        .get_one::<NonZeroU64>("wait-seconds")
        .map(|seconds| {
            ensure!(
                seconds.get() <= MAX_WAIT_SECONDS,
                "adoption wait exceeds seven days"
            );
            Ok(Duration::from_secs(seconds.get()))
        })
        .transpose()?;
    Ok(Options {
        pid,
        exclusive: matches.get_flag("exclusive"),
        memory,
        timeout,
    })
}

pub(super) fn dispatch(args: &[OsString]) -> Result<i32> {
    if args.len() == 1 && (args[0] == "--help" || args[0] == "-h") {
        cli().print_help()?;
        let mut output = std::io::stdout().lock();
        writeln!(output)?;
        output.flush()?;
        return Ok(0);
    }
    let options = options(args)?;
    check_ancestors()?;
    let started = Instant::now();
    let deadline = options
        .timeout
        .map(|duration| {
            started
                .checked_add(duration)
                .context("adoption deadline is unrepresentable")
        })
        .transpose()?;
    let mut adoption = Adoption::for_current_user(
        options.pid,
        worktree_lock()?,
        options.exclusive,
        options.memory,
    )?;
    let mut previous = None;
    loop {
        ensure!(
            deadline.is_none_or(|until| Instant::now() < until),
            "native adoption deadline expired before another registration attempt"
        );
        match adoption.attempt()? {
            Attempt::Waiting(reason) => {
                let reason = format!("{reason:?}");
                if previous.as_ref() != Some(&reason) {
                    // A diagnostic failure must not interrupt the native wait.
                    let _ = writeln!(
                        std::io::stderr().lock(),
                        "targo: waiting for native adoption: {reason}"
                    );
                    previous = Some(reason);
                }
                std::thread::sleep(Duration::from_millis(50));
            }
            Attempt::Admitted(outcome) => {
                ensure!(
                    deadline.is_none_or(|until| Instant::now() < until),
                    "native adoption observation crossed the original deadline; debt may already be recorded and is retained; inspect resource status"
                );
                let mut output = std::io::stdout().lock();
                serde_json::to_writer(&mut output, &outcome).context(
                    "adoption reply failed; the recorded debt remains, do not replay automatically",
                )?;
                let incomplete_reply = "adoption reply may be incomplete; the recorded debt remains, do not replay automatically";
                writeln!(output).context(incomplete_reply)?;
                output.flush().context(incomplete_reply)?;
                ensure!(
                    deadline.is_none_or(|until| Instant::now() < until),
                    "adoption reply crossed the original deadline; the recorded debt is retained"
                );
                return Ok(0);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn words(values: &[&str]) -> Vec<OsString> {
        values.iter().map(OsString::from).collect()
    }
    #[test]
    fn only_bounded_pid_debt_policy_is_parsed() {
        let value = options(&words(&[
            "--exclusive",
            "--memory-mib",
            "2",
            "--wait-seconds",
            "3",
            "17",
        ]))
        .unwrap();
        assert_eq!(value.pid, 17);
        assert!(value.exclusive);
        assert_eq!(value.memory.get(), 2 * 1024 * 1024);
        assert_eq!(value.timeout, Some(Duration::from_secs(3)));
    }
    #[test]
    fn cpu_namespace_inherited_and_unbounded_launch_arguments_are_not_adoption() {
        for args in [
            vec!["0"],
            vec!["2147483648"],
            vec!["--cpus", "2", "17"],
            vec!["--slots", "2", "17"],
            vec!["--dir", "/foreign", "17"],
            vec!["--wait-seconds", "604801", "17"],
            vec!["--memory-mib", "18446744073709551615", "17"],
            vec!["17", "--", "/bin/sleep"],
        ] {
            assert!(options(&words(&args)).is_err(), "{args:?}");
        }
    }
}
