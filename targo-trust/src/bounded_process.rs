//! Bounded subprocess capture for identity and metadata probes.

use std::io::{self, Read};
use std::process::{Child, Command, Output, Stdio};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc::{self, Receiver, RecvTimeoutError};
use std::thread;
use std::time::{Duration, Instant};

const POST_EXIT_PIPE_CLOSE_GRACE: Duration = Duration::from_millis(250);

pub(crate) fn output(
    command: &mut Command,
    context: &str,
    max_stream_bytes: usize,
    timeout: Duration,
) -> Result<Output, String> {
    if max_stream_bytes == 0 || timeout.is_zero() {
        return Err(format!("{context} has an invalid zero output or timeout bound"));
    }
    command.stdin(Stdio::null()).stdout(Stdio::piped()).stderr(Stdio::piped());
    configure_process_group(command);
    let mut child =
        command.spawn().map_err(|error| format!("{context} could not start: {error}"))?;
    let child_pid = child.id();
    let Some(stdout) = child.stdout.take() else {
        terminate_child_group(&mut child, child_pid);
        return Err(format!("{context} did not expose stdout"));
    };
    let Some(stderr) = child.stderr.take() else {
        terminate_child_group(&mut child, child_pid);
        return Err(format!("{context} did not expose stderr"));
    };
    let output_exceeded = Arc::new(AtomicBool::new(false));
    let stdout_reader = spawn_reader(stdout, max_stream_bytes, Arc::clone(&output_exceeded));
    let stderr_reader = spawn_reader(stderr, max_stream_bytes, Arc::clone(&output_exceeded));
    let Some(deadline) = Instant::now().checked_add(timeout) else {
        terminate_child_group(&mut child, child_pid);
        return Err(format!("{context} timeout deadline overflowed"));
    };

    loop {
        if output_exceeded.load(Ordering::Acquire) {
            terminate_child_group(&mut child, child_pid);
            return Err(format!("{context} output exceeded {max_stream_bytes} bytes per stream"));
        }
        match exited_without_reaping(&mut child) {
            Ok(true) => break,
            Ok(false) if Instant::now() < deadline => thread::sleep(Duration::from_millis(10)),
            Ok(false) => {
                terminate_child_group(&mut child, child_pid);
                return Err(format!("{context} exceeded the {timeout:?} timeout"));
            }
            Err(error) => {
                terminate_child_group(&mut child, child_pid);
                return Err(format!("{context} could not be polled: {error}"));
            }
        }
    }

    // WNOWAIT keeps the leader's PID reserved as the process-group ID while
    // inherited pipes drain. Cleanup therefore cannot signal a reused PGID.
    // A short grace admits buffered output from the exited leader without
    // making an unauthorized pipe-inheriting descendant consume the entire
    // command timeout. A redirected descendant does not hold these channels
    // open and is still removed by the unconditional group cleanup below.
    let pipe_deadline =
        Instant::now().checked_add(POST_EXIT_PIPE_CLOSE_GRACE).unwrap_or(deadline).min(deadline);
    let stdout_result =
        receive_reader_after_exit(stdout_reader, context, "stdout", pipe_deadline, child_pid);
    let stderr_result =
        receive_reader_after_exit(stderr_reader, context, "stderr", pipe_deadline, child_pid);
    if let Err(error) = stdout_result.as_ref().and(stderr_result.as_ref()) {
        terminate_child_group(&mut child, child_pid);
        return Err(error.clone());
    }
    let (stdout, stdout_exceeded) = stdout_result.expect("checked reader result");
    let (stderr, stderr_exceeded) = stderr_result.expect("checked reader result");
    let _ = terminate_process_group(child_pid);
    let status = child.wait().map_err(|error| format!("{context} could not be reaped: {error}"))?;
    if stdout_exceeded || stderr_exceeded {
        return Err(format!("{context} output exceeded {max_stream_bytes} bytes per stream"));
    }
    Ok(Output { status, stdout, stderr })
}

fn terminate_child_group(child: &mut std::process::Child, child_pid: u32) {
    let _ = terminate_process_group(child_pid);
    let _ = child.kill();
    let _ = child.wait();
}

fn spawn_reader<R: Read + Send + 'static>(
    reader: R,
    max_stream_bytes: usize,
    output_exceeded: Arc<AtomicBool>,
) -> Receiver<io::Result<(Vec<u8>, bool)>> {
    let (sender, receiver) = mpsc::sync_channel(1);
    thread::spawn(move || {
        let _ = sender.send(drain_with_signal(reader, max_stream_bytes, Some(&output_exceeded)));
    });
    receiver
}

#[cfg(test)]
fn drain(mut reader: impl Read, max_stream_bytes: usize) -> io::Result<(Vec<u8>, bool)> {
    drain_with_signal(&mut reader, max_stream_bytes, None)
}

fn drain_with_signal(
    mut reader: impl Read,
    max_stream_bytes: usize,
    output_exceeded: Option<&AtomicBool>,
) -> io::Result<(Vec<u8>, bool)> {
    let retained_limit = max_stream_bytes.saturating_add(1);
    let mut retained = Vec::with_capacity(retained_limit.min(8 * 1024));
    let mut exceeded = false;
    let mut chunk = [0_u8; 8 * 1024];
    loop {
        let read = reader.read(&mut chunk)?;
        if read == 0 {
            break;
        }
        let remaining = retained_limit.saturating_sub(retained.len());
        retained.extend_from_slice(&chunk[..read.min(remaining)]);
        exceeded |= read > remaining || retained.len() > max_stream_bytes;
        if exceeded {
            if let Some(output_exceeded) = output_exceeded {
                output_exceeded.store(true, Ordering::Release);
            }
        }
    }
    Ok((retained, exceeded))
}

fn receive_reader_after_exit(
    reader: Receiver<io::Result<(Vec<u8>, bool)>>,
    context: &str,
    stream: &str,
    deadline: Instant,
    child_pid: u32,
) -> Result<(Vec<u8>, bool), String> {
    match reader.recv_timeout(deadline.saturating_duration_since(Instant::now())) {
        Ok(result) => result.map_err(|error| format!("{context} could not read {stream}: {error}")),
        Err(RecvTimeoutError::Disconnected) => {
            Err(format!("{context} {stream} reader disconnected"))
        }
        Err(RecvTimeoutError::Timeout) => {
            terminate_process_group(child_pid).map_err(|error| {
                format!(
                    "{context} {stream} remained open and its process group could not be terminated: {error}"
                )
            })?;
            Err(format!(
                "{context} spawned a background descendant that kept {stream} open past the output deadline"
            ))
        }
    }
}

#[cfg(unix)]
pub(crate) fn configure_process_group(command: &mut Command) {
    use std::os::unix::process::CommandExt as _;

    command.process_group(0);
}

#[cfg(not(unix))]
pub(crate) fn configure_process_group(_command: &mut Command) {}

/// Observe child exit without releasing its PID/PGID reservation on Unix.
pub(crate) fn exited_without_reaping(child: &mut Child) -> io::Result<bool> {
    #[cfg(unix)]
    {
        let pid = i32::try_from(child.id()).map_err(|_| {
            io::Error::new(io::ErrorKind::InvalidInput, "child pid does not fit platform pid_t")
        })?;
        let mut exit_info = std::mem::MaybeUninit::<libc::siginfo_t>::zeroed();
        let observed = unsafe {
            libc::waitid(
                libc::P_PID,
                pid as libc::id_t,
                exit_info.as_mut_ptr(),
                libc::WEXITED | libc::WNOHANG | libc::WNOWAIT,
            )
        };
        if observed < 0 {
            return Err(io::Error::last_os_error());
        }
        let exit_info = unsafe { exit_info.assume_init() };
        Ok(unsafe { exit_info.si_pid() } == pid)
    }
    #[cfg(not(unix))]
    {
        child.try_wait().map(|status| status.is_some())
    }
}

#[cfg(unix)]
pub(crate) fn terminate_process_group(pid: u32) -> io::Result<()> {
    let pid = i32::try_from(pid).map_err(|_| {
        io::Error::new(io::ErrorKind::InvalidInput, "child pid does not fit platform pid_t")
    })?;
    let result = unsafe { libc::kill(-pid, libc::SIGKILL) };
    if result == 0 {
        Ok(())
    } else {
        let error = io::Error::last_os_error();
        if error.raw_os_error() == Some(libc::ESRCH) { Ok(()) } else { Err(error) }
    }
}

#[cfg(not(unix))]
pub(crate) fn terminate_process_group(_pid: u32) -> io::Result<()> {
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(unix)]
    #[test]
    fn rejects_oversized_hanging_and_background_probes() {
        let mut successful = Command::new("/bin/sh");
        successful.args(["-c", "printf bounded"]);
        let successful_output =
            output(&mut successful, "successful probe", 1024, Duration::from_secs(2))
                .expect("a completed child with closed streams must be accepted");
        assert!(successful_output.status.success());
        assert_eq!(successful_output.stdout, b"bounded");

        let (retained, exceeded) =
            drain(io::Cursor::new(vec![b'x'; 100_000]), 64 * 1024).expect("read bounded fixture");
        assert!(exceeded);
        assert_eq!(retained.len(), 64 * 1024 + 1);

        let mut oversized = Command::new("/bin/sh");
        oversized.args(["-c", "while :; do printf 0123456789abcdef; done"]);
        assert!(
            output(&mut oversized, "oversized probe", 1024, Duration::from_secs(5))
                .expect_err("oversized output must fail")
                .contains("output exceeded")
        );

        let mut hanging = Command::new("/bin/sh");
        hanging.args(["-c", "while :; do :; done"]);
        assert!(
            output(&mut hanging, "hanging probe", 1024, Duration::from_millis(100))
                .expect_err("hanging command must fail")
                .contains("timeout")
        );

        let mut background = Command::new("/bin/sh");
        background.args(["-c", "sleep 10 & exit 0"]);
        assert!(
            output(&mut background, "background probe", 1024, Duration::from_secs(2))
                .expect_err("background descendant must fail")
                .contains("background descendant")
        );

        let marker = std::env::temp_dir()
            .join(format!("trust-bounded-process-descendant-{}", std::process::id()));
        let _ = std::fs::remove_file(&marker);
        let mut redirected_background = Command::new("/bin/sh");
        redirected_background
            .arg("-c")
            .arg(
                "sh -c 'trap \"\" HUP; sleep 1; printf survived > \"$1\"' descendant \"$1\" \
                 </dev/null >/dev/null 2>&1 & printf '%s' \"$!\"",
            )
            .arg("bounded-process-test")
            .arg(&marker);
        let redirected_output = output(
            &mut redirected_background,
            "redirected background probe",
            1024,
            Duration::from_secs(2),
        )
        .expect("closed probe streams may complete after group cleanup");
        let pid: i32 = String::from_utf8(redirected_output.stdout)
            .expect("pid UTF-8")
            .parse()
            .expect("numeric pid");
        // A killed grandchild can briefly remain as an init-owned zombie, for
        // which `kill(pid, 0)` misleadingly succeeds. Prove that it cannot
        // execute after cleanup instead.
        thread::sleep(Duration::from_millis(1_200));
        assert!(
            !marker.exists(),
            "redirected descendant {pid} survived cleanup and wrote its marker"
        );
        let _ = std::fs::remove_file(marker);
    }
}
