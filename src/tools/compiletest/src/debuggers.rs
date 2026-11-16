// Blessed env_mutation (2026-07-20): vendored upstream tool code, compiled by
// the Trust toolchain's extended tools build. These files mutate process-global
// env under their own discipline (rust-analyzer's EnvChange holds an env lock;
// compiletest/tidy/opt-dist run single-threaded harness setup). Upstream builds
// them under stock rustc, so unknown_lints keeps that path green too.
#![allow(unknown_lints)]
#![allow(env_mutation)]
use std::process::{Command, ExitStatus, Stdio};
use std::time::{Duration, Instant};

use camino::Utf8Path;
use semver::Version;

// Trust: how long the up-front LLDB scripting probe may take before we declare
// the LLDB installation unusable for batch-mode tests. Generous: a healthy
// probe takes ~1s even on a loaded machine.
const LLDB_PROBE_TIMEOUT: Duration = Duration::from_secs(60);

/// Trust: checks that `lldb` can execute a trivial command through its embedded
/// Python interpreter, in bounded time. This is the capability every lldb
/// debuginfo test depends on (`src/etc/lldb_lookup.py` runs inside that
/// interpreter). Returns a human-readable reason on failure.
// Trust: upstream 1.101 removed `configure_lldb` (the probe's call site)
// when debugger setup moved to `cli.rs`/`lib.rs`. Kept for re-hooking there.
#[allow(dead_code)]
pub(crate) fn lldb_can_run_batch_driver(lldb: &Utf8Path) -> Result<(), String> {
    let mut cmd = Command::new(lldb);
    cmd.arg("--no-lldbinit")
        .arg("--batch")
        .arg("-o")
        .arg("script --language python -- print(7 * 191)");

    let run = run_bounded(cmd, LLDB_PROBE_TIMEOUT)
        .map_err(|e| format!("failed to spawn `{lldb}`: {e}"))?;

    if run.timed_out {
        return Err(format!(
            "probe (`script --language python -- print(...)`) did not finish within {}s; \
             killed its process group",
            LLDB_PROBE_TIMEOUT.as_secs()
        ));
    }

    let stdout = String::from_utf8_lossy(&run.stdout);
    if run.status.success() && stdout.contains("1337") {
        Ok(())
    } else {
        Err(format!(
            "probe exited with {} without evaluating Python (LLDB without Python scripting \
             support?)\nprobe stdout:\n{}\nprobe stderr:\n{}",
            run.status,
            stdout,
            String::from_utf8_lossy(&run.stderr),
        ))
    }
}

/// Trust: result of [`run_bounded`].
pub(crate) struct BoundedRun {
    pub(crate) status: ExitStatus,
    pub(crate) stdout: Vec<u8>,
    pub(crate) stderr: Vec<u8>,
    /// True if the child exceeded the deadline and was killed.
    pub(crate) timed_out: bool,
}

/// Trust: runs a command to completion with a hard wall-clock bound.
///
/// The child is placed in its own process group (on Unix) so that when the
/// deadline is exceeded the *whole* group is SIGKILLed — for LLDB this also
/// reaps `debugserver` and a suspended debuggee, which would otherwise linger
/// stopped (T state) forever. stdin is null; stdout/stderr are captured.
///
/// This exists because a debugger invocation is the one place in compiletest
/// where a child can block indefinitely on the *operating system* (macOS
/// debug-launch authorization/attach), not on anything the test controls, and
/// the test executor only warns — never kills — long-running tests.
pub(crate) fn run_bounded(mut cmd: Command, timeout: Duration) -> std::io::Result<BoundedRun> {
    use std::io::Read;

    cmd.stdin(Stdio::null()).stdout(Stdio::piped()).stderr(Stdio::piped());
    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt;
        // New process group, so we can kill the child and its descendants.
        cmd.process_group(0);
    }

    let mut child = cmd.spawn()?;

    let mut stdout_pipe = child.stdout.take().unwrap();
    let mut stderr_pipe = child.stderr.take().unwrap();
    let stdout_reader = std::thread::spawn(move || {
        let mut buf = Vec::new();
        let _ = stdout_pipe.read_to_end(&mut buf);
        buf
    });
    let stderr_reader = std::thread::spawn(move || {
        let mut buf = Vec::new();
        let _ = stderr_pipe.read_to_end(&mut buf);
        buf
    });

    let deadline = Instant::now() + timeout;
    let mut timed_out = false;
    let status = loop {
        if let Some(status) = child.try_wait()? {
            break status;
        }
        if Instant::now() >= deadline {
            timed_out = true;
            #[cfg(unix)]
            {
                // Kill the whole process group (negative pid). Best-effort:
                // the direct `child.kill()` below is the fallback.
                unsafe {
                    libc::kill(-(child.id() as libc::pid_t), libc::SIGKILL);
                }
            }
            let _ = child.kill();
            break child.wait()?;
        }
        std::thread::sleep(Duration::from_millis(50));
    };

    let stdout = stdout_reader.join().unwrap_or_default();
    let stderr = stderr_reader.join().unwrap_or_default();
    Ok(BoundedRun { status, stdout, stderr, timed_out })
}

pub(crate) fn query_cdb_version(cdb: &Utf8Path) -> Option<[u16; 4]> {
    let mut version = None;
    if let Ok(output) = Command::new(cdb).arg("/version").output() {
        if let Some(first_line) = String::from_utf8_lossy(&output.stdout).lines().next() {
            version = extract_cdb_version(&first_line);
        }
    }
    version
}

pub(crate) fn extract_cdb_version(full_version_line: &str) -> Option<[u16; 4]> {
    // Example full_version_line: "cdb version 10.0.18362.1"
    let version = full_version_line.rsplit(' ').next()?;
    let mut components = version.split('.');
    let major: u16 = components.next().unwrap().parse().unwrap();
    let minor: u16 = components.next().unwrap().parse().unwrap();
    let patch: u16 = components.next().unwrap_or("0").parse().unwrap();
    let build: u16 = components.next().unwrap_or("0").parse().unwrap();
    Some([major, minor, patch, build])
}

pub(crate) fn query_gdb_version(gdb: &Utf8Path) -> Option<u32> {
    let mut version_line = None;
    if let Ok(output) = Command::new(&gdb).arg("--version").output() {
        if let Some(first_line) = String::from_utf8_lossy(&output.stdout).lines().next() {
            version_line = Some(first_line.to_string());
        }
    }

    let version = match version_line {
        Some(line) => extract_gdb_version(&line),
        None => return None,
    };

    version
}

pub(crate) fn extract_gdb_version(full_version_line: &str) -> Option<u32> {
    let full_version_line = full_version_line.trim();

    // GDB versions look like this: "major.minor.patch?.yyyymmdd?", with both
    // of the ? sections being optional

    // We will parse up to 3 digits for each component, ignoring the date

    // We skip text in parentheses.  This avoids accidentally parsing
    // the openSUSE version, which looks like:
    //  GNU gdb (GDB; openSUSE Leap 15.0) 8.1
    // This particular form is documented in the GNU coding standards:
    // https://www.gnu.org/prep/standards/html_node/_002d_002dversion.html#g_t_002d_002dversion

    let unbracketed_part = full_version_line.split('[').next().unwrap();
    let mut splits = unbracketed_part.trim_end().rsplit(' ');
    let version_string = splits.next().unwrap();

    let mut splits = version_string.split('.');
    let major = splits.next().unwrap();
    let minor = splits.next().unwrap();
    let patch = splits.next();

    let major: u32 = major.parse().unwrap();
    let (minor, patch): (u32, u32) = match minor.find(not_a_digit) {
        None => {
            let minor = minor.parse().unwrap();
            let patch: u32 = match patch {
                Some(patch) => match patch.find(not_a_digit) {
                    None => patch.parse().unwrap(),
                    Some(idx) if idx > 3 => 0,
                    Some(idx) => patch[..idx].parse().unwrap(),
                },
                None => 0,
            };
            (minor, patch)
        }
        // There is no patch version after minor-date (e.g. "4-2012").
        Some(idx) => {
            let minor = minor[..idx].parse().unwrap();
            (minor, 0)
        }
    };

    Some(((major * 1000) + minor) * 1000 + patch)
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum LldbVersion {
    /// LLDB distributed by Apple as part of Xcode. Uses a unique versioning scheme that does not
    /// match LLVM's LLDB.
    Apple([u64; 4]),
    /// LLDB distributed by LLVM, uses traditional semver.
    Llvm(Version),
}

impl LldbVersion {
    /// Takes a string consisting of 1-4 `.`-separated numbers and returns an `LldbVersion::Apple`.
    ///
    /// If a number fails to parse, that section and any following sections are silently converted
    /// to `0` (e.g. `"15.6.asdf.3"` -> `[15, 6, 0, 0]`)
    pub(crate) fn apple_from_str(version_num: &str) -> Self {
        let mut ver: [u64; 4] = [0; 4];

        for (i, val) in version_num.split('.').enumerate().take_while(|(i, _)| *i < 4) {
            if let Ok(part) = val.parse::<u64>() {
                ver[i] = part;
            } else {
                eprintln!(
                    "Warning: Invalid LLDB version format: '{version_num}'. Falling back to version '{ver:?}'"
                );
                break;
            }
        }

        Self::Apple(ver)
    }

    /// Takes a string consisting of 1-3 `.`-separated numbers and returns an `LldbVersion::Llvm`.
    ///
    /// If a number fails to parse, that section and any following sections are silently converted
    /// to `0` (e.g. `"15.asdf.3"` -> `[15, 0, 0]`)
    pub(crate) fn llvm_from_str(version_num: &str) -> Self {
        let mut ver: [u64; 3] = [0; 3];

        for (i, val) in version_num.split('.').enumerate().take_while(|(i, _)| *i < 3) {
            if let Ok(part) = val.parse::<u64>() {
                ver[i] = part;
            } else {
                eprintln!(
                    "Warning: Invalid LLDB version number format: '{version_num}'. Falling back to version '{ver:?}'"
                );
                break;
            }
        }

        Self::Llvm(Version::new(ver[0], ver[1], ver[2]))
    }
}

/// Returns LLDB version
pub(crate) fn extract_lldb_version(full_version_line: &str) -> Option<LldbVersion> {
    // Extract the major LLDB version from the given version string.
    // LLDB version strings are different for Apple and non-Apple platforms.
    // The Apple variant looks like this:
    //
    // LLDB-179.5 (older versions)
    // lldb-300.2.51 (new versions)
    // lldb-1703.0.236.21 (even newer versions)
    //
    // LLVM versions look like:
    // lldb version 6.0.1
    //
    // There doesn't seem to be a way to correlate the Apple version
    // with the upstream version.

    let full_version_line = full_version_line.trim();

    if let Some(apple_str) =
        full_version_line.strip_prefix("LLDB-").or_else(|| full_version_line.strip_prefix("lldb-"))
    {
        let version_str = apple_str.split_whitespace().next()?;

        return Some(LldbVersion::apple_from_str(version_str));
    }

    if let Some(lldb_str) = full_version_line.strip_prefix("lldb version ") {
        let version_str = lldb_str.split_whitespace().next()?;

        return Some(LldbVersion::llvm_from_str(version_str));
    }
    None
}

fn not_a_digit(c: char) -> bool {
    !c.is_ascii_digit()
}

// Trust: tests for the bounded-run helper and the LLDB batch-driver gating.
#[cfg(all(test, unix))]
#[path = "debuggers/tests.rs"]
mod trust_tests;
