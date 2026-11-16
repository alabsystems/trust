//! Bounded diagnostics for bootstrap's compiletest JSONL sidecars.
//!
//! Both the sidecars and the renderer log come from the same bootstrap process.
//! Agreement between them is useful falsification evidence, not independent
//! execution authentication.

use std::collections::{BTreeMap, BTreeSet};
#[cfg(unix)]
use std::ffi::{CStr, CString};
use std::fs::{self, File};
use std::io::Read;
#[cfg(unix)]
use std::os::unix::fs::{MetadataExt, OpenOptionsExt};
#[cfg(unix)]
use std::os::unix::io::{AsRawFd, FromRawFd};
use std::path::Path;

use serde::de::{MapAccess, Visitor};
use serde::{Deserialize, Deserializer, Serialize};
use serde_json::Value;

use super::observations::Observation;
use super::sha256_bytes;
use super::ui_denominator::UiCase;
use crate::TestOutcome;

const EVENT_SCHEMA: &str = "trust.compiletest.case-events/v1";
const REPORT_SCHEMA: &str = "trust.upstream-rust.structured-sidecars.v1";
const PREFIX: &str = "compiletest-events-";
const SUFFIX: &str = ".jsonl";
const MAX_DIRECTORY_ENTRIES: usize = 4096;
const MAX_FILES: usize = 256;
const MAX_FILE_BYTES: u64 = 64 * 1024 * 1024;
const MAX_TOTAL_BYTES: u64 = 256 * 1024 * 1024;
const MAX_LINE_BYTES: usize = 2 * 1024 * 1024;
const MAX_EVENTS: usize = 200_000;
const MAX_SELECTED: usize = 100_000;
const MAX_ARGV: usize = 512;
const MAX_ARG_BYTES: usize = 16 * 1024;
const MAX_NAME_BYTES: usize = 4096;
const MAX_DIAGNOSTICS: usize = 24;

#[cfg(unix)]
struct DirectoryStream(*mut libc::DIR);

#[cfg(unix)]
impl Drop for DirectoryStream {
    fn drop(&mut self) {
        unsafe { libc::closedir(self.0) };
    }
}

#[derive(Serialize)]
pub(super) struct SidecarReport {
    schema: &'static str,
    authority: &'static str,
    streams_valid: bool,
    files: Vec<SidecarFile>,
    ui: Option<UiComparison>,
    diagnostics: Vec<String>,
}

#[derive(Serialize)]
struct SidecarFile {
    name: String,
    sha256: Option<String>,
    bytes: Option<u64>,
    valid: bool,
    suite: Option<String>,
    mode: Option<String>,
    host: Option<String>,
    target: Option<String>,
    selected_count: Option<usize>,
    passed: Option<usize>,
    failed: Option<usize>,
    ignored: Option<usize>,
    filtered_out: Option<usize>,
    cases: Vec<CaseOutcome>,
    diagnostics: Vec<String>,
}

impl SidecarFile {
    fn new(name: String) -> Self {
        Self {
            name,
            sha256: None,
            bytes: None,
            valid: false,
            suite: None,
            mode: None,
            host: None,
            target: None,
            selected_count: None,
            passed: None,
            failed: None,
            ignored: None,
            filtered_out: None,
            cases: Vec::new(),
            diagnostics: Vec::new(),
        }
    }
}

#[derive(Serialize)]
struct CaseOutcome {
    name: String,
    outcome: TestOutcome,
    timed_out: bool,
}

#[derive(Serialize)]
struct UiComparison {
    expected_cases: usize,
    sidecar_cases: usize,
    ui_streams: usize,
    missing_cases: usize,
    unexpected_cases: usize,
    duplicate_cases: usize,
    renderer_mismatches: usize,
    context_reconciled: bool,
    roster_reconciled: bool,
    renderer_reconciled: bool,
    diagnostics: Vec<String>,
}

struct ParsedStream {
    suite: String,
    mode: String,
    host: String,
    target: String,
    selected: usize,
    passed: usize,
    failed: usize,
    ignored: usize,
    filtered_out: usize,
    cases: Vec<CaseOutcome>,
}

struct CaseState {
    outcome: Option<TestOutcome>,
    timed_out: bool,
}

// serde_json::Value silently keeps the last occurrence of a duplicate key.
// Reject duplicates before inspecting exact record fields.
struct StrictObject(BTreeMap<String, Value>);

impl<'de> Deserialize<'de> for StrictObject {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        struct ObjectVisitor;

        impl<'de> Visitor<'de> for ObjectVisitor {
            type Value = StrictObject;

            fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                formatter.write_str("a JSON object with unique fields")
            }

            fn visit_map<M: MapAccess<'de>>(self, mut map: M) -> Result<Self::Value, M::Error> {
                let mut fields = BTreeMap::new();
                while let Some((key, value)) = map.next_entry::<String, Value>()? {
                    if fields.insert(key.clone(), value).is_some() {
                        return Err(serde::de::Error::custom(format!("duplicate field {key}")));
                    }
                }
                Ok(StrictObject(fields))
            }
        }

        deserializer.deserialize_map(ObjectVisitor)
    }
}

fn diagnostic(rows: &mut Vec<String>, message: impl Into<String>) {
    if rows.len() < MAX_DIAGNOSTICS {
        rows.push(message.into());
    }
}

fn fields<'a>(
    record: &'a BTreeMap<String, Value>,
    expected: &[&str],
) -> Result<&'a BTreeMap<String, Value>, String> {
    let actual = record.keys().map(String::as_str).collect::<BTreeSet<_>>();
    let expected = expected.iter().copied().collect::<BTreeSet<_>>();
    if actual != expected {
        return Err(format!(
            "record fields differ: missing {:?}, unexpected {:?}",
            expected.difference(&actual).collect::<Vec<_>>(),
            actual.difference(&expected).collect::<Vec<_>>()
        ));
    }
    Ok(record)
}

fn string<'a>(record: &'a BTreeMap<String, Value>, key: &str) -> Result<&'a str, String> {
    record.get(key).and_then(Value::as_str).ok_or_else(|| format!("{key} must be a string"))
}

fn number(record: &BTreeMap<String, Value>, key: &str) -> Result<usize, String> {
    record
        .get(key)
        .and_then(Value::as_u64)
        .and_then(|value| usize::try_from(value).ok())
        .ok_or_else(|| format!("{key} must be a nonnegative integer"))
}

fn nullable_string(record: &BTreeMap<String, Value>, key: &str) -> Result<(), String> {
    match record.get(key) {
        Some(Value::Null | Value::String(_)) => Ok(()),
        _ => Err(format!("{key} must be a string or null")),
    }
}

fn record(line: &[u8]) -> Result<BTreeMap<String, Value>, String> {
    let StrictObject(record) =
        serde_json::from_slice(line).map_err(|error| format!("invalid JSON object: {error}"))?;
    if string(&record, "schema")? != EVENT_SCHEMA {
        return Err("case-event schema mismatch".into());
    }
    Ok(record)
}

fn option(argv: &[String], flag: &str) -> Result<String, String> {
    let mut found = None;
    for (index, arg) in argv.iter().enumerate() {
        if arg == flag {
            let value =
                argv.get(index + 1).filter(|value| !value.is_empty() && !value.starts_with('-'));
            if found.is_some() || value.is_none() {
                return Err(format!("missing or repeated invocation {flag}"));
            }
            found = value.cloned();
        }
    }
    found.ok_or_else(|| format!("missing invocation {flag}"))
}

fn parse_header(line: &[u8]) -> Result<(String, String, String, String), String> {
    let header = record(line)?;
    fields(&header, &["schema", "type", "argv"])?;
    if string(&header, "type")? != "invocation" {
        return Err("first record is not an invocation header".into());
    }
    let argv =
        header["argv"].as_array().ok_or_else(|| "invocation argv must be an array".to_string())?;
    if argv.is_empty() || argv.len() > MAX_ARGV {
        return Err("invocation argv count is empty or exceeds bound".into());
    }
    let argv = argv
        .iter()
        .map(|arg| {
            let arg =
                arg.as_str().ok_or_else(|| "invocation argv must contain strings".to_string())?;
            if arg.len() > MAX_ARG_BYTES || arg.contains(['\0', '\n', '\r']) {
                return Err(
                    "invocation argument exceeds bound or contains a control character".into()
                );
            }
            Ok(arg.to_string())
        })
        .collect::<Result<Vec<_>, String>>()?;
    let suite = option(&argv, "--suite")?;
    let mode = option(&argv, "--mode")?;
    let host = option(&argv, "--host")?;
    let target = option(&argv, "--target")?;
    if !suite.bytes().all(|byte| byte.is_ascii_lowercase() || byte == b'-')
        || !mode.bytes().all(|byte| byte.is_ascii_lowercase() || byte == b'-')
    {
        return Err("invocation suite or mode has an invalid spelling".into());
    }
    Ok((suite, mode, host, target))
}

fn parse_stream(bytes: &[u8]) -> Result<ParsedStream, String> {
    if !bytes.ends_with(b"\n") {
        return Err("sidecar lacks final newline".into());
    }
    let lines = bytes.split(|byte| *byte == b'\n').collect::<Vec<_>>();
    if lines.len() < 4 || lines.len() - 2 > MAX_EVENTS {
        return Err("sidecar event count is incomplete or exceeds bound".into());
    }
    if lines[..lines.len() - 1].iter().any(|line| line.is_empty() || line.len() > MAX_LINE_BYTES) {
        return Err("sidecar contains an empty or oversized line".into());
    }
    let (suite, mode, host, target) = parse_header(lines[0])?;
    let mut selected = None;
    let mut ended = false;
    let mut cases = BTreeMap::<String, CaseState>::new();
    let mut passed = 0usize;
    let mut failed = 0usize;
    let mut ignored = 0usize;
    let mut filtered_out = None;
    for (index, line) in lines[1..lines.len() - 1].iter().enumerate() {
        let line_number = index + 2;
        let event = record(line).map_err(|error| format!("line {line_number}: {error}"))?;
        let kind = string(&event, "type")?;
        let action = string(&event, "event")?;
        let invalid = |reason: &str| format!("line {line_number}: {reason}");
        if ended {
            return Err(invalid("event after suite terminal"));
        }
        match (kind, action) {
            ("suite", "started") => {
                fields(&event, &["schema", "type", "event", "test_count", "selected_count"])?;
                let count = number(&event, "test_count")?;
                if selected.is_some()
                    || count == 0
                    || count > MAX_SELECTED
                    || number(&event, "selected_count")? != count
                {
                    return Err(invalid("duplicate, empty, oversized, or inconsistent selection"));
                }
                selected = Some(count);
            }
            ("test", "started" | "timeout" | "ok" | "failed" | "ignored") => {
                if selected.is_none() {
                    return Err(invalid("test event before suite selection"));
                }
                if action == "started" || action == "timeout" {
                    fields(&event, &["schema", "type", "event", "name"])?;
                } else {
                    fields(&event, &["schema", "type", "event", "name", "message", "stdout"])?;
                    nullable_string(&event, "message")?;
                    nullable_string(&event, "stdout")?;
                }
                let name = string(&event, "name")?;
                if name.is_empty()
                    || name.len() > MAX_NAME_BYTES
                    || name.contains(['\0', '\n', '\r'])
                {
                    return Err(invalid(
                        "case identity is empty, oversized, or contains a control character",
                    ));
                }
                match action {
                    "started" => {
                        if cases.len() >= selected.unwrap_or(0)
                            || cases
                                .insert(
                                    name.to_owned(),
                                    CaseState { outcome: None, timed_out: false },
                                )
                                .is_some()
                        {
                            return Err(invalid("duplicate or excess selected case start"));
                        }
                    }
                    "timeout" => {
                        let Some(case) = cases.get_mut(name) else {
                            return Err(invalid("timeout without case start"));
                        };
                        if case.outcome.is_some() {
                            return Err(invalid("timeout after case terminal"));
                        }
                        if case.timed_out {
                            return Err(invalid("duplicate case timeout"));
                        }
                        case.timed_out = true;
                    }
                    _ => {
                        let Some(case) = cases.get_mut(name) else {
                            return Err(invalid("terminal without case start"));
                        };
                        if case.outcome.is_some() {
                            return Err(invalid("duplicate case terminal"));
                        }
                        let (outcome, count) = match action {
                            "ok" => (TestOutcome::Passed, &mut passed),
                            "failed" => (TestOutcome::Failed, &mut failed),
                            _ => (TestOutcome::Skipped, &mut ignored),
                        };
                        case.outcome = Some(outcome);
                        *count += 1;
                    }
                }
            }
            ("suite", "ok" | "failed") => {
                fields(
                    &event,
                    &[
                        "schema",
                        "type",
                        "event",
                        "selected_count",
                        "executed_count",
                        "terminal_count",
                        "protocol_valid",
                        "protocol_error",
                        "passed",
                        "failed",
                        "ignored",
                        "measured",
                        "filtered_out",
                        "exec_time",
                    ],
                )?;
                let Some(selected) = selected else {
                    return Err(invalid("suite terminal without selection"));
                };
                let executed =
                    passed.checked_add(failed).ok_or_else(|| invalid("count overflow"))?;
                let terminal =
                    executed.checked_add(ignored).ok_or_else(|| invalid("count overflow"))?;
                let time = &event["exec_time"];
                if number(&event, "selected_count")? != selected
                    || number(&event, "executed_count")? != executed
                    || number(&event, "terminal_count")? != terminal
                    || number(&event, "passed")? != passed
                    || number(&event, "failed")? != failed
                    || number(&event, "ignored")? != ignored
                    || number(&event, "measured")? != 0
                    || event["protocol_valid"] != true
                    || event["protocol_error"] != Value::Null
                    || !(time.is_null()
                        || time.as_f64().is_some_and(|value| value.is_finite() && value >= 0.0))
                    || terminal != selected
                    || cases.len() != selected
                    || cases.values().any(|case| case.outcome.is_none())
                    || (action == "ok") != (failed == 0)
                {
                    return Err(invalid("inconsistent or incomplete suite terminal"));
                }
                filtered_out = Some(number(&event, "filtered_out")?);
                ended = true;
            }
            _ => return Err(invalid("unknown or misplaced case event")),
        }
    }
    if !ended {
        return Err("sidecar lacks complete suite terminal".into());
    }
    Ok(ParsedStream {
        suite,
        mode,
        host,
        target,
        selected: selected.unwrap_or(0),
        passed,
        failed,
        ignored,
        filtered_out: filtered_out.expect("suite terminal checked"),
        cases: cases
            .into_iter()
            .map(|(name, case)| CaseOutcome {
                name,
                outcome: case.outcome.expect("terminal checked"),
                timed_out: case.timed_out,
            })
            .collect(),
    })
}

fn canonical_file_name(name: &str) -> bool {
    let Some((pid, serial)) = name
        .strip_prefix(PREFIX)
        .and_then(|name| name.strip_suffix(SUFFIX))
        .and_then(|stem| stem.split_once('-'))
    else {
        return false;
    };
    let canonical = |value: &str| value.parse::<u64>().is_ok_and(|n| n.to_string() == value);
    canonical(pid) && pid != "0" && canonical(serial)
}

// O_NOFOLLOW and O_NONBLOCK are not exposed by std. Keep platform values
// explicit and fail closed on targets without reviewed values. Nonblocking
// open also prevents a file-to-FIFO replacement from stalling before fstat.
#[cfg(any(
    target_os = "macos",
    target_os = "ios",
    target_os = "freebsd",
    target_os = "netbsd",
    target_os = "openbsd",
    target_os = "dragonfly"
))]
const NOFOLLOW_FLAG: i32 = 0x100;
#[cfg(any(
    target_os = "macos",
    target_os = "ios",
    target_os = "freebsd",
    target_os = "netbsd",
    target_os = "openbsd",
    target_os = "dragonfly"
))]
const NONBLOCK_FLAG: i32 = 0x4;
#[cfg(all(target_os = "linux", any(target_arch = "x86", target_arch = "x86_64")))]
const NOFOLLOW_FLAG: i32 = 0x20000;
#[cfg(all(target_os = "linux", target_arch = "aarch64"))]
const NOFOLLOW_FLAG: i32 = 0x8000;
#[cfg(all(
    target_os = "linux",
    any(target_arch = "x86", target_arch = "x86_64", target_arch = "aarch64")
))]
const NONBLOCK_FLAG: i32 = 0x800;
#[cfg(any(target_os = "macos", target_os = "ios"))]
const CLOEXEC_FLAG: i32 = 0x01000000;
#[cfg(target_os = "freebsd")]
const CLOEXEC_FLAG: i32 = 0x00100000;
#[cfg(target_os = "dragonfly")]
const CLOEXEC_FLAG: i32 = 0x00020000;
#[cfg(target_os = "openbsd")]
const CLOEXEC_FLAG: i32 = 0x10000;
#[cfg(target_os = "netbsd")]
const CLOEXEC_FLAG: i32 = 0x400000;
#[cfg(all(
    target_os = "linux",
    any(target_arch = "x86", target_arch = "x86_64", target_arch = "aarch64")
))]
const CLOEXEC_FLAG: i32 = 0x80000;

#[cfg(any(
    target_os = "macos",
    target_os = "ios",
    target_os = "freebsd",
    target_os = "netbsd",
    target_os = "openbsd",
    target_os = "dragonfly",
    all(
        target_os = "linux",
        any(target_arch = "x86", target_arch = "x86_64", target_arch = "aarch64")
    )
))]
unsafe extern "C" {
    fn openat(directory: i32, path: *const std::ffi::c_char, flags: i32, ...) -> i32;
}

#[cfg(any(
    target_os = "macos",
    target_os = "ios",
    target_os = "freebsd",
    target_os = "netbsd",
    target_os = "openbsd",
    target_os = "dragonfly",
    all(
        target_os = "linux",
        any(target_arch = "x86", target_arch = "x86_64", target_arch = "aarch64")
    )
))]
fn open_nofollow(path: &Path) -> Result<File, String> {
    fs::OpenOptions::new()
        .read(true)
        .custom_flags(NOFOLLOW_FLAG | NONBLOCK_FLAG)
        .open(path)
        .map_err(|error| format!("cannot open sidecar without following symlinks: {error}"))
}

#[cfg(not(any(
    target_os = "macos",
    target_os = "ios",
    target_os = "freebsd",
    target_os = "netbsd",
    target_os = "openbsd",
    target_os = "dragonfly",
    all(
        target_os = "linux",
        any(target_arch = "x86", target_arch = "x86_64", target_arch = "aarch64")
    )
)))]
fn open_nofollow(_path: &Path) -> Result<File, String> {
    Err("sidecar O_NOFOLLOW is unavailable on this target".into())
}

#[cfg(any(
    target_os = "macos",
    target_os = "ios",
    target_os = "freebsd",
    target_os = "netbsd",
    target_os = "openbsd",
    target_os = "dragonfly",
    all(
        target_os = "linux",
        any(target_arch = "x86", target_arch = "x86_64", target_arch = "aarch64")
    )
))]
fn open_at_nofollow(directory: &File, name: &str) -> Result<File, String> {
    let name = CString::new(name).map_err(|_| "sidecar filename contains NUL".to_string())?;
    // The directory fd is already checked; openat keeps the leaf bound to it.
    let fd = unsafe {
        openat(directory.as_raw_fd(), name.as_ptr(), NOFOLLOW_FLAG | NONBLOCK_FLAG | CLOEXEC_FLAG)
    };
    if fd < 0 {
        return Err(format!(
            "cannot open sidecar relative to proof directory: {}",
            std::io::Error::last_os_error()
        ));
    }
    // openat returned an owned descriptor on success.
    Ok(unsafe { File::from_raw_fd(fd) })
}

#[cfg(not(any(
    target_os = "macos",
    target_os = "ios",
    target_os = "freebsd",
    target_os = "netbsd",
    target_os = "openbsd",
    target_os = "dragonfly",
    all(
        target_os = "linux",
        any(target_arch = "x86", target_arch = "x86_64", target_arch = "aarch64")
    )
)))]
fn open_at_nofollow(_directory: &File, _name: &str) -> Result<File, String> {
    Err("sidecar openat O_NOFOLLOW is unavailable on this target".into())
}

#[cfg(any(target_os = "macos", target_os = "ios", target_os = "freebsd"))]
fn errno_location() -> *mut libc::c_int {
    unsafe { libc::__error() }
}

#[cfg(any(target_os = "netbsd", target_os = "openbsd"))]
fn errno_location() -> *mut libc::c_int {
    unsafe { libc::__errno() }
}

#[cfg(any(
    target_os = "dragonfly",
    all(
        target_os = "linux",
        any(target_arch = "x86", target_arch = "x86_64", target_arch = "aarch64")
    )
))]
fn errno_location() -> *mut libc::c_int {
    unsafe { libc::__errno_location() }
}

#[cfg(any(
    target_os = "macos",
    target_os = "ios",
    target_os = "freebsd",
    target_os = "netbsd",
    target_os = "openbsd",
    target_os = "dragonfly",
    all(
        target_os = "linux",
        any(target_arch = "x86", target_arch = "x86_64", target_arch = "aarch64")
    )
))]
fn enumerate_sidecar_names(directory: &File, diagnostics: &mut Vec<String>) -> Vec<String> {
    let clone = match directory.try_clone() {
        Ok(clone) => clone,
        Err(error) => {
            diagnostic(diagnostics, format!("cannot clone proof directory: {error}"));
            return Vec::new();
        }
    };
    let stream = unsafe { libc::fdopendir(clone.as_raw_fd()) };
    if stream.is_null() {
        diagnostic(
            diagnostics,
            format!("cannot enumerate proof directory: {}", std::io::Error::last_os_error()),
        );
        return Vec::new();
    }
    std::mem::forget(clone); // closedir now owns the cloned descriptor.
    let stream = DirectoryStream(stream);
    let mut names = Vec::new();
    let mut entry_count = 0;
    loop {
        unsafe { *errno_location() = 0 };
        let entry = unsafe { libc::readdir(stream.0) };
        if entry.is_null() {
            let errno = unsafe { *errno_location() };
            if errno != 0 {
                diagnostic(
                    diagnostics,
                    format!(
                        "cannot enumerate proof directory: {}",
                        std::io::Error::from_raw_os_error(errno)
                    ),
                );
            }
            break;
        }
        let name = unsafe { CStr::from_ptr((*entry).d_name.as_ptr()) }.to_bytes();
        if name == b"." || name == b".." {
            continue;
        }
        if entry_count >= MAX_DIRECTORY_ENTRIES {
            diagnostic(diagnostics, "proof directory entry count exceeds bound");
            break;
        }
        entry_count += 1;
        match std::str::from_utf8(name) {
            Ok(name) if name.starts_with(PREFIX) => names.push(name.to_owned()),
            Ok(_) => {}
            Err(_) => diagnostic(diagnostics, "proof directory contains a non-UTF-8 filename"),
        }
    }
    names
}

#[cfg(not(any(
    target_os = "macos",
    target_os = "ios",
    target_os = "freebsd",
    target_os = "netbsd",
    target_os = "openbsd",
    target_os = "dragonfly",
    all(
        target_os = "linux",
        any(target_arch = "x86", target_arch = "x86_64", target_arch = "aarch64")
    )
)))]
fn enumerate_sidecar_names(_directory: &File, diagnostics: &mut Vec<String>) -> Vec<String> {
    diagnostic(
        diagnostics,
        "descriptor-bound proof directory enumeration is unavailable on this target",
    );
    Vec::new()
}

#[cfg(unix)]
fn same_metadata(left: &fs::Metadata, right: &fs::Metadata) -> bool {
    left.dev() == right.dev()
        && left.ino() == right.ino()
        && left.len() == right.len()
        && left.mtime() == right.mtime()
        && left.mtime_nsec() == right.mtime_nsec()
        && left.ctime() == right.ctime()
        && left.ctime_nsec() == right.ctime_nsec()
}

#[cfg(unix)]
fn same_snapshot(left: &fs::Metadata, right: &fs::Metadata) -> bool {
    left.file_type().is_file() && right.file_type().is_file() && same_metadata(left, right)
}

#[cfg(unix)]
fn same_directory_snapshot(left: &fs::Metadata, right: &fs::Metadata) -> bool {
    left.file_type().is_dir() && right.file_type().is_dir() && same_metadata(left, right)
}

#[cfg(not(unix))]
fn same_snapshot(_left: &fs::Metadata, _right: &fs::Metadata) -> bool {
    false
}

#[cfg(not(unix))]
fn same_directory_snapshot(_left: &fs::Metadata, _right: &fs::Metadata) -> bool {
    false
}

fn open_proof_directory(path: &Path) -> Result<(File, fs::Metadata), String> {
    let before = fs::symlink_metadata(path)
        .map_err(|error| format!("cannot stat proof directory: {error}"))?;
    if !before.file_type().is_dir() {
        return Err("proof directory is not a directory or is a symlink".into());
    }
    let directory = open_nofollow(path)?;
    let opened =
        directory.metadata().map_err(|error| format!("cannot fstat proof directory: {error}"))?;
    if !same_directory_snapshot(&before, &opened) {
        return Err("proof directory identity or metadata changed before open".into());
    }
    Ok((directory, opened))
}

fn directory_unchanged(path: &Path, directory: &File, opened: &fs::Metadata) -> Result<(), String> {
    let after_fd =
        directory.metadata().map_err(|error| format!("cannot fstat proof directory: {error}"))?;
    let after_path = fs::symlink_metadata(path)
        .map_err(|error| format!("cannot restat proof directory: {error}"))?;
    if !same_directory_snapshot(opened, &after_fd) || !same_directory_snapshot(opened, &after_path)
    {
        return Err("proof directory identity or metadata changed while reading".into());
    }
    Ok(())
}

fn read_file(proof_dir: &Path, directory: &File, name: String, budget: &mut u64) -> SidecarFile {
    let mut file_report = SidecarFile::new(name);
    let result = (|| -> Result<ParsedStream, String> {
        let path = proof_dir.join(&file_report.name);
        let before =
            fs::symlink_metadata(&path).map_err(|error| format!("cannot stat sidecar: {error}"))?;
        if !before.file_type().is_file() {
            return Err("sidecar is not a regular file".into());
        }
        let mut file = open_at_nofollow(directory, &file_report.name)?;
        let opened = file.metadata().map_err(|error| format!("cannot fstat sidecar: {error}"))?;
        if !same_snapshot(&before, &opened) {
            return Err("sidecar identity or metadata changed before open".into());
        }
        file_report.bytes = Some(opened.len());
        if opened.len() > MAX_FILE_BYTES || opened.len() > *budget {
            return Err("sidecar exceeds file or cumulative byte bound".into());
        }
        *budget -= opened.len();
        let mut bytes = Vec::new();
        (&mut file)
            .take(opened.len() + 1)
            .read_to_end(&mut bytes)
            .map_err(|error| format!("cannot read sidecar: {error}"))?;
        file_report.sha256 = Some(sha256_bytes(&bytes));
        let after_fd = file.metadata().map_err(|error| format!("cannot fstat sidecar: {error}"))?;
        let after_path = fs::symlink_metadata(&path)
            .map_err(|error| format!("cannot restat sidecar: {error}"))?;
        if !same_snapshot(&opened, &after_fd) || !same_snapshot(&opened, &after_path) {
            return Err("sidecar identity or metadata changed while reading".into());
        }
        if bytes.len() as u64 != opened.len() {
            return Err("sidecar changed while reading or exceeded byte bound".into());
        }
        if !canonical_file_name(&file_report.name) {
            return Err(
                "sidecar filename is not canonical compiletest-events-PID-SERIAL.jsonl".into()
            );
        }
        parse_stream(&bytes)
    })();
    match result {
        Ok(stream) => {
            file_report.valid = true;
            file_report.suite = Some(stream.suite);
            file_report.mode = Some(stream.mode);
            file_report.host = Some(stream.host);
            file_report.target = Some(stream.target);
            file_report.selected_count = Some(stream.selected);
            file_report.passed = Some(stream.passed);
            file_report.failed = Some(stream.failed);
            file_report.ignored = Some(stream.ignored);
            file_report.filtered_out = Some(stream.filtered_out);
            file_report.cases = stream.cases;
        }
        Err(error) => file_report.diagnostics.push(error),
    }
    file_report
}

fn compare_ui(
    files: &[SidecarFile],
    roster: &[UiCase],
    observations: &[Observation],
    streams_valid: bool,
    expected_host: Option<&str>,
    expected_target: Option<&str>,
) -> UiComparison {
    let ui_files =
        files.iter().filter(|file| file.suite.as_deref() == Some("ui")).collect::<Vec<_>>();
    let expected = roster.iter().map(|case| case.id.as_str()).collect::<BTreeSet<_>>();
    let mut observed = BTreeMap::<&str, Vec<&CaseOutcome>>::new();
    for file in &ui_files {
        for case in &file.cases {
            observed.entry(&case.name).or_default().push(case);
        }
    }
    let mut diagnostics = Vec::new();
    let mut missing = 0;
    let mut unexpected = 0;
    let mut duplicate = 0;
    let mut foreign_ui_cases = 0;
    if expected.len() != roster.len() {
        diagnostic(&mut diagnostics, "pinned UI roster contains duplicate case identities");
    }
    if ui_files.len() != 1 || ui_files[0].mode.as_deref() != Some("ui") {
        diagnostic(
            &mut diagnostics,
            format!("expected one UI-mode sidecar, found {} UI suite sidecar(s)", ui_files.len()),
        );
    }
    for case in roster {
        match observed.get(case.id.as_str()).map(Vec::as_slice).unwrap_or(&[]) {
            [] => {
                missing += 1;
                diagnostic(&mut diagnostics, format!("missing sidecar UI case: {}", case.id));
            }
            [_, .., _] => {
                duplicate += 1;
                diagnostic(&mut diagnostics, format!("duplicate sidecar UI case: {}", case.id));
            }
            [_] => {}
        }
    }
    for (name, rows) in &observed {
        if !expected.contains(name) {
            unexpected += 1;
            diagnostic(
                &mut diagnostics,
                format!("unexpected sidecar UI case: {name} ({} record(s))", rows.len()),
            );
        }
    }
    for file in files.iter().filter(|file| file.suite.as_deref() != Some("ui")) {
        for case in &file.cases {
            if case.name.starts_with("[ui] tests/ui/") {
                foreign_ui_cases += 1;
                unexpected += 1;
                diagnostic(
                    &mut diagnostics,
                    format!("UI case in non-UI sidecar {}: {}", file.name, case.name),
                );
            }
        }
    }
    if ui_files.len() == 1 && ui_files[0].selected_count != Some(roster.len()) {
        diagnostic(
            &mut diagnostics,
            "UI sidecar selected count differs from pinned expanded roster",
        );
    }
    if ui_files.len() == 1 && ui_files[0].filtered_out != Some(0) {
        diagnostic(&mut diagnostics, "UI sidecar filtered out cases from the full roster");
    }
    let context_reconciled = match (
        expected_host.filter(|value| !value.is_empty()),
        expected_target.filter(|value| !value.is_empty()),
    ) {
        (Some(host), Some(target)) if ui_files.len() == 1 => {
            let file = ui_files[0];
            if file.host.as_deref() == Some(host) && file.target.as_deref() == Some(target) {
                true
            } else {
                diagnostic(
                    &mut diagnostics,
                    format!(
                        "UI invocation host/target mismatch: expected {host}/{target}, sidecar {:?}/{:?}",
                        file.host, file.target
                    ),
                );
                false
            }
        }
        (Some(_), Some(_)) => false,
        _ => {
            diagnostic(
                &mut diagnostics,
                "runner host/target context is unavailable for UI sidecars",
            );
            false
        }
    };
    let roster_reconciled = streams_valid
        && context_reconciled
        && expected.len() == roster.len()
        && ui_files.len() == 1
        && ui_files[0].mode.as_deref() == Some("ui")
        && ui_files[0].selected_count == Some(roster.len())
        && ui_files[0].filtered_out == Some(0)
        && missing == 0
        && unexpected == 0
        && duplicate == 0;
    let mut renderer = BTreeMap::<&str, Vec<&Observation>>::new();
    for row in observations
        .iter()
        .filter(|row| row.name.starts_with("[ui] ") || row.path.starts_with("tests/ui/"))
    {
        renderer.entry(&row.name).or_default().push(row);
    }
    let mut renderer_mismatches = 0;
    for case in roster {
        let sidecar = observed.get(case.id.as_str()).map(Vec::as_slice).unwrap_or(&[]);
        let rows = renderer.get(case.id.as_str()).map(Vec::as_slice).unwrap_or(&[]);
        if sidecar.len() != 1
            || rows.len() != 1
            || !rows[0].complete_suite
            || rows[0].outcome != sidecar[0].outcome
        {
            renderer_mismatches += 1;
            diagnostic(&mut diagnostics, format!("sidecar/renderer UI mismatch: {}", case.id));
        }
    }
    for name in renderer.keys() {
        if !expected.contains(name) {
            renderer_mismatches += 1;
            diagnostic(&mut diagnostics, format!("unexpected renderer UI case: {name}"));
        }
    }
    UiComparison {
        expected_cases: roster.len(),
        sidecar_cases: observed.values().map(Vec::len).sum::<usize>() + foreign_ui_cases,
        ui_streams: ui_files.len(),
        missing_cases: missing,
        unexpected_cases: unexpected,
        duplicate_cases: duplicate,
        renderer_mismatches,
        context_reconciled,
        roster_reconciled,
        renderer_reconciled: roster_reconciled && renderer_mismatches == 0,
        diagnostics,
    }
}

pub(super) fn inspect(
    proof_dir: &Path,
    ui_roster: Option<&[UiCase]>,
    observations: &[Observation],
    expected_host: Option<&str>,
    expected_target: Option<&str>,
) -> SidecarReport {
    let mut diagnostics = Vec::new();
    let mut names = Vec::new();
    let anchor = match open_proof_directory(proof_dir) {
        Ok(anchor) => Some(anchor),
        Err(error) => {
            diagnostic(&mut diagnostics, error);
            None
        }
    };
    if let Some((directory, opened)) = &anchor {
        names = enumerate_sidecar_names(directory, &mut diagnostics);
        if let Err(error) = directory_unchanged(proof_dir, directory, opened) {
            diagnostic(&mut diagnostics, error);
        }
    }
    names.sort();
    if names.is_empty() {
        diagnostic(&mut diagnostics, "no compiletest sidecar files found");
    }
    if names.len() > MAX_FILES {
        diagnostic(
            &mut diagnostics,
            format!("compiletest sidecar file count {} exceeds bound {MAX_FILES}", names.len()),
        );
    }
    let mut budget = MAX_TOTAL_BYTES;
    let files = match &anchor {
        Some((directory, _)) => names
            .into_iter()
            .take(MAX_FILES)
            .map(|name| read_file(proof_dir, directory, name, &mut budget))
            .collect::<Vec<_>>(),
        None => Vec::new(),
    };
    if let Some((directory, opened)) = &anchor {
        if let Err(error) = directory_unchanged(proof_dir, directory, opened) {
            diagnostic(&mut diagnostics, error);
        }
    }
    for file in &files {
        for problem in &file.diagnostics {
            diagnostic(&mut diagnostics, format!("{}: {problem}", file.name));
        }
    }
    let streams_valid = diagnostics.is_empty() && files.iter().all(|file| file.valid);
    let ui = ui_roster.map(|roster| {
        compare_ui(&files, roster, observations, streams_valid, expected_host, expected_target)
    });
    SidecarReport {
        schema: REPORT_SCHEMA,
        authority: "diagnostic_only; not independently authenticated",
        streams_valid,
        files,
        ui,
        diagnostics,
    }
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;
    use std::sync::atomic::{AtomicU64, Ordering};

    use serde_json::{json, to_value};

    use super::*;

    struct Fixture(PathBuf);

    impl Fixture {
        fn new() -> Self {
            static NEXT: AtomicU64 = AtomicU64::new(0);
            let path = std::env::temp_dir().join(format!(
                "trust-case-events-{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
            fs::create_dir(&path).unwrap();
            Self(path)
        }

        fn write(&self, name: &str, lines: &[Value]) -> PathBuf {
            let path = self.0.join(name);
            let bytes = lines.iter().map(|line| format!("{line}\n")).collect::<String>();
            fs::write(&path, bytes).unwrap();
            path
        }
    }

    impl Drop for Fixture {
        fn drop(&mut self) {
            fs::remove_dir_all(&self.0).unwrap();
        }
    }

    fn ui_case(name: &str) -> UiCase {
        UiCase { id: name.into(), path: "tests/ui/a.rs".into(), source_git_blob: "a".repeat(40) }
    }

    const TEST_TRIPLE: &str = "x86_64-unknown-linux-gnu";

    fn inspect_with_context(
        proof_dir: &Path,
        roster: Option<&[UiCase]>,
        observations: &[Observation],
    ) -> SidecarReport {
        inspect(proof_dir, roster, observations, Some(TEST_TRIPLE), Some(TEST_TRIPLE))
    }

    fn stream(name: &str, result: &str) -> Vec<Value> {
        vec![
            json!({"schema": EVENT_SCHEMA, "type": "invocation", "argv": ["--suite", "ui", "--mode", "ui", "--host", "x86_64-unknown-linux-gnu", "--target", "x86_64-unknown-linux-gnu"]}),
            json!({"schema": EVENT_SCHEMA, "type": "suite", "event": "started", "test_count": 1, "selected_count": 1}),
            json!({"schema": EVENT_SCHEMA, "type": "test", "event": "started", "name": name}),
            json!({"schema": EVENT_SCHEMA, "type": "test", "event": result, "name": name, "message": null, "stdout": null}),
            json!({"schema": EVENT_SCHEMA, "type": "suite", "event": if result == "failed" { "failed" } else { "ok" }, "selected_count": 1, "executed_count": if result == "ignored" { 0 } else { 1 }, "terminal_count": 1, "protocol_valid": true, "protocol_error": null, "passed": if result == "ok" { 1 } else { 0 }, "failed": if result == "failed" { 1 } else { 0 }, "ignored": if result == "ignored" { 1 } else { 0 }, "measured": 0, "filtered_out": 0, "exec_time": 0.1}),
        ]
    }

    #[test]
    fn accepts_complete_sidecar_and_retains_hash_without_authentication() {
        let fixture = Fixture::new();
        let name = "[ui] tests/ui/a.rs#rev";
        let path = fixture.write("compiletest-events-42-0.jsonl", &stream(name, "ok"));
        let renderer = super::super::observations::parse_log(&format!(
            "running 1 tests\ntest {name} ... ok\ntest result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out\n"
        ));
        let report =
            to_value(inspect_with_context(&fixture.0, Some(&[ui_case(name)]), &renderer)).unwrap();
        assert_eq!(report["streams_valid"], true);
        assert_eq!(report["ui"]["context_reconciled"], true);
        assert_eq!(report["ui"]["roster_reconciled"], true);
        assert_eq!(report["ui"]["renderer_reconciled"], true);
        assert_eq!(report["files"][0]["sha256"], sha256_bytes(&fs::read(path).unwrap()));
        assert_eq!(report["files"][0]["cases"][0]["outcome"], "passed");
        assert!(report["authority"].as_str().unwrap().contains("not independently authenticated"));
    }

    #[test]
    fn abbreviated_renderer_summary_cannot_reconcile_sidecar() {
        let fixture = Fixture::new();
        let name = "[ui] tests/ui/a.rs";
        fixture.write("compiletest-events-42-0.jsonl", &stream(name, "ok"));
        let roster = [ui_case(name)];
        let prefix = format!("running 1 tests\ntest {name} ... ok\n");
        let complete = super::super::observations::parse_log(&format!(
            "{prefix}test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out\n"
        ));
        let control = to_value(inspect_with_context(&fixture.0, Some(&roster), &complete)).unwrap();
        assert_eq!(control["streams_valid"], true);
        assert_eq!(control["ui"]["roster_reconciled"], true);
        assert_eq!(control["ui"]["renderer_reconciled"], true);

        let abbreviated = super::super::observations::parse_log(&format!(
            "{prefix}test result: ok. 1 passed; 0 failed; 0 ignored\n"
        ));
        let report =
            to_value(inspect_with_context(&fixture.0, Some(&roster), &abbreviated)).unwrap();
        assert_eq!(report["streams_valid"], true);
        assert_eq!(report["ui"]["roster_reconciled"], true);
        assert_eq!(report["ui"]["renderer_mismatches"], 1);
        assert_eq!(report["ui"]["renderer_reconciled"], false);
    }

    #[test]
    fn ui_context_must_match_runner_host_and_target() {
        let name = "[ui] tests/ui/a.rs";
        let renderer = super::super::observations::parse_log(&format!(
            "running 1 tests\ntest {name} ... ok\ntest result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out\n"
        ));
        for (index, label) in [(5, "host"), (7, "target")] {
            let fixture = Fixture::new();
            let mut lines = stream(name, "ok");
            lines[0]["argv"][index] = json!("other-triple");
            fixture.write("compiletest-events-42-0.jsonl", &lines);
            let report =
                to_value(inspect_with_context(&fixture.0, Some(&[ui_case(name)]), &renderer))
                    .unwrap();
            assert_eq!(report["streams_valid"], true, "{label}");
            assert_eq!(report["ui"]["context_reconciled"], false, "{label}");
            assert_eq!(report["ui"]["roster_reconciled"], false, "{label}");
            assert_eq!(report["ui"]["renderer_reconciled"], false, "{label}");
            assert!(
                report["ui"]["diagnostics"][0].as_str().unwrap().contains("host/target mismatch")
            );
        }

        let fixture = Fixture::new();
        fixture.write("compiletest-events-42-0.jsonl", &stream(name, "ok"));
        for (host, target) in [(None, Some(TEST_TRIPLE)), (Some(TEST_TRIPLE), None)] {
            let report =
                to_value(inspect(&fixture.0, Some(&[ui_case(name)]), &renderer, host, target))
                    .unwrap();
            assert_eq!(report["ui"]["context_reconciled"], false);
            assert_eq!(report["ui"]["roster_reconciled"], false);
            assert_eq!(report["ui"]["renderer_reconciled"], false);
        }
    }

    #[test]
    fn accepts_failed_and_ignored_terminal_outcomes_without_promoting_them() {
        let name = "[ui] tests/ui/a.rs";
        for (result, outcome) in [("failed", "failed"), ("ignored", "skipped")] {
            let fixture = Fixture::new();
            let mut lines = stream(name, result);
            lines.insert(
                3,
                json!({"schema": EVENT_SCHEMA, "type": "test", "event": "timeout", "name": name}),
            );
            fixture.write("compiletest-events-42-0.jsonl", &lines);
            let report =
                to_value(inspect_with_context(&fixture.0, Some(&[ui_case(name)]), &[])).unwrap();
            assert_eq!(report["streams_valid"], true, "{result}");
            assert_eq!(report["ui"]["roster_reconciled"], true, "{result}");
            assert_eq!(report["files"][0]["cases"][0]["outcome"], outcome);
            assert_eq!(report["files"][0]["cases"][0]["timed_out"], true);
        }
    }

    #[test]
    fn rejects_missing_start_duplicate_terminal_and_false_counts() {
        let name = "[ui] tests/ui/a.rs";
        for (label, mut lines) in [
            ("missing-start", stream(name, "ok")),
            ("duplicate-terminal", stream(name, "ok")),
            ("wrong-count", stream(name, "ok")),
            ("duplicate-timeout", stream(name, "ok")),
        ] {
            match label {
                "missing-start" => {
                    lines.remove(2);
                }
                "duplicate-terminal" => {
                    lines.insert(4, lines[3].clone());
                }
                "duplicate-timeout" => {
                    let timeout = json!({"schema": EVENT_SCHEMA, "type": "test", "event": "timeout", "name": name});
                    lines.insert(3, timeout.clone());
                    lines.insert(4, timeout);
                }
                _ => {
                    lines[4]["terminal_count"] = json!(0);
                }
            }
            let fixture = Fixture::new();
            fixture.write("compiletest-events-42-0.jsonl", &lines);
            let report =
                to_value(inspect_with_context(&fixture.0, Some(&[ui_case(name)]), &[])).unwrap();
            assert_eq!(report["streams_valid"], false, "{label}");
            assert_eq!(report["ui"]["roster_reconciled"], false, "{label}");
            assert!(report["files"][0]["sha256"].is_string(), "{label}");
            if label == "duplicate-timeout" {
                assert!(
                    report["files"][0]["diagnostics"][0]
                        .as_str()
                        .unwrap()
                        .contains("duplicate case timeout")
                );
            }
        }
    }

    #[test]
    fn rejects_schema_shape_duplicate_keys_and_truncation() {
        let name = "[ui] tests/ui/a.rs";
        for (label, mut lines) in [
            ("schema", stream(name, "ok")),
            ("shape", stream(name, "ok")),
            ("truncated", stream(name, "ok")),
        ] {
            match label {
                "schema" => {
                    lines[1]["schema"] = json!("other");
                }
                "shape" => {
                    lines[2]["extra"] = json!(1);
                }
                _ => {
                    lines.pop();
                }
            }
            let fixture = Fixture::new();
            fixture.write("compiletest-events-42-0.jsonl", &lines);
            let report =
                to_value(inspect_with_context(&fixture.0, Some(&[ui_case(name)]), &[])).unwrap();
            assert_eq!(report["streams_valid"], false, "{label}");
        }
        let fixture = Fixture::new();
        let valid = stream(name, "ok");
        let mut bytes = valid.iter().map(|line| format!("{line}\n")).collect::<String>();
        bytes =
            bytes.replacen("\"selected_count\":1", "\"selected_count\":1,\"selected_count\":1", 1);
        fs::write(fixture.0.join("compiletest-events-42-0.jsonl"), bytes).unwrap();
        let report =
            to_value(inspect_with_context(&fixture.0, Some(&[ui_case(name)]), &[])).unwrap();
        assert_eq!(report["streams_valid"], false);
        assert!(report["diagnostics"][0].as_str().unwrap().contains("duplicate field"));
    }

    #[test]
    fn mismatched_and_duplicate_ui_rosters_fail_closed() {
        let fixture = Fixture::new();
        let name = "[ui] tests/ui/a.rs";
        fixture.write("compiletest-events-42-0.jsonl", &stream(name, "ok"));
        let report =
            to_value(inspect_with_context(&fixture.0, Some(&[ui_case("[ui] tests/ui/b.rs")]), &[]))
                .unwrap();
        assert_eq!(report["ui"]["missing_cases"], 1);
        assert_eq!(report["ui"]["unexpected_cases"], 1);
        assert_eq!(report["ui"]["roster_reconciled"], false);
        fixture.write("compiletest-events-43-0.jsonl", &stream(name, "ok"));
        let report =
            to_value(inspect_with_context(&fixture.0, Some(&[ui_case(name)]), &[])).unwrap();
        assert_eq!(report["ui"]["duplicate_cases"], 1);
        assert_eq!(report["ui"]["roster_reconciled"], false);
    }

    #[test]
    fn filtered_ui_cases_cannot_reconcile_full_roster() {
        let fixture = Fixture::new();
        let name = "[ui] tests/ui/a.rs";
        let filename = "compiletest-events-42-0.jsonl";
        let mut lines = stream(name, "ok");
        fixture.write(filename, &lines);
        let roster = [ui_case(name)];
        let control = to_value(inspect_with_context(&fixture.0, Some(&roster), &[])).unwrap();
        assert_eq!(control["streams_valid"], true);
        assert_eq!(control["files"][0]["filtered_out"], 0);
        assert_eq!(control["ui"]["roster_reconciled"], true);

        lines[4]["filtered_out"] = json!(1);
        fixture.write(filename, &lines);
        let report = to_value(inspect_with_context(&fixture.0, Some(&roster), &[])).unwrap();
        assert_eq!(report["streams_valid"], true);
        assert_eq!(report["files"][0]["filtered_out"], 1);
        assert_eq!(report["ui"]["roster_reconciled"], false);
        assert_eq!(report["ui"]["renderer_reconciled"], false);
        assert!(
            report["ui"]["diagnostics"]
                .as_array()
                .unwrap()
                .iter()
                .any(|entry| entry.as_str().unwrap().contains("filtered out cases"))
        );
    }

    #[test]
    fn ui_case_hidden_in_other_suite_cannot_reconcile_roster() {
        let fixture = Fixture::new();
        let name = "[ui] tests/ui/a.rs";
        fixture.write("compiletest-events-42-0.jsonl", &stream(name, "ok"));

        let mut other = stream("[ui] tests/rustdoc-ui/b.rs", "ok");
        other[0]["argv"][1] = json!("rustdoc-ui");
        fixture.write("compiletest-events-43-0.jsonl", &other);
        let control =
            to_value(inspect_with_context(&fixture.0, Some(&[ui_case(name)]), &[])).unwrap();
        assert_eq!(control["streams_valid"], true);
        assert_eq!(control["ui"]["roster_reconciled"], true);

        for foreign_name in [name, "[ui] tests/ui/b.rs"] {
            other[2]["name"] = json!(foreign_name);
            other[3]["name"] = json!(foreign_name);
            fixture.write("compiletest-events-43-0.jsonl", &other);
            let report =
                to_value(inspect_with_context(&fixture.0, Some(&[ui_case(name)]), &[])).unwrap();
            assert_eq!(report["streams_valid"], true, "{foreign_name}");
            assert_eq!(report["ui"]["roster_reconciled"], false, "{foreign_name}");
            assert_eq!(report["ui"]["renderer_reconciled"], false, "{foreign_name}");
            assert_eq!(report["ui"]["sidecar_cases"], 2, "{foreign_name}");
            assert_eq!(report["ui"]["unexpected_cases"], 1, "{foreign_name}");
            assert!(
                report["ui"]["diagnostics"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .any(|row| row.as_str().unwrap().contains("UI case in non-UI sidecar"))
            );
        }
    }

    #[cfg(any(
        target_os = "macos",
        all(target_os = "linux", any(target_arch = "x86_64", target_arch = "aarch64"))
    ))]
    #[test]
    fn descriptor_relative_open_uses_platform_flags_and_rejects_symlink() {
        use std::os::unix::fs::symlink;

        assert_eq!(NOFOLLOW_FLAG, libc::O_NOFOLLOW);
        assert_eq!(NONBLOCK_FLAG, libc::O_NONBLOCK);
        assert_eq!(CLOEXEC_FLAG, libc::O_CLOEXEC);

        let fixture = Fixture::new();
        let name = "compiletest-events-42-0.jsonl";
        let target = fixture.write("source.jsonl", &stream("[ui] tests/ui/a.rs", "ok"));
        symlink(target, fixture.0.join(name)).unwrap();
        let (directory, _) = open_proof_directory(&fixture.0).unwrap();
        assert!(open_at_nofollow(&directory, name).is_err());

        fs::remove_file(fixture.0.join(name)).unwrap();
        fixture.write(name, &stream("[ui] tests/ui/a.rs", "ok"));
        let opened = open_at_nofollow(&directory, name).unwrap();
        let flags = unsafe { libc::fcntl(opened.as_raw_fd(), libc::F_GETFD) };
        assert!(flags >= 0);
        assert_ne!(flags & libc::FD_CLOEXEC, 0);
    }

    #[test]
    fn oversized_and_missing_sidecars_never_reconcile() {
        let fixture = Fixture::new();
        let name = "[ui] tests/ui/a.rs";
        let empty =
            to_value(inspect_with_context(&fixture.0, Some(&[ui_case(name)]), &[])).unwrap();
        assert_eq!(empty["streams_valid"], false);
        assert_eq!(empty["ui"]["roster_reconciled"], false);
        let path = fixture.0.join("compiletest-events-42-0.jsonl");
        let file = File::create(path).unwrap();
        file.set_len(MAX_FILE_BYTES + 1).unwrap();
        let report =
            to_value(inspect_with_context(&fixture.0, Some(&[ui_case(name)]), &[])).unwrap();
        assert_eq!(report["streams_valid"], false);
        assert!(report["files"][0]["diagnostics"][0].as_str().unwrap().contains("byte bound"));
    }

    #[test]
    fn sidecar_file_population_is_bounded() {
        let fixture = Fixture::new();
        let name = "[ui] tests/ui/a.rs";
        for serial in 0..=MAX_FILES {
            fixture.write(&format!("compiletest-events-42-{serial}.jsonl"), &stream(name, "ok"));
        }
        let report =
            to_value(inspect_with_context(&fixture.0, Some(&[ui_case(name)]), &[])).unwrap();
        assert_eq!(report["streams_valid"], false);
        assert_eq!(report["files"].as_array().unwrap().len(), MAX_FILES);
        assert!(
            report["diagnostics"]
                .as_array()
                .unwrap()
                .iter()
                .any(|entry| { entry.as_str().unwrap().contains("file count") })
        );
        assert_eq!(report["ui"]["roster_reconciled"], false);
    }

    #[cfg(unix)]
    #[test]
    fn symlinked_proof_directory_cannot_reconcile() {
        use std::os::unix::fs::symlink;

        let fixture = Fixture::new();
        let proof_dir = fixture.0.join("proof");
        fs::create_dir(&proof_dir).unwrap();
        fs::write(
            proof_dir.join("compiletest-events-42-0.jsonl"),
            stream("[ui] tests/ui/a.rs", "ok")
                .iter()
                .map(|line| format!("{line}\n"))
                .collect::<String>(),
        )
        .unwrap();
        let link = fixture.0.join("link");
        symlink(&proof_dir, &link).unwrap();
        let report =
            to_value(inspect_with_context(&link, Some(&[ui_case("[ui] tests/ui/a.rs")]), &[]))
                .unwrap();
        assert_eq!(report["streams_valid"], false);
        assert_eq!(report["ui"]["roster_reconciled"], false);
        assert!(
            report["diagnostics"][0]
                .as_str()
                .unwrap()
                .contains("proof directory is not a directory or is a symlink")
        );
    }

    #[cfg(unix)]
    #[test]
    fn replaced_proof_directory_cannot_rebind_leaf_open() {
        use std::os::unix::fs::symlink;

        for replacement_is_symlink in [false, true] {
            let fixture = Fixture::new();
            let proof_dir = fixture.0.join("proof");
            let alternate = fixture.0.join("alternate");
            let held = fixture.0.join("held");
            let filename = "compiletest-events-42-0.jsonl";
            fs::create_dir(&proof_dir).unwrap();
            fs::create_dir(&alternate).unwrap();
            let original = stream("[ui] tests/ui/a.rs", "ok")
                .iter()
                .map(|line| format!("{line}\n"))
                .collect::<String>();
            let replacement = stream("[ui] tests/ui/a.rs", "failed")
                .iter()
                .map(|line| format!("{line}\n"))
                .collect::<String>();
            fs::write(proof_dir.join(filename), &original).unwrap();
            fs::write(alternate.join(filename), &replacement).unwrap();
            let (directory, opened) = open_proof_directory(&proof_dir).unwrap();
            fs::rename(&proof_dir, &held).unwrap();
            if replacement_is_symlink {
                symlink(&alternate, &proof_dir).unwrap();
            } else {
                fs::rename(&alternate, &proof_dir).unwrap();
            }

            let mut anchored = String::new();
            open_at_nofollow(&directory, filename).unwrap().read_to_string(&mut anchored).unwrap();
            assert_eq!(anchored, original);
            assert_ne!(anchored, fs::read_to_string(proof_dir.join(filename)).unwrap());
            assert!(directory_unchanged(&proof_dir, &directory, &opened).is_err());
            let mut budget = MAX_TOTAL_BYTES;
            let file = read_file(&proof_dir, &directory, filename.into(), &mut budget);
            assert!(!file.valid);
            assert!(file.diagnostics[0].contains("identity or metadata changed before open"));
        }
    }

    #[cfg(unix)]
    #[test]
    fn ancestor_swap_cannot_hide_duplicate_ui_sidecar_during_enumeration() {
        let fixture = Fixture::new();
        let run = fixture.0.join("run");
        let proof_dir = run.join("proof");
        let alternate = fixture.0.join("alternate");
        let held = fixture.0.join("held");
        fs::create_dir_all(&proof_dir).unwrap();
        fs::create_dir_all(alternate.join("proof")).unwrap();
        let name = "[ui] tests/ui/a.rs";
        let good_file = "compiletest-events-42-0.jsonl";
        let duplicate_file = "compiletest-events-43-0.jsonl";
        let good = stream(name, "ok").iter().map(|line| format!("{line}\n")).collect::<String>();
        let failed =
            stream(name, "failed").iter().map(|line| format!("{line}\n")).collect::<String>();
        fs::write(proof_dir.join(good_file), &good).unwrap();
        fs::write(proof_dir.join(duplicate_file), &failed).unwrap();
        fs::write(alternate.join("proof").join(good_file), &good).unwrap();

        let (directory, opened) = open_proof_directory(&proof_dir).unwrap();
        fs::rename(&run, &held).unwrap();
        fs::rename(&alternate, &run).unwrap();
        assert_eq!(fs::read_dir(&proof_dir).unwrap().count(), 1);
        let mut diagnostics = Vec::new();
        let mut names = enumerate_sidecar_names(&directory, &mut diagnostics);
        fs::rename(&run, &alternate).unwrap();
        fs::rename(&held, &run).unwrap();

        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        assert!(directory_unchanged(&proof_dir, &directory, &opened).is_ok());
        names.sort();
        assert_eq!(names, [good_file, duplicate_file]);
        let mut budget = MAX_TOTAL_BYTES;
        let files = names
            .into_iter()
            .map(|name| read_file(&proof_dir, &directory, name, &mut budget))
            .collect::<Vec<_>>();
        assert!(files.iter().all(|file| file.valid));
        let roster = [ui_case(name)];
        let renderer = super::super::observations::parse_log(&format!(
            "running 1 tests\ntest {name} ... ok\ntest result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out\n"
        ));
        let comparison = to_value(compare_ui(
            &files,
            &roster,
            &renderer,
            true,
            Some(TEST_TRIPLE),
            Some(TEST_TRIPLE),
        ))
        .unwrap();
        assert_eq!(comparison["ui_streams"], 2);
        assert_eq!(comparison["roster_reconciled"], false);
        assert_eq!(comparison["renderer_reconciled"], false);
    }

    #[cfg(unix)]
    #[test]
    fn symlink_and_replaced_path_cannot_become_valid_sidecars() {
        use std::os::unix::fs::symlink;

        let fixture = Fixture::new();
        let name = "[ui] tests/ui/a.rs";
        let target = fixture.write("source.jsonl", &stream(name, "ok"));
        let sidecar = fixture.0.join("compiletest-events-42-0.jsonl");
        symlink(&target, &sidecar).unwrap();
        assert!(open_nofollow(&sidecar).is_err());
        let report =
            to_value(inspect_with_context(&fixture.0, Some(&[ui_case(name)]), &[])).unwrap();
        assert_eq!(report["streams_valid"], false);
        assert!(
            report["files"][0]["diagnostics"][0].as_str().unwrap().contains("not a regular file")
        );

        fs::remove_file(&sidecar).unwrap();
        fixture.write("compiletest-events-42-0.jsonl", &stream(name, "ok"));
        let before = fs::symlink_metadata(&sidecar).unwrap();
        let opened = open_nofollow(&sidecar).unwrap();
        let opened_metadata = opened.metadata().unwrap();
        assert!(same_snapshot(&before, &opened_metadata));
        fs::rename(&target, &sidecar).unwrap();
        let after = fs::symlink_metadata(&sidecar).unwrap();
        assert!(!same_snapshot(&opened_metadata, &after));
    }
}
