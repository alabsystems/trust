//! Lean/Lake readback consistency, not seed lineage or proof authority.

use std::fs::{self, OpenOptions};
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

const SCHEMA: &[u8] = b"trust.lean-toolchain-readback.v1";

fn invalid(message: &str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}

fn version(text: &str) -> bool {
    let mut parts = text.split('.');
    (0..3).all(|_| {
        parts
            .next()
            .is_some_and(|part| !part.is_empty() && part.bytes().all(|b| b.is_ascii_digit()))
    }) && parts.next().is_none()
}

fn pinned_version(pin: &str) -> Option<&str> {
    pin.strip_prefix("leanprover/lean4:v").filter(|s| version(s))
}

fn commit(text: &str) -> bool {
    (7..=40).contains(&text.len())
        && text.bytes().all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

fn host(text: &str) -> bool {
    (1..=128).contains(&text.len())
        && text.as_bytes()[0].is_ascii_alphanumeric()
        && text.bytes().all(|b| b.is_ascii_alphanumeric() || matches!(b, b'.' | b'_' | b'-'))
}

struct Lean<'a> {
    version: &'a str,
    host: &'a str,
    commit: &'a str,
}

fn lean_report(report: &str) -> Option<Lean<'_>> {
    let body = report.strip_prefix("Lean (version ")?.strip_suffix(')')?;
    let fields: Vec<_> = body.split(", ").collect();
    if fields.len() != 4
        || !version(fields[0])
        || !host(fields[1])
        || !matches!(fields[3], "Release" | "Debug")
    {
        return None;
    }
    let hash = fields[2].strip_prefix("commit ")?;
    commit(hash).then_some(Lean { version: fields[0], host: fields[1], commit: hash })
}

fn lake_report(report: &str) -> Option<(&str, &str)> {
    let body = report.strip_prefix("Lake version ")?.strip_suffix(')')?;
    let (lake, lean) = body.split_once(" (Lean version ")?;
    let (lake_version, hash) = lake.split_once('-')?;
    (version(lake_version) && commit(hash) && version(lean)).then_some((lean, hash))
}

struct Admitted {
    pin: String,
    lean_report: String,
    host: String,
    bin: PathBuf,
    core: PathBuf,
}

fn admit_reports(
    pin: &str,
    lean: &str,
    lake: &str,
    bin: &Path,
    prefix: &Path,
) -> io::Result<Admitted> {
    let wanted = pinned_version(pin);
    let parsed = lean_report(lean);
    let lake = lake_report(lake);
    let (Some(wanted), Some(parsed), Some((lake_version, lake_commit))) = (wanted, parsed, lake)
    else {
        return Err(invalid("unrecognized pinned Lean/Lake version report"));
    };
    if parsed.version != wanted || lake_version != wanted {
        return Err(invalid("selected Lean/Lake version differs from the pinned toolchain"));
    }
    if !parsed.commit.starts_with(lake_commit) {
        return Err(invalid("selected Lean and Lake report different Lean source commits"));
    }
    let bin = fs::canonicalize(bin)?;
    let prefix = fs::canonicalize(prefix)?;
    if !bin.is_dir() || !prefix.is_dir() || bin != prefix.join("bin") {
        return Err(invalid("selected Lean bin differs from its reported prefix"));
    }
    Ok(Admitted {
        pin: pin.into(),
        lean_report: lean.into(),
        host: parsed.host.into(),
        bin,
        core: prefix.join("lib/lean"),
    })
}

fn query(executable: &Path, option: &str) -> io::Result<Vec<u8>> {
    let output = Command::new(executable)
        .arg(option)
        .stdin(Stdio::null())
        .stderr(Stdio::inherit())
        .output()?;
    if !output.status.success() {
        return Err(io::Error::other(format!(
            "{} {option} failed ({})",
            executable.display(),
            output.status
        )));
    }
    // Match shell command substitution: remove trailing LF, not whitespace or
    // internal newlines (a real prefix may contain them).
    let mut data = output.stdout;
    while data.last() == Some(&b'\n') {
        data.pop();
    }
    Ok(data)
}

fn text(bytes: &[u8]) -> io::Result<&str> {
    std::str::from_utf8(bytes).map_err(|_| invalid("tool version report is not UTF-8"))
}

fn prefix_path(bytes: Vec<u8>) -> io::Result<PathBuf> {
    if bytes.is_empty() || bytes.contains(&0) {
        return Err(invalid("selected Lean returned an empty or invalid prefix"));
    }
    #[cfg(unix)]
    let path = {
        use std::os::unix::ffi::OsStringExt;
        PathBuf::from(std::ffi::OsString::from_vec(bytes))
    };
    #[cfg(not(unix))]
    let path = PathBuf::from(text(&bytes)?);
    if !path.is_absolute() {
        return Err(invalid("selected Lean must report an absolute prefix"));
    }
    Ok(path)
}

fn read_selected(source: &Path, bin: &Path) -> io::Result<Admitted> {
    let pin = fs::read_to_string(source.join("lean-toolchain"))?;
    let pin = pin.trim_end_matches('\n');
    if pinned_version(pin).is_none() {
        return Err(invalid("unrecognized pinned Lean/Lake version report"));
    }
    let bin = fs::canonicalize(bin)?;
    if !bin.is_dir() {
        return Err(invalid("selected Lean bin is not a directory"));
    }
    let lean = query(&bin.join("lean"), "--version")?;
    let prefix = prefix_path(query(&bin.join("lean"), "--print-prefix")?)?;
    let lake = query(&bin.join("lake"), "--version")?;
    let admitted = admit_reports(pin, text(&lean)?, text(&lake)?, &bin, &prefix)?;
    if !admitted.core.is_dir() {
        return Err(invalid("selected Lean core olean directory is missing"));
    }
    Ok(admitted)
}

fn write_report(admitted: &Admitted, path: &Path) -> io::Result<()> {
    // NUL framing preserves spaces/newlines in filesystem paths without a
    // shell quoting convention or another JSON/Python parser. Reports are data.
    let fields = [
        SCHEMA,
        admitted.host.as_bytes(),
        admitted.pin.as_bytes(),
        admitted.lean_report.as_bytes(),
        admitted.bin.as_os_str().as_encoded_bytes(),
        admitted.core.as_os_str().as_encoded_bytes(),
    ];
    let mut data = Vec::new();
    for field in fields {
        data.extend_from_slice(field);
        data.push(0);
    }
    let mut options = OpenOptions::new();
    options.write(true).create_new(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.mode(0o600);
    }
    let mut file = options.open(path)?;
    if let Err(error) = file.write_all(&data) {
        drop(file);
        let _ = fs::remove_file(path);
        return Err(error);
    }
    Ok(())
}

pub(super) fn admit(source: &Path, bin: &Path, report: &Path) -> io::Result<()> {
    write_report(&read_selected(source, bin)?, report)
}

#[cfg(test)]
mod tests {
    use std::sync::atomic::{AtomicUsize, Ordering};

    use super::*;
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    const PIN: &str = "leanprover/lean4:v4.8.0";
    const LEAN: &str =
        "Lean (version 4.8.0, aarch64-unknown-linux-gnu, commit df668f00e6c0, Release)";
    const LAKE: &str = "Lake version 5.0.0-df668f0 (Lean version 4.8.0)";

    struct Root(PathBuf);
    impl Root {
        fn new() -> Self {
            let path = std::env::temp_dir().join(format!(
                "tool-pair-{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
            fs::create_dir(&path).unwrap();
            fs::create_dir(path.join("bin")).unwrap();
            Self(path)
        }
        fn check(&self, pin: &str, lean: &str, lake: &str) -> io::Result<Admitted> {
            admit_reports(pin, lean, lake, &self.0.join("bin"), &self.0)
        }
    }
    impl Drop for Root {
        fn drop(&mut self) {
            fs::remove_dir_all(&self.0).unwrap();
        }
    }
    fn refusal(result: io::Result<Admitted>, reason: &str) {
        let error = result.err().expect("invalid tool pair admitted");
        assert!(error.to_string().contains(reason), "{error}");
    }

    #[test]
    fn actual_host_and_moved_prefix_are_retained() {
        let mut root = Root::new();
        assert_eq!(root.check(PIN, LEAN, LAKE).unwrap().host, "aarch64-unknown-linux-gnu");
        let moved = root.0.with_extension("moved");
        fs::rename(&root.0, &moved).unwrap();
        assert!(root.check(PIN, LEAN, LAKE).is_err());
        root.0 = moved;
        assert_eq!(root.check(PIN, LEAN, LAKE).unwrap().host, "aarch64-unknown-linux-gnu");
    }

    #[test]
    fn newer_lean_or_other_lake_version_cannot_be_relabelled() {
        let root = Root::new();
        refusal(
            root.check(PIN, &LEAN.replace("4.8.0", "4.33.0"), &LAKE.replace("4.8.0", "4.33.0")),
            "pinned toolchain",
        );
        refusal(root.check(PIN, LEAN, &LAKE.replace("4.8.0", "4.9.0")), "pinned toolchain");
    }

    #[test]
    fn source_commits_must_have_the_same_reported_prefix() {
        let root = Root::new();
        refusal(root.check(PIN, LEAN, &LAKE.replace("df668f0", "abcdef0")), "source commits");
        refusal(
            root.check(PIN, LEAN, &LAKE.replace("df668f0", "df668f00e6c0000")),
            "source commits",
        );
    }

    #[test]
    fn prefix_must_bind_the_selected_existing_directory() {
        let root = Root::new();
        let foreign = Root::new();
        refusal(admit_reports(PIN, LEAN, LAKE, &root.0.join("bin"), &foreign.0), "reported prefix");
        assert!(admit_reports(PIN, LEAN, LAKE, &root.0.join("missing"), &root.0).is_err());
    }

    #[test]
    fn malformed_reports_and_option_looking_data_refuse() {
        let root = Root::new();
        for lean in [
            format!("{LEAN}\nforged"),
            LEAN.replace("df668f00e6c0", "unknown"),
            "--help".into(),
            LEAN.replace("4.8.0", "4.٨.0"),
            LEAN.replace("Release", "Unknown"),
        ] {
            refusal(root.check(PIN, &lean, LAKE), "unrecognized");
        }
        refusal(root.check("leanprover/lean4:nightly", LEAN, LAKE), "unrecognized");
        refusal(root.check(PIN, LEAN, "--help"), "unrecognized");
    }

    #[test]
    fn host_and_commit_grammars_stay_closed() {
        let root = Root::new();
        for host in ["../linux", "-linux", "", "linux:forged", &"x".repeat(129)] {
            refusal(
                root.check(PIN, &LEAN.replace("aarch64-unknown-linux-gnu", host), LAKE),
                "unrecognized",
            );
        }
        for hash in ["abcdef", "ABCDEF0", &"a".repeat(41)] {
            refusal(root.check(PIN, &LEAN.replace("df668f00e6c0", hash), LAKE), "unrecognized");
        }
        assert!(root.check(PIN, &LEAN.replace("Release", "Debug"), LAKE).is_ok());
    }

    #[test]
    fn whitespace_and_numeric_versions_keep_exact_string_semantics() {
        let root = Root::new();
        let (pin, lean, lake) = (PIN, LEAN, LAKE);
        for bad in [
            format!(" {pin}"),
            format!("{pin} "),
            format!("{pin}\t"),
            format!("{pin}\r\n"),
            String::new(),
        ] {
            refusal(root.check(&bad, lean, lake), "unrecognized");
        }
        for bad in [
            format!(" {lean}"),
            format!("{lean} "),
            format!("{lean}\t"),
            format!("{lean}\r\n"),
            String::new(),
        ] {
            refusal(root.check(pin, &bad, lake), "unrecognized");
        }
        for bad in [
            format!(" {lake}"),
            format!("{lake} "),
            format!("{lake}\t"),
            format!("{lake}\r\n"),
            String::new(),
        ] {
            refusal(root.check(pin, lean, &bad), "unrecognized");
        }
        refusal(root.check("leanprover/lean4:v4.08.0", LEAN, LAKE), "pinned toolchain");
        let huge = format!("{}.8.0", "9".repeat(30));
        refusal(root.check(PIN, &LEAN.replace("4.8.0", &huge), LAKE), "pinned toolchain");
        assert!(
            root.check(
                &format!("leanprover/lean4:v{huge}"),
                &LEAN.replace("4.8.0", &huge),
                &LAKE.replace("4.8.0", &huge)
            )
            .is_ok()
        );
        assert!(root.check(PIN, LEAN, &LAKE.replace("5.0.0", "9.9.9")).is_ok());
    }

    #[test]
    fn report_is_framed_data_and_never_overwrites_existing_output() {
        let root = Root::new();
        let admitted = root.check(PIN, LEAN, LAKE).unwrap();
        let path = root.0.join("readback");
        write_report(&admitted, &path).unwrap();
        let bytes = fs::read(&path).unwrap();
        let fields: Vec<_> = bytes.split(|b| *b == 0).collect();
        assert_eq!(fields.len(), 7);
        assert_eq!(fields[0], SCHEMA);
        assert_eq!(fields[1], b"aarch64-unknown-linux-gnu");
        assert_eq!(fields[2], PIN.as_bytes());
        assert_eq!(fields[3], LEAN.as_bytes());
        assert!(fields[6].is_empty());
        assert!(write_report(&admitted, &path).is_err());
        assert_eq!(fs::read(path).unwrap(), bytes);
    }
}
