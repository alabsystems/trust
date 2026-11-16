//! Release an exited bootstrap child's exact build holder after tree shutdown.
//! This is ownership cleanup, never stale-lock takeover or a recovery policy.

use std::fs::{self, File, Metadata, OpenOptions};
use std::io::{self, Read};
use std::os::unix::fs::{MetadataExt, OpenOptionsExt};
use std::path::{Path, PathBuf};
use std::process::Command;

use build_helper::trust_build_lock::NamespaceGuard;

const LIMIT: u64 = 16 * 1024;

pub(super) struct ParentHandoff {
    pid: u32,
    start: String,
    start_utc: String,
    token: String,
    _nonce: tempfile::NamedTempFile,
}

impl ParentHandoff {
    pub(super) fn new() -> Result<Self, String> {
        let pid = std::process::id();
        let start = process_start(pid)?;
        let start_utc = process_start_utc(pid)?;
        let nonce = tempfile::Builder::new()
            .prefix("trust-native-repo-owner-")
            .rand_bytes(16)
            .tempfile()
            .map_err(|e| e.to_string())?;
        let token = nonce.path().file_name().unwrap().to_str().unwrap().to_owned();
        Ok(Self { pid, start, start_utc, token, _nonce: nonce })
    }

    /// `..._START` is this process's zoned start, which the child echoes into
    /// `release_parent_start` and `capture` compares with `self.start`, byte for
    /// byte. `..._START_UTC` (EW18-LOCKUTC-1) is what a current bootstrap
    /// compares with its own zone-free `ps` of this pid, so a child whose TZ or
    /// locale differs from ours still recognises its actual parent. An older
    /// bootstrap ignores it and compares the zoned start as before.
    pub(super) fn configure(&self, command: &mut Command) {
        command
            .env("TRUST_NATIVE_REPO_PARENT_PID", self.pid.to_string())
            .env("TRUST_NATIVE_REPO_PARENT_START", &self.start)
            .env("TRUST_NATIVE_REPO_PARENT_START_UTC", &self.start_utc)
            .env("TRUST_NATIVE_REPO_PARENT_TOKEN", &self.token);
    }
}

struct Snapshot {
    directory: Metadata,
    file: Metadata,
    bytes: Vec<u8>,
}

pub(super) struct HeldBuildLease {
    directory: PathBuf,
    snapshot: Snapshot,
}

impl HeldBuildLease {
    /// The caller still holds `pid` as its unreaped child, so it cannot name
    /// another process. A preexisting peer holder is never captured or removed.
    pub(super) fn capture(
        root: &Path,
        pid: u32,
        parent: &ParentHandoff,
    ) -> Result<Option<Self>, String> {
        let _namespace = NamespaceGuard::acquire(root).map_err(|e| e.to_string())?;
        let directory = root.join(".trust-build-lock");
        let Some(snapshot) = snapshot(&directory)? else {
            return Ok(None);
        };
        let text = std::str::from_utf8(&snapshot.bytes).map_err(|e| e.to_string())?;
        let owner = field(text, "pid")?.parse::<u32>().map_err(|e| e.to_string())?;
        if owner != pid {
            return Ok(None);
        }
        // The unreaped PID may have belonged to a stale holder before THIS
        // child started. Never turn that reuse into stale-lock takeover.
        //
        // EW18-LOCKUTC-1: `pstart` is in the WRITER's time zone and locale, so a
        // child that ran in another one read as a stranger. A record with
        // `pstart_utc` is judged by that zone-free field alone; one without it
        // (written by a bootstrap that predates the field) by `pstart`, exactly
        // as before. `pstart` is still required either way. A `pstart_utc` that
        // is present but empty cannot judge, so the holder is refused as
        // malformed and preserved; it never falls back to the zoned field.
        let zoned = field(text, "pstart")?;
        let same_process = match optional_field(text, "pstart_utc")? {
            Some(recorded) => recorded == process_start_utc(pid)?,
            None => zoned == process_start(pid)?,
        };
        if !same_process {
            return Ok(None);
        }
        if field(text, "release_parent_pid")? != parent.pid.to_string()
            || field(text, "release_parent_start")? != parent.start
            || field(text, "release_token")? != parent.token
        {
            return Err("native bootstrap did not acknowledge this parent's release handoff".into());
        }
        let token = field(text, "token")?;
        if !token.starts_with(".trust-build-lock.tmp.")
            || Path::new(token).file_name().and_then(|name| name.to_str()) != Some(token)
            || field(text, "kind")? != "build"
            || field(text, "pgid")?.parse::<u32>().map_err(|e| e.to_string())? != pid
        {
            return Err("refusing malformed native bootstrap build holder".into());
        }
        Ok(Some(Self { directory, snapshot }))
    }

    /// Call only after stop_tree succeeded with no remaining writers, while the
    /// leader is still unreaped. Preserve any replacement, even identical bytes
    /// in a different file/directory, rather than releasing another holder.
    pub(super) fn release(self) -> Result<(), String> {
        let root = self.directory.parent().ok_or("native holder has no root")?;
        let _namespace = NamespaceGuard::acquire(root).map_err(|e| e.to_string())?;
        let Some(current) = snapshot(&self.directory)? else {
            return Ok(());
        };
        if current.bytes != self.snapshot.bytes
            || !same(&current.directory, &self.snapshot.directory)
            || !same(&current.file, &self.snapshot.file)
        {
            return Err("native bootstrap build holder changed; preserving its replacement".into());
        }
        let entries = fs::read_dir(&self.directory)
            .map_err(|e| e.to_string())?
            .map(|entry| entry.map(|entry| entry.file_name()))
            .collect::<io::Result<Vec<_>>>()
            .map_err(|e| e.to_string())?;
        if entries.len() != 1 || entries[0] != "info" {
            return Err(
                "native bootstrap build holder has unexpected entries; preserving it".into()
            );
        }
        // Every current native/legacy mutation uses this same persistent
        // namespace guard. No initializer, recovery or third acquirer can
        // replace the public directory between exact validation and removal.
        fs::remove_file(self.directory.join("info")).map_err(|e| e.to_string())?;
        fs::remove_dir(&self.directory).map_err(|e| e.to_string())
    }
}

fn read_regular(file: File, expected: Option<&Metadata>) -> Result<(Metadata, Vec<u8>), String> {
    let before = file.metadata().map_err(|e| e.to_string())?;
    if !before.is_file()
        || before.len() > LIMIT
        || expected.is_some_and(|expected| !same(expected, &before))
    {
        return Err("native build holder changed before opening".into());
    }
    let mut reader = file.take(LIMIT + 1);
    let mut bytes = Vec::new();
    reader.read_to_end(&mut bytes).map_err(|e| e.to_string())?;
    if bytes.len() as u64 != before.len()
        || !same(&before, &reader.get_ref().metadata().map_err(|e| e.to_string())?)
    {
        return Err("native build holder moved while reading".into());
    }
    Ok((before, bytes))
}

pub(super) fn process_start(pid: u32) -> Result<String, String> {
    lstart(Command::new("ps"), pid)
}

/// `ps -o lstart=` with no time zone and no locale (EW18-LOCKUTC-1): LC_ALL=C
/// overrides LANG and every LC_* variable, and TZ=UTC0 is a POSIX zone spec that
/// needs no zoneinfo file, so the text is the same in every caller's environment.
pub(super) fn process_start_utc(pid: u32) -> Result<String, String> {
    lstart(zone_free_ps(), pid)
}

fn zone_free_ps() -> Command {
    let mut command = Command::new("ps");
    command.env("LC_ALL", "C").env("TZ", "UTC0").env_remove("LANG").env_remove("LC_TIME");
    command
}

fn lstart(mut command: Command, pid: u32) -> Result<String, String> {
    let output = command
        .args(["-o", "lstart=", "-p", &pid.to_string()])
        .output()
        .map_err(|e| e.to_string())?;
    let start = String::from_utf8(output.stdout).map_err(|e| e.to_string())?;
    if !output.status.success() || start.trim().is_empty() {
        return Err("cannot establish native bootstrap holder's process start".into());
    }
    Ok(start.trim().to_owned())
}

fn field<'a>(text: &'a str, key: &str) -> Result<&'a str, String> {
    let mut values = text.lines().filter_map(|line| {
        let (name, value) = line.split_once('=')?;
        (name == key).then_some(value)
    });
    let value = values.next().filter(|value| !value.is_empty());
    if values.next().is_some() {
        return Err(format!("duplicate native build holder field {key}"));
    }
    value.ok_or_else(|| format!("missing native build holder field {key}"))
}

/// A field a record may lack: `None` when absent. Present but empty is an error,
/// as is a duplicate, so the caller never mistakes either for absence.
fn optional_field<'a>(text: &'a str, key: &str) -> Result<Option<&'a str>, String> {
    let mut values = text.lines().filter_map(|line| {
        let (name, value) = line.split_once('=')?;
        (name == key).then_some(value)
    });
    let Some(value) = values.next() else {
        return Ok(None);
    };
    if values.next().is_some() {
        return Err(format!("duplicate native build holder field {key}"));
    }
    if value.is_empty() {
        return Err(format!("native build holder field {key} is present but empty"));
    }
    Ok(Some(value))
}

fn same(left: &Metadata, right: &Metadata) -> bool {
    left.dev() == right.dev()
        && left.ino() == right.ino()
        && left.mode() == right.mode()
        && left.len() == right.len()
        && left.mtime() == right.mtime()
        && left.mtime_nsec() == right.mtime_nsec()
        && left.ctime() == right.ctime()
        && left.ctime_nsec() == right.ctime_nsec()
}

fn snapshot(directory: &Path) -> Result<Option<Snapshot>, String> {
    let before_directory = match fs::symlink_metadata(directory) {
        Ok(metadata) => metadata,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(None),
        Err(error) => return Err(error.to_string()),
    };
    if !before_directory.is_dir() || before_directory.file_type().is_symlink() {
        return Err("native build holder is not an exact directory".into());
    }
    let path = directory.join("info");
    let before = fs::symlink_metadata(&path).map_err(|e| e.to_string())?;
    if !before.is_file() || before.file_type().is_symlink() || before.len() > LIMIT {
        return Err("native build holder info is not a bounded regular file".into());
    }
    let file = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK)
        .open(&path)
        .map_err(|e| e.to_string())?;
    let (_, bytes) = read_regular(file, Some(&before))?;
    if !same(&before, &fs::symlink_metadata(&path).map_err(|e| e.to_string())?)
        || !same(&before_directory, &fs::symlink_metadata(directory).map_err(|e| e.to_string())?)
    {
        return Err("native build holder moved while reading".into());
    }
    Ok(Some(Snapshot { directory: before_directory, file: before, bytes }))
}

#[cfg(test)]
mod tests {
    use std::fs;

    use super::{HeldBuildLease, ParentHandoff};

    /// A holder record as bootstrap writes it. `start_utc` is `None` for a record
    /// from a bootstrap that predates `pstart_utc` (EW18-LOCKUTC-1).
    fn record(pid: u32, start: &str, start_utc: Option<&str>, parent: &ParentHandoff) -> Vec<u8> {
        let start_utc = start_utc.map(|value| format!("pstart_utc={value}\n")).unwrap_or_default();
        format!(
            "token=.trust-build-lock.tmp.fixture\nkind=build\npid={pid}\npstart={start}\n{start_utc}pgid={pid}\nrelease_parent_pid={}\nrelease_parent_start={}\nrelease_token={}\n",
            parent.pid, parent.start, parent.token,
        )
        .into_bytes()
    }

    fn install(root: &std::path::Path, bytes: &[u8]) {
        fs::create_dir(root.join(".trust-build-lock")).unwrap();
        fs::write(root.join(".trust-build-lock/info"), bytes).unwrap();
    }

    fn fixture(root: &std::path::Path, pid: u32, parent: &ParentHandoff) -> Vec<u8> {
        let (start, start_utc) = if pid == std::process::id() {
            (super::process_start(pid).unwrap(), zoned_start(pid, "UTC0", Some("C")))
        } else {
            ("peer process".into(), "peer process".into())
        };
        let bytes = record(pid, &start, Some(&start_utc), parent);
        install(root, &bytes);
        bytes
    }

    /// `ps -o lstart=` for `pid` as a caller in `zone` (and `locale`) reads it.
    fn zoned_start(pid: u32, zone: &str, locale: Option<&str>) -> String {
        let mut command = std::process::Command::new("ps");
        command.args(["-o", "lstart=", "-p", &pid.to_string()]).env("TZ", zone);
        command.env_remove("LC_ALL");
        if let Some(locale) = locale {
            command.env("LC_ALL", locale);
        }
        let output = command.output().unwrap();
        assert!(output.status.success(), "{output:?}");
        String::from_utf8(output.stdout).unwrap().trim().to_owned()
    }

    /// This process's start as a writer in another time zone recorded it: the
    /// zoned text differs from what this reader's `ps` prints.
    fn start_elsewhere(pid: u32) -> String {
        let here = super::process_start(pid).unwrap();
        ["Asia/Tokyo", "America/Los_Angeles"]
            .map(|zone| zoned_start(pid, zone, None))
            .into_iter()
            .find(|start| *start != here)
            .unwrap()
    }

    /// EW18-LOCKUTC-1: a record that has `pstart_utc` is judged by it alone. A
    /// child that wrote its zoned `pstart` in another time zone is still this
    /// invocation's holder; a matching `pstart` does not rescue a `pstart_utc`
    /// that names another process; and an empty `pstart_utc` cannot judge, so the
    /// holder is refused and preserved rather than judged by the zoned field.
    #[test]
    fn a_record_with_pstart_utc_is_judged_by_it() {
        let pid = std::process::id();
        let here = super::process_start(pid).unwrap();
        let zone_free = zoned_start(pid, "UTC0", Some("C"));
        let elsewhere = start_elsewhere(pid);
        let parent = ParentHandoff::new().unwrap();
        let root = tempfile::tempdir().unwrap();
        install(root.path(), &record(pid, &elsewhere, Some(&zone_free), &parent));
        let held = HeldBuildLease::capture(root.path(), pid, &parent).unwrap();
        held.expect("a holder from another time zone is this invocation's holder")
            .release()
            .unwrap();
        assert!(!root.path().join(".trust-build-lock").exists());
        for (zone_free, refused) in [("Thu Jan  1 00:00:00 1970", false), ("", true)] {
            let root = tempfile::tempdir().unwrap();
            let bytes = record(pid, &here, Some(zone_free), &parent);
            install(root.path(), &bytes);
            let captured = HeldBuildLease::capture(root.path(), pid, &parent);
            match captured {
                Err(error) if refused => assert!(error.contains("present but empty"), "{error}"),
                Ok(None) if !refused => {}
                Err(error) => panic!("{zone_free:?}: refused: {error}"),
                Ok(held) => panic!("{zone_free:?}: captured: {}", held.is_some()),
            }
            assert_eq!(fs::read(root.path().join(".trust-build-lock/info")).unwrap(), bytes);
        }
    }

    /// A record from a bootstrap that predates `pstart_utc` is judged by `pstart`
    /// exactly as before: ours when it matches this reader's `ps`, and preserved
    /// as another process's when it does not, including when its writer was in
    /// another time zone. Nothing on disk says which zone wrote it.
    #[test]
    fn a_legacy_record_is_judged_by_pstart() {
        let pid = std::process::id();
        let parent = ParentHandoff::new().unwrap();
        let root = tempfile::tempdir().unwrap();
        install(root.path(), &record(pid, &super::process_start(pid).unwrap(), None, &parent));
        let held = HeldBuildLease::capture(root.path(), pid, &parent).unwrap();
        held.expect("a matching legacy pstart is this invocation's holder").release().unwrap();
        let root = tempfile::tempdir().unwrap();
        let bytes = record(pid, &start_elsewhere(pid), None, &parent);
        install(root.path(), &bytes);
        assert!(HeldBuildLease::capture(root.path(), pid, &parent).unwrap().is_none());
        assert_eq!(fs::read(root.path().join(".trust-build-lock/info")).unwrap(), bytes);
    }

    /// EW18-LOCKUTC-1: the handoff a child bootstrap reads. A current bootstrap
    /// identifies its parent by `..._START_UTC` alone when it is set and by the
    /// zoned `..._START` (the parent's own reading, in the parent's time zone)
    /// when it is not, so without it a child in another zone refuses its actual
    /// parent. The zone-free value must be this process's start as a `ps` with no
    /// zone or locale prints it; `..._START` keeps the zoned reading that the
    /// child echoes into `release_parent_start` for `capture` to compare.
    #[test]
    fn configure_sends_the_zone_free_parent_start() {
        let pid = std::process::id();
        let parent = ParentHandoff::new().unwrap();
        let mut command = std::process::Command::new("true");
        parent.configure(&mut command);
        let sent: std::collections::BTreeMap<String, Option<String>> = command
            .get_envs()
            .map(|(key, value)| {
                let text = |text: &std::ffi::OsStr| text.to_str().unwrap().to_owned();
                (text(key), value.map(text))
            })
            .collect();
        let value = |key: &str| sent.get(key).cloned().flatten();
        assert_eq!(value("TRUST_NATIVE_REPO_PARENT_PID"), Some(pid.to_string()));
        assert_eq!(value("TRUST_NATIVE_REPO_PARENT_START"), Some(parent.start.clone()));
        assert_eq!(value("TRUST_NATIVE_REPO_PARENT_TOKEN"), Some(parent.token.clone()));
        let zone_free = zoned_start(pid, "UTC0", Some("C"));
        assert!(!zone_free.is_empty());
        assert_eq!(value("TRUST_NATIVE_REPO_PARENT_START_UTC"), Some(zone_free));
        assert_eq!(sent.len(), 4, "{sent:?}");
    }

    // Every comparison in these tests runs in the test's own locale, so none could
    // tell a zone-free reading that kept the caller's locale from one that did not
    // (EW18-LOCKUTC-1, final review). This pins the override itself: a targo run
    // under LANG=fr_FR would otherwise send its parent start in French, and
    // bootstrap, reading in C, would refuse its actual parent.
    #[test]
    fn the_zone_free_reading_overrides_the_callers_zone_and_locale() {
        let command = super::zone_free_ps();
        let set: std::collections::BTreeMap<String, Option<String>> = command
            .get_envs()
            .map(|(key, value)| {
                let text = |text: &std::ffi::OsStr| text.to_str().unwrap().to_owned();
                (text(key), value.map(text))
            })
            .collect();
        assert_eq!(set.get("LC_ALL"), Some(&Some("C".to_owned())), "{set:?}");
        assert_eq!(set.get("TZ"), Some(&Some("UTC0".to_owned())), "{set:?}");
        assert_eq!(set.get("LANG"), Some(&None), "{set:?}");
        assert_eq!(set.get("LC_TIME"), Some(&None), "{set:?}");
        assert_eq!(command.get_program(), "ps");
    }

    #[test]
    fn peer_and_legacy_holders_are_never_released() {
        let root = tempfile::tempdir().unwrap();
        let pid = std::process::id();
        let parent = ParentHandoff::new().unwrap();
        fs::write(root.path().join(".trust-measurement-in-flight"), b"legacy holder").unwrap();
        let bytes = fixture(root.path(), pid.wrapping_add(1), &parent);
        assert!(HeldBuildLease::capture(root.path(), pid, &parent).unwrap().is_none());
        assert_eq!(fs::read(root.path().join(".trust-build-lock/info")).unwrap(), bytes);
        assert_eq!(
            fs::read(root.path().join(".trust-measurement-in-flight")).unwrap(),
            b"legacy holder"
        );
    }

    #[test]
    fn changed_or_replaced_holder_is_preserved() {
        for change in ["bytes", "file", "directory", "symlink", "fifo"] {
            let root = tempfile::tempdir().unwrap();
            let pid = std::process::id();
            let parent = ParentHandoff::new().unwrap();
            let bytes = fixture(root.path(), pid, &parent);
            let held = HeldBuildLease::capture(root.path(), pid, &parent).unwrap().unwrap();
            let directory = root.path().join(".trust-build-lock");
            let info = directory.join("info");
            match change {
                "bytes" => fs::write(&info, b"replacement peer holder").unwrap(),
                "file" => {
                    fs::rename(&info, root.path().join("preserved-info")).unwrap();
                    fs::write(&info, &bytes).unwrap();
                }
                "directory" => {
                    fs::rename(&directory, root.path().join("preserved-directory")).unwrap();
                    fixture(root.path(), pid, &parent);
                }
                "symlink" => {
                    let preserved = root.path().join("preserved-info");
                    fs::rename(&info, &preserved).unwrap();
                    std::os::unix::fs::symlink(preserved, &info).unwrap();
                }
                _ => {
                    fs::remove_file(&info).unwrap();
                    assert!(
                        std::process::Command::new("mkfifo").arg(&info).status().unwrap().success()
                    );
                }
            }
            assert!(held.release().is_err(), "{change}");
            assert!(fs::symlink_metadata(&info).is_ok(), "preserve {change}");
        }
    }

    #[test]
    fn malformed_or_oversized_native_holder_is_refused() {
        let pid = std::process::id();
        for changed in [
            format!("token=foreign\nkind=build\npid={pid}\n").into_bytes(),
            vec![b'x'; super::LIMIT as usize + 1],
        ] {
            let root = tempfile::tempdir().unwrap();
            let parent = ParentHandoff::new().unwrap();
            fixture(root.path(), pid, &parent);
            let info = root.path().join(".trust-build-lock/info");
            fs::write(&info, &changed).unwrap();
            assert!(HeldBuildLease::capture(root.path(), pid, &parent).is_err());
            assert_eq!(fs::read(&info).unwrap(), changed);
        }
    }

    #[test]
    fn stale_holder_with_the_same_pid_is_not_taken_over() {
        let root = tempfile::tempdir().unwrap();
        let pid = std::process::id();
        let parent = ParentHandoff::new().unwrap();
        fixture(root.path(), pid, &parent);
        let bytes = format!(
            "token=.trust-build-lock.tmp.stale\nkind=build\npid={pid}\npstart=previous process\npgid={pid}\n"
        );
        let info = root.path().join(".trust-build-lock/info");
        fs::write(&info, &bytes).unwrap();
        assert!(HeldBuildLease::capture(root.path(), pid, &parent).unwrap().is_none());
        assert_eq!(fs::read_to_string(&info).unwrap(), bytes);
    }

    #[test]
    fn a_different_invocations_handoff_cannot_release_the_holder() {
        let root = tempfile::tempdir().unwrap();
        let pid = std::process::id();
        let parent = ParentHandoff::new().unwrap();
        let other = ParentHandoff::new().unwrap();
        assert_ne!(parent.token, other.token);
        let bytes = fixture(root.path(), pid, &parent);
        assert!(HeldBuildLease::capture(root.path(), pid, &other).is_err());
        assert_eq!(fs::read(root.path().join(".trust-build-lock/info")).unwrap(), bytes);
    }

    #[test]
    fn guard_failure_retains_the_exact_holder() {
        let root = tempfile::tempdir().unwrap();
        let parent = ParentHandoff::new().unwrap();
        let bytes = fixture(root.path(), std::process::id(), &parent);
        let held =
            HeldBuildLease::capture(root.path(), std::process::id(), &parent).unwrap().unwrap();
        let guard = root.path().join(build_helper::trust_build_lock::GUARD_NAME);
        fs::write(&guard, b"invalid guard").unwrap();
        assert!(held.release().is_err());
        assert_eq!(fs::read(root.path().join(".trust-build-lock/info")).unwrap(), bytes);
    }
}
