// Trust: this file is Trust-owned. It pins the build directory's Time Machine
// exclusion (EW-18; `trust_build_tree.rs`).

use super::*;

#[cfg(target_os = "macos")]
mod macos {
    use std::io::Write as _;
    use std::path::{Path, PathBuf};
    use std::process::Command;

    use super::*;

    /// Say that a test could not observe what it checks, where a run shows it: libtest
    /// captures `eprintln!` and prints it only for a failing test, so a skip written
    /// that way reads as the same green as a real observation.
    fn skipped(test: &str, why: std::fmt::Arguments<'_>) {
        let _ = writeln!(std::io::stderr(), "SKIPPED: {test}: {why}");
    }

    /// A fresh directory under `home/.bootstrap-tm-probe/`, named for this process.
    /// A run killed by a signal never removes its own, and the OS never cleans the
    /// home directory, so each run first removes those whose process is gone.
    fn probe_dir(home: &Path) -> std::io::Result<tempfile::TempDir> {
        let parent = home.join(".bootstrap-tm-probe");
        std::fs::create_dir_all(&parent)?;
        for entry in std::fs::read_dir(&parent)?.flatten() {
            let name = entry.file_name();
            let pid = name.to_str().and_then(|n| n.split('-').next()?.parse::<i32>().ok());
            let Some(pid) = pid else { continue };
            // SAFETY: signal 0 only asks whether the process exists.
            let gone = unsafe { libc::kill(pid, 0) } != 0
                && std::io::Error::last_os_error().raw_os_error() == Some(libc::ESRCH);
            if gone {
                let _ = std::fs::remove_dir_all(entry.path());
            }
        }
        tempfile::Builder::new().prefix(&format!("{}-", std::process::id())).tempdir_in(&parent)
    }

    fn read_exclusion(dir: &Path) -> Option<Vec<u8>> {
        let out = Command::new("/usr/bin/xattr")
            .args(["-px", BACKUP_EXCLUDE_XATTR])
            .arg(dir)
            .output()
            .expect("xattr runs");
        if !out.status.success() {
            return None;
        }
        let hex: String = String::from_utf8(out.stdout).unwrap().split_whitespace().collect();
        Some(
            (0..hex.len())
                .step_by(2)
                .map(|i| u8::from_str_radix(&hex[i..i + 2], 16).unwrap())
                .collect(),
        )
    }

    fn time_machine_says(dir: &Path) -> String {
        let out = Command::new("/usr/bin/tmutil").arg("isexcluded").arg(dir).output().unwrap();
        assert!(out.status.success(), "tmutil isexcluded failed: {out:?}");
        String::from_utf8_lossy(&out.stdout).into_owned()
    }

    /// The bytes bootstrap writes are the ones `tmutil addexclusion` writes, so Time
    /// Machine reads them the same way. The sticky exclusion needs no privilege, so a
    /// `tmutil` that is present and fails is a failure, not a skip.
    #[test]
    fn the_value_is_what_tmutil_writes() {
        if !Path::new("/usr/bin/tmutil").exists() {
            skipped(
                "the_value_is_what_tmutil_writes",
                format_args!("no /usr/bin/tmutil; the plist's structure is checked below"),
            );
            return;
        }
        let temp = tempfile::tempdir().unwrap();
        let by_tmutil = temp.path().join("by-tmutil");
        std::fs::create_dir(&by_tmutil).unwrap();
        let out = Command::new("/usr/bin/tmutil").arg("addexclusion").arg(&by_tmutil).output();
        assert!(matches!(&out, Ok(o) if o.status.success()), "tmutil addexclusion: {out:?}");
        assert_eq!(read_exclusion(&by_tmutil).as_deref(), Some(BACKUP_EXCLUDE_VALUE));
    }

    /// Time Machine itself reads the mark, for the directory and what is under it. The
    /// system's temporary directories are excluded already, so this needs a directory
    /// Time Machine would back up: a fresh one in the home directory. Where there is none
    /// (no `$HOME`, one it cannot write, or one outside backups), the verdict cannot be
    /// observed, and it says so in the run's output (`SKIPPED:`).
    #[test]
    fn time_machine_reads_the_mark_on_a_directory_it_would_back_up() {
        const TEST: &str = "time_machine_reads_the_mark_on_a_directory_it_would_back_up";
        let Some(home) = std::env::var_os("HOME").map(PathBuf::from) else {
            skipped(TEST, format_args!("no $HOME; Time Machine's verdict is not observable"));
            return;
        };
        let temp = match probe_dir(&home) {
            Ok(temp) => temp,
            Err(error) => {
                skipped(
                    TEST,
                    format_args!(
                        "cannot write in {} ({error}); Time Machine's verdict is not observable",
                        home.display()
                    ),
                );
                return;
            }
        };
        let build = temp.path().join("build");
        std::fs::create_dir_all(build.join("aarch64-apple-darwin/llvm")).unwrap();
        let included = time_machine_says(&build).contains("[Included]");
        if included {
            assert_eq!(exclude_from_backups(&build).unwrap(), BackupExclusion::Excluded);
            for dir in [build.clone(), build.join("aarch64-apple-darwin/llvm")] {
                let said = time_machine_says(&dir);
                assert!(said.contains("[Excluded]"), "tmutil isexcluded said: {said}");
            }
        }
        drop(temp);
        let _ = std::fs::remove_dir(home.join(".bootstrap-tm-probe"));
        if !included {
            skipped(
                TEST,
                format_args!(
                    "{} is excluded already; Time Machine's verdict is not observable",
                    home.display()
                ),
            );
        }
    }

    /// A probe directory that a killed run left is removed by the next run; one whose
    /// process is alive, or that is not a probe directory, is left alone.
    #[test]
    fn a_probe_left_by_a_killed_run_is_removed_by_the_next() {
        let home = tempfile::tempdir().unwrap();
        let parent = home.path().join(".bootstrap-tm-probe");
        let mut child = Command::new("/usr/bin/true").spawn().unwrap();
        let dead = child.id();
        child.wait().unwrap();
        let left = parent.join(format!("{dead}-x1y2z3/build/aarch64-apple-darwin/llvm"));
        let alive = parent.join(format!("{}-other", std::process::id()));
        let foreign = parent.join("not-a-probe");
        for dir in [&left, &alive, &foreign] {
            std::fs::create_dir_all(dir).unwrap();
        }
        let probe = probe_dir(home.path()).unwrap();
        assert!(!parent.join(format!("{dead}-x1y2z3")).exists(), "the dead run's probe is gone");
        assert!(alive.exists() && foreign.exists());
        assert!(probe.path().starts_with(&parent));
    }

    /// On exFAT the attribute would be written as an AppleDouble `._build` file beside
    /// the directory, which `git status` shows; Time Machine does not back such a volume
    /// up, so nothing is written there.
    #[test]
    fn nothing_is_written_on_a_volume_time_machine_does_not_back_up() {
        const TEST: &str = "nothing_is_written_on_a_volume_time_machine_does_not_back_up";
        let temp = tempfile::tempdir().unwrap();
        let image = temp.path().join("exfat.dmg");
        let mount = temp.path().join("mnt");
        std::fs::create_dir(&mount).unwrap();
        let made = Command::new("/usr/bin/hdiutil")
            .args(["create", "-quiet", "-size", "8m", "-fs", "ExFAT", "-volname", "tmprobe"])
            .arg(&image)
            .status();
        if !matches!(made, Ok(status) if status.success()) {
            skipped(TEST, format_args!("hdiutil cannot make an exFAT image ({made:?})"));
            return;
        }
        let attached = Command::new("/usr/bin/hdiutil")
            .args(["attach", "-quiet", "-nobrowse", "-noverify", "-mountpoint"])
            .arg(&mount)
            .arg(&image)
            .status();
        if !matches!(attached, Ok(status) if status.success()) {
            skipped(TEST, format_args!("hdiutil cannot attach the image ({attached:?})"));
            return;
        }
        struct Detach<'a>(&'a Path);
        impl Drop for Detach<'_> {
            fn drop(&mut self) {
                let detach = |force: bool| {
                    let mut command = Command::new("/usr/bin/hdiutil");
                    command.args(["detach", "-quiet"]).arg(self.0);
                    if force {
                        command.arg("-force");
                    }
                    command.status().is_ok_and(|status| status.success())
                };
                if !detach(false) {
                    detach(true);
                }
            }
        }
        let _detach = Detach(&mount);
        let build = mount.join("build");
        std::fs::create_dir(&build).unwrap();
        // macOS can create a provenance AppleDouble file during mkdir itself.
        // Attribute only changes after the call to the exclusion helper.
        let sidecar_bytes = || match std::fs::read(mount.join("._build")) {
            Ok(bytes) => Some(bytes),
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => None,
            Err(error) => panic!("cannot inspect AppleDouble file: {error}"),
        };
        let before = sidecar_bytes();
        assert_eq!(read_exclusion(&build), None);
        assert_eq!(exclude_from_backups(&build).unwrap(), BackupExclusion::NotOnABackedUpVolume);
        assert_eq!(sidecar_bytes(), before, "exclusion must not create or change AppleDouble data");
        assert_eq!(read_exclusion(&build), None);
    }

    #[test]
    fn a_new_build_dir_is_excluded_once_and_then_found_excluded() {
        let temp = tempfile::tempdir().unwrap();
        let build = temp.path().join("build");
        std::fs::create_dir_all(build.join("aarch64-apple-darwin/llvm")).unwrap();
        assert_eq!(read_exclusion(&build), None);
        assert_eq!(exclude_from_backups(&build).unwrap(), BackupExclusion::Excluded);
        assert_eq!(read_exclusion(&build).as_deref(), Some(BACKUP_EXCLUDE_VALUE));
        assert_eq!(exclude_from_backups(&build).unwrap(), BackupExclusion::AlreadyExcluded);
    }

    /// A different value under the same name, longer than the read buffer or not, is
    /// replaced by the one Time Machine reads.
    #[test]
    fn a_foreign_value_is_replaced() {
        for foreign in ["not a plist".to_string(), "x".repeat(300)] {
            let temp = tempfile::tempdir().unwrap();
            let status = Command::new("/usr/bin/xattr")
                .args(["-w", BACKUP_EXCLUDE_XATTR, &foreign])
                .arg(temp.path())
                .status()
                .unwrap();
            assert!(status.success());
            assert_eq!(exclude_from_backups(temp.path()).unwrap(), BackupExclusion::Excluded);
            assert_eq!(read_exclusion(temp.path()).as_deref(), Some(BACKUP_EXCLUDE_VALUE));
        }
    }

    /// Under the Spotlight layout the mark lands on the real `build.noindex`.
    #[test]
    fn the_spotlight_link_marks_the_real_directory() {
        let temp = tempfile::tempdir().unwrap();
        let physical = temp.path().join("build.noindex");
        std::fs::create_dir(&physical).unwrap();
        let build = temp.path().join("build");
        std::os::unix::fs::symlink("build.noindex", &build).unwrap();

        assert_eq!(exclude_from_backups(&build).unwrap(), BackupExclusion::Excluded);
        assert_eq!(read_exclusion(&physical).as_deref(), Some(BACKUP_EXCLUDE_VALUE));
        assert_eq!(exclude_from_backups(&physical).unwrap(), BackupExclusion::AlreadyExcluded);
    }

    #[test]
    fn a_missing_directory_is_an_error_not_a_mark() {
        let temp = tempfile::tempdir().unwrap();
        assert!(exclude_from_backups(&temp.path().join("absent")).is_err());
        let file = temp.path().join("file");
        std::fs::write(&file, b"").unwrap();
        assert!(exclude_from_backups(&file).is_err());
        assert_eq!(read_exclusion(&file), None);
    }
}

/// The value is a well-formed binary property list whose one object is the string
/// `com.apple.backupd`, read field by field, so a change to it is caught where `tmutil`
/// cannot run.
#[test]
fn the_value_is_the_backupd_plist() {
    let v = BACKUP_EXCLUDE_VALUE;
    let be = |bytes: &[u8]| bytes.iter().fold(0u64, |n, b| (n << 8) | u64::from(*b));
    assert_eq!(&v[..8], b"bplist00", "header");
    // Trailer: 6 unused bytes, offset-int size, object-ref size, object count, top
    // object, offset-table offset (the last three big-endian u64).
    let trailer = &v[v.len() - 32..];
    assert_eq!(&trailer[..6], &[0; 6]);
    assert_eq!((trailer[6], trailer[7]), (1, 1), "one-byte offsets and object refs");
    assert_eq!(be(&trailer[8..16]), 1, "one object");
    assert_eq!(be(&trailer[16..24]), 0, "the top object is object 0");
    let table = be(&trailer[24..32]) as usize;
    let object = v[table] as usize;
    // Object 0: an ASCII string (0x5_) whose length follows as a one-byte int (0x10).
    assert_eq!(&v[object..object + 3], &[0x5f, 0x10, 17]);
    assert_eq!(&v[object + 3..object + 20], b"com.apple.backupd");
    assert_eq!(object + 20, table, "the offset table follows the only object");
    assert_eq!(table + 1 + 32, v.len(), "nothing after the trailer");
}

/// Time Machine backs up APFS and HFS+ volumes only, and those keep the attribute in
/// the directory; every other type is left unmarked.
#[test]
fn only_apfs_and_hfs_volumes_are_marked() {
    for (kind, marked) in [
        (&b"apfs"[..], true),
        (b"hfs", true),
        (b"exfat", false),
        (b"msdos", false),
        (b"smbfs", false),
        (b"nfs", false),
        (b"", false),
    ] {
        assert_eq!(time_machine_backs_up(kind), marked, "{}", String::from_utf8_lossy(kind));
    }
}

/// Off macOS there is no Time Machine: the call writes nothing and fails nothing.
#[cfg(not(target_os = "macos"))]
#[test]
fn nothing_is_done_off_macos() {
    let temp = tempfile::tempdir().unwrap();
    exclude_build_dir_from_backups(temp.path());
    exclude_build_dir_from_backups(&temp.path().join("absent"));
    assert_eq!(std::fs::read_dir(temp.path()).unwrap().count(), 0);
}
