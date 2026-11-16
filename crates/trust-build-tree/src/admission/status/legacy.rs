use super::*;

const TOTAL_RECORD_BYTES: usize = 16 * 1024 * 1024;
struct Budget(usize);

fn open_readonly(directory: &Directory, name: &std::ffi::OsStr) -> io::Result<File> {
    if name.as_bytes().is_empty() || name.as_bytes().contains(&b'/') {
        return Err(invalid("status requires a single original directory entry"));
    }
    directory.check()?;
    let name_c = std::ffi::CString::new(name.as_bytes()).map_err(io::Error::other)?;
    let raw = unsafe {
        libc::openat(
            directory.file.as_raw_fd(),
            name_c.as_ptr(),
            libc::O_RDONLY | libc::O_NOFOLLOW | libc::O_NONBLOCK | libc::O_CLOEXEC,
        )
    };
    if raw < 0 {
        return Err(io::Error::last_os_error());
    }
    // SAFETY: successful openat returned this newly owned read-only FD.
    let file = unsafe { File::from_raw_fd(raw) };
    directory.check_file(name, &file)?;
    Ok(file)
}

fn shared_probe(file: &File) -> io::Result<LockState> {
    match file.try_lock_shared() {
        Ok(()) => Ok(LockState::SharedCompatible),
        Err(fs::TryLockError::WouldBlock) => Ok(LockState::ExclusiveHeld),
        Err(fs::TryLockError::Error(error)) => Err(error),
    }
}

fn stable_bytes(
    directory: &Directory,
    name: &std::ffi::OsStr,
    file: &File,
    budget: &mut Budget,
) -> io::Result<Vec<u8>> {
    directory.check_file(name, file)?;
    if budget.0 < MAX_RECORD as usize {
        return Err(invalid("status aggregate record observation bound reached"));
    }
    let bytes = read_record(file)?;
    budget.0 -= bytes.len();
    if read_record(file)? != bytes {
        return Err(invalid("status record changed during observation"));
    }
    directory.check_file(name, file)?;
    Ok(bytes)
}

fn reported(bytes: &[u8]) -> io::Result<ReportedOwner> {
    let value: serde_json::Value = serde_json::from_slice(bytes).map_err(io::Error::other)?;
    let object =
        value.as_object().ok_or_else(|| invalid("status owner record is not an object"))?;
    let text = |name: &str| -> io::Result<Option<String>> {
        match object.get(name) {
            None | Some(serde_json::Value::Null) => Ok(None),
            Some(serde_json::Value::String(value)) if value.len() <= 8192 => {
                Ok(Some(value.clone()))
            }
            _ => Err(invalid("status owner text is invalid or exceeds its bound")),
        }
    };
    let number = |name: &str| -> io::Result<Option<u32>> {
        object
            .get(name)
            .filter(|value| !value.is_null())
            .map(|value| {
                value
                    .as_u64()
                    .and_then(|number| u32::try_from(number).ok())
                    .filter(|number| *number != 0)
                    .ok_or_else(|| invalid("status owner number is invalid"))
            })
            .transpose()
    };
    let exclusive = object
        .get("exclusive")
        .filter(|value| !value.is_null())
        .map(|value| value.as_bool().ok_or_else(|| invalid("status exclusive label is invalid")))
        .transpose()?;
    Ok(ReportedOwner {
        pid: number("pid")?,
        cpu_mode: text("cpu_mode")?,
        cpu_budget: number("cpu_budget")?,
        exclusive,
        command: text("cmd")?,
        cwd: text("cwd")?,
    })
}

fn lease(directory: &Directory, name: &std::ffi::OsStr, budget: &mut Budget) -> LeaseObservation {
    let mut row = LeaseObservation {
        name_bytes: name.as_bytes().to_vec(),
        lock: Observation::Absent,
        reported: Observation::Absent,
    };
    match open_readonly(directory, name) {
        Err(error) if error.kind() == io::ErrorKind::NotFound => {}
        Err(error) => row.lock = Observation::error(error),
        Ok(file) => match shared_probe(&file) {
            Err(error) => row.lock = Observation::error(error),
            Ok(state) => {
                // A stale record is deliberately not promoted to a live owner.
                if state == LockState::ExclusiveHeld {
                    row.reported = Observation::result(
                        stable_bytes(directory, name, &file, budget)
                            .and_then(|bytes| reported(&bytes)),
                    );
                }
                row.lock = Observation::result(directory.check_file(name, &file).map(|()| state));
            }
        },
    }
    row
}

pub(super) fn snapshot(namespace: &Path, minimum: Option<u32>) -> Observation<LegacyStatus> {
    let directory = match Directory::open(namespace) {
        Ok(directory) => directory,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Observation::Absent,
        Err(error) => return Observation::error(error),
    };
    Observation::result((|| {
        let mut names = std::collections::BTreeSet::new();
        for index in 0..minimum.unwrap_or(0) {
            names.insert(std::ffi::OsString::from(format!("slot-{index}")));
        }
        for name in directory.entries()? {
            if name
                .as_bytes()
                .strip_prefix(b"slot-")
                .is_some_and(|suffix| !suffix.is_empty() && suffix.iter().all(u8::is_ascii_digit))
            {
                names.insert(name);
                if names.len() > MAX_TICKETS {
                    return Err(invalid("status slot population exceeds its bound"));
                }
            }
        }
        let mut budget = Budget(TOTAL_RECORD_BYTES);
        let slots = names.iter().map(|name| lease(&directory, name, &mut budget)).collect();
        let admission = lease(&directory, std::ffi::OsStr::new("admission.lock"), &mut budget);
        let queue = queue(&namespace.join("admission"), &mut budget);
        let adopted = adopted(&namespace.join("adopted"), &mut budget);
        directory.check()?;
        Ok(LegacyStatus { slots, admission, queue, adopted })
    })())
}

/// A shared registry probe excludes cooperating queue publication/retirement.
/// It never registers a ticket or removes an unlocked stale entry.
fn queue(path: &Path, budget: &mut Budget) -> Observation<QueueStatus> {
    guarded_directory(path, "registry.lock", |directory| {
        let mut tickets = Vec::new();
        for name in directory.entries()? {
            let Some(tail) = name.as_bytes().strip_prefix(b"wait-") else { continue };
            if tail.is_empty() || !tail.iter().all(u8::is_ascii_digit) {
                continue;
            }
            let order = std::str::from_utf8(tail)
                .ok()
                .and_then(|text| text.parse().ok())
                .ok_or_else(|| invalid("status admission order exceeds its bound"))?;
            let (lock, requirements) = match open_readonly(directory, &name) {
                Err(error) => (Observation::error(error), Observation::Absent),
                Ok(file) => match shared_probe(&file) {
                    Err(error) => (Observation::error(error), Observation::Absent),
                    Ok(state) => {
                        let requirements = if state == LockState::ExclusiveHeld {
                            Observation::result(
                                stable_bytes(directory, &name, &file, budget)
                                    .and_then(|bytes| requirements_from_bytes(&bytes))
                                    .map(Into::into),
                            )
                        } else {
                            Observation::Absent
                        };
                        (
                            Observation::result(directory.check_file(&name, &file).map(|()| state)),
                            requirements,
                        )
                    }
                },
            };
            tickets.push(TicketObservation {
                name_bytes: name.as_bytes().to_vec(),
                order,
                lock,
                requirements,
            });
        }
        tickets.sort_by(|left, right| {
            (left.order, &left.name_bytes).cmp(&(right.order, &right.name_bytes))
        });
        directory.check()?;
        Ok(QueueStatus { tickets })
    })
}

fn adopted(path: &Path, budget: &mut Budget) -> Observation<Vec<AdoptionObservation>> {
    guarded_directory(path, "registration.lock", |directory| {
        let mut records = Vec::new();
        let mut names = directory.entries()?;
        names.sort();
        for name in names {
            if !name.as_bytes().ends_with(b".json") {
                continue;
            }
            let record = (|| {
                let file = open_readonly(directory, &name)?;
                let bytes = stable_bytes(directory, &name, &file, budget)?;
                let record = super::super::adopted::observe_for_status(&bytes)?;
                directory.check_file(&name, &file)?;
                Ok(record)
            })();
            records.push(AdoptionObservation {
                name_bytes: name.as_bytes().to_vec(),
                record: Observation::result(record),
            });
        }
        directory.check()?;
        Ok(records)
    })
}

fn guarded_directory<T>(
    path: &Path,
    registry: &str,
    observe: impl FnOnce(&Directory) -> io::Result<T>,
) -> Observation<T> {
    let directory = match Directory::open(path) {
        Ok(directory) => directory,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Observation::Absent,
        Err(error) => return Observation::error(error),
    };
    // An existing directory without its registry is incomplete, not an empty
    // population. O_RDONLY never initializes or repairs its protocol.
    let registry = std::ffi::OsStr::new(registry);
    let file = match open_readonly(&directory, registry) {
        Ok(file) => file,
        Err(error) => return Observation::error(error),
    };
    match shared_probe(&file) {
        Ok(LockState::ExclusiveHeld) => Observation::Busy,
        Err(error) => Observation::error(error),
        Ok(LockState::SharedCompatible) => Observation::result((|| {
            let result = observe(&directory)?;
            directory.check_file(registry, &file)?;
            Ok(result)
        })()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn readonly_probe_preserves_original_flags_cursor_and_detects_replaced_entry() {
        use std::io::{Seek, SeekFrom};
        let root = crate::owner_only::tempdir();
        let path = root.path().join("slot-0");
        crate::launcher_file::write(&path, b"original owner");
        let mut original = OpenOptions::new().read(true).write(true).open(&path).unwrap();
        original.try_lock().unwrap();
        original.seek(SeekFrom::Start(4)).unwrap();
        let flags = unsafe { libc::fcntl(original.as_raw_fd(), libc::F_GETFL) };
        let directory = Directory::open(root.path()).unwrap();
        let file = open_readonly(&directory, std::ffi::OsStr::new("slot-0")).unwrap();
        assert_eq!(
            unsafe { libc::fcntl(file.as_raw_fd(), libc::F_GETFL) } & libc::O_ACCMODE,
            libc::O_RDONLY
        );
        assert_ne!(unsafe { libc::fcntl(file.as_raw_fd(), libc::F_GETFD) } & libc::FD_CLOEXEC, 0);
        assert_eq!(shared_probe(&file).unwrap(), LockState::ExclusiveHeld);
        assert_eq!(
            stable_bytes(
                &directory,
                std::ffi::OsStr::new("slot-0"),
                &file,
                &mut Budget(TOTAL_RECORD_BYTES)
            )
            .unwrap(),
            b"original owner"
        );
        assert_eq!(original.stream_position().unwrap(), 4);
        assert_eq!(unsafe { libc::fcntl(original.as_raw_fd(), libc::F_GETFL) }, flags);
        fs::rename(&path, root.path().join("original")).unwrap();
        crate::owner_only::write(&path, b"replacement");
        assert!(
            stable_bytes(
                &directory,
                std::ffi::OsStr::new("slot-0"),
                &file,
                &mut Budget(TOTAL_RECORD_BYTES)
            )
            .is_err()
        );
        assert_eq!(fs::read(&path).unwrap(), b"replacement");
    }
    #[test]
    fn exhausted_aggregate_budget_refuses_without_read_or_repair() {
        let root = crate::owner_only::tempdir();
        let path = root.path().join("slot-0");
        crate::launcher_file::write(&path, b"original");
        let directory = Directory::open(root.path()).unwrap();
        let file = open_readonly(&directory, std::ffi::OsStr::new("slot-0")).unwrap();
        assert!(
            stable_bytes(&directory, std::ffi::OsStr::new("slot-0"), &file, &mut Budget(0))
                .is_err()
        );
        assert_eq!(fs::read(&path).unwrap(), b"original");
    }
    #[test]
    fn fixture_tests_pass_under_a_group_writable_umask() {
        crate::owner_only::under_umask_002(
            "admission::status::legacy::tests::fixture_tests_pass_under_a_group_writable_umask",
            || {
                readonly_probe_preserves_original_flags_cursor_and_detects_replaced_entry();
                exhausted_aggregate_budget_refuses_without_read_or_repair();
            },
        );
    }
}
