//! Existing persistent adoption debt, observed only under the actual lease lock.

use super::*;

#[derive(Deserialize)]
struct Record {
    schema: u32,
    adopted: bool,
    pid: u32,
    identity: Identity,
    pool: PathBuf,
    worktree: Option<PathBuf>,
    leases: Vec<PathBuf>,
    #[serde(default)]
    exclusive: bool,
}
#[derive(Deserialize)]
struct Identity {
    pid: u32,
    uid: u32,
    birth: String,
    executable: PathBuf,
}

impl Record {
    fn validate(&self) -> io::Result<()> {
        if self.schema != 1
            || !self.adopted
            || self.pid == 0
            || self.pid != self.identity.pid
            || !valid_birth(&self.identity.birth)
            || self.identity.executable.as_os_str().is_empty()
            || self.leases.is_empty()
            || self.leases.len() > MAX_TICKETS
        {
            return Err(invalid("invalid adopted build reservation"));
        }
        // UID and executable are stored diagnostics. Neither a later exec nor
        // a UID transition makes a matching PID+birth free.
        let _reported_uid = self.identity.uid;
        // Exclusivity is diagnostic for availability; the actual lease paths
        // still determine debt. Native repeat checks validate complete coverage.
        let _reported_exclusive = self.exclusive;
        validate_path(&self.pool)?;
        for path in &self.leases {
            validate_path(path)?;
            if canonical_location(path)? != *path {
                return Err(invalid("adopted lease path is not canonical"));
            }
        }
        if self.worktree.as_ref().is_some_and(|path| !self.leases.contains(path)) {
            return Err(invalid("adopted worktree is missing from its complete claim"));
        }
        Ok(())
    }
}

/// Old worktrees can disappear after a process exits. Resolve the longest
/// existing ancestor and preserve the missing suffix, matching the original
/// registry's canonical-location semantics. Permission errors or aliases still
/// refuse; missing files alone do not make a known dead birth unknowable.
pub(super) fn canonical_location(path: &Path) -> io::Result<PathBuf> {
    let mut at = path;
    let mut missing = Vec::new();
    loop {
        match fs::canonicalize(at) {
            Ok(mut canonical) => {
                for leaf in missing.into_iter().rev() {
                    canonical.push(leaf);
                }
                return Ok(canonical);
            }
            Err(error) if error.kind() == io::ErrorKind::NotFound => {
                missing.push(
                    at.file_name()
                        .ok_or_else(|| invalid("adopted path has no existing ancestor"))?
                        .to_os_string(),
                );
                at = at.parent().ok_or_else(|| invalid("adopted path has no existing ancestor"))?;
            }
            Err(error) => return Err(error),
        }
    }
}

fn valid_birth(birth: &str) -> bool {
    fn number(value: &str) -> Option<u64> {
        let parsed = value.parse::<u64>().ok()?;
        (parsed.to_string() == value).then_some(parsed)
    }
    #[cfg(target_os = "macos")]
    {
        let Some(rest) = birth.strip_prefix("darwin:") else { return false };
        let Some((seconds, micros)) = rest.split_once(':') else { return false };
        number(seconds).is_some_and(|seconds| seconds > 0)
            && number(micros).is_some_and(|micros| micros < 1_000_000)
    }
    #[cfg(target_os = "linux")]
    {
        let Some(rest) = birth.strip_prefix("linux:") else { return false };
        let Some((boot, ticks)) = rest.split_once(':') else { return false };
        boot.len() == 36
            && boot.bytes().enumerate().all(|(index, byte)| {
                if [8, 13, 18, 23].contains(&index) {
                    byte == b'-'
                } else {
                    byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte)
                }
            })
            && number(ticks).is_some_and(|ticks| ticks > 0)
    }
}

#[cfg(feature = "machine-admission")]
pub(super) struct ValidRecord {
    pub(super) pid: u32,
    pub(super) birth: String,
    pub(super) pool: PathBuf,
    pub(super) worktree: Option<PathBuf>,
    pub(super) leases: Vec<PathBuf>,
    pub(super) exclusive: bool,
}

#[cfg(feature = "machine-admission")]
pub(super) fn read_valid_record(bytes: &[u8]) -> io::Result<ValidRecord> {
    let record: Record = serde_json::from_slice(bytes).map_err(io::Error::other)?;
    record.validate()?;
    Ok(ValidRecord {
        pid: record.pid,
        birth: record.identity.birth,
        pool: record.pool,
        worktree: record.worktree,
        leases: record.leases,
        exclusive: record.exclusive,
    })
}

/// Diagnostic inspection only. Even a known dead/reused birth retains its
/// original registry entry; this path never calls availability or retirement.
#[cfg(feature = "machine-admission")]
pub(super) fn observe_for_status(bytes: &[u8]) -> io::Result<super::status::AdoptedRecord> {
    use super::status::{AdoptedProcess, AdoptedRecord, Observation};
    let record: Record = serde_json::from_slice(bytes).map_err(io::Error::other)?;
    record.validate()?;
    let process = match crate::trust_repo_lock::management::process::live_adoption_birth(record.pid)
    {
        Ok(Some(birth)) if birth == record.identity.birth => {
            Observation::Observed { value: AdoptedProcess::SameBirth }
        }
        Ok(_) => Observation::Observed { value: AdoptedProcess::GoneOrReused },
        Err(error) => Observation::Unavailable {
            message: error.to_string(),
            raw_os_error: error.raw_os_error(),
        },
    };
    Ok(AdoptedRecord {
        reported_pid: record.pid,
        reported_birth: record.identity.birth,
        lease_paths_bytes: record
            .leases
            .iter()
            .map(|path| path.as_os_str().as_bytes().to_vec())
            .collect(),
        process,
    })
}

/// The caller retains the actual flock for `lease_path` through observation
/// and acquisition. This is not a cached snapshot: a publisher must own every
/// same lease lock before publishing its complete record. Unknown records or
/// process observations preserve exclusion. No process is signalled.
pub(super) fn available(registry_path: &Path, lease_path: &Path) -> io::Result<bool> {
    available_with(registry_path, lease_path, |pid| {
        crate::trust_repo_lock::management::process::live_adoption_birth(pid)
    })
}

fn available_with(
    registry_path: &Path,
    lease_path: &Path,
    mut observe_birth: impl FnMut(u32) -> io::Result<Option<String>>,
) -> io::Result<bool> {
    let directory = match Directory::open(registry_path) {
        Ok(directory) => directory,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(true),
        Err(error) => return Err(error),
    };
    // Old adoption takes registration before queue/path locks. Ordinary
    // admission must never block on this reverse edge: busy releases the
    // caller's partial claim and retries as a whole.
    let registration = directory.open_file("registration.lock", true)?;
    if !try_exclusive(&registration)? {
        return Ok(false);
    }
    for name in directory.entries()? {
        if !name.as_bytes().ends_with(b".json") {
            continue;
        }
        let Some(name) = name.to_str() else { return Ok(false) };
        let file = match directory.open_file(name, false) {
            Ok(file) => file,
            Err(error) if error.kind() == io::ErrorKind::NotFound => continue,
            Err(error) => return Err(error),
        };
        let bytes = read_record(&file)?;
        let record = match serde_json::from_slice::<Record>(&bytes) {
            Ok(record) if record.validate().is_ok() => record,
            _ => return Ok(false),
        };
        if !record.leases.iter().any(|path| path == lease_path) {
            continue;
        }
        match observe_birth(record.pid) {
            Err(_) => return Ok(false),
            Ok(Some(birth)) if birth == record.identity.birth => return Ok(false),
            Ok(_) => {
                // The original publication is now dead or its PID was reused.
                // Never unlink a replacement or changed original record.
                if read_record(&file)? != bytes {
                    return Err(invalid("adopted record changed during retirement"));
                }
                match directory.remove(name, &file) {
                    Ok(()) => {}
                    Err(error) if error.kind() == io::ErrorKind::NotFound => {}
                    Err(error) => return Err(error),
                }
            }
        }
    }
    directory.check()?;
    Ok(true)
}

#[cfg(test)]
mod tests;
