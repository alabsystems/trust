//! Exact extern inputs selected by the actual runtime-finalized Cargo argv.
//! Held input descriptions/bytes confer no build or proof authority.
use super::*;
use std::fs::{File, Metadata, OpenOptions};

const MAX_FILES: usize = 256;
const MAX_BYTES: u64 = 16 * 1024 * 1024 * 1024;

#[derive(Debug)]
pub(super) struct Inputs {
    files: Vec<Input>,
}
#[derive(Debug)]
struct Input {
    path: PathBuf,
    resolved: PathBuf,
    file: File,
    metadata: Metadata,
    sha256: [u8; 32],
}
impl Inputs {
    pub(super) fn data(&self) -> Vec<serde_json::Value> {
        self.files.iter().map(|input|serde_json::json!({"path_hex":hex::encode(input.path.as_os_str().as_encoded_bytes()),"resolved_path_hex":hex::encode(input.resolved.as_os_str().as_encoded_bytes()),"bytes":input.metadata.len(),"sha256":hex::encode(input.sha256)})).collect()
    }
    pub(super) fn capture(command: &ProcessBuilder, deadline: Instant) -> CargoResult<Self> {
        let cwd = command
            .get_cwd()
            .context("original dependency command has no cwd")?;
        let args = command.get_args().collect::<Vec<_>>();
        let mut selected = std::collections::BTreeSet::new();
        let mut at = 0;
        while let Some(arg) = args.get(at) {
            let value = if arg.as_encoded_bytes() == b"--extern" {
                at += 1;
                Some(
                    args.get(at)
                        .context("missing actual extern value")?
                        .as_os_str(),
                )
            } else {
                arg.as_encoded_bytes()
                    .strip_prefix(b"--extern=")
                    .map(|value| {
                        // SAFETY: value is a suffix of an actual OsStr, split at ASCII.
                        unsafe { OsStr::from_encoded_bytes_unchecked(value) }
                    })
            };
            if let Some(value) = value {
                let bytes = value.as_encoded_bytes();
                let split = bytes
                    .iter()
                    .position(|b| *b == b'=')
                    .context("native verification refuses an unbound sysroot/implicit extern")?;
                let bytes = &bytes[split + 1..];
                ensure!(
                    !bytes.is_empty() && !bytes.starts_with(b"@"),
                    "invalid native extern input"
                );
                // SAFETY: actual OsStr split only at ASCII '='.
                let path = Path::new(unsafe { OsStr::from_encoded_bytes_unchecked(bytes) });
                selected.insert(if path.is_absolute() {
                    path.to_owned()
                } else {
                    cwd.join(path)
                });
            }
            at += 1;
        }
        ensure!(
            selected.len() <= MAX_FILES,
            "complete native extern population exceeds retained bound"
        );
        let mut bytes = 0u64;
        let mut files = Vec::new();
        for path in selected {
            ensure!(
                Instant::now() < deadline,
                "original extern capture deadline exceeded"
            );
            let mut options = OpenOptions::new();
            options.read(true);
            #[cfg(unix)]
            {
                use std::os::unix::fs::OpenOptionsExt as _;
                options.custom_flags(libc::O_CLOEXEC | libc::O_NOFOLLOW | libc::O_NONBLOCK);
            }
            let file = options.open(&path)?;
            let metadata = file.metadata()?;
            ensure!(metadata.is_file(), "native extern is not a regular input");
            bytes = bytes
                .checked_add(metadata.len())
                .context("extern byte count overflow")?;
            ensure!(
                bytes <= MAX_BYTES,
                "complete native extern bytes exceed retained bound"
            );
            let sha256 = hash(&file, metadata.len(), deadline)?;
            let input = Input {
                resolved: path.canonicalize()?,
                path,
                file,
                metadata,
                sha256,
            };
            input.validate(deadline)?;
            files.push(input);
        }
        Ok(Self { files })
    }
    pub(super) fn validate(&self, deadline: Instant) -> CargoResult<()> {
        for input in &self.files {
            input.validate(deadline)?;
        }
        Ok(())
    }
}
fn hash(file: &File, expected: u64, deadline: Instant) -> CargoResult<[u8; 32]> {
    let mut hash = cargo_util::Sha256::new();
    let mut count = 0u64;
    let mut bytes = [0u8; 65536];
    loop {
        ensure!(
            Instant::now() < deadline,
            "original extern hashing deadline exceeded"
        );
        #[cfg(unix)]
        let read = {
            use std::os::unix::fs::FileExt as _;
            file.read_at(&mut bytes, count)?
        };
        #[cfg(not(unix))]
        let read: usize = {
            let _ = file;
            anyhow::bail!("native held extern byte reads unavailable")
        };
        if read == 0 {
            break;
        }
        count = count
            .checked_add(read as u64)
            .context("extern byte count overflow")?;
        ensure!(count <= expected, "original extern grew while binding");
        hash.update(&bytes[..read]);
    }
    ensure!(
        count == expected,
        "original extern length changed while binding"
    );
    Ok(hash.finish())
}
fn same(a: &Metadata, b: &Metadata) -> bool {
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt as _;
        (
            a.dev(),
            a.ino(),
            a.len(),
            a.mode(),
            a.nlink(),
            a.mtime(),
            a.mtime_nsec(),
            a.ctime(),
            a.ctime_nsec(),
        ) == (
            b.dev(),
            b.ino(),
            b.len(),
            b.mode(),
            b.nlink(),
            b.mtime(),
            b.mtime_nsec(),
            b.ctime(),
            b.ctime_nsec(),
        )
    }
    #[cfg(not(unix))]
    {
        let _ = (a, b);
        false
    }
}
impl Input {
    fn validate(&self, deadline: Instant) -> CargoResult<()> {
        ensure!(
            Instant::now() < deadline,
            "original extern validation deadline exceeded"
        );
        let named = std::fs::symlink_metadata(&self.path)?;
        ensure!(
            named.is_file()
                && !named.file_type().is_symlink()
                && same(&self.metadata, &named)
                && same(&self.metadata, &self.file.metadata()?)
                && self.path.canonicalize()? == self.resolved,
            "original extern input was replaced or changed"
        );
        // Read through the SAME held description without moving its shared
        // OFD cursor. Parallel input rechecks cannot interfere with each other.
        ensure!(
            hash(&self.file, self.metadata.len(), deadline)? == self.sha256
                && same(&self.metadata, &self.file.metadata()?)
                && same(&self.metadata, &std::fs::symlink_metadata(&self.path)?),
            "original extern bytes changed after capture"
        );
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn repeated_actual_externs_bind_once_and_drift_or_alias_substitution_refuses() {
        let dir = tempfile::tempdir().unwrap();
        let root = dir.path().canonicalize().unwrap();
        let dep = root.join("actual dependency.rlib");
        std::fs::write(&dep, b"original").unwrap();
        let mut cmd = ProcessBuilder::new("not-executed");
        cmd.cwd(&root).args(&[
            OsStr::new("--extern"),
            OsStr::new("dep=actual dependency.rlib"),
            OsStr::new("--extern=alias=actual dependency.rlib"),
        ]);
        let until = Instant::now() + Duration::from_secs(10);
        let inputs = Inputs::capture(&cmd, until).unwrap();
        assert_eq!(inputs.files.len(), 1);
        inputs.validate(until).unwrap();
        std::fs::write(&dep, b"modified").unwrap();
        assert!(inputs.validate(until).is_err());
        std::fs::write(&dep, b"original").unwrap();
        assert!(
            inputs.validate(until).is_err(),
            "restoring bytes cannot restore original stamp"
        );
        let inputs = Inputs::capture(&cmd, until).unwrap();
        std::fs::rename(&dep, root.join("old")).unwrap();
        std::fs::write(&dep, b"original").unwrap();
        assert!(inputs.validate(until).is_err());
    }
    #[test]
    fn implicit_externs_and_response_substitution_never_become_empty_dependencies() {
        let root = tempfile::tempdir().unwrap();
        for arg in ["--extern=unbound", "--extern=dep=@args"] {
            let mut cmd = ProcessBuilder::new("never-run");
            cmd.cwd(root.path()).arg(arg);
            assert!(Inputs::capture(&cmd, Instant::now() + Duration::from_secs(1)).is_err());
        }
    }
}
