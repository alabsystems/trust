//! The actual AY crate inputs and default-policy files observed before Cargo
//! configuration. This is input consistency, never source/proof authority.
use super::*;
use crate::compiler::action_inputs::SourceInputs;
use std::fs::{File, Metadata, OpenOptions};
use std::os::unix::{
    ffi::OsStringExt as _,
    fs::{MetadataExt as _, OpenOptionsExt as _},
};
use std::time::Instant;
use trust_resource_controller::{paired_qualification::AySubject, workload::InputFile};
mod defaults;

const MAX_FILE_BYTES: u64 = 4 * 1024 * 1024;
struct BoundFile {
    path: PathBuf,
    file: File,
    metadata: Metadata,
    sha256: [u8; 32],
    bytes: Vec<u8>,
}
fn same(a: &Metadata, b: &Metadata) -> bool {
    a.is_file() && b.is_file() && same_entry(a, b)
}
fn same_entry(a: &Metadata, b: &Metadata) -> bool {
    a.file_type() == b.file_type()
        && (
            a.dev(),
            a.ino(),
            a.len(),
            a.mode(),
            a.uid(),
            a.gid(),
            a.mtime(),
            a.mtime_nsec(),
            a.ctime(),
            a.ctime_nsec(),
        ) == (
            b.dev(),
            b.ino(),
            b.len(),
            b.mode(),
            b.uid(),
            b.gid(),
            b.mtime(),
            b.mtime_nsec(),
            b.ctime(),
            b.ctime_nsec(),
        )
}
fn hash(file: &File, limit: u64, deadline: Instant) -> CargoResult<([u8; 32], Vec<u8>)> {
    use std::os::unix::fs::FileExt as _;
    let mut sha = cargo_util::Sha256::new();
    let mut bytes = Vec::new();
    let mut buffer = [0; 64 * 1024];
    loop {
        ensure!(
            Instant::now() < deadline,
            "AY input binding exceeded original deadline"
        );
        let count = match file.read_at(&mut buffer, bytes.len() as u64) {
            Err(error) if error.kind() == std::io::ErrorKind::Interrupted => continue,
            result => result?,
        };
        if count == 0 {
            break;
        }
        ensure!(
            (bytes.len() as u64)
                .checked_add(count as u64)
                .is_some_and(|n| n <= limit),
            "AY input exceeded bounded original length"
        );
        sha.update(&buffer[..count]);
        bytes.extend_from_slice(&buffer[..count]);
    }
    ensure!(
        bytes.len() as u64 == limit,
        "AY input changed length during binding"
    );
    Ok((sha.finish(), bytes))
}
impl BoundFile {
    fn open(input: &InputFile, deadline: Instant) -> CargoResult<Self> {
        let path = PathBuf::from(std::ffi::OsString::from_vec(input.path.clone()));
        ensure!(
            path.canonicalize()? == path,
            "AY input path traverses a substituted alias"
        );
        let file = OpenOptions::new()
            .read(true)
            .custom_flags(libc::O_CLOEXEC | libc::O_NOFOLLOW | libc::O_NONBLOCK)
            .open(&path)?;
        let metadata = file.metadata()?;
        ensure!(
            metadata.is_file() && metadata.len() <= MAX_FILE_BYTES,
            "AY input must be a bounded regular file"
        );
        let (sha256, bytes) = hash(&file, metadata.len(), deadline)?;
        ensure!(
            sha256 == input.sha256,
            "AY input differs from complete paired plan"
        );
        let original = Self {
            path,
            file,
            metadata,
            sha256,
            bytes,
        };
        original.validate(deadline)?;
        Ok(original)
    }
    fn validate(&self, deadline: Instant) -> CargoResult<()> {
        ensure!(
            self.path.canonicalize()? == self.path
                && same(&self.metadata, &std::fs::symlink_metadata(&self.path)?)
                && same(&self.metadata, &self.file.metadata()?),
            "original AY input entry/description changed"
        );
        let (sha256, _) = hash(&self.file, self.metadata.len(), deadline)?;
        ensure!(
            sha256 == self.sha256
                && same(&self.metadata, &self.file.metadata()?)
                && same(&self.metadata, &std::fs::symlink_metadata(&self.path)?),
            "original AY input bytes changed"
        );
        Ok(())
    }
}

pub(crate) struct Subject {
    source: SourceInputs,
    root: PathBuf,
    files: Vec<BoundFile>,
    deadline: Instant,
    policy_failure: Option<String>,
    legacy: Option<Metadata>,
}
impl Subject {
    #[cfg(test)]
    fn capture(subject: &AySubject, deadline: Instant) -> CargoResult<Arc<Self>> {
        Self::capture_with(subject, deadline, SourceInputs::capture)
    }
    pub(crate) fn capture_admitted(
        subject: &AySubject,
        deadline: Instant,
        budget: &Arc<trust_resource_controller::descriptors::DescriptorBudget>,
        output: &Path,
        cache: &Path,
    ) -> CargoResult<Arc<Self>> {
        Self::capture_with(subject, deadline, |root| {
            SourceInputs::capture_admitted(root, budget, deadline, output, cache)
        })
    }
    fn capture_with(
        subject: &AySubject,
        deadline: Instant,
        source: impl FnOnce(&Path) -> CargoResult<SourceInputs>,
    ) -> CargoResult<Arc<Self>> {
        subject.validate()?;
        let root = PathBuf::from(std::ffi::OsString::from_vec(subject.root.clone()));
        ensure!(
            root.canonicalize()? == root,
            "AY source root is not original canonical path"
        );
        let legacy = match std::fs::symlink_metadata(root.join(".cargo/config")) {
            Ok(metadata) => Some(metadata),
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => None,
            Err(error) => return Err(error.into()),
        };
        let source = source(&root.join("crates/ay-proof-common"))?;
        let mut files = Vec::new();
        for input in [
            &subject.workspace_manifest,
            &subject.crate_manifest,
            &subject.lockfile,
            &subject.cargo_config,
            &subject.toolchain_config,
        ] {
            files.push(BoundFile::open(input, deadline)?);
        }
        let mut policy_failure = (|| -> CargoResult<()> {
            defaults::validate(
                std::str::from_utf8(&files[3].bytes)?,
                std::str::from_utf8(&files[4].bytes)?,
            )
        })()
        .err()
        .map(|error| format!("{error:#}"));
        if legacy.is_some() {
            policy_failure.get_or_insert("ambiguous legacy AY Cargo policy".into());
        }
        let original = Arc::new(Self {
            source,
            root,
            files,
            deadline,
            policy_failure,
            legacy,
        });
        original.validate()?;
        Ok(original)
    }
    /// A known invalid AY default blocks its own compile/verify nodes. The
    /// original source binding remains inspectable and independent consumer
    /// coverage may still run under the same root. Drift remains a fatal input
    /// failure, never normalized into this declared policy outcome.
    pub(crate) fn require_default_policy(&self) -> CargoResult<()> {
        self.validate()?;
        ensure!(
            self.policy_failure.is_none(),
            "AY default-policy node failed: {}",
            self.policy_failure.as_deref().unwrap_or("")
        );
        Ok(())
    }
    pub(crate) fn validate(&self) -> CargoResult<()> {
        let mut failures = Vec::new();
        if let Err(error) = self.source.ensure_current() {
            failures.push(format!("{error:#}"));
        }
        for file in &self.files {
            if let Err(error) = file.validate(self.deadline) {
                failures.push(format!("{}: {error:#}", file.path.display()));
            }
        }
        let legacy = std::fs::symlink_metadata(self.root.join(".cargo/config"));
        let unchanged = match (&self.legacy, &legacy) {
            (None, Err(error)) => error.kind() == std::io::ErrorKind::NotFound,
            (Some(before), Ok(now)) => same_entry(before, now),
            _ => false,
        };
        if !unchanged {
            failures.push("original legacy AY Cargo configuration presence/entry changed".into());
        }
        if self.root.canonicalize().ok().as_deref() != Some(self.root.as_path()) {
            failures.push("AY source root changed".into());
        }
        ensure!(
            failures.is_empty(),
            "AY source/policy revalidation failed: {}",
            failures.join("; ")
        );
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::os::unix::ffi::OsStrExt as _;
    fn fixture(root: &Path) -> AySubject {
        std::fs::create_dir_all(root.join("crates/ay-proof-common/src")).unwrap();
        std::fs::create_dir(root.join(".cargo")).unwrap();
        let pinned = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../../../../first-party/ay");
        for name in [".cargo/config.toml", "rust-toolchain.toml"] {
            std::fs::copy(pinned.join(name), root.join(name)).unwrap();
        }
        for (name, bytes) in [
            (
                "Cargo.toml",
                "[workspace]\nmembers=['crates/ay-proof-common']\n",
            ),
            ("Cargo.lock", "version = 4\n"),
            (
                "crates/ay-proof-common/Cargo.toml",
                "[package]\nname='ay-proof-common'\nversion='0.0.0'\n",
            ),
            (
                "crates/ay-proof-common/src/lib.rs",
                "pub fn original()->u8 {7}\n",
            ),
        ] {
            std::fs::write(root.join(name), bytes).unwrap();
        }
        let input = |name: &str| {
            let path = root.join(name);
            let mut sha = cargo_util::Sha256::new();
            sha.update_path(&path).unwrap();
            InputFile {
                path: path.as_os_str().as_bytes().to_vec(),
                sha256: sha.finish(),
            }
        };
        AySubject {
            root: root.as_os_str().as_bytes().to_vec(),
            workspace_manifest: input("Cargo.toml"),
            crate_manifest: input("crates/ay-proof-common/Cargo.toml"),
            lockfile: input("Cargo.lock"),
            cargo_config: input(".cargo/config.toml"),
            toolchain_config: input("rust-toolchain.toml"),
            source_commit: [1; 20],
            crate_tree: [2; 20],
        }
    }
    #[test]
    fn original_native_files_and_full_crate_membership_are_rebound_without_saved_data_authority() {
        let temporary = tempfile::tempdir().unwrap();
        let root = temporary.path().canonicalize().unwrap();
        let plan = fixture(&root);
        let subject = Subject::capture(&plan, Instant::now() + Duration::from_secs(30)).unwrap();
        subject.validate().unwrap();
        subject.require_default_policy().unwrap();
        std::fs::write(
            root.join("crates/ay-proof-common/src/new_module.rs"),
            "pub const NEW:u8=1;",
        )
        .unwrap();
        assert!(subject.validate().is_err());
        std::fs::remove_file(root.join("crates/ay-proof-common/src/new_module.rs")).unwrap();
        subject.validate().unwrap();
        // Matching saved bytes cannot substitute a new actual file identity.
        let bytes = std::fs::read(root.join("Cargo.lock")).unwrap();
        std::fs::rename(root.join("Cargo.lock"), root.join("old-lock")).unwrap();
        std::fs::write(root.join("Cargo.lock"), bytes).unwrap();
        std::fs::write(root.join("Cargo.toml"), "[workspace]\nmembers=[]\n").unwrap();
        let failure = subject.validate().unwrap_err().to_string();
        assert!(
            failure.contains("Cargo.lock") && failure.contains("Cargo.toml"),
            "every original file is rebound even after earlier failures: {failure}"
        );
    }
    #[test]
    fn wrong_plan_digest_alias_and_appearing_legacy_config_refuse() {
        let temporary = tempfile::tempdir().unwrap();
        let root = temporary.path().canonicalize().unwrap();
        let mut plan = fixture(&root);
        plan.lockfile.sha256 = [9; 32];
        assert!(Subject::capture(&plan, Instant::now() + Duration::from_secs(30)).is_err());
        plan = fixture_rebind(&root, &plan);
        let subject = Subject::capture(&plan, Instant::now() + Duration::from_secs(30)).unwrap();
        std::fs::write(root.join(".cargo/config"), "").unwrap();
        assert!(subject.validate().is_err());
        std::fs::remove_file(root.join(".cargo/config")).unwrap();
        let bytes = std::fs::read(root.join("Cargo.lock")).unwrap();
        std::fs::remove_file(root.join("Cargo.lock")).unwrap();
        std::fs::write(root.join("other-lock"), bytes).unwrap();
        std::os::unix::fs::symlink("other-lock", root.join("Cargo.lock")).unwrap();
        assert!(Subject::capture(&plan, Instant::now() + Duration::from_secs(30)).is_err());
    }
    #[test]
    fn known_default_policy_failure_remains_separate_from_changed_source_inputs() {
        let temporary = tempfile::tempdir().unwrap();
        let root = temporary.path().canonicalize().unwrap();
        let mut plan = fixture(&root);
        let path = root.join(".cargo/config.toml");
        let text = std::fs::read_to_string(&path).unwrap();
        std::fs::write(
            &path,
            text.replace("-Ztrust-verify-level=2", "-Ztrust-verify-level=1"),
        )
        .unwrap();
        let mut sha = cargo_util::Sha256::new();
        sha.update_path(&path).unwrap();
        plan.cargo_config.sha256 = sha.finish();
        let subject = Subject::capture(&plan, Instant::now() + Duration::from_secs(30)).unwrap();
        assert!(subject.require_default_policy().is_err());
        subject.validate().unwrap();
        std::fs::write(path, text).unwrap();
        assert!(
            subject.validate().is_err(),
            "later source change cannot become a mere policy result"
        );
    }
    #[test]
    fn initial_legacy_policy_refusal_retains_inputs_but_later_replacement_is_drift() {
        let temporary = tempfile::tempdir().unwrap();
        let root = temporary.path().canonicalize().unwrap();
        let plan = fixture(&root);
        std::fs::write(root.join(".cargo/config"), "[build]\njobs=1\n").unwrap();
        let subject = Subject::capture(&plan, Instant::now() + Duration::from_secs(30)).unwrap();
        assert!(subject.require_default_policy().is_err());
        subject.validate().unwrap();
        std::fs::remove_file(root.join(".cargo/config")).unwrap();
        assert!(subject.validate().is_err());
    }
    fn fixture_rebind(root: &Path, plan: &AySubject) -> AySubject {
        let mut plan = plan.clone();
        let mut sha = cargo_util::Sha256::new();
        sha.update_path(&root.join("Cargo.lock")).unwrap();
        plan.lockfile.sha256 = sha.finish();
        plan
    }
}
