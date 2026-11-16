//! Trust: source-tree inputs for confined compiler actions.
//!
//! A dep-info file names files read by the previous compilation. It cannot
//! describe negative facts, such as the absence of a second module candidate.
//! This snapshot includes every entry in a read-only package tree. It is one
//! component of an action identity, not a complete shared-cache authority.

use std::fs::{self, Metadata, OpenOptions};
use std::io::Read;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use anyhow::{Context, bail};
use cargo_util::Sha256;

use super::{BuildRunner, Unit};
use crate::CargoResult;
use crate::util::file_identity::{
    metadata_is_plain_directory, metadata_is_plain_file, opened_file_identity,
};

const MAX_ENTRIES: usize = 100_000;
const MAX_BYTES: u64 = 512 * 1024 * 1024;

#[derive(Debug)]
pub(crate) struct SourceInputs {
    root: PathBuf,
    digest: String,
    // SAME admitted package originals retained across units, policies and
    // failed commands. Legacy content identity alone acquires no such owner.
    #[cfg(unix)]
    native: Option<(
        Arc<trust_resource_controller::descriptors::AdmittedPackageSource>,
        std::time::Instant,
    )>,
}

impl SourceInputs {
    pub fn capture(root: &Path) -> CargoResult<Self> {
        #[cfg(unix)]
        if let Some(startup) =
            crate::resource_v3::current().filter(|startup| startup.workload_bank.is_some())
        {
            let budget = startup
                .descriptor_budget
                .as_ref()
                .context("native source lost SAME preparation budget")?;
            let process = startup
                .workload_process
                .as_ref()
                .context("native source lost original Root inputs")?;
            use std::os::unix::ffi::OsStringExt as _;
            let path = |bytes: &[u8]| PathBuf::from(std::ffi::OsString::from_vec(bytes.to_vec()));
            let invocation = process.invocation.header();
            return Self::capture_admitted(
                root,
                budget,
                process.deadline,
                &path(invocation.output_root),
                &path(invocation.cargo_home),
            );
        }
        Self::capture_legacy(root)
    }
    fn capture_legacy(root: &Path) -> CargoResult<Self> {
        tracing::trace!(path = %root.display(), "capturing confined source inputs");
        if !root.is_absolute() {
            bail!("source input root must be absolute");
        }
        let selected = root.to_path_buf();
        let root = root.canonicalize()?;
        let entries = inventory(&root)?;
        let mut hash = Sha256::new();
        field(&mut hash, b"targo-read-only-source-tree-v1");
        field(&mut hash, selected.as_os_str().as_encoded_bytes());
        field(&mut hash, root.as_os_str().as_encoded_bytes());
        let mut bytes = 0_u64;
        for (relative, directory) in &entries {
            field(&mut hash, relative.as_os_str().as_encoded_bytes());
            field(&mut hash, if *directory { b"directory" } else { b"file" });
            let path = root.join(relative);
            let metadata = fs::symlink_metadata(&path)?;
            permissions(&mut hash, &metadata);
            if !directory {
                let mut options = OpenOptions::new();
                options.read(true);
                #[cfg(unix)]
                {
                    use std::os::unix::fs::OpenOptionsExt;
                    options.custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK);
                }
                let mut file = options.open(&path)?;
                let before = file.metadata()?;
                if !metadata_is_plain_file(&before) {
                    bail!("source input is not a regular file: {}", path.display());
                }
                let opened = opened_file_identity(&file)?;
                bytes = bytes
                    .checked_add(before.len())
                    .context("source input size overflow")?;
                if bytes > MAX_BYTES {
                    bail!("source input tree exceeds its byte limit");
                }
                hash.update(&before.len().to_le_bytes());
                let mut count = 0;
                let mut buffer = [0; 64 * 1024];
                loop {
                    let read = file.read(&mut buffer)?;
                    if read == 0 {
                        break;
                    }
                    count += read as u64;
                    if count > before.len() {
                        bail!("source input grew during capture");
                    }
                    hash.update(&buffer[..read]);
                }
                if count != before.len()
                    || !unchanged(&before, &file.metadata()?)
                    || opened != opened_file_identity(&options.open(&path)?)?
                {
                    bail!("source input changed during capture: {}", path.display());
                }
            }
        }
        if entries != inventory(&root)? || selected.canonicalize()? != root {
            bail!("source input directory membership changed during capture");
        }
        Ok(Self {
            root: selected,
            digest: hash.finish_hex(),
            #[cfg(unix)]
            native: None,
        })
    }

    #[cfg(unix)]
    pub(crate) fn capture_admitted(
        root: &Path,
        budget: &Arc<trust_resource_controller::descriptors::DescriptorBudget>,
        deadline: std::time::Instant,
        output: &Path,
        cache: &Path,
    ) -> CargoResult<Self> {
        if !source_is_read_only(root, &[output.to_owned()], cache) {
            bail!("native package source overlaps writable output/cache or cannot be resolved");
        }
        let original = budget.capture_source(root, deadline)?;
        original.validate(deadline)?;
        Ok(Self {
            root: root.into(),
            digest: hex::encode(original.content_digest()),
            native: Some((original, deadline)),
        })
    }

    pub fn digest(&self) -> &str {
        &self.digest
    }

    /// Bind a prepared capture to its exact package path without rereading it.
    /// Live input validation still belongs to each planning/execution boundary.
    pub fn ensure_bound_to(&self, root: &Path) -> CargoResult<()> {
        if self.root != root {
            bail!("confined command source capture belongs to another package");
        }
        Ok(())
    }

    pub fn ensure_current(&self) -> CargoResult<()> {
        #[cfg(unix)]
        if let Some((original, deadline)) = &self.native {
            original.validate(*deadline)?;
            return Ok(());
        }
        if Self::capture_legacy(&self.root)?.digest != self.digest {
            bail!(
                "confined action source inputs changed: {}",
                self.root.display()
            );
        }
        Ok(())
    }
}

fn field(hash: &mut Sha256, value: &[u8]) {
    hash.update(&(value.len() as u64).to_le_bytes());
    hash.update(value);
}

fn permissions(hash: &mut Sha256, metadata: &Metadata) {
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        hash.update(&metadata.mode().to_le_bytes());
        hash.update(&metadata.uid().to_le_bytes());
        hash.update(&metadata.gid().to_le_bytes());
    }
    #[cfg(not(unix))]
    hash.update(&[u8::from(metadata.permissions().readonly())]);
}

fn unchanged(before: &Metadata, after: &Metadata) -> bool {
    if before.len() != after.len()
        || !before
            .modified()
            .ok()
            .zip(after.modified().ok())
            .is_some_and(|(a, b)| a == b)
    {
        return false;
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        if (before.ctime(), before.ctime_nsec()) != (after.ctime(), after.ctime_nsec()) {
            return false;
        }
    }
    true
}

fn inventory(root: &Path) -> CargoResult<Vec<(PathBuf, bool)>> {
    let mut pending = vec![root.to_path_buf()];
    let mut entries = Vec::new();
    while let Some(path) = pending.pop() {
        if entries.len() >= MAX_ENTRIES {
            bail!("source input tree exceeds its entry limit");
        }
        let metadata = fs::symlink_metadata(&path)?;
        let directory = metadata_is_plain_directory(&metadata);
        if !directory && !metadata_is_plain_file(&metadata) {
            bail!(
                "source input tree contains a link or special file: {}",
                path.display()
            );
        }
        entries.push((path.strip_prefix(root)?.to_path_buf(), directory));
        if directory {
            for entry in fs::read_dir(&path)? {
                if pending.len() + entries.len() >= MAX_ENTRIES {
                    bail!("source input tree exceeds its entry limit");
                }
                pending.push(entry?.path());
            }
        }
    }
    entries.sort();
    Ok(entries)
}

/// A source tree containing writable build/cache state cannot be treated as a
/// read-only input. Do not omit that state from a purported complete snapshot.
pub(super) fn for_unit(
    build: &mut BuildRunner<'_, '_>,
    unit: &Unit,
) -> CargoResult<Option<Arc<SourceInputs>>> {
    if !build.bcx.confines(unit) {
        return Ok(None);
    }
    let package = unit.pkg.package_id();
    if let Some(inputs) = build.action_source_inputs.get(&package) {
        if let Some(inputs) = inputs {
            // Replanning after a unit-lock wait must not reuse the earlier
            // source snapshot after the live directory has changed.
            inputs.ensure_current()?;
        }
        return Ok(inputs.clone());
    }
    let root = unit.pkg.root().to_path_buf();
    let mut writable = vec![
        build.bcx.ws.target_dir().into_path_unlocked(),
        build.bcx.ws.build_dir().into_path_unlocked(),
    ];
    if let Some(shared) = &build.bcx.shared_dependency_root {
        writable.push(shared.clone());
    }
    if let Some(export) = &build.bcx.build_config.export_dir {
        writable.push(build.bcx.gctx.cwd().join(export));
    }
    let home = build.bcx.gctx.home().as_path_unlocked();
    let inputs = if source_is_read_only(&root, &writable, home) {
        Some(Arc::new(SourceInputs::capture(&root)?))
    } else {
        None
    };
    build.action_source_inputs.insert(package, inputs.clone());
    Ok(inputs)
}

fn source_is_read_only(root: &Path, writable: &[PathBuf], cache: &Path) -> bool {
    let (Ok(root), Ok(cache)) = (root.canonicalize(), cache.canonicalize()) else {
        return false;
    };
    !cache.starts_with(&root)
        && writable.iter().all(|path| {
            path.canonicalize()
                .is_ok_and(|path| !path.starts_with(&root) && !root.starts_with(path))
        })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    #[test]
    fn admitted_native_package_reuses_originals_and_preserves_legacy_content_scope() {
        let temporary = tempfile::tempdir().unwrap();
        let base = temporary.path().canonicalize().unwrap();
        let source = base.join("source");
        let output = base.join("output");
        let cache = base.join("cache");
        for path in [&source, &output, &cache] {
            fs::create_dir(path).unwrap();
        }
        fs::create_dir(source.join("empty")).unwrap();
        fs::write(
            source.join("lib.rs"),
            b"mod absent;
",
        )
        .unwrap();
        fs::write(source.join(".hidden"), b"").unwrap();
        let legacy = SourceInputs::capture_legacy(&source).unwrap();
        let budget =
            trust_resource_controller::descriptors::DescriptorBudget::for_preparation(1, 0)
                .unwrap();
        let until = std::time::Instant::now() + std::time::Duration::from_secs(30);
        let first =
            SourceInputs::capture_admitted(&source, &budget, until, &output, &cache).unwrap();
        let second =
            SourceInputs::capture_admitted(&source, &budget, until, &output, &cache).unwrap();
        assert_eq!(first.digest(), legacy.digest());
        assert!(Arc::ptr_eq(
            &first.native.as_ref().unwrap().0,
            &second.native.as_ref().unwrap().0
        ));
        for _ in 0..8 {
            let reused =
                SourceInputs::capture_admitted(&source, &budget, until, &output, &cache).unwrap();
            assert!(Arc::ptr_eq(
                &first.native.as_ref().unwrap().0,
                &reused.native.as_ref().unwrap().0
            ));
            reused.ensure_current().unwrap();
        }
        fs::write(source.join("absent.rs"), b"new input").unwrap();
        assert!(first.ensure_current().is_err());
        fs::remove_file(source.join("absent.rs")).unwrap();
        assert!(
            second.ensure_current().is_err(),
            "no restored-byte resurrection of an original owner"
        );
        assert!(SourceInputs::capture_admitted(&source, &budget, until, &output, &cache).is_err());
    }
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    #[test]
    fn native_package_cache_cannot_rebind_legacy_selected_path_spelling() {
        let temporary = tempfile::tempdir().unwrap();
        let base = temporary.path().canonicalize().unwrap();
        let source = base.join("source");
        let alias = base.join("alias");
        let output = base.join("output");
        let cache = base.join("cache");
        for path in [&source, &output, &cache] {
            fs::create_dir(path).unwrap();
        }
        fs::write(
            source.join("lib.rs"),
            b"pub fn original() {}
",
        )
        .unwrap();
        std::os::unix::fs::symlink(&source, &alias).unwrap();
        let original = SourceInputs::capture_legacy(&source).unwrap();
        let selected_alias = SourceInputs::capture_legacy(&alias).unwrap();
        assert_ne!(
            original.digest(),
            selected_alias.digest(),
            "v1 binds selected spelling independently of resolved root"
        );
        let budget =
            trust_resource_controller::descriptors::DescriptorBudget::for_preparation(1, 0)
                .unwrap();
        let until = std::time::Instant::now() + std::time::Duration::from_secs(30);
        let admitted =
            SourceInputs::capture_admitted(&source, &budget, until, &output, &cache).unwrap();
        assert_eq!(admitted.digest(), original.digest());
        assert!(SourceInputs::capture_admitted(&alias, &budget, until, &output, &cache).is_err());
        admitted.ensure_current().unwrap();
        let shared =
            SourceInputs::capture_admitted(&source, &budget, until, &output, &cache).unwrap();
        assert!(Arc::ptr_eq(
            &admitted.native.as_ref().unwrap().0,
            &shared.native.as_ref().unwrap().0
        ));
    }

    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    #[test]
    fn native_source_refuses_nested_output_and_cache_before_admitted_capture() {
        let temporary = tempfile::tempdir().unwrap();
        let base = temporary.path().canonicalize().unwrap();
        let root = base.join("source");
        let output = base.join("output");
        let cache = base.join("cache");
        for path in [&root, &output, &cache] {
            fs::create_dir(path).unwrap();
        }
        let nested = root.join("nested");
        fs::create_dir(&nested).unwrap();
        let budget =
            trust_resource_controller::descriptors::DescriptorBudget::for_preparation(1, 0)
                .unwrap();
        let until = std::time::Instant::now() + std::time::Duration::from_secs(30);
        assert!(SourceInputs::capture_admitted(&root, &budget, until, &nested, &cache).is_err());
        assert!(SourceInputs::capture_admitted(&root, &budget, until, &output, &nested).is_err());
    }

    #[test]
    fn writable_roots_cannot_be_hidden_from_the_source_identity() {
        let temp = tempfile::tempdir().unwrap();
        let source = temp.path().join("source");
        let output = temp.path().join("output");
        let cache = temp.path().join("cache");
        for path in [&source, &output, &cache] {
            fs::create_dir(path).unwrap();
        }
        assert!(source_is_read_only(&source, &[output.clone()], &cache));
        let nested = source.join("target");
        fs::create_dir(&nested).unwrap();
        assert!(!source_is_read_only(&source, &[nested], &cache));
        assert!(!source_is_read_only(&source, &[output.clone()], &source));
        assert!(!source_is_read_only(
            &source,
            &[temp.path().join("unknown")],
            &cache
        ));
        #[cfg(unix)]
        {
            let alias = temp.path().join("alias");
            std::os::unix::fs::symlink(&source, &alias).unwrap();
            assert!(!source_is_read_only(&source, &[alias], &cache));
        }
    }

    #[test]
    fn source_identity_includes_membership_and_bytes_but_not_timestamps() {
        let root = tempfile::tempdir().unwrap();
        let source = root.path().join("lib.rs");
        fs::write(&source, "mod child;\n").unwrap();
        let first = SourceInputs::capture(root.path()).unwrap();
        filetime::set_file_mtime(&source, filetime::FileTime::from_unix_time(1, 0)).unwrap();
        first.ensure_current().unwrap();
        fs::create_dir(root.path().join("child")).unwrap();
        assert!(first.ensure_current().is_err());
        fs::remove_dir(root.path().join("child")).unwrap();
        first.ensure_current().unwrap();
        fs::write(&source, "mod other;\n").unwrap();
        assert!(first.ensure_current().is_err());
    }

    #[test]
    fn prepared_source_binding_rejects_another_package() {
        let root = tempfile::tempdir().unwrap();
        let other = tempfile::tempdir().unwrap();
        let inputs = SourceInputs::capture(root.path()).unwrap();
        inputs.ensure_bound_to(root.path()).unwrap();
        assert!(inputs.ensure_bound_to(other.path()).is_err());
    }

    #[cfg(unix)]
    #[test]
    fn source_snapshot_does_not_follow_links_out_of_its_root() {
        let root = tempfile::tempdir().unwrap();
        std::os::unix::fs::symlink("/etc/passwd", root.path().join("escape")).unwrap();
        assert!(SourceInputs::capture(root.path()).is_err());
    }

    #[cfg(unix)]
    #[test]
    fn source_root_retargeting_invalidates_its_binding() {
        let temp = tempfile::tempdir().unwrap();
        let first = temp.path().join("first");
        let second = temp.path().join("second");
        for root in [&first, &second] {
            fs::create_dir(root).unwrap();
            fs::write(root.join("lib.rs"), "pub fn value() {}\n").unwrap();
        }
        let selected = temp.path().join("selected");
        std::os::unix::fs::symlink(&first, &selected).unwrap();
        let inputs = SourceInputs::capture(&selected).unwrap();
        fs::remove_file(&selected).unwrap();
        std::os::unix::fs::symlink(&second, &selected).unwrap();
        assert!(inputs.ensure_current().is_err());
    }
}
