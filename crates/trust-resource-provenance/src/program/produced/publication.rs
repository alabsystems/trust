// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Fixed original-FD publication primitive. This establishes copied DATA only;
//! the native controller owns CPU admission, writer exclusion and completion.
use super::*;
#[cfg(not(all(target_os = "macos", target_arch = "aarch64")))]
use sha2::Digest as _;
use sha2::Sha256;
use std::io::Write as _;
#[cfg(not(all(target_os = "macos", target_arch = "aarch64")))]
use std::os::unix::fs::FileExt as _;
use std::sync::atomic::AtomicBool;

const MAX_BYTES: u64 = 8 * 1024 * 1024 * 1024;
const MAX_FILES: u64 = 4096;

/// Negative identity DATA from an actual held program/runtime. It grants no
/// write/CPU/SDK rights. Native scope owners must supply the full actual set.
#[derive(Clone, Default)]
pub struct PublicationExclusions {
    pub files: Vec<(u64, u64)>,
    pub directories: Vec<(u64, u64)>,
    pub trees: Vec<(u64, u64)>,
}
impl PublicationExclusions {
    pub fn reject_file_identity(&self, (device, inode): (u64, u64)) -> io::Result<()> {
        if self.files.contains(&(device, inode)) {
            return Err(refused("private entry aliases a protected original file"));
        }
        Ok(())
    }
    pub fn reject_directory_identity(&self, (device, inode): (u64, u64)) -> io::Result<()> {
        if self.directories.contains(&(device, inode)) || self.trees.contains(&(device, inode)) {
            return Err(refused(
                "private entry aliases a protected original directory",
            ));
        }
        Ok(())
    }
    pub(super) fn check_directory(&self, fd: i32) -> io::Result<()> {
        let mut stat: libc::stat = unsafe { std::mem::zeroed() };
        // SAFETY: held original directory and initialized native stat output.
        if unsafe { libc::fstat(fd, &mut stat) } != 0 {
            return Err(io::Error::last_os_error());
        }
        if self
            .directories
            .contains(&(stat.st_dev as u64, stat.st_ino as u64))
        {
            return Err(refused(
                "local write aliases a protected original program directory",
            ));
        }
        Ok(())
    }
    pub(super) fn check_file(&self, meta: &Metadata) -> io::Result<()> {
        if self.files.contains(&(meta.dev(), meta.ino())) {
            return Err(refused(
                "local write aliases a protected original program/runtime inode",
            ));
        }
        Ok(())
    }
}
impl HeldProgram {
    /// Physical negative checks from SAME held SDK/image/runtime originals.
    /// These observations can only veto writes, never authorize execution.
    pub fn publication_exclusions(&self, deadline:Instant) -> io::Result<PublicationExclusions> {
        self.validate(deadline)?;
        let mut result=PublicationExclusions {
            files: std::iter::once(&self.executable).chain(self.runtime.iter()).map(|held|(held.before.dev(),held.before.ino())).collect(),
            directories: self.directories.values().filter(|held|held.selected).map(|held|(held.before.dev(),held.before.ino())).collect(),
            trees: Vec::new(),
        };
        let root=self.directories.get(&self.root).ok_or_else(||refused("original protected SDK root description absent"))?;
        result.trees.push((root.before.dev(),root.before.ino()));
        result.trees.extend(result.directories.iter().copied());
        self.validate(deadline)?; Ok(result)
    }
}
impl HeldProducedProgram {
    /// Observe the actual retained originals, not a path-derived exclusion
    /// registry. Validation precedes projection and no execution is granted.
    pub fn publication_exclusions(&self, deadline: Instant) -> io::Result<PublicationExclusions> {
        self.validate(deadline)?;
        let files = std::iter::once(&self.inputs.executable)
            .chain(self.inputs.runtime.iter())
            .map(|held| (held.before.dev(), held.before.ino()))
            .collect();
        let directories = self
            .inputs
            .directories
            .values()
            .filter(|held| held.selected)
            .map(|held| (held.before.dev(), held.before.ino()))
            .collect();
        let mut result = PublicationExclusions {
            files,
            directories,
            trees: Vec::new(),
        };
        result.files.extend(
            std::iter::once(&self.sdk.executable)
                .chain(self.sdk.runtime.iter())
                .map(|held| (held.before.dev(), held.before.ino())),
        );
        result.directories.extend(
            self.sdk
                .directories
                .values()
                .filter(|held| held.selected)
                .map(|held| (held.before.dev(), held.before.ino())),
        );
        let root = self
            .sdk
            .directories
            .get(&self.sdk.root)
            .ok_or_else(|| refused("original protected SDK root description absent"))?;
        result.trees.push((root.before.dev(), root.before.ino()));
        result.trees.extend(result.directories.iter().copied());
        Ok(result)
    }
}

impl HeldRootFile {
    /// Reserve before every parent/temp/read description is materialized.
    pub fn publication_descriptor_bound() -> usize {
        MAX_COMPONENTS + 6
    }
}

impl HeldOutputRoot {
    /// Observe kernel parent identities from this actual original. Exclusion
    /// DATA only rejects; no path spelling or inode record grants authority.
    pub fn require_disjoint_trees(
        &self,
        exclusions: &PublicationExclusions,
        deadline: Instant,
    ) -> io::Result<()> {
        self.validate(deadline)?;
        require_disjoint_trees(self.backing.file.as_raw_fd(), exclusions, deadline)?;
        self.validate(deadline)
    }

    /// Copy from the actual retained read-only original, through no-follow
    /// parents of this SAME root, into a create-new temporary inode. Only the
    /// completed independent copy is atomically renamed over the destination.
    /// No link, chmod, truncate or rename ever touches the source original.
    ///
    /// # Safety
    /// The caller must own a genuinely admitted native local-operation scope
    /// over a distinct funded original unit, the actual selected output and
    /// Layout guards, and independent exclusion of compiler/foreign writers
    /// and OTHER readers for publication. The coordinator may remain on its
    /// first unit and read; this proves no global read quiescence or pause.
    /// Publication must be disjoint from all of its native writable rules.
    /// Descriptor admission must precede this
    /// call and remain held through its result. Only the fixed native
    /// controller consumer may turn the result into a publication completion;
    /// a path, digest, CPU count or callback cannot discharge these duties.
    pub unsafe fn publish_original_file(
        &self,
        source: &HeldRootFile,
        destination: &Path,
        operation: [u8; 16],
        ordinal: u64,
        exclusions: &PublicationExclusions,
        deadline: Instant,
    ) -> io::Result<HeldRootFile> {
        self.copy_original_file(
            source,
            destination,
            operation,
            ordinal,
            exclusions,
            deadline,
        )
    }
    // The exact lexical filesystem algorithm is separately testable as DATA.
    // Only the unsafe native wrapper above is available to production callers;
    // CPU/exclusion/SDK/local-return authority stays in the native controller.
    fn copy_original_file(
        &self,
        source: &HeldRootFile,
        destination: &Path,
        operation: [u8; 16],
        ordinal: u64,
        exclusions: &PublicationExclusions,
        deadline: Instant,
    ) -> io::Result<HeldRootFile> {
        if !Arc::ptr_eq(&self.backing, &source.output)
            || operation == [0; 16]
            || ordinal >= MAX_FILES
            || destination == source.observation().path
        {
            return Err(refused(
                "publication differs from SAME original output/source operation",
            ));
        }
        self.require_disjoint_trees(exclusions, deadline)?;
        source.validate(deadline)?;
        canonical(destination)?;
        let relative = destination
            .strip_prefix(self.path())
            .map_err(|_| refused("publication destination escapes original output root"))?;
        if relative.as_os_str().is_empty()
            || relative
                .components()
                .any(|part| !matches!(part, Component::Normal(_)))
            || source.input.before.len() > MAX_BYTES
        {
            return Err(refused(
                "publication destination or byte demand exceeds supported profile",
            ));
        }
        let name = destination
            .file_name()
            .ok_or_else(|| refused("publication destination name missing"))?;
        let mut parents = BTreeMap::<PathBuf, HeldDirectory>::new();
        let mut current = self.path().to_owned();
        for component in relative.parent().into_iter().flat_map(Path::components) {
            time(deadline)?;
            let Component::Normal(name) = component else {
                return Err(refused("publication parent is noncanonical"));
            };
            let parent = selected_parent(&self.backing, &parents, &current)?;
            let file = openat(parent, name, true)?;
            let before = owned(&file, true, false)?;
            current.push(name);
            parents.insert(
                current.clone(),
                HeldDirectory {
                    file,
                    before,
                    selected: false,
                },
            );
        }
        let parent = selected_parent(&self.backing, &parents, &current)?;
        require_disjoint_trees(parent, exclusions, deadline)?;
        exclusions.check_directory(parent)?;
        match openat(parent, name, false) {
            Ok(existing) => {
                let before = owned(&existing, false, false)?;
                exclusions.check_file(&before)?;
                if before.dev() == source.input.before.dev()
                    && before.ino() == source.input.before.ino()
                {
                    return Err(refused(
                        "publication destination aliases the retained source inode",
                    ));
                }
            }
            Err(error) if error.kind() == io::ErrorKind::NotFound => {}
            Err(error) => return Err(error),
        }
        // A collision is evidence/refusal. Never delete or reuse an existing
        // temporary file, including one left by an earlier failed operation.
        let temporary = format!(
            ".targo-publish-{}-{ordinal:016x}",
            crate::schema::hex(&operation)
        );
        let temporary_c = CString::new(temporary.as_bytes())
            .map_err(|_| refused("invalid publication temporary name"))?;
        let destination_c = CString::new(name.as_bytes())
            .map_err(|_| refused("invalid publication destination name"))?;
        time(deadline)?;
        // SAFETY: held original parent, bounded single component, create-new
        // private inode; no following, truncating or changing an existing file.
        let raw = unsafe {
            libc::openat(
                parent,
                temporary_c.as_ptr(),
                libc::O_WRONLY | libc::O_CREAT | libc::O_EXCL | libc::O_NOFOLLOW | libc::O_CLOEXEC,
                0o600,
            )
        };
        if raw < 0 {
            return Err(io::Error::last_os_error());
        }
        // SAFETY: successful openat transfers this fresh original description.
        let mut writer = unsafe { File::from_raw_fd(raw) };
        let mut offset = 0u64;
        let mut buffer = [0u8; 65536];
        let mut hash = Sha256::new();
        while offset < source.input.before.len() {
            time(deadline)?;
            let wanted = (source.input.before.len() - offset).min(buffer.len() as u64) as usize;
            let count = source.input.file.read_at(&mut buffer[..wanted], offset)?;
            if count == 0 {
                return Err(refused("publication source shortened during copy"));
            }
            writer.write_all(&buffer[..count])?;
            hash.update(&buffer[..count]);
            offset += count as u64;
        }
        if source.input.file.read_at(&mut buffer[..1], offset)? != 0 {
            return Err(refused("publication source grew during copy"));
        }
        let sha256 = crate::schema::hex(&hash.finalize());
        if sha256 != source.observation().sha256 {
            return Err(refused("publication source bytes changed"));
        }
        writer.flush()?;
        time(deadline)?;
        // SAFETY: only the newly created destination inode is changed. The
        // original source's mode/inode/ctime remain untouched.
        // POSIX permission bits fit mode_t on every supported platform,
        // including Darwin's narrower native mode_t.
        let permissions = (source.input.before.mode() & 0o777) as libc::mode_t;
        if unsafe { libc::fchmod(writer.as_raw_fd(), permissions) } != 0 {
            return Err(io::Error::last_os_error());
        }
        writer.sync_all()?;
        time(deadline)?;
        let written = owned(&writer, false, false)?;
        if written.len() != offset || written.nlink() != 1 {
            return Err(refused("publication temporary inode changed"));
        }
        let reader = openat(parent, OsStr::new(&temporary), false)?;
        if stamp(&owned(&reader, false, false)?) != stamp(&written) {
            return Err(refused("publication temporary pathname was substituted"));
        }
        drop(writer);
        source.validate(deadline)?;
        validate_parents(&self.backing, &parents, deadline)?;
        self.validate(deadline)?;
        // SAFETY: two bounded single names relative to the SAME held parent.
        // Atomic publication touches the independent temporary inode only.
        if unsafe { libc::renameat(parent, temporary_c.as_ptr(), parent, destination_c.as_ptr()) }
            != 0
        {
            return Err(io::Error::last_os_error());
        }
        time(deadline)?;
        let before = owned(&reader, false, false)?;
        if before.dev() != written.dev()
            || before.ino() != written.ino()
            || before.len() != offset
            || before.nlink() != 1
        {
            return Err(refused(
                "published destination inode differs from completed copy",
            ));
        }
        source.validate(deadline)?;
        let result = HeldRootFile {
            output: self.backing.clone(),
            parents,
            input: HeldFile {
                file: reader,
                before,
                observation: FileObservation {
                    path: destination.to_owned(),
                    sha256,
                    bytes: offset,
                    device: written.dev(),
                    inode: written.ino(),
                },
            },
            invalid: AtomicBool::new(false),
        };
        result.validate(deadline)?;
        source.validate(deadline)?;
        time(deadline)?;
        Ok(result)
    }
}
fn selected_parent(
    output: &OutputBacking,
    parents: &BTreeMap<PathBuf, HeldDirectory>,
    path: &Path,
) -> io::Result<i32> {
    if path == output.path {
        Ok(output.file.as_raw_fd())
    } else {
        parents
            .get(path)
            .map(|held| held.file.as_raw_fd())
            .ok_or_else(|| refused("publication parent original missing"))
    }
}
fn validate_parents(
    output: &OutputBacking,
    parents: &BTreeMap<PathBuf, HeldDirectory>,
    deadline: Instant,
) -> io::Result<()> {
    for (path, held) in parents {
        time(deadline)?;
        let named = openat(
            selected_parent(
                output,
                parents,
                path.parent()
                    .ok_or_else(|| refused("publication parent has no ancestor"))?,
            )?,
            path.file_name()
                .ok_or_else(|| refused("publication parent name missing"))?,
            true,
        )?;
        for original in [&held.file, &named] {
            if !same_directory(&held.before, &owned(original, true, false)?, false) {
                return Err(refused("publication parent original was substituted"));
            }
        }
    }
    output.validate(deadline)
}

/// Shared original-FD ancestry veto; callers admit two scratch descriptors.
pub(super) fn require_disjoint_trees(
    fd: i32,
    exclusions: &PublicationExclusions,
    deadline: Instant,
) -> io::Result<()> {
    // SAFETY: caller retains the original; F_DUPFD_CLOEXEC creates our owned copy.
    let raw = unsafe { libc::fcntl(fd, libc::F_DUPFD_CLOEXEC, 3) };
    if raw < 0 {
        return Err(io::Error::last_os_error());
    }
    let mut current = unsafe { File::from_raw_fd(raw) };
    let mut seen = Vec::new();
    for _ in 0..MAX_COMPONENTS {
        time(deadline)?;
        let meta = owned(&current, true, false)?;
        let id = (meta.dev(), meta.ino());
        if exclusions.trees.contains(&id) {
            return Err(refused(
                "selected output aliases a protected SDK/source subtree",
            ));
        }
        if seen.contains(&id) {
            return Err(refused("selected output parent identity cycle"));
        }
        seen.push(id);
        let parent = openat(current.as_raw_fd(), OsStr::new(".."), true)?;
        let next = owned(&parent, true, false)?;
        if (next.dev(), next.ino()) == id {
            return time(deadline);
        }
        current = parent;
    }
    Err(refused("selected output ancestry exceeds native bound"))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;
    fn deadline() -> Instant {
        Instant::now() + Duration::from_secs(60)
    }
    #[test]
    fn lexical_copy_atomically_replaces_with_independent_readonly_original() {
        use std::os::unix::fs::{MetadataExt as _, PermissionsExt as _};
        // Filesystem DATA qualification only. This creates no native local
        // grant, coordinator, SDK, producer eligibility or completion owner.
        let scratch = tempfile::tempdir().unwrap();
        let root = scratch.path().canonicalize().unwrap();
        let output = HeldOutputRoot::open(&root, deadline()).unwrap();
        let _private = output
            .prepare_directory(&root.join("private"), deadline())
            .unwrap();
        let _canonical = output
            .prepare_directory(&root.join("canonical"), deadline())
            .unwrap();
        let source_path = root.join("private/original");
        let destination = root.join("canonical/published");
        let bytes = b"actual retained artifact bytes\0\xff\n";
        std::fs::write(&source_path, bytes).unwrap();
        std::fs::set_permissions(&source_path, std::fs::Permissions::from_mode(0o750)).unwrap();
        std::fs::write(&destination, b"old canonical bytes").unwrap();
        let source = output.file(&source_path, deadline()).unwrap();
        let old = output.file(&destination, deadline()).unwrap();
        let original_fd = File::from(
            source
                .descriptor(deadline())
                .unwrap()
                .try_clone_to_owned()
                .unwrap(),
        );
        let old_fd = File::from(
            old.descriptor(deadline())
                .unwrap()
                .try_clone_to_owned()
                .unwrap(),
        );
        let before = original_fd.metadata().unwrap();
        let copied = output
            .copy_original_file(
                &source,
                &destination,
                [0x71; 16],
                0,
                &PublicationExclusions::default(),
                deadline(),
            )
            .unwrap();
        assert_eq!(std::fs::read(&destination).unwrap(), bytes);
        let current = std::fs::metadata(&destination).unwrap();
        assert_eq!(current.mode() & 0o777, 0o750);
        assert_ne!((current.dev(), current.ino()), (before.dev(), before.ino()));
        assert_eq!(current.nlink(), 1);
        let after = original_fd.metadata().unwrap();
        assert_eq!(
            (
                before.dev(),
                before.ino(),
                before.ctime(),
                before.ctime_nsec(),
                before.mode(),
                before.nlink()
            ),
            (
                after.dev(),
                after.ino(),
                after.ctime(),
                after.ctime_nsec(),
                after.mode(),
                after.nlink()
            )
        );
        source.validate(deadline()).unwrap();
        let mut old_bytes = [0; 19];
        old_fd.read_exact_at(&mut old_bytes, 0).unwrap();
        assert_eq!(&old_bytes, b"old canonical bytes");
        assert!(
            old.validate(deadline()).is_err(),
            "old path owner cannot describe the replacement"
        );
        let raw = copied.descriptor(deadline()).unwrap().as_raw_fd();
        assert_eq!(
            unsafe { libc::fcntl(raw, libc::F_GETFL) } & libc::O_ACCMODE,
            libc::O_RDONLY
        );
        drop(source);
        drop(output);
        copied.validate(deadline()).unwrap();
        let mut retained = vec![0; bytes.len()];
        original_fd.read_exact_at(&mut retained, 0).unwrap();
        assert_eq!(retained, bytes);
    }

    #[test]
    fn actual_ancestor_identity_vetoes_output_and_selected_private_directory() {
        let scratch = tempfile::tempdir().unwrap();
        let root = scratch.path().canonicalize().unwrap();
        let output = HeldOutputRoot::open(&root, deadline()).unwrap();
        let selected = output
            .prepare_directory(&root.join("private/unit"), deadline())
            .unwrap();
        let meta = std::fs::metadata(root.join("private")).unwrap();
        let exclusions = PublicationExclusions {
            trees: vec![(meta.dev(), meta.ino())],
            ..Default::default()
        };
        output
            .require_disjoint_trees(&exclusions, deadline())
            .unwrap();
        assert!(
            selected
                .require_disjoint_trees(&exclusions, deadline())
                .is_err()
        );
        let root_id = std::fs::metadata(&root).unwrap();
        let exclusions = PublicationExclusions {
            trees: vec![(root_id.dev(), root_id.ino())],
            ..Default::default()
        };
        assert!(
            output
                .require_disjoint_trees(&exclusions, deadline())
                .is_err()
        );
        assert!(
            selected
                .require_disjoint_trees(&exclusions, deadline())
                .is_err()
        );
    }

    #[test]
    fn protected_parent_identity_refuses_before_mkdir() {
        let scratch = tempfile::tempdir().unwrap();
        let root = scratch.path().canonicalize().unwrap();
        let output = HeldOutputRoot::open(&root, deadline()).unwrap();
        let existing = output
            .prepare_directory(&root.join("protected"), deadline())
            .unwrap();
        let meta = std::fs::metadata(existing.path()).unwrap();
        let exclusions = PublicationExclusions {
            directories: vec![(meta.dev(), meta.ino())],
            ..Default::default()
        };
        assert!(
            output
                .prepare_directory_excluding(&root.join("protected/new"), &exclusions, deadline())
                .is_err()
        );
        assert!(!root.join("protected/new").exists());
        std::fs::create_dir(root.join("protected/existing")).unwrap();
        let tree = PublicationExclusions {
            trees: vec![(meta.dev(), meta.ino())],
            ..Default::default()
        };
        assert!(
            output
                .prepare_directory_excluding(
                    &root.join("protected/existing/new"),
                    &tree,
                    deadline()
                )
                .is_err()
        );
        assert!(
            !root.join("protected/existing/new").exists(),
            "reject a protected ancestor before modifying its deeper child"
        );
        let unrelated = output
            .prepare_directory_excluding(&root.join("safe/new"), &exclusions, deadline())
            .unwrap();
        unrelated.validate(deadline()).unwrap();
    }

    #[test]
    fn hardlink_identity_is_a_negative_veto_without_path_comparison() {
        let scratch = tempfile::tempdir().unwrap();
        let original = scratch.path().join("original");
        let alias = scratch.path().join("other-spelling");
        std::fs::write(&original, b"retained bytes").unwrap();
        std::fs::hard_link(&original, &alias).unwrap();
        let meta = std::fs::metadata(original).unwrap();
        let exclusions = PublicationExclusions {
            files: vec![(meta.dev(), meta.ino())],
            ..Default::default()
        };
        let alias = std::fs::metadata(alias).unwrap();
        assert!(
            exclusions
                .reject_file_identity((alias.dev(), alias.ino()))
                .is_err()
        );
        assert!(
            exclusions
                .reject_file_identity((alias.dev(), alias.ino() + 1))
                .is_ok()
        );
    }
}
