//! Original fixed-Root output membership, independent of CPU/source/SDK grade.
//!
//! Only the original Root issues the record binding. Directory mechanics below
//! cannot add membership to an inherited V1 claim or create a resource grant.

use std::os::fd::{AsFd, AsRawFd, BorrowedFd};
use std::os::unix::fs::PermissionsExt as _;

use trust_resource_provenance::data_directory;

use super::*;
use crate::trust_output_lock::OutputLock;

#[derive(Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct Identity {
    device: u64,
    inode: u64,
}
impl Identity {
    fn of(file: &File) -> io::Result<Self> {
        let meta = file.metadata()?;
        Ok(Self { device: meta.dev(), inode: meta.ino() })
    }
}

#[derive(Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct Wire {
    root: Vec<u8>,
    directory: Identity,
    lock: Identity,
    directory_fd: i32,
    lock_fd: i32,
}
impl Wire {
    pub(crate) fn digest(&self) -> io::Result<[u8; 32]> {
        let mut digest = Sha256::new();
        digest.update(b"trust-fixed-original-output-member-v2\0");
        digest.update(u64::try_from(self.root.len()).map_err(io::Error::other)?.to_le_bytes());
        digest.update(&self.root);
        for identity in [self.directory, self.lock] {
            digest.update(identity.device.to_le_bytes());
            digest.update(identity.inode.to_le_bytes());
        }
        Ok(digest.finalize().into())
    }

    pub(super) fn descriptors(&self) -> [i32; 2] {
        [self.directory_fd, self.lock_fd]
    }
}

/// Root-created output exclusion. Drop belongs to the original group after
/// actual descendant retirement, never to an observation or an acknowledgement.
pub(crate) struct Issued {
    lock: OutputLock,
    // LAST: release the original lock before removing this private temporary root.
    directory: tempfile::TempDir,
}
impl Issued {
    pub(crate) fn create() -> io::Result<Self> {
        let directory = tempfile::Builder::new()
            .prefix("trust-fixed-output-")
            .permissions(fs::Permissions::from_mode(0o700))
            .tempdir()?;
        let lock = OutputLock::try_acquire(directory.path())?
            .ok_or_else(|| invalid("new original output directory is already owned"))?;
        let issued = Self { lock, directory };
        issued.check()?;
        Ok(issued)
    }

    pub(crate) fn root(&self) -> io::Result<&Path> {
        self.check()?;
        self.lock.original_root()
    }

    pub(crate) fn check(&self) -> io::Result<()> {
        self.lock.check_current()?;
        let root = self.lock.original_directory()?;
        // This is a fresh private Root, not a repair of a caller's directory.
        let file: File = root.try_clone_to_owned()?.into();
        private_root(&file)?;
        self.lock.check_root(self.directory.path())
    }

    pub(crate) fn wire(&self) -> io::Result<Wire> {
        self.check()?;
        // SAFETY: only close-only original descriptions are offered. Issued
        // stays inside the original fixed claim through actual group drain.
        let originals = unsafe { self.lock.original_descriptions()? };
        let directory: File = originals.directory().try_clone_to_owned()?.into();
        let lock: File = originals.lock().try_clone_to_owned()?.into();
        Ok(Wire {
            root: originals.root().as_os_str().as_bytes().to_vec(),
            directory: Identity::of(&directory)?,
            lock: Identity::of(&lock)?,
            directory_fd: originals.directory().as_raw_fd(),
            lock_fd: originals.lock().as_raw_fd(),
        })
    }
}

fn private_root(file: &File) -> io::Result<()> {
    data_directory::require_owner_mutation_scope(file)?;
    if file.metadata()?.mode() & 0o077 != 0 {
        return Err(invalid("fixed output member is not an original private directory"));
    }
    Ok(())
}

/// Retained originals accepted only after the same fixed record binds Wire's
/// digest. A matching pathname or possession of an unrelated directory is not
/// an issuer and cannot construct this owner outside this module.
pub(super) struct Retained {
    wire: Wire,
    directory: File,
    lock: File,
}
impl Retained {
    pub(super) fn root(&self) -> &Path {
        Path::new(OsStr::from_bytes(&self.wire.root))
    }

    pub(super) fn source_directory(&self, path: &Path) -> io::Result<Option<MemberDirectory>> {
        self.check()?;
        if !path.starts_with(self.root()) {
            return Ok(None);
        }
        self.directory(path).map(Some)
    }

    pub(super) fn check_source_file(
        &self,
        directory: &MemberDirectory,
        name: &OsStr,
    ) -> io::Result<()> {
        self.check_directory(directory)?;
        let file = data_directory::open_regular_at(&directory.directory, name)?;
        let before = file.metadata()?;
        if before.uid() != data_directory::effective_uid()
            || before.nlink() != 1
            || before.mode() & 0o022 != 0
        {
            return Err(invalid("member source file is not its owned ordinary single-link file"));
        }
        trust_resource_provenance::require_no_acl_entries(&file)?;
        let after = data_directory::open_regular_at(&directory.directory, name)?;
        let current = after.metadata()?;
        if Identity::of(&file)? != Identity::of(&after)?
            || (before.uid(), before.mode(), before.nlink())
                != (current.uid(), current.mode(), current.nlink())
        {
            return Err(invalid("member source file mapping changed"));
        }
        self.check_directory(directory)
    }
    pub(super) fn capture(
        wire: Wire,
        originals: Option<[std::os::fd::OwnedFd; 2]>,
    ) -> io::Result<Self> {
        let [directory, lock] = match originals {
            Some(originals) => originals.map(File::from),
            None => wire
                .descriptors()
                .map(|fd| trust_build_cpu::duplicate_descriptor(OsStr::new(&fd.to_string())))
                .into_iter()
                .collect::<io::Result<Vec<_>>>()?
                .try_into()
                .map_err(|_| invalid("incomplete original output member"))?,
        };
        let retained = Self { wire, directory, lock };
        retained.check()?;
        // The independent open must contend, and the SAME description must
        // retain EX. Neither operation unlocks or creates another output grant.
        let probe = data_directory::open_regular_at(&retained.directory, OsStr::new("lock"))?;
        match probe.try_lock_shared() {
            Err(std::fs::TryLockError::WouldBlock) => {}
            Err(std::fs::TryLockError::Error(error)) => return Err(error),
            Ok(()) => return Err(invalid("original output member is not exclusively held")),
        }
        retained.lock.try_lock().map_err(io::Error::other)?;
        retained.check()?;
        Ok(retained)
    }

    pub(super) fn check(&self) -> io::Result<()> {
        private_root(&self.directory)?;
        if Identity::of(&self.directory)? != self.wire.directory
            || Identity::of(&self.lock)? != self.wire.lock
        {
            return Err(invalid("original output member descriptions changed"));
        }
        let root = Path::new(OsStr::from_bytes(&self.wire.root));
        let named = fs::symlink_metadata(root)?;
        if !named.is_dir()
            || named.file_type().is_symlink()
            || (named.dev(), named.ino()) != (self.wire.directory.device, self.wire.directory.inode)
        {
            return Err(invalid("original output member root mapping changed"));
        }
        let named_lock = data_directory::open_regular_at(&self.directory, OsStr::new("lock"))?;
        let meta = self.lock.metadata()?;
        if Identity::of(&named_lock)? != self.wire.lock
            || !meta.is_file()
            || meta.nlink() != 1
            || meta.uid() != data_directory::effective_uid()
            || meta.mode() & 0o077 != 0
        {
            return Err(invalid("original output member lock changed"));
        }
        Ok(())
    }

    pub(super) fn descriptors(&self) -> [BorrowedFd<'_>; 2] {
        [self.directory.as_fd(), self.lock.as_fd()]
    }

    pub(super) fn directory(&self, path: &Path) -> io::Result<MemberDirectory> {
        self.directory_with(path, DirectoryPreparation::Existing)
    }

    pub(super) fn prepare_directory(&self, path: &Path) -> io::Result<MemberDirectory> {
        self.directory_with(path, DirectoryPreparation::Create)
    }

    fn directory_with(
        &self,
        path: &Path,
        preparation: DirectoryPreparation,
    ) -> io::Result<MemberDirectory> {
        self.check()?;
        let root = Path::new(OsStr::from_bytes(&self.wire.root));
        let relative = path
            .strip_prefix(root)
            .map_err(|_| invalid("directory is outside its original output member"))?;
        let directory = walk_with(&self.directory, relative, preparation)?;
        let member = MemberDirectory {
            directory,
            relative: relative.to_path_buf(),
            binding: self.wire.digest()?,
        };
        self.check_directory(&member)?;
        Ok(member)
    }

    pub(super) fn check_directory(&self, member: &MemberDirectory) -> io::Result<()> {
        self.check()?;
        if member.binding != self.wire.digest()?
            || Identity::of(&walk(&self.directory, &member.relative)?)?
                != Identity::of(&member.directory)?
        {
            return Err(invalid("directory no longer belongs to the same original output member"));
        }
        Ok(())
    }
}

fn walk(root: &File, relative: &Path) -> io::Result<File> {
    walk_with(root, relative, DirectoryPreparation::Existing)
}

#[derive(Clone, Copy)]
enum DirectoryPreparation {
    Existing,
    Create,
}

fn walk_with(root: &File, relative: &Path, preparation: DirectoryPreparation) -> io::Result<File> {
    let mut directory = data_directory::open_directory_at(root, OsStr::new("."))?;
    let mut count = 0usize;
    for component in relative.components() {
        let std::path::Component::Normal(name) = component else {
            return Err(invalid("output member directory has a non-child component"));
        };
        count += 1;
        if count > 256 {
            return Err(invalid("output member directory depth exceeds its bound"));
        }
        directory = match data_directory::open_directory_at(&directory, name) {
            Ok(directory) => directory,
            Err(error)
                if error.kind() == io::ErrorKind::NotFound
                    && matches!(preparation, DirectoryPreparation::Create) =>
            {
                match data_directory::create_directory_at(&directory, name) {
                    Ok(()) => {}
                    Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {}
                    Err(error) => return Err(error),
                }
                data_directory::open_directory_at(&directory, name)?
            }
            Err(error) => return Err(error),
        };
        data_directory::require_owner_mutation_scope(&directory)?;
    }
    Ok(directory)
}

/// Actual opened directory beneath one retained original output member. This
/// is a cwd/target retention boundary, never a CPU, source or SDK capability.
pub struct MemberDirectory {
    directory: File,
    relative: PathBuf,
    binding: [u8; 32],
}
impl MemberDirectory {
    // Only `handoff::nested`, compiled under the same gate, calls this.
    #[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
    pub(crate) fn original(&self) -> BorrowedFd<'_> {
        self.directory.as_fd()
    }
    pub(super) fn matches(&self, file: &File) -> io::Result<bool> {
        Ok(Identity::of(&self.directory)? == Identity::of(file)?)
    }
    pub(super) fn same_member_directory(&self, other: &Self) -> bool {
        self.binding == other.binding && self.relative == other.relative
    }
}

#[cfg(test)]
#[path = "output_member/tests.rs"]
pub(super) mod tests;
