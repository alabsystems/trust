//! Live ownership of fresh private view entries, never reconstructed from DATA.
//! Cleanup requires the original process and a single-producer private namespace.
//! POSIX unlink is not an atomic unlink-by-inode operation: arbitrary concurrent
//! same-UID namespace replacement is outside this supported profile.
//! The original private root owns the created subtree transitively. Descendant
//! records are private factory DATA; scoped opens do not recover original OFDs.

use super::*;
use std::collections::BTreeSet;

struct CreatedDirectory {
    name: OsString,
    before: Metadata,
}

struct CreatedFile {
    parent: usize,
    name: OsString,
    metadata: Metadata,
    removed: bool,
}

/// Only fresh creation through the actual held parent constructs this owner.
/// Drop retains bytes. No path/report/serde constructor or restart adoption.
pub(in super::super) struct OwnedView {
    parent: File,
    leaf: OsString,
    root: Directory,
    children: Vec<CreatedDirectory>,
    files: Vec<CreatedFile>,
    file_names: BTreeSet<(usize, OsString)>,
    process: u32,
    sealed: bool,
    failed: Cell<bool>,
    cleaned: bool,
}

impl OwnedView {
    pub(super) fn create(parent: &Directory, name: &OsStr) -> CargoResult<Self> {
        ensure!(
            Path::new(name).components().count() == 1
                && matches!(
                    Path::new(name).components().next(),
                    Some(std::path::Component::Normal(_))
                ),
            "private view requires a single fresh leaf"
        );
        let root = parent.create_child(name)?;
        let mut result = Self {
            parent: parent.file.try_clone()?,
            leaf: name.to_owned(),
            root,
            children: Vec::new(),
            files: Vec::new(),
            file_names: BTreeSet::new(),
            process: std::process::id(),
            sealed: false,
            failed: Cell::new(false),
            cleaned: false,
        };
        result.directory(OsStr::new("info"))?;
        result.directory(OsStr::new("pack"))?;
        Ok(result)
    }

    #[cfg(test)]
    pub(super) fn test_create(path: &Path) -> CargoResult<Self> {
        let (_, parent) = controlled_parent(path.parent().context("view parent unavailable")?)?;
        Self::create(&parent, path.file_name().context("view name unavailable")?)
    }

    pub(in super::super) fn path(&self) -> &Path {
        &self.root.path
    }

    pub(super) fn parent_is(&self, parent: &File) -> CargoResult<bool> {
        Ok(stamp(&self.parent.metadata()?, &parent.metadata()?))
    }

    pub(super) fn leaf(&self) -> &OsStr {
        &self.leaf
    }

    fn building(&self) -> CargoResult<()> {
        let result = (|| {
            ensure!(
                !self.sealed,
                "private view is not the original building owner"
            );
            self.live()
        })();
        if result.is_err() {
            self.failed.set(true);
        }
        result
    }

    fn live(&self) -> CargoResult<()> {
        ensure!(
            self.process == std::process::id() && !self.failed.get() && !self.cleaned,
            "private view lost its original live ownership"
        );
        self.root.private_current()
    }

    pub(super) fn directory(&mut self, name: &OsStr) -> CargoResult<usize> {
        let result = (|| {
            self.building()?;
            ensure!(
                matches!(
                    Path::new(name).components().next(),
                    Some(std::path::Component::Normal(_))
                ) && Path::new(name).components().count() == 1,
                "private view requires a single directory leaf"
            );
            if let Some(index) = self.children.iter().position(|entry| entry.name == name) {
                return Ok(index + 1);
            }
            let child = self.root.create_child(name)?;
            // Only actual fresh creation under our held root can add a child.
            self.children.push(CreatedDirectory {
                name: name.to_owned(),
                before: child.before,
            });
            self.root.private_current()?;
            Ok(self.children.len())
        })();
        if result.is_err() {
            self.failed.set(true);
        }
        result
    }

    pub(super) fn check_directory(directory: &Directory, sealed_stamp: bool) -> CargoResult<()> {
        let held = directory.file.metadata()?;
        ensure!(
            held.dev() == directory.before.dev() && held.ino() == directory.before.ino(),
            "original private view directory identity changed"
        );
        // private_current binds this opened description to its current name
        // and validates owner/mode/ACL. The check above additionally binds it
        // to the factory's original creation record, even before sealing.
        directory.private_current()?;
        if sealed_stamp {
            directory.current()?;
        }
        Ok(())
    }

    /// The callback borrows a parent for one operation, never returns its FD.
    /// Mutable phases admit our own clock changes, not a different child inode.
    /// Once sealed, observations require the recorded full stamp.
    fn with_parent(
        &self,
        index: usize,
        sealed_stamp: bool,
        operation: impl FnOnce(&Directory) -> CargoResult<()>,
    ) -> CargoResult<()> {
        let result = (|| {
            self.live()?;
            if sealed_stamp {
                self.root.current()?;
            }
            if index == 0 {
                let result = operation(&self.root);
                let after = Self::check_directory(&self.root, sealed_stamp);
                return result.and(after);
            }
            let entry = self
                .children
                .get(index - 1)
                .context("private object parent unavailable")?;
            let mut directory = self.root.child(&entry.name)?;
            directory.before = entry.before.clone();
            Self::check_directory(&directory, sealed_stamp)?;
            let result = operation(&directory);
            let after = Self::check_directory(&directory, sealed_stamp);
            let root_after = Self::check_directory(&self.root, sealed_stamp);
            result.and(after).and(root_after)
        })();
        if result.is_err() {
            self.failed.set(true);
        }
        result
    }

    /// The private copy callback returns the actual freshly created file, not
    /// metadata supplied by a caller. Its named identity is checked and recorded
    /// inside this live owner before the file closes.
    pub(super) fn create_file(
        &mut self,
        parent: usize,
        name: &OsStr,
        copy: impl FnOnce(&File) -> CargoResult<File>,
    ) -> CargoResult<()> {
        let result = (|| {
            self.building()?;
            ensure!(
                matches!(
                    Path::new(name).components().next(),
                    Some(std::path::Component::Normal(_))
                ) && Path::new(name).components().count() == 1,
                "private view requires a single file leaf"
            );
            let key = (parent, name.to_owned());
            ensure!(
                !self.file_names.contains(&key),
                "private object view entry repeated"
            );
            let mut metadata = None;
            self.with_parent(parent, false, |directory| {
                let file = copy(&directory.file)?;
                let before = file.metadata()?;
                ensure!(
                    before.is_file()
                        && before.nlink() == 1
                        && stamp(&before, &Self::observe_file(&directory.file, name)?),
                    "private object view file changed"
                );
                metadata = Some(before);
                Ok(())
            })?;
            self.file_names.insert(key);
            self.files.push(CreatedFile {
                parent,
                name: name.to_owned(),
                metadata: metadata.context("private view creation did not observe a file")?,
                removed: false,
            });
            Ok(())
        })();
        if result.is_err() {
            self.failed.set(true);
        }
        result
    }

    fn observe_file(parent: &File, name: &OsStr) -> CargoResult<Metadata> {
        Ok(Self::open_file(parent, name)?.metadata()?)
    }

    fn open_file(parent: &File, name: &OsStr) -> CargoResult<File> {
        Ok(File::from(rustix::fs::openat(
            parent,
            name,
            OFlags::RDONLY | OFlags::NOFOLLOW | OFlags::NONBLOCK | OFlags::CLOEXEC,
            Mode::empty(),
        )?))
    }

    fn with_pack_parent(
        &self,
        read: impl FnOnce(usize, &Directory) -> CargoResult<()>,
    ) -> CargoResult<()> {
        let result = (|| {
            ensure!(self.sealed, "private object view is not sealed");
            let parent = self
                .children
                .iter()
                .position(|child| child.name == "pack")
                .map(|index| index + 1)
                .context("private object view lost its pack directory")?;
            self.with_parent(parent, true, |directory| read(parent, directory))
        })();
        if result.is_err() {
            self.failed.set(true);
        }
        result
    }

    fn read_created_file(
        directory: &Directory,
        entry: &CreatedFile,
        read: impl FnOnce(&mut File, u64) -> CargoResult<()>,
    ) -> CargoResult<()> {
        let mut file = Self::open_file(&directory.file, &entry.name)?;
        ensure!(
            stamp(&entry.metadata, &file.metadata()?),
            "original private view file changed before reading"
        );
        let result = read(&mut file, entry.metadata.len());
        let after = (|| {
            ensure!(
                stamp(&entry.metadata, &file.metadata()?)
                    && stamp(
                        &entry.metadata,
                        &Self::observe_file(&directory.file, &entry.name)?
                    ),
                "original private view file changed during reading"
            );
            Ok(())
        })();
        result.and(after)
    }

    pub(in super::super) fn for_each_pack_index(
        &self,
        mut read: impl FnMut(&OsStr, &mut File, u64) -> CargoResult<()>,
    ) -> CargoResult<()> {
        self.with_pack_parent(|parent, directory| {
            for entry in self.files.iter().filter(|entry| {
                entry.parent == parent
                    && Path::new(&entry.name).extension() == Some(OsStr::new("idx"))
            }) {
                Self::read_created_file(directory, entry, |file, len| {
                    read(&entry.name, file, len)
                })?;
            }
            Ok(())
        })
    }

    pub(in super::super) fn read_pack(
        &self,
        name: &OsStr,
        read: impl FnOnce(&mut File, u64) -> CargoResult<()>,
    ) -> CargoResult<()> {
        self.with_pack_parent(|parent, directory| {
            let entry = self
                .files
                .iter()
                .find(|entry| entry.parent == parent && entry.name == name)
                .context("private object view lost its indexed pack")?;
            Self::read_created_file(directory, entry, read)
        })
    }

    fn census(&self, sealed_stamp: bool) -> CargoResult<()> {
        let mut expected = BTreeMap::<usize, BTreeSet<OsString>>::new();
        for child in &self.children {
            expected.entry(0).or_default().insert(child.name.clone());
        }
        for file in &self.files {
            if !file.removed {
                expected
                    .entry(file.parent)
                    .or_default()
                    .insert(file.name.clone());
            }
        }
        for index in 0..=self.children.len() {
            self.with_parent(index, sealed_stamp, |directory| {
                let actual = directory.names()?.into_iter().collect::<BTreeSet<_>>();
                ensure!(
                    actual == expected.remove(&index).unwrap_or_default(),
                    "private object view contains an unexpected or missing entry"
                );
                Ok(())
            })?;
        }
        Ok(())
    }

    pub(super) fn seal(&mut self) -> CargoResult<()> {
        let result = (|| {
            self.building()?;
            self.census(false)?;
            for entry in &self.files {
                self.check_file(entry, false, "new private view file changed before sealing")?;
            }
            // Exactly one transition from fresh mutable build to sealed
            // private DATA. Record clocks only after creation identity and
            // private/named bookends; a replaced child cannot refresh them.
            for index in 0..self.children.len() {
                let mut before = None;
                self.with_parent(index + 1, false, |directory| {
                    before = Some(directory.file.metadata()?);
                    Ok(())
                })?;
                self.children[index].before =
                    before.context("private view child not observed at seal")?;
            }
            self.root.private_current()?;
            self.root.before = self.root.file.metadata()?;
            self.sealed = true;
            self.check_current()
        })();
        if result.is_err() {
            self.failed.set(true);
        }
        result
    }

    fn check_file(&self, entry: &CreatedFile, sealed_stamp: bool, reason: &str) -> CargoResult<()> {
        self.with_parent(entry.parent, sealed_stamp, |directory| {
            ensure!(
                stamp(
                    &entry.metadata,
                    &Self::observe_file(&directory.file, &entry.name)?
                ),
                "{reason}"
            );
            Ok(())
        })
    }

    pub(in super::super) fn check_current(&self) -> CargoResult<()> {
        let result = (|| {
            ensure!(self.sealed, "private view lost its original live ownership");
            self.census(true)?;
            for entry in &self.files {
                self.check_file(entry, true, "original private view file changed")?;
            }
            Self::check_directory(&self.root, true)
        })();
        if result.is_err() {
            self.failed.set(true);
        }
        result
    }

    /// Called only after all ODBs are dropped and the final input bookends pass.
    /// Unknown/replaced entries refuse; a cleanup error retains remaining DATA.
    pub(super) fn cleanup(&mut self) -> CargoResult<()> {
        self.cleanup_with(|| Ok(()))
    }

    fn cleanup_with(&mut self, after_files: impl FnOnce() -> CargoResult<()>) -> CargoResult<()> {
        let result = (|| {
            self.check_current()?;
            for index in 0..self.files.len() {
                let entry = &self.files[index];
                self.with_parent(entry.parent, false, |directory| {
                    ensure!(
                        stamp(
                            &entry.metadata,
                            &Self::observe_file(&directory.file, &entry.name)?
                        ),
                        "private view entry changed before cleanup"
                    );
                    rustix::fs::unlinkat(&directory.file, &entry.name, AtFlags::empty())?;
                    Ok(())
                })?;
                self.files[index].removed = true;
            }
            after_files()?;
            self.census(false)?;
            for entry in self.children.iter().rev() {
                // The original root performs removal. The scoped child stays
                // open through the final named check and actual unlink only.
                self.with_parent(0, false, |root| {
                    let mut directory = root.child(&entry.name)?;
                    directory.before = entry.before.clone();
                    Self::check_directory(&directory, false)?;
                    ensure!(
                        directory.names()?.is_empty(),
                        "private view directory is not empty"
                    );
                    Self::check_directory(&directory, false)?;
                    let named = root.child(&entry.name)?;
                    ensure!(
                        stamp(&directory.file.metadata()?, &named.file.metadata()?),
                        "private view directory changed before cleanup"
                    );
                    rustix::fs::unlinkat(&root.file, &entry.name, AtFlags::REMOVEDIR)?;
                    ensure!(
                        root.missing_relative(Path::new(&entry.name))?,
                        "private view directory reappeared during cleanup"
                    );
                    Ok(())
                })?;
            }
            self.root.private_current()?;
            ensure!(
                self.root.names()?.is_empty(),
                "private view root is not empty"
            );
            let named = File::from(rustix::fs::openat(
                &self.parent,
                &self.leaf,
                OFlags::RDONLY | OFlags::DIRECTORY | OFlags::NOFOLLOW | OFlags::CLOEXEC,
                Mode::empty(),
            )?);
            ensure!(
                stamp(&self.root.file.metadata()?, &named.metadata()?),
                "private view root changed before cleanup"
            );
            rustix::fs::unlinkat(&self.parent, &self.leaf, AtFlags::REMOVEDIR)?;
            self.cleaned = true;
            Ok(())
        })();
        if result.is_err() {
            self.failed.set(true);
        }
        result
    }
}

#[cfg(test)]
mod tests;
