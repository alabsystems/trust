// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Original immutable image handles shared by book-backed discovery and known-program pins.
use sha2::{Digest, Sha256};

use super::*;
use crate::private::stamp;
use crate::schema::{FileId, digest_shaped};
pub(super) const MAX_IMAGE: u64 = 1024 * 1024 * 1024;

pub(super) struct ImageRef<'a> {
    pub store: &'a Store,
    pub path: &'a Path,
    pub digest: &'a str,
    pub image: FileId,
    pub directory: FileId,
}
impl ImageRef<'_> {
    pub(super) fn open(&self, deadline: Instant) -> io::Result<Image> {
        expired(deadline)?;
        self.store.check()?;
        let directory =
            private::directory(self.path.parent().ok_or_else(|| refused("missing image parent"))?)?;
        let directory_before = directory.metadata()?;
        if identity(&directory_before) != self.directory
            || directory_before.mode() & 0o7777 != 0o500
        {
            return Err(refused("immutable image directory changed"));
        }
        let mut file = private::open_private(&directory, OsStr::new("aterm"))?;
        let before = file.metadata()?;
        if identity(&before) != self.image
            || before.mode() & 0o7777 != 0o500
            || before.len() == 0
            || before.len() > MAX_IMAGE
        {
            return Err(refused("invalid immutable image"));
        }
        let mut hash = Sha256::new();
        let mut bytes = [0; 65536];
        let mut total = 0u64;
        loop {
            expired(deadline)?;
            let count = file.read(&mut bytes)?;
            if count == 0 {
                break;
            }
            total =
                total.checked_add(count as u64).ok_or_else(|| refused("image size overflow"))?;
            if total > MAX_IMAGE {
                return Err(refused("oversized image"));
            }
            hash.update(&bytes[..count]);
        }
        if total != before.len()
            || hex(&hash.finalize()) != self.digest
            || stamp(&before) != stamp(&file.metadata()?)
        {
            return Err(refused("immutable image content changed"));
        }
        let image = Image { file, before, directory, directory_before };
        self.check(&image)?;
        expired(deadline)?;
        Ok(image)
    }
    pub(super) fn check(&self, image: &Image) -> io::Result<()> {
        self.store.check()?;
        private::named_directory(
            self.path.parent().ok_or_else(|| refused("missing image parent"))?,
            &image.directory,
        )?;
        private::named_file(self.path, &image.file)?;
        if identity(&image.directory.metadata()?) != self.directory
            || identity(&image.file.metadata()?) != self.image
            || stamp(&image.directory.metadata()?) != stamp(&image.directory_before)
            || image.directory.metadata()?.mode() & 0o7777 != 0o500
            || stamp(&image.file.metadata()?) != stamp(&image.before)
        {
            return Err(refused("pinned image backing changed"));
        }
        Ok(())
    }
}

/// A once-hashed original immutable executable, independent of listener/book rows.
/// Validation proves only native image provenance, never resource admission.
pub struct PinnedProgram {
    store: Store,
    path: PathBuf,
    digest: String,
    image: Image,
}
impl Store {
    /// Pin exactly an existing `images/<canonical SHA256>/aterm` image in this store.
    /// The initial digest is read once from the same original held file used later.
    pub fn pin_program(&self, path: &Path, deadline: Instant) -> io::Result<PinnedProgram> {
        expired(deadline)?;
        self.check()?;
        let parent = path.parent().ok_or_else(|| refused("missing cached image parent"))?;
        let digest = parent
            .file_name()
            .and_then(OsStr::to_str)
            .filter(|s| digest_shaped(s))
            .ok_or_else(|| refused("invalid cached image digest"))?;
        let canonical = self.0.path.join("images").join(digest).join("aterm");
        if canonical.as_os_str() != path.as_os_str() {
            return Err(refused("exact cached image path required"));
        }
        let directory = private::directory(parent)?;
        let file = private::open_private(&directory, OsStr::new("aterm"))?;
        let reference = ImageRef {
            store: self,
            path,
            digest,
            image: identity(&file.metadata()?),
            directory: identity(&directory.metadata()?),
        };
        let image = reference.open(deadline)?;
        Ok(PinnedProgram { store: self.clone(), path: canonical, digest: digest.to_owned(), image })
    }
}
impl PinnedProgram {
    fn reference(&self) -> ImageRef<'_> {
        ImageRef {
            store: &self.store,
            path: &self.path,
            digest: &self.digest,
            image: identity(&self.image.before),
            directory: identity(&self.image.directory_before),
        }
    }
    /// Validate original held/fresh metadata, private backing and the exact
    /// current kernel-loaded image. No executable bytes are rehashed here.
    pub fn validate_cached_process(&self, native: Identity, deadline: Instant) -> io::Result<()> {
        expired(deadline)?;
        self.reference().check(&self.image)?;
        if process::read_identity(native.pid)? != native
            || !process::image_matches(native, &self.image.file, &self.path)?
            || process::read_identity(native.pid)? != native
        {
            return Err(refused("cached image process changed"));
        }
        self.reference().check(&self.image)?;
        expired(deadline)
    }
}
#[cfg(test)]
#[path = "image_pin/tests.rs"]
mod tests;
