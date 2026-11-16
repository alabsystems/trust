// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Actual bounded physical input reads, without committed/source meaning.
//! The caller retains its genuine semantic root beside this SAME read-set.

use super::*;

impl HeldSourceReadSet {
    /// Capture actual protected file bytes/mode, a directory, or the FIRST
    /// anchored missing component under this SAME original readonly root.
    /// No link is followed. This supplies physical DATA, never committed
    /// membership, configuration completeness, a source owner, Seed or SDK.
    ///
    /// All original guards and shared population/byte bounds remain in force.
    /// Accepted files/ancestors are retained before any payload allocation or
    /// read, including when that read or a later size/bookend check refuses.
    /// Refusal permanently quarantines this same set; it cannot be retried as
    /// a fresh interpretation after restoring the path or bytes.
    pub fn capture_input(&mut self, root: BorrowedFd<'_>, path: &Path) -> io::Result<SourceRead> {
        let captured = (|| {
            selected_path(path)?;
            self.check_current(root)?;
            let actual = self.capture_input_inner(root, path)?;
            self.check_current(root)?;
            Ok(actual)
        })();
        if captured.is_err() {
            self.revoked.store(true, Ordering::Release);
        }
        captured
    }

    fn capture_input_inner(&mut self, root: BorrowedFd<'_>, path: &Path) -> io::Result<SourceRead> {
        let mut prefix = PathBuf::new();
        for part in path.components() {
            time(self.deadline)?;
            prefix.push(part);
            if let Some(leaf) = self.leaves.get(&prefix) {
                match leaf {
                    Leaf::Absent => return self.read(root, &prefix),
                    Leaf::Link { .. } => {
                        return Err(invalid("physical input capture refuses source links"));
                    }
                    Leaf::File { .. } if prefix != path => {
                        return Err(invalid("physical input ancestor is not a directory"));
                    }
                    Leaf::File { .. } => return self.read(root, path),
                }
            }
            self.room(1)?;
            let parent = self.parent(root, &prefix, 1)?;
            let file = match open(parent, prefix.file_name().unwrap(), prefix != path) {
                Ok(file) => file,
                Err(error) if error.kind() == io::ErrorKind::NotFound => {
                    self.leaves.insert(prefix, Leaf::Absent);
                    return Ok(SourceRead::Absent);
                }
                Err(error) => return Err(error),
            };
            if file.metadata()?.is_dir() {
                let stamp = protected(&file, true)?;
                if let Some(original) = self.directories.get(&prefix) {
                    if original.stamp != stamp {
                        return Err(invalid("physical input ancestor was substituted"));
                    }
                } else {
                    self.directories.insert(prefix.clone(), Directory { file, stamp });
                }
                if prefix == path {
                    return Ok(SourceRead::Directory);
                }
                continue;
            }

            let stamp = protected(&file, false)?;
            let size = stamp.size;
            let mode = (stamp.mode & 0o177777) as u16;
            // Retain the SAME accepted original BEFORE bounds/allocation/read.
            self.leaves.insert(prefix.clone(), Leaf::File { file, stamp, bytes: Vec::new(), mode });
            if mode & 0o7000 != 0 || size > MAX_FILE_BYTES as u64 {
                return Err(invalid("physical input mode or file size exceeds buffered profile"));
            }
            let size = usize::try_from(size).map_err(error)?;
            self.bytes = self
                .bytes
                .checked_add(size)
                .filter(|total| *total <= MAX_BYTES)
                .ok_or_else(|| invalid("physical input retained bytes exceed bound"))?;
            let Leaf::File { file, stamp, bytes: captured, mode } =
                self.leaves.get_mut(&prefix).expect("same pending original file")
            else {
                unreachable!()
            };
            *captured = bytes(file, stamp, self.deadline)?;
            return Ok(SourceRead::File { mode: *mode, bytes: captured.clone() });
        }
        Err(invalid("physical input has no selected component"))
    }
}

#[cfg(test)]
mod tests;
