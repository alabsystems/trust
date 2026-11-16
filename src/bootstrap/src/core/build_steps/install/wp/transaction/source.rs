//! Trust: compare actual source bytes with the selected raw committed tree.
//! Git status can trust configurable stat caches, filters and executable modes.

use std::fs;
use std::io::{BufRead, BufReader, Read, Write};
use std::os::unix::ffi::OsStrExt;
use std::os::unix::fs::MetadataExt;
use std::path::{Component, Path};
use std::process::{Child, ChildStdin, ChildStdout, Stdio};

use super::{Directory, cache, error, same_contents_metadata};

// One native process streams raw blobs for the repository, with bounded buffers.
// On every failure its owned child is reaped, including recursive gitlink errors.
struct Blobs {
    child: Child,
    input: Option<ChildStdin>,
    output: BufReader<ChildStdout>,
    finished: bool,
}

impl Blobs {
    fn open(root: &Path) -> Result<Self, String> {
        // Trust: refuse before any raw child is delivered in protected mode.
        crate::utils::exec::require_standalone_process("committed-source blob reader")
            .map_err(error)?;
        let mut child = cache::git_command(root)
            .args(["cat-file", "--batch"])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit())
            .spawn()
            .map_err(error)?;
        let input = child.stdin.take().expect("piped Git input");
        let output = BufReader::new(child.stdout.take().expect("piped Git output"));
        Ok(Self { child, input: Some(input), output, finished: false })
    }

    fn compare(&mut self, object: &str, actual: &mut impl Read) -> Result<(), String> {
        writeln!(self.input.as_mut().unwrap(), "{object}").map_err(error)?;
        let mut header = String::new();
        self.output.read_line(&mut header).map_err(error)?;
        let fields = header.split_whitespace().collect::<Vec<_>>();
        if fields.len() != 3 || fields[0] != object || fields[1] != "blob" {
            return Err("cannot read raw committed source blob".into());
        }
        let mut remaining = fields[2].parse::<u64>().map_err(error)?;
        let mut expected = [0; 65536];
        let mut observed = [0; 65536];
        while remaining != 0 {
            let count = remaining.min(expected.len() as u64) as usize;
            self.output.read_exact(&mut expected[..count]).map_err(error)?;
            actual
                .read_exact(&mut observed[..count])
                .map_err(|e| format!("source differs from committed bytes: {e}"))?;
            if expected[..count] != observed[..count] {
                return Err("source differs from committed bytes".into());
            }
            remaining -= count as u64;
        }
        let mut extra = [0];
        if actual.read(&mut extra).map_err(error)? != 0 {
            return Err("source differs from committed bytes".into());
        }
        self.output.read_exact(&mut extra).map_err(error)?;
        if extra != [b'\n'] {
            return Err("invalid committed source blob framing".into());
        }
        Ok(())
    }

    fn finish(mut self) -> Result<(), String> {
        drop(self.input.take());
        let mut extra = [0];
        if self.output.read(&mut extra).map_err(error)? != 0 {
            return Err("unexpected committed source blob output".into());
        }
        let status = self.child.wait().map_err(error)?;
        self.finished = true;
        if !status.success() {
            return Err("cannot complete raw committed source observation".into());
        }
        Ok(())
    }
}

impl Drop for Blobs {
    fn drop(&mut self) {
        if !self.finished {
            let _ = self.child.kill();
            let _ = self.child.wait();
        }
    }
}

pub(super) fn require_committed_tree(root: &Path, commit: &str) -> Result<(), String> {
    require_committed_tree_with_hooks(root, commit, |_| {}, |_| {}, |_| {})
}

fn require_committed_tree_with_hooks(
    root: &Path,
    commit: &str,
    mut before_entry: impl FnMut(&Path),
    mut parent_opened: impl FnMut(&Path),
    mut entry_ready: impl FnMut(&Path),
) -> Result<(), String> {
    let source = Directory::open(&fs::canonicalize(root).map_err(error)?)?;
    let tree = cache::git(root, &["ls-tree", "--full-tree", "-r", "-z", commit])?;
    let mut blobs = Blobs::open(root)?;
    // Trust: retain only the last parent, not an inventory-sized descriptor map.
    // Adjacent tree entries commonly share it; every use still checks its name.
    let mut directory: Option<Directory> = None;
    for entry in tree.split(|&byte| byte == 0).filter(|entry| !entry.is_empty()) {
        let separator =
            entry.iter().position(|&byte| byte == b'\t').ok_or("invalid source tree")?;
        let fields = std::str::from_utf8(&entry[..separator])
            .map_err(error)?
            .split_whitespace()
            .collect::<Vec<_>>();
        if fields.len() != 3
            || !matches!(fields[2].len(), 40 | 64)
            || !fields[2].bytes().all(|byte| byte.is_ascii_hexdigit())
        {
            return Err("invalid committed source object".into());
        }
        let path = Path::new(std::ffi::OsStr::from_bytes(&entry[separator + 1..]));
        let components = path.components().collect::<Vec<_>>();
        if !components.iter().all(|component| matches!(component, Component::Normal(_))) {
            return Err("invalid committed source path".into());
        }
        let (leaf, parents) = components.split_last().ok_or("empty committed source path")?;
        before_entry(path);
        let parent_path = source.path.join(path.parent().ok_or("empty committed source path")?);
        if directory.as_ref().is_none_or(|cached| cached.path != parent_path) {
            directory = None;
            for component in parents {
                let child = directory.as_ref().unwrap_or(&source).child(component.as_os_str())?;
                parent_opened(&child.path);
                directory = Some(child);
            }
        }
        let parent = directory.as_ref().unwrap_or(&source);
        // A retained descriptor is reusable only while its current canonical
        // path still names it. Keep the existing after-entry check below too.
        parent.check()?;
        entry_ready(path);
        let leaf = leaf.as_os_str();
        let path = parent.path.join(leaf);
        match (fields[0], fields[1]) {
            (mode @ ("100644" | "100755"), "blob") => {
                let mut file = parent.open_entry(leaf, libc::O_RDONLY)?;
                let before = file.metadata().map_err(error)?;
                // Git records the owner's executable bit, not every Unix mode bit.
                if !before.is_file() || (before.mode() & 0o100 != 0) != (mode == "100755") {
                    return Err(format!("source differs from committed mode: {}", path.display()));
                }
                blobs
                    .compare(fields[2], &mut file)
                    .map_err(|error| format!("{error}: {}", path.display()))?;
                if !same_contents_metadata(&before, &file.metadata().map_err(error)?)
                    || !same_contents_metadata(
                        &before,
                        &fs::symlink_metadata(&path).map_err(error)?,
                    )
                {
                    return Err("source moved during committed byte comparison".into());
                }
            }
            ("120000", "blob") => {
                let before = fs::symlink_metadata(&path).map_err(error)?;
                if !before.is_symlink() {
                    return Err(format!(
                        "source differs from committed symlink mode: {}",
                        path.display()
                    ));
                }
                let target = fs::read_link(&path).map_err(error)?;
                blobs
                    .compare(fields[2], &mut target.as_os_str().as_bytes())
                    .map_err(|error| format!("{error}: {}", path.display()))?;
                if !same_contents_metadata(&before, &fs::symlink_metadata(&path).map_err(error)?) {
                    return Err("source link moved during committed byte comparison".into());
                }
            }
            ("160000", "commit") => {
                let child = parent.child(leaf)?;
                super::require_clean_source(&child.path, fields[2])?;
                child.check()?;
            }
            _ => return Err("unsupported committed source mode".into()),
        }
        parent.check()?;
    }
    blobs.finish()?;
    source.check()?;
    if fs::canonicalize(root).map_err(error)? != source.path {
        return Err("observed source root moved during committed byte comparison".into());
    }
    Ok(())
}

#[cfg(test)]
mod tests;
