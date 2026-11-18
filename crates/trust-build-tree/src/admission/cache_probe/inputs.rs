//! Original-directory-relative libstd observations and supported compiler pins.
//! These are health inputs, never SDK readiness, proof or release owners.

use std::ffi::CString;
use std::os::fd::{BorrowedFd, FromRawFd as _};
use std::os::unix::ffi::OsStrExt as _;
use std::os::unix::fs::MetadataExt as _;

use super::*;

#[derive(Debug)]
pub(super) struct StdInput {
    anchor: Arc<File>,
    parent: Arc<File>,
    relative: PathBuf,
    name: OsString,
    file: File,
    before: std::fs::Metadata,
    sha256: [u8; 32],
}
fn open(parent: BorrowedFd<'_>, name: &OsStr, directory: bool) -> io::Result<File> {
    let name = CString::new(name.as_bytes()).map_err(io::Error::other)?;
    let flags = libc::O_RDONLY
        | libc::O_NOFOLLOW
        | libc::O_NONBLOCK
        | libc::O_CLOEXEC
        | if directory { libc::O_DIRECTORY } else { 0 };
    let fd = unsafe { libc::openat(parent.as_raw_fd(), name.as_ptr(), flags) };
    if fd < 0 {
        return Err(io::Error::last_os_error());
    }
    Ok(unsafe { File::from_raw_fd(fd) })
}
fn directory(root: BorrowedFd<'_>, relative: &Path) -> io::Result<File> {
    let mut held = open(root, OsStr::new("."), true)?;
    for part in relative.components() {
        let Component::Normal(part) = part else {
            return Err(invalid("version input is not relative to original output"));
        };
        held = open(held.as_fd(), part, true)?;
    }
    Ok(held)
}
fn identity(meta: &std::fs::Metadata) -> (u64, u64) {
    (meta.dev(), meta.ino())
}
pub(super) fn original_identities(inputs: &[StdInput]) -> impl Iterator<Item = (u64, u64)> + '_ {
    inputs.iter().map(|input| identity(&input.before))
}
fn same_content(before: &std::fs::Metadata, after: &std::fs::Metadata) -> bool {
    identity(before) == identity(after)
        && before.is_file()
        && after.is_file()
        && before.len() == after.len()
        && before.mode() == after.mode()
        && before.uid() == after.uid()
        && before.gid() == after.gid()
        && (before.mtime(), before.mtime_nsec()) == (after.mtime(), after.mtime_nsec())
}
fn digest(file: &File, until: Instant) -> io::Result<[u8; 32]> {
    use std::os::unix::fs::FileExt as _;
    let before = file.metadata()?;
    if !before.is_file() {
        return Err(invalid("version input is not a regular file"));
    }
    let mut hash = Sha256::new();
    let mut bytes = [0; 16384];
    let mut offset = 0;
    loop {
        if Instant::now() >= until {
            return Err(io::ErrorKind::TimedOut.into());
        }
        let n = file.read_at(&mut bytes, offset)?;
        if n == 0 {
            break;
        }
        hash.update(&bytes[..n]);
        offset += n as u64;
    }
    if !same_content(&before, &file.metadata()?) {
        return Err(invalid("version input changed while hashing"));
    }
    Ok(hash.finalize().into())
}

pub(super) fn capture(
    output: &OutputLock,
    relative: &Path,
    host: &OsStr,
    until: Instant,
) -> io::Result<Option<(Arc<HeldProgram>, Vec<StdInput>)>> {
    output.check_current()?;
    let anchor = Arc::new(open(output.original_directory()?, OsStr::new("."), true)?);
    let stage = match directory(anchor.as_fd(), relative) {
        Ok(file) => file,
        Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(None),
        Err(e) => return Err(e),
    };
    let bin = match open(stage.as_fd(), OsStr::new("bin"), true) {
        Ok(file) => file,
        Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(None),
        Err(e) => return Err(e),
    };
    let compiler = match open(bin.as_fd(), OsStr::new("trustc"), false) {
        Ok(file) => file,
        Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(None),
        Err(e) => return Err(e),
    };
    let original = compiler.metadata()?;
    if !original.is_file() {
        return Err(invalid("selected version compiler is not a regular native file"));
    }
    let sha256 = digest(&compiler, until)?;
    let root = output_physical(output)?.join(relative);
    if identity(&std::fs::symlink_metadata(&root)?) != identity(&stage.metadata()?) {
        return Err(invalid("selected sysroot mapping changed"));
    }
    let program = root.join("bin/trustc");
    let held = HeldProgram::open(&root, &program, &sha256, until)?;
    if !same_content(&original, &compiler.metadata()?)
        || held.observation().executable.device != original.dev()
        || held.observation().executable.inode != original.ino()
    {
        return Err(invalid("version compiler differs from original output description"));
    }
    let std_relative = relative.join("lib/rustlib").join(host).join("lib");
    let parent = match directory(anchor.as_fd(), &std_relative) {
        Ok(parent) => Arc::new(parent),
        Err(error) if error.kind() == io::ErrorKind::NotFound => {
            output.check_current()?;
            return Ok(Some((Arc::new(held), Vec::new())));
        }
        Err(error) => return Err(error),
    };
    // Reuse the maintained native Directory enumerator on this INDEPENDENT
    // observation OFD. Its dup+rewind never touches the original output OFD.
    let physical = output_physical(output)?.join(&std_relative);
    let observed = super::super::Directory {
        path: physical,
        file: open(parent.as_fd(), OsStr::new("."), true)?,
    };
    let mut std = Vec::new();
    for name in observed.entries()? {
        let bytes = name.as_bytes();
        if !bytes.starts_with(b"libstd-") || !bytes.ends_with(b".rlib") {
            continue;
        }
        let file = open(parent.as_fd(), &name, false)?;
        let before = file.metadata()?;
        if !before.is_file() {
            return Err(invalid("selected libstd observation is not regular"));
        }
        let sha256 = digest(&file, until)?;
        std.push(StdInput {
            anchor: Arc::clone(&anchor),
            parent: Arc::clone(&parent),
            relative: std_relative.clone(),
            name,
            file,
            before,
            sha256,
        });
    }
    output.check_current()?;
    Ok(Some((Arc::new(held), std)))
}
fn output_physical(output: &OutputLock) -> io::Result<PathBuf> {
    Ok(output.original_root()?.to_owned())
}
pub(super) fn recheck_std(inputs: &[StdInput], until: Instant) -> io::Result<()> {
    for input in inputs {
        let current_parent = directory(input.anchor.as_fd(), &input.relative)?;
        if identity(&current_parent.metadata()?) != identity(&input.parent.metadata()?) {
            return Err(invalid("original libstd directory changed"));
        }
        let named = open(current_parent.as_fd(), &input.name, false)?;
        if !same_content(&input.before, &input.file.metadata()?)
            || !same_content(&input.before, &named.metadata()?)
            || digest(&input.file, until)? != input.sha256
            || digest(&named, until)? != input.sha256
        {
            return Err(invalid("original libstd bytes/name changed across maintenance"));
        }
    }
    Ok(())
}

/// Positive absence witnesses on the SAME original physical host directory.
/// Observations grant no lock/execution/cleanup authority and have no decoder.
#[derive(Debug)]
pub(super) struct AbsentCompilers {
    root: Arc<File>,
    host: Arc<File>,
    relative: PathBuf,
}
impl AbsentCompilers {
    pub(super) fn capture(output: &OutputLock, host: &OsStr) -> io::Result<Self> {
        output.check_current()?;
        let root = Arc::new(open(output.original_directory()?, OsStr::new("."), true)?);
        let relative = PathBuf::from(host);
        let held = Arc::new(directory(root.as_fd(), &relative)?);
        let witness = Self { root, host: held, relative };
        witness.check(output)?;
        Ok(witness)
    }
    pub(super) fn check(&self, output: &OutputLock) -> io::Result<()> {
        output.check_current()?;
        let original = open(output.original_directory()?, OsStr::new("."), true)?;
        if identity(&original.metadata()?) != identity(&self.root.metadata()?) {
            return Err(invalid("seed-tools original output changed"));
        }
        let named = directory(original.as_fd(), &self.relative)?;
        if identity(&named.metadata()?) != identity(&self.host.metadata()?) {
            return Err(invalid("seed-tools original host mapping changed"));
        }
        for stage in ["stage1", "stage2"] {
            match open(self.host.as_fd(), OsStr::new(stage), false) {
                Ok(_) => {
                    return Err(invalid(
                        "seed-tools profile requires BOTH stage1 and stage2 to be absent",
                    ));
                }
                Err(error) if error.kind() == io::ErrorKind::NotFound => {}
                Err(error) => return Err(error),
            }
        }
        if identity(&directory(original.as_fd(), &self.relative)?.metadata()?)
            != identity(&self.host.metadata()?)
        {
            return Err(invalid("seed-tools host changed across absence observation"));
        }
        output.check_current()
    }
}
