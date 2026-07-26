//! Durable publication for machine-readable evidence files without following
//! caller-writable symlink components.

use std::fs;
use std::io::{self, Write as _};
use std::path::Path;
#[cfg(not(unix))]
use std::path::PathBuf;

#[cfg(unix)]
use std::ffi::CString;
#[cfg(unix)]
use std::os::fd::{AsRawFd as _, FromRawFd as _};
#[cfg(unix)]
use std::os::unix::ffi::OsStrExt as _;

/// Atomically publish owner-private bytes in the destination directory.
/// Existing regular files may be replaced; symlinks and non-files fail closed.
pub(crate) fn atomic_write_private(path: &Path, bytes: &[u8]) -> io::Result<()> {
    let parent =
        path.parent().filter(|parent| !parent.as_os_str().is_empty()).unwrap_or(Path::new("."));

    #[cfg(unix)]
    {
        return atomic_write_private_unix(parent, path, bytes);
    }

    #[cfg(not(unix))]
    {
        create_directories_without_symlinks(parent)?;
        match fs::symlink_metadata(path) {
            Ok(metadata) if metadata.file_type().is_symlink() => {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!("refusing to replace symlink output {}", path.display()),
                ));
            }
            Ok(metadata) if !metadata.file_type().is_file() => {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!("refusing to replace non-file output {}", path.display()),
                ));
            }
            Ok(_) => {}
            Err(error) if error.kind() == io::ErrorKind::NotFound => {}
            Err(error) => return Err(error),
        }

        let mut staged = tempfile::Builder::new().prefix(".trust-evidence-").tempfile_in(parent)?;
        staged.write_all(bytes)?;
        staged.flush()?;
        staged.as_file().sync_all()?;

        // Rust's portable rename cannot atomically replace an existing file on
        // every non-Unix platform. Fail closed instead of unlinking a validated
        // leaf and reopening a race window.
        if path.exists() {
            return Err(io::Error::new(
                io::ErrorKind::AlreadyExists,
                format!(
                    "atomic evidence replacement is unsupported for existing {}",
                    path.display()
                ),
            ));
        }
        staged.persist(path).map_err(|error| error.error)?;
        Ok(())
    }
}

#[cfg(unix)]
fn atomic_write_private_unix(parent: &Path, path: &Path, bytes: &[u8]) -> io::Result<()> {
    let destination = path.file_name().ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::InvalidInput,
            format!("evidence output has no file name: {}", path.display()),
        )
    })?;
    let destination = CString::new(destination.as_bytes()).map_err(|_| {
        io::Error::new(io::ErrorKind::InvalidInput, "evidence output name contains NUL")
    })?;
    let directory = open_directory_no_follow(parent)?;
    validate_replaceable_leaf(directory.as_raw_fd(), &destination, path)?;

    let mut random = [0_u8; 16];
    getrandom::fill(&mut random).map_err(io::Error::other)?;
    let nonce = random.iter().map(|byte| format!("{byte:02x}")).collect::<String>();
    let mut staged_name = None;
    let mut staged_file = None;
    for attempt in 0_u32..128 {
        let candidate = CString::new(format!(".trust-evidence-{nonce}-{attempt}"))
            .expect("generated evidence staging name has no NUL");
        let descriptor = unsafe {
            libc::openat(
                directory.as_raw_fd(),
                candidate.as_ptr(),
                libc::O_WRONLY | libc::O_CREAT | libc::O_EXCL | libc::O_CLOEXEC | libc::O_NOFOLLOW,
                0o600,
            )
        };
        if descriptor >= 0 {
            staged_name = Some(candidate);
            staged_file = Some(unsafe { fs::File::from_raw_fd(descriptor) });
            break;
        }
        let error = io::Error::last_os_error();
        if error.kind() != io::ErrorKind::AlreadyExists {
            return Err(error);
        }
    }
    let staged_name = staged_name.ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::AlreadyExists,
            "could not allocate a unique evidence staging file",
        )
    })?;
    let mut staged_file = staged_file.expect("staged name and file are created together");

    let publish = (|| {
        staged_file.write_all(bytes)?;
        staged_file.flush()?;
        staged_file.sync_all()?;
        // Recheck immediately before publication. A later leaf substitution is
        // still safe: renameat replaces the directory entry and never follows
        // its target.
        validate_replaceable_leaf(directory.as_raw_fd(), &destination, path)?;
        let result = unsafe {
            libc::renameat(
                directory.as_raw_fd(),
                staged_name.as_ptr(),
                directory.as_raw_fd(),
                destination.as_ptr(),
            )
        };
        if result != 0 {
            return Err(io::Error::last_os_error());
        }
        directory.sync_all()
    })();

    if publish.is_err() {
        unsafe {
            libc::unlinkat(directory.as_raw_fd(), staged_name.as_ptr(), 0);
        }
    }
    publish
}

#[cfg(unix)]
fn open_directory_no_follow(path: &Path) -> io::Result<fs::File> {
    use std::path::Component;

    let absolute =
        if path.is_absolute() { path.to_path_buf() } else { std::env::current_dir()?.join(path) };
    let mut directory = fs::File::open(Path::new("/"))?;
    for component in absolute.components() {
        let name = match component {
            Component::RootDir | Component::CurDir => continue,
            Component::Normal(name) => name,
            Component::ParentDir | Component::Prefix(_) => {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!(
                        "evidence output directory contains a non-normal component: {}",
                        path.display()
                    ),
                ));
            }
        };
        let name = CString::new(name.as_bytes()).map_err(|_| {
            io::Error::new(io::ErrorKind::InvalidInput, "evidence directory name contains NUL")
        })?;
        let mut component = component_stat(directory.as_raw_fd(), &name)?;
        if component.is_none() {
            let result = unsafe { libc::mkdirat(directory.as_raw_fd(), name.as_ptr(), 0o700) };
            if result != 0 {
                let error = io::Error::last_os_error();
                if error.kind() != io::ErrorKind::AlreadyExists {
                    return Err(error);
                }
            }
            component = component_stat(directory.as_raw_fd(), &name)?;
        }
        let is_symlink =
            component.as_ref().is_some_and(|stat| stat.st_mode & libc::S_IFMT == libc::S_IFLNK);
        if is_symlink && !directory_is_root_owned_nonwritable(directory.as_raw_fd())? {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!(
                    "refusing caller-writable symlink component in evidence directory {}",
                    path.display()
                ),
            ));
        }
        // Root-owned aliases such as macOS `/var -> private/var` are outside
        // the caller's replacement authority. All ordinary components retain
        // O_NOFOLLOW, and the opened directory descriptor owns every later
        // operation.
        let no_follow = if is_symlink { 0 } else { libc::O_NOFOLLOW };
        let descriptor = unsafe {
            libc::openat(
                directory.as_raw_fd(),
                name.as_ptr(),
                libc::O_RDONLY | libc::O_DIRECTORY | libc::O_CLOEXEC | no_follow,
            )
        };
        if descriptor < 0 {
            return Err(io::Error::last_os_error());
        }
        directory = unsafe { fs::File::from_raw_fd(descriptor) };
    }
    Ok(directory)
}

#[cfg(unix)]
fn component_stat(
    directory_fd: std::os::fd::RawFd,
    name: &CString,
) -> io::Result<Option<libc::stat>> {
    let mut stat = std::mem::MaybeUninit::<libc::stat>::uninit();
    let result = unsafe {
        libc::fstatat(directory_fd, name.as_ptr(), stat.as_mut_ptr(), libc::AT_SYMLINK_NOFOLLOW)
    };
    if result != 0 {
        let error = io::Error::last_os_error();
        if error.kind() == io::ErrorKind::NotFound {
            return Ok(None);
        }
        return Err(error);
    }
    Ok(Some(unsafe { stat.assume_init() }))
}

#[cfg(not(unix))]
fn create_directories_without_symlinks(path: &Path) -> io::Result<()> {
    use std::path::Component;

    let absolute =
        if path.is_absolute() { path.to_path_buf() } else { std::env::current_dir()?.join(path) };
    let mut current = PathBuf::new();
    for component in absolute.components() {
        match component {
            Component::Prefix(prefix) => current.push(prefix.as_os_str()),
            Component::RootDir => current.push(component.as_os_str()),
            Component::CurDir => continue,
            Component::ParentDir => {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!("evidence output directory is not canonical: {}", path.display()),
                ));
            }
            Component::Normal(name) => current.push(name),
        }
        match fs::symlink_metadata(&current) {
            Ok(metadata) if metadata.file_type().is_symlink() => {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!("refusing symlink component in evidence directory {}", path.display()),
                ));
            }
            Ok(metadata) if !metadata.file_type().is_dir() => {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!("non-directory component in evidence directory {}", path.display()),
                ));
            }
            Ok(_) => {}
            Err(error) if error.kind() == io::ErrorKind::NotFound => fs::create_dir(&current)?,
            Err(error) => return Err(error),
        }
    }
    Ok(())
}

#[cfg(unix)]
fn directory_is_root_owned_nonwritable(directory_fd: std::os::fd::RawFd) -> io::Result<bool> {
    let mut stat = std::mem::MaybeUninit::<libc::stat>::uninit();
    let result = unsafe { libc::fstat(directory_fd, stat.as_mut_ptr()) };
    if result != 0 {
        return Err(io::Error::last_os_error());
    }
    let stat = unsafe { stat.assume_init() };
    Ok(stat.st_uid == 0 && stat.st_mode & 0o022 == 0)
}

#[cfg(unix)]
fn validate_replaceable_leaf(
    directory_fd: std::os::fd::RawFd,
    destination: &CString,
    display_path: &Path,
) -> io::Result<()> {
    let mut stat = std::mem::MaybeUninit::<libc::stat>::uninit();
    let result = unsafe {
        libc::fstatat(
            directory_fd,
            destination.as_ptr(),
            stat.as_mut_ptr(),
            libc::AT_SYMLINK_NOFOLLOW,
        )
    };
    if result != 0 {
        let error = io::Error::last_os_error();
        if error.kind() == io::ErrorKind::NotFound {
            return Ok(());
        }
        return Err(error);
    }
    let stat = unsafe { stat.assume_init() };
    let kind = stat.st_mode & libc::S_IFMT;
    if kind == libc::S_IFLNK {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!("refusing to replace symlink output {}", display_path.display()),
        ));
    }
    if kind != libc::S_IFREG {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!("refusing to replace non-file output {}", display_path.display()),
        ));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn atomically_replaces_regular_output() {
        let root = tempfile::tempdir().expect("atomic output fixture");
        let output = root.path().join("report.json");
        atomic_write_private(&output, b"one").expect("first write");
        #[cfg(unix)]
        atomic_write_private(&output, b"two").expect("atomic replacement");
        #[cfg(unix)]
        assert_eq!(fs::read(&output).expect("read output"), b"two");
    }

    #[cfg(unix)]
    #[test]
    fn rejects_leaf_symlink_without_clobbering_target() {
        use std::os::unix::fs::symlink;

        let root = tempfile::tempdir().expect("symlink output fixture");
        let victim = root.path().join("victim");
        let output = root.path().join("report.json");
        fs::write(&victim, b"safe").expect("write victim");
        symlink(&victim, &output).expect("link output");
        let error = atomic_write_private(&output, b"clobber").expect_err("symlink must fail");
        assert_eq!(error.kind(), io::ErrorKind::InvalidInput);
        assert_eq!(fs::read(&victim).expect("read victim"), b"safe");
    }

    #[cfg(unix)]
    #[test]
    fn rejects_symlinked_parent_without_publishing_through_it() {
        use std::os::unix::fs::symlink;

        let root = tempfile::tempdir().expect("symlink parent fixture");
        let victim_directory = root.path().join("victim");
        let linked_directory = root.path().join("linked");
        fs::create_dir(&victim_directory).expect("create victim directory");
        symlink(&victim_directory, &linked_directory).expect("link output parent");
        let output = linked_directory.join("report.json");
        atomic_write_private(&output, b"clobber").expect_err("symlinked parent must fail");
        assert!(!victim_directory.join("report.json").exists());
    }

    #[cfg(unix)]
    #[test]
    fn does_not_create_missing_directories_through_a_parent_symlink() {
        use std::os::unix::fs::symlink;

        let root = tempfile::tempdir().expect("symlink parent creation fixture");
        let victim_directory = root.path().join("victim");
        let linked_directory = root.path().join("linked");
        fs::create_dir(&victim_directory).expect("create victim directory");
        symlink(&victim_directory, &linked_directory).expect("link output parent");

        let output = linked_directory.join("new/nested/report.json");
        atomic_write_private(&output, b"clobber")
            .expect_err("directory creation through a symlink must fail");
        assert!(!victim_directory.join("new").exists());
    }
}
