//! Fixed deny-default restriction for the compiler's proc-macro worker (D21).
//!
//! The worker is the compiler's own executable in its worker role. It calls this
//! before it opens a proc-macro dylib, so the dylib's load-time initializers and
//! every macro it exports run under the policy. This is containment, not
//! authority: it authenticates no dylib and bounds no resource.

use std::ffi::CString;
use std::io;
use std::os::unix::ffi::OsStrExt;
use std::os::unix::fs::MetadataExt;
use std::path::Path;

/// Restrict the current process to the proc-macro worker policy.
///
/// Granted: reading and mapping files (a macro reads its own dylib, the runtime
/// it links, and source or data files it expands from), writing under
/// `private_tmp` only, `sysctl` reads, and signalling itself. Everything else is
/// denied by default: file writes anywhere else, network, creating a child
/// process, executing another image, and Mach or POSIX IPC lookups.
///
/// `private_tmp` must be an existing canonical directory owned by this user with
/// mode 0700. Its path reaches the policy as a parameter, never as policy text.
///
/// Descriptors that are already open stay usable; the caller closes the ones the
/// worker must not hold before calling this. Installation is irreversible, and a
/// failure is terminal: the caller must exit rather than load a macro.
pub fn restrict_current_to_macro_worker(private_tmp: &Path) -> io::Result<()> {
    let invalid = |message: &'static str| io::Error::new(io::ErrorKind::InvalidInput, message);
    if !private_tmp.is_absolute() {
        return Err(invalid("macro worker temporary directory must be absolute"));
    }
    if std::fs::canonicalize(private_tmp)? != private_tmp {
        return Err(invalid("macro worker temporary directory must be canonical"));
    }
    let metadata = std::fs::symlink_metadata(private_tmp)?;
    if !metadata.is_dir() {
        return Err(invalid("macro worker temporary directory must be a directory"));
    }
    // SAFETY: query only the current process's effective user.
    if metadata.uid() != unsafe { libc::geteuid() } || metadata.mode() & 0o777 != 0o700 {
        return Err(invalid("macro worker temporary directory must be private to this user"));
    }
    let directory = CString::new(private_tmp.as_os_str().as_bytes())
        .map_err(|_| invalid("macro worker temporary directory contains NUL"))?;
    super::seal::install_macro_worker_profile(&directory)?;
    if !super::fork_denied(std::process::id())? {
        return Err(io::Error::other("macro worker restriction observation unavailable"));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::os::unix::fs::{DirBuilderExt, PermissionsExt};

    use super::*;

    fn scratch(name: &str) -> std::path::PathBuf {
        let root = std::env::temp_dir().canonicalize().unwrap().join(".ubd");
        std::fs::create_dir_all(&root).unwrap();
        let path = root.join(format!("macro-worker-{name}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&path);
        std::fs::DirBuilder::new().mode(0o700).create(&path).unwrap();
        path
    }

    #[test]
    fn shared_relative_or_aliased_directories_refuse_before_restriction() {
        let directory = scratch("refusals");
        std::fs::set_permissions(&directory, std::fs::Permissions::from_mode(0o755)).unwrap();
        assert_eq!(
            restrict_current_to_macro_worker(&directory).unwrap_err().to_string(),
            "macro worker temporary directory must be private to this user"
        );
        std::fs::set_permissions(&directory, std::fs::Permissions::from_mode(0o700)).unwrap();
        let alias = directory.with_extension("alias");
        let _ = std::fs::remove_file(&alias);
        std::os::unix::fs::symlink(&directory, &alias).unwrap();
        assert_eq!(
            restrict_current_to_macro_worker(&alias).unwrap_err().to_string(),
            "macro worker temporary directory must be canonical"
        );
        assert_eq!(
            restrict_current_to_macro_worker(Path::new("relative")).unwrap_err().to_string(),
            "macro worker temporary directory must be absolute"
        );
        let file = directory.join("file");
        std::fs::write(&file, b"x").unwrap();
        assert_eq!(
            restrict_current_to_macro_worker(&file).unwrap_err().to_string(),
            "macro worker temporary directory must be a directory"
        );
        // None of the refusals above installed a policy on this test process.
        assert!(!crate::fork_denied(std::process::id()).unwrap());
        std::fs::remove_file(alias).unwrap();
        std::fs::remove_dir_all(directory).unwrap();
    }

    /// The restricted role, run only in the child `policy_holds_in_an_owned_child`
    /// starts. Exit 0 means every probe had the required outcome.
    #[test]
    fn restricted_child_payload() {
        let Some(directory) = std::env::var_os("TRUST_MACRO_WORKER_POLICY_PAYLOAD") else {
            return;
        };
        let directory = std::path::PathBuf::from(directory);
        let outside = directory.with_extension("outside");
        std::fs::write(&outside, b"before").unwrap();
        restrict_current_to_macro_worker(&directory).unwrap();
        let denied = |error: io::Error| {
            assert!(
                matches!(error.raw_os_error(), Some(libc::EPERM | libc::EACCES)),
                "expected policy denial, got {error}"
            );
        };
        // Granted: reads anywhere, writes under the private directory.
        assert!(!std::fs::read("/etc/hosts").unwrap().is_empty());
        assert_eq!(std::fs::read(&outside).unwrap(), b"before");
        std::fs::write(directory.join("inside"), b"granted").unwrap();
        std::fs::create_dir(directory.join("nested")).unwrap();
        std::fs::write(directory.join("nested/file"), b"granted").unwrap();
        // Denied: any write outside it, including to a file that already exists.
        denied(std::fs::write(&outside, b"after").unwrap_err());
        denied(std::fs::write(directory.with_extension("created"), b"x").unwrap_err());
        denied(std::fs::remove_file(&outside).unwrap_err());
        denied(std::net::TcpStream::connect("127.0.0.1:9").unwrap_err());
        // SAFETY: an unexpectedly permitted child only calls _exit; it is reaped.
        let child = unsafe { libc::fork() };
        if child == 0 {
            unsafe { libc::_exit(99) };
        }
        assert!(child < 0, "macro worker policy allowed fork");
        denied(io::Error::last_os_error());
        let arguments = [c"true".as_ptr(), std::ptr::null()];
        // SAFETY: static argv. An unexpected exec replaces this owned child with
        // `true`, whose parent then finds none of the files this payload writes.
        assert_eq!(unsafe { libc::execv(c"/usr/bin/true".as_ptr(), arguments.as_ptr()) }, -1);
        denied(io::Error::last_os_error());
        std::process::exit(0);
    }

    #[test]
    fn policy_holds_in_an_owned_child() {
        let directory = scratch("policy");
        let name =
            concat!(module_path!(), "::restricted_child_payload").split_once("::").unwrap().1;
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .args(["--exact", name, "--nocapture", "--test-threads=1"])
            .env("TRUST_MACRO_WORKER_POLICY_PAYLOAD", &directory)
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "restricted child failed: {}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        // The parent sees what the child could and could not change.
        assert_eq!(std::fs::read(directory.join("inside")).unwrap(), b"granted");
        assert_eq!(std::fs::read(directory.join("nested/file")).unwrap(), b"granted");
        assert_eq!(std::fs::read(directory.with_extension("outside")).unwrap(), b"before");
        assert!(!directory.with_extension("created").exists());
        std::fs::remove_file(directory.with_extension("outside")).unwrap();
        std::fs::remove_dir_all(directory).unwrap();
    }
}
