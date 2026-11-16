//! Fixed restriction for a trusted Darwin entry, before native constructors.
//! This is not a worker launcher, immutable-image receipt or macro admission.

use std::ffi::{CStr, CString};
use std::fs::File;
use std::io;
use std::os::fd::AsRawFd;

/// Keeps the admitted descriptor alive for a subsequent native loader call.
/// Neither its existence nor successful loading authenticates native code.
pub struct RestrictedNativeImage {
    _file: File,
    loader_path: CString,
}

impl RestrictedNativeImage {
    /// A descriptor path, never the caller's pathname. The linked file must
    /// remain on its read-only filesystem while the native loader uses it.
    pub fn loader_path(&self) -> &CStr {
        &self.loader_path
    }
}

/// Restrict the current process to reading/mapping this one read-only file.
/// No filesystem writes, network, child creation or subsequent exec is granted.
///
/// The trusted caller must supply the separately authenticated native image,
/// preserve its read-only mount and runtime closure, close ambient descriptors,
/// establish resource limits, and retain outside lifecycle ownership. Existing
/// open descriptors remain capabilities. This function establishes none of
/// those obligations and returns no readiness or proof authority.
///
/// Call only in the trusted worker entry before untrusted code/constructors and
/// before creating threads. Any error after installation is terminal: the
/// restriction cannot be rolled back and must not trigger a weaker fallback.
pub fn restrict_current_to_readonly_image(file: File) -> io::Result<RestrictedNativeImage> {
    let metadata = file.metadata()?;
    if !metadata.is_file() {
        return Err(invalid("native image must be a regular file"));
    }
    let fd = file.as_raw_fd();
    // SAFETY: the owned descriptor stays live throughout admission and loading.
    let flags = unsafe { libc::fcntl(fd, libc::F_GETFL) };
    if flags < 0 {
        return Err(io::Error::last_os_error());
    }
    if flags & libc::O_ACCMODE != libc::O_RDONLY {
        return Err(invalid("native image descriptor must be read-only"));
    }
    let mut filesystem = std::mem::MaybeUninit::<libc::statfs>::uninit();
    // SAFETY: writable native storage and a live descriptor; success initializes it.
    if unsafe { libc::fstatfs(fd, filesystem.as_mut_ptr()) } != 0 {
        return Err(io::Error::last_os_error());
    }
    if unsafe { filesystem.assume_init() }.f_flags & libc::MNT_RDONLY as u32 == 0 {
        return Err(invalid("native image must reside on a read-only filesystem"));
    }
    let mut path = [0_u8; libc::PATH_MAX as usize];
    // SAFETY: F_GETPATH writes at most PATH_MAX bytes to this complete buffer.
    if unsafe { libc::fcntl(fd, libc::F_GETPATH, path.as_mut_ptr()) } != 0 {
        return Err(io::Error::last_os_error());
    }
    let path = CStr::from_bytes_until_nul(&path)
        .map_err(|_| invalid("native image path is not terminated"))?;
    let bytes = path.to_bytes();
    if bytes.first() != Some(&b'/') {
        return Err(invalid("native image path must be absolute"));
    }
    let loader_path = CString::new(format!("/dev/fd/{fd}"))
        .map_err(|_| invalid("native descriptor path contains NUL"))?;
    // dyld checks both its /dev/fd alias and the descriptor's resolved vnode
    // path. Grant only these two names, never the whole descriptor directory.
    super::seal::install_image_profile(path, &loader_path)?;
    if !super::fork_denied(std::process::id())? {
        return Err(io::Error::other("native image restriction observation unavailable"));
    }
    Ok(RestrictedNativeImage { _file: file, loader_path })
}

fn invalid(message: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidInput, message)
}

#[cfg(test)]
mod tests {
    use std::io::Write;

    use super::*;

    #[test]
    fn ordinary_writable_filesystem_refuses_before_restriction() {
        let root = std::env::temp_dir().join(".ubd");
        std::fs::create_dir_all(&root).unwrap();
        let path = root.join(format!("native-policy-{}.txt", std::process::id()));
        let mut file =
            std::fs::OpenOptions::new().create_new(true).write(true).open(&path).unwrap();
        file.write_all(b"input").unwrap();
        assert!(matches!(
            restrict_current_to_readonly_image(file),
            Err(e) if e.to_string() == "native image descriptor must be read-only"
        ));
        assert!(matches!(
            restrict_current_to_readonly_image(File::open(&path).unwrap()),
            Err(e) if e.to_string() == "native image must reside on a read-only filesystem"
        ));
        std::fs::remove_file(path).unwrap();
    }

    #[test]
    fn non_regular_input_refuses_before_restriction() {
        assert!(matches!(
            restrict_current_to_readonly_image(File::open("/dev/null").unwrap()),
            Err(e) if e.to_string() == "native image must be a regular file"
        ));
    }
}
