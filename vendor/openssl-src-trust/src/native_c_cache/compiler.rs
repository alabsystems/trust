//! Close the compiler-image/runtime part missing from Clang's native action key.

use super::runtime::RuntimeSnapshot;
use sha2::{Digest, Sha256};
use std::ffi::OsStr;
use std::fs::{self, File, OpenOptions};
use std::io::Read;
use std::os::fd::AsRawFd;
use std::os::unix::fs::{MetadataExt, OpenOptionsExt};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

extern "C" {
    fn _dyld_shared_cache_contains_path(path: *const libc::c_char) -> bool;
}

pub(super) struct Compiler {
    pub path: PathBuf,
    file: File,
    stamp: fs::Metadata,
    runtime: RuntimeSnapshot,
    loader: (PathBuf, File, fs::Metadata),
    pub digest: [u8; 32],
}

impl Compiler {
    pub fn capture(candidate: &Path, recipe: &Command) -> Result<Self, String> {
        // Injection, alternate shared regions and compiler-specific environment
        // rewriting are outside this deliberately narrow native profile.
        for (key, _) in std::env::vars_os() {
            let key = key.to_string_lossy();
            if (key.starts_with("DYLD_") && key != "DYLD_FALLBACK_LIBRARY_PATH")
                || key.starts_with("CCC_")
                || key == "CLANG_CONFIG_FILE_SYSTEM_DIR"
                || key == "CLANG_CONFIG_FILE_USER_DIR"
                || key == "CLANG_RESOURCE_DIR"
            {
                return Err(format!("unbound compiler loader/config input: {key}"));
            }
        }
        let mut selector = Command::new("/usr/bin/xcrun");
        selector.args(["--find", "clang"]);
        for (key, value) in recipe.get_envs() {
            match value {
                Some(value) => {
                    selector.env(key, value);
                }
                None => {
                    selector.env_remove(key);
                }
            }
        }
        let selected = bounded_selection(selector, false)?;
        let selected = PathBuf::from(
            std::str::from_utf8(&selected)
                .map_err(|e| e.to_string())?
                .trim(),
        )
        .canonicalize()
        .map_err(|e| e.to_string())?;
        if selected != Path::new("/Library/Developer/CommandLineTools/usr/bin/clang") {
            return Err("unqualified-native-compiler-location".into());
        }
        // /usr/bin/cc is the platform dispatcher, not the compiler image. The
        // admitted recipe replaces it with the actual selected image below.
        let path = recipe
            .get_envs()
            .find_map(|(key, value)| (key == "PATH").then_some(value))
            .map(|value| value.map(OsStr::to_owned).unwrap_or_default())
            .unwrap_or_else(|| std::env::var_os("PATH").unwrap_or_default());
        let requested = resolve_candidate(candidate, &path)?;
        if requested != Path::new("/usr/bin/cc")
            && requested != Path::new("/usr/bin/clang")
            && requested != selected
        {
            return Err("custom compiler is outside the native C-cache profile".into());
        }
        if selected.to_str().is_none()
            || !selected
                .as_os_str()
                .as_encoded_bytes()
                .iter()
                .all(|b| b.is_ascii_alphanumeric() || matches!(b, b'/' | b'.' | b'_' | b'-'))
        {
            return Err("selected compiler needs unsupported Configure path quoting".into());
        }
        // Preserve the selected recipe's default-config behavior. Compare the
        // actual requested driver plan with a closed selected-image plan,
        // then disable future automatic config reads in that admitted recipe.
        let mut original = Command::new(&requested);
        let mut closed = Command::new(&selected);
        for child in [&mut original, &mut closed] {
            child.args([
                "-###",
                "--target=arm64-apple-macosx",
                "-x",
                "c",
                "-c",
                "/dev/null",
                "-o",
                "/dev/null",
            ]);
            for (key, value) in recipe.get_envs() {
                match value {
                    Some(value) => {
                        child.env(key, value);
                    }
                    None => {
                        child.env_remove(key);
                    }
                }
            }
        }
        closed.arg("--no-default-config");
        let original = bounded_selection(original, true)?;
        let closed = bounded_selection(closed, true)?;
        let original = std::str::from_utf8(&original).map_err(|e| e.to_string())?;
        let closed = std::str::from_utf8(&closed).map_err(|e| e.to_string())?;
        let cc1 = |text: &str| text.find(" \"-cc1\"").map(|at| text[at..].to_owned());
        if original.contains("Configuration file:")
            || closed.contains("Configuration file:")
            || cc1(original).is_none()
            || cc1(original) != cc1(closed)
        {
            return Err("native compiler default configuration is not closed".into());
        }
        let stamp = fs::symlink_metadata(&selected).map_err(|e| e.to_string())?;
        if !stamp.is_file() || stamp.len() > 256 * 1024 * 1024 {
            return Err("native compiler is not a bounded regular image".into());
        }
        let mut file = OpenOptions::new()
            .read(true)
            .custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK | libc::O_CLOEXEC)
            .open(&selected)
            .map_err(|e| e.to_string())?;
        if !same(&stamp, &file.metadata().map_err(|e| e.to_string())?) {
            return Err("compiler image changed before opening".into());
        }
        let mut bytes = Vec::with_capacity(stamp.len() as usize);
        (&mut file)
            .take(stamp.len() + 1)
            .read_to_end(&mut bytes)
            .map_err(|e| e.to_string())?;
        if bytes.len() as u64 != stamp.len() {
            return Err("compiler image changed while reading".into());
        }
        check_imports(&bytes)?;
        let image_digest = Sha256::digest(&bytes);
        let image_hex: String = image_digest.iter().map(|b| format!("{b:02x}")).collect();
        // Initial explicitly qualified compiler profile. Unknown versions and
        // custom images compile normally; a link-import list alone cannot
        // prove an arbitrary compiler has no implicit plugin/dlopen inputs.
        if image_hex != "fc5e3cbba6ad54059295cad716aacb05ace8235f5f7a6031f1d8c15d24bd6d66" {
            return Err("unqualified-native-compiler-image".into());
        }
        let loader_path = Path::new("/usr/lib/dyld")
            .canonicalize()
            .map_err(|e| e.to_string())?;
        let loader_stamp = fs::symlink_metadata(&loader_path).map_err(|e| e.to_string())?;
        if !loader_stamp.is_file() || loader_stamp.len() > 64 * 1024 * 1024 {
            return Err("unbounded native system loader image".into());
        }
        let mut loader_file = OpenOptions::new()
            .read(true)
            .custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK | libc::O_CLOEXEC)
            .open(&loader_path)
            .map_err(|e| e.to_string())?;
        if !same(
            &loader_stamp,
            &loader_file.metadata().map_err(|e| e.to_string())?,
        ) {
            return Err("native system loader changed before opening".into());
        }
        let mut loader_bytes = Vec::with_capacity(loader_stamp.len() as usize);
        (&mut loader_file)
            .take(loader_stamp.len() + 1)
            .read_to_end(&mut loader_bytes)
            .map_err(|e| e.to_string())?;
        if loader_bytes.len() as u64 != loader_stamp.len() {
            return Err("native system loader changed during reading".into());
        }
        let runtime = RuntimeSnapshot::capture()?;
        let mut hash = Sha256::new();
        hash.update(b"trust.openssl-c-compiler.v2\0");
        hash.update((selected.as_os_str().len() as u64).to_le_bytes());
        hash.update(selected.as_os_str().as_encoded_bytes());
        hash.update(image_digest);
        hash.update(Sha256::digest(loader_bytes));
        hash.update(runtime.digest);
        let compiler = Self {
            path: selected,
            file,
            stamp,
            runtime,
            loader: (loader_path, loader_file, loader_stamp),
            digest: hash.finalize().into(),
        };
        compiler.check_current()?;
        Ok(compiler)
    }

    pub fn check_current(&self) -> Result<(), String> {
        let (path, file, stamp) = &self.loader;
        if Path::new("/usr/lib/dyld")
            .canonicalize()
            .map_err(|e| e.to_string())?
            != *path
            || !same(stamp, &file.metadata().map_err(|e| e.to_string())?)
            || !same(
                stamp,
                &fs::symlink_metadata(path).map_err(|e| e.to_string())?,
            )
        {
            return Err("native system loader image changed".into());
        }
        if !same(
            &self.stamp,
            &self.file.metadata().map_err(|e| e.to_string())?,
        ) || !same(
            &self.stamp,
            &fs::symlink_metadata(&self.path).map_err(|e| e.to_string())?,
        ) {
            return Err("native compiler image changed".into());
        }
        self.runtime.check_current()
    }
}

pub(super) fn resolve_candidate(candidate: &Path, path: &OsStr) -> Result<PathBuf, String> {
    if candidate.components().count() > 1 || candidate.is_absolute() {
        return candidate.canonicalize().map_err(|e| e.to_string());
    }
    for directory in std::env::split_paths(path) {
        let candidate = directory.join(candidate);
        let c = std::ffi::CString::new(candidate.as_os_str().as_encoded_bytes())
            .map_err(|e| e.to_string())?;
        // Query actual executable selection. PATH text alone is not compiler
        // identity and a custom earlier executable must never be substituted.
        if candidate.is_file() && unsafe { libc::access(c.as_ptr(), libc::X_OK) } == 0 {
            return candidate.canonicalize().map_err(|e| e.to_string());
        }
    }
    Err("requested native compiler is absent from the effective PATH".into())
}

pub(super) fn bounded_selection(mut command: Command, diagnostic: bool) -> Result<Vec<u8>, String> {
    if diagnostic {
        command.stderr(Stdio::piped()).stdout(Stdio::null());
    } else {
        command.stdout(Stdio::piped()).stderr(Stdio::null());
    }
    let mut child = command.spawn().map_err(|e| e.to_string())?;
    let result = (|| {
        let mut stdout: Box<dyn ReadFd> = if diagnostic {
            Box::new(
                child
                    .stderr
                    .take()
                    .ok_or("compiler selector has no diagnostic")?,
            )
        } else {
            Box::new(
                child
                    .stdout
                    .take()
                    .ok_or("compiler selector has no output")?,
            )
        };
        let fd = stdout.as_raw_fd();
        let flags = unsafe { libc::fcntl(fd, libc::F_GETFL) };
        if flags < 0 || unsafe { libc::fcntl(fd, libc::F_SETFL, flags | libc::O_NONBLOCK) } < 0 {
            return Err(std::io::Error::last_os_error().to_string());
        }
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(5);
        let mut output = Vec::new();
        let mut eof = false;
        loop {
            let mut buffer = [0_u8; 1024];
            loop {
                match stdout.read(&mut buffer) {
                    Ok(0) => {
                        eof = true;
                        break;
                    }
                    Ok(n) => {
                        if output.len() + n > 16 * 1024 {
                            return Err("compiler selection output exceeds16KiB".into());
                        }
                        output.extend_from_slice(&buffer[..n]);
                    }
                    Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => break,
                    Err(e) if e.kind() == std::io::ErrorKind::Interrupted => continue,
                    Err(e) => return Err(e.to_string()),
                }
            }
            if let Some(status) = child.try_wait().map_err(|e| e.to_string())? {
                if !status.success() {
                    return Err("native compiler selection failed".into());
                }
                if eof {
                    return Ok(output);
                }
            }
            if std::time::Instant::now() >= deadline {
                return Err("native compiler selection exceeded deadline".into());
            }
            std::thread::sleep(std::time::Duration::from_millis(5));
        }
    })();
    if result.is_err() {
        let _ = child.kill();
        let _ = child.wait();
    }
    result
}

trait ReadFd: Read + AsRawFd {}
impl<T: Read + AsRawFd> ReadFd for T {}

fn same(a: &fs::Metadata, b: &fs::Metadata) -> bool {
    a.dev() == b.dev()
        && a.ino() == b.ino()
        && a.mode() == b.mode()
        && a.len() == b.len()
        && a.mtime() == b.mtime()
        && a.mtime_nsec() == b.mtime_nsec()
        && a.ctime() == b.ctime()
        && a.ctime_nsec() == b.ctime_nsec()
}

fn word(bytes: &[u8], at: usize, big: bool) -> Result<u32, String> {
    let value = bytes
        .get(at..at.checked_add(4).ok_or("Mach-O offset overflow")?)
        .ok_or("truncated Mach-O image")?
        .try_into()
        .unwrap();
    Ok(if big {
        u32::from_be_bytes(value)
    } else {
        u32::from_le_bytes(value)
    })
}

fn check_imports(image: &[u8]) -> Result<(), String> {
    let mut image = image;
    if word(image, 0, true)? == 0xcafebabe {
        let count = word(image, 4, true)? as usize;
        if count == 0 || count > 16 {
            return Err("unsupported compiler fat header".into());
        }
        let mut selected = None;
        for index in 0..count {
            let at = 8 + index * 20;
            if word(image, at, true)? != 0x0100000c {
                continue;
            }
            let start = word(image, at + 8, true)? as usize;
            let length = word(image, at + 12, true)? as usize;
            let slice = image
                .get(start..start.checked_add(length).ok_or("Mach-O slice overflow")?)
                .ok_or("truncated compiler slice")?;
            if selected.replace(slice).is_some() {
                return Err("ambiguous compiler architecture".into());
            }
        }
        image = selected.ok_or("compiler has no native ARM64 image")?;
    }
    if word(image, 0, false)? != 0xfeedfacf || word(image, 4, false)? != 0x0100000c {
        return Err("unsupported native compiler image format".into());
    }
    let count = word(image, 16, false)? as usize;
    let length = word(image, 20, false)? as usize;
    let end = 32usize
        .checked_add(length)
        .ok_or("Mach-O commands overflow")?;
    if end > image.len() || count > 8192 {
        return Err("invalid compiler command bounds".into());
    }
    let mut at = 32;
    let mut imports = 0;
    for _ in 0..count {
        let command = word(image, at, false)?;
        let size = word(image, at + 4, false)? as usize;
        let next = at.checked_add(size).ok_or("Mach-O command overflow")?;
        if size < 8 || next > end {
            return Err("invalid compiler command size".into());
        }
        if matches!(command, 0x27 | 0x10) {
            return Err("compiler has unbound loader configuration".into());
        }
        // All load/reexport/upward/weak dylibs must be current cached system
        // images. @rpath and external plugin runtimes are not a closed profile.
        if matches!(command, 0xc | 0x80000018 | 0x8000001f | 0x80000023 | 0x20) {
            if size < 24 {
                return Err("truncated compiler dependency".into());
            }
            let offset = word(image, at + 8, false)? as usize;
            if offset < 24 || offset >= size {
                return Err("invalid compiler dependency name".into());
            }
            let raw = &image[at + offset..next];
            let end = raw
                .iter()
                .position(|b| *b == 0)
                .ok_or("unterminated compiler dependency")?;
            let path =
                std::ffi::CStr::from_bytes_with_nul(&raw[..=end]).map_err(|e| e.to_string())?;
            if !path.to_bytes().starts_with(b"/usr/lib/")
                // SAFETY: bounded validated NUL-terminated path; query only.
                || !unsafe { _dyld_shared_cache_contains_path(path.as_ptr()) }
            {
                return Err("compiler imports an unbound native runtime image".into());
            }
            imports += 1;
        }
        at = next;
    }
    if at != end || imports == 0 {
        return Err("incomplete compiler dependency commands".into());
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::os::unix::fs::PermissionsExt;

    #[test]
    fn actual_recipe_path_selection_never_substitutes_a_custom_compiler() {
        let temp = tempfile::tempdir().unwrap();
        let custom = temp.path().join("cc");
        fs::write(&custom, b"#!/bin/sh\nexec /usr/bin/clang \"$@\"\n").unwrap();
        fs::set_permissions(&custom, fs::Permissions::from_mode(0o700)).unwrap();
        let mut recipe = Command::new("/usr/bin/perl");
        recipe.env("PATH", temp.path());
        let reason = Compiler::capture(Path::new("cc"), &recipe).err().unwrap();
        assert!(reason.contains("custom compiler"), "{reason}");
        assert_eq!(
            resolve_candidate(Path::new("cc"), temp.path().as_os_str()).unwrap(),
            custom.canonicalize().unwrap()
        );
    }

    #[test]
    fn compiler_selection_output_is_bounded_before_allocation_or_acceptance() {
        let mut command = Command::new("/usr/bin/yes");
        command.arg("unbounded native selector");
        let reason = bounded_selection(command, false).unwrap_err();
        assert!(reason.contains("exceeds16KiB"), "{reason}");
    }
}
