//! A closed native store is reusable only under this owner and its lease.

use sha2::{Digest, Sha256};
use std::fs::{self, File, OpenOptions};
use std::io::{Read, Seek, SeekFrom, Write};
use std::os::fd::AsRawFd;
use std::os::unix::fs::{DirBuilderExt, MetadataExt, OpenOptionsExt};
use std::os::unix::process::CommandExt;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::Arc;

pub(super) struct Store {
    pub root: PathBuf,
    lease: Arc<File>,
    directory: File,
    stamp: fs::Metadata,
    pub previous: bool,
    pub reset_reason: Option<String>,
}

impl Store {
    pub fn acquire(root: PathBuf) -> Result<Self, String> {
        validate_existing_ancestors(&root)?;
        private_directory(&root)?;
        let directory = OpenOptions::new()
            .read(true)
            .custom_flags(libc::O_NOFOLLOW | libc::O_DIRECTORY | libc::O_CLOEXEC)
            .open(&root)
            .map_err(|e| e.to_string())?;
        let stamp = directory.metadata().map_err(|e| e.to_string())?;
        trust_fs_acl::require_no_acl_grants(&directory).map_err(|e| e.to_string())?;
        let lease_path = root.join("lease");
        let lease = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .mode(0o600)
            .custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK | libc::O_CLOEXEC)
            .open(&lease_path)
            .map_err(|e| e.to_string())?;
        let meta = lease.metadata().map_err(|e| e.to_string())?;
        trust_fs_acl::require_no_acl_grants(&lease).map_err(|e| e.to_string())?;
        if !meta.is_file()
            || meta.uid() != unsafe { libc::geteuid() }
            || meta.mode() & 0o077 != 0
            || meta.nlink() != 1
        {
            return Err("native store lease is redirected or not private".into());
        }
        // Never wait while holding a build scheduler credit. A contended
        // producer preserves the ordinary supported compilation path.
        if unsafe { libc::flock(lease.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) } != 0 {
            return Err(format!(
                "native store lease unavailable: {}",
                std::io::Error::last_os_error()
            ));
        }
        let mut store = Self {
            root,
            lease: Arc::new(lease),
            directory,
            stamp,
            previous: false,
            reset_reason: None,
        };
        store.check_current()?;
        let cas = store.root.join("cas");
        let seal = store.root.join("closed-store.sha256");
        if cas.exists() {
            let expected = read_seal(&seal);
            let actual = digest_tree(&cas);
            if expected.as_ref().ok() == actual.as_ref().ok() && expected.is_ok() {
                store.previous = true;
            } else {
                // Preserve a failed store for diagnosis. The quarantine is
                // never read by the compiler and cannot authorize a hit.
                let suffix = format!(
                    "{}-{}",
                    std::process::id(),
                    std::time::SystemTime::now()
                        .duration_since(std::time::UNIX_EPOCH)
                        .map_err(|e| e.to_string())?
                        .as_nanos()
                );
                fs::rename(&cas, store.root.join(format!("refused-{suffix}")))
                    .map_err(|e| e.to_string())?;
                if seal.exists() {
                    fs::rename(&seal, store.root.join(format!("refused-{suffix}.sha256")))
                        .map_err(|e| e.to_string())?;
                }
                store.reset_reason = Some("missing-or-changed-closed-native-store".into());
            }
        } else if seal.exists() {
            store.reset_reason = Some("missing-native-store".into());
        }
        // Mark the store open before any process can modify it. A killed
        // producer cannot leave its earlier seal authorizing partial writes.
        match fs::remove_file(&seal) {
            Ok(()) => {}
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
            Err(e) => return Err(e.to_string()),
        }
        if !cas.exists() {
            private_directory(&cas)?;
        }
        store.check_current()?;
        Ok(store)
    }

    pub fn check_current(&self) -> Result<(), String> {
        validate_existing_ancestors(&self.root)?;
        trust_fs_acl::require_no_acl_grants(&self.directory)
            .map_err(|e| e.to_string())?;
        trust_fs_acl::require_no_acl_grants(&self.lease).map_err(|e| e.to_string())?;
        let path = fs::symlink_metadata(&self.root).map_err(|e| e.to_string())?;
        let fd = self.directory.metadata().map_err(|e| e.to_string())?;
        if !path.is_dir()
            || path.dev() != self.stamp.dev()
            || path.ino() != self.stamp.ino()
            || fd.dev() != self.stamp.dev()
            || fd.ino() != self.stamp.ino()
            || path.uid() != unsafe { libc::geteuid() }
            || path.mode() & 0o077 != 0
        {
            return Err("native store namespace changed".into());
        }
        let lease = fs::symlink_metadata(self.root.join("lease")).map_err(|e| e.to_string())?;
        let held = self.lease.metadata().map_err(|e| e.to_string())?;
        if lease.dev() != held.dev() || lease.ino() != held.ino() || !lease.is_file() {
            return Err("native store lease was substituted".into());
        }
        Ok(())
    }

    pub fn configure(&self, command: &mut Command) -> Result<(), String> {
        self.check_current()?;
        let lease = Arc::clone(&self.lease);
        // SAFETY: retain this exact lease through the actual make/clang
        // process tree. Only async-signal-safe fcntl runs after fork. Drop
        // only closes: LOCK_UN would wrongly release live descendants' lock.
        unsafe {
            command.pre_exec(move || {
                let flags = libc::fcntl(lease.as_raw_fd(), libc::F_GETFD);
                if flags < 0
                    || libc::fcntl(lease.as_raw_fd(), libc::F_SETFD, flags & !libc::FD_CLOEXEC) < 0
                {
                    return Err(std::io::Error::last_os_error());
                }
                Ok(())
            });
        }
        Ok(())
    }

    pub fn finish(&self) -> Result<String, String> {
        self.check_current()?;
        let digest = digest_tree(&self.root.join("cas"))?;
        let temporary = self.root.join("closed-store.pending");
        // The exclusive lease owns publication. Never follow a preexisting
        // pending locator left by an interrupted producer.
        if temporary.exists() {
            fs::remove_file(&temporary).map_err(|e| e.to_string())?;
        }
        let mut file = OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o600)
            .custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC)
            .open(&temporary)
            .map_err(|e| e.to_string())?;
        writeln!(file, "{digest}").map_err(|e| e.to_string())?;
        file.sync_all().map_err(|e| e.to_string())?;
        self.check_current()?;
        fs::rename(temporary, self.root.join("closed-store.sha256")).map_err(|e| e.to_string())?;
        self.directory.sync_all().map_err(|e| e.to_string())?;
        Ok(digest)
    }
}

fn validate_existing_ancestors(path: &Path) -> Result<(), String> {
    if !path.is_absolute() || path.components().count() > 64 || path.as_os_str().len() > 4096 {
        return Err("native store ancestry exceeds canonical path bounds".into());
    }
    let ancestors = path.ancestors().collect::<Vec<_>>();
    for path in ancestors.into_iter().rev() {
        let file = match OpenOptions::new()
            .read(true)
            .custom_flags(libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC)
            .open(path)
        {
            Ok(file) => file,
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => break,
            Err(e) => return Err(e.to_string()),
        };
        let meta = file.metadata().map_err(|e| e.to_string())?;
        if !meta.is_dir()
            || meta.mode() & 0o022 != 0
            || (meta.uid() != 0 && meta.uid() != unsafe { libc::geteuid() })
        {
            return Err("native cache ancestry permits another writer".into());
        }
        trust_fs_acl::require_no_acl_grants(&file).map_err(|e| e.to_string())?;
    }
    Ok(())
}

fn read_seal(path: &Path) -> Result<String, String> {
    let meta = fs::symlink_metadata(path).map_err(|e| e.to_string())?;
    if !meta.is_file() || meta.len() != 65 {
        return Err("invalid closed native store seal".into());
    }
    let mut file = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK)
        .open(path)
        .map_err(|e| e.to_string())?;
    let mut bytes = Vec::new();
    let opened = file.metadata().map_err(|e| e.to_string())?;
    if !same(&meta, &opened) {
        return Err("closed native store seal substituted".into());
    }
    (&mut file)
        .take(66)
        .read_to_end(&mut bytes)
        .map_err(|e| e.to_string())?;
    if bytes.len() != 65 || bytes[64] != b'\n' || !bytes[..64].iter().all(u8::is_ascii_hexdigit) {
        return Err("invalid closed native store digest".into());
    }
    if !same(&meta, &file.metadata().map_err(|e| e.to_string())?)
        || !same(
            &meta,
            &fs::symlink_metadata(path).map_err(|e| e.to_string())?,
        )
    {
        return Err("closed native store seal changed during validation".into());
    }
    String::from_utf8(bytes[..64].to_vec()).map_err(|e| e.to_string())
}

pub(super) fn private_directory(path: &Path) -> Result<(), String> {
    if !path.try_exists().map_err(|e| e.to_string())? {
        if let Some(parent) = path.parent() {
            private_directory_parent(parent)?;
        }
        match fs::DirBuilder::new().mode(0o700).create(path) {
            Ok(()) => {}
            Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => {}
            Err(e) => return Err(e.to_string()),
        }
    }
    let meta = fs::symlink_metadata(path).map_err(|e| e.to_string())?;
    if !meta.is_dir() || meta.uid() != unsafe { libc::geteuid() } || meta.mode() & 0o077 != 0 {
        return Err("native store directory is not private and owned".into());
    }
    Ok(())
}

fn private_directory_parent(path: &Path) -> Result<(), String> {
    let mut pending = Vec::new();
    let mut current = path;
    loop {
        if current.as_os_str().len() > 4096 || pending.len() >= 64 {
            return Err("native store parent path exceeds its bounded depth/length".into());
        }
        if current.try_exists().map_err(|e| e.to_string())? {
            let meta = fs::symlink_metadata(current).map_err(|e| e.to_string())?;
            if !meta.is_dir() || meta.mode() & 0o022 != 0 {
                return Err("native store parent is redirected or writable by others".into());
            }
            break;
        }
        pending.push(current);
        current = current
            .parent()
            .ok_or("native store parent has no owned ancestor")?;
    }
    for path in pending.into_iter().rev() {
        fs::DirBuilder::new()
            .mode(0o700)
            .create(path)
            .map_err(|e| e.to_string())?;
    }
    Ok(())
}

pub(super) fn digest_tree(root: &Path) -> Result<String, String> {
    let mut hash = Sha256::new();
    hash.update(b"trust.closed-native-cas.v2.sparse\0");
    let mut budget = (0_u64, 0_usize);
    digest_directory(root, root, &mut hash, &mut budget, 0)?;
    Ok(hash.finalize().iter().map(|b| format!("{b:02x}")).collect())
}

fn digest_directory(
    root: &Path,
    path: &Path,
    hash: &mut Sha256,
    budget: &mut (u64, usize),
    depth: usize,
) -> Result<(), String> {
    if depth > 64 {
        return Err("native store directory depth limit exceeded".into());
    }
    let before = fs::symlink_metadata(path).map_err(|e| e.to_string())?;
    if !before.is_dir() {
        return Err("native store directory is redirected".into());
    }
    let mut entries = Vec::new();
    for entry in fs::read_dir(path).map_err(|e| e.to_string())? {
        budget.1 += 1;
        if budget.1 > 100_000 {
            return Err("native store entry limit exceeded".into());
        }
        entries.push(entry.map_err(|e| e.to_string())?);
    }
    entries.sort_by_key(|e| e.file_name());
    for entry in entries {
        let path = entry.path();
        let meta = fs::symlink_metadata(&path).map_err(|e| e.to_string())?;
        let relative = path
            .strip_prefix(root)
            .map_err(|e| e.to_string())?
            .as_os_str()
            .as_encoded_bytes();
        hash.update((relative.len() as u64).to_le_bytes());
        hash.update(relative);
        hash.update(meta.mode().to_le_bytes());
        if meta.is_dir() {
            hash.update(b"directory");
            digest_directory(root, &path, hash, budget, depth + 1)?;
        } else if meta.is_file() {
            budget.0 = budget
                .0
                .checked_add(meta.len())
                .ok_or("native store byte overflow")?;
            if budget.0 > 64 * 1024 * 1024 * 1024 {
                return Err("native store exceeds its 64-GiB checked bound".into());
            }
            let mut file = OpenOptions::new()
                .read(true)
                .custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK | libc::O_CLOEXEC)
                .open(&path)
                .map_err(|e| e.to_string())?;
            if !same(&meta, &file.metadata().map_err(|e| e.to_string())?) {
                return Err("native store leaf substituted".into());
            }
            hash.update(b"file");
            hash.update(meta.len().to_le_bytes());
            digest_file(&mut file, meta.len(), hash)?;
            if !same(&meta, &file.metadata().map_err(|e| e.to_string())?)
                || !same(
                    &meta,
                    &fs::symlink_metadata(&path).map_err(|e| e.to_string())?,
                )
            {
                return Err("native store leaf changed during validation".into());
            }
        } else {
            return Err("native store contains a link or special node".into());
        }
    }
    if !same(
        &before,
        &fs::symlink_metadata(path).map_err(|e| e.to_string())?,
    ) {
        return Err("native store directory changed during validation".into());
    }
    Ok(())
}

// Filesystem-reported holes read as zero by the kernel. Bind their exact
// logical ranges, not stat block counts, and read every byte in every data
// extent. Physical-layout changes conservatively miss. Unsupported filesystems
// retain a complete bounded stream; no output bytes are ignored.
fn digest_file(file: &mut File, length: u64, hash: &mut Sha256) -> Result<(), String> {
    let mut ranges = Vec::new();
    let mut at = 0;
    let mut supported = true;
    while at < length {
        let data = unsafe { libc::lseek(file.as_raw_fd(), at as i64, libc::SEEK_DATA) };
        if data < 0 {
            let e = std::io::Error::last_os_error();
            if e.raw_os_error() == Some(libc::ENXIO) {
                break;
            }
            if matches!(e.raw_os_error(), Some(libc::EINVAL) | Some(libc::ENOTSUP)) {
                supported = false;
                break;
            }
            return Err(e.to_string());
        }
        let hole = unsafe { libc::lseek(file.as_raw_fd(), data, libc::SEEK_HOLE) };
        if hole < 0 {
            return Err(std::io::Error::last_os_error().to_string());
        }
        let (data, hole) = (data as u64, hole as u64);
        if data < at || data >= length || hole <= data || hole > length {
            return Err("invalid native store filesystem extent".into());
        }
        if ranges.len() >= 131_072 {
            return Err("native store extent count exceeds bound".into());
        }
        ranges.push((data, hole));
        at = hole;
    }
    if !supported {
        ranges.clear();
        if length != 0 {
            ranges.push((0, length));
        }
    }
    hash.update(if supported {
        b"kernel-zero-extents".as_slice()
    } else {
        b"complete-stream".as_slice()
    });
    hash.update((ranges.len() as u64).to_le_bytes());
    let mut buffer = [0_u8; 64 * 1024];
    for (start, end) in ranges {
        hash.update(start.to_le_bytes());
        hash.update(end.to_le_bytes());
        file.seek(SeekFrom::Start(start))
            .map_err(|e| e.to_string())?;
        let mut remaining = end - start;
        while remaining > 0 {
            let count = remaining.min(buffer.len() as u64) as usize;
            file.read_exact(&mut buffer[..count])
                .map_err(|e| e.to_string())?;
            hash.update(&buffer[..count]);
            remaining -= count as u64;
        }
    }
    Ok(())
}

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

#[cfg(test)]
mod tests {
    use super::*;
    use std::ffi::OsStr;
    use std::io::{BufRead, BufReader};
    use std::process::Stdio;

    fn tempdir() -> tempfile::TempDir {
        tempfile::Builder::new()
            .tempdir_in(std::env::temp_dir().canonicalize().unwrap())
            .unwrap()
    }

    #[test]
    fn macos_acl_grants_refuse_before_native_cache_admission() {
        let temp = tempdir();
        let root = temp.path().join("store");
        let store = Store::acquire(root.clone()).unwrap();
        drop(store);
        let status = Command::new("/bin/chmod")
            .args(["+a", "everyone allow write"])
            .arg(&root)
            .status()
            .unwrap();
        assert!(status.success());
        let reason = Store::acquire(root).err().unwrap();
        assert!(reason.contains("ACL grants access"), "{reason}");
    }

    fn actual_cached_compile(store: &Store, fixture: &Path) -> (Vec<u8>, String) {
        let output = fixture.join("actual.o");
        let _ = fs::remove_file(&output);
        let mut command = Command::new("/Library/Developer/CommandLineTools/usr/bin/clang");
        command
            .current_dir(fixture)
            .args([
                "--no-default-config",
                "-fdepscan=inline",
                "-Xclang=-fcache-compile-job",
                "-Xclang=-fcas-path",
            ])
            .arg(format!("-Xclang={}", store.root.join("cas").display()))
            .args(["-Rcompile-job-cache", "-c", "actual.c", "-o"])
            .arg(&output);
        store.configure(&mut command).unwrap();
        let remarks = crate::native_c_cache::compiler::bounded_selection(command, true).unwrap();
        (
            fs::read(output).unwrap(),
            String::from_utf8(remarks).unwrap(),
        )
    }

    fn actual_leaf(root: &Path) -> PathBuf {
        let files = fs::read_dir(root.join("cas/v1.1"))
            .unwrap()
            .map(Result::unwrap)
            .map(|entry| entry.path())
            .filter(|path| path.is_file() && path.metadata().unwrap().len() != 0)
            .collect::<Vec<_>>();
        files
            .iter()
            .find(|path| path.extension() == Some(OsStr::new("leaf")))
            .or_else(|| files.first())
            .unwrap()
            .clone()
    }

    #[test]
    fn actual_clang_cached_objects_reject_corruption_missing_and_substitution_before_replay() {
        let temp = tempdir();
        let fixture = temp.path().canonicalize().unwrap();
        let root = fixture.join("store");
        fs::write(
            fixture.join("actual.c"),
            "int checked_native_object(void) { return 179; }\n",
        )
        .unwrap();
        let cold = Store::acquire(root.clone()).unwrap();
        let (expected, remarks) = actual_cached_compile(&cold, &fixture);
        assert!(remarks.contains("cache miss"), "{remarks}");
        cold.finish().unwrap();
        drop(cold);
        let warm = Store::acquire(root.clone()).unwrap();
        assert!(warm.previous);
        let (bytes, remarks) = actual_cached_compile(&warm, &fixture);
        assert!(remarks.contains("cache hit"), "{remarks}");
        assert_eq!(bytes, expected);
        warm.finish().unwrap();
        drop(warm);

        let path = actual_leaf(&root);
        let mut corrupt = OpenOptions::new()
            .read(true)
            .write(true)
            .open(path)
            .unwrap();
        let mut byte = [0];
        corrupt.read_exact(&mut byte).unwrap();
        byte[0] ^= 1;
        corrupt.seek(SeekFrom::Start(0)).unwrap();
        corrupt.write_all(&byte).unwrap();
        drop(corrupt);
        let repaired = Store::acquire(root.clone()).unwrap();
        assert!(!repaired.previous);
        assert!(repaired.reset_reason.is_some());
        let (bytes, remarks) = actual_cached_compile(&repaired, &fixture);
        assert!(
            remarks.contains("cache miss"),
            "corrupt object reached replay: {remarks}"
        );
        assert_eq!(bytes, expected);
        repaired.finish().unwrap();
        drop(repaired);

        fs::remove_file(actual_leaf(&root)).unwrap();
        let missing = Store::acquire(root.clone()).unwrap();
        assert!(!missing.previous);
        let (bytes, remarks) = actual_cached_compile(&missing, &fixture);
        assert!(
            remarks.contains("cache miss"),
            "missing object reached replay: {remarks}"
        );
        assert_eq!(bytes, expected);
        missing.finish().unwrap();
        drop(missing);

        let path = actual_leaf(&root);
        fs::remove_file(&path).unwrap();
        let canary = fixture.join("outside-cache");
        fs::write(&canary, b"untouched canary").unwrap();
        std::os::unix::fs::symlink(&canary, path).unwrap();
        let redirected = Store::acquire(root).unwrap();
        assert!(!redirected.previous);
        let (bytes, remarks) = actual_cached_compile(&redirected, &fixture);
        assert!(
            remarks.contains("cache miss"),
            "substituted object reached replay: {remarks}"
        );
        assert_eq!(bytes, expected);
        assert_eq!(fs::read(canary).unwrap(), b"untouched canary");
        redirected.finish().unwrap();
    }

    #[repr(C)]
    struct VnodeFdInfo {
        flags: u32,
        status: u32,
        offset: i64,
        kind: i32,
        guard: u32,
        vnode: libc::vnode_info,
    }

    fn child_owns_lease(pid: i32, fd: i32, stamp: &fs::Metadata) -> bool {
        let mut info = std::mem::MaybeUninit::<VnodeFdInfo>::uninit();
        let size = std::mem::size_of::<VnodeFdInfo>();
        let read =
            unsafe { libc::proc_pidfdinfo(pid, fd, 1, info.as_mut_ptr().cast(), size as i32) };
        if read != size as i32 {
            return false;
        }
        let stat = unsafe { &info.assume_init_ref().vnode.vi_stat };
        stat.vst_dev as u64 == stamp.dev() && stat.vst_ino == stamp.ino()
    }

    struct NativeFixture {
        child: std::process::Child,
        compiler: i32,
        lease: Arc<File>,
        lease_slot: i32,
        leader_reaped: bool,
    }
    impl Drop for NativeFixture {
        fn drop(&mut self) {
            if !self.leader_reaped {
                // This fixture is the sole waiter. An unreaped leader still
                // reserves its process-group identifier, including on panic.
                unsafe {
                    libc::kill(-(self.child.id() as i32), libc::SIGKILL);
                }
            }
            if self.compiler > 0
                && child_owns_lease(
                    self.compiler,
                    self.lease_slot,
                    &self.lease.metadata().unwrap(),
                )
            {
                unsafe {
                    libc::kill(self.compiler, libc::SIGKILL);
                }
            }
            let _ = self.child.kill();
            let _ = self.child.wait();
        }
    }

    #[test]
    fn actual_make_and_orphaned_clang_keep_the_original_store_lease() {
        let temp = tempdir();
        let root = temp.path().join("store");
        let store = Store::acquire(root.clone()).unwrap();
        let fd = store.lease.as_raw_fd();
        let stamp = store.lease.metadata().unwrap();
        let fifo = temp.path().join("input.c");
        let raw = std::ffi::CString::new(fifo.as_os_str().as_encoded_bytes()).unwrap();
        assert_eq!(unsafe { libc::mkfifo(raw.as_ptr(), 0o600) }, 0);
        fs::write(temp.path().join("Makefile"),
            "all:\n\t@printf '%s' $$$$ > compiler.pid; exec /Library/Developer/CommandLineTools/usr/bin/clang --no-default-config -x c -fsyntax-only input.c\n").unwrap();
        let mut command = Command::new("/usr/bin/make");
        command.current_dir(temp.path()).process_group(0);
        store.configure(&mut command).unwrap();
        let child = command.spawn().unwrap();
        drop(command);
        let mut fixture = NativeFixture {
            child,
            compiler: 0,
            lease: Arc::clone(&store.lease),
            lease_slot: fd,
            leader_reaped: false,
        };
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(10);
        loop {
            if let Ok(pid) = fs::read_to_string(temp.path().join("compiler.pid")) {
                if let Ok(pid) = pid.parse() {
                    let mut path = [0_u8; 4096];
                    let length = unsafe {
                        libc::proc_pidpath(pid, path.as_mut_ptr().cast(), path.len() as u32)
                    };
                    if length > 0 && path[..length as usize].windows(6).any(|s| s == b"/clang") {
                        fixture.compiler = pid;
                        break;
                    }
                }
            }
            assert!(
                std::time::Instant::now() < deadline,
                "real clang did not reach its blocking source input"
            );
            std::thread::sleep(std::time::Duration::from_millis(5));
        }
        assert!(
            child_owns_lease(fixture.compiler, fd, &stamp),
            "actual clang stripped its explicit owned store lease"
        );
        drop(store);
        // Drop the Rust owner's final descriptor too: only actual native
        // descendants retain the lock. The fixture's FD is a duplicate owner
        // only for cleanup identity, so close it before contention checks.
        // Keep the identity through an independently reopened descriptor,
        // which does not share or keep the flock's open-file description.
        let independent = File::open(root.join("lease")).unwrap();
        fixture.lease = Arc::new(independent);
        assert!(Store::acquire(root.clone()).is_err());
        let mut writer = loop {
            match OpenOptions::new()
                .write(true)
                .custom_flags(libc::O_NONBLOCK)
                .open(&fifo)
            {
                Ok(writer) => break writer,
                Err(e) if e.raw_os_error() == Some(libc::ENXIO) => {}
                Err(e) => panic!("actual clang input handshake failed: {e}"),
            }
            assert!(
                std::time::Instant::now() < deadline,
                "actual clang did not open its source FIFO"
            );
            std::thread::sleep(std::time::Duration::from_millis(5));
        };
        fixture.child.kill().unwrap();
        fixture.child.wait().unwrap();
        fixture.leader_reaped = true;
        assert!(
            Store::acquire(root.clone()).is_err(),
            "killing make released a live clang worker's lease"
        );
        writer
            .write_all(b"int actual_native_lease_control;\n")
            .unwrap();
        drop(writer);
        loop {
            if let Ok(done) = Store::acquire(root.clone()) {
                drop(done);
                break;
            }
            assert!(
                std::time::Instant::now() < deadline,
                "actual clang did not release its store lease"
            );
            std::thread::sleep(std::time::Duration::from_millis(5));
        }
        fixture.compiler = 0;
    }

    #[test]
    fn sparse_store_identity_binds_zero_extents_data_and_logical_length() {
        let temp = tempdir();
        let path = temp.path().join("sparse");
        let mut file = File::create(&path).unwrap();
        file.set_len(64 * 1024 * 1024).unwrap();
        file.seek(SeekFrom::Start(4096)).unwrap();
        file.write_all(b"checked data").unwrap();
        drop(file);
        let first = digest_tree(temp.path()).unwrap();
        let mut file = OpenOptions::new().write(true).open(&path).unwrap();
        file.seek(SeekFrom::Start(32 * 1024 * 1024)).unwrap();
        file.write_all(b"changed previous zero extent").unwrap();
        drop(file);
        let changed = digest_tree(temp.path()).unwrap();
        assert_ne!(first, changed);
        OpenOptions::new()
            .write(true)
            .open(&path)
            .unwrap()
            .set_len(4096)
            .unwrap();
        assert_ne!(changed, digest_tree(temp.path()).unwrap());
    }

    #[test]
    fn uncreated_parent_paths_are_bounded_before_recursive_work() {
        let temp = tempdir();
        let mut path = temp.path().to_path_buf();
        for _ in 0..70 {
            path.push("nested");
        }
        assert!(Store::acquire(path).is_err());
    }

    #[test]
    fn complete_store_rejects_changed_missing_and_redirected_outputs() {
        let temp = tempdir();
        let root = temp.path().join("store");
        let first = Store::acquire(root.clone()).unwrap();
        assert!(!first.previous);
        fs::write(root.join("cas/object"), b"actual object bytes").unwrap();
        first.finish().unwrap();
        drop(first);
        let warm = Store::acquire(root.clone()).unwrap();
        assert!(warm.previous);
        warm.finish().unwrap();
        drop(warm);
        fs::write(root.join("cas/object"), b"corrupted object bytes").unwrap();
        let corrupt = Store::acquire(root.clone()).unwrap();
        assert!(!corrupt.previous);
        assert!(corrupt.reset_reason.is_some());
        assert!(!root.join("cas/object").exists());
        fs::write(root.join("cas/object"), b"new checked object").unwrap();
        corrupt.finish().unwrap();
        drop(corrupt);
        fs::remove_file(root.join("cas/object")).unwrap();
        let missing = Store::acquire(root.clone()).unwrap();
        assert!(!missing.previous);
        assert!(missing.reset_reason.is_some());
        missing.finish().unwrap();
        drop(missing);
        let canary = temp.path().join("canary");
        fs::write(&canary, b"outside cache").unwrap();
        std::os::unix::fs::symlink(&canary, root.join("cas/redirected")).unwrap();
        let redirected = Store::acquire(root.clone()).unwrap();
        assert!(!redirected.previous);
        assert!(redirected.reset_reason.is_some());
        assert_eq!(fs::read(canary).unwrap(), b"outside cache");
    }

    #[test]
    fn actual_child_retains_close_only_lease_after_rust_owner_drops() {
        let temp = tempdir();
        let root = temp.path().join("store");
        let store = Store::acquire(root.clone()).unwrap();
        let mut command = Command::new("/bin/sh");
        command
            .args(["-c", "printf 'ready\\n'; read ignored"])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped());
        store.configure(&mut command).unwrap();
        let mut child = command.spawn().unwrap();
        drop(command);
        let mut line = String::new();
        BufReader::new(child.stdout.take().unwrap())
            .read_line(&mut line)
            .unwrap();
        assert_eq!(line, "ready\n");
        drop(store);
        assert!(Store::acquire(root.clone())
            .err()
            .unwrap()
            .contains("lease unavailable"));
        drop(child.stdin.take());
        assert!(!child.wait().unwrap().success());
        Store::acquire(root).unwrap();
    }

    #[test]
    fn second_producer_and_substituted_lease_cannot_admit() {
        let temp = tempdir();
        let root = temp.path().join("store");
        let owner = Store::acquire(root.clone()).unwrap();
        assert!(Store::acquire(root.clone()).is_err());
        fs::rename(root.join("lease"), root.join("original-lease")).unwrap();
        fs::write(root.join("lease"), b"substitute").unwrap();
        assert!(owner.check_current().unwrap_err().contains("substituted"));
        assert!(owner.finish().is_err());
    }
}
