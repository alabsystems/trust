//! Native dyld mapping observation and checked content-derived UUID binding.
//! A UUID copied from a file is not sufficient: every signed data page and
//! Apple's content-derived UUID recipe must validate against the live mapping.

use std::fs::{self, File, OpenOptions};
use std::io::{Read, Seek, SeekFrom};
use std::mem::{size_of, MaybeUninit};
use std::os::unix::fs::{MetadataExt, OpenOptionsExt};
use std::path::PathBuf;

mod signature;
use sha2::{Digest, Sha256};

#[repr(C)]
#[derive(Clone, Copy)]
struct TaskDyldInfo {
    address: u64,
    size: u64,
    format: i32,
}

// Public SDK mach-o/dyld_images.h. Only the stable prefix through v18's
// shared-cache identity is copied; pointer-valued fields are never followed.
#[repr(C)]
#[derive(Clone, Copy)]
struct DyldImagesPrefix {
    version: u32,
    image_count: u32,
    image_array: usize,
    notification: usize,
    detached: u8,
    system_initialized: u8,
    dyld_address: usize,
    jit: usize,
    dyld_version: usize,
    error_message: usize,
    termination_flags: usize,
    symbolication: usize,
    system_order: usize,
    uuid_count: usize,
    uuid_array: usize,
    own_address: usize,
    initial_image_count: usize,
    error_kind: usize,
    error_client: usize,
    error_target: usize,
    error_symbol: usize,
    shared_cache_slide: usize,
    shared_cache_uuid: [u8; 16],
    shared_cache_address: usize,
}

extern "C" {
    static mach_task_self_: libc::mach_port_t;
    fn mach_vm_read_overwrite(
        task: libc::mach_port_t,
        address: u64,
        size: u64,
        data: u64,
        copied: *mut u64,
    ) -> libc::kern_return_t;
}

/// Mapping observation only. It cannot authorize reuse until exact runtime
/// bytes have passed the signature/content-derived-UUID validation below.
#[derive(Debug, Clone, Eq, PartialEq)]
pub(super) struct RuntimeOrigin {
    uuid: [u8; 16],
    base: u64,
}

pub(super) struct VerifiedMain {
    pub path: PathBuf,
    pub file: File,
    pub digest: [u8; 32],
    pub header: Vec<u8>,
    // The stamp from BEFORE the authenticated read, never a fresh baseline.
    stamp: fs::Metadata,
}

impl VerifiedMain {
    fn check_current(&self) -> Result<(), String> {
        if !same_file(
            &self.stamp,
            &self.file.metadata().map_err(|e| e.to_string())?,
        ) || !same_file(
            &self.stamp,
            &fs::symlink_metadata(&self.path).map_err(|e| e.to_string())?,
        ) {
            return Err("authenticated main runtime changed before manifest consumption".into());
        }
        Ok(())
    }
}

/// Complete current shared-cache closure, selected by authenticated main-cache
/// dependency entries rather than a guessed directory/version inventory.
pub(super) struct RuntimeSnapshot {
    origin: RuntimeOrigin,
    files: Vec<(PathBuf, File, fs::Metadata)>,
    pub digest: [u8; 32],
    pub bytes: u64,
}

impl RuntimeSnapshot {
    pub(super) fn capture() -> Result<Self, String> {
        let origin = RuntimeOrigin::capture()?;
        let mut main = origin.open_verified_main()?;
        main.check_current()?;
        let mapping_offset = u32::from_le_bytes(main.header[16..20].try_into().unwrap());
        if mapping_offset < 464 {
            return Err("native runtime has no supported complete subcache manifest".into());
        }
        let offset = u32::from_le_bytes(main.header[392..396].try_into().unwrap()) as u64;
        let count = u32::from_le_bytes(main.header[396..400].try_into().unwrap()) as usize;
        let signature_offset = u64::from_le_bytes(main.header[40..48].try_into().unwrap());
        if count > 128
            || offset
                .checked_add((count * 56) as u64)
                .is_none_or(|end| end > signature_offset)
        {
            return Err("native runtime subcache manifest exceeds its signed bounds".into());
        }
        let mut entries = vec![0_u8; count * 56];
        main.file
            .seek(SeekFrom::Start(offset))
            .map_err(|e| e.to_string())?;
        main.file
            .read_exact(&mut entries)
            .map_err(|e| e.to_string())?;
        main.check_current()?;
        let mut hash = Sha256::new();
        hash.update(b"trust.native-dyld-runtime-content.v1\0");
        hash.update(origin.uuid);
        hash.update(main.digest);
        let mut bytes = main.stamp.len();
        let mut files = Vec::with_capacity(count + 1);
        let mut names = std::collections::BTreeSet::new();
        let base_name = main
            .path
            .file_name()
            .and_then(|name| name.to_str())
            .ok_or("non-UTF8 native cache name")?
            .to_owned();
        let root = main
            .path
            .parent()
            .ok_or("native cache has no parent")?
            .to_owned();
        files.push((main.path, main.file, main.stamp));
        for entry in entries.chunks_exact(56) {
            let uuid: [u8; 16] = entry[..16].try_into().unwrap();
            let raw = &entry[24..56];
            let end = raw
                .iter()
                .position(|byte| *byte == 0)
                .ok_or("unterminated native cache suffix")?;
            let suffix = std::str::from_utf8(&raw[..end]).map_err(|e| e.to_string())?;
            if !suffix.starts_with('.')
                || suffix.len() < 2
                || suffix.contains("..")
                || !suffix
                    .bytes()
                    .all(|b| b.is_ascii_alphanumeric() || b == b'.' || b == b'_')
                || !names.insert(suffix.to_owned())
                || uuid == [0; 16]
            {
                return Err("invalid signed native cache dependency".into());
            }
            let path = root.join(format!("{base_name}{suffix}"));
            let before = fs::symlink_metadata(&path).map_err(|e| e.to_string())?;
            bytes = bytes
                .checked_add(before.len())
                .ok_or("native runtime size overflow")?;
            if bytes > 8 * 1024 * 1024 * 1024 {
                return Err(
                    "native runtime closure exceeds its eight-GiB observation bound".into(),
                );
            }
            if !before.is_file() || before.file_type().is_symlink() {
                return Err("native cache dependency is redirected or special".into());
            }
            let mut file = OpenOptions::new()
                .read(true)
                .custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK | libc::O_CLOEXEC)
                .open(&path)
                .map_err(|e| e.to_string())?;
            if !same_file(&before, &file.metadata().map_err(|e| e.to_string())?) {
                return Err("native dependency was replaced before opening".into());
            }
            let verified = signature::verify(&mut file, uuid)?;
            if !same_file(&before, &file.metadata().map_err(|e| e.to_string())?)
                || !same_file(
                    &before,
                    &fs::symlink_metadata(&path).map_err(|e| e.to_string())?,
                )
            {
                return Err("native runtime dependency changed during content validation".into());
            }
            hash.update((suffix.len() as u64).to_le_bytes());
            hash.update(suffix.as_bytes());
            hash.update(verified.digest);
            files.push((path, file, before));
        }
        let snapshot = Self {
            origin,
            files,
            digest: hash.finalize().into(),
            bytes,
        };
        snapshot.check_current()?;
        Ok(snapshot)
    }

    pub(super) fn check_current(&self) -> Result<(), String> {
        if RuntimeOrigin::capture()? != self.origin {
            return Err("actual native runtime mapping changed".into());
        }
        for (path, file, stamp) in &self.files {
            if !same_file(stamp, &file.metadata().map_err(|e| e.to_string())?)
                || !same_file(
                    stamp,
                    &fs::symlink_metadata(path).map_err(|e| e.to_string())?,
                )
            {
                return Err("opened native runtime namespace changed".into());
            }
        }
        Ok(())
    }
}

impl RuntimeOrigin {
    pub(super) fn capture() -> Result<Self, String> {
        // SAFETY: libSystem initializes this task's special port before main.
        let task_port = unsafe { mach_task_self_ };
        let mut task = TaskDyldInfo {
            address: 0,
            size: 0,
            format: 0,
        };
        let mut count = (size_of::<TaskDyldInfo>() / size_of::<u32>()) as u32;
        // SAFETY: kernel writes at most count words into this owned buffer.
        let result = unsafe {
            libc::task_info(
                task_port,
                17,
                (&mut task as *mut TaskDyldInfo).cast(),
                &mut count,
            )
        };
        if result != 0
            || count < 5
            || task.format != 1
            || task.size < size_of::<DyldImagesPrefix>() as u64
            || task.address == 0
        {
            return Err("native runtime has no supported task dyld mapping".into());
        }
        let mut prefix = MaybeUninit::<DyldImagesPrefix>::uninit();
        let mut copied = 0;
        // SAFETY: the kernel copies from this task's declared mapping. No Rust
        // reference races with unrelated mutable dyld metadata.
        let result = unsafe {
            mach_vm_read_overwrite(
                task_port,
                task.address,
                size_of::<DyldImagesPrefix>() as u64,
                prefix.as_mut_ptr() as u64,
                &mut copied,
            )
        };
        if result != 0 || copied != size_of::<DyldImagesPrefix>() as u64 {
            return Err("could not copy actual dyld mapping".into());
        }
        // SAFETY: every plain-data byte was initialized by the kernel.
        let prefix = unsafe { prefix.assume_init() };
        if prefix.version < 15
            || prefix.detached != 0
            || prefix.shared_cache_address == 0
            || prefix.shared_cache_uuid == [0; 16]
        {
            return Err("native runtime does not expose its actual shared-cache mapping".into());
        }
        Ok(Self {
            uuid: prefix.shared_cache_uuid,
            base: prefix.shared_cache_address as u64,
        })
    }

    pub(super) fn open_verified_main(&self) -> Result<VerifiedMain, String> {
        for root in [
            "/System/Volumes/Preboot/Cryptexes/OS/System/Library/dyld",
            "/System/Library/dyld",
        ] {
            let entries = match fs::read_dir(root) {
                Ok(entries) => entries,
                Err(e) if e.kind() == std::io::ErrorKind::NotFound => continue,
                Err(e) => return Err(e.to_string()),
            };
            for entry in entries {
                let entry = entry.map_err(|e| e.to_string())?;
                let name = entry.file_name();
                if !name.as_encoded_bytes().starts_with(b"dyld_shared_cache_")
                    || name.as_encoded_bytes().contains(&b'.')
                {
                    continue;
                }
                let path = entry.path();
                let before = fs::symlink_metadata(&path).map_err(|e| e.to_string())?;
                if !before.is_file() || before.file_type().is_symlink() {
                    continue;
                }
                let mut file = OpenOptions::new()
                    .read(true)
                    .custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK | libc::O_CLOEXEC)
                    .open(&path)
                    .map_err(|e| e.to_string())?;
                if !same_file(&before, &file.metadata().map_err(|e| e.to_string())?) {
                    return Err("native cache object moved before opening".into());
                }
                let mut header = [0_u8; 104];
                file.read_exact(&mut header).map_err(|e| e.to_string())?;
                if !header.starts_with(b"dyld_v1") || header[88..104] != self.uuid {
                    continue;
                }
                // Matching UUID fields alone never admits candidate content.
                let verified = signature::verify(&mut file, self.uuid)?;
                if !same_file(&before, &file.metadata().map_err(|e| e.to_string())?)
                    || !same_file(
                        &before,
                        &fs::symlink_metadata(&path).map_err(|e| e.to_string())?,
                    )
                    || Self::capture()? != *self
                {
                    return Err("native runtime moved while its bytes were verified".into());
                }
                return Ok(VerifiedMain {
                    path,
                    file,
                    digest: verified.digest,
                    header: verified.header,
                    stamp: before,
                });
            }
        }
        Err("actual runtime has no content-bound native cache file".into())
    }
}

fn same_file(a: &fs::Metadata, b: &fs::Metadata) -> bool {
    a.dev() == b.dev()
        && a.ino() == b.ino()
        && a.mode() == b.mode()
        && a.len() == b.len()
        && a.mtime() == b.mtime()
        && a.mtime_nsec() == b.mtime_nsec()
        && a.ctime() == b.ctime()
        && a.ctime_nsec() == b.ctime_nsec()
}

#[test]
fn actual_runtime_origin_names_its_checked_shared_cache_bytes() {
    let origin = RuntimeOrigin::capture().unwrap();
    let verified = origin.open_verified_main().unwrap();
    assert!(verified.file.metadata().unwrap().len() > 104);
    assert_eq!(RuntimeOrigin::capture().unwrap(), origin);
    assert!(verified.header.len() >= 400);
    eprintln!(
        "actual runtime content-bound main: {} SHA256={:02x?}",
        verified.path.display(),
        verified.digest
    );
}

#[test]
fn actual_cache_data_and_code_directory_tampering_cannot_copy_runtime_identity() {
    let origin = RuntimeOrigin::capture().unwrap();
    let verified = origin.open_verified_main().unwrap();
    let root = tempfile::tempdir().unwrap();
    let path = root.path().join("copied-main-cache");
    let mut bytes = fs::read(&verified.path).unwrap();
    fs::write(&path, &bytes).unwrap();
    assert_eq!(
        signature::verify(&mut File::open(&path).unwrap(), origin.uuid)
            .unwrap()
            .digest,
        verified.digest
    );
    bytes[4096] ^= 1;
    fs::write(&path, &bytes).unwrap();
    let refusal = signature::verify(&mut File::open(&path).unwrap(), origin.uuid)
        .err()
        .unwrap();
    assert!(refusal.contains("page hash"), "{refusal}");
    bytes[4096] ^= 1;
    let signature_offset = u64::from_le_bytes(bytes[40..48].try_into().unwrap()) as usize;
    let directory_offset = u32::from_be_bytes(
        bytes[signature_offset + 16..signature_offset + 20]
            .try_into()
            .unwrap(),
    ) as usize;
    bytes[signature_offset + directory_offset + 88] ^= 1;
    fs::write(&path, &bytes).unwrap();
    let refusal = signature::verify(&mut File::open(&path).unwrap(), origin.uuid)
        .err()
        .unwrap();
    assert!(refusal.contains("derive"), "{refusal}");
}

#[test]
fn verified_main_cannot_adopt_a_new_stamp_before_manifest_consumption() {
    let origin = RuntimeOrigin::capture().unwrap();
    let verified = origin.open_verified_main().unwrap();
    let root = tempfile::tempdir().unwrap();
    let path = root.path().join("actual-main-copy");
    fs::copy(&verified.path, &path).unwrap();
    let stamp = fs::symlink_metadata(&path).unwrap();
    let mut file = File::open(&path).unwrap();
    let checked = signature::verify(&mut file, origin.uuid).unwrap();
    let main = VerifiedMain {
        path: path.clone(),
        file,
        digest: checked.digest,
        header: checked.header,
        stamp,
    };
    main.check_current().unwrap();
    let offset = u32::from_le_bytes(main.header[392..396].try_into().unwrap()) as usize;
    let mut bytes = fs::read(&path).unwrap();
    // Alter an authenticated subcache UUID after signature validation. A
    // freshly captured stamp would silently adopt these new dependency bytes.
    bytes[offset] ^= 1;
    fs::write(&path, bytes).unwrap();
    assert!(main
        .check_current()
        .unwrap_err()
        .contains("before manifest consumption"));
}

#[test]
#[ignore = "streams the actual complete native dyld cache; run through machine admission"]
fn actual_complete_runtime_closure_is_byte_checked() {
    let start = std::time::Instant::now();
    let snapshot = RuntimeSnapshot::capture().unwrap();
    snapshot.check_current().unwrap();
    eprintln!(
        "native runtime closure files={} bytes={} SHA256={:02x?} elapsed={:?}",
        snapshot.files.len(),
        snapshot.bytes,
        snapshot.digest,
        start.elapsed()
    );
}
