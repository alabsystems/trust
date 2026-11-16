use std::fs::File;
use std::os::fd::{AsRawFd, FromRawFd};
use std::os::unix::fs::MetadataExt;

use sha2::{Digest, Sha256};
use trust_process_isolation::{Budget, Charge};

use super::{InputSource, checked, contract};
use crate::{Error, system};

#[derive(Debug)]
pub(crate) struct Snapshot {
    pub file: File,
    pub sha256: [u8; 32],
    pub size: u64,
    pub executable: bool,
}

pub(crate) fn copy(source: &InputSource<'_>, budget: &Budget) -> Result<Snapshot, Error> {
    checked(budget)?;
    let meta = source.file.metadata().map_err(|e| Error::System("source metadata", e))?;
    if !meta.is_file() || meta.len() != source.size || source.size == 0 {
        return Err(contract("source size/type"));
    }
    let flags = libc::MFD_CLOEXEC | libc::MFD_ALLOW_SEALING;
    // SAFETY: the constant name has a terminating NUL; the syscall returns one
    // owned descriptor or an error, without inheriting a source path identity.
    let fd = unsafe { libc::memfd_create(c"trust-worker-input".as_ptr(), flags) };
    if fd < 0 {
        return Err(system("snapshot memfd"));
    }
    // SAFETY: successful memfd_create returned a new uniquely owned descriptor.
    let writable = unsafe { File::from_raw_fd(fd) };
    budget
        .charge(Charge { allocation_bytes: source.size, ..Charge::default() })
        .map_err(Error::Budget)?;
    let mut buffer = [0; 8192];
    let mut offset = 0u64;
    let mut digest = Sha256::new();
    while offset < source.size {
        checked(budget)?;
        let count = usize::try_from((source.size - offset).min(buffer.len() as u64))
            .map_err(|_| contract("snapshot conversion"))?;
        // Read, hash and copy are charged before traversal. Kernel page backing
        // is separately reserved above, including coexistence with parent data.
        budget
            .charge(Charge { work: 4 * count as u64, ..Charge::default() })
            .map_err(Error::Budget)?;
        let off = i64::try_from(offset).map_err(|_| contract("snapshot offset"))?;
        // SAFETY: the stack destination is writable for count bytes, source is
        // an owned regular-file FD, and pread does not mutate its shared offset.
        let read =
            unsafe { libc::pread(source.file.as_raw_fd(), buffer.as_mut_ptr().cast(), count, off) };
        if read <= 0 || read as usize > count {
            return Err(if read < 0 { system("snapshot pread") } else { contract("short source") });
        }
        let read = read as usize;
        digest.update(&buffer[..read]);
        let mut written = 0;
        while written < read {
            checked(budget)?;
            // SAFETY: the initialized buffer range remains live; writable is
            // this owner's snapshot, and checked offsets fit off_t.
            let n = unsafe {
                libc::pwrite(
                    fd,
                    buffer[written..read].as_ptr().cast(),
                    read - written,
                    off + written as i64,
                )
            };
            if n <= 0 || n as usize > read - written {
                return Err(if n < 0 {
                    system("snapshot pwrite")
                } else {
                    contract("short snapshot write")
                });
            }
            written += n as usize;
        }
        offset += read as u64;
    }
    checked(budget)?;
    budget.charge(Charge { work: 1, ..Charge::default() }).map_err(Error::Budget)?;
    let mut extra = 0u8;
    // SAFETY: extra is one writable byte and the checked offset is after the
    // exact expected source length. Growth/short copies never become inputs.
    let n = unsafe {
        libc::pread(
            source.file.as_raw_fd(),
            (&mut extra as *mut u8).cast(),
            1,
            i64::try_from(offset).map_err(|_| contract("snapshot offset"))?,
        )
    };
    if n != 0 {
        return Err(if n < 0 { system("snapshot end") } else { contract("source grew") });
    }
    let sha256: [u8; 32] = digest.finalize().into();
    if sha256 != source.sha256 {
        return Err(contract("snapshot digest"));
    }
    let seals = libc::F_SEAL_WRITE | libc::F_SEAL_GROW | libc::F_SEAL_SHRINK | libc::F_SEAL_SEAL;
    // SAFETY: scalar irreversible seals address only our newly created memfd.
    if unsafe { libc::fcntl(fd, libc::F_ADD_SEALS, seals) } != 0 {
        return Err(system("snapshot seals"));
    }
    // Reopening is parent-only and refers to an owned live descriptor, never a
    // source pathname or a target-supplied procfd alias. The sealed bytes cannot
    // change between this reopen and the child's consumption.
    budget.charge(Charge { work: 64, ..Charge::default() }).map_err(Error::Budget)?;
    let path = proc_path(b"self/fd/", fd as u32, b"")?;
    // SAFETY: proc_path produces a terminated bounded path for our live owned
    // descriptor. The new read-only capability is uniquely owned on success.
    let readonly_fd = unsafe { libc::open(path.as_ptr().cast(), libc::O_RDONLY | libc::O_CLOEXEC) };
    if readonly_fd < 0 {
        return Err(system("readonly snapshot"));
    }
    // SAFETY: successful open returned a fresh uniquely owned descriptor.
    let readonly = unsafe { File::from_raw_fd(readonly_fd) };
    checked(budget)?;
    drop(writable);
    checked(budget)?;
    Ok(Snapshot { file: readonly, sha256, size: source.size, executable: source.executable })
}

pub(crate) fn proc_path(prefix: &[u8], number: u32, suffix: &[u8]) -> Result<[u8; 64], Error> {
    let mut result = [0; 64];
    let start = b"/proc/";
    let mut digits = [0; 10];
    let mut n = number;
    let mut count = 0;
    loop {
        digits[count] = b'0' + (n % 10) as u8;
        count += 1;
        n /= 10;
        if n == 0 {
            break;
        }
    }
    let len = start.len() + prefix.len() + count + suffix.len();
    if len >= result.len() {
        return Err(contract("proc observation path"));
    }
    result[..start.len()].copy_from_slice(start);
    let mut at = start.len();
    result[at..at + prefix.len()].copy_from_slice(prefix);
    at += prefix.len();
    for d in digits[..count].iter().rev() {
        result[at] = *d;
        at += 1;
    }
    result[at..at + suffix.len()].copy_from_slice(suffix);
    Ok(result)
}

/// A new open-file description of the same still-owned sealed inode. Only the
/// parent's literal descriptor path is used; target aliases are never paths.
pub(crate) fn fresh_readonly(s: &Snapshot, budget: &Budget) -> Result<File, Error> {
    checked(budget)?;
    budget.charge(Charge { work: 512, ..Charge::default() }).map_err(Error::Budget)?;
    let original = s.file.metadata().map_err(|e| Error::System("immutable metadata", e))?;
    let required = libc::F_SEAL_WRITE | libc::F_SEAL_GROW | libc::F_SEAL_SHRINK | libc::F_SEAL_SEAL;
    // SAFETY: the source is a live uniquely owned snapshot descriptor, queried
    // only for irreversible seal state. It remains borrowed through reopening.
    let source_seals = unsafe { libc::fcntl(s.file.as_raw_fd(), libc::F_GET_SEALS) };
    if !original.is_file()
        || original.len() != s.size
        || source_seals < 0
        || source_seals & required != required
    {
        return Err(contract("immutable reopen source"));
    }
    let path = proc_path(b"self/fd/", s.file.as_raw_fd() as u32, b"")?;
    // SAFETY: the terminated bounded path names this live parent's descriptor,
    // never a worker pathname. The successful new FD is uniquely owned.
    let fd = unsafe { libc::open(path.as_ptr().cast(), libc::O_RDONLY | libc::O_CLOEXEC) };
    if fd < 0 {
        return Err(system("immutable fresh description"));
    }
    // SAFETY: successful open returned one fresh uniquely owned descriptor.
    let fresh = unsafe { File::from_raw_fd(fd) };
    let actual = fresh.metadata().map_err(|e| Error::System("immutable reopen metadata", e))?;
    // SAFETY: scalar flag/seal observations address only this new owned FD.
    let (seals, flags, descriptor) = unsafe {
        (
            libc::fcntl(fd, libc::F_GET_SEALS),
            libc::fcntl(fd, libc::F_GETFL),
            libc::fcntl(fd, libc::F_GETFD),
        )
    };
    if !actual.is_file()
        || actual.len() != s.size
        || actual.dev() != original.dev()
        || actual.ino() != original.ino()
        || seals < 0
        || seals & required != required
        || flags < 0
        || flags & libc::O_ACCMODE != libc::O_RDONLY
        || descriptor < 0
        || descriptor & libc::FD_CLOEXEC == 0
    {
        return Err(contract("immutable reopen identity/roles"));
    }
    checked(budget)?;
    Ok(fresh)
}

#[cfg(test)]
mod tests {
    use std::io::Write;
    use std::time::{Duration, Instant};

    use trust_process_isolation::Limits;

    use super::*;
    fn source() -> File {
        // SAFETY: constant terminated memfd name, returning a fresh descriptor.
        let fd = unsafe {
            libc::memfd_create(
                c"snapshot-test".as_ptr(),
                libc::MFD_CLOEXEC | libc::MFD_ALLOW_SEALING,
            )
        };
        assert!(fd >= 0);
        // SAFETY: successful memfd_create returned one uniquely owned FD.
        let mut file = unsafe { File::from_raw_fd(fd) };
        file.write_all(&[b'p'; 4096]).unwrap();
        file
    }
    fn b(work: u64, allocation_bytes: u64) -> Budget {
        Budget::new(
            Limits {
                frame_bytes: 1024,
                wire_bytes: 10000,
                allocation_bytes,
                values: 100,
                work,
                calls: 10,
                live_handles: 4,
                depth: 8,
            },
            Instant::now() + Duration::from_secs(5),
        )
        .unwrap()
    }
    #[test]
    fn exact_snapshot_is_sealed_readonly_and_survives_source_changes() {
        let file = source();
        let input = InputSource {
            file: &file,
            sha256: Sha256::digest([b'p'; 4096]).into(),
            size: 4096,
            executable: false,
        };
        let snapshot = copy(&input, &b(16449, 4096)).unwrap();
        // SAFETY: scalar observations of this test's two owned descriptors;
        // pwrite mutates only the original, not the sealed read-only snapshot.
        unsafe {
            assert_eq!(
                libc::fcntl(snapshot.file.as_raw_fd(), libc::F_GETFL) & libc::O_ACCMODE,
                libc::O_RDONLY
            );
            let seals =
                libc::F_SEAL_WRITE | libc::F_SEAL_GROW | libc::F_SEAL_SHRINK | libc::F_SEAL_SEAL;
            assert_eq!(libc::fcntl(snapshot.file.as_raw_fd(), libc::F_GET_SEALS) & seals, seals);
            assert_eq!(libc::pwrite(file.as_raw_fd(), b"x".as_ptr().cast(), 1, 0), 1);
            let mut byte = 0u8;
            assert_eq!(
                libc::pread(snapshot.file.as_raw_fd(), (&mut byte as *mut u8).cast(), 1, 0),
                1
            );
            assert_eq!(byte, b'p');
        }
    }
    #[test]
    fn one_short_snapshot_work_or_backing_allocation_sticks() {
        let file = source();
        let input = InputSource {
            file: &file,
            sha256: Sha256::digest([b'p'; 4096]).into(),
            size: 4096,
            executable: false,
        };
        for budget in [b(16448, 4096), b(16449, 4095)] {
            assert!(copy(&input, &budget).is_err());
            assert!(budget.clone().check().is_err());
        }
    }
}
