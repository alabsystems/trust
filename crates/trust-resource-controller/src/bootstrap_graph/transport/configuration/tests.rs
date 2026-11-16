//! Native file/SCM observations; no fixture is a Manager or resident Job issuer.
use std::fs::{self, File, OpenOptions};
use std::io::{Seek as _, SeekFrom};
use std::os::unix::fs::{MetadataExt as _, OpenOptionsExt as _, symlink};
use std::os::unix::net::UnixStream;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use super::*;

struct Inputs {
    path: PathBuf,
    source: File,
    file: File,
    request: ConfigurationAttachment,
}
impl Inputs {
    fn new() -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let path = std::env::temp_dir().join(format!(
            "trust-config-offer-{}-{}-{}",
            std::process::id(),
            SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos(),
            NEXT.fetch_add(1, Ordering::Relaxed),
        ));
        fs::create_dir(&path).unwrap();
        fs::create_dir(path.join("config")).unwrap();
        let bytes = b"[build]\njobs = 4\n";
        fs::write(path.join("config/bootstrap.toml"), bytes).unwrap();
        let source = File::open(&path).unwrap();
        let file = OpenOptions::new()
            .read(true)
            .custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK | libc::O_CLOEXEC)
            .open(path.join("config/bootstrap.toml"))
            .unwrap();
        let metadata = file.metadata().unwrap();
        let request = ConfigurationAttachment {
            key: crate::bootstrap_graph::tests::key(),
            sequence: 1,
            relative: b"config/bootstrap.toml".to_vec(),
            file: FileIdentity { device: metadata.dev(), inode: metadata.ino() },
            bytes: bytes.len() as u64,
            sha256: Sha256::digest(bytes).into(),
            modified: Timestamp {
                seconds: metadata.mtime(),
                nanoseconds: metadata.mtime_nsec().try_into().unwrap(),
            },
            changed: Timestamp {
                seconds: metadata.ctime(),
                nanoseconds: metadata.ctime_nsec().try_into().unwrap(),
            },
            input_remaining_ns: 60_000_000_000,
        };
        Self { path, source, file, request }
    }
    fn check(&self) -> io::Result<()> {
        check_configuration(&self.request, self.source.as_fd(), self.file.as_fd(), deadline())
    }
}
impl Drop for Inputs {
    fn drop(&mut self) {
        fs::remove_dir_all(&self.path).unwrap();
    }
}
fn deadline() -> Instant {
    Instant::now() + Duration::from_secs(60)
}

#[test]
fn original_file_transfers_and_hashes_without_changing_its_shared_cursor() {
    let mut input = Inputs::new();
    input.file.seek(SeekFrom::Start(3)).unwrap();
    input.check().unwrap();
    assert_eq!(input.file.stream_position().unwrap(), 3);
    let (left, right) = UnixStream::pair().unwrap();
    let (mut sender, mut receiver) = (Channel::new(left).unwrap(), Channel::new(right).unwrap());
    send_configuration_description(&mut sender, input.file.as_fd(), deadline()).unwrap();
    let retained = receive_configuration_description(&mut receiver, deadline()).unwrap();
    check_configuration(&input.request, input.source.as_fd(), retained.as_fd(), deadline())
        .unwrap();
    let mut borrowed = File::from(retained.try_clone().unwrap());
    assert_eq!(borrowed.stream_position().unwrap(), 3);
    borrowed.seek(SeekFrom::Start(5)).unwrap();
    assert_eq!(input.file.stream_position().unwrap(), 5);
}

#[test]
fn equal_bytes_from_a_foreign_file_or_named_replacement_do_not_validate() {
    let input = Inputs::new();
    let other = Inputs::new();
    assert!(
        check_configuration(&input.request, input.source.as_fd(), other.file.as_fd(), deadline(),)
            .is_err()
    );
    fs::rename(input.path.join("config"), input.path.join("original")).unwrap();
    fs::create_dir(input.path.join("config")).unwrap();
    fs::write(input.path.join("config/bootstrap.toml"), b"[build]\njobs = 4\n").unwrap();
    assert!(input.check().is_err());
}

#[test]
fn symlinks_writers_changed_bytes_and_expired_endpoints_refuse() {
    let input = Inputs::new();
    let writer = OpenOptions::new()
        .read(true)
        .write(true)
        .open(input.path.join("config/bootstrap.toml"))
        .unwrap();
    assert!(
        check_configuration(&input.request, input.source.as_fd(), writer.as_fd(), deadline(),)
            .is_err()
    );
    assert!(
        check_configuration(
            &input.request,
            input.source.as_fd(),
            input.file.as_fd(),
            Instant::now(),
        )
        .is_err()
    );
    fs::rename(input.path.join("config"), input.path.join("original")).unwrap();
    symlink("original", input.path.join("config")).unwrap();
    assert!(input.check().is_err());
    fs::remove_file(input.path.join("config")).unwrap();
    fs::rename(input.path.join("original"), input.path.join("config")).unwrap();
    fs::write(input.path.join("config/bootstrap.toml"), b"[build]\njobs = 9\n").unwrap();
    assert!(input.check().is_err());
}

#[test]
fn delivered_description_is_retained_even_when_its_content_check_refuses() {
    let input = Inputs::new();
    let (left, right) = UnixStream::pair().unwrap();
    let (mut sender, mut receiver) = (Channel::new(left).unwrap(), Channel::new(right).unwrap());
    send_configuration_description(&mut sender, input.file.as_fd(), deadline()).unwrap();
    let retained = receive_configuration_description(&mut receiver, deadline()).unwrap();
    let mut changed = input.request.clone();
    changed.sha256[0] ^= 1;
    assert!(
        check_configuration(&changed, input.source.as_fd(), retained.as_fd(), deadline(),).is_err()
    );
    assert!(inspect(retained.as_fd()).is_ok());
    input.check().unwrap();
}

#[test]
fn wrong_rights_count_poison_cannot_resume_as_a_configuration_offer() {
    let input = Inputs::new();
    let (left, right) = UnixStream::pair().unwrap();
    let (mut sender, mut receiver) = (Channel::new(left).unwrap(), Channel::new(right).unwrap());
    sender
        .send_bootstrap_descriptions(
            &[input.source.as_fd(), input.file.as_fd()],
            crate::bootstrap_graph::configuration::RIGHTS_MARKER,
            deadline(),
        )
        .unwrap();
    assert!(receive_configuration_description(&mut receiver, deadline()).is_err());
    assert!(receiver.send(b"not a retry", deadline()).is_err());
}

#[test]
fn two_actual_descriptions_remain_retained_after_the_second_content_refusal() {
    use crate::bootstrap_graph::configuration::ConfigurationBudget;
    let input = Inputs::new();
    let bytes = b"[rust]\ndebug = true\n";
    let path = input.path.join("config/profile.toml");
    fs::write(&path, bytes).unwrap();
    let file = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK | libc::O_CLOEXEC)
        .open(path)
        .unwrap();
    let metadata = file.metadata().unwrap();
    let mut second = input.request.clone();
    second.sequence = 2;
    second.relative = b"config/profile.toml".to_vec();
    second.file = FileIdentity { device: metadata.dev(), inode: metadata.ino() };
    second.bytes = bytes.len() as u64;
    second.sha256 = Sha256::digest(bytes).into();
    second.modified = Timestamp {
        seconds: metadata.mtime(),
        nanoseconds: metadata.mtime_nsec().try_into().unwrap(),
    };
    second.changed = Timestamp {
        seconds: metadata.ctime(),
        nanoseconds: metadata.ctime_nsec().try_into().unwrap(),
    };
    let mut budget = ConfigurationBudget::default();
    let (left, right) = UnixStream::pair().unwrap();
    let (mut sender, mut receiver) = (Channel::new(left).unwrap(), Channel::new(right).unwrap());
    let mut retained = Vec::new();
    for (request, file) in [(&input.request, &input.file), (&second, &file)] {
        // The actual receiving slot reserves before receiving/reading contents.
        budget.reserve(request).unwrap();
        send_configuration_description(&mut sender, file.as_fd(), deadline()).unwrap();
        retained.push(receive_configuration_description(&mut receiver, deadline()).unwrap());
        check_configuration(
            request,
            input.source.as_fd(),
            retained.last().unwrap().as_fd(),
            deadline(),
        )
        .unwrap();
    }
    assert_eq!(budget.remaining_files(), crate::bootstrap_graph::configuration::MAX_FILES - 2);
    assert_eq!(
        budget.remaining_bytes(),
        crate::bootstrap_graph::configuration::MAX_BYTES - input.request.bytes - second.bytes
    );
    second.sha256[0] ^= 1;
    assert!(
        check_configuration(&second, input.source.as_fd(), retained[1].as_fd(), deadline())
            .is_err()
    );
    assert!(retained.iter().all(|description| inspect(description.as_fd()).is_ok()));
    input.check().unwrap();
}
