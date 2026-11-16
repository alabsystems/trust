//! Real descriptor/SCM controls, not original Manager or Job authority fixtures.
use std::fs::{self, File, OpenOptions};
use std::io::{Seek as _, SeekFrom};
use std::os::unix::net::UnixStream;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use super::*;

struct Inputs {
    path: PathBuf,
    files: [File; 4],
    request: SourceAttachment,
}
impl Inputs {
    fn new() -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let path = std::env::temp_dir().join(format!(
            "trust-source-offer-{}-{}-{}",
            std::process::id(),
            SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        let holder = path.join(".trust-build-lock");
        fs::create_dir(&holder).unwrap();
        fs::write(holder.join("info"), b"private acquired record").unwrap();
        let old = File::open(holder.join("info")).unwrap();
        fs::remove_file(holder.join("info")).unwrap();
        fs::write(holder.join("info"), b"private withheld record").unwrap();
        let files = [
            File::open(&path).unwrap(),
            File::open(&holder).unwrap(),
            old,
            File::open(holder.join("info")).unwrap(),
        ];
        let record = |index: usize, bytes: &[u8]| SourceRecord {
            identity: inspect(files[index].as_fd()).unwrap().identity,
            bytes: bytes.len() as u64,
            sha256: Sha256::digest(bytes).into(),
        };
        let request = SourceAttachment {
            key: crate::bootstrap_graph::tests::key(),
            source_directory: inspect(files[0].as_fd()).unwrap().identity,
            holder_directory: inspect(files[1].as_fd()).unwrap().identity,
            holder_name: crate::bootstrap_graph::source::HOLDER_NAME.to_vec(),
            original_record: record(2, b"private acquired record"),
            withheld_record: record(3, b"private withheld record"),
        };
        Self { path, files, request }
    }
    fn fds(&self) -> [BorrowedFd<'_>; 4] {
        self.files.each_ref().map(|file| file.as_fd())
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
fn same_four_descriptions_transfer_with_unlinked_original_and_unchanged_cursor() {
    let mut inputs = Inputs::new();
    inputs.files[2].seek(SeekFrom::Start(3)).unwrap();
    let (left, right) = UnixStream::pair().unwrap();
    let (mut sender, mut receiver) = (Channel::new(left).unwrap(), Channel::new(right).unwrap());
    send_source(&mut sender, &inputs.request, &inputs.fds(), deadline(), || Ok(())).unwrap();
    let received = receive_source(&mut receiver, &inputs.request, deadline(), || Ok(())).unwrap();
    assert_eq!(inspect(received[2].as_fd()).unwrap().links, 0);
    assert_eq!(inputs.files[2].stream_position().unwrap(), 3);
    let mut same = File::from(received[2].try_clone().unwrap());
    assert_eq!(same.stream_position().unwrap(), 3);
    same.seek(SeekFrom::Start(5)).unwrap();
    assert_eq!(inputs.files[2].stream_position().unwrap(), 5);
    check_source(&inputs.request, &received.each_ref().map(|fd| fd.as_fd()), deadline()).unwrap();
    sender.send(b"same live graph", deadline()).unwrap();
    assert_eq!(receiver.receive(deadline()).unwrap(), b"same live graph");
}

#[test]
fn writable_duplicate_changed_record_and_replaced_holder_refuse() {
    let inputs = Inputs::new();
    let writer = OpenOptions::new()
        .read(true)
        .write(true)
        .open(inputs.path.join(".trust-build-lock/info"))
        .unwrap();
    let mut fds = inputs.fds();
    fds[3] = writer.as_fd();
    assert!(check_source(&inputs.request, &fds, deadline()).is_err());
    fds = inputs.fds();
    fds[2] = fds[3];
    assert!(check_source(&inputs.request, &fds, deadline()).is_err());
    assert!(check_source(&inputs.request, &inputs.fds(), Instant::now()).is_err());
    fs::write(inputs.path.join(".trust-build-lock/info"), b"private withheld CHANGED").unwrap();
    assert!(check_source(&inputs.request, &inputs.fds(), deadline()).is_err());
    fs::rename(inputs.path.join(".trust-build-lock"), inputs.path.join("old-holder")).unwrap();
    fs::create_dir(inputs.path.join(".trust-build-lock")).unwrap();
    assert!(check_source(&inputs.request, &inputs.fds(), deadline()).is_err());
}

#[test]
fn partial_source_offer_poison_cannot_resume() {
    let inputs = Inputs::new();
    let (left, right) = UnixStream::pair().unwrap();
    let (mut sender, mut receiver) = (Channel::new(left).unwrap(), Channel::new(right).unwrap());
    // Deliberately malformed source offer: existing two-description primitive
    // can send the source marker, but the receiver requires exactly four.
    sender
        .send_bootstrap_descriptions(
            &inputs.fds()[..2],
            crate::bootstrap_graph::source::RIGHTS_MARKER,
            deadline(),
        )
        .unwrap();
    assert!(receive_source(&mut receiver, &inputs.request, deadline(), || Ok(())).is_err());
    assert!(receiver.send(b"must remain poisoned", deadline()).is_err());
}
