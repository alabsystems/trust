//! Stateful/socket DATA controls. No test constructs CompletedObjectCompile,
//! an original graph, native retirement, SDK custody or a producing admission.
use std::os::fd::AsFd as _;
use std::os::unix::ffi::OsStrExt as _;
use std::os::unix::fs::PermissionsExt as _;
use std::os::unix::net::UnixStream;

use super::*;

struct Source {
    directory: std::path::PathBuf,
    root: std::fs::File,
    file: std::fs::File,
    request: object::Request,
}
impl Source {
    fn new() -> Self {
        use std::time::{SystemTime, UNIX_EPOCH};
        // Parallel tests can read one clock microsecond; the sequence keeps each fixture its own.
        static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
        let directory = std::env::temp_dir().join(format!(
            "object-client-source-{}-{}-{}",
            std::process::id(),
            SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos(),
            NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
        ));
        std::fs::create_dir_all(directory.join("src/bootstrap")).unwrap();
        let directory = std::fs::canonicalize(directory).unwrap();
        let path = directory.join("src/bootstrap/native_object.rs");
        std::fs::write(&path, object::SOURCE_BYTES).unwrap();
        let root = std::fs::File::open(&directory).unwrap();
        let file = std::fs::File::open(&path).unwrap();
        let mut request = object::tests::request();
        let meta = root.metadata().unwrap();
        request.source_root = directory.as_os_str().as_bytes().to_vec();
        request.source_directory = crate::FileIdentity { device: meta.dev(), inode: meta.ino() };
        let meta = file.metadata().unwrap();
        request.source.path = path.as_os_str().as_bytes().to_vec();
        request.source.device = meta.dev();
        request.source.inode = meta.ino();
        Self { directory, root, file, request }
    }
}
impl Drop for Source {
    fn drop(&mut self) {
        std::fs::remove_dir_all(&self.directory).unwrap();
    }
}

fn artifact(path: &std::path::Path) -> (File, MetadataFile) {
    std::fs::write(path, b"native file observation only").unwrap();
    std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o400)).unwrap();
    let file = File::open(path).unwrap();
    let meta = file.metadata().unwrap();
    let observed = MetadataFile {
        path: path.as_os_str().as_bytes().to_vec(),
        sha256: [0; 32],
        bytes: meta.len(),
        device: meta.dev(),
        inode: meta.ino(),
    };
    (file, observed)
}
#[test]
fn sealed_file_observation_requires_exact_readonly_identity_mode_and_one_link() {
    let inputs = Source::new();
    let path = inputs.directory.join("artifact.o");
    let (file, observed) = artifact(&path);
    let until = Instant::now() + Duration::from_secs(60);
    assert_eq!(unsafe { libc::lseek(file.as_raw_fd(), 7, libc::SEEK_SET) }, 7);
    require_sealed_file(&observed, &file, until).unwrap();
    assert_eq!(unsafe { libc::lseek(file.as_raw_fd(), 0, libc::SEEK_CUR) }, 7);
    let mut foreign = observed.clone();
    foreign.inode += 1;
    assert!(require_sealed_file(&foreign, &file, until).is_err());
    std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o600)).unwrap();
    let writable = std::fs::OpenOptions::new().read(true).write(true).open(&path).unwrap();
    std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o400)).unwrap();
    assert!(require_sealed_file(&observed, &writable, until).is_err());
    std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o500)).unwrap();
    assert!(require_sealed_file(&observed, &file, until).is_err());
    std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o400)).unwrap();
    std::fs::hard_link(&path, inputs.directory.join("artifact-alias.o")).unwrap();
    assert!(require_sealed_file(&observed, &file, until).is_err());
    // Native access observations alone create neither an artifact owner nor a
    // CompletedObjectCompile: this fixture deliberately has no such constructor.
}
#[cfg(target_os = "macos")]
#[test]
fn actual_extended_write_acl_refuses_even_when_posix_mode_is_sealed() {
    let inputs = Source::new();
    let path = inputs.directory.join("artifact.o");
    let (file, observed) = artifact(&path);
    let until = Instant::now() + Duration::from_secs(60);
    require_sealed_file(&observed, &file, until).unwrap();
    assert!(
        std::process::Command::new("/bin/chmod")
            .args(["+a", "everyone allow write"])
            .arg(&path)
            .status()
            .unwrap()
            .success()
    );
    assert_eq!(
        file.metadata().unwrap().mode() & 0o7777,
        0o400,
        "actual ACL grants do not alter the POSIX seal bits"
    );
    assert!(require_sealed_file(&observed, &file, until).is_err());
}
#[test]
fn sealed_file_observation_cannot_succeed_after_original_deadline() {
    let inputs = Source::new();
    let (file, observed) = artifact(&inputs.directory.join("artifact.o"));
    assert_eq!(
        require_sealed_file(&observed, &file, Instant::now()).unwrap_err().kind(),
        io::ErrorKind::TimedOut
    );
}

#[test]
fn actual_socket_source_transfer_streams_distinct_terminal_and_ack_have_one_complete_transcript() {
    let inputs = Source::new();
    let request = inputs.request.clone();
    let digest = [7; 32];
    let (left, right) = UnixStream::pair().unwrap();
    let mut client = Channel::new(left).unwrap();
    let until = Instant::now() + Duration::from_secs(60);
    let server = std::thread::spawn(move || {
        let mut channel = Channel::new(right.try_clone().unwrap()).unwrap();
        channel
            .send(
                &object::Event::Prepared(Box::new(object::tests::prepared(&request)))
                    .encode(&request, digest)
                    .unwrap(),
                until,
            )
            .unwrap();
        let received =
            object::transport::receive_source(&mut channel, &request, until, || Ok(())).unwrap();
        assert_eq!(received.len(), 2);
        for event in [
            object::Event::Started(crate::bootstrap_graph::query::tests::started()),
            object::Event::Output {
                stream: object::Stream::Stdout,
                offset: 0,
                bytes: vec![0, 255, 1],
            },
            object::Event::Eof { stream: object::Stream::Stdout, bytes: 3 },
            object::Event::Eof { stream: object::Stream::Stderr, bytes: 0 },
        ] {
            channel.send(&event.encode(&request, digest).unwrap(), until).unwrap();
        }
        let completion = MetadataCompletion {
            finished: crate::StatusFrame {
                root_attempt: request.key.graph.query.binding.root_attempt,
                member_attempt: request.key.operation,
                status: crate::Status::Finished {
                    outcome: crate::Outcome::Exit(0),
                    cause: crate::CompletionCause::Exited,
                    runtime_ns: 8,
                },
            },
            inputs_unchanged: Ok(()),
        };
        let artifact = MetadataFile {
            path: request.output_path(),
            sha256: [9; 32],
            bytes: 544,
            device: 1,
            inode: 14,
        };
        channel
            .send(
                &object::Terminal::Completed {
                    completion: Box::new(completion),
                    observation: crate::accounting::Observation::uncollected(),
                    artifact: Some(artifact),
                }
                .encode(&request, digest)
                .unwrap(),
                until,
            )
            .unwrap();
        right.shutdown(std::net::Shutdown::Write).unwrap();
        assert_eq!(channel.receive(until).unwrap(), [1]);
    });
    let mut transcript = Transcript::new();
    let (completion, accounting, artifact) = receive_operation(
        &mut client,
        ExpectedPreparation { request: &inputs.request, digest, host: "host", boot: "boot" },
        until,
        &mut transcript,
        &[inputs.root.as_fd(), inputs.file.as_fd()],
        || Ok(()),
    )
    .unwrap();
    require_final_eof(&mut client, until, &mut transcript).unwrap();
    assert!(matches!(
        completion.finished.status,
        crate::Status::Finished { outcome: crate::Outcome::Exit(0), .. }
    ));
    assert!(accounting.cpu_times.is_none() && accounting.peak_rss_bytes.is_none());
    assert_eq!(artifact.unwrap().path, inputs.request.output_path());
    assert_eq!(transcript.stdout, [0, 255, 1]);
    assert!(transcript.stderr.is_empty());
    assert_eq!(transcript.frames_seen, 6);
    client.send(&[1], until).unwrap();
    server.join().unwrap();
    // This is the receive DATA reducer only. It cannot construct the separate
    // CompletedObjectCompile that requires the original pinned accepted Host.
}

fn prepared() -> object::Event {
    object::Event::Prepared(Box::new(object::tests::prepared(&object::tests::request())))
}
fn started() -> object::Event {
    object::Event::Started(crate::bootstrap_graph::query::tests::started())
}
#[test]
fn object_transcript_requires_prepared_start_contiguous_output_and_both_original_eofs() {
    let mut transcript = Transcript::new();
    assert!(transcript.event(started()).is_err());
    assert!(transcript.event(prepared()).is_err(), "failed transcript cannot recover");
    let mut transcript = Transcript::new();
    transcript.event(prepared()).unwrap();
    transcript.event(started()).unwrap();
    transcript
        .event(object::Event::Output {
            stream: object::Stream::Stdout,
            offset: 0,
            bytes: vec![0, 255],
        })
        .unwrap();
    assert!(transcript.complete().is_err());
    transcript.event(object::Event::Eof { stream: object::Stream::Stdout, bytes: 2 }).unwrap();
    assert!(transcript.complete().is_err());
    transcript.event(object::Event::Eof { stream: object::Stream::Stderr, bytes: 0 }).unwrap();
    transcript.complete().unwrap();
    assert_eq!(transcript.stdout, [0, 255]);
    assert!(
        transcript
            .event(object::Event::Output {
                stream: object::Stream::Stdout,
                offset: 2,
                bytes: vec![1]
            })
            .is_err()
    );
    assert!(transcript.complete().is_err());
}
#[test]
fn malformed_prepared_policy_is_retained_before_decode_and_no_source_is_offered() {
    let request = object::tests::request();
    let digest = [7; 32];
    let mut bytes = prepared().encode(&request, digest).unwrap();
    let offset = bytes
        .windows(object::PREPARED_POLICY.len())
        .position(|s| s == object::PREPARED_POLICY.as_bytes())
        .unwrap();
    bytes[offset] ^= 1;
    let (left, right) = UnixStream::pair().unwrap();
    let mut sender = Channel::new(left).unwrap();
    let mut receiver = Channel::new(right).unwrap();
    let until = Instant::now() + Duration::from_secs(60);
    sender.send(&bytes, until).unwrap();
    let (a, b) = UnixStream::pair().unwrap();
    let mut transcript = Transcript::new();
    assert!(
        receive_operation(
            &mut receiver,
            ExpectedPreparation { request: &request, digest, host: "host", boot: "boot" },
            until,
            &mut transcript,
            &[a.as_fd(), b.as_fd()],
            || panic!("malformed Prepared must not offer source")
        )
        .is_err()
    );
    assert!(receiver.poisoned());
    assert_eq!(transcript.frames_seen, 1);
    assert!(transcript.raw.windows(bytes.len()).any(|part| part == bytes));
    assert!(transcript.prepared.is_none() && transcript.started.is_none());
    assert!(!sender.ready_to_receive().unwrap());
}
#[test]
fn old_query_terminal_and_wrong_operation_never_create_object_completion() {
    let request = object::tests::request();
    let digest = [7; 32];
    let query = crate::bootstrap_graph::query::tests::request();
    let frames = [
        crate::bootstrap_graph::query::tests::terminal(&query).encode(&query, digest).unwrap(),
        object::Terminal::Unknown { reason: "original producer remains unresolved".into() }
            .encode(&request, [8; 32])
            .unwrap(),
    ];
    for frame in frames {
        let (left, right) = UnixStream::pair().unwrap();
        let mut sender = Channel::new(left).unwrap();
        let mut receiver = Channel::new(right).unwrap();
        let until = Instant::now() + Duration::from_secs(60);
        sender.send(&frame, until).unwrap();
        let (a, b) = UnixStream::pair().unwrap();
        let mut transcript = Transcript::new();
        assert!(
            receive_operation(
                &mut receiver,
                ExpectedPreparation { request: &request, digest, host: "host", boot: "boot" },
                until,
                &mut transcript,
                &[a.as_fd(), b.as_fd()],
                || Ok(())
            )
            .is_err()
        );
        assert!(transcript.failed && receiver.poisoned());
        assert!(transcript.bytes_seen >= frame.len() as u64);
        assert_eq!(transcript.frames_seen, 1);
        assert!(transcript.complete().is_err());
    }
}
#[test]
fn overflow_and_duplicate_eof_are_permanent_and_keep_actual_prefix() {
    let mut transcript = Transcript::new();
    transcript.event(prepared()).unwrap();
    transcript.event(started()).unwrap();
    transcript
        .event(object::Event::Output {
            stream: object::Stream::Stderr,
            offset: 0,
            bytes: vec![3; object::MAX_OUTPUT as usize],
        })
        .unwrap();
    assert!(
        transcript
            .event(object::Event::Output {
                stream: object::Stream::Stderr,
                offset: object::MAX_OUTPUT,
                bytes: vec![4]
            })
            .is_err()
    );
    assert_eq!(transcript.stderr.len(), object::MAX_OUTPUT as usize);
    assert!(
        transcript
            .event(object::Event::Eof { stream: object::Stream::Stderr, bytes: object::MAX_OUTPUT })
            .is_err()
    );
    let mut transcript = Transcript::new();
    transcript.event(prepared()).unwrap();
    transcript.event(started()).unwrap();
    transcript.event(object::Event::Eof { stream: object::Stream::Stdout, bytes: 0 }).unwrap();
    assert!(
        transcript.event(object::Event::Eof { stream: object::Stream::Stdout, bytes: 0 }).is_err()
    );
    assert!(transcript.complete().is_err());
}
