// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

use std::fs::{File, Permissions};
use std::io::Read as _;
use std::os::unix::fs::{DirBuilderExt as _, PermissionsExt as _};
use std::os::unix::process::{CommandExt as _, ExitStatusExt as _};
use std::path::PathBuf;
use std::time::Duration;

use sha2::{Digest as _, Sha256};

use super::*;

#[test]
fn process_state_validation_keeps_fault_and_original_image_refusals() {
    // Private data exercises the same validator after each explicit lock; it
    // does not construct a live coordinator, reservation or input owner.
    let actual = process::read_identity(std::process::id()).unwrap();
    let mut state = ProcessState {
        original: actual,
        pending: 0,
        held: 0,
        held_sources: 0,
        held_outputs: 0,
        held_directories: 0,
        faulted: false,
    };
    check_process_state(&state, actual).unwrap();
    for changed in [
        process::Identity { pid: actual.pid ^ 1, ..actual },
        process::Identity { birth: actual.birth ^ 1, ..actual },
        process::Identity { unique_id: actual.unique_id ^ 1, ..actual },
        process::Identity { exec_version: actual.exec_version ^ 1, ..actual },
    ] {
        assert_eq!(
            check_process_state(&state, changed).unwrap_err().kind(),
            io::ErrorKind::WouldBlock,
        );
    }
    state.faulted = true;
    assert_eq!(check_process_state(&state, actual).unwrap_err().kind(), io::ErrorKind::WouldBlock,);
}

struct Scratch(PathBuf);
impl Scratch {
    fn new() -> Self {
        let parent = process::account_home()
            .unwrap()
            .join(".cache/trust/native-fd-admission-fixtures.noindex");
        std::fs::create_dir_all(&parent).unwrap();
        // Parallel tests can read one clock microsecond; the sequence keeps each fixture its own.
        static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
        let path = parent.join(format!(
            "{}-{}-{}",
            std::process::id(),
            std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos(),
            NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
        ));
        std::fs::DirBuilder::new().mode(0o700).create(&path).unwrap();
        eprintln!("native descriptor original fixture={}", path.display());
        Self(path)
    }
}
impl Drop for Scratch {
    fn drop(&mut self) {
        if std::thread::panicking() {
            eprintln!("retained native descriptor failed input={}", self.0.display());
        } else {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }
}
fn fixture() -> (Scratch, Arc<HeldProgram>) {
    let root = Scratch::new();
    let image = root.0.join("image");
    std::fs::create_dir_all(image.join("bin")).unwrap();
    let target = image.join("lib/rustlib/aarch64-apple-darwin/lib");
    std::fs::create_dir_all(&target).unwrap();
    let program = image.join("bin/trustc");
    // Genuine native image is read, never executed from this copied path.
    // Target files are input-custody data, not a functional or fabricated SDK.
    std::fs::copy(std::env::current_exe().unwrap(), &program).unwrap();
    std::fs::set_permissions(&program, Permissions::from_mode(0o555)).unwrap();
    for index in 0..507 {
        std::fs::write(target.join(format!("original-{index}")), b"original bytes").unwrap();
    }
    let mut input = File::open(&program).unwrap();
    let mut hash = Sha256::new();
    let mut bytes = [0; 65536];
    loop {
        let n = input.read(&mut bytes).unwrap();
        if n == 0 {
            break;
        }
        hash.update(&bytes[..n]);
    }
    drop(input);
    let digest: [u8; 32] = hash.finalize().into();
    let held = HeldProgram::open(&image, &program, &digest, deadline()).unwrap();
    (root, Arc::new(held))
}
fn deadline() -> Instant {
    Instant::now() + Duration::from_secs(60)
}

struct Actor {
    child: std::process::Child,
    readers: Vec<std::thread::JoinHandle<Vec<u8>>>,
}
impl Drop for Actor {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
        for reader in self.readers.drain(..) {
            let _ = reader.join();
        }
    }
}
fn reader(stream: impl std::io::Read + Send + 'static) -> std::thread::JoinHandle<Vec<u8>> {
    std::thread::spawn(move || {
        let mut output = Vec::new();
        stream.take(1024 * 1024 + 1).read_to_end(&mut output).unwrap();
        output
    })
}
const MODE: &str = "TRUST_NATIVE_DESCRIPTOR_LIFETIME_ACTOR";
const TEST: &str = "descriptors::tests::native_shared_descriptor_lifetimes_and_process_boundaries";
const MARKER: &str = "NATIVE_DESCRIPTOR_LIFETIME_ASSERTIONS_PASSED";
fn run(mode: &str) {
    let mut child = std::process::Command::new(std::env::current_exe().unwrap())
        .args(["--exact", TEST, "--nocapture"])
        .env(MODE, mode)
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .unwrap();
    let readers = vec![reader(child.stdout.take().unwrap()), reader(child.stderr.take().unwrap())];
    let mut actor = Actor { child, readers };
    let end = deadline();
    let status = loop {
        if let Some(status) = actor.child.try_wait().unwrap() {
            break status;
        }
        assert!(Instant::now() < end, "native descriptor actor hang detector expired");
        std::thread::sleep(Duration::from_millis(5));
    };
    let stdout = actor.readers.remove(0).join().unwrap();
    let stderr = actor.readers.remove(0).join().unwrap();
    assert!(stdout.len() <= 1024 * 1024 && stderr.len() <= 1024 * 1024);
    let stdout = String::from_utf8(stdout).unwrap();
    let stderr = String::from_utf8(stderr).unwrap();
    assert!(status.success(), "mode={mode} stdout={stdout} stderr={stderr}");
    assert!(
        stdout.contains("running 1 test") && stdout.contains("1 passed; 0 failed"),
        "wrong test selector: {stdout}"
    );
    assert_eq!(stderr.matches(MARKER).count(), 1, "native actor assertions incomplete: {stderr}");
}
fn soft_256() {
    let mut limit = limits().unwrap();
    assert!(
        limit.rlim_cur >= 256 && limit.rlim_max >= 1024,
        "COULD NOT RUN exact native limit control: inherited limits too low; no test raise"
    );
    limit.rlim_cur = 256;
    assert_eq!(unsafe { libc::setrlimit(libc::RLIMIT_NOFILE, &limit) }, 0);
}

#[test]
fn native_shared_descriptor_lifetimes_and_process_boundaries() {
    let Some(mode) = std::env::var_os(MODE) else {
        for mode in [
            "retained-target",
            "paired-envelope",
            "concurrent",
            "plan-failure",
            "partial-failure",
            "fork",
            "exec",
            "packages",
            "package-capacity",
            "outputs",
            "received-outputs",
            "output-capacity",
            "source-scopes",
            "directories",
            "directory-capacity",
            "root-directories",
            "root-directory-capacity",
        ] {
            run(mode);
        }
        return;
    };
    match mode.to_str().unwrap() {
        "received-outputs" => {
            let root = Scratch::new();
            std::fs::create_dir_all(root.0.join("debug/deps")).unwrap();
            std::fs::create_dir_all(root.0.join("private/unit")).unwrap();
            let selected = root.0.join("debug/deps/input.rmeta");
            std::fs::write(&selected, b"actual original bytes").unwrap();
            let output = HeldOutputRoot::open(&root.0, deadline()).unwrap();
            let budget = DescriptorBudget::for_preparation(2, 0).unwrap();
            let observer = DescriptorBudget::for_preparation(1, 0).unwrap();
            let before = budget.observation().unwrap();
            let incoming = budget.reserve_original_inputs(2).unwrap();
            let file = File::open(&selected).unwrap();
            let directory = File::open(root.0.join("private/unit")).unwrap();
            let file = budget
                .capture_output_file_from_original(&output, &selected, file.into(), deadline())
                .unwrap();
            let directory = budget
                .capture_output_directory_from_original(
                    &output,
                    &root.0.join("private/unit"),
                    directory.into(),
                    deadline(),
                )
                .unwrap();
            drop(incoming);
            let admitted = observer.observation().unwrap();
            assert_eq!(admitted.pending, before.pending);
            assert_eq!(admitted.held_outputs, before.held_outputs + 3);
            assert_eq!(admitted.held_directories, before.held_directories + 2);
            std::thread::scope(|scope| {
                let gate = Arc::new(std::sync::Barrier::new(3));
                for _ in 0..2 {
                    let file = Arc::clone(&file);
                    let directory = Arc::clone(&directory);
                    let gate = Arc::clone(&gate);
                    scope.spawn(move || {
                        gate.wait();
                        for _ in 0..8 {
                            file.validate(deadline()).unwrap();
                            directory.validate(deadline()).unwrap();
                        }
                    });
                }
                gate.wait();
            });
            let failed = Arc::clone(&file);
            std::fs::write(&selected, b"late mutation").unwrap();
            assert!(failed.validate(deadline()).is_err());
            drop(file);
            drop(directory);
            drop(budget);
            assert_eq!(observer.observation().unwrap().held_outputs, before.held_outputs + 3);
            assert!(failed.validate(deadline()).is_err());
            drop(failed);
            let after = observer.observation().unwrap();
            assert_eq!(
                (after.pending, after.held_outputs, after.held_directories, after.occupied),
                (before.pending, before.held_outputs, before.held_directories, before.occupied)
            );
        }
        "root-directories" => {
            let root = Scratch::new();
            let output = HeldOutputRoot::open(&root.0, deadline()).unwrap();
            let path = root.0.join("private/unit");
            let budget = DescriptorBudget::for_preparation(1, 0).unwrap();
            let observer = DescriptorBudget::for_preparation(1, 0).unwrap();
            let before = budget.observation().unwrap();
            let original = budget.prepare_output_directory(&output, &path, deadline()).unwrap();
            assert_eq!(original.output_root(), output.path());
            assert_eq!(original.path(), path);
            let captured = observer.observation().unwrap();
            assert_eq!(captured.pending, before.pending);
            assert_eq!(captured.held_directories, before.held_directories + 2);
            let repeated = budget.prepare_output_directory(&output, &path, deadline());
            assert!(matches!(repeated, Err(error) if error.kind() == io::ErrorKind::AlreadyExists));
            assert_eq!(observer.observation().unwrap().held_directories, captured.held_directories);
            let retained = Arc::clone(&original);
            std::thread::scope(|scope| {
                scope.spawn(|| original.validate(deadline()).unwrap());
                retained.validate(deadline()).unwrap();
            });
            drop(original);
            drop(budget);
            std::fs::rename(&path, root.0.join("retained-unit")).unwrap();
            std::fs::create_dir(&path).unwrap();
            assert!(retained.validate(deadline()).is_err());
            assert!(retained.descriptor(deadline()).is_err());
            assert_eq!(observer.observation().unwrap().held_directories, captured.held_directories);
            drop(retained);
            let after = observer.observation().unwrap();
            assert_eq!(
                (after.pending, after.held_directories, after.occupied),
                (before.pending, before.held_directories, before.occupied)
            );
        }
        "root-directory-capacity" => {
            let root = Scratch::new();
            let output = HeldOutputRoot::open(&root.0, deadline()).unwrap();
            let selected = root.0.join("not-created/private-unit");
            let mut limit = limits().unwrap();
            limit.rlim_cur = 256;
            limit.rlim_max = 256;
            assert_eq!(unsafe { libc::setrlimit(libc::RLIMIT_NOFILE, &limit) }, 0);
            let budget = DescriptorBudget::for_preparation(1, 0).unwrap();
            let initial = budget.observation().unwrap();
            let room = (initial.soft as usize)
                .saturating_sub(initial.occupied + initial.pending + RESERVE);
            let demand = HeldRootDirectory::capture_descriptor_bound();
            let _pressure = if room >= demand {
                Some(budget.reserve_original_inputs(room - demand + 1).unwrap())
            } else {
                None
            };
            let before = budget.observation().unwrap();
            let result = budget.prepare_output_directory(&output, &selected, deadline());
            assert!(
                matches!(result, Err(error) if matches!(error.kind(), io::ErrorKind::WouldBlock | io::ErrorKind::Unsupported))
            );
            assert!(
                !root.0.join("not-created").exists(),
                "admission refusal must precede any mkdir"
            );
            let after = budget.observation().unwrap();
            assert_eq!(
                (after.pending, after.held_directories, after.occupied),
                (before.pending, before.held_directories, before.occupied)
            );
        }
        "directories" => {
            let root = Scratch::new();
            let path = root.0.join("mutable-bookkeeping");
            std::fs::create_dir(&path).unwrap();
            let budget = DescriptorBudget::for_preparation(1, 0).unwrap();
            let observer = DescriptorBudget::for_preparation(1, 0).unwrap();
            let before = budget.observation().unwrap();
            let original = budget.capture_directory(&path, deadline()).unwrap();
            let captured = observer.observation().unwrap();
            assert!(captured.held_directories > before.held_directories);
            assert_eq!(captured.pending, before.pending);
            std::fs::write(path.join("new-fingerprint"), b"mutable membership").unwrap();
            std::thread::scope(|scope| {
                let shared = Arc::clone(&original);
                scope.spawn(move || shared.validate(deadline()).unwrap());
                original.validate(deadline()).unwrap();
            });
            assert_eq!(observer.observation().unwrap().occupied, captured.occupied);
            let failed = Arc::clone(&original);
            std::fs::rename(&path, root.0.join("retained-original")).unwrap();
            std::fs::create_dir(&path).unwrap();
            assert!(failed.validate(deadline()).is_err());
            drop(original);
            drop(budget);
            assert_eq!(observer.observation().unwrap().held_directories, captured.held_directories);
            drop(failed);
            let after = observer.observation().unwrap();
            assert_eq!(
                (after.pending, after.held_directories, after.occupied),
                (before.pending, before.held_directories, before.occupied)
            );
            let missing = root.0.join("absent");
            assert!(observer.capture_directory(&missing, deadline()).is_err());
            let after = observer.observation().unwrap();
            assert_eq!(
                (after.pending, after.held_directories, after.occupied),
                (before.pending, before.held_directories, before.occupied),
                "partial originals close before their failed preparation charge returns"
            );
        }
        "directory-capacity" => {
            let root = Scratch::new();
            let selected = root.0.join("bookkeeping");
            std::fs::create_dir(&selected).unwrap();
            let mut limit = limits().unwrap();
            limit.rlim_cur = 256;
            limit.rlim_max = 256;
            assert_eq!(unsafe { libc::setrlimit(libc::RLIMIT_NOFILE, &limit) }, 0);
            let budget = DescriptorBudget::for_preparation(1, 0).unwrap();
            let initial = budget.observation().unwrap();
            let room = (initial.soft as usize)
                .saturating_sub(initial.occupied + initial.pending + RESERVE);
            let demand = HeldDirectoryInput::capture_descriptor_bound();
            let _pressure = if room >= demand {
                Some(budget.reserve_original_inputs(room - demand + 1).unwrap())
            } else {
                None
            };
            let before = budget.observation().unwrap();
            let error = match budget.capture_directory(&selected, deadline()) {
                Ok(_) => panic!("directory capture exceeded actual hard capacity"),
                Err(error) => error,
            };
            assert!(matches!(error.kind(), io::ErrorKind::WouldBlock | io::ErrorKind::Unsupported));
            let after = budget.observation().unwrap();
            assert_eq!(
                (after.pending, after.held_directories, after.occupied),
                (before.pending, before.held_directories, before.occupied),
                "capacity refusal must precede opening unpaid original directories"
            );
        }
        "source-scopes" => {
            let root = Scratch::new();
            let selected = root.0.join("package");
            std::fs::create_dir(&selected).unwrap();
            let file = selected.join("lib.rs");
            std::fs::write(&file, b"original").unwrap();
            let budget = DescriptorBudget::for_preparation(1, 0).unwrap();
            let before = budget.observation().unwrap();
            let first_scope = budget.source_scope().unwrap();
            let first = first_scope.capture(&selected, deadline()).unwrap();
            let repeated = first_scope.capture(&selected, deadline()).unwrap();
            assert!(Arc::ptr_eq(&first, &repeated));
            let first_digest = *first.content_digest();
            drop(repeated);
            drop(first_scope);
            assert_eq!(budget.observation().unwrap().held_sources, before.held_sources + 1);
            first.validate(deadline()).unwrap();
            drop(first);
            let closed = budget.observation().unwrap();
            assert_eq!(
                (closed.pending, closed.held_sources, closed.occupied),
                (before.pending, before.held_sources, before.occupied)
            );
            // Only after all old owners close may the next independent Job
            // capture its changed namespace through the SAME capacity budget.
            std::fs::write(&file, b"new independent input version").unwrap();
            let second_scope = budget.source_scope().unwrap();
            let second = second_scope.capture(&selected, deadline()).unwrap();
            assert_ne!(second.content_digest(), &first_digest);
            let shared = second_scope.capture(&selected, deadline()).unwrap();
            assert!(Arc::ptr_eq(&second, &shared));
            drop(shared);
            drop(second);
            drop(second_scope);
            let failed_scope = budget.source_scope().unwrap();
            let alias = selected.join("unowned-link");
            std::os::unix::fs::symlink(&file, &alias).unwrap();
            assert!(failed_scope.capture(&selected, deadline()).is_err());
            std::fs::remove_file(alias).unwrap();
            assert!(
                failed_scope.capture(&selected, deadline()).is_err(),
                "one scope never refreshes failed capture"
            );
            let after = budget.observation().unwrap();
            assert_eq!(
                (after.pending, after.held_sources, after.occupied),
                (before.pending, before.held_sources, before.occupied)
            );
        }
        "outputs" => {
            let root = Scratch::new();
            std::fs::create_dir_all(root.0.join("debug/deps")).unwrap();
            let selected = root.0.join("debug/deps/selected.rmeta");
            std::fs::write(&selected, b"").unwrap();
            let output = HeldOutputRoot::open(&root.0, deadline()).unwrap();
            let budget = DescriptorBudget::for_preparation(2, 0).unwrap();
            let observer = DescriptorBudget::for_preparation(1, 0).unwrap();
            let before = budget.observation().unwrap();
            let original = budget.capture_output_file(&output, &selected, deadline()).unwrap();
            assert_eq!(original.observation().bytes, 0, "zero is DATA, not valid Rust metadata");
            let captured = observer.observation().unwrap();
            assert_eq!(captured.pending, before.pending);
            assert_eq!(captured.held_outputs, before.held_outputs + 3);
            assert_eq!(original.admission_observation().shared_descriptors, 3);
            std::thread::scope(|scope| {
                let gate = Arc::new(std::sync::Barrier::new(3));
                for _ in 0..2 {
                    let original = Arc::clone(&original);
                    let gate = Arc::clone(&gate);
                    scope.spawn(move || {
                        gate.wait();
                        for _ in 0..8 {
                            original.validate(deadline()).unwrap();
                        }
                    });
                }
                gate.wait();
            });
            assert_eq!(observer.observation().unwrap().occupied, captured.occupied);
            let failed_consumer = Arc::clone(&original);
            std::fs::write(&selected, b"replacement").unwrap();
            assert!(failed_consumer.validate(deadline()).is_err());
            drop(original);
            drop(budget);
            assert_eq!(observer.observation().unwrap().held_outputs, before.held_outputs + 3);
            assert!(failed_consumer.descriptor(deadline()).is_err());
            drop(failed_consumer);
            let after = observer.observation().unwrap();
            assert_eq!(
                (after.pending, after.held_outputs, after.occupied),
                (before.pending, before.held_outputs, before.occupied)
            );
            output.validate(deadline()).unwrap();
        }
        "output-capacity" => {
            let root = Scratch::new();
            std::fs::write(root.0.join("selected.rmeta"), b"original").unwrap();
            let output = HeldOutputRoot::open(&root.0, deadline()).unwrap();
            let mut limit = limits().unwrap();
            limit.rlim_cur = 256;
            limit.rlim_max = 256;
            assert_eq!(unsafe { libc::setrlimit(libc::RLIMIT_NOFILE, &limit) }, 0);
            let budget = DescriptorBudget::for_preparation(1, 0).unwrap();
            let initial = budget.observation().unwrap();
            let room = (initial.soft as usize)
                .saturating_sub(initial.occupied + initial.pending + RESERVE);
            let demand = HeldRootFile::capture_descriptor_bound();
            let _pressure = if room >= demand {
                Some(budget.reserve_original_inputs(room - demand + 1).unwrap())
            } else {
                None
            };
            let before = budget.observation().unwrap();
            let error = match budget.capture_output_file(
                &output,
                &root.0.join("selected.rmeta"),
                deadline(),
            ) {
                Ok(_) => panic!("new output originals exceeded actual hard capacity"),
                Err(error) => error,
            };
            assert!(matches!(error.kind(), io::ErrorKind::WouldBlock | io::ErrorKind::Unsupported));
            let after = budget.observation().unwrap();
            assert_eq!(
                (after.pending, after.held_outputs, after.occupied),
                (before.pending, before.held_outputs, before.occupied),
                "refused capture never opened unpaid originals or leaked its charge"
            );
            output.validate(deadline()).unwrap();
        }
        "packages" => {
            let root = Scratch::new();
            let source = root.0.join("source");
            std::fs::create_dir_all(source.join("src/empty")).unwrap();
            for name in ["Cargo.toml", "src/lib.rs", ".hidden"] {
                std::fs::write(source.join(name), b"original").unwrap();
            }
            let budget = DescriptorBudget::for_preparation(2, 0).unwrap();
            let other_budget = DescriptorBudget::for_preparation(1, 0).unwrap();
            let before = budget.observation().unwrap();
            let owners = std::thread::scope(|scope| {
                let gate = Arc::new(std::sync::Barrier::new(3));
                let workers = (0..2)
                    .map(|_| {
                        let budget = &budget;
                        let source = &source;
                        let gate = gate.clone();
                        scope.spawn(move || {
                            gate.wait();
                            budget.capture_source(source, deadline()).unwrap()
                        })
                    })
                    .collect::<Vec<_>>();
                gate.wait();
                workers.into_iter().map(|worker| worker.join().unwrap()).collect::<Vec<_>>()
            });
            assert!(Arc::ptr_eq(&owners[0], &owners[1]));
            let captured = budget.observation().unwrap();
            for _ in 0..8 {
                let reused = budget.capture_source(&source, deadline()).unwrap();
                assert!(Arc::ptr_eq(&owners[0], &reused));
                reused.validate(deadline()).unwrap();
            }
            let after_reuse = budget.observation().unwrap();
            assert_eq!(
                (after_reuse.held_sources, after_reuse.occupied),
                (captured.held_sources, captured.occupied)
            );
            assert_eq!(budget.observation().unwrap().held_sources, before.held_sources + 3);
            let member = other_budget.try_root().unwrap().unwrap();
            assert_eq!(
                other_budget.observation().unwrap().pending,
                before.pending + EXTRA_PER_ROOT
            );
            let failed_command = owners[0].clone();
            std::fs::write(source.join("src/lib.rs"), b"changed").unwrap();
            assert!(failed_command.validate(deadline()).is_err());
            assert!(budget.capture_source(&source, deadline()).is_err());
            drop(owners);
            drop(budget);
            drop(member);
            assert_eq!(other_budget.observation().unwrap().held_sources, before.held_sources + 3);
            drop(failed_command);
            let after = other_budget.observation().unwrap();
            assert_eq!(
                (after.pending, after.held_sources, after.occupied),
                (before.pending, before.held_sources, before.occupied)
            );
        }
        "package-capacity" => {
            let root = Scratch::new();
            let source = root.0.join("source");
            std::fs::create_dir(&source).unwrap();
            for index in 0..507 {
                std::fs::write(source.join(format!("original-{index}")), b"original").unwrap();
            }
            let mut limit = limits().unwrap();
            limit.rlim_cur = 256;
            limit.rlim_max = 256;
            assert_eq!(unsafe { libc::setrlimit(libc::RLIMIT_NOFILE, &limit) }, 0);
            let budget = DescriptorBudget::for_preparation(2, 0).unwrap();
            let before = budget.observation().unwrap();
            assert!(budget.capture_source(&source, deadline()).is_err());
            let after = budget.observation().unwrap();
            assert_eq!(
                (after.pending, after.held_sources, after.occupied),
                (before.pending, before.held_sources, before.occupied)
            );
            for index in 1..507 {
                std::fs::remove_file(source.join(format!("original-{index}"))).unwrap();
            }
            assert!(
                budget.capture_source(&source, deadline()).is_err(),
                "later smaller input cannot replace a refused original graph capture"
            );
        }
        "paired-envelope" => {
            let (_root, compiler) = fixture();
            soft_256();
            let budget = DescriptorBudget::for_preparation(1, 0).unwrap();
            let plan = HeldRustTargetSysroot::plan(compiler, deadline()).unwrap();
            let target = budget.capture_target(plan, deadline()).unwrap();
            let member = target.try_member().unwrap().unwrap();
            let expected_pair = EXTRA_PER_ROOT
                + trust_resource_provenance::ORIGINAL_CONTROL_DESCRIPTORS + 1;
            let before = budget.observation().unwrap();
            let pair = target.reserve_paired_control().unwrap();
            assert_eq!(budget.observation().unwrap().pending, before.pending + expected_pair);
            assert_eq!(budget.active.load(Ordering::Acquire), 1);
            drop(pair);
            assert_eq!(budget.observation().unwrap().pending, before.pending);
            let pressure = budget.observation().unwrap();
            let ceiling = pressure.occupied + pressure.pending + RESERVE + expected_pair - 1;
            let mut limit = limits().unwrap();
            assert!(ceiling < usize::try_from(limit.rlim_max).unwrap());
            limit.rlim_cur = ceiling as libc::rlim_t;
            limit.rlim_max = ceiling as libc::rlim_t;
            assert_eq!(unsafe { libc::setrlimit(libc::RLIMIT_NOFILE, &limit) }, 0);
            assert!(target.reserve_paired_control().is_err());
            assert_eq!(budget.observation().unwrap().pending, before.pending);
            assert_eq!(budget.active.load(Ordering::Acquire), 1);
            drop(member);
            drop(target);
        }
        "retained-target" => {
            let (_root, compiler) = fixture();
            soft_256();
            let budget = DescriptorBudget::for_preparation(2, 0).unwrap();
            let before = budget.observation().unwrap();
            let plan = HeldRustTargetSysroot::plan(compiler.clone(), deadline()).unwrap();
            let demand = plan.descriptor_demand(deadline()).unwrap();
            assert_eq!(demand, 507);
            let target = budget.capture_target(plan, deadline()).unwrap();
            target.validate(deadline()).unwrap();
            assert_eq!(target.file_observations().count(), 507);
            let admitted = target.admission_observation();
            assert_eq!(admitted.shared_descriptors, demand);
            assert_eq!(admitted.reserved.pending, demand);
            assert_eq!(admitted.materialized.pending, 0);
            assert_eq!(admitted.materialized.held_targets, demand);
            assert!(admitted.materialized.soft > 256);
            assert_eq!(admitted.materialized.hard, before.hard);
            let member = target.try_member().unwrap().unwrap();
            assert_eq!(budget.observation().unwrap().pending, EXTRA_PER_ROOT);
            drop(member);
            let retained_failure = target.clone();
            drop(target);
            std::fs::write(
                compiler.root().join("lib/rustlib/aarch64-apple-darwin/lib/original-0"),
                b"changed bytes!",
            )
            .unwrap();
            assert!(retained_failure.validate(deadline()).is_err());
            let failed = budget.observation().unwrap();
            assert_eq!((failed.pending, failed.held_targets), (0, demand));
            assert!(failed.occupied >= before.occupied + demand);
            drop(retained_failure);
            let after = budget.observation().unwrap();
            assert_eq!((after.pending, after.held_targets), (0, 0));
            assert_eq!(after.occupied, before.occupied);
            assert!(after.soft > 256);
            assert_eq!(after.hard, before.hard);
        }
        "concurrent" => {
            soft_256();
            let first = DescriptorBudget::for_preparation(64, 0).unwrap();
            let second = DescriptorBudget::for_preparation(64, 0).unwrap();
            let start = Arc::new(std::sync::Barrier::new(3));
            let workers = [first.clone(), second.clone()]
                .into_iter()
                .map(|budget| {
                    let start = start.clone();
                    std::thread::spawn(move || {
                        start.wait();
                        let mut held = Vec::new();
                        while let Some(permit) = budget.try_root().unwrap() {
                            held.push(permit);
                        }
                        held
                    })
                })
                .collect::<Vec<_>>();
            start.wait();
            let held = workers.into_iter().map(|worker| worker.join().unwrap()).collect::<Vec<_>>();
            let count = held.iter().map(Vec::len).sum::<usize>();
            let observed = first.observation().unwrap();
            assert!(count > 0);
            assert_eq!(observed.pending, count * EXTRA_PER_ROOT);
            assert!(observed.occupied + observed.pending + RESERVE <= observed.soft as usize);
            assert!(first.try_root().unwrap().is_none() && second.try_root().unwrap().is_none());
            drop(held);
            assert_eq!(first.observation().unwrap().pending, 0);
            assert!(second.try_root().unwrap().is_some());
        }
        "plan-failure" | "partial-failure" => {
            let (_root, compiler) = fixture();
            soft_256();
            let budget = DescriptorBudget::for_preparation(2, 0).unwrap();
            let before = budget.observation().unwrap();
            let plan = HeldRustTargetSysroot::plan(compiler.clone(), deadline()).unwrap();
            let mut pressure = Vec::new();
            let result = budget.capture_target_after_reservation(plan, deadline(), || {
                if mode == "plan-failure" {
                    std::fs::write(
                        compiler.root().join("lib/rustlib/aarch64-apple-darwin/lib/original-0"),
                        b"changed bytes!",
                    )
                    .unwrap();
                } else {
                    // Deliberately unregistered real kernel FD pressure must
                    // refuse materialization, never turn a reservation into GO.
                    loop {
                        match File::open("/dev/null") {
                            Ok(file) => pressure.push(file),
                            Err(error) => {
                                assert_eq!(error.raw_os_error(), Some(libc::EMFILE));
                                break;
                            }
                        }
                    }
                    assert!(pressure.len() > 100);
                    for _ in 0..100 {
                        drop(pressure.pop().unwrap());
                    }
                }
            });
            let error = result.err().expect("actual materialization must refuse");
            if mode == "partial-failure" {
                assert_eq!(error.raw_os_error(), Some(libc::EMFILE));
            }
            drop(pressure);
            let after = budget.observation().unwrap();
            assert_eq!((after.pending, after.held_targets), (0, 0));
            assert_eq!(
                after.occupied, before.occupied,
                "partial original files/directories must close before future charge returns"
            );
            assert!(
                after.soft > 256,
                "process-owned soft pool remains raised after failed materialization"
            );
            assert_eq!(after.hard, before.hard);
            assert!(budget.try_root().unwrap().is_some());
        }
        "fork" => {
            let budget = DescriptorBudget::for_preparation(2, 0).unwrap();
            let permit = budget.try_root().unwrap().unwrap();
            let before = budget.observation().unwrap();
            let (process_coordinator, actual) = process_context().unwrap();
            let guard = process_coordinator.lock().unwrap();
            check_process_state(&guard, actual).unwrap();
            // Deliberately fork with the original mutex held. The child may
            // only run the async-safe PID refusal path then _exit: no allocator,
            // identity I/O or copied mutex may be touched before rejection.
            let child = unsafe { libc::fork() };
            assert!(child >= 0);
            if child == 0 {
                let refused = matches!(budget.try_root(), Err(error) if error.raw_os_error() == Some(libc::EPERM));
                unsafe { libc::_exit(if refused { 0 } else { 74 }) };
            }
            struct OwnedPid(i32, bool);
            impl Drop for OwnedPid {
                fn drop(&mut self) {
                    if !self.1 {
                        unsafe {
                            libc::kill(self.0, libc::SIGKILL);
                        }
                        loop {
                            let result = unsafe { libc::waitpid(self.0, std::ptr::null_mut(), 0) };
                            if result == self.0
                                || result < 0
                                    && std::io::Error::last_os_error().raw_os_error()
                                        != Some(libc::EINTR)
                            {
                                break;
                            }
                        }
                    }
                }
            }
            let mut child = OwnedPid(child, false);
            let end = Instant::now() + Duration::from_secs(10);
            let mut status = 0;
            loop {
                let result = unsafe { libc::waitpid(child.0, &mut status, libc::WNOHANG) };
                assert!(result >= 0);
                if result == child.0 {
                    child.1 = true;
                    break;
                }
                assert!(
                    Instant::now() < end,
                    "fork child touched copied coordinator mutex before original-PID refusal"
                );
                std::thread::sleep(Duration::from_millis(5));
            }
            assert!(std::process::ExitStatus::from_raw(status).success());
            drop(guard);
            assert_eq!(budget.observation().unwrap().pending, before.pending);
            drop(permit);
            assert_eq!(budget.observation().unwrap().pending, 0);
        }
        "exec" => {
            let budget = DescriptorBudget::for_preparation(2, 0).unwrap();
            let _permit = budget.try_root().unwrap().unwrap();
            let before = budget.observation().unwrap();
            assert_eq!(before.pending, EXTRA_PER_ROOT);
            let error = std::process::Command::new(std::env::current_exe().unwrap())
                .args(["--exact", TEST, "--nocapture"])
                .env(MODE, "after-exec")
                .env("TRUST_FD_ORIGINAL_PID", before.process.pid.to_string())
                .env("TRUST_FD_ORIGINAL_BIRTH", before.process.birth.to_string())
                .exec();
            panic!("native self exec failed: {error}");
        }
        "after-exec" => {
            let budget = DescriptorBudget::for_preparation(2, 0).unwrap();
            let actual = budget.observation().unwrap();
            assert_eq!(
                actual.process.pid,
                std::env::var("TRUST_FD_ORIGINAL_PID").unwrap().parse::<u32>().unwrap()
            );
            assert_eq!(
                actual.process.birth,
                std::env::var("TRUST_FD_ORIGINAL_BIRTH").unwrap().parse::<u64>().unwrap()
            );
            assert_eq!(
                (actual.pending, actual.held_targets),
                (0, 0),
                "new native image cannot replay its previous image's reservation"
            );
            assert!(budget.try_root().unwrap().is_some());
        }
        _ => panic!("unsupported native descriptor actor mode"),
    }
    eprintln!("{MARKER}");
}
