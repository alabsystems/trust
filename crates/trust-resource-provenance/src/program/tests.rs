use std::fs;
use std::io::{BufRead as _, Read as _, Write as _};
use std::os::unix::fs::PermissionsExt as _;
use std::process::{Child, Command, Stdio};
use std::sync::{Arc, Mutex};
use std::time::Duration;

use sha2::Sha256;

use super::*;

static SERIAL: Mutex<()> = Mutex::new(());
const ACTOR: &str = "program::tests::native_program_actor";

fn deadline() -> Instant {
    Instant::now() + Duration::from_secs(60)
}

pub(super) fn command(kind: u32, text: &str, fixed: usize) -> Vec<u8> {
    let length = (fixed + text.len() + 1).next_multiple_of(8);
    let mut out = vec![0u8; length];
    out[..4].copy_from_slice(&kind.to_le_bytes());
    out[4..8].copy_from_slice(&(length as u32).to_le_bytes());
    out[8..12].copy_from_slice(&(fixed as u32).to_le_bytes());
    out[fixed..fixed + text.len()].copy_from_slice(text.as_bytes());
    out
}
pub(super) fn image(executable: bool, loads: &[&str], extras: Vec<Vec<u8>>) -> Vec<u8> {
    let mut cmds = extras;
    if executable {
        cmds.push(command(0xe, "/usr/lib/dyld", 12));
    }
    cmds.extend(loads.iter().map(|load| command(0xc, load, 24)));
    let mut out = vec![0u8; 32];
    for (offset, value) in [
        (0, 0xfeed_facfu32),
        (4, 0x0100_000c),
        (12, if executable { 2 } else { 6 }),
        (16, cmds.len() as u32),
        (20, cmds.iter().map(Vec::len).sum::<usize>() as u32),
    ] {
        out[offset..offset + 4].copy_from_slice(&value.to_le_bytes());
    }
    out.extend(cmds.iter().flatten());
    out
}

struct Fixture {
    directory: std::mem::ManuallyDrop<tempfile::TempDir>,
    root: PathBuf,
    program: PathBuf,
    execution_attempted: bool,
    execution_proved: bool,
}
impl Fixture {
    fn new(loads: &[&str]) -> Self {
        // Own build output is a checked private ancestor, unlike world-writable
        // /tmp. No account state or unrelated checkout is created or changed.
        let base = std::env::current_exe().unwrap().parent().unwrap().canonicalize().unwrap();
        let directory = tempfile::Builder::new()
            .prefix("native-program-")
            .suffix(".noindex")
            .tempdir_in(base)
            .unwrap();
        let root = directory.path().join("sdk");
        fs::create_dir(&root).unwrap();
        for name in ["bin", "lib"] {
            fs::create_dir(root.join(name)).unwrap();
        }
        let program = root.join("bin/program");
        fs::write(&program, image(true, loads, Vec::new())).unwrap();
        fs::set_permissions(&program, fs::Permissions::from_mode(0o555)).unwrap();
        Self {
            directory: std::mem::ManuallyDrop::new(directory),
            root,
            program,
            execution_attempted: false,
            execution_proved: false,
        }
    }
    fn digest(&self) -> [u8; 32] {
        Sha256::digest(fs::read(&self.program).unwrap()).into()
    }
    fn open(&self) -> io::Result<HeldProgram> {
        HeldProgram::open(&self.root, &self.program, &self.digest(), deadline())
    }
    fn runtime(&self, name: &str, loads: &[&str]) {
        let path = self.root.join("lib").join(name);
        fs::write(
            &path,
            image(false, loads, vec![command(0x8000_001c, "@loader_path/../lib", 12)]),
        )
        .unwrap();
        fs::set_permissions(path, fs::Permissions::from_mode(0o444)).unwrap();
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        if self.execution_attempted && !self.execution_proved {
            eprintln!("preserved native image without execution proof: {}", self.root.display());
        } else {
            unsafe {
                std::mem::ManuallyDrop::drop(&mut self.directory);
            }
        }
    }
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[test]
fn native_program_retains_exact_transitive_runtime_and_detects_later_changes() {
    let _serial = SERIAL.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    let fixture = Fixture::new(&["@rpath/a.dylib", "/usr/lib/libSystem.B.dylib"]);
    fixture.runtime("a.dylib", &["@rpath/b.dylib", "/usr/lib/libSystem.B.dylib"]);
    fixture.runtime("b.dylib", &["/usr/lib/libSystem.B.dylib"]);
    let pin = fixture.open().unwrap();
    assert_eq!(pin.observation().runtime.len(), 2);
    assert_eq!(pin.observation().system_dependencies, ["/usr/lib/libSystem.B.dylib"]);
    assert_eq!(
        pin.runtime_environment().unwrap(),
        [("DYLD_LIBRARY_PATH".into(), fixture.root.join("lib").into_os_string())]
    );
    pin.validate(deadline()).unwrap();
    let path = fixture.root.join("lib/b.dylib");
    fs::set_permissions(&path, fs::Permissions::from_mode(0o644)).unwrap();
    fs::write(&path, image(false, &["/usr/lib/libSystem.B.dylib"], Vec::new())).unwrap();
    fs::set_permissions(path, fs::Permissions::from_mode(0o444)).unwrap();
    assert!(
        pin.validate(deadline()).is_err(),
        "restored permissions cannot replace original metadata"
    );
}

#[test]
fn system_only_environment_keeps_actual_search_root_and_shadow_custody() {
    let _serial = SERIAL.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    let fixture = Fixture::new(&["/usr/lib/libSystem.B.dylib"]);
    let pin = fixture.open().unwrap();
    assert!(pin.runtime.is_empty());
    assert_eq!(pin.observation().loader_paths, [fixture.root.join("lib")]);
    assert_eq!(pin.observation().system_dependencies, ["/usr/lib/libSystem.B.dylib"]);
    assert!(pin.runtime_environment().unwrap().is_empty());
    pin.validate(deadline()).unwrap();
    // A missing override does not discard the original namespace bookends.
    let lib = fixture.root.join("lib");
    let original = fixture.root.join("original-lib");
    fs::rename(&lib, &original).unwrap();
    fs::create_dir(&lib).unwrap();
    assert!(pin.validate(deadline()).is_err());
    fs::remove_dir(&lib).unwrap();
    fs::rename(&original, &lib).unwrap();
    assert!(pin.validate(deadline()).is_err());
    drop(pin);
    // New capture still refuses a private image shadowing the OS dependency.
    fixture.runtime("libSystem.B.dylib", &[]);
    assert!(fixture.open().is_err());
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[test]
fn unrelated_outer_entries_do_not_change_selected_inputs_but_retargeting_does() {
    let _serial = SERIAL.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    let fixture = Fixture::new(&["/usr/lib/libSystem.B.dylib"]);
    let held = fixture.open().unwrap();
    fs::write(fixture.directory.path().join("unrelated"), b"activity outside the SDK").unwrap();
    held.validate(deadline()).unwrap();
    let outer = fixture.directory.path().to_owned();
    let backup = outer.with_extension("retargeted.noindex");
    fs::rename(&outer, &backup).unwrap();
    fs::create_dir(&outer).unwrap();
    assert!(
        held.validate(deadline()).is_err(),
        "a different ancestor inode cannot replace the original"
    );
    drop(held);
    fs::remove_dir_all(backup).unwrap();
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[test]
fn native_program_refuses_foreign_loader_selection_aliases_and_unbounded_images() {
    let _serial = SERIAL.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    for loads in [
        &["@rpath/missing.dylib"][..],
        &["/foreign/code.dylib"][..],
        &["@loader_path/code.dylib"][..],
        &["/usr/lib/../foreign"][..],
    ] {
        assert!(Fixture::new(loads).open().is_err());
    }
    let fixture = Fixture::new(&["/usr/lib/libSystem.B.dylib"]);
    fixture.runtime("libSystem.B.dylib", &["/usr/lib/libSystem.B.dylib"]);
    assert!(fixture.open().is_err(), "a selected sysroot cannot shadow OS runtime");
    for alteration in 0..8 {
        let fixture = Fixture::new(&["/usr/lib/libSystem.B.dylib"]);
        let mut digest = fixture.digest();
        match alteration {
            0 => {
                fs::set_permissions(&fixture.program, fs::Permissions::from_mode(0o644)).unwrap();
                fs::write(&fixture.program, b"#!/bin/sh\nexit 0\n").unwrap();
                fs::set_permissions(&fixture.program, fs::Permissions::from_mode(0o555)).unwrap();
            }
            1 => fs::set_permissions(&fixture.program, fs::Permissions::from_mode(0o577)).unwrap(),
            2 => {
                let real = fixture.root.join("real");
                fs::rename(&fixture.program, &real).unwrap();
                std::os::unix::fs::symlink(real, &fixture.program).unwrap();
            }
            3 => {
                fs::rename(fixture.root.join("bin"), fixture.root.join("real-bin")).unwrap();
                std::os::unix::fs::symlink("real-bin", fixture.root.join("bin")).unwrap();
            }
            4 => fs::set_permissions(fixture.root.join("bin"), fs::Permissions::from_mode(0o777))
                .unwrap(),
            5 => {
                fs::set_permissions(&fixture.program, fs::Permissions::from_mode(0o755)).unwrap();
                fs::OpenOptions::new()
                    .write(true)
                    .open(&fixture.program)
                    .unwrap()
                    .set_len(MAX_IMAGE + 1)
                    .unwrap();
            }
            6 => {
                fs::set_permissions(&fixture.program, fs::Permissions::from_mode(0o755)).unwrap();
                fs::write(
                    &fixture.program,
                    image(true, &[], vec![command(0x27, "DYLD_INSERT_LIBRARIES=/foreign", 12)]),
                )
                .unwrap();
            }
            7 => {
                fs::set_permissions(&fixture.program, fs::Permissions::from_mode(0o755)).unwrap();
                fs::write(
                    &fixture.program,
                    image(true, &[], vec![command(0x8000_001c, "/foreign", 12)]),
                )
                .unwrap();
            }
            _ => unreachable!(),
        }
        if matches!(alteration, 0 | 6 | 7) {
            digest = fixture.digest();
        }
        assert!(
            HeldProgram::open(&fixture.root, &fixture.program, &digest, deadline()).is_err(),
            "accepted altered native input {alteration}"
        );
    }
    let fixture = Fixture::new(&["/usr/lib/libSystem.B.dylib"]);
    assert!(HeldProgram::open(&fixture.root, &fixture.program, &[0; 32], deadline()).is_err());
    assert!(
        HeldProgram::open(&fixture.root, &fixture.program, &fixture.digest(), Instant::now())
            .is_err()
    );
}

struct OwnedChild(Child, Option<std::thread::JoinHandle<()>>);
impl Drop for OwnedChild {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
        if let Some(reader) = self.1.take() {
            let _ = reader.join();
        }
    }
}
fn actor(fixture: &mut Fixture) -> OwnedChild {
    actor_for(fixture, ACTOR, &[("NATIVE_PROGRAM_ACTOR", "1")])
}
fn actor_for(fixture: &mut Fixture, test: &str, environment: &[(&str, &str)]) -> OwnedChild {
    fixture.execution_attempted = true;
    let current_code = test == "program::tests::native_current_code_actor";
    let stderr = if current_code {
        Stdio::from(File::create(fixture.directory.path().join("current-code-stderr")).unwrap())
    } else {
        Stdio::inherit()
    };
    let mut child = OwnedChild(
        Command::new(&fixture.program)
            .args(["--exact", test, "--nocapture"])
            .env_clear()
            .envs(environment.iter().copied())
            .stderr(stderr)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .unwrap(),
        None,
    );
    let evidence = current_code.then(|| fixture.directory.path().join("current-code-stdout"));
    let output = child.0.stdout.take().unwrap();
    let (send, receive) = std::sync::mpsc::sync_channel(1);
    let reader = std::thread::spawn(move || {
        // Bound even a single unterminated line before allocation.
        let mut read = std::io::BufReader::new(output).take(4097);
        let mut transcript = String::new();
        let mut line = String::new();
        let mut total = 0;
        let mut send = Some(send);
        loop {
            line.clear();
            if read.read_line(&mut line).unwrap() == 0 {
                break;
            }
            total += line.len();
            transcript.push_str(&line);
            if let Some(path) = &evidence {
                fs::write(path, &transcript).unwrap();
            }
            assert!(total <= 4096);
            if line.contains("held-native-program-running")
                && let Some(send) = send.take()
            {
                send.send(()).unwrap();
            }
        }
        if current_code {
            assert!(transcript.contains("running 1 test"));
            assert!(transcript.contains("CURRENT_CODE_ASSERTIONS_PASSED"));
            assert!(transcript.contains("1 passed; 0 failed; 0 ignored"));
        }
    });
    child.1 = Some(reader);
    receive.recv_timeout(Duration::from_secs(60)).unwrap();
    // This stronger actor keeps its failed source/output until all assertions
    // and the exact one-test harness result have actually completed.
    fixture.execution_proved = !current_code;
    child
}
fn finish(child: OwnedChild) {
    finish_before(child, deadline());
}
fn finish_before(mut child: OwnedChild, end: Instant) {
    child.0.stdin.take().unwrap().write_all(b"x").unwrap();
    loop {
        if let Some(status) = child.0.try_wait().unwrap() {
            if let Some(reader) = child.1.take() {
                reader.join().unwrap();
            }
            assert!(status.success());
            break;
        }
        assert!(Instant::now() < end);
        std::thread::sleep(Duration::from_millis(5));
    }
}

#[test]
fn native_program_actor() {
    if std::env::var_os("NATIVE_PROGRAM_ACTOR").is_none() {
        return;
    }
    println!("held-native-program-running");
    std::io::stdout().flush().unwrap();
    let mut byte = [0];
    std::io::stdin().read_exact(&mut byte).unwrap();
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[test]
fn actual_native_child_matches_original_held_image_not_equal_bytes_at_another_path() {
    let _serial = SERIAL.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    let mut fixture = Fixture::new(&[]);
    fs::set_permissions(&fixture.program, fs::Permissions::from_mode(0o755)).unwrap();
    fs::copy(std::env::current_exe().unwrap(), &fixture.program).unwrap();
    fs::set_permissions(&fixture.program, fs::Permissions::from_mode(0o555)).unwrap();
    // Establish actual execution before pinning first-run OS image metadata.
    // Both copies remain at their original paths until a child proved execution.
    finish(actor(&mut fixture));
    let other = fixture.root.join("bin/other");
    fs::copy(&fixture.program, &other).unwrap();
    let digest = fixture.digest();
    let pin = fixture.open().unwrap();
    let other_pin = HeldProgram::open(&fixture.root, &other, &digest, deadline()).unwrap();
    // This actual executable has no private dynamic dependencies. Existing SDK lib/
    // custody is still observed without inventing a DYLD override for its execution.
    assert!(pin.runtime.is_empty());
    assert!(!pin.observation().loader_paths.is_empty());
    assert!(pin.runtime_environment().unwrap().is_empty());
    let child = actor(&mut fixture);
    let identity = process::read_identity(child.0.id()).unwrap();
    pin.validate_loaded(identity, deadline()).unwrap();
    assert!(other_pin.validate_loaded(identity, deadline()).is_err());
    let mut reused = identity;
    reused.birth += 1;
    assert!(pin.validate_loaded(reused, deadline()).is_err());
    finish(child);
    assert!(pin.validate_loaded(identity, deadline()).is_err());
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[test]
#[ignore = "explicit real SDK input profile; no executable is launched"]
fn real_sdk_held_program_profile() {
    let root =
        PathBuf::from(std::env::var_os("TRUST_PROGRAM_TEST_SDK_ROOT").expect("explicit SDK root"));
    for (name, digest_variable) in [
        ("trustc", "TRUST_PROGRAM_TEST_TRUSTC_SHA256"),
        ("targo", "TRUST_PROGRAM_TEST_TARGO_SHA256"),
    ] {
        let digest = std::env::var(digest_variable).unwrap();
        let digest: [u8; 32] = crate::schema::unhex(&digest).unwrap().try_into().unwrap();
        let held =
            HeldProgram::open(&root, &root.join("bin").join(name), &digest, deadline()).unwrap();
        held.validate(deadline()).unwrap();
        println!(
            "actual-sdk-input tool={name} image={} runtime_files={} runtime_bytes={} policy={}",
            held.observation().executable.sha256,
            held.observation().runtime.len(),
            held.observation().runtime.iter().map(|file| file.bytes).sum::<u64>(),
            held.observation().policy
        );
    }
}

fn write_output(path: &Path, bytes: &[u8], executable: bool) {
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, bytes).unwrap();
    fs::set_permissions(path, fs::Permissions::from_mode(if executable { 0o555 } else { 0o444 }))
        .unwrap();
}

#[test]
fn produced_inputs_keep_original_output_root_across_compilation_and_hold_both_runtime_roots() {
    let _serial = SERIAL.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    let fixture = Fixture::new(&["/usr/lib/libSystem.B.dylib"]);
    fixture.runtime("sdk.dylib", &["/usr/lib/libSystem.B.dylib"]);
    let sdk = Arc::new(fixture.open().unwrap());
    let output = fixture.directory.path().join("outputs");
    fs::create_dir(&output).unwrap();
    let (original, mut evidence) =
        produced::HeldOutputRoot::open_with_evidence(&output, &sdk, [1; 16], 64, 2, deadline())
            .unwrap();
    // Inputs appear after the original root was captured, as compiler output.
    let program = output.join("debug/build/package/hash/out/test-program");
    let deps = output.join("debug/deps");
    write_output(
        &program,
        &image(
            true,
            &["@rpath/local.dylib", "/usr/lib/libSystem.B.dylib"],
            vec![command(0x8000_001c, deps.to_str().unwrap(), 12)],
        ),
        true,
    );
    write_output(
        &deps.join("local.dylib"),
        &image(false, &["@rpath/sdk.dylib"], vec![command(0x8000_001c, "@loader_path", 12)]),
        false,
    );
    let digest = Sha256::digest(fs::read(&program).unwrap()).into();
    let held = original
        .program(Arc::clone(&sdk), &program, &digest, std::slice::from_ref(&deps), deadline())
        .unwrap();
    assert_eq!(held.program(), program);
    assert_eq!(held.output_root(), output);
    assert_eq!(held.observation().policy, produced::RUNTIME_POLICY);
    assert_eq!(held.observation().runtime.len(), 2);
    let mut prefix = evidence.create(OsStr::new("action.stderr"), 64, deadline()).unwrap();
    assert_eq!(prefix.append(b"raw\0\xff", deadline()).unwrap(), 5);
    prefix.sync_prefix(deadline()).unwrap();
    held.validate(deadline()).unwrap();
    assert!(HeldProgram::open(&output, &program, &digest, deadline()).is_err());
    let moved = output.with_extension("moved");
    fs::rename(&output, &moved).unwrap();
    fs::create_dir(&output).unwrap();
    assert!(original.validate(deadline()).is_err());
    assert!(held.validate(deadline()).is_err());
    assert!(held.executable_descriptor(deadline()).is_err());
}

#[test]
fn produced_inputs_refuse_aliased_ambiguous_shadowed_or_escaping_loader_inputs() {
    let _serial = SERIAL.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    for altered in 0..7 {
        let fixture = Fixture::new(&["/usr/lib/libSystem.B.dylib"]);
        if altered == 3 {
            fixture.runtime("runtime.dylib", &["/usr/lib/libSystem.B.dylib"]);
        }
        let sdk = Arc::new(fixture.open().unwrap());
        let output = fixture.directory.path().join("outputs");
        fs::create_dir(&output).unwrap();
        let original = produced::HeldOutputRoot::open(&output, deadline()).unwrap();
        let program = output.join("unit/out/test-program");
        let deps = output.join("deps");
        fs::create_dir(&deps).unwrap();
        let mut extra = Vec::new();
        if altered == 4 {
            extra.push(command(0x8000_001c, "/foreign", 12));
        }
        let load = if altered == 6 { "/usr/lib/libSystem.B.dylib" } else { "@rpath/runtime.dylib" };
        write_output(&program, &image(true, &[load], extra), true);
        let runtime = deps.join(if altered == 6 { "libSystem.B.dylib" } else { "runtime.dylib" });
        write_output(&runtime, &image(false, &["/usr/lib/libSystem.B.dylib"], Vec::new()), false);
        match altered {
            0 => {
                fs::hard_link(&program, output.join("program-alias")).unwrap();
            }
            1 => {
                fs::hard_link(&runtime, output.join("runtime-alias")).unwrap();
            }
            2 => {
                fs::rename(&runtime, output.join("runtime-moved")).unwrap();
                std::os::unix::fs::symlink(output.join("runtime-moved"), &runtime).unwrap();
            }
            3 | 4 | 6 => {}
            5 => {}
            _ => unreachable!(),
        }
        let digest = Sha256::digest(fs::read(&program).unwrap()).into();
        let roots = if altered == 5 { vec![fixture.root.join("lib")] } else { vec![deps] };
        assert!(
            original.program(sdk, &program, &digest, &roots, deadline()).is_err(),
            "altered {altered}"
        );
    }
}

#[test]
fn produced_inputs_match_the_actual_original_child_image_and_reject_later_byte_changes() {
    let _serial = SERIAL.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    let mut fixture = Fixture::new(&["/usr/lib/libSystem.B.dylib"]);
    let sdk = Arc::new(fixture.open().unwrap());
    let output = fixture.directory.path().join("outputs");
    fs::create_dir(&output).unwrap();
    let original = produced::HeldOutputRoot::open(&output, deadline()).unwrap();
    let program = output.join("unit/out/test-program");
    fs::create_dir_all(program.parent().unwrap()).unwrap();
    fs::copy(std::env::current_exe().unwrap(), &program).unwrap();
    fs::set_permissions(&program, fs::Permissions::from_mode(0o555)).unwrap();
    fixture.program = program.clone();
    finish(actor(&mut fixture));
    let digest = fixture.digest();
    let held = original.program(sdk, &program, &digest, &[], deadline()).unwrap();
    let child = actor(&mut fixture);
    held.validate_loaded(process::read_identity(child.0.id()).unwrap(), deadline()).unwrap();
    finish(child);
    // Actual native image, borrowed from its original input owner after child
    // retirement. This descriptor observation is not another execution grant.
    let borrowed = held.executable_descriptor(deadline()).unwrap();
    let actual = fs::File::from(borrowed.try_clone_to_owned().unwrap()).metadata().unwrap();
    assert_eq!(actual.dev(), held.observation().executable.device);
    assert_eq!(actual.ino(), held.observation().executable.inode);
    // SAFETY: these commands only observe flags on the live borrowed original.
    let flags = unsafe { libc::fcntl(borrowed.as_raw_fd(), libc::F_GETFL) };
    assert!(flags >= 0);
    assert_eq!(flags & libc::O_ACCMODE, libc::O_RDONLY);
    // SAFETY: same live borrowed description, no descriptor or flag mutation.
    let descriptor_flags = unsafe { libc::fcntl(borrowed.as_raw_fd(), libc::F_GETFD) };
    assert!(descriptor_flags >= 0);
    assert_ne!(descriptor_flags & libc::FD_CLOEXEC, 0);
    fs::set_permissions(&program, fs::Permissions::from_mode(0o755)).unwrap();
    fs::write(&program, b"different bytes after actual retirement").unwrap();
    fs::set_permissions(&program, fs::Permissions::from_mode(0o555)).unwrap();
    assert!(held.validate(deadline()).is_err());
    assert!(held.executable_descriptor(deadline()).is_err());
}

#[test]
fn produced_descriptor_refuses_path_replacement_and_sdk_runtime_drift_before_borrow() {
    let _serial = SERIAL.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    for replaced_path in [true, false] {
        let fixture = Fixture::new(&["/usr/lib/libSystem.B.dylib"]);
        fixture.runtime("sdk.dylib", &["/usr/lib/libSystem.B.dylib"]);
        let sdk = Arc::new(fixture.open().unwrap());
        let output = fixture.directory.path().join("outputs");
        fs::create_dir(&output).unwrap();
        let original = produced::HeldOutputRoot::open(&output, deadline()).unwrap();
        let program = output.join("debug/test-program");
        let bytes = image(true, &["@rpath/sdk.dylib"], Vec::new());
        write_output(&program, &bytes, true);
        let digest = Sha256::digest(&bytes).into();
        let held = original.program(sdk, &program, &digest, &[], deadline()).unwrap();
        assert_eq!(held.observation().runtime.len(), 1);
        assert!(held.executable_descriptor(deadline()).is_ok());
        assert_eq!(
            held.executable_descriptor(Instant::now()).unwrap_err().kind(),
            io::ErrorKind::TimedOut
        );
        if replaced_path {
            // Matching saved bytes at the path cannot replace the retained FD.
            fs::rename(&program, program.with_extension("old")).unwrap();
            write_output(&program, &bytes, true);
        } else {
            let runtime = fixture.root.join("lib/sdk.dylib");
            fs::set_permissions(&runtime, fs::Permissions::from_mode(0o644)).unwrap();
            fs::write(&runtime, b"changed original SDK runtime").unwrap();
            fs::set_permissions(&runtime, fs::Permissions::from_mode(0o444)).unwrap();
        }
        assert!(held.executable_descriptor(deadline()).is_err());
    }
}

#[test]
fn produced_evidence_preserves_binary_prefixes_and_enforces_shared_bounds_without_reuse() {
    let fixture = Fixture::new(&[]);
    let sdk = fixture.open().unwrap();
    let root = fixture.directory.path().join("output");
    fs::create_dir(&root).unwrap();
    let (output, mut evidence) =
        produced::HeldOutputRoot::open_with_evidence(&root, &sdk, [2; 16], 6, 2, deadline())
            .unwrap();
    let mut first = evidence.create(OsStr::new("first"), 4, deadline()).unwrap();
    assert_eq!(first.append(b"\0\xffabcd", deadline()).unwrap(), 4);
    assert_eq!(first.bytes_written(), 4);
    assert_eq!(first.append(b"z", deadline()).unwrap_err().kind(), io::ErrorKind::StorageFull);
    let mut second = evidence.create(OsStr::new("second"), 4, deadline()).unwrap();
    assert_eq!(second.append(b"xyz", deadline()).unwrap(), 2);
    assert_eq!(second.append(b"z", deadline()).unwrap_err().kind(), io::ErrorKind::StorageFull);
    assert!(evidence.create(OsStr::new("third"), 1, deadline()).is_err());
    first.sync_prefix(deadline()).unwrap();
    second.sync_prefix(deadline()).unwrap();
    assert_eq!(fs::read(evidence.path().join("first")).unwrap(), b"\0\xffab");
    assert_eq!(fs::read(evidence.path().join("second")).unwrap(), b"xy");
    assert!(
        produced::HeldOutputRoot::open_with_evidence(&root, &sdk, [2; 16], 6, 2, deadline())
            .is_err()
    );
    let (_, new_attempt) =
        produced::HeldOutputRoot::open_with_evidence(&root, &sdk, [3; 16], 6, 2, deadline())
            .unwrap();
    assert_ne!(new_attempt.path(), evidence.path());
    output.validate(deadline()).unwrap();
}

#[test]
fn produced_evidence_rejects_path_escapes_replaced_names_and_retargeted_directories() {
    let fixture = Fixture::new(&[]);
    let sdk = fixture.open().unwrap();
    let root = fixture.directory.path().join("output");
    fs::create_dir(&root).unwrap();
    let (_, mut evidence) =
        produced::HeldOutputRoot::open_with_evidence(&root, &sdk, [4; 16], 64, 8, deadline())
            .unwrap();
    for name in ["", ".", "..", "../outside", "/absolute", "nul\0name"] {
        assert!(evidence.create(OsStr::new(name), 8, deadline()).is_err());
    }
    let mut prefix = evidence.create(OsStr::new("prefix"), 8, deadline()).unwrap();
    prefix.append(b"actual", deadline()).unwrap();
    fs::rename(evidence.path().join("prefix"), evidence.path().join("original")).unwrap();
    fs::write(evidence.path().join("prefix"), b"forged").unwrap();
    assert!(prefix.append(b"x", deadline()).is_err());
    assert!(prefix.sync_prefix(deadline()).is_err());
    let original = evidence.path().with_extension("moved");
    fs::rename(evidence.path(), &original).unwrap();
    fs::create_dir(evidence.path()).unwrap();
    assert!(evidence.create(OsStr::new("later"), 1, deadline()).is_err());
    assert_eq!(fs::read(original.join("original")).unwrap(), b"actual");
}

#[test]
fn produced_evidence_exit_actor() {
    let Some(root) = std::env::var_os("TRUST_EVIDENCE_EXIT_ACTOR") else {
        return;
    };
    let sdk_root = PathBuf::from(std::env::var_os("TRUST_EVIDENCE_EXIT_SDK_ROOT").unwrap());
    let program = sdk_root.join("bin/program");
    let digest = Sha256::digest(fs::read(&program).unwrap()).into();
    let sdk = HeldProgram::open(&sdk_root, &program, &digest, deadline()).unwrap();
    let (_, mut evidence) = produced::HeldOutputRoot::open_with_evidence(
        Path::new(&root),
        &sdk,
        [5; 16],
        64,
        1,
        deadline(),
    )
    .unwrap();
    let mut prefix = evidence.create(OsStr::new("raw-prefix"), 64, deadline()).unwrap();
    prefix.append(b"received\0\xff-before-unknown", deadline()).unwrap();
    prefix.sync_prefix(deadline()).unwrap();
    // Deliberately bypass every Rust destructor, as an owning-custody failure
    // can do. No successful-execution or retirement fact is written.
    std::process::exit(7);
}

#[test]
fn produced_evidence_survives_actual_writer_exit_without_destructors() {
    let mut fixture = Fixture::new(&[]);
    let root = fixture.directory.path().join("output");
    fs::create_dir(&root).unwrap();
    let original = produced::HeldOutputRoot::open(&root, deadline()).unwrap();
    fixture.execution_attempted = true;
    let mut child = OwnedChild(
        Command::new(std::env::current_exe().unwrap())
            .args(["--exact", "program::tests::produced_evidence_exit_actor", "--nocapture"])
            .env_clear()
            .env("TRUST_EVIDENCE_EXIT_ACTOR", &root)
            .env("TRUST_EVIDENCE_EXIT_SDK_ROOT", &fixture.root)
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::inherit())
            .spawn()
            .unwrap(),
        None,
    );
    let until = deadline();
    loop {
        if let Some(status) = child.0.try_wait().unwrap() {
            assert_eq!(status.code(), Some(7));
            break;
        }
        assert!(Instant::now() < until, "owned evidence writer did not exit");
        std::thread::sleep(Duration::from_millis(5));
    }
    original.validate(deadline()).unwrap();
    let prefix = root
        .join(".trust-workload-evidence.noindex")
        .join(crate::schema::hex(&[5; 16]))
        .join("raw-prefix");
    assert_eq!(fs::read(prefix).unwrap(), b"received\0\xff-before-unknown");
    fixture.execution_proved = true;
}

#[test]
fn produced_evidence_cannot_write_into_sdk_or_reclassify_source_roots() {
    let fixture = Fixture::new(&[]);
    let sdk = fixture.open().unwrap();
    assert!(
        produced::HeldOutputRoot::open_with_evidence(
            &fixture.root,
            &sdk,
            [6; 16],
            64,
            1,
            deadline()
        )
        .is_err()
    );
    assert!(!fixture.root.join(".trust-workload-evidence.noindex").exists());
    let source = fixture.directory.path().join("source");
    fs::create_dir(&source).unwrap();
    fs::write(source.join("Cargo.toml"), b"original source marker").unwrap();
    assert!(
        produced::HeldOutputRoot::open_with_evidence(&source, &sdk, [6; 16], 64, 1, deadline())
            .is_err()
    );
    assert_eq!(fs::read(source.join("Cargo.toml")).unwrap(), b"original source marker");
    assert!(!source.join(".trust-workload-evidence.noindex").exists());
}

fn direct_load_override_is_refused(relative: bool) {
    let fixture = Fixture::new(&["/usr/lib/libSystem.B.dylib"]);
    let sdk = Arc::new(fixture.open().unwrap());
    let root = fixture.directory.path().join("output");
    fs::create_dir(&root).unwrap();
    let output = produced::HeldOutputRoot::open(&root, deadline()).unwrap();
    let program = root.join("unit/out/test-program");
    let deps = root.join("deps");
    let library = deps.join("runtime.dylib");
    let load = if relative {
        "@loader_path/../../deps/runtime.dylib".to_owned()
    } else {
        library.to_str().unwrap().to_owned()
    };
    write_output(&program, &image(true, &[&load], Vec::new()), true);
    write_output(&library, &image(false, &["/usr/lib/libSystem.B.dylib"], Vec::new()), false);
    let digest = Sha256::digest(fs::read(&program).unwrap()).into();
    let clean = output
        .program(Arc::clone(&sdk), &program, &digest, std::slice::from_ref(&deps), deadline())
        .unwrap();
    assert_eq!(clean.observation().runtime.len(), 1);
    assert_eq!(clean.observation().runtime[0].path, library);
    drop(clean);
    // The emitted DYLD_LIBRARY_PATH starts with this program's parent.
    // Its same-leaf image must not override the recorded direct dependency.
    write_output(
        &program.parent().unwrap().join("runtime.dylib"),
        &image(false, &["/usr/lib/libc++.1.dylib"], Vec::new()),
        false,
    );
    assert!(output.program(sdk, &program, &digest, &[deps], deadline()).is_err());
}

#[test]
fn produced_inputs_refuse_direct_absolute_loader_overrides() {
    direct_load_override_is_refused(false);
}

#[test]
fn produced_inputs_refuse_direct_relative_loader_overrides() {
    direct_load_override_is_refused(true);
}

#[test]
fn native_current_code_actor() {
    if std::env::var_os("NATIVE_CURRENT_CODE_ACTOR").is_none() {
        return;
    }
    // Actual execution proof precedes any pin of first-run OS image metadata.
    println!("held-native-program-running");
    std::io::stdout().flush().unwrap();
    let mut byte = [0];
    std::io::stdin().read_exact(&mut byte).unwrap();
    let executable = std::env::current_exe().unwrap().canonicalize().unwrap();
    let root = executable.parent().unwrap().parent().unwrap();
    let foreign_root = root.parent().unwrap().join("other-sdk");
    fs::create_dir_all(foreign_root.join("bin")).unwrap();
    let foreign = foreign_root.join("bin/program");
    fs::copy(&executable, &foreign).unwrap();
    fs::set_permissions(&foreign, fs::Permissions::from_mode(0o555)).unwrap();
    let expected: [u8; 32] = Sha256::digest(fs::read(&executable).unwrap()).into();
    let program = Arc::new(HeldProgram::open(root, &executable, &expected, deadline()).unwrap());
    assert!(std::env::var_os("DYLD_LIBRARY_PATH").is_none());
    let anchors = [native_current_code_actor as *const ()];
    let owner = program.bind_current_code(&anchors, deadline()).unwrap();
    owner.validate(deadline()).unwrap();
    let identity = *owner.content_identity();
    let wrong =
        Arc::new(HeldProgram::open(&foreign_root, &foreign, &expected, deadline()).unwrap());
    assert!(
        wrong.bind_current_code(&anchors, deadline()).is_err(),
        "equal bytes cannot replace the actual original mapped vnode"
    );
    assert!(program.bind_current_code(&[], deadline()).is_err());
    assert!(program.bind_current_code(&[std::ptr::null()], deadline()).is_err());
    assert!(
        program.bind_current_code(&[libc::getpid as *const ()], deadline()).is_err(),
        "system code is outside the owned main/driver closure"
    );
    let data = 19usize;
    assert!(
        program.bind_current_code(&[(&data as *const usize).cast()], deadline()).is_err(),
        "a data address cannot stand for builtin executable code"
    );
    // A new Darwin vnode does not acquire a validated code-signature cache
    // merely by copying signed bytes. Actually execute/reap this exact foreign
    // image through the maintained one-test actor before asking the kernel for
    // an executable mapping. No signing mutation, MAP_JIT or policy bypass.
    let evidence = root.parent().unwrap();
    let stdout = evidence.join("foreign-execution-stdout");
    let stderr = evidence.join("foreign-execution-stderr");
    let foreign_child = OwnedChild(
        Command::new(&foreign)
            .args(["--exact", ACTOR, "--nocapture"])
            .env_clear()
            .env("NATIVE_PROGRAM_ACTOR", "1")
            .stdin(Stdio::piped())
            .stdout(File::create(&stdout).unwrap())
            .stderr(File::create(&stderr).unwrap())
            .spawn()
            .unwrap(),
        None,
    );
    // Finish this owned child well inside the parent's sixty-second watchdog.
    finish_before(foreign_child, Instant::now() + Duration::from_secs(15));
    assert!(fs::metadata(&stdout).unwrap().len() <= 4096);
    let transcript = fs::read_to_string(stdout).unwrap();
    assert!(transcript.contains("running 1 test"));
    assert!(transcript.contains("held-native-program-running"));
    assert!(transcript.contains("1 passed; 0 failed; 0 ignored"));
    let foreign_digest: [u8; 32] = Sha256::digest(fs::read(&foreign).unwrap()).into();
    assert_eq!(foreign_digest, expected);
    let file = File::open(&foreign).unwrap();
    let size = usize::try_from(file.metadata().unwrap().len()).unwrap();
    // Real equal-byte foreign executable mapping. The main-only image check
    // still passes while the closed current-code profile must refuse.
    let mapping = unsafe {
        libc::mmap(
            std::ptr::null_mut(),
            size,
            libc::PROT_READ | libc::PROT_EXEC,
            libc::MAP_PRIVATE,
            file.as_raw_fd(),
            0,
        )
    };
    let mapping_error = io::Error::last_os_error();
    assert_ne!(
        mapping,
        libc::MAP_FAILED,
        "native executable shadow control must actually map: {mapping_error}"
    );
    struct Mapping(*mut libc::c_void, usize);
    impl Drop for Mapping {
        fn drop(&mut self) {
            unsafe { libc::munmap(self.0, self.1) };
        }
    }
    let mapping = Mapping(mapping, size);
    program
        .validate_loaded(process::read_identity(std::process::id()).unwrap(), deadline())
        .unwrap();
    assert!(
        owner.validate(deadline()).is_err(),
        "unexpected actual executable vnode is not covered by main-image equality"
    );
    drop(mapping);
    assert!(
        owner.validate(deadline()).is_err(),
        "later equal content cannot clear an observed failure"
    );
    let current = program.bind_current_code(&anchors, deadline()).unwrap();
    assert_eq!(current.content_identity(), &identity);
    assert!(current.validate(Instant::now()).is_err());
    assert!(current.validate(deadline()).is_err());
    let current = program.bind_current_code(&anchors, deadline()).unwrap();
    fs::create_dir(root.join("unexpected-input")).unwrap();
    assert!(current.validate(deadline()).is_err());
    fs::write(root.parent().unwrap().join("current-code-identity"), crate::schema::hex(&identity))
        .unwrap();
    println!("CURRENT_CODE_ASSERTIONS_PASSED");
    std::io::stdout().flush().unwrap();
}

#[test]
fn actual_current_code_binds_original_vnode_and_identity_survives_real_prefix_relocation() {
    let _serial = SERIAL.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    let mut keys = Vec::new();
    let mut files = Vec::new();
    let mut fixtures = Vec::new();
    for _ in 0..2 {
        let mut fixture = Fixture::new(&[]);
        fs::set_permissions(&fixture.program, fs::Permissions::from_mode(0o755)).unwrap();
        fs::copy(std::env::current_exe().unwrap(), &fixture.program).unwrap();
        let before = fs::metadata(&fixture.program).unwrap();
        files.push((before.dev(), before.ino()));
        let child = actor_for(
            &mut fixture,
            "program::tests::native_current_code_actor",
            &[("NATIVE_CURRENT_CODE_ACTOR", "1")],
        );
        finish(child);
        let key = fs::read(fixture.directory.path().join("current-code-identity")).unwrap();
        assert_eq!(key.len(), 64);
        assert!(key.iter().all(u8::is_ascii_hexdigit));
        keys.push(key);
        fixtures.push(fixture);
    }
    assert_ne!(files[0], files[1]);
    assert_eq!(
        keys[0], keys[1],
        "actual original content key excludes physical prefix/vnode/address instance"
    );
    for fixture in &mut fixtures {
        fixture.execution_proved = true;
    }
}
