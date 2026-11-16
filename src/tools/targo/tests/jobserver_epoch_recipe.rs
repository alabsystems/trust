// Trust: genuine helper startup data and pre-birth original log custody.
// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

#![cfg(any(target_os = "linux", target_os = "macos"))]

use std::fs::{self, File, OpenOptions};
use std::io::{self, BufRead as _, Read as _, Write as _};
use std::num::NonZeroU32;
use std::os::unix::fs::{MetadataExt as _, OpenOptionsExt as _};
use std::os::unix::process::CommandExt as _;
use std::path::{Path, PathBuf};
use std::process::{Child, ChildStdin, Command, ExitStatus, Stdio};
use std::sync::mpsc::{self, Receiver};
use std::time::{Duration, Instant};

use serde_json::{Value, json};
use trust_build_cpu::{Owner, RetainedPool};

const EPOCH: &str = "0123456789abcdef0123456789abcdef";
const FINALIZATION: &str = "fedcba9876543210fedcba9876543210";
const HANG: Duration = Duration::from_secs(60);
const FRAME: usize = 16 * 1024;

struct World(Option<tempfile::TempDir>);
impl World {
    fn new() -> Self {
        let directory = tempfile::Builder::new()
            .prefix("targo-epoch-recipe-")
            .suffix(".noindex")
            .tempdir()
            .unwrap();
        fs::create_dir(directory.path().join("home")).unwrap();
        Self(Some(directory))
    }
    fn path(&self) -> &Path {
        self.0.as_ref().unwrap().path()
    }
    fn passed(mut self) {
        drop(self.0.take());
    }
}
impl Drop for World {
    fn drop(&mut self) {
        if let Some(directory) = self.0.take() {
            eprintln!("kept failed recipe fixture: {}", directory.keep().display());
        }
    }
}

// On failure the original helper receives EOF and drains its actual roots.
// Only a hung owned helper is terminated; the failed world and debt survive.
struct Helper {
    child: Child,
    input: Option<ChildStdin>,
    output: Option<Receiver<io::Result<Option<Value>>>>,
    reader: Option<std::thread::JoinHandle<()>>,
    reaped: bool,
}
impl Helper {
    fn start(world: &Path, width: u32, recipes: &[String]) -> Self {
        let errors = OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o600)
            .open(world.join("helper.stderr"))
            .unwrap();
        let mut command = Command::new(env!("CARGO_BIN_EXE_targo"));
        let cargo_home = std::env::var_os("CARGO_HOME")
            .map(PathBuf::from)
            .unwrap_or_else(|| {
                PathBuf::from(std::env::var_os("HOME").expect("parent HOME")).join(".cargo")
            });
        command
            .args(["--unverified", "__resource-epoch", "--directory"])
            .arg(world.join("transport.noindex"))
            .args([
                "--epoch",
                EPOCH,
                "--backing",
                &width.to_string(),
                "--roots",
                &width.to_string(),
            ])
            .env_clear()
            .env("HOME", world.join("home"))
            .env("CARGO_HOME", cargo_home)
            .env("PATH", std::env::var_os("PATH").expect("parent PATH"))
            .env_remove("CARGO_MAKEFLAGS")
            .env_remove("MAKEFLAGS")
            .env_remove("MFLAGS")
            .process_group(0)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(errors);
        for recipe in recipes {
            command.arg("--root-recipe").arg(recipe);
        }
        let mut child = command.spawn().unwrap();
        let input = child.stdin.take();
        let stdout = child.stdout.take().unwrap();
        let (sender, output) = mpsc::sync_channel(16);
        let reader = std::thread::spawn(move || {
            let mut reader = io::BufReader::new(stdout);
            loop {
                let frame = (|| {
                    let mut bytes = Vec::new();
                    let count = (&mut reader)
                        .take((FRAME + 1) as u64)
                        .read_until(b'\n', &mut bytes)?;
                    if count == 0 {
                        return Ok(None);
                    }
                    if bytes.len() > FRAME || bytes.last() != Some(&b'\n') {
                        return Err(io::Error::other("unbounded helper frame"));
                    }
                    serde_json::from_slice(&bytes)
                        .map(Some)
                        .map_err(io::Error::other)
                })();
                let done = !matches!(frame, Ok(Some(_)));
                if sender.send(frame).is_err() || done {
                    break;
                }
            }
        });
        Self {
            child,
            input,
            output: Some(output),
            reader: Some(reader),
            reaped: false,
        }
    }
    fn next(&self) -> Option<Value> {
        let value = self
            .output
            .as_ref()
            .unwrap()
            .recv_timeout(HANG)
            .expect("actual helper output within hang detector")
            .unwrap();
        if let Some(value) = &value {
            assert_eq!(value["v"], 4);
            assert_eq!(value["epoch"], EPOCH);
        }
        value
    }
    fn send(&mut self, frame: Value) {
        let mut bytes = serde_json::to_vec(&frame).unwrap();
        bytes.push(b'\n');
        assert!(bytes.len() < FRAME);
        self.input.as_mut().unwrap().write_all(&bytes).unwrap();
    }
    fn wait(&mut self) -> ExitStatus {
        let deadline = Instant::now() + HANG;
        loop {
            if let Some(status) = self.child.try_wait().unwrap() {
                self.reaped = true;
                return status;
            }
            assert!(Instant::now() < deadline, "actual helper did not exit");
            std::thread::sleep(Duration::from_millis(10));
        }
    }
}
impl Drop for Helper {
    fn drop(&mut self) {
        drop(self.output.take());
        drop(self.input.take());
        if !self.reaped {
            let deadline = Instant::now() + HANG;
            loop {
                match self.child.try_wait() {
                    Ok(Some(_)) => break,
                    Ok(None) if Instant::now() < deadline => {
                        std::thread::sleep(Duration::from_millis(10));
                    }
                    _ => {
                        let _ = self.child.kill();
                        let _ = self.child.wait();
                        break;
                    }
                }
            }
        }
        if let Some(reader) = self.reader.take() {
            let _ = reader.join();
        }
    }
}

fn recipe() -> Value {
    let rustc =
        fs::canonicalize(std::env::var_os("RUSTC").expect("explicit native Trust SDK")).unwrap();
    let bin = rustc.parent().unwrap();
    json!({"schema":1,"id":0,"profile":"dev","bin":"recipe-fixture","jobs":1,
        "package":null,"features":[],"default_features":true,"all_features":false,
        "offline":true,"version":"1.2.0+g012345678","rustc":rustc,
        "rustdoc":bin.join("trustdoc"),"path":[bin]})
}

fn pool(world: &World, width: u32) -> RetainedPool {
    RetainedPool::create_private(
        &world.path().join("cpu.noindex"),
        NonZeroU32::new(width).unwrap(),
    )
    .unwrap()
}
fn pin(path: &Path) -> File {
    let file = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK | libc::O_CLOEXEC)
        .open(path)
        .unwrap();
    let metadata = file.metadata().unwrap();
    assert!(metadata.is_file() && metadata.nlink() == 1 && metadata.mode() & 0o777 == 0o600);
    assert_eq!(metadata.len(), 0);
    file
}

#[test]
fn invalid_recipes_refuse_before_transport_or_credits_are_published() {
    let value = recipe();
    let mut environment = value.clone();
    environment["env"] = json!({"RUSTC_WRAPPER":"unaccepted"});
    let mut profile = value.clone();
    profile["profile"] = json!("arbitrary-profile");
    let mut foreign = value.clone();
    foreign["id"] = json!(2);
    for rows in [
        vec![environment.to_string()],
        vec![profile.to_string()],
        vec![foreign.to_string()],
        vec![value.to_string(), value.to_string()],
        vec![" ".repeat(FRAME + 1)],
    ] {
        let world = World::new();
        let pool = pool(&world, 2);
        let caps: Vec<_> = (0..2)
            .map(|_| pool.try_acquire(Owner::current(None)).unwrap().unwrap())
            .collect();
        let mut helper = Helper::start(world.path(), 2, &rows);
        assert!(
            helper.next().is_none(),
            "invalid recipe published a control event"
        );
        assert!(!helper.wait().success());
        assert!(!world.path().join("transport.noindex").exists());
        assert!(pool.try_acquire(Owner::current(None)).unwrap().is_none());
        drop(caps);
        let reopened = RetainedPool::open_existing(pool.path()).unwrap().unwrap();
        assert!(
            reopened
                .try_acquire(Owner::current(None))
                .unwrap()
                .is_none(),
            "a refusal or closed kernel FD must not refund retained backing"
        );
        drop(helper);
        world.passed();
    }
}

#[test]
fn original_recipe_logs_can_be_pinned_before_any_root_birth() {
    let world = World::new();
    let pool = pool(&world, 1);
    let cap = pool.try_acquire(Owner::current(None)).unwrap().unwrap();
    let mut helper = Helper::start(world.path(), 1, &[recipe().to_string()]);
    let opened = helper.next().unwrap();
    assert_eq!(opened["event"], "opened");
    let transport = world.path().join("transport.noindex");
    let mut stdout = pin(&transport.join("root-0.stdout"));
    let mut stderr = pin(&transport.join("root-0.stderr"));
    let fifo = PathBuf::from(opened["fifo"].as_str().unwrap());
    let pinned_fifo = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK | libc::O_CLOEXEC)
        .open(&fifo)
        .unwrap();
    helper.send(json!({"v":4,"epoch":EPOCH,"op":"close"}));
    assert_eq!(helper.next().unwrap()["event"], "closing");
    helper.send(json!({"v":4,"epoch":EPOCH,"op":"finalize","finalization":FINALIZATION}));
    let retired = helper.next().unwrap();
    assert_eq!(retired["event"], "retired");
    assert_eq!(retired["finalization"], FINALIZATION);
    assert!(helper.next().is_none());
    assert!(helper.wait().success());
    let group = i32::try_from(helper.child.id()).unwrap();
    // SAFETY: signal zero only observes this actual reaped helper's original group.
    assert_eq!(unsafe { libc::kill(-group, 0) }, -1);
    assert_eq!(io::Error::last_os_error().raw_os_error(), Some(libc::ESRCH));
    let named = fs::symlink_metadata(&fifo).unwrap();
    let held = pinned_fifo.metadata().unwrap();
    assert_eq!((named.dev(), named.ino()), (held.dev(), held.ino()));
    fs::remove_file(&fifo).unwrap();
    File::open(&transport).unwrap().sync_all().unwrap();
    assert_eq!(pinned_fifo.metadata().unwrap().nlink(), 0);
    cap.settle().unwrap();
    let recovered = pool.try_acquire(Owner::current(None)).unwrap().unwrap();
    assert!(pool.try_acquire(Owner::current(None)).unwrap().is_none());
    recovered.settle().unwrap();
    let mut bytes = Vec::new();
    stdout.read_to_end(&mut bytes).unwrap();
    stderr.read_to_end(&mut bytes).unwrap();
    assert!(
        bytes.is_empty(),
        "no root was launched in this output custody fixture"
    );
    drop(helper);
    world.passed();
}

#[test]
fn configured_recipe_preserves_project_configuration_bin_profile_and_stamp() {
    let world = World::new();
    let project = world.path().join("project.noindex");
    fs::create_dir(&project).unwrap();
    fs::create_dir(project.join("src")).unwrap();
    fs::create_dir(project.join(".cargo")).unwrap();
    fs::write(
        project.join("Cargo.toml"),
        r#"
[package]
name = "recipe-fixture"
version = "1.2.0"
edition = "2024"
[workspace]
[features]
default = ["forbidden-default"]
forbidden-default = []
native-contract = []
[[bin]]
name = "recipe-tool"
path = "src/recipe.rs"
[[bin]]
name = "forbidden"
path = "src/forbidden.rs"
"#,
    )
    .unwrap();
    fs::write(
        project.join("Cargo.lock"),
        "version = 4\n[[package]]\nname = \"recipe-fixture\"\nversion = \"1.2.0\"\n",
    )
    .unwrap();
    fs::write(
        project.join(".cargo/config.toml"),
        "[env]\nEPOCH_RECIPE_CWD = { value = 'from-project', force = true }\n",
    )
    .unwrap();
    fs::write(
        project.join("src/recipe.rs"),
        r#"
fn main() {
    assert_eq!(env!("EPOCH_RECIPE_CWD"), "from-project");
    assert_eq!(env!("ALAB_HARNESS_VERSION"), "1.2.0+g012345678");
    assert!(!cfg!(debug_assertions));
    assert!(cfg!(feature = "native-contract"));
    assert!(!cfg!(feature = "forbidden-default"));
    println!("recipe-tool 1.2.0+g012345678 from-project release");
}
"#,
    )
    .unwrap();
    fs::write(
        project.join("src/forbidden.rs"),
        "compile_error!(\"unselected bin must not compile\");\n",
    )
    .unwrap();
    let mut selected = recipe();
    selected["profile"] = json!("release");
    selected["bin"] = json!("recipe-tool");
    selected["package"] = json!("recipe-fixture");
    selected["features"] = json!(["native-contract"]);
    selected["default_features"] = json!(false);
    let sdk = PathBuf::from(selected["rustc"].as_str().unwrap())
        .parent()
        .unwrap()
        .to_owned();
    let mut paths = vec![sdk];
    for path in std::env::split_paths(&std::env::var_os("PATH").expect("parent PATH")) {
        if path.is_absolute() && !paths.contains(&path) {
            paths.push(path);
        }
    }
    selected["path"] = json!(paths);
    let pool = pool(&world, 1);
    let cap = pool.try_acquire(Owner::current(None)).unwrap().unwrap();
    let mut helper = Helper::start(world.path(), 1, &[selected.to_string()]);
    let opened = helper.next().unwrap();
    assert_eq!(opened["event"], "opened");
    let transport = world.path().join("transport.noindex");
    let mut output = pin(&transport.join("root-0.stdout"));
    let _errors = pin(&transport.join("root-0.stderr"));
    let fifo = transport.join("credits.fifo");
    let pinned_fifo = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK | libc::O_CLOEXEC)
        .open(&fifo)
        .unwrap();
    let target = world.path().join("stable-target.noindex");
    helper.send(json!({"v":4,"epoch":EPOCH,"op":"spawn","id":0,
        "manifest":project.join("Cargo.toml"),"target":target}));
    let spawned = helper.next().unwrap();
    assert_eq!(spawned["event"], "spawned");
    helper.send(json!({"v":4,"epoch":EPOCH,"op":"close"}));
    let mut closing = false;
    let mut exited = false;
    while !closing || !exited {
        let frame = helper.next().expect("root result before EOF");
        match frame["event"].as_str().unwrap() {
            "closing" => {
                assert!(!closing);
                closing = true;
            }
            "root-exit" => {
                assert!(!exited);
                assert_eq!(frame["id"], 0);
                assert_eq!(frame["pid"], spawned["pid"]);
                assert_eq!(frame["code"], 0);
                assert_eq!(frame["success"], true);
                exited = true;
            }
            other => panic!("unexpected native recipe event {other}"),
        }
    }
    helper.send(json!({"v":4,"epoch":EPOCH,"op":"finalize","finalization":FINALIZATION}));
    let retired = helper.next().unwrap();
    assert_eq!(retired["event"], "retired");
    assert_eq!(retired["finalization"], FINALIZATION);
    assert!(helper.next().is_none());
    assert!(helper.wait().success());
    let group = i32::try_from(helper.child.id()).unwrap();
    // SAFETY: signal zero observes this actual reaped helper's original group only.
    assert_eq!(unsafe { libc::kill(-group, 0) }, -1);
    assert_eq!(io::Error::last_os_error().raw_os_error(), Some(libc::ESRCH));
    assert!(pool.try_acquire(Owner::current(None)).unwrap().is_none());
    let mut bytes = Vec::new();
    (&mut output)
        .take(1024 * 1024 + 1)
        .read_to_end(&mut bytes)
        .unwrap();
    assert!(bytes.len() <= 1024 * 1024);
    let executables: Vec<_> = bytes
        .split(|byte| *byte == b'\n')
        .filter_map(|line| serde_json::from_slice::<Value>(line).ok())
        .filter(|frame| {
            frame["reason"] == "compiler-artifact" && frame["target"]["name"] == "recipe-tool"
        })
        .filter_map(|frame| frame["executable"].as_str().map(PathBuf::from))
        .collect();
    assert_eq!(
        executables.len(),
        1,
        "complete original JSON must name one selected artifact"
    );
    // Darwin canonicalizes /tmp to /private/tmp in emitted artifact paths.
    // Compare physical containment and the exact selected release executable.
    let physical_target = target.canonicalize().unwrap();
    let physical_executable = executables[0].canonicalize().unwrap();
    assert!(physical_executable.starts_with(&physical_target));
    assert_eq!(
        physical_executable,
        physical_target.join("release/recipe-tool")
    );
    let mut artifact = Command::new(&executables[0])
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let deadline = Instant::now() + HANG;
    loop {
        if artifact.try_wait().unwrap().is_some() {
            break;
        }
        if Instant::now() >= deadline {
            let _ = artifact.kill();
            let _ = artifact.wait();
            panic!("actual recipe artifact did not execute; executable remains preserved");
        }
        std::thread::sleep(Duration::from_millis(10));
    }
    let result = artifact.wait_with_output().unwrap();
    assert!(result.status.success());
    assert_eq!(
        result.stdout,
        b"recipe-tool 1.2.0+g012345678 from-project release\n"
    );
    // No source or executable path is removed until the actual artifact writes
    // its first-exec proof. This fixture used no root descendants or survivors.
    let named = fs::symlink_metadata(&fifo).unwrap();
    let held = pinned_fifo.metadata().unwrap();
    assert_eq!((named.dev(), named.ino()), (held.dev(), held.ino()));
    fs::remove_file(&fifo).unwrap();
    File::open(&transport).unwrap().sync_all().unwrap();
    assert_eq!(pinned_fifo.metadata().unwrap().nlink(), 0);
    cap.settle().unwrap();
    let recovered = pool.try_acquire(Owner::current(None)).unwrap().unwrap();
    assert!(pool.try_acquire(Owner::current(None)).unwrap().is_none());
    recovered.settle().unwrap();
    drop(helper);
    world.passed();
}
