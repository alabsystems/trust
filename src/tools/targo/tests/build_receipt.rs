//! Trust: a real `targo build` keeps the receipt of the units its graph used
//! (DC-12a), and a failed one leaves the receipt before it; a build that holds
//! its profile's lock exclusively removes, when it ends, the incremental
//! folders no kept receipt's unit uses (DC-12b); a build with incremental
//! compilation off keeps a receipt of its own (DC-12e).
// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates
//
// targo-core's `compiler::build_receipt` tests drive the receipt's types and
// its write. These run the built `targo` as `targo` on a small workspace, so
// what they check is the whole path: the job queue's record of each unit,
// the hand-off to `finish_compilation`, `BuildRunner::receipt_of` and the
// write after the graph.
#![cfg(unix)]

use std::collections::BTreeSet;
use std::fs;
use std::os::unix::fs::MetadataExt as _;
use std::os::unix::process::CommandExt as _;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::time::{Duration, Instant};

use serde_json::Value;

/// The folder at the top of the build directory that holds the receipts.
const RECEIPTS: &str = ".targo-receipts";

/// A private world under the system's temporary folder: `ws/`, a workspace
/// whose one member, `receipt-member`, depends on `dep/`, the package
/// `receipt-dep` outside the workspace, which has a build script; `home/`, its
/// Cargo home; and `target/`, its build directory once a build runs.
fn world() -> tempfile::TempDir {
    let base = std::env::temp_dir()
        .join(".ubd")
        .join("targo-build-receipt-e2e.noindex");
    fs::create_dir_all(&base).unwrap();
    let world = tempfile::Builder::new()
        .prefix("world-")
        .tempdir_in(base)
        .unwrap();
    let root = world.path();
    fs::create_dir_all(root.join("ws").join("src")).unwrap();
    fs::create_dir_all(root.join("dep").join("src")).unwrap();
    fs::create_dir_all(root.join("home")).unwrap();
    fs::write(
        root.join("ws").join("Cargo.toml"),
        "[package]\nname = \"receipt-member\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n\
         [dependencies]\nreceipt-dep = { path = \"../dep\" }\n\n[workspace]\n",
    )
    .unwrap();
    fs::write(
        root.join("ws").join("src").join("lib.rs"),
        "pub fn value() -> u32 {\n    receipt_dep::value()\n}\n",
    )
    .unwrap();
    fs::write(
        root.join("dep").join("Cargo.toml"),
        "[package]\nname = \"receipt-dep\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
    )
    .unwrap();
    fs::write(root.join("dep").join("build.rs"), "fn main() {}\n").unwrap();
    fs::write(
        root.join("dep").join("src").join("lib.rs"),
        "pub fn value() -> u32 {\n    7\n}\n",
    )
    .unwrap();
    world
}

/// `targo --unverified build --offline --message-format=json` in the world's
/// workspace, run as `targo`, with the world's Cargo home and build directory,
/// and nothing of the caller's environment that would move the build
/// directory or a unit out of it, pick the old layout, wrap the compiler or
/// turn incremental compilation off (`CARGO_INCREMENTAL`,
/// `CARGO_BUILD_INCREMENTAL`, a `CARGO_PROFILE_*_INCREMENTAL` of the dev or
/// test profile, or a CI run's `CI` or `TF_BUILD`).
///
/// Freshness is by modification time (`build.fingerprint="mtime"`), so the
/// second build of an unchanged world compiles nothing under any compiler.
/// By content, targo's default, what a second build compiles depends on the
/// compiler that runs, which can be older than this source: targo reuses a
/// unit only where that compiler's dep-info holds a checksum of every file it
/// read, and a linked one (the build script) only where the compiler reported
/// the native tools it read (`-Ztrust-tool-inputs`,
/// `fingerprint/tool_inputs.rs`). A compiler from before that flag, or one
/// that drops the checksum of a sysroot file whose path holds a space (fixed
/// in `prepare_dep_info`, compiler/rustc_interface/src/passes.rs), has every
/// unit of this world compiled again, and the receipt then says so. The
/// receipt reads neither method: it records what the queue dispatched fresh
/// and what it dispatched dirty.
fn build_command(world: &Path) -> Command {
    let mut command = Command::new(env!("CARGO_BIN_EXE_targo"));
    command
        .arg0("targo")
        .current_dir(world.join("ws"))
        .args([
            "--unverified",
            "--config",
            "build.fingerprint=\"mtime\"",
            "build",
            "--offline",
            "--message-format=json",
        ])
        .env("CARGO_HOME", world.join("home"))
        .env("CARGO_TARGET_DIR", world.join("target"));
    for name in [
        "CARGO_BUILD_ACTION_SANDBOX",
        "CARGO_BUILD_BUILD_DIR",
        "CARGO_BUILD_INCREMENTAL",
        "CARGO_BUILD_SHARED_DEPENDENCY_CACHE",
        "CARGO_BUILD_TARGET",
        "CARGO_INCREMENTAL",
        "CARGO_LOG",
        "CARGO_MAKEFLAGS",
        "CARGO_PROFILE_DEV_INCREMENTAL",
        "CARGO_PROFILE_TEST_INCREMENTAL",
        "CI",
        "MAKEFLAGS",
        "MFLAGS",
        "RUSTC_WRAPPER",
        "RUSTC_WORKSPACE_WRAPPER",
        "TF_BUILD",
        "__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT",
    ] {
        command.env_remove(name);
    }
    command
}

/// Run the build in `world` to its end, its output kept in the world's
/// `<label>.stdout` and `<label>.stderr`. A one-minute hang detector: a build
/// still running then is killed, and the test fails.
fn build(world: &Path, label: &str) -> Output {
    run(world, label, build_command(world))
}

/// Run `command`, a build in `world`, as `build` runs it.
fn run(world: &Path, label: &str, mut command: Command) -> Output {
    let stdout = world.join(format!("{label}.stdout"));
    let stderr = world.join(format!("{label}.stderr"));
    command
        .stdin(Stdio::null())
        .stdout(fs::File::create(&stdout).unwrap())
        .stderr(fs::File::create(&stderr).unwrap());
    let mut child = command.spawn().unwrap();
    drop(command);
    let deadline = Instant::now() + Duration::from_secs(60);
    let status = loop {
        if let Some(status) = child.try_wait().unwrap() {
            break status;
        }
        if Instant::now() >= deadline {
            // Only this build, which the test started, is signalled.
            let _ = child.kill();
            let _ = child.wait();
            panic!("the {label} build exceeded its hang detector");
        }
        std::thread::sleep(Duration::from_millis(10));
    };
    let output = Output {
        status,
        stdout: fs::read(stdout).unwrap(),
        stderr: fs::read(stderr).unwrap(),
    };
    prints_no_receipt(&output);
    output
}

/// A receipt adds no message: nothing `output` printed names it.
fn prints_no_receipt(output: &Output) {
    for printed in [&output.stdout, &output.stderr] {
        let printed = String::from_utf8_lossy(printed);
        assert!(
            !printed.contains(RECEIPTS) && !printed.contains("build receipt"),
            "{printed}"
        );
    }
}

/// Assert that `output` is a build that succeeded.
fn succeeded(output: &Output) {
    assert!(
        output.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

/// The `compiler-artifact` messages of `output` whose unit was compiled
/// (`fresh` false): what aterm's verify counts as compiled.
fn compiled(output: &Output) -> Vec<Value> {
    String::from_utf8_lossy(&output.stdout)
        .lines()
        .filter_map(|line| serde_json::from_str::<Value>(line).ok())
        .filter(|row| row["reason"] == "compiler-artifact" && row["fresh"] == false)
        .collect()
}

/// The bytes of the files `rows` name, counted as aterm's verify counts them
/// (`output_bytes` in aterm's crates/aterm-verify/src/compile_account.rs):
/// one `symlink_metadata` of each path, each path and each file (device and
/// inode) once, regular files only.
fn bytes_of(rows: &[Value]) -> u64 {
    let mut paths = BTreeSet::new();
    let mut files = BTreeSet::new();
    let mut total = 0_u64;
    for name in rows
        .iter()
        .flat_map(|row| row["filenames"].as_array().unwrap())
    {
        let path = PathBuf::from(name.as_str().unwrap());
        if !paths.insert(path.clone()) {
            continue;
        }
        let Ok(meta) = fs::symlink_metadata(&path) else {
            continue;
        };
        if meta.file_type().is_file() && files.insert((meta.dev(), meta.ino())) {
            total += meta.len();
        }
    }
    total
}

/// Whether `word` is a unit's hash: sixteen lowercase hex digits.
fn is_hash(word: &str) -> bool {
    word.len() == 16
        && word
            .bytes()
            .all(|byte| matches!(byte, b'0'..=b'9' | b'a'..=b'f'))
}

/// The names in the folder `dir`, sorted.
fn names(dir: &Path) -> Vec<String> {
    let mut names: Vec<String> = fs::read_dir(dir)
        .unwrap()
        .map(|entry| entry.unwrap().file_name().into_string().unwrap())
        .collect();
    names.sort();
    names
}

/// The one receipt in the world's build directory, which is all its receipts'
/// folder holds: its path and its bytes. Its name is sixteen lowercase hex
/// digits and `.json`.
fn receipt(world: &Path) -> (PathBuf, Vec<u8>) {
    let dir = world.join("target").join(RECEIPTS);
    let names = names(&dir);
    assert_eq!(names.len(), 1, "{names:?}");
    let stem = names[0].strip_suffix(".json");
    assert!(stem.is_some_and(is_hash), "{names:?}");
    let path = dir.join(&names[0]);
    let bytes = fs::read(&path).unwrap();
    (path, bytes)
}

/// The units of the build directory's `debug` profile, as the new layout
/// keeps them (`debug/build/<package>/<hash>/`, each with its `fingerprint/`):
/// each one's hash, and whether it is a build script's run (it has `run/`).
fn units(world: &Path) -> Vec<(String, bool)> {
    let mut units = Vec::new();
    let build = world.join("target").join("debug").join("build");
    for package in fs::read_dir(&build).unwrap() {
        let package = package.unwrap().path();
        if !package.is_dir() {
            continue;
        }
        for unit in fs::read_dir(&package).unwrap() {
            let unit = unit.unwrap().path();
            let Some(hash) = unit.file_name().and_then(|name| name.to_str()) else {
                continue;
            };
            if is_hash(hash) && unit.join("fingerprint").is_dir() {
                units.push((hash.to_owned(), unit.join("run").is_dir()));
            }
        }
    }
    units.sort();
    units
}

/// The hashes the receipt array `value` holds.
fn hashes(value: &Value) -> BTreeSet<&str> {
    value
        .as_array()
        .unwrap_or_else(|| panic!("{value}"))
        .iter()
        .map(|hash| hash.as_str().unwrap())
        .collect()
}

/// A cold build keeps one receipt: its `debug` profile names each of the four
/// units the build directory holds (the dependency's library, its build
/// script and that script's run, and the member's library); `built` names
/// each but the build script's run, as many as the `compiler-artifact`
/// messages that compiled; `output_bytes` is what aterm's verify counts of
/// those messages' files; `members` is the member alone; the selection's one
/// root is the member, with no version. A warm build of the same selection
/// replaces that receipt at the same name, names the same units, builds none
/// and counts no bytes. A build that fails leaves the warm one's receipt byte
/// for byte, and nothing else in the folder. No build prints anything of a
/// receipt.
///
/// Negative control: the warm build's receipt differs from the cold one's
/// bytes, so a build that succeeds does replace the receipt; only the failed
/// build leaves it as it was.
#[test]
fn a_targo_build_keeps_a_receipt_of_its_units_and_a_failed_one_keeps_the_one_before() {
    let scratch = world();
    let world = scratch.path();

    let cold = build(world, "cold");
    succeeded(&cold);
    let (path, cold_bytes) = receipt(world);
    let first: Value = serde_json::from_slice(&cold_bytes).unwrap();
    let units = units(world);
    assert_eq!(units.len(), 4, "{units:?}");
    let all: BTreeSet<&str> = units.iter().map(|(hash, _)| hash.as_str()).collect();
    let runs: BTreeSet<&str> = units
        .iter()
        .filter(|(_, run)| *run)
        .map(|(hash, _)| hash.as_str())
        .collect();
    assert_eq!(runs.len(), 1, "{units:?}");
    let built: BTreeSet<&str> = all.difference(&runs).copied().collect();
    assert_eq!(first["profiles"].as_object().unwrap().len(), 1, "{first}");
    assert_eq!(hashes(&first["profiles"]["debug"]), all, "{first}");
    assert_eq!(first["built"].as_object().unwrap().len(), 1, "{first}");
    assert_eq!(hashes(&first["built"]["debug"]), built, "{first}");
    let messages = compiled(&cold);
    assert_eq!(messages.len(), built.len(), "{messages:?}");
    let written = bytes_of(&messages);
    assert!(written > 0);
    assert_eq!(first["output_bytes"].as_u64(), Some(written), "{first}");
    assert_eq!(first["members"], serde_json::json!(["receipt-member"]));
    assert_eq!(first["receipt"], 1);
    assert!(first["began_ms"].is_u64(), "{first}");
    let roots = first["selection"]["roots"].as_array().unwrap();
    assert_eq!(roots.len(), 1, "{first}");
    assert_eq!(roots[0]["package"], "receipt-member");
    assert!(roots[0].get("version").is_none(), "{first}");

    let warm = build(world, "warm");
    succeeded(&warm);
    assert!(compiled(&warm).is_empty());
    let (again, warm_bytes) = receipt(world);
    assert_eq!(again, path);
    assert_ne!(warm_bytes, cold_bytes);
    let second: Value = serde_json::from_slice(&warm_bytes).unwrap();
    assert_eq!(second["profiles"], first["profiles"]);
    assert_eq!(second["built"], serde_json::json!({}));
    assert_eq!(second["output_bytes"], 0);
    assert_eq!(second["members"], first["members"]);
    assert_eq!(second["selection"], first["selection"]);

    fs::write(
        world.join("ws").join("src").join("lib.rs"),
        "pub fn broken() -> u8 {}\n",
    )
    .unwrap();
    let failed = build(world, "failed");
    assert!(!failed.status.success(), "the broken member built");
    let (kept, kept_bytes) = receipt(world);
    assert_eq!(kept, path);
    assert_eq!(kept_bytes, warm_bytes);
}

/// A build whose receipt cannot be written succeeds as it would have: with a
/// file standing where the receipts' folder goes, `targo build` compiles its
/// three units, succeeds, prints nothing of a receipt, and leaves the file as
/// it was.
///
/// Negative control: with that file gone, the same build keeps a receipt,
/// which names the four units and, since they are fresh by then, builds
/// none.
#[test]
fn a_targo_build_whose_receipt_cannot_be_written_still_succeeds() {
    let scratch = world();
    let world = scratch.path();
    let target = world.join("target");
    fs::create_dir_all(&target).unwrap();
    let blocker = target.join(RECEIPTS);
    fs::write(&blocker, b"not a folder").unwrap();

    let blocked = build(world, "blocked");
    succeeded(&blocked);
    assert_eq!(compiled(&blocked).len(), 3);
    assert_eq!(fs::read(&blocker).unwrap(), b"not a folder");

    fs::remove_file(&blocker).unwrap();
    let unblocked = build(world, "unblocked");
    succeeded(&unblocked);
    let (_, bytes) = receipt(world);
    let receipt: Value = serde_json::from_slice(&bytes).unwrap();
    assert_eq!(receipt["built"], serde_json::json!({}));
    assert_eq!(hashes(&receipt["profiles"]["debug"]).len(), 4, "{receipt}");
}

/// `build_command` with `-Zfine-grain-locking`, where each unit has a lock of
/// its own and two builds of one build directory overlap.
fn locking_command(world: &Path) -> Command {
    let mut command = build_command(world);
    command
        .args(["-Zfine-grain-locking", "-Zbuild-dir-new-layout"])
        .env("__CARGO_TEST_CHANNEL_OVERRIDE_DO_NOT_USE_THIS", "nightly");
    command
}

/// The build directory's unit of the member's library: its folder, which
/// holds its `.lock`, and its fingerprint's hash file.
fn member_library(world: &Path) -> (PathBuf, PathBuf) {
    let package = world
        .join("target")
        .join("debug")
        .join("build")
        .join("receipt-member");
    let mut found = Vec::new();
    for unit in fs::read_dir(&package).unwrap() {
        let unit = unit.unwrap().path();
        let fingerprint = unit.join("fingerprint").join("lib-receipt_member");
        if fingerprint.is_file() {
            found.push((unit, fingerprint));
        }
    }
    assert_eq!(found.len(), 1, "{found:?}");
    found.pop().unwrap()
}

/// The build `locking_command` runs while another build holds the member's
/// library: this test holds the unit's lock, as a build using it does, with
/// its fingerprint gone, so the build plans to compile it and waits for the
/// lock. Once the build says it is waiting, `finish` stands for the other
/// build (it puts the fingerprint back, or not), and the lock is released.
/// One-minute hang detectors on the wait and on the build; the build is
/// killed if either passes.
fn build_behind_another(world: &Path, label: &str, finish: impl FnOnce()) -> Output {
    use std::io::{BufRead as _, BufReader};
    use targo::util::{Filesystem, GlobalContext};

    /// Kills the build this test started, if it is still running.
    struct Started(std::process::Child);
    impl Drop for Started {
        fn drop(&mut self) {
            if self.0.try_wait().ok().flatten().is_none() {
                let _ = self.0.kill();
                let _ = self.0.wait();
            }
        }
    }

    let (unit, fingerprint) = member_library(world);
    let gctx = GlobalContext::default().unwrap();
    let held = Filesystem::new(unit.clone())
        .open_ro_shared(unit.join(".lock"), &gctx, "the other build")
        .unwrap();
    fs::remove_file(&fingerprint).unwrap();

    let stdout = world.join(format!("{label}.stdout"));
    let mut command = locking_command(world);
    command
        .stdin(Stdio::null())
        .stdout(fs::File::create(&stdout).unwrap())
        .stderr(Stdio::piped());
    let mut started = Started(command.spawn().unwrap());
    drop(command);
    let stderr = started.0.stderr.take().unwrap();
    let (waiting, wait) = std::sync::mpsc::channel();
    let reader = std::thread::spawn(move || {
        let mut text = String::new();
        for line in BufReader::new(stderr).lines() {
            let line = line.unwrap();
            if line.contains("waiting for file lock on receipt-member") {
                let _ = waiting.send(());
            }
            text.push_str(&line);
            text.push('\n');
        }
        text
    });
    wait.recv_timeout(Duration::from_secs(60))
        .unwrap_or_else(|_| panic!("the {label} build never waited for the member's lock"));
    finish();
    drop(held);

    let deadline = Instant::now() + Duration::from_secs(60);
    let status = loop {
        if let Some(status) = started.0.try_wait().unwrap() {
            break status;
        }
        assert!(
            Instant::now() < deadline,
            "the {label} build exceeded its hang detector"
        );
        std::thread::sleep(Duration::from_millis(10));
    };
    let output = Output {
        status,
        stdout: fs::read(stdout).unwrap(),
        stderr: reader.join().unwrap().into_bytes(),
    };
    prints_no_receipt(&output);
    output
}

/// Two overlapping builds (`-Zfine-grain-locking`): a build that planned to
/// compile the member's library and waited for its lock while another build
/// completed it uses it and does not compile it, so its receipt names it in
/// `profiles`, not in `built`, and counts none of its bytes, as its
/// `compiler-artifact` messages say. The lock wait is real: the build says it
/// is waiting before the other build finishes. Today the build waits in its
/// planner's lease acquisition (`LockManager`), plans again once it has the
/// lease and dispatches the unit fresh, so the job queue's recheck under the
/// lock (`Ledger::found_fresh`) is not what answers here; this holds the
/// receipt to the outcome whichever of the two answers.
///
/// Negative control: where the other build leaves the unit unfinished (no
/// fingerprint), the build compiles it once it has the lock, and its receipt
/// names it built, with the bytes its message's files hold.
#[test]
fn a_unit_another_build_completed_while_this_one_waited_counts_as_fresh() {
    let scratch = world();
    let world = scratch.path();
    let mut cold = locking_command(world);
    let cold = cold.output().unwrap();
    succeeded(&cold);
    prints_no_receipt(&cold);
    let all: BTreeSet<String> = units(world).into_iter().map(|(hash, _)| hash).collect();
    assert_eq!(all.len(), 4, "{all:?}");
    let (unit, fingerprint) = member_library(world);
    let member = unit.file_name().unwrap().to_str().unwrap().to_owned();
    let finished = fs::read(&fingerprint).unwrap();

    let behind = build_behind_another(world, "behind", || {
        fs::write(&fingerprint, &finished).unwrap();
    });
    succeeded(&behind);
    assert!(
        compiled(&behind).is_empty(),
        "{}",
        String::from_utf8_lossy(&behind.stdout)
    );
    let (_, bytes) = receipt(world);
    let receipt_behind: Value = serde_json::from_slice(&bytes).unwrap();
    let named: BTreeSet<String> = hashes(&receipt_behind["profiles"]["debug"])
        .into_iter()
        .map(str::to_owned)
        .collect();
    assert_eq!(named, all, "{receipt_behind}");
    assert_eq!(receipt_behind["built"], serde_json::json!({}));
    assert_eq!(receipt_behind["output_bytes"], 0);

    // Negative control: the other build leaves the unit unfinished.
    let unfinished = build_behind_another(world, "unfinished", || {});
    succeeded(&unfinished);
    let messages = compiled(&unfinished);
    assert_eq!(messages.len(), 1, "{messages:?}");
    let (_, bytes) = receipt(world);
    let receipt_unfinished: Value = serde_json::from_slice(&bytes).unwrap();
    assert_eq!(
        hashes(&receipt_unfinished["built"]["debug"]),
        BTreeSet::from([member.as_str()]),
        "{receipt_unfinished}"
    );
    let written = bytes_of(&messages);
    assert!(written > 0);
    assert_eq!(
        receipt_unfinished["output_bytes"].as_u64(),
        Some(written),
        "{receipt_unfinished}"
    );
}

/// The `debug` profile's incremental folder of the world's build directory.
fn incremental(world: &Path) -> PathBuf {
    world.join("target").join("debug").join("incremental")
}

/// The crate folders in the world's `debug` incremental folder whose crate is
/// `krate`, by name, sorted.
fn crate_folders(world: &Path, krate: &str) -> Vec<String> {
    names(&incremental(world))
        .into_iter()
        .filter(|name| name.split_once('-').is_some_and(|(of, _)| of == krate))
        .collect()
}

/// What the receipt `receipt` names under `incremental` for its `debug`
/// profile: each unit's hash and the folders it uses.
fn incremental_named(receipt: &Value) -> Vec<(String, BTreeSet<String>)> {
    receipt["incremental"]["debug"]
        .as_object()
        .unwrap_or_else(|| panic!("{receipt}"))
        .iter()
        .map(|(hash, folders)| {
            let folders = folders
                .as_array()
                .unwrap_or_else(|| panic!("{receipt}"))
                .iter()
                .map(|folder| folder.as_str().unwrap().to_owned())
                .collect();
            (hash.clone(), folders)
        })
        .collect()
}

/// The folders the world's one receipt names under its `debug` profile's
/// `incremental`, and the one folder of the member's crate among them. Every
/// unit it names there is one of the profile's units, and every folder it
/// names is one on disk, named by its own name (`<crate>-<id>`), not by a bare
/// crate: the job queue noted the folder each compile wrote.
fn named_folders(world: &Path) -> (BTreeSet<String>, String) {
    let (_, bytes) = receipt(world);
    let receipt: Value = serde_json::from_slice(&bytes).unwrap();
    let units = hashes(&receipt["profiles"]["debug"]);
    let mut all = BTreeSet::new();
    for (hash, folders) in incremental_named(&receipt) {
        assert!(units.contains(hash.as_str()), "{receipt}");
        assert!(!folders.is_empty(), "{receipt}");
        all.extend(folders);
    }
    assert!(all.iter().all(|folder| folder.contains('-')), "{receipt}");
    let on_disk: BTreeSet<String> = names(&incremental(world)).into_iter().collect();
    assert!(all.is_subset(&on_disk), "{all:?} {on_disk:?}");
    let member: Vec<&String> = all
        .iter()
        .filter(|folder| folder.starts_with("receipt_member-"))
        .collect();
    assert_eq!(member.len(), 1, "{receipt}");
    let member = member[0].clone();
    (all, member)
}

/// Make the folder `path` last written a day ago, so no build that begins
/// now takes it for one of its own.
fn age(path: &Path) {
    let day_ago = std::time::SystemTime::now() - Duration::from_secs(24 * 60 * 60);
    filetime::set_file_mtime(path, filetime::FileTime::from_system_time(day_ago)).unwrap();
}

/// A real build names, in its receipt, the incremental folder the
/// compile of the member's library wrote, and every folder it names is one
/// on disk. Once the member is a new variant (its version bumped), its old
/// folder, which no kept receipt names any more, is removed when a plain
/// build of the new variant ends, and the new variant's folder, which its
/// receipt names, stays.
///
/// Negative control: the same build run with `-Zfine-grain-locking`, which
/// holds its profile's lock shared, leaves the old folder: another build
/// could be compiling in the profile. Only the next plain build removes it.
#[test]
fn a_targo_build_removes_the_incremental_folder_of_a_variant_no_kept_receipt_uses() {
    let scratch = world();
    let world = scratch.path();

    let cold = build(world, "cold");
    succeeded(&cold);
    let (_, old) = named_folders(world);
    assert_eq!(crate_folders(world, "receipt_member"), [old.clone()]);
    age(&incremental(world).join(&old));

    let manifest = world.join("ws").join("Cargo.toml");
    let bumped = fs::read_to_string(&manifest)
        .unwrap()
        .replace("version = \"0.1.0\"", "version = \"0.2.0\"");
    fs::write(&manifest, bumped).unwrap();
    let shared = run(world, "shared", locking_command(world));
    succeeded(&shared);
    let (_, new) = named_folders(world);
    assert_ne!(new, old);
    let mut both = vec![old.clone(), new.clone()];
    both.sort();
    assert_eq!(crate_folders(world, "receipt_member"), both);

    let plain = build(world, "plain");
    succeeded(&plain);
    let (named, member) = named_folders(world);
    assert!(named.contains(&new), "{named:?}");
    assert_eq!(member, new);
    assert_eq!(crate_folders(world, "receipt_member"), [new]);
}

/// The receipts in the world's build directory, by name: each one's bytes.
fn receipts(world: &Path) -> Vec<(String, Vec<u8>)> {
    let dir = world.join("target").join(RECEIPTS);
    names(&dir)
        .into_iter()
        .map(|name| {
            let bytes = fs::read(dir.join(&name)).unwrap();
            (name, bytes)
        })
        .collect()
}

/// DC-12e. A plain `targo build` and the same build with
/// `CARGO_INCREMENTAL=0` (aterm verify's main lane, in the build directory
/// plain builds share) keep a receipt each: the plain build's selection has no
/// `incremental`, and the one with it off says `"incremental":false`, is
/// otherwise the plain build's selection, names the member's library under
/// another unit hash and no unit under `incremental`, and leaves the plain
/// build's receipt byte for byte.
///
/// Negative control: the same build with `CARGO_INCREMENTAL=1`, which is
/// the profile's default, is the plain build's selection: it replaces the
/// plain build's receipt at its name, and the build with it off keeps its own.
#[test]
fn a_targo_build_with_cargo_incremental_0_keeps_its_own_receipt() {
    let scratch = world();
    let world = scratch.path();

    let plain = build(world, "plain");
    succeeded(&plain);
    let (plain_path, plain_bytes) = receipt(world);
    let first: Value = serde_json::from_slice(&plain_bytes).unwrap();
    assert!(first["selection"].get("incremental").is_none(), "{first}");
    assert!(!incremental_named(&first).is_empty(), "{first}");

    let mut off = build_command(world);
    off.env("CARGO_INCREMENTAL", "0");
    let off = run(world, "off", off);
    succeeded(&off);
    let kept = receipts(world);
    assert_eq!(
        kept.len(),
        2,
        "{:?}",
        kept.iter().map(|(name, _)| name).collect::<Vec<_>>()
    );
    assert_eq!(fs::read(&plain_path).unwrap(), plain_bytes);
    let plain_name = plain_path.file_name().unwrap().to_str().unwrap();
    let (_, off_bytes) = kept.iter().find(|(name, _)| name != plain_name).unwrap();
    let second: Value = serde_json::from_slice(off_bytes).unwrap();
    assert_eq!(second["selection"]["incremental"], false, "{second}");
    let mut without = second["selection"].clone();
    without.as_object_mut().unwrap().remove("incremental");
    assert_eq!(without, first["selection"]);
    assert_eq!(second["incremental"], serde_json::json!({}), "{second}");
    assert_ne!(
        second["profiles"]["debug"], first["profiles"]["debug"],
        "{second}"
    );

    // Negative control: incremental compilation on, as the profile says.
    let mut on = build_command(world);
    on.env("CARGO_INCREMENTAL", "1");
    let on = run(world, "on", on);
    succeeded(&on);
    let after = receipts(world);
    assert_eq!(
        after.iter().map(|(name, _)| name).collect::<Vec<_>>(),
        kept.iter().map(|(name, _)| name).collect::<Vec<_>>()
    );
    let third: Value = serde_json::from_slice(&fs::read(&plain_path).unwrap()).unwrap();
    assert!(
        third["began_ms"].as_u64() > first["began_ms"].as_u64(),
        "{third}"
    );
    assert_eq!(third["selection"], first["selection"]);
    let (_, off_again) = after.iter().find(|(name, _)| name != plain_name).unwrap();
    assert_eq!(off_again, off_bytes);
}
