//! Trust TG6 (`TG6-FACTS-1` (21)): a compiler whose driver library is replaced
//! under its path while it runs opens no store. This is what a toolchain rebuilt
//! at the same commit does: bootstrap unlinks the old driver and links the new
//! one under the same name. The path no longer names the image the process runs,
//! so the process has no identity, stores no fact and checks afresh. A compiler
//! of the replacement then misses: nothing the old checker made was filed under
//! the new image's identity.
//!
//! Before the fix the replaced process hashed the new file, stored its facts
//! under that file's identity, and the replacement's compiler hit them without
//! a check. NEGATIVE CONTROL (2026-11-06): this sequence run by hand on a
//! main-derived stage 1 without the fix: the old process stored 3 facts and
//! the replacement's compiler hit all 3, elaborating nothing. At the unit
//! level, `clean_fact`'s
//! `an_image_replaced_under_its_path_gives_its_old_runner_no_identity` fails
//! without the device and inode check.
//!
//! The window is between the driver's load and the compiler's first fact open,
//! which comes before any macro expands (the resolver checks the root crate's
//! islands as one batch first), so a proc macro cannot hold the compiler there.
//! Its source can: `lib.rs` is a FIFO, so the compiler, driver loaded, waits in
//! the read of its input until the test has replaced the driver and written it.

//@ ignore-cross-compile
//@ ignore-windows

use std::fs::OpenOptions;
use std::io::{ErrorKind, Write};
use std::os::unix::fs::OpenOptionsExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

use run_make_support::{cmd, cwd, env_var, libc, rfs};

const SOURCE: &str = r#"
clean {
    theorem tg6_replaced : forall (n : Nat), n + 0 = n := fun n => rfl
}

pub fn f() -> u64 { 1 }
"#;

fn misses(stderr: &str) -> usize {
    stderr
        .lines()
        .filter(|line| line.starts_with("TRUST_CLEAN_FACT ELABORATE ") && !line.ends_with(" audit"))
        .count()
}

fn stores(stderr: &str) -> usize {
    stderr.lines().filter(|line| line.starts_with("TRUST_CLEAN_FACT STORE ")).count()
}

/// `compiler`'s rustc on `lib.rs`, its own driver loaded (no library path).
fn compile(compiler: &Path) -> Command {
    let mut command = Command::new(compiler.join("bin/rustc"));
    command
        .args(["lib.rs", "--crate-name=tg6_replaced", "--crate-type=lib", "--edition=2021"])
        .args(["--emit=metadata", "-Ztrust-verify=on", "-Ztrust-policy=advisory"])
        .env("CARGO_HOME", cwd().join("cargo-home"))
        .env("TRUST_CLEAN_FACT_STATS", "1")
        .env_remove("TRUST_NO_VERIFY")
        .env_remove(env_var("LD_LIB_PATH_ENVVAR"))
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    command
}

fn finish(command: &mut Command) -> String {
    let output = command.output().expect("the compiler runs");
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    assert!(output.status.success(), "{stderr}");
    stderr
}

/// A sysroot of copies: the rustc binary and every library file, with the
/// original's directories (`lib/rustlib`) linked. Returns it and its driver.
fn copied_compiler() -> (PathBuf, PathBuf) {
    let sysroot =
        PathBuf::from(run_make_support::rustc().print("sysroot").run().stdout_utf8().trim());
    let copy = cwd().join("compiler");
    rfs::create_dir_all(copy.join("bin"));
    rfs::create_dir_all(copy.join("lib"));
    rfs::copy(sysroot.join("bin/rustc"), copy.join("bin/rustc"));
    let mut driver = None;
    for entry in rfs::read_dir(sysroot.join("lib")) {
        let entry = entry.unwrap();
        let (from, to) = (entry.path(), copy.join("lib").join(entry.file_name()));
        if from.is_dir() {
            rfs::symlink_dir(&from, &to);
        } else {
            rfs::copy(&from, &to);
            if entry.file_name().to_string_lossy().starts_with("librustc_driver") {
                driver = Some(to);
            }
        }
    }
    (copy, driver.expect("the sysroot has a driver library"))
}

/// Unlink `driver` and put a new file of different bytes at its path, as a
/// rebuild at the same commit does (re-signed under another identifier on
/// macOS, one byte longer elsewhere).
fn replace(driver: &Path) {
    let staged = driver.with_extension("staged");
    rfs::copy(driver, &staged);
    if cfg!(target_os = "macos") {
        cmd("codesign")
            .args(["-f", "-s", "-", "--identifier", "trust.tg6.replaced-image"])
            .arg(&staged)
            .run();
    } else {
        let mut bytes = rfs::read(&staged);
        bytes.extend_from_slice(b"\0tg6");
        rfs::write(&staged, bytes);
    }
    assert_ne!(rfs::read(&staged), rfs::read(driver), "the replacement differs");
    rfs::remove_file(driver);
    rfs::rename(&staged, driver);
}

fn main() {
    let (compiler, driver) = copied_compiler();

    // The old image runs; its driver is replaced while it waits for its source.
    cmd("mkfifo").arg("lib.rs").run();
    let mut running = compile(&compiler).spawn().expect("the old compiler starts");
    let start = Instant::now();
    let mut source = loop {
        // A FIFO opened to write without blocking fails with ENXIO until its
        // reader has opened it: then the compiler, driver loaded, is reading.
        match OpenOptions::new().write(true).custom_flags(libc::O_NONBLOCK).open("lib.rs") {
            Ok(source) => break source,
            Err(error) if error.raw_os_error() == Some(libc::ENXIO) => {}
            Err(error) if error.kind() == ErrorKind::Interrupted => {}
            Err(error) => panic!("the source FIFO: {error}"),
        }
        if let Some(status) = running.try_wait().expect("the old compiler") {
            panic!("the compiler ended ({status}) before it read its source");
        }
        assert!(start.elapsed() < Duration::from_secs(600), "the compiler never read its source");
        std::thread::sleep(Duration::from_millis(20));
    };
    replace(&driver);
    source.write_all(SOURCE.as_bytes()).expect("the source");
    drop(source);
    let output = running.wait_with_output().expect("the old compiler ends");
    let old = String::from_utf8_lossy(&output.stderr).into_owned();
    assert!(output.status.success(), "it still compiles, checking afresh:\n{old}");
    assert!(old.contains("TRUST_CLEAN_FACT UNMAPPED "), "it has no identity:\n{old}");
    assert!(old.contains("TRUST_CLEAN_FACT UNAVAILABLE "), "so no store:\n{old}");
    assert_eq!(stores(&old), 0, "and stores nothing:\n{old}");

    // The replacement finds nothing the old checker made under its identity.
    rfs::remove_file("lib.rs");
    rfs::write("lib.rs", SOURCE);
    let new = finish(&mut compile(&compiler));
    assert!(misses(&new) >= 1, "the replacement's compiler misses:\n{new}");
    assert!(stores(&new) >= 1, "and stores its own facts:\n{new}");
    // POSITIVE CONTROL: and imports them next time.
    let again = finish(&mut compile(&compiler));
    assert_eq!(misses(&again), 0, "{again}");
}
