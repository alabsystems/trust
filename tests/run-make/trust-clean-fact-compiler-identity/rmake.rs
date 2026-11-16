//! Trust TG6: a local kernel fact is keyed by the compiler that produced it —
//! the trustc commit, the Clean kernel version, the fact-delta format and the
//! SHA-256 of the compiler image that elaborated it. A compiler whose image
//! differs by one signature misses every fact the other one stored.
//!
//! NEGATIVE CONTROL: the same compiler, run again, imports its facts.
//!
//! The other compiler is the same sysroot with a copied driver library whose
//! bytes differ (re-signed under another identifier on macOS, one byte longer
//! elsewhere); its `lib/rustlib` is the original's, linked.

//@ ignore-cross-compile
//@ ignore-windows

use std::path::{Path, PathBuf};

use run_make_support::{cmd, cwd, env_var, rfs, rustc};

const SOURCE: &str = r#"
clean {
    theorem tg6_identity : forall (n : Nat), n + 0 = n := fun n => rfl
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

/// The same flags for either compiler.
fn args() -> Vec<String> {
    [
        "lib.rs",
        "--crate-name=tg6_identity",
        "--crate-type=lib",
        "--emit=metadata",
        "-Ztrust-verify=on",
        "-Ztrust-policy=advisory",
    ]
    .iter()
    .map(|arg| arg.to_string())
    .collect()
}

fn build_with_this_compiler() -> String {
    rustc()
        .args(args())
        .env("CARGO_HOME", cwd().join("cargo-home"))
        .env("TRUST_CLEAN_FACT_STATS", "1")
        .env_remove("TRUST_NO_VERIFY")
        .run()
        .stderr_utf8()
}

fn build_with(other: &Path) -> String {
    // No library path: the copy's own `@loader_path/../lib` (`$ORIGIN/../lib`)
    // must load ITS driver, not the original's.
    cmd(other.join("bin/rustc"))
        .args(args())
        .env("CARGO_HOME", cwd().join("cargo-home"))
        .env("TRUST_CLEAN_FACT_STATS", "1")
        .env_remove("TRUST_NO_VERIFY")
        .env_remove(env_var("LD_LIB_PATH_ENVVAR"))
        .run()
        .stderr_utf8()
}

/// A sysroot whose driver library differs from this one's in its bytes only.
fn other_compiler() -> PathBuf {
    let sysroot = PathBuf::from(rustc().print("sysroot").run().stdout_utf8().trim());
    let other = cwd().join("other-compiler");
    rfs::create_dir_all(other.join("bin"));
    rfs::create_dir_all(other.join("lib"));
    rfs::copy(sysroot.join("bin/rustc"), other.join("bin/rustc"));
    let mut driver = None;
    for entry in rfs::read_dir(sysroot.join("lib")) {
        let entry = entry.unwrap();
        let from = entry.path();
        let to = other.join("lib").join(entry.file_name());
        if from.is_dir() {
            rfs::symlink_dir(&from, &to);
        } else {
            rfs::copy(&from, &to);
            if entry.file_name().to_string_lossy().starts_with("librustc_driver") {
                driver = Some(to);
            }
        }
    }
    let driver = driver.expect("the sysroot has a driver library");
    let before = rfs::read(&driver);
    if cfg!(target_os = "macos") {
        cmd("codesign")
            .args(["-f", "-s", "-", "--identifier", "trust.tg6.other-compiler"])
            .arg(&driver)
            .run();
    } else {
        let mut bytes = before.clone();
        bytes.extend_from_slice(b"\0tg6");
        rfs::write(&driver, bytes);
    }
    assert_ne!(rfs::read(&driver), before, "the other compiler's image differs");
    other
}

fn main() {
    rfs::write("lib.rs", SOURCE);
    let first = build_with_this_compiler();
    assert!(stores(&first) >= 1, "{first}");

    // NEGATIVE CONTROL: the same compiler imports its own facts.
    let again = build_with_this_compiler();
    assert_eq!(misses(&again), 0, "{again}");

    let other = other_compiler();
    let changed = build_with(&other);
    assert!(misses(&changed) >= 1, "another compiler identity misses:\n{changed}");
    assert!(stores(&changed) >= 1, "and stores its own facts:\n{changed}");

    // Each identity keeps its own facts: both hit now.
    let other_again = build_with(&other);
    assert_eq!(misses(&other_again), 0, "{other_again}");
    let this_again = build_with_this_compiler();
    assert_eq!(misses(&this_again), 0, "{this_again}");
}
