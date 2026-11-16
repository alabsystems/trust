//! A display version cannot identify the compiler that produced an artifact.

use std::ffi::OsStr;
use std::fs;
use std::path::Path;
use std::process::Command;

fn build(root: &Path, compiler: &OsStr, features: &[&str]) -> Vec<serde_json::Value> {
    let executable = std::env::var_os("TARGO_COMPILER_IDENTITY_TEST_BINARY")
        .unwrap_or_else(|| env!("CARGO_BIN_EXE_targo").into());
    let result = Command::new(executable)
        .current_dir(root)
        .env_clear()
        .env("HOME", root)
        .env("CARGO_HOME", root.join("home"))
        .env("CARGO_TARGET_DIR", root.join("target"))
        .env("PATH", std::env::var_os("PATH").unwrap_or_default())
        .env("RUSTC", compiler)
        .env("REAL_COMPILER", std::env::var_os("RUSTC").unwrap())
        .env("COMPILER_TRACE", root.join("compiler-trace"))
        .env("TEST_SYSROOT", root.join("sysroot"))
        .args([
            "--unverified",
            "build",
            "--offline",
            "--message-format=json",
        ])
        .args(features)
        .output()
        .unwrap();
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    let rows: Vec<_> = String::from_utf8(result.stdout)
        .unwrap()
        .lines()
        .filter_map(|line| serde_json::from_str::<serde_json::Value>(line).ok())
        .filter(|row| row["reason"] == "compiler-artifact")
        .collect();
    assert!(!rows.is_empty());
    rows
}

fn binary(root: &Path, name: &str) -> std::path::PathBuf {
    root.join("target/debug")
        .join(format!("{name}{}", std::env::consts::EXE_SUFFIX))
}

#[test]
fn equal_version_and_metadata_do_not_hide_changed_compiler_bytes() {
    let temp = tempfile::tempdir_in(std::env::current_dir().unwrap()).unwrap();
    let proxy_root = temp.path().join("proxy");
    fs::create_dir_all(proxy_root.join("src")).unwrap();
    fs::write(proxy_root.join("Cargo.toml"), "[package]\nname='compiler_proxy'\nversion='0.0.0'\nedition='2021'\n[workspace]\n[features]\ntwo=[]\n[profile.dev]\ndebug=0\nincremental=false\n").unwrap();
    fs::write(
        proxy_root.join("src/main.rs"),
        r#"
        use std::io::Write;
        fn main() {
            let args: Vec<_> = std::env::args_os().skip(1).collect();
            let sysroot = std::path::PathBuf::from(std::env::var_os("TEST_SYSROOT").unwrap());
            if sysroot.is_dir() && args.len() == 1 && args[0] == "--print=sysroot" {
                println!("{}", sysroot.display());
                return;
            }
            let choice = if sysroot.is_dir() {
                let library = std::fs::read(sysroot.join("lib/rustlib/native/lib/libcore.rlib")).unwrap();
                if library == b"two" { "choice_two" } else { "choice_one" }
            } else if cfg!(feature="two") { "choice_two" } else { "choice_one" };
            let mut cmd = std::process::Command::new(std::env::var_os("REAL_COMPILER").unwrap());
            if args.iter().any(|arg| arg == "-vV") {
                let mut trace = std::fs::OpenOptions::new().create(true).append(true)
                    .open(std::env::var_os("COMPILER_TRACE").unwrap()).unwrap();
                writeln!(trace, "{choice}").unwrap();
            } else {
                if let Some(metadata) = args.iter().find(|arg| {
                    let value = arg.to_string_lossy();
                    value.starts_with("metadata=") || value.starts_with("-Cmetadata=")
                }) {
                    let mut trace = std::fs::OpenOptions::new().create(true).append(true)
                        .open(std::env::var_os("COMPILER_TRACE").unwrap()).unwrap();
                    writeln!(trace, "symbol-{}", metadata.to_string_lossy()).unwrap();
                }
                cmd.args(["--cfg", choice]);
            }
            let status = cmd.args(args).env_remove("CARGO_MAKEFLAGS")
                .env_remove("MAKEFLAGS").status().unwrap();
            std::process::exit(status.code().unwrap_or(1));
        }
    "#,
    )
    .unwrap();
    let real = std::env::var_os("RUSTC").unwrap();
    build(&proxy_root, &real, &[]);
    let first = fs::read(binary(&proxy_root, "compiler_proxy")).unwrap();
    build(&proxy_root, &real, &["--features", "two"]);
    let second = fs::read(binary(&proxy_root, "compiler_proxy")).unwrap();
    assert_ne!(first, second);
    assert_eq!(
        first.len(),
        second.len(),
        "the replacement must preserve file size"
    );

    let root = temp.path().join("consumer");
    fs::create_dir_all(root.join("src")).unwrap();
    fs::write(
        root.join("Cargo.toml"),
        "[package]\nname='consumer'\nversion='0.0.0'\nedition='2021'\n[workspace]\n",
    )
    .unwrap();
    fs::write(
        root.join("src/main.rs"),
        "fn main() { #[cfg(choice_one)] print!(\"one\"); #[cfg(choice_two)] print!(\"two\"); }\n",
    )
    .unwrap();
    let proxy = root.join(format!("compiler{}", std::env::consts::EXE_SUFFIX));
    fs::copy(binary(&proxy_root, "compiler_proxy"), &proxy).unwrap();
    fs::write(&proxy, &first).unwrap();
    let timestamp = filetime::FileTime::from_last_modification_time(&fs::metadata(&proxy).unwrap());
    assert!(
        build(&root, proxy.as_os_str(), &[])
            .iter()
            .all(|row| row["fresh"] == false)
    );
    assert_eq!(
        Command::new(binary(&root, "consumer"))
            .output()
            .unwrap()
            .stdout,
        b"one"
    );
    assert!(
        build(&root, proxy.as_os_str(), &[])
            .iter()
            .all(|row| row["fresh"] == true)
    );

    let prior_trace = fs::read(root.join("compiler-trace")).unwrap();
    let changed_time = filetime::FileTime::from_system_time(
        std::time::SystemTime::now() + std::time::Duration::from_secs(60),
    );
    filetime::set_file_mtime(&proxy, changed_time).unwrap();
    assert!(
        build(&root, proxy.as_os_str(), &[])
            .iter()
            .all(|row| row["fresh"] == true)
    );
    assert_eq!(
        fs::read(root.join("compiler-trace")).unwrap(),
        prior_trace,
        "touching the same compiler bytes must preserve the probe cache"
    );

    fs::write(&proxy, &second).unwrap();
    filetime::set_file_mtime(&proxy, timestamp).unwrap();
    assert!(
        build(&root, proxy.as_os_str(), &[])
            .iter()
            .all(|row| row["fresh"] == false),
        "a different compiler reporting the same -vV must invalidate artifacts"
    );
    assert_eq!(
        Command::new(binary(&root, "consumer"))
            .output()
            .unwrap()
            .stdout,
        b"two"
    );
    let trace = fs::read_to_string(root.join("compiler-trace")).unwrap();
    assert!(
        trace.contains("choice_one") && trace.contains("choice_two"),
        "the compiler capability/version cache must also refresh"
    );
    assert!(
        build(&root, proxy.as_os_str(), &[])
            .iter()
            .all(|row| row["fresh"] == true)
    );
    let symbols: Vec<_> = trace
        .lines()
        .filter(|line| line.starts_with("symbol-"))
        .collect();
    assert_eq!(symbols.len(), 2, "observe both real compiler invocations");
    assert_eq!(
        symbols[0], symbols[1],
        "cache identity must not change Rust symbol metadata"
    );

    // The earlier compiler's product remains available; this is reuse, not a
    // second execution of that compiler after switching back.
    fs::write(&proxy, &first).unwrap();
    filetime::set_file_mtime(&proxy, timestamp).unwrap();
    assert!(
        build(&root, proxy.as_os_str(), &[])
            .iter()
            .all(|row| row["fresh"] == true),
        "switching back must reuse the earlier compiler's artifact"
    );
    assert_eq!(
        Command::new(binary(&root, "consumer"))
            .output()
            .unwrap()
            .stdout,
        b"one"
    );

    // Keep the compiler executable and reported version unchanged while its
    // selected sysroot changes. This native proxy makes the library an actual
    // compilation input, so stale reuse produces the wrong observable program.
    let library_dir = root.join("sysroot/lib/rustlib/native/lib");
    fs::create_dir_all(&library_dir).unwrap();
    let library = library_dir.join("libcore.rlib");
    fs::write(&library, b"two").unwrap();
    let rebuilt = build(&root, proxy.as_os_str(), &[]);
    assert_eq!(
        Command::new(binary(&root, "consumer"))
            .output()
            .unwrap()
            .stdout,
        b"two",
        "a changed selected sysroot must not replay the old program"
    );
    assert!(rebuilt.iter().all(|row| row["fresh"] == false));
    assert!(
        build(&root, proxy.as_os_str(), &[])
            .iter()
            .all(|row| row["fresh"] == true)
    );
    let stamp = filetime::FileTime::from_last_modification_time(&fs::metadata(&library).unwrap());
    filetime::set_file_mtime(&library, changed_time).unwrap();
    assert!(
        build(&root, proxy.as_os_str(), &[])
            .iter()
            .all(|row| row["fresh"] == true)
    );
    fs::write(&library, b"one").unwrap();
    filetime::set_file_mtime(&library, stamp).unwrap();
    assert!(
        build(&root, proxy.as_os_str(), &[])
            .iter()
            .all(|row| row["fresh"] == false)
    );
    assert_eq!(
        Command::new(binary(&root, "consumer"))
            .output()
            .unwrap()
            .stdout,
        b"one"
    );
    fs::write(&library, b"two").unwrap();
    filetime::set_file_mtime(&library, stamp).unwrap();
    assert!(
        build(&root, proxy.as_os_str(), &[])
            .iter()
            .all(|row| row["fresh"] == true)
    );
    assert_eq!(
        Command::new(binary(&root, "consumer"))
            .output()
            .unwrap()
            .stdout,
        b"two"
    );
}
