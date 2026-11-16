//! Native source reuse must follow compiler-observed bytes, not timestamps.

use std::fs;
use std::path::Path;
use std::process::Command;

fn build(root: &Path, value: &str) -> Vec<serde_json::Value> {
    build_with_compiler(
        root,
        value,
        &std::env::var_os("RUSTC").expect("test compiler"),
        &root.join("target"),
    )
}

fn build_with_compiler(
    root: &Path,
    value: &str,
    compiler: &std::ffi::OsStr,
    target: &Path,
) -> Vec<serde_json::Value> {
    build_with_extern(root, value, compiler, target, None)
}

fn build_with_extern(
    root: &Path,
    value: &str,
    compiler: &std::ffi::OsStr,
    target: &Path,
    manual_extern: Option<&Path>,
) -> Vec<serde_json::Value> {
    let mut command = Command::new(env!("CARGO_BIN_EXE_targo"));
    command
        .current_dir(root)
        .env_clear()
        .env("HOME", root)
        .env("PATH", std::env::var_os("PATH").unwrap_or_default())
        .env("CARGO_HOME", root.join("cargo_home"))
        .env("CARGO_TARGET_DIR", target)
        .env("CONTENT_TEST_VALUE", value)
        .env("RUSTC", compiler)
        .env(
            "CONTENT_REAL_COMPILER",
            std::env::var_os("RUSTC").expect("test compiler"),
        )
        .args([
            "--unverified",
            if manual_extern.is_some() {
                "rustc"
            } else {
                "build"
            },
            "--offline",
            "--message-format=json",
        ]);
    if let Some(path) = manual_extern {
        let mut argument = std::ffi::OsString::from("manual_dep=");
        argument.push(path);
        command.args(["--", "--extern"]).arg(argument);
    }
    let result = command.output().unwrap();
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
    assert!(
        !rows.is_empty(),
        "the native build must report its compilation units"
    );
    rows
}

fn output(root: &Path) -> String {
    let result = Command::new(root.join("target/debug").join(if cfg!(windows) {
        "content_fixture.exe"
    } else {
        "content_fixture"
    }))
    .output()
    .unwrap();
    assert!(result.status.success());
    String::from_utf8(result.stdout).unwrap()
}

#[test]
fn native_sources_reuse_equal_bytes_and_reject_timestamp_hidden_changes() {
    let temporary = tempfile::tempdir_in(std::env::current_dir().unwrap()).unwrap();
    let root = temporary.path();
    let dependency = root.join("cargo_home/registry/content_dep");
    fs::create_dir_all(dependency.join("src")).unwrap();
    fs::create_dir_all(root.join("src")).unwrap();
    fs::write(root.join("Cargo.toml"), "[package]\nname='content_fixture'\nversion='0.0.0'\nedition='2021'\n[workspace]\n[dependencies]\ncontent_dep={path='cargo_home/registry/content_dep'}\n").unwrap();
    fs::write(
        dependency.join("Cargo.toml"),
        "[package]\nname='content_dep'\nversion='0.0.0'\nedition='2021'\n",
    )
    .unwrap();
    fs::write(root.join("src/main.rs"), "fn main() { print!(\"{} {} {}\", content_dep::value(), content_dep::DATA, content_dep::ENV); }\n").unwrap();
    let source = dependency.join("src/lib.rs");
    fs::write(&source, "pub fn value() -> u8 { 9 }\npub const DATA: &str = include_str!(\"value.txt\");\npub const ENV: &str = env!(\"CONTENT_TEST_VALUE\");\n").unwrap();
    let included = dependency.join("src/value.txt");
    fs::write(&included, "one").unwrap();

    let cold = build(root, "alpha");
    assert_eq!(cold.len(), 2, "both compilation units must be observed");
    assert!(cold.iter().all(|row| row["fresh"] == false));
    assert_eq!(output(root), "9 one alpha");
    assert!(build(root, "alpha").iter().all(|row| row["fresh"] == true));

    let changed_time = filetime::FileTime::from_system_time(
        std::time::SystemTime::now() + std::time::Duration::from_secs(60),
    );
    for file in [&source, &included, &root.join("src/main.rs")] {
        filetime::set_file_mtime(file, changed_time).unwrap();
    }
    assert!(
        build(root, "alpha").iter().all(|row| row["fresh"] == true),
        "timestamp-only changes must not run the compiler"
    );

    let bytes = fs::read_to_string(&source).unwrap();
    fs::write(&source, bytes.replace("{ 9 }", "{ 8 }")).unwrap();
    filetime::set_file_mtime(&source, changed_time).unwrap();
    assert!(
        build(root, "alpha").iter().all(|row| row["fresh"] == false),
        "same-size source changes inside cargo_home must invalidate"
    );
    assert_eq!(output(root), "8 one alpha");

    fs::write(&included, "two").unwrap();
    filetime::set_file_mtime(&included, changed_time).unwrap();
    assert!(
        build(root, "alpha").iter().all(|row| row["fresh"] == false),
        "compiler-observed include bytes must invalidate"
    );
    assert_eq!(output(root), "8 two alpha");

    assert!(
        build(root, "omega").iter().all(|row| row["fresh"] == false),
        "compiler-observed environment must still invalidate"
    );
    assert_eq!(output(root), "8 two omega");
    assert!(build(root, "omega").iter().all(|row| row["fresh"] == true));

    #[cfg(unix)]
    {
        use std::os::unix::fs::symlink;
        let first = dependency.join("src/first.txt");
        let second = dependency.join("src/second.txt");
        fs::write(&first, "one").unwrap();
        fs::write(&second, "two").unwrap();
        filetime::set_file_mtime(&first, changed_time).unwrap();
        filetime::set_file_mtime(&second, changed_time).unwrap();
        fs::remove_file(&included).unwrap();
        symlink("first.txt", &included).unwrap();
        assert!(build(root, "omega").iter().all(|row| row["fresh"] == false));
        assert_eq!(output(root), "8 one omega");
        fs::remove_file(&included).unwrap();
        symlink("second.txt", &included).unwrap();
        assert!(
            build(root, "omega").iter().all(|row| row["fresh"] == false),
            "the compiler-observed path must follow a retargeted symlink"
        );
        assert_eq!(output(root), "8 two omega");
    }
}

#[test]
fn a_compiler_missing_either_content_option_still_builds_and_reuses() {
    for option in ["checksum-hash-algorithm", "binary-dep-depinfo"] {
        compiler_missing_content_option(option);
    }
}

fn compiler_missing_content_option(option: &str) {
    let temporary = tempfile::tempdir_in(std::env::current_dir().unwrap()).unwrap();
    let root = temporary.path();
    fs::create_dir_all(root.join("src")).unwrap();
    fs::write(root.join("Cargo.toml"), "[package]\nname='incapable_compiler_fixture'\nversion='0.0.0'\nedition='2021'\n[workspace]\n").unwrap();
    // Build a native test compiler proxy. It rejects only the optional
    // capability query, and delegates every real compilation to the SDK.
    fs::write(root.join("src/main.rs"), r#"
        fn main() {
            let args: Vec<_> = std::env::args_os().skip(1).collect();
            if args.iter().any(|a| a.to_string_lossy().contains("REJECTED_OPTION")) {
                std::process::exit(1);
            }
            let status = std::process::Command::new(std::env::var_os("CONTENT_REAL_COMPILER").unwrap())
                .args(args).env_remove("CARGO_MAKEFLAGS").env_remove("MAKEFLAGS")
                .status().unwrap();
            std::process::exit(status.code().unwrap_or(1));
        }
    "#.replace("REJECTED_OPTION", option)).unwrap();
    let compiler = std::env::var_os("RUSTC").expect("test compiler");
    let proxy_target = root.join("proxy-target");
    let built = build_with_compiler(root, "alpha", &compiler, &proxy_target);
    assert_eq!(built.len(), 1);
    let proxy = proxy_target.join("debug").join(if cfg!(windows) {
        "incapable_compiler_fixture.exe"
    } else {
        "incapable_compiler_fixture"
    });
    fs::write(
        root.join("src/main.rs"),
        "fn main() { assert_eq!(2 + 2, 4); }\n",
    )
    .unwrap();
    let target = root.join("target");
    assert!(
        build_with_compiler(root, "alpha", proxy.as_os_str(), &target)
            .iter()
            .all(|row| row["fresh"] == false)
    );
    assert!(
        build_with_compiler(root, "alpha", proxy.as_os_str(), &target)
            .iter()
            .all(|row| row["fresh"] == true)
    );
}

#[test]
fn native_manual_extern_reuse_follows_binary_bytes_at_the_same_path() {
    let temporary = tempfile::tempdir_in(std::env::current_dir().unwrap()).unwrap();
    let root = temporary.path();
    let dependency = root.join("dependency");
    let consumer = root.join("consumer");
    for package in [&dependency, &consumer] {
        fs::create_dir_all(package.join("src")).unwrap();
    }
    fs::write(
        dependency.join("Cargo.toml"),
        "[package]\nname='manual_dep'\nversion='0.0.0'\nedition='2021'\n[workspace]\n",
    )
    .unwrap();
    let source = dependency.join("src/lib.rs");
    fs::write(&source, "pub const VALUE: u8 = 1;\n").unwrap();
    assert!(
        build(&dependency, "alpha")
            .iter()
            .all(|row| row["fresh"] == false)
    );
    let external = root.join("libmanual_dep.rlib");
    fs::copy(
        dependency.join("target/debug/libmanual_dep.rlib"),
        &external,
    )
    .unwrap();
    fs::write(
        consumer.join("Cargo.toml"),
        "[package]\nname='content_fixture'\nversion='0.0.0'\nedition='2021'\n[workspace]\n",
    )
    .unwrap();
    fs::write(
        consumer.join("src/main.rs"),
        "fn main() { print!(\"{}\", manual_dep::VALUE); }\n",
    )
    .unwrap();
    let compiler = std::env::var_os("RUSTC").expect("test compiler");
    let target = consumer.join("target");
    let compile = || build_with_extern(&consumer, "alpha", &compiler, &target, Some(&external));
    assert!(compile().iter().all(|row| row["fresh"] == false));
    assert_eq!(output(&consumer), "1");
    assert!(compile().iter().all(|row| row["fresh"] == true));

    let changed_time = filetime::FileTime::from_system_time(
        std::time::SystemTime::now() + std::time::Duration::from_secs(60),
    );
    filetime::set_file_mtime(&external, changed_time).unwrap();
    assert!(
        compile().iter().all(|row| row["fresh"] == true),
        "timestamp-only external-library changes must remain reusable"
    );
    let original = fs::read(&external).unwrap();
    fs::write(&source, "pub const VALUE: u8 = 2;\n").unwrap();
    assert!(
        build(&dependency, "alpha")
            .iter()
            .all(|row| row["fresh"] == false)
    );
    fs::copy(
        dependency.join("target/debug/libmanual_dep.rlib"),
        &external,
    )
    .unwrap();
    filetime::set_file_mtime(&external, changed_time).unwrap();
    assert_ne!(fs::read(&external).unwrap(), original);
    assert!(
        compile().iter().all(|row| row["fresh"] == false),
        "used binary bytes changed with the exact extern path and timestamp preserved"
    );
    assert_eq!(output(&consumer), "2");
    assert!(compile().iter().all(|row| row["fresh"] == true));
}
