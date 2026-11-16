//! Tests for the `cargo clean` command.

use crate::prelude::*;
use cargo_test_support::compare::assert_e2e;
use cargo_test_support::registry::Package;
use cargo_test_support::str;
use cargo_test_support::{
    basic_bin_manifest, basic_manifest, git, main_file, project, project_in, rustc_host,
};
use glob::GlobError;
use std::env;
use std::path::{Path, PathBuf};

#[cargo_test]
fn cargo_clean_simple() {
    let p = project()
        .file("Cargo.toml", &basic_bin_manifest("foo"))
        .file("src/foo.rs", &main_file(r#""i am foo""#, &[]))
        .build();

    p.cargo("build")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .run();
    assert!(p.build_dir().is_dir());

    p.cargo("clean")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .run();
    assert!(!p.build_dir().is_dir());
}

#[cargo_test]
fn different_dir() {
    let p = project()
        .file("Cargo.toml", &basic_bin_manifest("foo"))
        .file("src/foo.rs", &main_file(r#""i am foo""#, &[]))
        .file("src/bar/a.rs", "")
        .build();

    p.cargo("build")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .run();
    assert!(p.build_dir().is_dir());

    p.cargo("clean")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .cwd("src")
        .with_stderr_data(str![[r#"
[REMOVED] [FILE_NUM] files, [FILE_SIZE]B total

"#]])
        .run();
    assert!(!p.build_dir().is_dir());
}

#[cargo_test]
fn clean_multiple_packages() {
    let p = project()
        .file(
            "Cargo.toml",
            r#"
                [package]
                name = "foo"
                version = "0.0.1"
                edition = "2015"
                authors = []

                [dependencies.d1]
                    path = "d1"
                [dependencies.d2]
                    path = "d2"

                [[bin]]
                    name = "foo"
            "#,
        )
        .file("src/foo.rs", &main_file(r#""i am foo""#, &[]))
        .file("d1/Cargo.toml", &basic_bin_manifest("d1"))
        .file("d1/src/main.rs", "fn main() { println!(\"d1\"); }")
        .file("d2/Cargo.toml", &basic_bin_manifest("d2"))
        .file("d2/src/main.rs", "fn main() { println!(\"d2\"); }")
        .build();

    p.cargo("build -p d1 -p d2 -p foo")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .run();

    let d1_path = &p
        .build_dir()
        .join("debug")
        .join(format!("d1{}", env::consts::EXE_SUFFIX));
    let d2_path = &p
        .build_dir()
        .join("debug")
        .join(format!("d2{}", env::consts::EXE_SUFFIX));

    assert!(p.bin("foo").is_file());
    assert!(d1_path.is_file());
    assert!(d2_path.is_file());

    p.cargo("clean -p d1 -p d2")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .cwd("src")
        .with_stderr_data(str![[r#"
[REMOVED] [FILE_NUM] files, [FILE_SIZE]B total

"#]])
        .run();
    assert!(p.bin("foo").is_file());
    assert!(!d1_path.is_file());
    assert!(!d2_path.is_file());
}

#[cargo_test]
fn clean_multiple_packages_in_glob_char_path() {
    let p = project_in("[d1]")
        .file("Cargo.toml", &basic_bin_manifest("foo"))
        .file("src/foo.rs", &main_file(r#""i am foo""#, &[]))
        .build();
    let foo_path = &p.build_dir().join("debug").join("deps");

    #[cfg(not(target_env = "msvc"))]
    let file_glob = "foo-*";

    #[cfg(target_env = "msvc")]
    let file_glob = "foo.pdb";

    // Assert that build artifacts are produced
    p.cargo("build")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .run();
    assert_ne!(get_build_artifacts(foo_path, file_glob).len(), 0);

    // Assert that build artifacts are destroyed
    p.cargo("clean -p foo")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .run();
    assert_eq!(get_build_artifacts(foo_path, file_glob).len(), 0);
}

fn get_build_artifacts(path: &PathBuf, file_glob: &str) -> Vec<Result<PathBuf, GlobError>> {
    let pattern = path.to_str().expect("expected utf-8 path");
    let pattern = glob::Pattern::escape(pattern);

    let path = PathBuf::from(pattern).join(file_glob);
    let path = path.to_str().expect("expected utf-8 path");
    glob::glob(path)
        .expect("expected glob to run")
        .into_iter()
        .collect::<Vec<Result<PathBuf, GlobError>>>()
}

#[cargo_test]
fn clean_p_only_cleans_specified_package() {
    let p = project()
        .file(
            "Cargo.toml",
            r#"
                [workspace]
                members = [
                    "foo",
                    "foo_core",
                    "foo-base",
                ]
            "#,
        )
        .file("foo/Cargo.toml", &basic_manifest("foo", "0.1.0"))
        .file("foo/src/lib.rs", "//! foo")
        .file("foo_core/Cargo.toml", &basic_manifest("foo_core", "0.1.0"))
        .file("foo_core/src/lib.rs", "//! foo_core")
        .file("foo-base/Cargo.toml", &basic_manifest("foo-base", "0.1.0"))
        .file("foo-base/src/lib.rs", "//! foo-base")
        .build();

    let fingerprint_path = &p.build_dir().join("debug").join(".fingerprint");

    p.cargo("build -p foo -p foo_core -p foo-base")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .run();

    let mut fingerprint_names = get_fingerprints_without_hashes(fingerprint_path);

    // Artifacts present for all after building
    assert!(fingerprint_names.iter().any(|e| e == "foo"));
    let num_foo_core_artifacts = fingerprint_names
        .iter()
        .filter(|&e| e == "foo_core")
        .count();
    assert_ne!(num_foo_core_artifacts, 0);
    let num_foo_base_artifacts = fingerprint_names
        .iter()
        .filter(|&e| e == "foo-base")
        .count();
    assert_ne!(num_foo_base_artifacts, 0);

    p.cargo("clean -p foo")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .run();

    fingerprint_names = get_fingerprints_without_hashes(fingerprint_path);

    // Cleaning `foo` leaves artifacts for the others
    assert!(!fingerprint_names.iter().any(|e| e == "foo"));
    assert_eq!(
        fingerprint_names
            .iter()
            .filter(|&e| e == "foo_core")
            .count(),
        num_foo_core_artifacts,
    );
    assert_eq!(
        fingerprint_names
            .iter()
            .filter(|&e| e == "foo-base")
            .count(),
        num_foo_core_artifacts,
    );
}

#[cargo_test]
fn clean_workspace_does_not_touch_non_workspace_packages() {
    Package::new("external_dependency", "0.1.0").publish();
    let foo_manifest = r#"
        [package]
        name = "foo"
        version = "0.1.0"
        edition = "2015"

        [dependencies]
        external_dependency = "0.1.0"
        "#;
    let p = project()
        .file(
            "Cargo.toml",
            r#"
                [workspace]
                members = [
                    "foo",
                    "foo_core",
                    "foo-base",
                ]
            "#,
        )
        .file("foo/Cargo.toml", foo_manifest)
        .file("foo/src/lib.rs", "//! foo")
        .file("foo_core/Cargo.toml", &basic_manifest("foo_core", "0.1.0"))
        .file("foo_core/src/lib.rs", "//! foo_core")
        .file("foo-base/Cargo.toml", &basic_manifest("foo-base", "0.1.0"))
        .file("foo-base/src/lib.rs", "//! foo-base")
        .build();

    let fingerprint_path = &p.build_dir().join("debug").join(".fingerprint");

    p.cargo("check -p foo -p foo_core -p foo-base")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .run();

    let mut fingerprint_names = get_fingerprints_without_hashes(fingerprint_path);

    // Artifacts present for all after building
    assert!(fingerprint_names.iter().any(|e| e == "foo"));
    assert!(fingerprint_names.iter().any(|e| e == "foo_core"));
    assert!(fingerprint_names.iter().any(|e| e == "foo-base"));

    let num_external_dependency_artifacts = fingerprint_names
        .iter()
        .filter(|&e| e == "external_dependency")
        .count();
    assert_ne!(num_external_dependency_artifacts, 0);

    p.cargo("clean --workspace")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .run();

    fingerprint_names = get_fingerprints_without_hashes(fingerprint_path);

    // Cleaning workspace members leaves artifacts for the external dependency
    assert!(
        !fingerprint_names
            .iter()
            .any(|e| e == "foo" || e == "foo_core" || e == "foo-base")
    );
    assert_eq!(
        fingerprint_names
            .iter()
            .filter(|&e| e == "external_dependency")
            .count(),
        num_external_dependency_artifacts,
    );
}

#[cargo_test]
fn clean_workspace_with_extra_package_specifiers() {
    Package::new("external_dependency_1", "0.1.0").publish();
    Package::new("external_dependency_2", "0.1.0").publish();
    let foo_manifest = r#"
        [package]
        name = "foo"
        version = "0.1.0"
        edition = "2015"

        [dependencies]
        external_dependency_1 = "0.1.0"
        external_dependency_2 = "0.1.0"
        "#;
    let p = project()
        .file(
            "Cargo.toml",
            r#"
                [workspace]
                members = [
                    "foo",
                    "foo_core",
                    "foo-base",
                ]
            "#,
        )
        .file("foo/Cargo.toml", foo_manifest)
        .file("foo/src/lib.rs", "//! foo")
        .file("foo_core/Cargo.toml", &basic_manifest("foo_core", "0.1.0"))
        .file("foo_core/src/lib.rs", "//! foo_core")
        .file("foo-base/Cargo.toml", &basic_manifest("foo-base", "0.1.0"))
        .file("foo-base/src/lib.rs", "//! foo-base")
        .build();

    let fingerprint_path = &p.build_dir().join("debug").join(".fingerprint");

    p.cargo("check -p foo -p foo_core -p foo-base")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .run();

    let mut fingerprint_names = get_fingerprints_without_hashes(fingerprint_path);

    // Artifacts present for all after building
    assert!(fingerprint_names.iter().any(|e| e == "foo"));
    assert!(fingerprint_names.iter().any(|e| e == "foo_core"));
    assert!(fingerprint_names.iter().any(|e| e == "foo-base"));

    let num_external_dependency_2_artifacts = fingerprint_names
        .iter()
        .filter(|&e| e == "external_dependency_2")
        .count();
    assert_ne!(num_external_dependency_2_artifacts, 0);

    p.cargo("clean --workspace -p external_dependency_1")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .run();

    fingerprint_names = get_fingerprints_without_hashes(fingerprint_path);

    // Cleaning workspace members and external_dependency_1 leaves artifacts for the external_dependency_2
    assert!(
        !fingerprint_names.iter().any(|e| e == "foo"
            || e == "foo_core"
            || e == "foo-base"
            || e == "external_dependency_1")
    );
    assert_eq!(
        fingerprint_names
            .iter()
            .filter(|&e| e == "external_dependency_2")
            .count(),
        num_external_dependency_2_artifacts,
    );
}

fn get_fingerprints_without_hashes(fingerprint_path: &Path) -> Vec<String> {
    std::fs::read_dir(fingerprint_path)
        .expect("Build dir should be readable")
        .filter_map(|entry| entry.ok())
        .map(|entry| {
            let name = entry.file_name();
            let name = name
                .into_string()
                .expect("fingerprint name should be UTF-8");
            name.rsplit_once('-')
                .expect("Name should contain at least one hyphen")
                .0
                .to_owned()
        })
        .collect()
}

#[cargo_test]
fn clean_release() {
    let p = project()
        .file(
            "Cargo.toml",
            r#"
                [package]
                name = "foo"
                version = "0.0.1"
                edition = "2015"
                authors = []

                [dependencies]
                a = { path = "a" }

                [lints.cargo]
                default = "allow"
            "#,
        )
        .file("src/main.rs", "fn main() {}")
        .file("a/Cargo.toml", &basic_manifest("a", "0.0.1"))
        .file("a/src/lib.rs", "")
        .build();

    p.cargo("build --release")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .run();

    p.cargo("clean -p foo")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .run();
    p.cargo("build --release")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .with_stderr_data(str![[r#"
[FINISHED] `release` profile [optimized] target(s) in [ELAPSED]s

"#]])
        .run();

    p.cargo("clean -p foo --release")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .run();
    p.cargo("build --release")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .with_stderr_data(str![[r#"
[COMPILING] foo v0.0.1 ([ROOT]/foo)
[FINISHED] `release` profile [optimized] target(s) in [ELAPSED]s

"#]])
        .run();

    p.cargo("build")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .run();

    p.cargo("clean")
        .arg("--release")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .run();
    assert!(p.build_dir().is_dir());
    assert!(p.build_dir().join("debug").is_dir());
    assert!(!p.build_dir().join("release").is_dir());
}

#[cargo_test]
fn clean_doc() {
    let p = project()
        .file(
            "Cargo.toml",
            r#"
                [package]
                name = "foo"
                version = "0.0.1"
                edition = "2015"
                authors = []

                [dependencies]
                a = { path = "a" }
            "#,
        )
        .file("src/main.rs", "fn main() {}")
        .file("a/Cargo.toml", &basic_manifest("a", "0.0.1"))
        .file("a/src/lib.rs", "")
        .build();

    p.cargo("doc")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .run();

    let doc_path = &p.build_dir().join("doc");

    assert!(doc_path.is_dir());

    p.cargo("clean --doc")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .with_stderr_data(str![[r#"
[REMOVED] [FILE_NUM] files, [FILE_SIZE]B total

"#]])
        .run();

    assert!(!doc_path.is_dir());
    assert!(p.build_dir().is_dir());
}

#[cargo_test]
fn clean_doc_target() {
    let target = rustc_host();
    let p = project()
        .file("Cargo.toml", &basic_manifest("foo", "0.1.0"))
        .file("src/lib.rs", "")
        .build();
    let doc_path = p.build_dir().join(target).join("doc");

    p.cargo("doc --target")
        .arg(target)
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .run();
    assert!(doc_path.is_dir());

    p.cargo("clean --doc --target")
        .arg(target)
        .with_stderr_data(str![[r#"
[REMOVED] [FILE_NUM] files, [FILE_SIZE]B total

"#]])
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .run();
    assert!(!doc_path.is_dir());

    p.change_file(
        ".cargo/config.toml",
        &format!("[build]\ntarget = \"{target}\""),
    );
    p.cargo("doc")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .run();
    assert!(doc_path.is_dir());

    p.cargo("clean --doc")
        .with_stderr_data(str![[r#"
[REMOVED] [FILE_NUM] files, [FILE_SIZE]B total

"#]])
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .run();
    assert!(!doc_path.is_dir());
}

#[cargo_test]
fn build_script() {
    let p = project()
        .file(
            "Cargo.toml",
            r#"
                [package]
                name = "foo"
                version = "0.0.1"
                edition = "2015"
                authors = []
                build = "build.rs"
            "#,
        )
        .file("src/main.rs", "fn main() {}")
        .file(
            "build.rs",
            r#"
                use std::path::PathBuf;
                use std::env;

                fn main() {
                    let out = PathBuf::from(env::var_os("OUT_DIR").unwrap());
                    if env::var("FIRST").is_ok() {
                        std::fs::File::create(out.join("out")).unwrap();
                    } else {
                        assert!(!out.join("out").exists());
                    }
                }
            "#,
        )
        .file("a/src/lib.rs", "")
        .build();

    p.cargo("build")
        .env("FIRST", "1")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .run();
    p.cargo("clean -p foo")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .run();
    p.cargo("build -v")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .with_stderr_data(str![[r#"
[COMPILING] foo v0.0.1 ([ROOT]/foo)
[RUNNING] `rustc [..] build.rs [..]`
[RUNNING] `[ROOT]/foo/target/debug/build/foo-[HASH]/build-script-build`
[RUNNING] `rustc [..] src/main.rs [..]`
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();
}

#[cargo_test]
fn clean_git() {
    let git = git::new("dep", |project| {
        project
            .file("Cargo.toml", &basic_manifest("dep", "0.5.0"))
            .file("src/lib.rs", "")
    });

    let p = project()
        .file(
            "Cargo.toml",
            &format!(
                r#"
                    [package]
                    name = "foo"
                    version = "0.0.1"
                    edition = "2015"
                    authors = []

                    [dependencies]
                    dep = {{ git = '{}' }}
                "#,
                git.url()
            ),
        )
        .file("src/main.rs", "fn main() {}")
        .build();

    p.cargo("build")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .run();
    p.cargo("clean -p dep")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .with_stderr_data(str![[r#"
[REMOVED] [FILE_NUM] files, [FILE_SIZE]B total

"#]])
        .run();
    p.cargo("build")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .run();
}

#[cargo_test]
fn registry() {
    let p = project()
        .file(
            "Cargo.toml",
            r#"
                [package]
                name = "foo"
                version = "0.0.1"
                edition = "2015"
                authors = []

                [dependencies]
                bar = "0.1"
            "#,
        )
        .file("src/main.rs", "fn main() {}")
        .build();

    Package::new("bar", "0.1.0").publish();

    p.cargo("build")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .run();
    p.cargo("clean -p bar")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .with_stderr_data(str![[r#"
[REMOVED] [FILE_NUM] files, [FILE_SIZE]B total

"#]])
        .run();
    p.cargo("build")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .run();
}

#[cargo_test]
fn clean_verbose() {
    let p = project()
        .file(
            "Cargo.toml",
            r#"
                [package]
                name = "foo"
                version = "0.0.1"
                edition = "2015"

                [dependencies]
                bar = "0.1"
            "#,
        )
        .file("src/main.rs", "fn main() {}")
        .build();

    Package::new("bar", "0.1.0").publish();

    p.cargo("build")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .run();
    let mut expected = String::from(
        "\
[REMOVING] [ROOT]/foo/target/debug/.fingerprint/bar-[HASH]
[REMOVING] [ROOT]/foo/target/debug/deps/libbar-[HASH].rlib
[REMOVING] [ROOT]/foo/target/debug/deps/bar-[HASH].d
[REMOVING] [ROOT]/foo/target/debug/deps/libbar-[HASH].rmeta
",
    );
    if cfg!(target_os = "macos") {
        // Rust 1.69 has changed so that split-debuginfo=unpacked includes unpacked for rlibs.
        for _ in p.glob("target/debug/deps/bar-*.o") {
            expected.push_str("[REMOVING] [ROOT]/foo/target/debug/deps/bar-[HASH][..].o\n");
        }
    }
    // Trust: a protocol-capable compiler declares this additional owned cache.
    // Keep every original non-cache removal line and require its real removal too.
    for dep_info in p.glob("target/debug/deps/bar-*.d") {
        for line in std::fs::read_to_string(dep_info.unwrap()).unwrap().lines() {
            if let Some(store) = line.strip_prefix("# trust-witness-output-v1:") {
                assert_eq!(store.len(), 21);
                assert!(store.ends_with(".twit"));
                assert!(
                    store[..16]
                        .bytes()
                        .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
                );
                expected.push_str(&format!(
                    "[REMOVING] [ROOT]/foo/target/debug/deps/{store}\n"
                ));
            }
        }
    }
    expected.push_str("[REMOVED] [FILE_NUM] files, [FILE_SIZE]B total\n");
    p.cargo("clean -p bar --verbose")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .with_stderr_data(&expected.unordered())
        .run();
    p.cargo("build")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .run();
}

#[cargo_test]
fn clean_remove_rlib_rmeta() {
    let p = project()
        .file(
            "Cargo.toml",
            r#"
                [package]
                name = "foo"
                version = "0.0.1"
                edition = "2015"
            "#,
        )
        .file("src/lib.rs", "")
        .build();

    p.cargo("build")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .run();
    assert!(p.target_debug_dir().join("libfoo.rlib").exists());
    let rmeta = p.glob("target/debug/deps/*.rmeta").next().unwrap().unwrap();
    assert!(rmeta.exists());
    p.cargo("clean -p foo")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .run();
    assert!(!p.target_debug_dir().join("libfoo.rlib").exists());
    assert!(!rmeta.exists());
}

#[cargo_test]
fn package_cleans_all_the_things() {
    // -p cleans everything
    // Use dashes everywhere to make sure dash/underscore stuff is handled.
    for crate_type in &["rlib", "dylib", "cdylib", "staticlib", "proc-macro"] {
        // Try each crate type individually since the behavior changes when
        // they are combined.
        let p = project()
            .file(
                "Cargo.toml",
                &format!(
                    r#"
                    [package]
                    name = "foo-bar"
                    version = "0.1.0"
                    edition = "2015"

                    [lib]
                    crate-type = ["{}"]
                    "#,
                    crate_type
                ),
            )
            .file("src/lib.rs", "")
            .build();
        p.cargo("build")
            .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
            .run();
        p.cargo("clean -p foo-bar")
            .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
            .run();
        assert_all_clean(&p.build_dir());
    }
    let p = project()
        .file(
            "Cargo.toml",
            r#"
            [package]
            name = "foo-bar"
            version = "0.1.0"
            edition = "2018"

            [lib]
            crate-type = ["rlib", "dylib", "staticlib"]

            [[example]]
            name = "foo-ex-rlib"
            crate-type = ["rlib"]
            test = true

            [[example]]
            name = "foo-ex-cdylib"
            crate-type = ["cdylib"]
            test = true

            [[example]]
            name = "foo-ex-bin"
            test = true
            "#,
        )
        .file("src/lib.rs", "")
        .file("src/lib/some-main.rs", "fn main() {}")
        .file("src/bin/other-main.rs", "fn main() {}")
        .file("examples/foo-ex-rlib.rs", "")
        .file("examples/foo-ex-cdylib.rs", "")
        .file("examples/foo-ex-bin.rs", "fn main() {}")
        .file("tests/foo-test.rs", "")
        .file("benches/foo-bench.rs", "")
        .file("build.rs", "fn main() {}")
        .build();

    p.cargo("build --all-targets")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .env("CARGO_INCREMENTAL", "1")
        .run();
    p.cargo("test --all-targets")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .env("CARGO_INCREMENTAL", "1")
        .run();
    p.cargo("check --all-targets")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .env("CARGO_INCREMENTAL", "1")
        .run();
    p.cargo("clean -p foo-bar")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .run();
    assert_all_clean(&p.build_dir());

    // Try some targets.
    p.cargo("build --all-targets --target")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .arg(rustc_host())
        .run();
    p.cargo("clean -p foo-bar --target")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .arg(rustc_host())
        .run();
    assert_all_clean(&p.build_dir());
}

#[cargo_test]
fn clean_p_respects_build_target_config() {
    let p = project()
        .file("Cargo.toml", &basic_manifest("foo", "0.1.0"))
        .file("src/lib.rs", "")
        .file(
            ".cargo/config.toml",
            &format!("[build]\ntarget = \"{}\"", rustc_host()),
        )
        .build();

    p.cargo("build").run();
    p.cargo("clean -p foo --dry-run")
        .with_stderr_data(str![[r#"
[SUMMARY] [FILE_NUM] files, [FILE_SIZE]B total
[WARNING] no files deleted due to --dry-run

"#]])
        .run();
    p.cargo("clean -p foo").run();
    assert_all_clean(&p.build_dir().join(rustc_host()));
}

// Ensures that all files for the package have been deleted.
#[track_caller]
fn assert_all_clean(build_dir: &Path) {
    let walker = walkdir::WalkDir::new(build_dir).into_iter();
    for entry in walker.filter_entry(|e| {
        let path = e.path();
        // This is a known limitation, clean can't differentiate between
        // the different build scripts from different packages.
        !(path
            .file_name()
            .unwrap()
            .to_str()
            .unwrap()
            .starts_with("build_script_build")
            && path
                .parent()
                .unwrap()
                .file_name()
                .unwrap()
                .to_str()
                .unwrap()
                == "incremental")
    }) {
        let entry = entry.unwrap();
        let path = entry.path();
        if let ".rustc_info.json"
        | ".cargo-lock"
        | ".cargo-build-lock"
        | ".cargo-artifact-lock"
        | "CACHEDIR.TAG" = path.file_name().unwrap().to_str().unwrap()
        {
            continue;
        }
        if path.is_symlink() || path.is_file() {
            panic!("{:?} was not cleaned", path);
        }
    }
}

#[cargo_test]
fn clean_spec_version() {
    // clean -p foo where foo matches multiple versions
    Package::new("bar", "0.1.0").publish();
    Package::new("bar", "0.2.0").publish();

    let p = project()
        .file(
            "Cargo.toml",
            r#"
            [package]
            name = "foo"
            version = "0.1.0"
            edition = "2015"

            [dependencies]
            bar1 = {version="0.1", package="bar"}
            bar2 = {version="0.2", package="bar"}
            "#,
        )
        .file("src/lib.rs", "")
        .build();

    p.cargo("build")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .run();

    // Check suggestion for bad pkgid.
    p.cargo("clean -p baz")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] package ID specification `baz` did not match any packages

[HELP] a package with a similar name exists: `bar`

"#]])
        .run();

    p.cargo("clean -p bar:0.1.0")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .with_stderr_data(str![[r#"
[WARNING] version qualifier in `-p bar:0.1.0` is ignored, cleaning all versions of `bar` found
[REMOVED] [FILE_NUM] files, [FILE_SIZE]B total

"#]])
        .run();
    let mut walker = walkdir::WalkDir::new(p.build_dir())
        .into_iter()
        .filter_map(|e| e.ok())
        .filter(|e| {
            let n = e.file_name().to_str().unwrap();
            n.starts_with("bar") || n.starts_with("libbar")
        });
    if let Some(e) = walker.next() {
        panic!("{:?} was not cleaned", e.path());
    }
}

#[cargo_test]
fn clean_spec_partial_version() {
    // clean -p foo where foo matches multiple versions
    Package::new("bar", "0.1.0").publish();
    Package::new("bar", "0.2.0").publish();

    let p = project()
        .file(
            "Cargo.toml",
            r#"
            [package]
            name = "foo"
            version = "0.1.0"
            edition = "2015"

            [dependencies]
            bar1 = {version="0.1", package="bar"}
            bar2 = {version="0.2", package="bar"}
            "#,
        )
        .file("src/lib.rs", "")
        .build();

    p.cargo("build")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .run();

    // Check suggestion for bad pkgid.
    p.cargo("clean -p baz")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] package ID specification `baz` did not match any packages

[HELP] a package with a similar name exists: `bar`

"#]])
        .run();

    p.cargo("clean -p bar:0.1")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .with_stderr_data(str![[r#"
[WARNING] version qualifier in `-p bar:0.1` is ignored, cleaning all versions of `bar` found
[REMOVED] [FILE_NUM] files, [FILE_SIZE]B total

"#]])
        .run();
    let mut walker = walkdir::WalkDir::new(p.build_dir())
        .into_iter()
        .filter_map(|e| e.ok())
        .filter(|e| {
            let n = e.file_name().to_str().unwrap();
            n.starts_with("bar") || n.starts_with("libbar")
        });
    if let Some(e) = walker.next() {
        panic!("{:?} was not cleaned", e.path());
    }
}

#[cargo_test]
fn clean_spec_partial_version_ambiguous() {
    // clean -p foo where foo matches multiple versions
    Package::new("bar", "0.1.0").publish();
    Package::new("bar", "0.2.0").publish();

    let p = project()
        .file(
            "Cargo.toml",
            r#"
            [package]
            name = "foo"
            version = "0.1.0"
            edition = "2015"

            [dependencies]
            bar1 = {version="0.1", package="bar"}
            bar2 = {version="0.2", package="bar"}
            "#,
        )
        .file("src/lib.rs", "")
        .build();

    p.cargo("build")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .run();

    // Check suggestion for bad pkgid.
    p.cargo("clean -p baz")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] package ID specification `baz` did not match any packages

[HELP] a package with a similar name exists: `bar`

"#]])
        .run();

    p.cargo("clean -p bar:0")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .with_stderr_data(str![[r#"
[WARNING] version qualifier in `-p bar:0` is ignored, cleaning all versions of `bar` found
[REMOVED] [FILE_NUM] files, [FILE_SIZE]B total

"#]])
        .run();
    let mut walker = walkdir::WalkDir::new(p.build_dir())
        .into_iter()
        .filter_map(|e| e.ok())
        .filter(|e| {
            let n = e.file_name().to_str().unwrap();
            n.starts_with("bar") || n.starts_with("libbar")
        });
    if let Some(e) = walker.next() {
        panic!("{:?} was not cleaned", e.path());
    }
}

#[cargo_test]
fn clean_spec_reserved() {
    // Clean when a target (like a test) has a reserved name. In this case,
    // make sure `clean -p` doesn't delete the reserved directory `build` when
    // there is a test named `build`.
    Package::new("bar", "1.0.0")
        .file("src/lib.rs", "")
        .file("build.rs", "fn main() {}")
        .publish();

    let p = project()
        .file(
            "Cargo.toml",
            r#"
                [package]
                name = "foo"
                version = "0.1.0"
                edition = "2015"

                [dependencies]
                bar = "1.0"

                [lints.cargo]
                default = "allow"
            "#,
        )
        .file("src/lib.rs", "")
        .file("tests/build.rs", "")
        .build();

    p.cargo("build --all-targets")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .run();
    assert!(p.target_debug_dir().join("build").is_dir());
    let build_test = p.glob("target/debug/deps/build-*").next().unwrap().unwrap();
    assert!(build_test.exists());
    // Tests are never "uplifted".
    assert!(p.glob("target/debug/build-*").next().is_none());

    p.cargo("clean -p foo")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .run();
    // Should not delete this.
    assert!(p.target_debug_dir().join("build").is_dir());

    // This should not rebuild bar.
    p.cargo("build -v --all-targets")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .with_stderr_data(str![[r#"
[FRESH] bar v1.0.0
[COMPILING] foo v0.1.0 ([ROOT]/foo)
[RUNNING] `rustc [..]`
[RUNNING] `rustc [..]`
[RUNNING] `rustc [..]`
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run();
}

#[cargo_test]
fn clean_dry_run() {
    // Basic `clean --dry-run` test.
    Package::new("bar", "1.0.0").publish();
    let p = project()
        .file(
            "Cargo.toml",
            r#"
                [package]
                name = "foo"
                version = "0.1.0"
                edition = "2015"

                [dependencies]
                bar = "1.0"
            "#,
        )
        .file("src/lib.rs", "")
        .build();

    // Start with no files.
    p.cargo("clean --dry-run")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .with_stdout_data("")
        .with_stderr_data(str![[r#"
[SUMMARY] 0 files
[WARNING] no files deleted due to --dry-run

"#]])
        .run();
    p.cargo("check")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .run();
    let before = p.build_dir().ls_r();
    p.cargo("clean --dry-run")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .with_stderr_data(str![[r#"
[SUMMARY] [FILE_NUM] files, [FILE_SIZE]B total
[WARNING] no files deleted due to --dry-run

"#]])
        .run();
    // Verify it didn't delete anything.
    let after = p.build_dir().ls_r();
    assert_eq!(before, after);
    let mut expected = itertools::join(before.iter().map(|p| p.to_str().unwrap()), "\n");
    expected.push_str("\n");
    let expected = snapbox::filter::normalize_paths(&expected);
    let expected = assert_e2e().redactions().redact(&expected);
    eprintln!("{expected}");
    // Verify the verbose output.
    p.cargo("clean --dry-run -v")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .with_stdout_data(expected.unordered())
        .with_stderr_data(str![[r#"
[SUMMARY] [FILE_NUM] files, [FILE_SIZE]B total
[WARNING] no files deleted due to --dry-run

"#]])
        .run();
}

#[cargo_test]
fn doc_with_package_selection() {
    // --doc with -p
    let p = project().file("src/lib.rs", "").build();
    p.cargo("clean --doc -p foo")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .with_status(101)
        .with_stderr_data(str![[r#"
[ERROR] --doc cannot be used with -p

"#]])
        .run();
}

#[cargo_test]
fn quiet_does_not_show_summary() {
    // Checks that --quiet works with `cargo clean`, since there was a
    // subtle issue with how the flag is defined as a global flag.
    let p = project()
        .file("Cargo.toml", &basic_manifest("foo", "0.1.0"))
        .file("src/lib.rs", "")
        .build();

    p.cargo("check")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .run();
    p.cargo("clean --quiet --dry-run")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .with_stdout_data("")
        .with_stderr_data("")
        .run();
    // Verify exact same command without -q would actually display something.
    p.cargo("clean --dry-run")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .with_stdout_data("")
        .with_stderr_data(str![[r#"
[SUMMARY] [FILE_NUM] files, [FILE_SIZE]B total
[WARNING] no files deleted due to --dry-run

"#]])
        .run();
}

#[cargo_test]
fn target_dir_is_file() {
    let p = project()
        .file("Cargo.toml", &basic_bin_manifest("foo"))
        .file("src/foo.rs", &main_file(r#""i am foo""#, &[]))
        .file("target", "")
        .build();

    p.cargo("clean")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .with_stderr_data(str![[r#"
[ERROR] cannot clean `[ROOT]/foo/target`: not a directory
  |
  = [NOTE] cleaning has been aborted to prevent accidental deletion of unrelated files

"#]])
        .with_status(101)
        .run();

    assert!(p.root().join("target").exists());
}

#[cargo_test]
fn explicit_target_dir_is_file() {
    let p = project()
        .file("Cargo.toml", &basic_bin_manifest("foo"))
        .file("src/foo.rs", &main_file(r#""i am foo""#, &[]))
        .file("bar", "")
        .build();

    p.cargo("clean --target-dir bar")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .with_stderr_data(str![[r#"
[ERROR] cannot clean `[ROOT]/foo/bar`: not a directory
  |
  = [NOTE] cleaning has been aborted to prevent accidental deletion of unrelated files

"#]])
        .with_status(101)
        .run();

    assert!(p.root().join("bar").exists());
}

#[cargo_test]
fn env_target_dir_is_file() {
    let p = project()
        .file("Cargo.toml", &basic_bin_manifest("foo"))
        .file("src/foo.rs", &main_file(r#""i am foo""#, &[]))
        .file("bar", "")
        .build();

    p.cargo("clean")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .env("CARGO_TARGET_DIR", "bar")
        .with_stderr_data(str![[r#"
[ERROR] cannot clean `[ROOT]/foo/bar`: not a directory
  |
  = [NOTE] cleaning has been aborted to prevent accidental deletion of unrelated files

"#]])
        .with_status(101)
        .run();

    assert!(p.root().join("bar").exists());
}

#[cargo_test]
fn config_target_dir_is_file() {
    let p = project()
        .file("Cargo.toml", &basic_bin_manifest("foo"))
        .file("src/foo.rs", &main_file(r#""i am foo""#, &[]))
        .file("bar", "")
        .file(
            ".cargo/config.toml",
            "[build]
        target-dir = 'bar'",
        )
        .build();

    p.cargo("clean")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .with_stderr_data(str![[r#"
[ERROR] cannot clean `[ROOT]/foo/bar`: not a directory
  |
  = [NOTE] cleaning has been aborted to prevent accidental deletion of unrelated files

"#]])
        .with_status(101)
        .run();

    assert!(p.root().join("bar").exists());
}

#[cargo_test]
fn target_dir_is_symlink_dir() {
    let p = project()
        .file("Cargo.toml", &basic_bin_manifest("foo"))
        .file("src/foo.rs", &main_file(r#""i am foo""#, &[]))
        .symlink_dir("bar-dest", "target")
        .file("bar-dest/.keep", "")
        .build();

    let mut check = p.cargo("clean");
    #[cfg(windows)]
    {
        check.with_stderr_data(str![[r#"
[REMOVED] 1 file

"#]]);
    }
    #[cfg(not(windows))]
    {
        check.with_stderr_data(str![[r#"
[REMOVED] 1 file, [FILE_SIZE]B total

"#]]);
    }
    check
        .with_status(0)
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .run();

    // make sure cargo has not deleted the files of the symlinked target dir
    assert!(p.root().join("bar-dest/.keep").exists());
}

#[cargo_test]
fn target_dir_is_symlink_file() {
    let p = project()
        .file("Cargo.toml", &basic_bin_manifest("foo"))
        .file("src/foo.rs", &main_file(r#""i am foo""#, &[]))
        .symlink("bar-dest", "target")
        .file("bar-dest", "")
        .build();

    let mut check = p.cargo("clean");
    #[cfg(windows)]
    {
        check.with_stderr_data(str![[r#"
[REMOVED] 1 file

"#]]);
    }
    #[cfg(not(windows))]
    {
        check.with_stderr_data(str![[r#"
[REMOVED] 1 file, [FILE_SIZE]B total

"#]]);
    }
    check
        .with_status(0)
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .run();

    // make sure cargo has not deleted the file of the symlinked target dir
    assert!(p.root().join("bar-dest").exists());
}

#[cargo_test]
fn explicit_target_dir_tag_not_present() {
    // invalid target dir explicitly specified via --target-dir cli arg

    let p = project()
        .file("Cargo.toml", &basic_bin_manifest("foo"))
        .file("src/foo.rs", &main_file(r#""i am foo""#, &[]))
        .file("bar/.keep", "")
        .build();

    p.cargo("clean --target-dir bar")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .with_stdout_data("")
        .with_stderr_data(str![[r#"
[ERROR] cannot clean `[ROOT]/foo/bar`: missing or invalid `CACHEDIR.TAG` file
  |
  = [NOTE] cleaning has been aborted to prevent accidental deletion of unrelated files

"#]])
        .with_status(101)
        .run();
}

#[cargo_test]
fn explicit_target_dir_tag_invalid_signature() {
    let p = project()
        .file("Cargo.toml", &basic_bin_manifest("foo"))
        .file("src/foo.rs", &main_file(r#""i am foo""#, &[]))
        .file("bar/CACHEDIR.TAG", "Signature: 1234")
        .build();

    p.cargo("clean --target-dir bar")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .with_stdout_data("")
        .with_stderr_data(str![[r#"
[ERROR] cannot clean `[ROOT]/foo/bar`: invalid signature in `CACHEDIR.TAG` file
  |
  = [NOTE] cleaning has been aborted to prevent accidental deletion of unrelated files

"#]])
        .with_status(101)
        .run();
}

#[cargo_test]
fn explicit_target_dir_tag_symlink() {
    let p = project()
        .file("Cargo.toml", &basic_bin_manifest("foo"))
        .file("src/foo.rs", &main_file(r#""i am foo""#, &[]))
        .file(
            "src/CACHEDIR.TAG",
            "Signature: 8a477f597d28d172789f06886806bc55",
        )
        .symlink("src/CACHEDIR.TAG", "bar/CACHEDIR.TAG")
        .build();

    p.cargo("clean --target-dir bar")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .with_stdout_data("")
        .with_stderr_data(str![[r#"
[ERROR] cannot clean `[ROOT]/foo/bar`: expect `CACHEDIR.TAG` to be a regular file, got a symlink
  |
  = [NOTE] cleaning has been aborted to prevent accidental deletion of unrelated files

"#]])
        .with_status(101)
        .run();
}

#[cargo_test]
fn explicit_target_dir_tag_valid() {
    let p = project()
        .file("Cargo.toml", &basic_bin_manifest("foo"))
        .file("src/foo.rs", &main_file(r#""i am foo""#, &[]))
        .file(
            "bar/CACHEDIR.TAG",
            "Signature: 8a477f597d28d172789f06886806bc55",
        )
        .build();

    p.cargo("clean --target-dir bar").run();
}

#[cargo_test]
fn env_target_dir_tag_not_present() {
    // invalid target dir specified via env var

    let p = project()
        .file("Cargo.toml", &basic_bin_manifest("foo"))
        .file("bar/.keep", "")
        .file("src/foo.rs", &main_file(r#""i am foo""#, &[]))
        .build();

    p.cargo("clean")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .env("CARGO_TARGET_DIR", "bar")
        .with_stderr_data(str![[r#"
[REMOVED] [FILE_NUM] files, [FILE_SIZE]B total

"#]])
        .run();
}

#[cargo_test]
fn env_target_dir_tag_invalid_signature() {
    let p = project()
        .file("Cargo.toml", &basic_bin_manifest("foo"))
        .file("src/foo.rs", &main_file(r#""i am foo""#, &[]))
        .file("bar/CACHEDIR.TAG", "Signature: 1234")
        .build();

    p.cargo("clean")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .env("CARGO_TARGET_DIR", "bar")
        .with_stderr_data(str![[r#"
[REMOVED] [FILE_NUM] files, [FILE_SIZE]B total

"#]])
        .run();
}

#[cargo_test]
fn env_target_dir_tag_symlink() {
    let p = project()
        .file("Cargo.toml", &basic_bin_manifest("foo"))
        .file("src/foo.rs", &main_file(r#""i am foo""#, &[]))
        .file(
            "src/CACHEDIR.TAG",
            "Signature: 8a477f597d28d172789f06886806bc55",
        )
        .symlink("src/CACHEDIR.TAG", "bar/CACHEDIR.TAG")
        .build();

    p.cargo("clean")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .env("CARGO_TARGET_DIR", "bar")
        .with_stderr_data(str![[r#"
[REMOVED] [FILE_NUM] files, [FILE_SIZE]B total

"#]])
        .run();
}

#[cargo_test]
fn env_target_dir_tag_valid() {
    let p = project()
        .file("Cargo.toml", &basic_bin_manifest("foo"))
        .file("src/foo.rs", &main_file(r#""i am foo""#, &[]))
        .file(
            "bar/CACHEDIR.TAG",
            "Signature: 8a477f597d28d172789f06886806bc55",
        )
        .build();

    p.cargo("clean").env("CARGO_TARGET_DIR", "bar").run();
}

#[cargo_test]
fn config_target_dir_tag_not_present() {
    // invalid target dir specified via build config

    let p = project()
        .file("Cargo.toml", &basic_bin_manifest("foo"))
        .file("bar/.keep", "")
        .file("src/foo.rs", "")
        .file(
            ".cargo/config.toml",
            "[build]
        target-dir = 'bar'",
        )
        .build();

    p.cargo("clean")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .with_stderr_data(str![[r#"
[REMOVED] [FILE_NUM] files, [FILE_SIZE]B total

"#]])
        .run();
}

#[cargo_test]
fn config_target_dir_tag_invalid_signature() {
    let p = project()
        .file("Cargo.toml", &basic_bin_manifest("foo"))
        .file("src/foo.rs", &main_file(r#""i am foo""#, &[]))
        .file("bar/CACHEDIR.TAG", "Signature: 1234")
        .file(
            ".cargo/config.toml",
            "[build]
        target-dir = 'bar'",
        )
        .build();

    p.cargo("clean")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .with_stderr_data(str![[r#"
[REMOVED] [FILE_NUM] files, [FILE_SIZE]B total

"#]])
        .run();
}

#[cargo_test]
fn config_target_dir_tag_symlink() {
    let p = project()
        .file("Cargo.toml", &basic_bin_manifest("foo"))
        .file("src/foo.rs", &main_file(r#""i am foo""#, &[]))
        .file(
            "src/CACHEDIR.TAG",
            "Signature: 8a477f597d28d172789f06886806bc55",
        )
        .symlink("src/CACHEDIR.TAG", "bar/CACHEDIR.TAG")
        .file(
            ".cargo/config.toml",
            "[build]
        target-dir = 'bar'",
        )
        .build();

    p.cargo("clean")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .with_stderr_data(str![[r#"
[REMOVED] [FILE_NUM] files, [FILE_SIZE]B total

"#]])
        .run();
}

#[cargo_test]
fn config_target_dir_tag_valid() {
    let p = project()
        .file("Cargo.toml", &basic_bin_manifest("foo"))
        .file("src/foo.rs", &main_file(r#""i am foo""#, &[]))
        .file(
            "bar/CACHEDIR.TAG",
            "Signature: 8a477f597d28d172789f06886806bc55",
        )
        .file(
            ".cargo/config.toml",
            "[build]
        target-dir = 'bar'",
        )
        .build();

    p.cargo("clean")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .run();
}

#[cargo_test]
fn explicit_target_dir_not_exists() {
    let p = project()
        .file("Cargo.toml", &basic_bin_manifest("foo"))
        .file("src/foo.rs", &main_file(r#""i am foo""#, &[]))
        .build();

    // should not error if target_dir does not exist
    p.cargo("clean --target-dir bar")
        .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
        .with_stderr_data(str![[r#"
[REMOVED] 0 files

"#]])
        .run();
}

// Trust: managed cache cleanup follows the compiler's basename plus Cargo's
// exact package binding; an opaque filename alone grants no ownership.
#[cargo_test]
fn package_witness_cleanup_respects_ownership_and_modes() {
    use std::collections::BTreeMap;
    use std::fs;

    for legacy in [true, false] {
        let p = project()
            .at(if legacy { "witness-clean-legacy" } else { "witness-clean-current" })
            .file("Cargo.toml", "[package]\nname='witness-owner'\nversion='1.0.0'\nedition='2021'\n[dependencies]\nwitness-other={path='other'}\n[workspace]\n[profile.dev]\nincremental=false\n")
            .file("src/lib.rs", "pub fn value(x: u32) -> u32 { witness_other::value(x) }")
            .file("other/Cargo.toml", "[package]\nname='witness-other'\nversion='1.0.0'\nedition='2021'\n")
            .file("other/src/lib.rs", "pub fn value(x: u32) -> u32 { x }")
            .build();
        let run = |args: &str| {
            let mut cmd = p.cargo(args);
            cmd.env(
                "__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT",
                if legacy { "1" } else { "0" },
            );
            cmd.run();
        };
        let stores = || {
            walkdir::WalkDir::new(p.build_dir())
                .into_iter()
                .map(Result::unwrap)
                .filter(|e| e.path().extension().is_some_and(|ext| ext == "twit"))
                .map(|e| (e.path().to_owned(), fs::read(e.path()).unwrap()))
                .collect::<BTreeMap<_, _>>()
        };
        // Read independent compiler/Targo declarations, not the cleanup parser.
        let owned = |profile: &str, target: Option<&str>, package: &str| {
            let base = target
                .map_or_else(|| p.build_dir(), |t| p.build_dir().join(t))
                .join(profile);
            let mut outputs = BTreeMap::new();
            for entry in walkdir::WalkDir::new(base).into_iter().map(Result::unwrap) {
                if !entry.path().extension().is_some_and(|ext| ext == "d") {
                    continue;
                }
                let contents = fs::read_to_string(entry.path()).unwrap();
                let compiler = contents
                    .lines()
                    .filter_map(|l| l.strip_prefix("# trust-witness-output-v1:"))
                    .collect::<Vec<_>>();
                let cargo = contents
                    .lines()
                    .filter_map(|l| l.strip_prefix("# targo-witness-owner-v1:"))
                    .map(|s| serde_json::from_str::<serde_json::Value>(s).unwrap())
                    .collect::<Vec<_>>();
                if cargo.iter().any(|v| {
                    v["package"]
                        .as_str()
                        .unwrap()
                        .starts_with(&format!("{package} "))
                }) {
                    assert_eq!(
                        compiler.len(),
                        1,
                        "missing compiler-owned cache identity: {}",
                        entry.path().display()
                    );
                    assert_eq!(cargo.len(), 1);
                    assert_eq!(cargo[0]["store"], compiler[0]);
                    assert_eq!(compiler[0].len(), 21);
                    assert!(compiler[0].ends_with(".twit"));
                    assert!(
                        compiler[0][..16]
                            .bytes()
                            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
                    );
                    let path = entry.path().parent().unwrap().join(compiler[0]);
                    if path.exists() {
                        outputs.insert(path.clone(), fs::read(path).unwrap());
                    }
                }
            }
            outputs
        };
        run("build");
        let debug_owner = owned("debug", None, "witness-owner");
        let debug_other = owned("debug", None, "witness-other");
        assert_eq!(
            debug_owner.len(),
            1,
            "the real compiler must declare the selected package's actual store"
        );
        assert_eq!(debug_other.len(), 1);
        assert_eq!(stores().len(), 2);
        let initial = stores();
        run("clean --dry-run -p witness-owner");
        assert_eq!(stores(), initial, "dry-run changed witness bytes or paths");
        run("build --release");
        let release_owner = owned("release", None, "witness-owner");
        let release_other = owned("release", None, "witness-other");
        assert_eq!(release_owner.len(), 1);
        assert_eq!(release_other.len(), 1);
        run(&format!("build --target {}", rustc_host()));
        let target_owner = owned("debug", Some(rustc_host()), "witness-owner");
        let target_other = owned("debug", Some(rustc_host()), "witness-other");
        assert_eq!(target_owner.len(), 1);
        assert_eq!(target_other.len(), 1);
        run("clean -p witness-owner --release");
        let after_release = stores();
        for (path, bytes) in debug_owner
            .iter()
            .chain(debug_other.iter())
            .chain(release_other.iter())
            .chain(target_owner.iter())
            .chain(target_other.iter())
        {
            assert_eq!(
                after_release.get(path),
                Some(bytes),
                "clean --release changed another store"
            );
        }
        assert!(release_owner.keys().all(|p| !p.exists()));
        run(&format!("clean -p witness-owner --target {}", rustc_host()));
        assert!(target_owner.keys().all(|p| !p.exists()));
        run("clean -p witness-owner");
        assert!(debug_owner.keys().all(|p| !p.exists()));
        let survivors = stores();
        assert_eq!(survivors.len(), 3);
        for (path, bytes) in debug_other
            .iter()
            .chain(release_other.iter())
            .chain(target_other.iter())
        {
            assert_eq!(
                survivors.get(path),
                Some(bytes),
                "another package's store was removed or rewritten"
            );
        }
        run("build");
        assert_eq!(
            owned("debug", None, "witness-owner"),
            debug_owner,
            "rebuild did not recreate the same managed store"
        );

        // Incremental compilation must not erase ownership of an earlier
        // managed cache when it replaces this unit's dep-info.
        let mut cmd = p.cargo("build");
        cmd.env(
            "__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT",
            if legacy { "1" } else { "0" },
        );
        cmd.env("CARGO_INCREMENTAL", "1").run();
        run("clean -p witness-owner");
        assert!(debug_owner.keys().all(|p| !p.exists()));
        run("build");

        // A failed type-check also rewrites dep-info after an earlier managed
        // cache was minted. Partial outputs still belong to the selected crate.
        let before_failed_rebuild = owned("debug", None, "witness-owner");
        assert_eq!(before_failed_rebuild.len(), 1);
        fs::write(
            p.root().join("src/lib.rs"),
            "pub fn value(x: u32) -> MissingType { x }",
        )
        .unwrap();
        p.cargo("build")
            .env(
                "__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT",
                if legacy { "1" } else { "0" },
            )
            .with_status(101)
            .with_stderr_contains("[..]cannot find type `MissingType`[..]")
            .run();
        assert!(
            before_failed_rebuild.keys().all(|p| p.exists()),
            "failed compilation removed the earlier cache unexpectedly"
        );
        if legacy {
            let dep_info = p
                .glob("target/debug/deps/witness_owner-*.d")
                .next()
                .unwrap()
                .unwrap();
            let text = fs::read_to_string(dep_info).unwrap();
            let declarations = text
                .lines()
                .filter(|l| l.starts_with("# trust-witness-output-v1:"))
                .count();
            let bindings = text
                .lines()
                .filter(|l| l.starts_with("# targo-witness-owner-v1:"))
                .count();
            assert_eq!(
                declarations, 1,
                "the real failed compiler invocation must declare its potential cache"
            );
            assert_eq!(
                bindings, 1,
                "failed compilation lost its package cleanup binding"
            );
        }
        run("clean -p witness-owner");
        assert!(
            before_failed_rebuild.keys().all(|p| !p.exists()),
            "package clean left its cache after a failed rebuild"
        );
        fs::write(
            p.root().join("src/lib.rs"),
            "pub fn value(x: u32) -> u32 { witness_other::value(x) }",
        )
        .unwrap();
        run("build");

        // An outside file with the same opaque basename is never adopted by
        // package clean. Actual explicit mint/replay modes are compiler-owner
        // run-make controls, not authority granted to an embedded test frontend.
        let explicit = p.root().join("caller-witness-store");
        fs::create_dir(&explicit).unwrap();
        for (path, bytes) in &debug_owner {
            fs::write(explicit.join(path.file_name().unwrap()), bytes).unwrap();
        }
        let external = fs::read_dir(&explicit)
            .unwrap()
            .map(|e| {
                let p = e.unwrap().path();
                (p.clone(), fs::read(p).unwrap())
            })
            .collect::<BTreeMap<_, _>>();
        assert!(!external.is_empty());
        run("clean -p witness-owner");
        for (path, bytes) in external {
            assert_eq!(fs::read(path).unwrap(), bytes);
        }
        for (path, bytes) in debug_other
            .iter()
            .chain(release_other.iter())
            .chain(target_other.iter())
        {
            assert_eq!(fs::read(path).unwrap(), *bytes);
        }
        if legacy {
            run("build");
            let dep_info = p
                .glob("target/debug/deps/witness_owner-*.d")
                .next()
                .unwrap()
                .unwrap();
            let original = fs::read_to_string(&dep_info).unwrap();
            let before_refusal = stores();
            fs::write(
                &dep_info,
                format!("{original}# trust-witness-output-v1:../outside.twit\n"),
            )
            .unwrap();
            p.cargo("clean -p witness-owner")
                .env("__CARGO_TEMPORARY_BUILD_DIR_NEW_LAYOUT_OPT_OUT", "1")
                .with_status(101)
                .with_stderr_contains("[..]invalid managed witness ownership[..]")
                .run();
            assert_eq!(
                stores(),
                before_refusal,
                "malformed ownership deleted a cache"
            );
            assert!(
                p.target_debug_dir().join("libwitness_owner.rlib").is_file(),
                "ownership refusal deleted an ordinary artifact"
            );
            fs::write(&dep_info, original).unwrap();

            // Another package can have the same crate-name-shaped dep-info.
            // The exact package binding, not that filename, decides ownership.
            let other_dep = p
                .glob("target/debug/deps/witness_other-*.d")
                .next()
                .unwrap()
                .unwrap();
            fs::copy(
                other_dep,
                p.target_debug_dir()
                    .join("deps/witness_owner-0000000000000000.d"),
            )
            .unwrap();
            run("clean -p witness-owner");
            for (path, bytes) in &debug_other {
                assert_eq!(
                    fs::read(path).unwrap(),
                    *bytes,
                    "foreign package binding was adopted"
                );
            }
        }
    }
}
