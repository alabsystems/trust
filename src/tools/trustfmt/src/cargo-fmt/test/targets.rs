use super::*;

struct ExpTarget {
    path: &'static str,
    edition: Edition,
    kind: &'static str,
}

mod all_targets {
    use super::*;

    fn assert_correct_targets_loaded(
        manifest_suffix: &str,
        source_root: &str,
        exp_targets: &[ExpTarget],
        exp_num_targets: usize,
    ) {
        let root_path = Path::new("tests/cargo-fmt/source").join(source_root);
        let get_path = |exp: &str| PathBuf::from(&root_path).join(exp).canonicalize().unwrap();
        let manifest_path = Path::new(&root_path).join(manifest_suffix);
        let targets = get_targets(&CargoFmtStrategy::All, Some(manifest_path.as_path()))
            .expect("Targets should have been loaded");

        assert_eq!(targets.len(), exp_num_targets);

        for target in exp_targets {
            assert!(targets.contains(&Target {
                path: get_path(target.path),
                edition: target.edition,
                kind: target.kind.to_owned(),
            }));
        }
    }

    mod different_crate_and_dir_names {
        use super::*;

        fn assert_correct_targets_loaded(manifest_suffix: &str) {
            let exp_targets = vec![
                ExpTarget {
                    path: "dependency-dir-name/subdep-dir-name/src/lib.rs",
                    edition: Edition::E2018,
                    kind: "lib",
                },
                ExpTarget {
                    path: "dependency-dir-name/src/lib.rs",
                    edition: Edition::E2018,
                    kind: "lib",
                },
                ExpTarget {
                    path: "src/main.rs",
                    edition: Edition::E2018,
                    kind: "main",
                },
            ];
            super::assert_correct_targets_loaded(
                manifest_suffix,
                "divergent-crate-dir-names",
                &exp_targets,
                3,
            );
        }

        #[test]
        fn correct_targets_from_root() {
            assert_correct_targets_loaded("Cargo.toml");
        }

        #[test]
        fn correct_targets_from_sub_local_dep() {
            assert_correct_targets_loaded("dependency-dir-name/Cargo.toml");
        }
    }

    mod workspaces {
        use super::*;

        fn assert_correct_targets_loaded(manifest_suffix: &str) {
            let exp_targets = vec![
                ExpTarget {
                    path: "ws/a/src/main.rs",
                    edition: Edition::E2018,
                    kind: "bin",
                },
                ExpTarget {
                    path: "ws/b/src/main.rs",
                    edition: Edition::E2018,
                    kind: "bin",
                },
                ExpTarget {
                    path: "ws/c/src/lib.rs",
                    edition: Edition::E2018,
                    kind: "lib",
                },
                ExpTarget {
                    path: "ws/a/d/src/lib.rs",
                    edition: Edition::E2018,
                    kind: "lib",
                },
                ExpTarget {
                    path: "e/src/main.rs",
                    edition: Edition::E2018,
                    kind: "main",
                },
                ExpTarget {
                    path: "ws/a/d/f/src/lib.rs",
                    edition: Edition::E2018,
                    kind: "lib",
                },
            ];
            super::assert_correct_targets_loaded(
                manifest_suffix,
                "workspaces/path-dep-above",
                &exp_targets,
                6,
            );
        }

        #[test]
        fn includes_outside_workspace_deps() {
            assert_correct_targets_loaded("ws/Cargo.toml");
        }

        #[test]
        fn includes_workspace_from_dep_above() {
            assert_correct_targets_loaded("e/Cargo.toml");
        }

        #[test]
        fn includes_all_packages_from_workspace_subdir() {
            assert_correct_targets_loaded("ws/a/d/f/Cargo.toml");
        }
    }

    #[cfg(unix)]
    #[test]
    fn canonicalizes_workspace_self_aliases_before_recursing() {
        use std::os::unix::fs::symlink;

        let temp = tempfile::tempdir().unwrap();
        let consumer = temp.path().join("consumer");
        let sibling = temp.path().join("sibling");
        let trust = temp.path().join("trust");
        let crates = trust.join("crates");
        let member_a = crates.join("member-a");
        let member_b = crates.join("member-b");
        let root_only = crates.join("root-only");

        for package in [&consumer, &sibling, &member_a, &member_b, &root_only] {
            fs::create_dir_all(package.join("src")).unwrap();
            fs::write(package.join("src/lib.rs"), "pub fn marker() {}\n").unwrap();
        }
        fs::create_dir_all(trust.join("first-party")).unwrap();
        symlink("..", trust.join("first-party/trust")).unwrap();

        fs::write(
            consumer.join("Cargo.toml"),
            r#"[package]
name = "consumer"
version = "0.0.0"
edition = "2021"

[dependencies]
member-a = { path = "../trust/crates/member-a" }
"#,
        )
        .unwrap();
        fs::write(
            trust.join("Cargo.toml"),
            r#"[workspace]
resolver = "2"
members = ["crates/member-a", "crates/member-b", "crates/root-only"]
"#,
        )
        .unwrap();
        fs::write(
            crates.join("Cargo.toml"),
            r#"[workspace]
resolver = "2"
members = ["member-a", "member-b"]
exclude = ["root-only"]
"#,
        )
        .unwrap();
        fs::write(
            member_a.join("Cargo.toml"),
            r#"[package]
name = "member-a"
version = "0.0.0"
edition = "2021"

[dependencies]
root-only = { path = "../root-only" }
sibling = { path = "../../../sibling" }
"#,
        )
        .unwrap();
        fs::write(
            sibling.join("Cargo.toml"),
            r#"[package]
name = "sibling"
version = "0.0.0"
edition = "2021"

[dependencies]
member-b = { path = "../trust/first-party/trust/crates/member-b" }
"#,
        )
        .unwrap();
        fs::write(
            root_only.join("Cargo.toml"),
            r#"[package]
name = "root-only"
version = "0.0.0"
edition = "2021"
"#,
        )
        .unwrap();
        fs::write(
            member_b.join("Cargo.toml"),
            r#"[package]
name = "member-b"
version = "0.0.0"
edition = "2021"
"#,
        )
        .unwrap();

        let targets = get_targets(
            &CargoFmtStrategy::All,
            Some(consumer.join("Cargo.toml").as_path()),
        )
        .expect("canonical self-aliases should not be loaded as second workspaces");

        assert_eq!(targets.len(), 5);
        for source in [
            consumer.join("src/lib.rs"),
            sibling.join("src/lib.rs"),
            member_a.join("src/lib.rs"),
            member_b.join("src/lib.rs"),
            root_only.join("src/lib.rs"),
        ] {
            let source = source.canonicalize().unwrap();
            assert!(targets.iter().any(|target| target.path == source));
        }
    }
}
