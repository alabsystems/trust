//! Explicit real-tool diagnostic: native Session naming must preserve both
//! source identity and actual Cargo freshness across committed source trees.

use super::*;

#[test]
#[ignore = "requires explicit genuine Targo/Trust paths and build-slot admission"]
fn committed_private_builds_reuse_unchanged_units_and_rebuild_changed_source() {
    let tool = |name: &str| {
        let path =
            PathBuf::from(std::env::var_os(name).expect("explicit genuine tool path required"));
        assert!(path.is_absolute() && path.is_file(), "{name}: {}", path.display());
        path
    };
    let targo = tool("TRUST_BOOTSTRAP_CACHE_WITNESS_TARGO");
    let rustc = tool("TRUST_BOOTSTRAP_CACHE_WITNESS_RUSTC");
    let version = Command::new(&targo).args(["--unverified", "--version"]).output().unwrap();
    assert!(version.status.success(), "the witness requires genuine Targo");
    let scratch = TempDir::new().unwrap();

    git_test(|ctx| {
        ctx.write(".gitignore", "/Cargo.lock");
        ctx.write("Cargo.toml", "[workspace]\nmembers = [\"engine\", \"app\"]\nresolver = \"2\"");
        ctx.write(
            "engine/Cargo.toml",
            "[package]\nname = \"engine\"\nversion = \"0.1.0\"\nedition = \"2021\"",
        );
        ctx.write(
            "engine/src/lib.rs",
            "include!(concat!(env!(\"CARGO_MANIFEST_DIR\"), \"/src/observed.rs\"));",
        );
        ctx.write(
            "engine/src/observed.rs",
            "pub fn value() -> u32 { 41 }\npub fn location() -> &'static str { file!() }",
        );
        ctx.write("app/Cargo.toml", "[package]\nname = \"app\"\nversion = \"0.1.0\"\nedition = \"2021\"\n[dependencies]\nengine = { path = \"../engine\" }");
        ctx.write("app/build.rs", "fn main() {\nprintln!(\"cargo:rerun-if-env-changed=CFG_COMMIT_HASH\");\nprintln!(\"cargo:rustc-env=BUILD_COMMIT={}\", std::env::var(\"CFG_COMMIT_HASH\").unwrap());\n}");
        ctx.write("app/src/main.rs", "fn main() { println!(\"{}|{}|{}\", env!(\"BUILD_COMMIT\"), engine::value(), engine::location()); }");
        ctx.commit();

        let run = |subcommand: &str, extra: &[&str]| {
            let info = head(ctx);
            let mut config = commit_named_config("build", 1);
            config.rust_info = GitInfo::Present(Some(info.clone()));
            let session = Session::new(config);
            assert_eq!(session.rust_sha(), Some(info.sha.as_str()));
            let remap = session.debuginfo_map_to(RemapScheme::NonCompiler).unwrap();
            assert_eq!(remap, "/rustc/trust-dev");
            let mut command = Command::new(&targo);
            if subcommand == "build" {
                command.arg("--unverified");
            }
            let output = command
                .arg(subcommand)
                .args(extra)
                .current_dir(ctx.get_path())
                .env("CARGO_TARGET_DIR", scratch.path().join("target"))
                .env("CARGO_BUILD_BUILD_DIR", scratch.path().join("build"))
                .env("CARGO_HOME", scratch.path().join("cargo-home"))
                .env("RUSTC", &rustc)
                .env("CFG_COMMIT_HASH", session.rust_sha().unwrap())
                .env("__CARGO_RUSTC_BOOTSTRAP_WS_REMAP", remap)
                .env_remove("RUSTFLAGS")
                .env_remove("CARGO_ENCODED_RUSTFLAGS")
                .env_remove("RUSTC_WRAPPER")
                .env_remove("RUSTC_WORKSPACE_WRAPPER")
                .output()
                .unwrap();
            assert!(
                output.status.success(),
                "{subcommand}:\n{}",
                String::from_utf8_lossy(&output.stderr)
            );
            output
        };
        run("generate-lockfile", &["--offline"]);
        let build = |expected_value: u32| {
            let output = run(
                "build",
                &["--frozen", "--message-format=json", "--config", "profile.dev.trim-paths='all'"],
            );
            let fresh: BTreeMap<String, bool> = String::from_utf8(output.stdout)
                .unwrap()
                .lines()
                .map(|line| serde_json::from_str::<serde_json::Value>(line).unwrap())
                .filter(|message| message["reason"] == "compiler-artifact")
                .filter_map(|message| {
                    let name = message["target"]["name"].as_str()?;
                    matches!(name, "engine" | "app")
                        .then(|| (name.to_owned(), message["fresh"].as_bool().unwrap()))
                })
                .collect();
            let binary = scratch
                .path()
                .join("target/debug")
                .join(format!("app{}", std::env::consts::EXE_SUFFIX));
            let output = Command::new(binary).output().unwrap();
            assert!(output.status.success());
            let expected = format!(
                "{}|{expected_value}|/rustc/trust-dev/engine/src/observed.rs",
                ctx.get_current_commit()
            );
            assert_eq!(
                String::from_utf8(output.stdout).unwrap().trim().replace('\\', "/"),
                expected
            );
            eprintln!("private-remap witness: {expected}; artifacts={fresh:?}");
            fresh
        };
        let first = build(41);
        assert_eq!(first.get("engine"), Some(&false));
        assert_eq!(first.get("app"), Some(&false));
        let initial = ctx.get_current_commit();

        ctx.write("docs/change.md", "documentation changes only");
        ctx.commit();
        assert_ne!(ctx.get_current_commit(), initial);
        let relabelled = build(41);
        assert_eq!(relabelled.get("engine"), Some(&true), "unchanged engine must be reused");
        assert_eq!(relabelled.get("app"), Some(&false), "the executable must carry current HEAD");

        fs::write(
            ctx.get_path().join("engine/src/observed.rs"),
            "pub fn value() -> u32 { 42 }\npub fn location() -> &'static str { file!() }\n",
        )
        .unwrap();
        ctx.commit();
        let changed = build(42);
        assert_eq!(
            changed.get("engine"),
            Some(&false),
            "source changes must invalidate the engine"
        );
        assert_eq!(changed.get("app"), Some(&false));
    });
}
