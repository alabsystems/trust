// Trust: metadata search paths must also reach direct build-script compilers.
use std::collections::BTreeMap;

use super::*;
use crate::core::session::Session;
use crate::utils::tests::TestCtx;

fn cargo_environment(sysroots: &[RmetaSysroot]) -> BTreeMap<String, String> {
    cargo_environment_with_tool_sysroot(sysroots, None)
}

fn cargo_environment_with_tool_sysroot(
    sysroots: &[RmetaSysroot],
    tool_sysroot: Option<&Path>,
) -> BTreeMap<String, String> {
    let context = TestCtx::new();
    let build = Session::new(context.config("check").stage(1).create_config());
    let builder = Builder::new(&build);
    let target = builder.config.host_target;
    let mut cargo = Cargo::new(
        &builder,
        Compiler::new(0, target),
        Mode::ToolRustcPrivate,
        SourceType::InTree,
        target,
        Kind::Check,
    );
    cargo.env("RUSTC_ADDITIONAL_SYSROOT_PATHS", "existing-shim-path");
    cargo.rustflag("--cfg=existing_flag");
    for sysroot in sysroots {
        sysroot.configure_cargo(&mut cargo);
    }
    if let Some(sysroot) = tool_sysroot {
        configure_tool_check_sysroot(&mut cargo, sysroot);
    }
    let mut command = cargo.into_cmd();
    command.mark_as_executed(); // Inspect the command without running Cargo.
    command
        .get_envs()
        .filter_map(|(key, value)| {
            value
                .map(|value| (key.to_str().unwrap().to_owned(), value.to_str().unwrap().to_owned()))
        })
        .collect()
}

fn tracked_flags(environment: &BTreeMap<String, String>) -> Vec<&str> {
    if let Some(encoded) = environment.get("CARGO_ENCODED_RUSTFLAGS") {
        encoded.split('\x1f').collect()
    } else {
        environment["RUSTFLAGS"].split_whitespace().collect()
    }
}

#[test]
fn rmeta_sysroot_tracks_both_direct_probe_paths_and_preserves_shim_paths() {
    let roots = [
        RmetaSysroot { host_dir: "rustc/host".into(), target_dir: "rustc/target".into() },
        RmetaSysroot { host_dir: "std/host".into(), target_dir: "std/target".into() },
    ];
    let environment = cargo_environment(&roots);
    assert_eq!(
        environment["RUSTC_ADDITIONAL_SYSROOT_PATHS"],
        "existing-shim-path,rustc/host,rustc/target,std/host,std/target"
    );
    let flags = tracked_flags(&environment);
    assert!(flags.contains(&"--cfg=existing_flag"));
    assert_eq!(
        flags.iter().copied().filter(|flag| flag.starts_with("-Lall=")).collect::<Vec<_>>(),
        ["-Lall=rustc/host", "-Lall=rustc/target", "-Lall=std/host", "-Lall=std/target"]
    );
}

#[test]
fn rmeta_sysroot_preserves_spaces_in_each_direct_probe_argument() {
    let environment = cargo_environment(&[RmetaSysroot {
        host_dir: "check output/host metadata".into(),
        target_dir: "check output/target metadata".into(),
    }]);
    assert!(environment.contains_key("CARGO_ENCODED_RUSTFLAGS"));
    let flags = tracked_flags(&environment);
    assert!(flags.contains(&"-Lall=check output/host metadata"));
    assert!(flags.contains(&"-Lall=check output/target metadata"));
}

#[test]
fn rmeta_sysroot_changes_either_path_in_cargo_tracked_inputs() {
    let original = RmetaSysroot { host_dir: "host-one".into(), target_dir: "target-one".into() };
    let baseline = cargo_environment(std::slice::from_ref(&original));
    for changed in [
        RmetaSysroot { host_dir: "host-two".into(), ..original.clone() },
        RmetaSysroot { target_dir: "target-two".into(), ..original.clone() },
    ] {
        let environment = cargo_environment(&[changed]);
        assert_ne!(tracked_flags(&baseline), tracked_flags(&environment));
    }
}

// Trust: exercise the real filtered copier after an earlier full build populated
// rustc-private artifacts, including stale destination state and std-side shims.
#[test]
fn tool_check_sysroot_isolates_full_artifacts_and_preserves_std() {
    let context = TestCtx::new();
    let session = Session::new(
        context.config("check").path("compiler/rustc").stage(1).no_dry_run().create_config(),
    );
    let source = context.dir().join("full compiler sysroot");
    let destination = context.dir().join("check sysroot");
    let relative = Path::new("lib/rustlib/test-host/lib");
    fs::create_dir_all(source.join(relative)).unwrap();
    fs::create_dir_all(source.join("lib/rustlib/src")).unwrap();
    fs::write(source.join("lib/rustlib/src/source-marker"), b"never copied").unwrap();
    fs::write(source.join(relative).join("libstd-current.rlib"), b"std bytes").unwrap();
    fs::write(
        source.join(relative).join("librustc_std_workspace_core-current.rlib"),
        b"shim bytes",
    )
    .unwrap();
    fs::write(source.join(relative).join("librustc_ast-full.rmeta"), b"full metadata").unwrap();
    fs::write(source.join("lib/rustc_driver-full.dll"), b"windows private runtime").unwrap();
    fs::create_dir_all(destination.join(relative)).unwrap();
    fs::write(destination.join(relative).join("librustc_ast-stale.rmeta"), b"stale metadata")
        .unwrap();
    copy_tool_check_sysroot(&session, &source, &destination);
    assert_eq!(
        fs::read(destination.join(relative).join("libstd-current.rlib")).unwrap(),
        b"std bytes"
    );
    assert_eq!(
        fs::read(destination.join(relative).join("librustc_std_workspace_core-current.rlib"))
            .unwrap(),
        b"shim bytes"
    );
    assert!(!destination.join(relative).join("librustc_ast-full.rmeta").exists());
    assert!(!destination.join(relative).join("librustc_ast-stale.rmeta").exists());
    assert!(!destination.join("lib/rustc_driver-full.dll").exists());
    assert!(!destination.join("lib/rustlib/src").exists());
    assert_eq!(
        fs::read(source.join(relative).join("librustc_ast-full.rmeta")).unwrap(),
        b"full metadata"
    );
    assert_eq!(fs::read(source.join("lib/rustlib/src/source-marker")).unwrap(), b"never copied");
}

// Trust: source aliases must not introduce a second source authority or copier writes.
#[cfg(unix)]
#[test]
fn tool_check_sysroot_does_not_follow_source_aliases() {
    let context = TestCtx::new();
    let session = Session::new(
        context.config("check").path("compiler/rustc").stage(1).no_dry_run().create_config(),
    );
    let source = context.dir().join("source");
    let destination = context.dir().join("isolated");
    let outside = context.dir().join("compiler-source");
    fs::create_dir_all(source.join("lib/rustlib")).unwrap();
    fs::create_dir_all(&outside).unwrap();
    fs::write(outside.join("marker"), b"original source").unwrap();
    std::os::unix::fs::symlink(&outside, source.join("lib/rustlib/src")).unwrap();
    std::os::unix::fs::symlink(&outside, source.join("lib/rustlib/rustc-src")).unwrap();
    copy_tool_check_sysroot(&session, &source, &destination);
    assert!(!destination.join("lib/rustlib/src").exists());
    assert!(!destination.join("lib/rustlib/rustc-src").exists());
    assert_eq!(fs::read(outside.join("marker")).unwrap(), b"original source");
}

#[test]
fn tool_check_sysroot_is_explicit_and_tracked_without_losing_rmeta_paths() {
    let sysroot = Path::new("check output/isolated std");
    let roots =
        [RmetaSysroot { host_dir: "checked/host".into(), target_dir: "checked/target".into() }];
    let environment = cargo_environment_with_tool_sysroot(&roots, Some(sysroot));
    assert_eq!(environment["RUSTC_SYSROOT"], sysroot.to_str().unwrap());
    assert_eq!(
        environment["RUSTC_ADDITIONAL_SYSROOT_PATHS"],
        "existing-shim-path,checked/host,checked/target"
    );
    let flags = tracked_flags(&environment);
    assert!(flags.windows(2).any(|args| args == ["--sysroot", "check output/isolated std"]));
    assert!(flags.contains(&"-Lall=checked/host"));
    assert!(flags.contains(&"-Lall=checked/target"));
    assert!(flags.contains(&"--cfg=existing_flag"));
}

// Trust: an unreplaceable destination cannot retain old metadata and earn a check.
#[test]
#[should_panic(expected = "failed to replace tool-check sysroot")]
fn tool_check_sysroot_refuses_unreplaceable_destination() {
    let context = TestCtx::new();
    let session = Session::new(
        context.config("check").path("compiler/rustc").stage(1).no_dry_run().create_config(),
    );
    let source = context.dir().join("source");
    let destination = context.dir().join("not-a-directory");
    fs::create_dir_all(source.join("lib")).unwrap();
    fs::write(&destination, b"must not be overwritten").unwrap();
    copy_tool_check_sysroot(&session, &source, &destination);
}
