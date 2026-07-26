use std::fs;
use std::path::{Path, PathBuf};

use super::resolve_file_url_path;
use crate::core::config::TargetSelection;
use crate::utils::helpers::exe;

#[test]
fn dedicated_trustfmt_uses_the_canonical_archive_component_prefix() {
    assert_eq!(super::dedicated_trustfmt_component_prefix(), "trustfmt");
}

#[test]
fn dedicated_trustfmt_rejects_a_stamped_but_partial_payload() {
    let tmp = std::env::temp_dir().join(format!(
        "trustfmt-payload-contract-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("system clock should be after epoch")
            .as_nanos()
    ));
    fs::create_dir_all(&tmp).expect("create formatter fixture");
    let trustfmt = tmp.join("trustfmt");
    let targo_fmt = tmp.join("targo-fmt");

    fs::write(&trustfmt, b"formatter").expect("write trustfmt fixture");
    assert!(
        !super::dedicated_trustfmt_payload_is_complete(&trustfmt, &targo_fmt),
        "one formatter binary must not bless a partial payload"
    );
    fs::write(&targo_fmt, b"driver").expect("write targo-fmt fixture");
    assert!(super::dedicated_trustfmt_payload_is_complete(&trustfmt, &targo_fmt));

    fs::remove_dir_all(&tmp).expect("remove formatter fixture");
}

#[test]
fn stage0_beta_downloads_targo_and_targo_trust() {
    let components = super::stage0_beta_extra_components();
    assert!(components.contains(&"targo"));
    assert!(components.contains(&"targo-trust"));
    assert!(components.contains(&"trustfmt"));
    assert!(components.contains(&"tippy"));
    assert!(components.contains(&"trust-analyzer"));
}

#[test]
fn stage0_targo_downloads_prefer_canonical_and_admit_only_pinned_legacy_inputs() {
    let date = "2026-06-23";
    let version = "1.96.0-trust";
    let host = "aarch64-apple-darwin";

    for (component, legacy_component) in [("targo", "tcargo"), ("targo-trust", "tcargo-trust")] {
        let legacy_url = format!("dist/{date}/{legacy_component}-{version}-{host}.tar.xz");
        let canonical_url = format!("dist/{date}/{component}-{version}-{host}.tar.xz");
        let mut checksums = std::collections::BTreeMap::from([(legacy_url, "legacy".to_owned())]);

        assert_eq!(
            super::select_stage0_targo_download(&checksums, date, version, host, component),
            super::TargoStage0Download {
                filename: format!("{legacy_component}-{version}-{host}.tar.xz"),
                prefix: legacy_component.to_owned(),
                legacy: true,
            }
        );

        checksums.insert(canonical_url, "canonical".to_owned());
        assert_eq!(
            super::select_stage0_targo_download(&checksums, date, version, host, component),
            super::TargoStage0Download {
                filename: format!("{component}-{version}-{host}.tar.xz"),
                prefix: component.to_owned(),
                legacy: false,
            }
        );

        assert_eq!(
            super::select_stage0_targo_download(
                &std::collections::BTreeMap::new(),
                date,
                version,
                host,
                component,
            ),
            super::TargoStage0Download {
                filename: format!("{component}-{version}-{host}.tar.xz"),
                prefix: component.to_owned(),
                legacy: false,
            }
        );
    }
}

#[cfg(unix)]
#[test]
fn legacy_stage0_targo_payload_is_semantically_translated_without_public_alias_leaves() {
    use std::os::unix::fs::PermissionsExt;
    use std::process::Command;

    let host = TargetSelection::from_user("x86_64-unknown-linux-gnu");
    let tmp = std::env::temp_dir().join(format!(
        "trust-stage0-legacy-targo-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("system clock should be after epoch")
            .as_nanos()
    ));
    let bin = tmp.join("bin");
    fs::create_dir_all(&bin).expect("create temp stage0 bin");

    let write_executable = |path: &Path, contents: &str| {
        fs::write(path, contents).expect("write fake legacy Targo tool");
        fs::set_permissions(path, fs::Permissions::from_mode(0o755))
            .expect("mark fake legacy Targo tool executable");
    };
    write_executable(
        &bin.join(exe("tcargo", host)),
        r#"#!/bin/sh
case "${1-}" in
    --version|-V|-vV)
        printf '%s\n' 'tcargo 1.96.0-trust' 'binary: tcargo'
        exit 0
        ;;
esac
printf '%s\n' "$(basename "$0")" "$@" >"$TARGO_ARG_LOG"
"#,
    );
    write_executable(&bin.join(exe("cargo", host)), "#!/bin/sh\nexit 0\n");
    for compiler_tool in ["trustc", "trustdoc"] {
        write_executable(
            &bin.join(exe(compiler_tool, host)),
            &format!("#!/bin/sh\nprintf '%s\\n' {compiler_tool}\n"),
        );
    }
    write_executable(&bin.join(exe("tcargo-fmt", host)), "#!/bin/sh\nprintf '%s\\n' legacy-fmt\n");
    for retired in ["cargo-fmt", "rustfmt", "rustdoc", "rust-analyzer"] {
        fs::write(bin.join(exe(retired, host)), b"retired alias")
            .expect("write retired companion alias");
    }
    let libexec = tmp.join("libexec");
    fs::create_dir_all(&libexec).expect("create temp stage0 libexec");
    fs::write(libexec.join(exe("rust-analyzer-proc-macro-srv", host)), b"retired helper alias")
        .expect("write retired analyzer helper");
    write_executable(
        &bin.join(exe("tcargo-trust", host)),
        r#"#!/bin/sh
if [ "${1-}" = "trust" ]; then shift; fi
case "${1-}" in
    --version|-V)
        printf '%s\n' 'tcargo-trust 1.96.0-trust' 'trust.identity=tcargo trust' 'trust.package=tcargo-trust'
        exit 0
        ;;
esac
printf '%s\n' "$@" >"$TARGO_TRUST_ARG_LOG"
"#,
    );
    fs::write(bin.join(exe("cargo-trust", host)), b"retired alias").expect("write retired alias");

    super::translate_legacy_targo_stage0_surface(&tmp, host, &["targo", "targo-trust"]);

    let targo = bin.join(exe("targo", host));
    let version = Command::new(&targo).arg("--version").output().expect("run translated targo");
    assert!(version.status.success());
    assert_eq!(
        String::from_utf8(version.stdout).expect("UTF-8 targo version"),
        "targo 1.96.0-trust\nbinary: targo\n"
    );

    let arg_log = tmp.join("targo-args.log");
    let trust_arg_log = tmp.join("targo-trust-args.log");
    let status = Command::new(&targo)
        .args(["build", "--locked"])
        .env("TARGO_ARG_LOG", &arg_log)
        .env("TARGO_TRUST_ARG_LOG", &trust_arg_log)
        .status()
        .expect("run translated targo command");
    assert!(status.success());
    assert_eq!(
        fs::read_to_string(&arg_log).expect("read targo argument log"),
        "tcargo\nbuild\n--locked\n"
    );

    let targo_trust = bin.join(exe("targo-trust", host));
    let version =
        Command::new(&targo_trust).arg("--version").output().expect("run translated targo-trust");
    assert!(version.status.success());
    let version = String::from_utf8(version.stdout).expect("UTF-8 targo-trust version");
    assert!(version.contains("targo-trust 1.96.0-trust"));
    assert!(version.contains("trust.identity=targo trust"));
    assert!(!version.contains("tcargo"));

    let private_dispatch = tmp.join("libexec").join("tcargo-trust");
    let version = Command::new(private_dispatch)
        .args(["trust", "--version"])
        .output()
        .expect("run private legacy dispatch shim");
    assert!(version.status.success());
    assert!(!String::from_utf8(version.stdout).expect("UTF-8 shim version").contains("tcargo"));

    assert!(bin.join(exe("cargo", host)).exists());
    assert!(bin.join(exe("targo-fmt", host)).exists());
    assert!(bin.join(exe("trustfmt", host)).exists());
    assert!(bin.join(exe("trust-analyzer", host)).exists());
    let fmt_output = Command::new(tmp.join("libexec").join("tcargo-fmt"))
        .output()
        .expect("run private fmt forwarding shim");
    assert!(fmt_output.status.success());
    assert_eq!(
        String::from_utf8(fmt_output.stdout).expect("UTF-8 fmt shim output"),
        "legacy-fmt\n"
    );
    for compiler_tool in ["trustc", "trustdoc"] {
        let output = Command::new(tmp.join("libexec").join(compiler_tool))
            .output()
            .expect("run private compiler forwarding shim");
        assert!(output.status.success());
        assert_eq!(
            String::from_utf8(output.stdout).expect("UTF-8 compiler shim output"),
            format!("{compiler_tool}\n")
        );
    }
    for legacy in [
        "tcargo",
        "tcargo-trust",
        "tcargo-fmt",
        "cargo-trust",
        "cargo-fmt",
        "rustfmt",
        "rustdoc",
        "rust-analyzer",
    ] {
        assert!(!bin.join(exe(legacy, host)).exists(), "legacy entrypoint {legacy} survived");
    }
    assert!(!libexec.join(exe("rust-analyzer-proc-macro-srv", host)).exists());
    assert!(libexec.join(exe("trust-analyzer-proc-macro-srv", host)).exists());

    fs::remove_dir_all(&tmp).expect("remove temp stage0 bin");
}

#[test]
fn stage0_tippy_download_prefers_canonical_and_admits_the_pinned_legacy_input() {
    let date = "2026-06-23";
    let version = "1.96.0-trust";
    let host = "aarch64-apple-darwin";
    let legacy_url = format!("dist/{date}/trust-clippy-{version}-{host}.tar.xz");
    let canonical_url = format!("dist/{date}/tippy-{version}-{host}.tar.xz");
    let mut checksums = std::collections::BTreeMap::from([(legacy_url, "legacy".to_owned())]);

    assert_eq!(
        super::select_stage0_tippy_download(&checksums, date, version, host),
        super::TippyStage0Download {
            filename: format!("trust-clippy-{version}-{host}.tar.xz"),
            prefix: "trust-clippy-preview",
            legacy: true,
        }
    );

    checksums.insert(canonical_url, "canonical".to_owned());
    assert_eq!(
        super::select_stage0_tippy_download(&checksums, date, version, host),
        super::TippyStage0Download {
            filename: format!("tippy-{version}-{host}.tar.xz"),
            prefix: "tippy",
            legacy: false,
        }
    );
}

#[cfg(unix)]
#[test]
fn legacy_stage0_tippy_payload_is_semantically_translated_without_alias_leaves() {
    use std::os::unix::fs::PermissionsExt;
    use std::process::Command;

    let host = TargetSelection::from_user("x86_64-unknown-linux-gnu");
    let tmp = std::env::temp_dir().join(format!(
        "trust-stage0-legacy-tippy-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("system clock should be after epoch")
            .as_nanos()
    ));
    let bin = tmp.join("bin");
    fs::create_dir_all(&bin).expect("create temp stage0 bin");
    let fake_frontend = r#"#!/bin/sh
printf '%s\n' "$@" >"$TIPPY_ARG_LOG"
case "$0" in
  */*) frontend_dir=${0%/*} ;;
  *) frontend_dir=. ;;
esac
test -x "$frontend_dir/trust-clippy-driver" || exit 97
"$frontend_dir/trust-clippy-driver" --frontend-probe
"$CARGO" --frontend-cargo-probe
case " $* " in
  *" --version "*|*" -V "*|*" -vV "*|*" -Vv "*)
    printf 'cargo-clippy 0.1.0\nbinary: cargo-clippy\n'
    ;;
esac
"#;
    for name in ["trust-clippy", "cargo-clippy"] {
        let path = bin.join(exe(name, host));
        fs::write(&path, fake_frontend).expect("write fake legacy Tippy frontend");
        fs::set_permissions(&path, fs::Permissions::from_mode(0o755))
            .expect("make fake legacy Tippy frontend executable");
    }
    let fake_driver = r#"#!/bin/sh
case " $* " in
  *" -vV "*|*" -Vv "*)
    printf 'rustc 1.96.0\nbinary: rustc\nhost: test-host\n'
    ;;
  *" --version "*|*" -V "*)
    printf 'clippy-driver 0.1.0\nbinary: clippy-driver\n'
    ;;
  *) printf '%s\n' "$@" >"$TIPPY_DRIVER_ARG_LOG" ;;
esac
"#;
    for name in ["trust-clippy-driver", "clippy-driver"] {
        let path = bin.join(exe(name, host));
        fs::write(&path, fake_driver).expect("write fake legacy Tippy driver");
        fs::set_permissions(&path, fs::Permissions::from_mode(0o755))
            .expect("make fake legacy Tippy driver executable");
    }
    let canonical_targo = bin.join(exe("targo", host));
    fs::write(
        &canonical_targo,
        "#!/bin/sh\nif [ -n \"${TIPPY_TARGO_ARG_LOG-}\" ]; then\n    printf '%s\\n' \"$@\" >\"$TIPPY_TARGO_ARG_LOG\"\nfi\n",
    )
    .expect("write canonical fake Targo");
    fs::set_permissions(&canonical_targo, fs::Permissions::from_mode(0o755))
        .expect("make canonical fake Targo executable");

    super::translate_legacy_tippy_stage0_surface(&tmp, host);

    let arg_log = tmp.join("tippy-args.log");
    let driver_arg_log = tmp.join("tippy-driver-args.log");
    let targo_arg_log = tmp.join("tippy-targo-args.log");
    let ambient_cargo_sentinel = tmp.join("ambient-cargo-was-used");
    let ambient_cargo = tmp.join("ambient-cargo");
    fs::write(&ambient_cargo, "#!/bin/sh\nprintf used >\"$TIPPY_CARGO_SENTINEL\"\nexit 98\n")
        .expect("write hostile ambient Cargo");
    fs::set_permissions(&ambient_cargo, fs::Permissions::from_mode(0o755))
        .expect("make hostile ambient Cargo executable");
    assert!(
        Command::new(bin.join(exe("tippy", host)))
            .arg("--workspace")
            .env("TIPPY_ARG_LOG", &arg_log)
            .env("TIPPY_DRIVER_ARG_LOG", &driver_arg_log)
            .env("TIPPY_TARGO_ARG_LOG", &targo_arg_log)
            .env("TIPPY_CARGO_SENTINEL", &ambient_cargo_sentinel)
            .env("CARGO", &ambient_cargo)
            .status()
            .expect("run translated direct Tippy")
            .success()
    );
    assert_eq!(
        fs::read_to_string(&arg_log).expect("read direct Tippy args"),
        "clippy\n--workspace\n"
    );
    assert_eq!(
        fs::read_to_string(&driver_arg_log).expect("read private driver probe args"),
        "--frontend-probe\n"
    );
    assert_eq!(
        fs::read_to_string(&targo_arg_log).expect("read canonical Targo probe args"),
        "--frontend-cargo-probe\n"
    );
    assert!(!ambient_cargo_sentinel.exists(), "ambient Cargo was executed");
    assert!(
        Command::new(bin.join(exe("targo-tippy", host)))
            .args(["tippy", "--all-targets"])
            .env("TIPPY_ARG_LOG", &arg_log)
            .env("TIPPY_DRIVER_ARG_LOG", &driver_arg_log)
            .status()
            .expect("run translated Targo subcommand")
            .success()
    );
    assert_eq!(
        fs::read_to_string(&arg_log).expect("read Targo Tippy args"),
        "clippy\n--all-targets\n"
    );
    assert!(
        Command::new(bin.join(exe("tippy-driver", host)))
            .args(["--edition", "2024", "input.rs"])
            .env("TIPPY_ARG_LOG", &arg_log)
            .env("TIPPY_DRIVER_ARG_LOG", &driver_arg_log)
            .status()
            .expect("run translated Tippy driver")
            .success()
    );
    assert_eq!(
        fs::read_to_string(&driver_arg_log).expect("read Tippy driver args"),
        "--edition\n2024\ninput.rs\n"
    );

    let version_queries: &[&[&str]] = &[
        &["--version"],
        &["-V"],
        &["-vV"],
        &["-Vv"],
        &["--version", "--verbose"],
        &["--verbose", "--version"],
    ];
    for query in version_queries {
        for (name, marker) in
            [("tippy", None), ("targo-tippy", Some("tippy")), ("tippy-driver", None)]
        {
            let mut command = Command::new(bin.join(exe(name, host)));
            if let Some(marker) = marker {
                command.arg(marker);
            }
            let output = command
                .args(*query)
                .env("TIPPY_ARG_LOG", &arg_log)
                .env("TIPPY_DRIVER_ARG_LOG", &driver_arg_log)
                .output()
                .expect("run translated Tippy version query");
            assert!(output.status.success(), "{name} {query:?} failed");
            let stdout = String::from_utf8(output.stdout).expect("Tippy version output is UTF-8");
            if name == "tippy-driver" && matches!(*query, ["-vV"] | ["-Vv"]) {
                assert!(stdout.starts_with("rustc "), "{name} {query:?}: {stdout:?}");
                assert!(stdout.contains("binary: rustc\n"), "{name} {query:?}: {stdout:?}");
            } else {
                assert!(stdout.starts_with("tippy "), "{name} {query:?}: {stdout:?}");
                assert!(
                    stdout.contains(&format!("binary: {name}\n")),
                    "{name} {query:?}: {stdout:?}"
                );
            }
        }
    }
    assert!(tmp.join("libexec/tippy-stage0-backend").exists());
    assert!(tmp.join("libexec/tippy-driver-stage0-backend").exists());
    for private_protocol in ["trust-clippy-driver", "clippy-driver"] {
        assert!(
            tmp.join("libexec").join(exe(private_protocol, host)).is_file(),
            "missing private legacy driver discovery shim {private_protocol}"
        );
    }
    for name in ["trust-clippy", "cargo-clippy", "trust-clippy-driver", "clippy-driver"] {
        assert!(!bin.join(exe(name, host)).exists(), "legacy entrypoint {name} survived");
    }

    fs::remove_dir_all(&tmp).expect("remove temp stage0 bin");
}

#[test]
fn stage0_surface_uses_only_required_compatibility_entrypoints() {
    assert_eq!(
        super::stage0_required_bins(),
        &[
            "trustc",
            "rustc",
            "trustdoc",
            "targo",
            "cargo",
            "targo-trust",
            "trustfmt",
            "targo-fmt",
            "tippy",
            "targo-tippy",
            "tippy-driver",
            "trust-analyzer",
        ]
    );
    assert_eq!(super::stage0_required_libexec_bins(), &["trust-analyzer-proc-macro-srv"]);
    assert!(super::stage0_forbidden_bins().contains(&"rustdoc"));
    assert!(super::stage0_forbidden_bins().contains(&"rustfmt"));
    assert!(super::stage0_forbidden_bins().contains(&"rust-analyzer"));
    assert!(super::stage0_forbidden_bins().contains(&"tcargo"));
    assert!(super::stage0_forbidden_bins().contains(&"tcargo-trust"));
    assert!(super::stage0_forbidden_bins().contains(&"tcargo-fmt"));
    assert!(super::stage0_forbidden_bins().contains(&"rust-windbg.cmd"));
    assert!(super::stage0_forbidden_libexec_bins().contains(&"rust-analyzer-proc-macro-srv"));
}

#[test]
fn stage0_beta_refreshes_when_targo_trust_is_missing_from_stamped_sysroot() {
    let host = TargetSelection::from_user("x86_64-unknown-linux-gnu");
    let tmp = std::env::temp_dir().join(format!(
        "trust-stage0-components-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("system clock should be after epoch")
            .as_nanos()
    ));
    let bin = tmp.join("bin");
    fs::create_dir_all(&bin).expect("create temp stage0 bin");
    fs::write(bin.join(exe("targo", host)), b"targo").expect("write fake targo");

    assert!(super::missing_extra_component_bin(&tmp, host, super::stage0_beta_extra_components()));

    for name in ["targo-trust", "trustfmt", "tippy", "trust-analyzer"] {
        fs::write(bin.join(exe(name, host)), name).expect("write fake extra component");
    }
    assert!(!super::missing_extra_component_bin(&tmp, host, super::stage0_beta_extra_components()));

    fs::remove_dir_all(&tmp).expect("remove temp stage0 bin");
}

#[test]
fn stage0_beta_refreshes_when_alias_bins_are_missing_from_stamped_sysroot() {
    let host = TargetSelection::from_user("x86_64-unknown-linux-gnu");
    let tmp = std::env::temp_dir().join(format!(
        "trust-stage0-aliases-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("system clock should be after epoch")
            .as_nanos()
    ));
    let bin = tmp.join("bin");
    let libexec = tmp.join("libexec");
    fs::create_dir_all(&bin).expect("create temp stage0 bin");
    fs::create_dir_all(&libexec).expect("create temp stage0 libexec");
    fs::write(bin.join(exe("targo", host)), b"targo").expect("write fake targo");
    fs::write(bin.join(exe("targo-trust", host)), b"targo-trust").expect("write fake targo-trust");

    assert!(super::stage0_tool_surface_needs_refresh(&tmp, host, "stage0"));

    fs::remove_file(bin.join(exe("targo", host))).expect("remove fake targo");
    assert!(super::stage0_tool_surface_needs_refresh(&tmp, host, "stage0"));

    for name in super::stage0_required_bins() {
        fs::write(bin.join(exe(name, host)), name).expect("write fake required stage0 bin");
    }
    for name in super::stage0_required_libexec_bins() {
        fs::write(libexec.join(exe(name, host)), name)
            .expect("write fake required stage0 libexec bin");
    }
    assert!(!super::stage0_tool_surface_needs_refresh(&tmp, host, "stage0"));
    assert!(!super::stage0_tool_surface_needs_refresh(&tmp, host, "stage1"));

    fs::write(bin.join(exe("miri", host)), b"miri").expect("write unsupported miri");
    assert!(super::stage0_tool_surface_needs_refresh(&tmp, host, "stage0"));

    fs::remove_dir_all(&tmp).expect("remove temp stage0 bin");
}

#[test]
fn stage0_surface_rejects_unsupported_inherited_bins() {
    let host = TargetSelection::from_user("x86_64-unknown-linux-gnu");
    let tmp = std::env::temp_dir().join(format!(
        "trust-stage0-normalize-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("system clock should be after epoch")
            .as_nanos()
    ));
    let bin = tmp.join("bin");
    let libexec = tmp.join("libexec");
    fs::create_dir_all(&bin).expect("create temp stage0 bin");
    fs::create_dir_all(&libexec).expect("create temp stage0 libexec");
    for name in super::stage0_forbidden_bins() {
        fs::write(bin.join(exe(name, host)), name).expect("write fake legacy tool");
    }
    for name in super::stage0_required_bins() {
        fs::write(bin.join(exe(name, host)), name).expect("write fake required stage0 bin");
    }
    for name in super::stage0_required_libexec_bins() {
        fs::write(libexec.join(exe(name, host)), name)
            .expect("write fake required stage0 libexec bin");
    }
    for name in super::stage0_forbidden_libexec_bins() {
        fs::write(libexec.join(exe(name, host)), name)
            .expect("write fake forbidden stage0 libexec bin");
    }

    assert!(super::stage0_tool_surface_needs_refresh(&tmp, host, "stage0"));

    fs::remove_dir_all(&tmp).expect("remove temp stage0 bin");
}

#[test]
fn resolves_trust_root_file_url_token() {
    let source = resolve_file_url_path(
        "file://{trust-root}/build/trust-stage0/dist/archive.tar.xz",
        Path::new("/repo/trust"),
    );
    assert_eq!(source, PathBuf::from("/repo/trust/build/trust-stage0/dist/archive.tar.xz"));
}

#[test]
fn resolves_localhost_file_urls_as_absolute_paths() {
    let source =
        resolve_file_url_path("file://localhost/tmp/trust/archive.tar.xz", Path::new("/repo"));
    assert_eq!(source, PathBuf::from("/tmp/trust/archive.tar.xz"));
}

#[test]
fn rejects_inherited_upstream_rust_download_hosts() {
    for url in [
        "https://static.rust-lang.org/dist/channel-rust-trust.toml",
        "https://ci-artifacts.rust-lang.org/rustc-builds/archive.tar.xz",
        "https://dev-static.rust-lang.org/dist/archive.tar.xz",
        "https://rust-lang.org/dist/archive.tar.xz",
    ] {
        assert!(
            super::inherited_upstream_rust_download_host(url).is_some(),
            "expected inherited upstream Rust host rejection for {url}"
        );
    }
}

#[test]
fn allows_non_rust_download_hosts_and_file_urls() {
    for url in [
        "file://{trust-root}/bootstrap/trust-stage0/dist/archive.tar.xz",
        "https://trust-artifacts.example/dist/archive.tar.xz",
        "https://static.rust-lang.org.evil.example/dist/archive.tar.xz",
    ] {
        assert_eq!(
            super::inherited_upstream_rust_download_host(url),
            None,
            "expected allowed Trust/nonmatching URL: {url}"
        );
    }
}
