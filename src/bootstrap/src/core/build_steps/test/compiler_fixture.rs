//! Trust: explicit compiler library-test runtime selection. A retained fixture
//! never selects the compiler or sysroot used to build the test binary.

use std::path::{Path, PathBuf};

use crate::core::config::Config;
use crate::core::config::flags::Subcommand;

/// Reject unsupported requests before a retained input can replace any normal
/// runtime prerequisite. The selected Cargo command is restricted to `--lib`.
pub(crate) fn validate_request(config: &Config) -> Result<(), String> {
    if config.compiler_test_fixture.is_none() {
        return Ok(());
    }
    let Subcommand::Test { trust_repo_check, trust_verified, .. } = &config.cmd else {
        return Err("compiler-test-fixture is only supported by compiler library tests".into());
    };
    if *trust_repo_check || *trust_verified {
        return Err(
            "compiler-test-fixture cannot select a verification or repository workflow".into()
        );
    }
    if config.cmd.test_target().runs_doctests() {
        return Err(
            "compiler-test-fixture requires explicit --tests or --no-doc; doctests are unsupported"
                .into(),
        );
    }
    if config.stage == 0 {
        return Err(
            "compiler-test-fixture requires a compiler library test stage of at least one".into()
        );
    }
    if config.include_default_paths || config.paths.is_empty() {
        return Err("compiler-test-fixture requires explicit compiler crate paths without default selections".into());
    }
    if config.hosts != [config.host_target]
        || config
            .target_config
            .get(&config.host_target)
            .is_some_and(|target| target.runner.is_some() || target.qemu_rootfs.is_some())
        || std::env::var_os("TEST_DEVICE_ADDR").is_some()
    {
        return Err("compiler-test-fixture supports only local tests on the build host".into());
    }
    let compiler = config
        .src
        .join("compiler")
        .canonicalize()
        .map_err(|error| format!("cannot resolve compiler library test source: {error}"))?;
    for path in &config.paths {
        let path = if path.is_absolute() { path.clone() } else { config.src.join(path) };
        let path = path.canonicalize().map_err(|error| {
            format!("cannot resolve compiler library test selector {}: {error}", path.display())
        })?;
        if path.parent() != Some(compiler.as_path()) || !library_manifest(&path)? {
            return Err(format!(
                "compiler-test-fixture requires an explicit compiler/<crate> library path: {}",
                path.display()
            ));
        }
    }
    Ok(())
}

fn library_manifest(path: &Path) -> Result<bool, String> {
    let manifest = std::fs::read_to_string(path.join("Cargo.toml"))
        .map_err(|error| format!("cannot read compiler crate manifest: {error}"))?;
    let manifest: toml::Value = toml::from_str(&manifest)
        .map_err(|error| format!("cannot parse compiler crate manifest: {error}"))?;
    let library = manifest.get("lib");
    if library.is_none()
        && manifest.get("package").and_then(|package| package.get("autolib"))
            == Some(&toml::Value::Boolean(false))
    {
        return Ok(false);
    }
    let file = library.and_then(|library| library.get("path"));
    let file = match file {
        Some(toml::Value::String(file)) => PathBuf::from(file),
        Some(_) => return Err("compiler library path must be a string".into()),
        None => PathBuf::from("src/lib.rs"),
    };
    let file = path
        .join(file)
        .canonicalize()
        .map_err(|error| format!("cannot resolve compiler library source: {error}"))?;
    Ok(file.starts_with(path) && file.is_file())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::utils::tests::TestCtx;

    fn selected(ctx: &TestCtx, command: &str, arguments: &[&str]) -> Config {
        let source = ctx.dir().join("source");
        let crate_dir = source.join("compiler/fixture_crate");
        std::fs::create_dir_all(crate_dir.join("src")).unwrap();
        std::fs::write(
            crate_dir.join("Cargo.toml"),
            "[package]\nname = 'fixture_crate'\nversion = '0.0.0'\n",
        )
        .unwrap();
        std::fs::write(crate_dir.join("src/lib.rs"), "").unwrap();
        let mut config = ctx.config(command).stage(1).args(arguments).create_config();
        config.src = source;
        config.compiler_test_fixture = Some(ctx.dir().join("runtime-fixture"));
        config
    }

    #[test]
    fn retained_compiler_fixture_requires_explicit_doc_free_library_selection() {
        for arguments in
            [vec!["--tests", "compiler/fixture_crate"], vec!["--no-doc", "compiler/fixture_crate"]]
        {
            let ctx = TestCtx::new();
            assert!(validate_request(&selected(&ctx, "test", &arguments)).is_ok());
        }
        for arguments in [
            vec!["compiler/fixture_crate"],
            vec!["--doc", "compiler/fixture_crate"],
            vec!["--tests"],
            vec!["--tests", "compiler"],
            vec!["--tests", "compiler/fixture_crate", "src/bootstrap"],
        ] {
            let ctx = TestCtx::new();
            assert!(validate_request(&selected(&ctx, "test", &arguments)).is_err());
        }
        let ctx = TestCtx::new();
        assert!(validate_request(&selected(&ctx, "build", &["compiler/fixture_crate"])).is_err());
    }

    #[test]
    fn retained_compiler_fixture_preserves_default_and_rejects_non_library_sources() {
        let ctx = TestCtx::new();
        let mut config = selected(&ctx, "test", &["--tests", "compiler/fixture_crate"]);
        config.compiler_test_fixture = None;
        config.paths.clear();
        assert!(validate_request(&config).is_ok(), "unselected requests keep their defaults");
        config.compiler_test_fixture = Some(ctx.dir().join("runtime-fixture"));
        config.paths = vec!["compiler/fixture_crate".into()];
        std::fs::write(
            config.src.join("compiler/fixture_crate/Cargo.toml"),
            "[package]\nname = 'fixture_crate'\nversion = '0.0.0'\nautolib = false\n",
        )
        .unwrap();
        assert!(validate_request(&config).is_err());
    }

    #[test]
    fn retained_compiler_fixture_cli_overrides_config_without_selecting_build_rustc() {
        let ctx = TestCtx::new();
        let baseline =
            ctx.config("test").path("compiler/rustc_mir_transform").arg("--tests").create_config();
        let config = ctx
            .config("test")
            .path("compiler/rustc_mir_transform")
            .arg("--tests")
            .args(&["--compiler-test-fixture", "/explicit/cli-fixture"])
            .with_default_toml_config(
                "[build]\ncompiler-test-fixture = '/explicit/config-fixture'\n",
            )
            .create_config();
        assert_eq!(
            config.compiler_test_fixture.as_deref(),
            Some(Path::new("/explicit/cli-fixture"))
        );
        assert_eq!(config.external_rustc, baseline.external_rustc);
        assert_eq!(config.external_cargo, baseline.external_cargo);
        assert!(config.keep_stage.is_empty());
        assert!(config.keep_stage_std.is_empty());
    }
}
