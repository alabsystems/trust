//! Trust: invocation-aware native admission policy without compiler execution.

use std::ffi::{OsStr, OsString};

#[expect(
    clippy::print_stdout,
    reason = "native resource discovery emits machine-readable JSON before a project or Shell is constructed"
)]
pub(super) fn respond(args: &[OsString]) -> bool {
    if args
        .first()
        .is_none_or(|arg| arg != "--resource-capabilities")
    {
        return false;
    }
    // Fixed original-claim admission does not require or advertise a paired
    // compiler worker runtime. Discovery is not admission or Host readiness.
    if args.get(1).is_some_and(|arg| arg == "--fixed-admission-v1") {
        if args.len() == 2 && cfg!(all(target_os = "macos", target_arch = "aarch64")) {
            println!("{{\"version\":1,\"fixed_admission\":\"original-fixed-v1\"}}");
        } else {
            println!("{{\"version\":1,\"fixed_admission\":null}}");
        }
        return true;
    }
    if args.get(1).is_some_and(|arg| arg == "--sealed-metadata-v1") {
        #[cfg(unix)]
        if args.len() == 2 && cfg!(all(target_os = "macos", target_arch = "aarch64")) {
            println!("{}", targo::metadata_service::capabilities());
            return true;
        }
        println!("{{\"version\":3,\"sealed_metadata\":null}}");
        return true;
    }
    // Driver-only discovery cannot prove the effective compiler cohort.
    // Native admission must supply the complete invocation and resolve its
    // configuration through the same parser as actual execution.
    if args.get(1).is_some_and(|arg| arg == "--") && invocation_supported(&args[2..]) {
        if let Ok(mut gctx) = targo::util::GlobalContext::default() {
            match super::cli::native_capability(&mut gctx, &args[2..]) {
                Ok(()) => return true,
                Err(error) => {
                    if let Some(error) = error.error.as_ref().filter(|error| native_refusal(error))
                    {
                        println!(
                            "{}",
                            serde_json::json!({
                                "version": 3,
                                "cpu_workers": true,
                                "supports_invocation": true,
                                "runtime_refusal": error.to_string(),
                            })
                        );
                        return true;
                    }
                }
            }
        }
    }
    println!("{{\"version\":3,\"cpu_workers\":false,\"supports_invocation\":false}}");
    true
}

#[expect(clippy::print_stdout, reason = "native admission capability response")]
pub(super) fn configured(
    gctx: &targo::util::GlobalContext,
    check_arguments: impl FnOnce() -> targo::util::CargoResult<()>,
) -> targo::util::CargoResult<()> {
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    {
        let _paired = require_paired_compiler(gctx)?;
        check_arguments()?;
        println!("{{\"version\":3,\"cpu_workers\":true,\"supports_invocation\":true}}");
        Ok(())
    }
    #[cfg(not(all(target_os = "macos", target_arch = "aarch64")))]
    {
        let _ = (gctx, check_arguments);
        anyhow::bail!("native compiler pairing is unsupported on this host")
    }
}

fn native_refusal(error: &anyhow::Error) -> bool {
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    if error.is::<NativeHelperRefusal>() {
        return true;
    }
    error.is::<targo::ops::NativeTestBudgetRefusal>()
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[derive(Debug)]
struct NativeHelperRefusal(String);
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
impl std::fmt::Display for NativeHelperRefusal {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(&self.0)
    }
}
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
impl std::error::Error for NativeHelperRefusal {}

/// Trust: ordinary fixed commands retain a recognized compiler/runtime pair,
/// without claiming the native worker SDK's link/debug helper surface. A
/// metadata-only unit must not need tools it never invokes. Pair mismatches
/// retain the existing fixed-admission fallback; actual native-worker entry
/// and capability discovery use `require_paired_compiler` below.
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
pub(super) fn optional_paired_compiler(
    gctx: &targo::util::GlobalContext,
) -> targo::util::CargoResult<Option<trust_resource_provenance::program::HeldProgram>> {
    match hold_paired_compiler(gctx) {
        Ok(program) => Ok(Some(program)),
        Err(_) => Ok(None),
    }
}

/// Early refusal only: these observations confer neither helper custody nor a
/// CPU grant. Actual execution still independently admits its native profile.
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
fn preflight_native_helpers(root: &std::path::Path) -> Result<(), NativeHelperRefusal> {
    use std::os::unix::fs::PermissionsExt as _;
    for name in ["rust-lld", "dsymutil"] {
        let path = root.join("bin").join(name);
        match std::fs::symlink_metadata(&path) {
            Ok(metadata) if metadata.is_file() && metadata.permissions().mode() & 0o111 != 0 => {}
            _ => {
                return Err(NativeHelperRefusal(format!(
                    "selected native compiler SDK needs its regular executable {}; native helper preflight refused",
                    path.display()
                )));
            }
        }
    }
    Ok(())
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
pub(super) fn require_paired_compiler(
    gctx: &targo::util::GlobalContext,
) -> targo::util::CargoResult<trust_resource_provenance::program::HeldProgram> {
    require_native_helpers(hold_paired_compiler(gctx)?)
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
fn require_native_helpers(
    held: trust_resource_provenance::program::HeldProgram,
) -> targo::util::CargoResult<trust_resource_provenance::program::HeldProgram> {
    preflight_native_helpers(held.root())?;
    Ok(held)
}

/// Trust: keep the exact original compiler/runtime inputs through execution.
/// Compatibility supplies neither helper completeness nor a source/CPU grant.
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
fn hold_paired_compiler(
    gctx: &targo::util::GlobalContext,
) -> targo::util::CargoResult<trust_resource_provenance::program::HeldProgram> {
    use std::time::{Duration, Instant};

    let encoded = option_env!("TRUST_TARGO_PAIRED_COMPILER_PROFILE")
        .ok_or_else(|| anyhow::anyhow!("native worker mode requires a producer-paired compiler/runtime; no compiler was started"))?;
    let compiler = gctx.native_worker_compiler_path()?.ok_or_else(|| {
        anyhow::anyhow!(
            "native worker mode does not support compiler wrappers or prepared query adapters"
        )
    })?;
    let executable = std::env::current_exe()?.canonicalize()?;
    let bin = executable
        .parent()
        .ok_or_else(|| anyhow::anyhow!("Targo has no binary directory"))?;
    hold_selected_compiler(
        gctx,
        bin,
        &compiler,
        encoded,
        Instant::now() + Duration::from_secs(2),
    )
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
fn hold_selected_compiler(
    gctx: &targo::util::GlobalContext,
    bin: &std::path::Path,
    compiler: &std::path::Path,
    encoded: &str,
    deadline: std::time::Instant,
) -> targo::util::CargoResult<trust_resource_provenance::program::HeldProgram> {
    use std::ffi::OsString;

    let root = bin
        .parent()
        .ok_or_else(|| anyhow::anyhow!("Targo has no paired SDK root"))?;
    anyhow::ensure!(
        bin.file_name() == Some(OsStr::new("bin"))
            && compiler.is_absolute()
            && compiler.parent() == Some(bin)
            && matches!(
                compiler.file_name().and_then(OsStr::to_str),
                Some("trustc" | "rustc")
            ),
        "configured compiler is outside Targo's paired SDK layout"
    );
    anyhow::ensure!(
        std::fs::symlink_metadata(bin)?.is_dir()
            && !std::fs::symlink_metadata(&compiler)?
                .file_type()
                .is_symlink(),
        "paired compiler directory or image is an indirect selection"
    );
    let held = targo::paired_compiler::hold(root, compiler, encoded, deadline)?;
    let expected = held.runtime_environment()?;
    let configured = gctx.env_config()?;
    let mut keys = std::env::vars_os()
        .map(|(key, _)| key)
        .collect::<std::collections::BTreeSet<_>>();
    keys.extend(configured.keys().map(OsString::from));
    for key in keys {
        if !key.as_encoded_bytes().starts_with(b"DYLD_")
            && !key.as_encoded_bytes().starts_with(b"LD_")
        {
            continue;
        }
        let key_str = key
            .to_str()
            .ok_or_else(|| anyhow::anyhow!("non-Unicode loader override"))?;
        if let Some(actual) = configured
            .get(key_str)
            .cloned()
            .or_else(|| std::env::var_os(&key))
        {
            anyhow::ensure!(
                expected
                    .iter()
                    .any(|(name, value)| name == &key && value == &actual),
                "configured compiler has an unsupported loader override"
            );
        }
    }
    Ok(held)
}

pub(super) fn invocation_supported(mut args: &[OsString]) -> bool {
    if args
        .first()
        .is_some_and(|arg| arg == "--resource-worker-v2")
    {
        args = &args[1..];
    }
    if args.len() < 2
        || args[0] != "--unverified"
        || args.iter().any(|arg| arg == "--resource-worker-v2")
    {
        return false;
    }
    match args[1].to_str() {
        Some("build" | "check") => true,
        Some("test") => {
            let selection = args[2..]
                .iter()
                .take_while(|arg| arg.as_os_str() != OsStr::new("--"))
                .collect::<Vec<_>>();
            // rustdoc's independent compile/execute tree retains its existing
            // route. Discovery never removes tests from the caller's request.
            !selection
                .iter()
                .any(|arg| arg.as_os_str() == OsStr::new("--doc"))
                && selection.iter().any(|arg| {
                    arg.as_os_str() == OsStr::new("--no-run")
                        || arg.to_str().is_some_and(|arg| {
                            [
                                "--lib",
                                "--tests",
                                "--test",
                                "--bins",
                                "--bin",
                                "--examples",
                                "--example",
                                "--benches",
                                "--bench",
                                "--all-targets",
                            ]
                            .iter()
                            .any(|name| arg == *name || arg.starts_with(&format!("{name}=")))
                        })
                })
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn typed_budget_refusal_is_distinct_from_an_unsupported_profile_error() {
        let error = targo::ops::validate_native_test_arguments(&["--test-threads=1"]).unwrap_err();
        assert!(native_refusal(&error));
        assert!(!native_refusal(&anyhow::anyhow!(error.to_string())));
    }

    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    #[test]
    fn helper_preflight_refuses_missing_nonexecutable_and_symlink_inputs() {
        use std::os::unix::fs::{PermissionsExt as _, symlink};
        let root = tempfile::tempdir().unwrap();
        let bin = root.path().join("bin");
        std::fs::create_dir(&bin).unwrap();
        let linker = bin.join("rust-lld");
        let debug = bin.join("dsymutil");
        assert!(preflight_native_helpers(root.path()).is_err());
        std::fs::write(
            &linker,
            b"presence observation only, never execution authority",
        )
        .unwrap();
        std::fs::set_permissions(&linker, std::fs::Permissions::from_mode(0o500)).unwrap();
        assert!(preflight_native_helpers(root.path()).is_err());
        std::fs::write(
            &debug,
            b"presence observation only, never execution authority",
        )
        .unwrap();
        std::fs::set_permissions(&debug, std::fs::Permissions::from_mode(0o400)).unwrap();
        assert!(preflight_native_helpers(root.path()).is_err());
        std::fs::set_permissions(&debug, std::fs::Permissions::from_mode(0o500)).unwrap();
        assert!(preflight_native_helpers(root.path()).is_ok());
        std::fs::remove_file(&debug).unwrap();
        symlink(&linker, &debug).unwrap();
        assert!(preflight_native_helpers(root.path()).is_err());
    }

    /// The provider and profile are actual qualified input DATA, not a fake
    /// compiler, SDK receipt, native-worker grant or favorable proof result.
    /// Run explicitly with the retained provider; absence never counts as PASS.
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    #[test]
    #[ignore = "requires real retained compiler bin/profile input paths"]
    fn real_pair_without_helpers_retains_ordinary_custody_but_refuses_native_worker() {
        use std::path::PathBuf;
        use std::time::{Duration, Instant};

        const ACTOR: &str = "TARGO_TEST_REAL_PAIR_ACTOR";
        const NAME: &str = "resource_capabilities::tests::real_pair_without_helpers_retains_ordinary_custody_but_refuses_native_worker";
        let actor = std::env::var(ACTOR).ok();
        if actor.is_none() {
            // Trust: Cargo adds its own loader search path for libtest. Observe
            // the compiler pair in an isolated actual native test process;
            // production still refuses every foreign compiler loader input.
            for mode in ["clean", "foreign-loader"] {
                let mut command = std::process::Command::new(std::env::current_exe().unwrap());
                command.args(["--exact", NAME, "--include-ignored"]);
                command.env(ACTOR, mode);
                for (key, _) in std::env::vars_os() {
                    if key.as_encoded_bytes().starts_with(b"DYLD_")
                        || key.as_encoded_bytes().starts_with(b"LD_")
                    {
                        command.env_remove(key);
                    }
                }
                if mode == "foreign-loader" {
                    command.env("LD_LIBRARY_PATH", "/foreign-compiler-loader-input");
                }
                let output = command.output().unwrap();
                assert!(
                    output.status.success(),
                    "real compiler pair actor {mode}: {output:?}"
                );
                assert!(
                    String::from_utf8_lossy(&output.stdout)
                        .contains("1 passed; 0 failed; 0 ignored;")
                );
            }
            return;
        }
        assert!(matches!(actor.as_deref(), Some("clean" | "foreign-loader")));

        let bin =
            PathBuf::from(std::env::var_os("TARGO_TEST_REAL_PAIR_BIN").expect("real pair bin"));
        let profile = PathBuf::from(
            std::env::var_os("TARGO_TEST_REAL_PAIR_PROFILE").expect("producer profile DATA"),
        );
        let encoded = std::fs::read_to_string(profile).unwrap();
        let root = bin.parent().unwrap();
        assert!(
            !root.join("bin/rust-lld").exists(),
            "retain the real absent-helper case"
        );
        assert!(
            !root.join("bin/dsymutil").exists(),
            "retain the real absent-helper case"
        );
        let compiler = bin.join("trustc");
        let gctx = targo::util::GlobalContext::default().unwrap();
        if actor.as_deref() == Some("foreign-loader") {
            let Err(error) = hold_selected_compiler(
                &gctx,
                &bin,
                &compiler,
                &encoded,
                Instant::now() + Duration::from_secs(30),
            ) else {
                panic!("foreign compiler loader input accepted");
            };
            assert!(
                error.to_string().contains("unsupported loader override"),
                "{error:#}"
            );
            return;
        }
        // A longer test observation budget removes disk-cache timing from the
        // semantic regression. Production keeps its original two-second bound.
        let held = hold_selected_compiler(
            &gctx,
            &bin,
            &compiler,
            &encoded,
            Instant::now() + Duration::from_secs(30),
        )
        .unwrap();
        held.validate(Instant::now() + Duration::from_secs(30))
            .unwrap();
        let Err(error) = require_native_helpers(held) else {
            panic!("native worker accepted a provider without its required helpers");
        };
        assert!(error.is::<NativeHelperRefusal>(), "{error:#}");
        assert!(native_refusal(&error));
        assert!(error.to_string().contains("rust-lld"));

        let mut wrong: serde_json::Value = serde_json::from_str(&encoded).unwrap();
        wrong["executable"]["sha256"] = "0".repeat(64).into();
        assert!(
            hold_selected_compiler(
                &gctx,
                &bin,
                &compiler,
                &wrong.to_string(),
                Instant::now() + Duration::from_secs(30)
            )
            .is_err()
        );
        assert!(
            hold_selected_compiler(
                &gctx,
                &root.join("lib"),
                &compiler,
                &encoded,
                Instant::now() + Duration::from_secs(30)
            )
            .is_err()
        );
    }

    #[test]
    fn admission_query_preserves_the_complete_native_test_selection() {
        for words in [
            vec!["--unverified", "test", "--lib"],
            vec!["--unverified", "test", "--test=native", "--", "filter"],
            vec!["--unverified", "test", "--no-run"],
            vec!["--resource-worker-v2", "--unverified", "test", "--tests"],
        ] {
            assert!(invocation_supported(
                &words.into_iter().map(OsString::from).collect::<Vec<_>>()
            ));
        }
        for words in [
            vec!["--unverified", "test"],
            vec!["--unverified", "test", "--doc", "--lib"],
            vec!["--unverified", "test", "--", "--lib"],
            vec!["trust", "test", "--lib"],
            vec!["--unverified", "bench", "--lib"],
            vec![
                "--resource-worker-v2",
                "--unverified",
                "test",
                "--resource-worker-v2",
                "--lib",
            ],
        ] {
            assert!(!invocation_supported(
                &words.into_iter().map(OsString::from).collect::<Vec<_>>()
            ));
        }
    }
}
