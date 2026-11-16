use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::{env, fs};

use build_helper::fs::{ignore_not_found, recursive_remove};
use camino::{Utf8Path, Utf8PathBuf};

use super::{ProcRes, TestCx, disable_error_reporting};
use crate::common::{
    Config, TRUST_VANILLA_ANNOUNCED_ENV, TRUST_VANILLA_RUSTC_FLAG, TestPaths, TestSuite,
    TrustVerificationLane,
};
use crate::util::{ArgFileCommand, copy_dir_all, dylib_env_var};

/// Trust: the real driver the `-Ztrust-verify=off` wrapper execs. Transport only.
const TRUST_OFF_REAL_RUSTC_ENV: &str = "__COMPILETEST_TRUST_OFF_REAL_RUSTC";
/// Trust: set on `--trust-vanilla` only; recipes read it as that lane's signal.
const TRUST_VANILLA_REAL_RUSTC_ENV: &str = "__COMPILETEST_TRUST_VANILLA_REAL_RUSTC";

/// Trust: what a recipe's `RUSTC` is.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum RecipeRustc {
    /// The real driver at its own default.
    Real,
    /// The wrapper that prepends `-Ztrust-verify=off`.
    Isolated,
    /// `Isolated`, plus the vanilla lane's signal.
    Vanilla,
}

/// Trust: the run-make half of `TrustVerificationLane::IsolatedOff`. On the
/// default lane an INHERITED recipe's compiles are isolated like every other
/// inherited test's, while Trust's own recipes keep the real driver (they state
/// `-Ztrust-verify=on|off` themselves, and some read `RUSTC`'s sysroot). The
/// verified lane and a non-Trust driver get the real driver unchanged.
fn recipe_rustc(config: &Config, testpaths: &TestPaths) -> RecipeRustc {
    match config.trust_verification_lane() {
        TrustVerificationLane::IsolatedOff if config.trust_vanilla() => RecipeRustc::Vanilla,
        TrustVerificationLane::IsolatedOff if !is_trust_run_make_test(testpaths) => {
            RecipeRustc::Isolated
        }
        TrustVerificationLane::IsolatedOff
        | TrustVerificationLane::Verified
        | TrustVerificationLane::Unsupported => RecipeRustc::Real,
    }
}

/// Trust: Trust's own run-make tests are the top-level `trust-*` / `trustc-*`
/// directories.
fn is_trust_run_make_test(testpaths: &TestPaths) -> bool {
    testpaths
        .relative_dir
        .iter()
        .next()
        .or_else(|| testpaths.file.file_name())
        .is_some_and(|top| top.starts_with("trust"))
}

impl TestCx<'_> {
    pub(super) fn run_rmake_test(&self) {
        // For `run-make`, we need to perform 2 steps to build and run a `run-make` recipe
        // (`rmake.rs`) to run the actual tests. The support library is already built as a tool rust
        // library. Bootstrap supplies its exact Cargo artifact paths.
        //
        // 1. We need to build the recipe `rmake.rs` as a binary and link in the `run_make_support`
        //    library.
        // 2. We need to run the recipe binary.

        let host_build_root = self.config.build_root.join(&self.config.host);

        // We construct the following directory tree for each rmake.rs test:
        // ```
        // <base_dir>/
        //     rmake.exe
        //     rmake_out/
        // ```
        // having the recipe executable separate from the output artifacts directory allows the
        // recipes to `remove_dir_all($TMPDIR)` without running into issues related trying to remove
        // a currently running executable because the recipe executable is not under the
        // `rmake_out/` directory.
        let base_dir = self.output_base_dir();
        ignore_not_found(|| recursive_remove(&base_dir)).unwrap();

        let rmake_out_dir = base_dir.join("rmake_out");
        fs::create_dir_all(&rmake_out_dir).unwrap();

        // Copy all input files (apart from rmake.rs) to the temporary directory,
        // so that the input directory structure from `tests/run-make/<test>` is mirrored
        // to the `rmake_out` directory.
        for entry in walkdir::WalkDir::new(&self.testpaths.file).min_depth(1) {
            let entry = entry.unwrap();
            let path = entry.path();
            let path = <&Utf8Path>::try_from(path).unwrap();
            if path.file_name().is_some_and(|s| s != "rmake.rs") {
                let target = rmake_out_dir.join(path.strip_prefix(&self.testpaths.file).unwrap());
                if path.is_dir() {
                    copy_dir_all(&path, &target).unwrap();
                } else {
                    fs::copy(path.as_std_path(), target).unwrap();
                }
            }
        }

        let support_lib_rlib_path = self
            .config
            .run_make_support_rlib
            .as_ref()
            .expect("run-make-support .rlib has to be passed for run-make tests");
        let support_lib_rmeta_path = self.config.run_make_support_rmeta.as_ref();

        // Trust: the support library and its dependencies must come from one Cargo
        // producer. Reconstructing a cache name here mixed current-Cargo dependencies
        // with the seed-built support library after Bootstrap split those caches.
        let support_lib_dependency_dirs = run_make_support_dependency_dirs(
            support_lib_rlib_path,
            support_lib_rmeta_path.map(|p| p.as_path()),
            &self.config.host,
        )
        .unwrap_or_else(|error| self.fatal(&error));

        // To compile the recipe with rustc, we need to provide suitable dynamic library search
        // paths to rustc. This includes both:
        // 1. The "base" dylib search paths that was provided to compiletest, e.g. `LD_LIBRARY_PATH`
        //    on some linux distros.
        // 2. Specific library paths in `self.config.compile_lib_path` needed for running rustc.

        let base_dylib_search_paths = Vec::from_iter(
            env::split_paths(&env::var(dylib_env_var()).unwrap())
                .map(|p| Utf8PathBuf::try_from(p).expect("dylib env var contains non-UTF8 paths")),
        );

        // Calculate the paths of the recipe binary. As previously discussed, this is placed at
        // `<base_dir>/<bin_name>` with `bin_name` being `rmake` or `rmake.exe` depending on
        // platform.
        let recipe_bin = {
            let mut p = base_dir.join("rmake");
            p.set_extension(env::consts::EXE_EXTENSION);
            p
        };

        let out_dirs_to_args = |paths: Vec<PathBuf>| {
            paths.into_iter().map(|p| format!("-Ldependency={}", p.display())).collect::<Vec<_>>()
        };

        // run-make-support and run-make tests are compiled using the stage0 compiler
        // If the stage is 0, then the compiler that we test (either bootstrap or an explicitly
        // set compiler) is the one that actually compiled run-make-support.
        let stage0_rustc = self
            .config
            .stage0_rustc_path
            .as_ref()
            .expect("stage0 rustc is required to run run-make tests");
        let mut rustc = ArgFileCommand::new(&stage0_rustc);
        rustc
            // `rmake.rs` **must** be buildable by a stable compiler, it may not use *any* unstable
            // library or compiler features. Here, we force the stage 0 rustc to consider itself as
            // a stable-channel compiler via `RUSTC_BOOTSTRAP=-1` to prevent *any* unstable
            // library/compiler usages, even if stage 0 rustc is *actually* a nightly rustc.
            .env("RUSTC_BOOTSTRAP", "-1")
            // Trust: the recipe is HARNESS code, not a verification subject. When stage0 is
            // a batteries-on Trust compiler — the sanctioned atpkg-pack stage0 — its own
            // Level-0 obligations on ordinary recipe code fail closed under strict policy,
            // and the whole run-make mode aborts at recipe-build before a single subject
            // compiles (measured: a stock control fails identically). bootstrap.py only
            // plants this env when stage0 does NOT understand the current flag, so the
            // modern stage0 path is exactly the one that verifies the recipe. Disable
            // verification for the RECIPE COMPILE ONLY via the version-invariant nested-
            // process transport (`rustc_driver_impl::apply_trust_verify_override`, a
            // post-parse override): a stock stage0 ignores the env, and it bypasses the
            // `RUSTC_BOOTSTRAP=-1` stable `-Z` gate that an argv `-Ztrust-verify=off`
            // would depend on. The recipe RUN below is a separate Command and drives the
            // subject compilations with their own explicit `-Ztrust-verify=on|off`, so
            // nothing a test asserts about verification is touched.
            .env("TRUST_NO_VERIFY", "1")
            .arg("-o")
            .arg(&recipe_bin)
            // Specify library search paths for `run_make_support`.
            .args(out_dirs_to_args(support_lib_dependency_dirs))
            // Provide `run_make_support` as extern prelude, so test writers don't need to write
            // `extern run_make_support;`.
            .arg("--extern")
            .arg(format!("run_make_support={}", &support_lib_rlib_path))
            .arg("--edition=2024")
            .arg(&self.testpaths.file.join("rmake.rs"))
            .arg("-Cprefer-dynamic");

        if let Some(support_lib_rmeta_path) = support_lib_rmeta_path {
            rustc.arg("--extern").arg(format!("run_make_support={}", &support_lib_rmeta_path));
        }

        // In test code we want to be very pedantic about values being silently discarded that are
        // annotated with `#[must_use]`.
        rustc.arg("-Dunused_must_use");

        // Now run rustc to build the recipe.
        let res = self.run_command_to_procres(rustc);
        if !res.status.success() {
            self.fatal_proc_rec("run-make test failed: could not build `rmake.rs` recipe", &res);
        }

        // To actually run the recipe, we have to provide the recipe with a bunch of information
        // provided through env vars.
        // Trust: a recipe spawns its OWN compilations through `RUSTC`, so the
        // lane has to reach it through this path or the recipe silently opts
        // out of whatever lane the run claims.
        //   vanilla  -- every recipe gets the `-Ztrust-verify=off` wrapper.
        //   default  -- inherited recipes get the same wrapper; Trust's own
        //               (`recipe_rustc`) get the real driver.
        //   verified -- the real BRANDED driver with NO injected flag, so
        //               recipe compiles land on the compiler's own shipping
        //               default (`-Ztrust-verify=on`, `-Ztrust-policy=strict`),
        //               which is exactly what this lane exists to witness. A
        //               wrapper here would measure the wrapper, not the default.
        let recipe_rustc_kind = recipe_rustc(self.config, self.testpaths);
        let recipe_rustc = match recipe_rustc_kind {
            RecipeRustc::Real => self.config.rustc_path.clone(),
            RecipeRustc::Isolated | RecipeRustc::Vanilla => {
                write_trust_off_rustc_wrapper(&base_dir)
            }
        };

        // Compute dynamic library search paths for recipes.
        // These dylib directories are needed to **execute the recipe**.
        let recipe_dylib_search_paths = {
            let mut paths = base_dylib_search_paths.clone();
            paths.push(
                stage0_rustc
                    .parent()
                    .unwrap()
                    .parent()
                    .unwrap()
                    .join("lib")
                    .join("rustlib")
                    .join(&self.config.host)
                    .join("lib"),
            );
            paths
        };

        let mut cmd = Command::new(&recipe_bin);
        cmd.current_dir(&rmake_out_dir)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            // Provide the target-specific env var that is used to record dylib search paths. For
            // example, this could be `LD_LIBRARY_PATH` on some linux distros but `PATH` on Windows.
            .env("LD_LIB_PATH_ENVVAR", dylib_env_var())
            // Provide the dylib search paths.
            // This is required to run the **recipe** itself.
            .env(dylib_env_var(), &env::join_paths(recipe_dylib_search_paths).unwrap())
            // Provide the directory to libraries that are needed to run the *compiler* invoked
            // by the recipe.
            .env("HOST_RUSTC_DYLIB_PATH", &self.config.host_compile_lib_path)
            // Provide the directory to libraries that might be needed to run binaries created
            // by a compiler invoked by the recipe.
            .env("TARGET_EXE_DYLIB_PATH", &self.config.target_run_lib_path)
            // Provide the target.
            .env("TARGET", &self.config.target)
            // Some tests unfortunately still need Python, so provide path to a Python interpreter.
            .env("PYTHON", &self.config.python)
            // Provide path to sources root.
            .env("SOURCE_ROOT", &self.config.src_root)
            // Path to the host build directory.
            .env("BUILD_ROOT", &host_build_root)
            // Provide path to stage-corresponding rustc.
            .env("RUSTC", &recipe_rustc)
            // Provide which LLVM components are available (e.g. which LLVM components are provided
            // through a specific CI runner).
            .env("LLVM_COMPONENTS", &self.config.llvm_components);

        // Trust: the recipe RUN is where a run-make test's subject compiles
        // happen, so it gets the same unconditional strip of an INHERITED
        // `TRUST_NO_VERIFY` that `configure_trust_verification_isolation` gives
        // every compile compiletest issues itself (see the reasoning there: the
        // driver applies the variable as a post-parse override, so it beats a
        // recipe's explicit `-Ztrust-verify=on`). The recipe COMPILE above sets it
        // on purpose and is a different command. Measured 2026-09-27 under
        // `x.py test --stage 1 tests/run-make/...` on a seed that makes
        // bootstrap plant the variable: trust-assumption-rows,
        // trustc-verifier-options, trust-temporal-carry,
        // trust-native-bundle-obligation-site and
        // trust-duplicate-crate-call-identity failed with verification OFF ("0
        // assumption:coroutine rows", "command unexpectedly succeeded",
        // "-Ztrust-dump=mir:<dir> ... require batteries-on Trust verification")
        // while the same recipe binaries passed when run with the same `RUSTC`
        // outside x.py, and failed identically with `TRUST_NO_VERIFY=1` added.
        // A recipe that wants vanilla compiles spells `-Ztrust-verify=off`, and
        // the vanilla lane's wrapper injects it.
        cmd.env_remove("TRUST_NO_VERIFY");

        // Trust (loud-when-off): run-make is a managed harness lane; its
        // isolation wrapper and any per-recipe `-Ztrust-verify=off` compile are
        // announced policy, so quiet the compiler's once-per-crate vanilla
        // note. A recipe that wants to observe the note removes this variable
        // from its own command.
        //
        // NOT on the verified lane: there, `-Ztrust-verify=off` is never
        // announced policy, so a recipe that reaches it is a FINDING and the
        // note must stay loud. (Every other lane is byte-identical to before.)
        if !self.config.trust_verified() {
            cmd.env(TRUST_VANILLA_ANNOUNCED_ENV, "1");
        }

        match recipe_rustc_kind {
            RecipeRustc::Real => {}
            RecipeRustc::Isolated => {
                cmd.env(TRUST_OFF_REAL_RUSTC_ENV, &self.config.rustc_path);
            }
            RecipeRustc::Vanilla => {
                cmd.env(TRUST_OFF_REAL_RUSTC_ENV, &self.config.rustc_path)
                    .env(TRUST_VANILLA_REAL_RUSTC_ENV, &self.config.rustc_path);
            }
        }

        if let Some(codegen_backend) = &self.config.override_codegen_backend {
            // In case it's a different codegen backend than LLVM.
            cmd.env("RUSTC_CODEGEN_BACKEND", codegen_backend.as_str());
        }

        // The `run-make-cargo` and `build-std` suites need an in-tree `cargo`, `run-make` does not.
        if matches!(self.config.suite, TestSuite::RunMakeCargo | TestSuite::BuildStd) {
            cmd.env(
                "CARGO",
                self.config.cargo_path.as_ref().expect("cargo must be built and made available"),
            );
        }

        if let Some(ref rustdoc) = self.config.rustdoc_path {
            cmd.env("RUSTDOC", rustdoc);
        }

        if let Some(ref node) = self.config.nodejs {
            cmd.env("NODE", node);
        }

        if let Some(ref linker) = self.config.target_linker {
            cmd.env("RUSTC_LINKER", linker);
        }

        if let Some(ref clang) = self.config.run_clang_based_tests_with {
            cmd.env("CLANG", clang);
        }

        if let Some(ref filecheck) = self.config.llvm_filecheck {
            cmd.env("LLVM_FILECHECK", filecheck);
        }

        if let Some(ref llvm_bin_dir) = self.config.llvm_bin_dir {
            cmd.env("LLVM_BIN_DIR", llvm_bin_dir);
        }

        if let Some(ref remote_test_client) = self.config.remote_test_client {
            cmd.env("REMOTE_TEST_CLIENT", remote_test_client);
        }

        if let Some(runner) = &self.config.runner {
            cmd.env("RUNNER", runner);
        }

        // Guard against externally-set env vars.
        // Set env var to enable verbose output for successful commands.
        // Only set when --verbose-run-make-subprocess-output is passed.
        cmd.env_remove("__RMAKE_VERBOSE_SUBPROCESS_OUTPUT");
        if self.config.verbose_run_make_subprocess_output {
            cmd.env("__RMAKE_VERBOSE_SUBPROCESS_OUTPUT", "1");
        }

        cmd.env_remove("__RUSTC_DEBUG_ASSERTIONS_ENABLED");
        if self.config.with_rustc_debug_assertions {
            // Used for `run_make_support::env::rustc_debug_assertions_enabled`.
            cmd.env("__RUSTC_DEBUG_ASSERTIONS_ENABLED", "1");
        }

        cmd.env_remove("__STD_DEBUG_ASSERTIONS_ENABLED");
        if self.config.with_std_debug_assertions {
            // Used for `run_make_support::env::std_debug_assertions_enabled`.
            cmd.env("__STD_DEBUG_ASSERTIONS_ENABLED", "1");
        }

        cmd.env_remove("__STD_REMAP_DEBUGINFO_ENABLED");
        if self.config.with_std_remap_debuginfo {
            // Used for `run_make_support::env::std_remap_debuginfo_enabled`.
            cmd.env("__STD_REMAP_DEBUGINFO_ENABLED", "1");
        }

        // Used for `run_make_support::env::jobs`.
        cmd.env("__BOOTSTRAP_JOBS", self.config.jobs.to_string());

        // We don't want RUSTFLAGS set from the outside to interfere with
        // compiler flags set in the test cases:
        cmd.env_remove("RUSTFLAGS");

        // Use dynamic musl for tests because static doesn't allow creating dylibs
        if self.config.host.contains("musl") {
            cmd.env("RUSTFLAGS", "-Ctarget-feature=-crt-static").env("IS_MUSL_HOST", "1");
        }

        if self.config.bless {
            // If we're running in `--bless` mode, set an environment variable to tell
            // `run_make_support` to bless snapshot files instead of checking them.
            //
            // The value is this test's source directory, because the support code
            // will need that path in order to bless the _original_ snapshot files,
            // not the copies in `rmake_out`.
            // (See <https://github.com/rust-lang/rust/issues/129038>.)
            cmd.env("RUSTC_BLESS_TEST", &self.testpaths.file);
        }

        if self.config.target.contains("msvc") && !self.config.cc.is_empty() {
            // We need to pass a path to `lib.exe`, so assume that `cc` is `cl.exe`
            // and that `lib.exe` lives next to it.
            let lib = Utf8Path::new(&self.config.cc).parent().unwrap().join("lib.exe");

            // MSYS doesn't like passing flags of the form `/foo` as it thinks it's
            // a path and instead passes `C:\msys64\foo`, so convert all
            // `/`-arguments to MSVC here to `-` arguments.
            let cflags = self
                .config
                .cflags
                .split(' ')
                .map(|s| s.replace("/", "-"))
                .collect::<Vec<_>>()
                .join(" ");
            let cxxflags = self
                .config
                .cxxflags
                .split(' ')
                .map(|s| s.replace("/", "-"))
                .collect::<Vec<_>>()
                .join(" ");

            cmd.env("IS_MSVC", "1")
                .env("IS_WINDOWS", "1")
                .env("MSVC_LIB", format!("'{}' -nologo", lib))
                .env("MSVC_LIB_PATH", &lib)
                // Note: we diverge from legacy run_make and don't lump `CC` the compiler and
                // default flags together.
                .env("CC_DEFAULT_FLAGS", &cflags)
                .env("CC", &self.config.cc)
                .env("CXX_DEFAULT_FLAGS", &cxxflags)
                .env("CXX", &self.config.cxx);
        } else {
            cmd.env("CC_DEFAULT_FLAGS", &self.config.cflags)
                .env("CC", &self.config.cc)
                .env("CXX_DEFAULT_FLAGS", &self.config.cxxflags)
                .env("CXX", &self.config.cxx)
                .env("AR", &self.config.ar);

            if self.config.target.contains("windows") {
                cmd.env("IS_WINDOWS", "1");
            }
        }

        let (Output { stdout, stderr, status }, truncated) = disable_error_reporting(|| {
            crate::case_scheduler::run(&mut cmd, |child| self.read2_abbreviated(child))
        })
        .expect("failed to execute `rmake`");
        let stdout = String::from_utf8_lossy(&stdout).into_owned();
        let stderr = String::from_utf8_lossy(&stderr).into_owned();
        // This conditions on `status.success()` so we don't print output twice on error.
        // NOTE: this code is called from an executor thread, so it's hidden by default unless --no-capture is passed.
        self.dump_output(status.success(), &cmd.get_program().to_string_lossy(), &stdout, &stderr);
        if !status.success() {
            let res = ProcRes { status, stdout, stderr, truncated, cmdline: format!("{:?}", cmd) };
            self.fatal_proc_rec("rmake recipe failed to complete", &res);
        }
    }
}

// Trust: accept Cargo's uplifted, legacy deps, and new build-unit artifact
// locations. rlib and separate rmeta must identify the same producer profile;
// neither a host name nor a cache-domain name supplied elsewhere can replace it.
fn run_make_support_profile_dir(
    artifact: &Utf8Path,
    extension: &str,
) -> Result<Utf8PathBuf, String> {
    let stem = artifact.file_stem().unwrap_or_default();
    if artifact.extension() != Some(extension)
        || !(stem == "librun_make_support"
            || stem.strip_prefix("librun_make_support-").is_some_and(|hash| !hash.is_empty()))
    {
        return Err(format!("invalid run-make-support .{extension} artifact: {artifact}"));
    }
    let parent = artifact.parent().ok_or_else(|| format!("no artifact directory: {artifact}"))?;
    let profile = match parent.file_name() {
        Some("deps") => parent.parent(),
        Some("out") => parent
            .parent()
            .and_then(Utf8Path::parent)
            .and_then(Utf8Path::parent)
            .filter(|build| build.file_name() == Some("build"))
            .and_then(Utf8Path::parent),
        _ => Some(parent),
    };
    profile
        .filter(|profile| profile.file_name().is_some())
        .map(Utf8Path::to_path_buf)
        .ok_or_else(|| format!("unrecognized run-make-support artifact layout: {artifact}"))
}

// Trust: keep the host-qualified and unqualified dependency halves in the
// selected producer only. In the new layout Rust libraries and build scripts
// both live under build/<package>/<unit>/out, so those directories matter too.
fn run_make_support_dependency_dirs(
    rlib: &Utf8Path,
    rmeta: Option<&Utf8Path>,
    host: &str,
) -> Result<Vec<PathBuf>, String> {
    let profile = run_make_support_profile_dir(rlib, "rlib")?;
    if let Some(rmeta) = rmeta {
        let metadata_profile = run_make_support_profile_dir(rmeta, "rmeta")?;
        if metadata_profile != profile {
            return Err(format!(
                "run-make-support rlib and rmeta use different Cargo producer profiles: \
                 {rlib} and {rmeta}"
            ));
        }
        if let Some(rlib_hash) = rlib.file_stem().unwrap().strip_prefix("librun_make_support-")
            && let Some(rmeta_hash) =
                rmeta.file_stem().unwrap().strip_prefix("librun_make_support-")
            && rlib_hash != rmeta_hash
        {
            return Err(format!(
                "run-make-support rlib and rmeta use different Cargo artifact hashes: \
                 {rlib} and {rmeta}"
            ));
        }
    }
    let mut profiles = vec![profile.clone()];
    if let Some(target) = profile.parent()
        && target.file_name() == Some(host)
        && let Some(root) = target.parent()
    {
        profiles.push(root.join(profile.file_name().expect("profile directory has a name")));
    }
    let mut paths = profiles.iter().map(|p| p.join("deps").into_std_path_buf()).collect::<Vec<_>>();
    for profile in profiles {
        let build = profile.join("build");
        paths.extend(discover_out_dirs(build.as_std_path()).map_err(|error| {
            format!("could not read support producer directory {build}: {error}")
        })?);
    }
    Ok(paths)
}

/// Trust: handle both build/<package-hash>/out and build/<package>/<unit>/out.
/// Missing build-script directories are normal for graphs without build scripts.
fn discover_out_dirs(dir: &Path) -> std::io::Result<Vec<PathBuf>> {
    fn output_is_directory(path: &Path) -> std::io::Result<bool> {
        match fs::metadata(path) {
            Ok(metadata) => Ok(metadata.is_dir()),
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(false),
            Err(error) => Err(error),
        }
    }

    fn directories(path: &Path) -> std::io::Result<Vec<PathBuf>> {
        let entries = match path.read_dir() {
            Ok(entries) => entries,
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(vec![]),
            Err(error) => return Err(error),
        };
        let mut dirs = vec![];
        for entry in entries {
            let path = entry?.path();
            if fs::metadata(&path)?.is_dir() {
                dirs.push(path);
            }
        }
        dirs.sort();
        Ok(dirs)
    }

    let mut outs = vec![];
    for package in directories(dir)? {
        let legacy_out = package.join("out");
        if output_is_directory(&legacy_out)? {
            outs.push(legacy_out);
        }
        for unit in directories(&package)? {
            if unit.file_name().is_some_and(|name| name == "out") {
                continue;
            }
            let out = unit.join("out");
            if output_is_directory(&out)? {
                outs.push(out);
            }
        }
    }
    outs.sort();
    outs.dedup();
    Ok(outs)
}

fn write_trust_off_rustc_wrapper(base_dir: &Utf8Path) -> Utf8PathBuf {
    let wrapper = trust_off_rustc_wrapper_path(base_dir);
    fs::write(&wrapper, trust_off_rustc_wrapper_script()).unwrap();

    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;

        let mut permissions = fs::metadata(&wrapper).unwrap().permissions();
        permissions.set_mode(0o755);
        fs::set_permissions(&wrapper, permissions).unwrap();
    }

    wrapper
}

/// Trust: keep this file name. `rustc_interface::util::rustc_path` accepts it
/// from `RUSTC`, which is how rustdoc's doctest compiles reach the wrapper too.
fn trust_off_rustc_wrapper_path(base_dir: &Utf8Path) -> Utf8PathBuf {
    let wrapper_name =
        if cfg!(windows) { "rustc-trust-vanilla.cmd" } else { "rustc-trust-vanilla" };
    base_dir.join(wrapper_name)
}

fn trust_off_rustc_wrapper_script() -> String {
    if cfg!(windows) {
        format!(
            "@echo off\r\nif \"%~1\"==\"\" (\r\n    \"%{}%\"\r\n) else (\r\n    \"%{}%\" {} %*\r\n)\r\nexit /b %ERRORLEVEL%\r\n",
            TRUST_OFF_REAL_RUSTC_ENV, TRUST_OFF_REAL_RUSTC_ENV, TRUST_VANILLA_RUSTC_FLAG
        )
    } else {
        format!(
            "#!/bin/sh\nif [ \"$#\" -eq 0 ]; then\n    exec \"${{{}}}\"\nelse\n    exec \"${{{}}}\" {} \"$@\"\nfi\n",
            TRUST_OFF_REAL_RUSTC_ENV, TRUST_OFF_REAL_RUSTC_ENV, TRUST_VANILLA_RUSTC_FLAG
        )
    }
}

#[cfg(test)]
mod tests;
