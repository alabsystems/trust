// Trust modifications Copyright 2026 Andrew Yates.
// Derived from cmake-rs 0.1.54; upstream MIT/Apache-2.0 attribution is retained.
//! A build dependency for running `cmake` to build a native library
//!
//! This crate provides some necessary boilerplate and shim support for running
//! the system `cmake` command to build a native library. It will add
//! appropriate cflags for building code to link into Rust, handle cross
//! compilation, and use the necessary generator for the platform being
//! targeted.
//!
//! The builder-style configuration allows for various variables and such to be
//! passed down into the build as well.
//!
//! ## Installation
//!
//! Add this to your `Cargo.toml`:
//!
//! ```toml
//! [build-dependencies]
//! cmake = "0.1"
//! ```
//!
//! ## Examples
//!
//! ```no_run
//! use cmake;
//!
//! // Builds the project in the directory located in `libfoo`, installing it
//! // into $OUT_DIR
//! let dst = cmake::build("libfoo");
//!
//! println!("cargo:rustc-link-search=native={}", dst.display());
//! println!("cargo:rustc-link-lib=static=foo");
//! ```
//!
//! ```no_run
//! use cmake::Config;
//!
//! let dst = Config::new("libfoo")
//!                  .define("FOO", "BAR")
//!                  .cflag("-foo")
//!                  .build();
//! println!("cargo:rustc-link-search=native={}", dst.display());
//! println!("cargo:rustc-link-lib=static=foo");
//! ```

#![deny(missing_docs)]

use std::collections::HashMap;
use std::env;
use std::ffi::{OsStr, OsString};
use std::fs::{self, File};
use std::io::ErrorKind;
use std::io::prelude::*;
use std::path::{Path, PathBuf};
use std::process::Command;

/// Builder style configuration for a pending CMake build.
#[derive(Clone)]
pub struct Config {
    path: PathBuf,
    generator: Option<OsString>,
    generator_toolset: Option<OsString>,
    cflags: OsString,
    cxxflags: OsString,
    asmflags: OsString,
    defines: Vec<(OsString, OsString)>,
    deps: Vec<String>,
    input_paths: Vec<(usize, PathBuf)>,
    input_programs: Vec<(usize, Vec<OsString>)>,
    execution_defines: Vec<usize>,
    selected_paths: Vec<PathBuf>,
    cleanup_opaque: bool,
    target: Option<String>,
    host: Option<String>,
    out_dir: Option<PathBuf>,
    profile: Option<String>,
    configure_args: Vec<OsString>,
    build_args: Vec<OsString>,
    cmake_target: Option<String>,
    env: Vec<(OsString, OsString)>,
    static_crt: Option<bool>,
    uses_cxx11: bool,
    always_configure: bool,
    no_build_target: bool,
    no_default_flags: bool,
    verbose_cmake: bool,
    verbose_make: bool,
    pic: Option<bool>,
    c_cfg: Option<cc::Build>,
    cxx_cfg: Option<cc::Build>,
    env_cache: HashMap<String, Option<OsString>>,
    cache_roots: Vec<PathBuf>,
}

/// Builds the native library rooted at `path` with the default cmake options.
/// This will return the directory in which the library was installed.
///
/// # Examples
///
/// ```no_run
/// use cmake;
///
/// // Builds the project in the directory located in `libfoo`, installing it
/// // into $OUT_DIR
/// let dst = cmake::build("libfoo");
///
/// println!("cargo:rustc-link-search=native={}", dst.display());
/// println!("cargo:rustc-link-lib=static=foo");
/// ```
///
pub fn build<P: AsRef<Path>>(path: P) -> PathBuf {
    Config::new(path.as_ref()).build()
}

impl Config {
    /// Return explicitly set profile or infer `CMAKE_BUILD_TYPE` from Rust's compilation profile.
    ///
    /// * if `opt-level=0` then `CMAKE_BUILD_TYPE=Debug`,
    /// * if `opt-level={1,2,3}` and:
    ///   * `debug=false` then `CMAKE_BUILD_TYPE=Release`
    ///   * otherwise `CMAKE_BUILD_TYPE=RelWithDebInfo`
    /// * if `opt-level={s,z}` then `CMAKE_BUILD_TYPE=MinSizeRel`
    pub fn get_profile(&self) -> &str {
        if let Some(profile) = self.profile.as_ref() {
            profile
        } else {
            // Determine Rust's profile, optimization level, and debug info:
            #[derive(PartialEq)]
            enum RustProfile {
                Debug,
                Release,
            }
            #[derive(PartialEq, Debug)]
            enum OptLevel {
                Debug,
                Release,
                Size,
            }

            let rust_profile = match &getenv_unwrap("PROFILE")[..] {
                "debug" => RustProfile::Debug,
                "release" | "bench" => RustProfile::Release,
                unknown => {
                    eprintln!(
                        "Warning: unknown Rust profile={}; defaulting to a release build.",
                        unknown
                    );
                    RustProfile::Release
                }
            };

            let opt_level = match &getenv_unwrap("OPT_LEVEL")[..] {
                "0" => OptLevel::Debug,
                "1" | "2" | "3" => OptLevel::Release,
                "s" | "z" => OptLevel::Size,
                unknown => {
                    let default_opt_level = match rust_profile {
                        RustProfile::Debug => OptLevel::Debug,
                        RustProfile::Release => OptLevel::Release,
                    };
                    eprintln!(
                        "Warning: unknown opt-level={}; defaulting to a {:?} build.",
                        unknown, default_opt_level
                    );
                    default_opt_level
                }
            };

            let debug_info: bool = match &getenv_unwrap("DEBUG")[..] {
                "false" => false,
                "true" => true,
                unknown => {
                    eprintln!("Warning: unknown debug={}; defaulting to `true`.", unknown);
                    true
                }
            };

            match (opt_level, debug_info) {
                (OptLevel::Debug, _) => "Debug",
                (OptLevel::Release, false) => "Release",
                (OptLevel::Release, true) => "RelWithDebInfo",
                (OptLevel::Size, _) => "MinSizeRel",
            }
        }
    }

    /// Creates a new blank set of configuration to build the project specified
    /// at the path `path`.
    pub fn new<P: AsRef<Path>>(path: P) -> Config {
        Config {
            path: env::current_dir().unwrap().join(path),
            generator: None,
            generator_toolset: None,
            no_default_flags: false,
            cflags: OsString::new(),
            cxxflags: OsString::new(),
            asmflags: OsString::new(),
            defines: Vec::new(),
            deps: Vec::new(),
            input_paths: Vec::new(),
            input_programs: Vec::new(),
            execution_defines: Vec::new(),
            selected_paths: Vec::new(),
            cleanup_opaque: false,
            profile: None,
            out_dir: None,
            target: None,
            host: None,
            configure_args: Vec::new(),
            build_args: Vec::new(),
            cmake_target: None,
            env: Vec::new(),
            static_crt: None,
            uses_cxx11: false,
            always_configure: true,
            no_build_target: false,
            verbose_cmake: false,
            verbose_make: false,
            pic: None,
            c_cfg: None,
            cxx_cfg: None,
            env_cache: HashMap::new(),
            cache_roots: Vec::new(),
        }
    }

    /// Writes the directory `root` as a token wherever the request key
    /// ([`Prepared::cache_inputs`]) would spell it, so two checkouts that differ only in where
    /// they lie request the same build. Only the key changes: every command still names the
    /// real paths. A root is replaced only where it stands as a whole path (the byte after it
    /// ends a path component, the byte before it does not continue one); the roots are tried
    /// in the order given.
    pub fn cache_root<P: AsRef<Path>>(&mut self, root: P) -> &mut Config {
        self.cache_roots.push(root.as_ref().to_owned());
        self
    }

    /// Sets flag for PIC. Otherwise use cc::Build platform default
    pub fn pic(&mut self, explicit_flag: bool) -> &mut Config {
        self.pic = Some(explicit_flag);
        self
    }

    /// Sets the build-tool generator (`-G`) for this compilation.
    ///
    /// If unset, this crate will use the `CMAKE_GENERATOR` environment variable
    /// if set. Otherwise, it will guess the best generator to use based on the
    /// build target.
    pub fn generator<T: AsRef<OsStr>>(&mut self, generator: T) -> &mut Config {
        self.generator = Some(generator.as_ref().to_owned());
        self
    }

    /// Sets the toolset name (-T) if supported by generator.
    /// Can be used to compile with Clang/LLVM instead of msvc when Visual Studio generator is selected.
    ///
    /// If unset, will use the default toolset of the selected generator.
    pub fn generator_toolset<T: AsRef<OsStr>>(&mut self, toolset_name: T) -> &mut Config {
        self.generator_toolset = Some(toolset_name.as_ref().to_owned());
        self
    }

    /// Adds a custom flag to pass down to the C compiler, supplementing those
    /// that this library already passes.
    pub fn cflag<P: AsRef<OsStr>>(&mut self, flag: P) -> &mut Config {
        self.cflags.push(" ");
        self.cflags.push(flag.as_ref());
        self
    }

    /// Adds a custom flag to pass down to the C++ compiler, supplementing those
    /// that this library already passes.
    pub fn cxxflag<P: AsRef<OsStr>>(&mut self, flag: P) -> &mut Config {
        self.cxxflags.push(" ");
        self.cxxflags.push(flag.as_ref());
        self
    }

    /// Adds a custom flag to pass down to the ASM compiler, supplementing those
    /// that this library already passes.
    pub fn asmflag<P: AsRef<OsStr>>(&mut self, flag: P) -> &mut Config {
        self.asmflags.push(" ");
        self.asmflags.push(flag.as_ref());
        self
    }

    /// Adds a new `-D` flag to pass to cmake during the generation step.
    pub fn define<K, V>(&mut self, k: K, v: V) -> &mut Config
    where
        K: AsRef<OsStr>,
        V: AsRef<OsStr>,
    {
        self.defines.push((k.as_ref().to_owned(), v.as_ref().to_owned()));
        self
    }

    /// Define a path consumed by the project and retain the same path as cleanup data.
    /// This does not establish the input's contents or the closure of arbitrary scripts.
    pub fn define_input_path<K: AsRef<OsStr>, P: AsRef<Path>>(
        &mut self,
        key: K,
        path: P,
    ) -> &mut Config {
        self.input_paths.push((self.defines.len(), path.as_ref().to_owned()));
        self.define(key, path.as_ref().as_os_str())
    }

    /// Bind a program definition under the same effective environment as CMake.
    /// Candidates are an explicit caller selection policy, tried in the supplied order.
    /// Only opt-in preparation binds them; ordinary mutable builds retain their request.
    pub fn define_input_program(
        &mut self,
        key: impl AsRef<OsStr>,
        candidates: &[&OsStr],
    ) -> &mut Config {
        let index = self.defines.len();
        self.define(key, candidates.first().copied().unwrap_or_else(|| OsStr::new("")));
        self.input_programs
            .push((index, candidates.iter().map(|value| value.to_os_string()).collect()));
        self
    }

    /// Emit a scheduling-only definition, excluding its exact command argument
    /// from requested configuration identity. Later ordinary definitions remain keyed.
    /// The caller must establish that the value affects scheduling only and cannot
    /// change artifact semantics; this annotation does not verify that property.
    pub fn define_execution_budget(
        &mut self,
        key: impl AsRef<OsStr>,
        value: impl AsRef<OsStr>,
    ) -> &mut Config {
        self.execution_defines.push(self.defines.len());
        self.define(key, value)
    }

    /// Retain an already selected input namespace as cleanup data, without claiming contents.
    pub fn input_path(&mut self, path: impl AsRef<Path>) -> &mut Config {
        self.selected_paths.push(path.as_ref().to_owned());
        self
    }

    /// Mark explicit consumed operands whose input namespaces cannot be established.
    /// Ordinary builds remain supported, but destructive callers must refuse cleanup.
    pub fn opaque_cleanup_inputs(&mut self) -> &mut Config {
        self.cleanup_opaque = true;
        self
    }

    /// Registers a dependency for this compilation on the native library built
    /// by Cargo previously.
    ///
    /// This registration will update the `CMAKE_PREFIX_PATH` environment
    /// variable for the [`build`][Self::build] system generation step.  The
    /// path will be updated to include the content of the environment
    /// variable `DEP_XXX_ROOT`, where `XXX` is replaced with the uppercased
    /// value of `dep` (if that variable exists).
    pub fn register_dep(&mut self, dep: &str) -> &mut Config {
        self.deps.push(dep.to_string());
        self
    }

    /// Sets the target triple for this compilation.
    ///
    /// This is automatically scraped from `$TARGET` which is set for Cargo
    /// build scripts so it's not necessary to call this from a build script.
    pub fn target(&mut self, target: &str) -> &mut Config {
        self.target = Some(target.to_string());
        self
    }

    /// Disables the cmake target option for this compilation.
    ///
    /// Note that this isn't related to the target triple passed to the compiler!
    pub fn no_build_target(&mut self, no_build_target: bool) -> &mut Config {
        self.no_build_target = no_build_target;
        self
    }

    /// Disables the generation of default compiler flags. The default compiler
    /// flags may cause conflicts in some cross compiling scenarios.
    pub fn no_default_flags(&mut self, no_default_flags: bool) -> &mut Config {
        self.no_default_flags = no_default_flags;
        self
    }

    /// Sets the host triple for this compilation.
    ///
    /// This is automatically scraped from `$HOST` which is set for Cargo
    /// build scripts so it's not necessary to call this from a build script.
    pub fn host(&mut self, host: &str) -> &mut Config {
        self.host = Some(host.to_string());
        self
    }

    /// Sets the output directory for this compilation.
    ///
    /// This is automatically scraped from `$OUT_DIR` which is set for Cargo
    /// build scripts so it's not necessary to call this from a build script.
    pub fn out_dir<P: AsRef<Path>>(&mut self, out: P) -> &mut Config {
        self.out_dir = Some(out.as_ref().to_path_buf());
        self
    }

    /// Sets the `CMAKE_BUILD_TYPE=build_type` variable.
    ///
    /// By default, this value is automatically inferred from Rust's compilation
    /// profile as follows:
    ///
    /// * if `opt-level=0` then `CMAKE_BUILD_TYPE=Debug`,
    /// * if `opt-level={1,2,3}` and:
    ///   * `debug=false` then `CMAKE_BUILD_TYPE=Release`
    ///   * otherwise `CMAKE_BUILD_TYPE=RelWithDebInfo`
    /// * if `opt-level={s,z}` then `CMAKE_BUILD_TYPE=MinSizeRel`
    pub fn profile(&mut self, profile: &str) -> &mut Config {
        self.profile = Some(profile.to_string());
        self
    }

    /// Configures whether the /MT flag or the /MD flag will be passed to msvc build tools.
    ///
    /// This option defaults to `false`, and affect only msvc targets.
    pub fn static_crt(&mut self, static_crt: bool) -> &mut Config {
        self.static_crt = Some(static_crt);
        self
    }

    /// Add an argument to the `cmake` configure step
    pub fn configure_arg<A: AsRef<OsStr>>(&mut self, arg: A) -> &mut Config {
        self.configure_args.push(arg.as_ref().to_owned());
        self
    }

    /// Add an argument to the final `cmake` build step
    pub fn build_arg<A: AsRef<OsStr>>(&mut self, arg: A) -> &mut Config {
        self.build_args.push(arg.as_ref().to_owned());
        self
    }

    /// Configure an environment variable for the `cmake` processes spawned by
    /// this crate in the `build` step.
    pub fn env<K, V>(&mut self, key: K, value: V) -> &mut Config
    where
        K: AsRef<OsStr>,
        V: AsRef<OsStr>,
    {
        self.env.push((key.as_ref().to_owned(), value.as_ref().to_owned()));
        self
    }

    /// Sets the build target for the final `cmake` build step, this will
    /// default to "install" if not specified.
    pub fn build_target(&mut self, target: &str) -> &mut Config {
        self.cmake_target = Some(target.to_string());
        self
    }

    /// Alters the default target triple on OSX to ensure that c++11 is
    /// available. Does not change the target triple if it is explicitly
    /// specified.
    ///
    /// This does not otherwise affect any CXX flags, i.e. it does not set
    /// -std=c++11 or -stdlib=libc++.
    #[deprecated = "no longer does anything, C++ is determined based on `cc::Build`, and the macOS issue has been fixed upstream"]
    pub fn uses_cxx11(&mut self) -> &mut Config {
        self.uses_cxx11 = true;
        self
    }

    /// Forces CMake to always run before building the custom target.
    ///
    /// In some cases, when you have a big project, you can disable
    /// subsequents runs of cmake to make `cargo build` faster.
    pub fn always_configure(&mut self, always_configure: bool) -> &mut Config {
        self.always_configure = always_configure;
        self
    }

    /// Sets very verbose output.
    pub fn very_verbose(&mut self, value: bool) -> &mut Config {
        self.verbose_cmake = value;
        self.verbose_make = value;
        self
    }

    // Simple heuristic to determine if we're cross-compiling using the Android
    // NDK toolchain file.
    fn uses_android_ndk(&self) -> bool {
        // `ANDROID_ABI` is the only required flag:
        // https://developer.android.com/ndk/guides/cmake#android_abi
        self.defined("ANDROID_ABI")
            && self.defines.iter().any(|(flag, value)| {
                flag == "CMAKE_TOOLCHAIN_FILE"
                    && Path::new(value).file_name() == Some("android.toolchain.cmake".as_ref())
            })
    }

    /// Initializes the C build configuration.
    pub fn init_c_cfg(&mut self, c_cfg: cc::Build) -> &mut Config {
        self.c_cfg = Some(c_cfg);
        self
    }

    /// Initializes the C++ build configuration.
    pub fn init_cxx_cfg(&mut self, cxx_cfg: cc::Build) -> &mut Config {
        self.cxx_cfg = Some(cxx_cfg);
        self
    }

    /// Resolve an isolated configuration without changing this builder or its output.
    /// Unavailable compiler inputs are returned as errors; opaque contexts have no cache key.
    pub fn try_prepare(&self) -> Result<Prepared, PrepareError> {
        let parent_cwd = env::current_dir().map_err(|error| PrepareError(error.to_string()))?;
        let mut snapshot = self.clone();
        snapshot.validate_prepare_inputs()?;
        snapshot.resolve(Some(&parent_cwd))
    }

    /// Run both the build-system generator and library build with the configured options.
    /// Repeated mutable-builder calls retain their existing behavior.
    pub fn build(&mut self) -> PathBuf {
        self.resolve(None).unwrap_or_else(|e| fail(&e.to_string())).build()
    }

    fn validate_prepare_inputs(&self) -> Result<(), PrepareError> {
        for (name, supplied) in [
            ("TARGET", self.target.is_some()),
            ("HOST", self.host.is_some()),
            ("OUT_DIR", self.out_dir.is_some()),
        ] {
            if !supplied && env::var(name).map_or(true, |v| v.is_empty()) {
                return Err(PrepareError(format!("missing or invalid {name}")));
            }
        }
        if self.profile.is_none() {
            for name in ["PROFILE", "OPT_LEVEL", "DEBUG"] {
                let value = env::var(name)
                    .map_err(|_| PrepareError(format!("missing or invalid {name}")))?;
                let supported = match name {
                    "PROFILE" => matches!(value.as_str(), "debug" | "release" | "bench"),
                    "OPT_LEVEL" => matches!(value.as_str(), "0" | "1" | "2" | "3" | "s" | "z"),
                    "DEBUG" => matches!(value.as_str(), "true" | "false"),
                    _ => unreachable!(),
                };
                if !supported {
                    return Err(PrepareError(format!("unsupported {name}")));
                }
            }
        }
        let target = self.target.clone().unwrap_or_else(|| env::var("TARGET").unwrap());
        let host = self.host.clone().unwrap_or_else(|| env::var("HOST").unwrap());
        if target.is_empty() || host.is_empty() {
            return Err(PrepareError("empty target or host".into()));
        }
        if let Some((_, value)) = self.defines.iter().find(|(key, _)| key == "CMAKE_BUILD_TYPE") {
            if value.to_str().is_none() {
                return Err(PrepareError("non-UTF8 CMAKE_BUILD_TYPE".into()));
            }
        }
        if target.contains("msvc")
            && (self.generator.is_none()
                || !["i686", "x86_64", "thumbv7a", "aarch64"]
                    .iter()
                    .any(|part| target.contains(part)))
        {
            return Err(PrepareError("unsupported pre-cache MSVC generator selection".into()));
        }
        if target.contains("darwin")
            && !self.defined("CMAKE_OSX_ARCHITECTURES")
            && !target.contains("x86_64")
            && !target.contains("aarch64")
        {
            return Err(PrepareError("unsupported Darwin architecture".into()));
        }
        let mut selector = self.clone();
        let has_toolchain = self.defined("CMAKE_TOOLCHAIN_FILE")
            || selector.getenv_target_os("CMAKE_TOOLCHAIN_FILE").is_some();
        if target != host
            && !self.defined("CMAKE_SYSTEM_NAME")
            && !has_toolchain
            && !target.contains("redox")
        {
            for name in ["CARGO_CFG_TARGET_OS", "CARGO_CFG_TARGET_ARCH"] {
                env::var(name).map_err(|_| PrepareError(format!("missing or invalid {name}")))?;
            }
        }
        Ok(())
    }

    fn resolve(&mut self, parent_cwd: Option<&Path>) -> Result<Prepared, PrepareError> {
        let preparing = parent_cwd.is_some();
        let target = match self.target.clone() {
            Some(t) => t,
            None => getenv_unwrap("TARGET"),
        };
        let host = self.host.clone().unwrap_or_else(|| getenv_unwrap("HOST"));

        // Some decisions later on are made if CMAKE_TOOLCHAIN_FILE is defined,
        // so we need to read it from the environment variables from the beginning.
        if !self.defined("CMAKE_TOOLCHAIN_FILE") {
            if let Some(s) = self.getenv_target_os("CMAKE_TOOLCHAIN_FILE") {
                self.define("CMAKE_TOOLCHAIN_FILE", s);
            } else if target.contains("redox") {
                if !self.defined("CMAKE_SYSTEM_NAME") {
                    self.define("CMAKE_SYSTEM_NAME", "Generic");
                }
            } else if target != host && !self.defined("CMAKE_SYSTEM_NAME") {
                // Set CMAKE_SYSTEM_NAME and CMAKE_SYSTEM_PROCESSOR when cross compiling
                let os = getenv_unwrap("CARGO_CFG_TARGET_OS");
                let arch = getenv_unwrap("CARGO_CFG_TARGET_ARCH");
                // CMAKE_SYSTEM_NAME list
                // https://gitlab.kitware.com/cmake/cmake/-/issues/21489#note_1077167
                //
                // CMAKE_SYSTEM_PROCESSOR
                // some of the values come from https://en.wikipedia.org/wiki/Uname
                let (system_name, system_processor) = match (os.as_str(), arch.as_str()) {
                    ("android", "arm") => ("Android", "armv7-a"),
                    ("android", "x86") => ("Android", "i686"),
                    ("android", arch) => ("Android", arch),
                    ("dragonfly", arch) => ("DragonFly", arch),
                    ("macos", "aarch64") => ("Darwin", "arm64"),
                    ("macos", arch) => ("Darwin", arch),
                    ("freebsd", "x86_64") => ("FreeBSD", "amd64"),
                    ("freebsd", arch) => ("FreeBSD", arch),
                    ("fuchsia", arch) => ("Fuchsia", arch),
                    ("haiku", arch) => ("Haiku", arch),
                    ("ios", "aarch64") => ("iOS", "arm64"),
                    ("ios", arch) => ("iOS", arch),
                    ("linux", arch) => {
                        let name = "Linux";
                        match arch {
                            "powerpc" => (name, "ppc"),
                            "powerpc64" => (name, "ppc64"),
                            "powerpc64le" => (name, "ppc64le"),
                            _ => (name, arch),
                        }
                    }
                    ("netbsd", arch) => ("NetBSD", arch),
                    ("openbsd", "x86_64") => ("OpenBSD", "amd64"),
                    ("openbsd", arch) => ("OpenBSD", arch),
                    ("solaris", arch) => ("SunOS", arch),
                    ("tvos", "aarch64") => ("tvOS", "arm64"),
                    ("tvos", arch) => ("tvOS", arch),
                    ("visionos", "aarch64") => ("visionOS", "arm64"),
                    ("visionos", arch) => ("visionOS", arch),
                    ("watchos", "aarch64") => ("watchOS", "arm64"),
                    ("watchos", arch) => ("watchOS", arch),
                    ("windows", "x86_64") => ("Windows", "AMD64"),
                    ("windows", "x86") => ("Windows", "X86"),
                    ("windows", "aarch64") => ("Windows", "ARM64"),
                    ("none", arch) => ("Generic", arch),
                    // Others
                    (os, arch) => (os, arch),
                };
                self.define("CMAKE_SYSTEM_NAME", system_name);
                self.define("CMAKE_SYSTEM_PROCESSOR", system_processor);
            }
        }

        let generator = self.generator.clone().or_else(|| self.getenv_target_os("CMAKE_GENERATOR"));

        let msvc = target.contains("msvc");
        let ndk = self.uses_android_ndk();
        let mut c_cfg = self.c_cfg.clone().unwrap_or_default();
        c_cfg
            .cargo_metadata(false)
            .cpp(false)
            .opt_level(0)
            .debug(false)
            .warnings(false)
            .host(&host)
            .no_default_flags(ndk || self.no_default_flags);
        if !ndk {
            c_cfg.target(&target);
        }
        let mut cxx_cfg = self.cxx_cfg.clone().unwrap_or_default();
        cxx_cfg
            .cargo_metadata(false)
            .cpp(true)
            .opt_level(0)
            .debug(false)
            .warnings(false)
            .host(&host)
            .no_default_flags(ndk || self.no_default_flags);
        if !ndk {
            cxx_cfg.target(&target);
        }
        if let Some(static_crt) = self.static_crt {
            c_cfg.static_crt(static_crt);
            cxx_cfg.static_crt(static_crt);
        }
        if let Some(explicit_flag) = self.pic {
            c_cfg.pic(explicit_flag);
            cxx_cfg.pic(explicit_flag);
        }
        let c_compiler = c_cfg.try_get_compiler().map_err(|e| PrepareError(e.to_string()))?;
        let cxx_compiler = cxx_cfg.try_get_compiler().map_err(|e| PrepareError(e.to_string()))?;
        let asm_compiler = c_cfg.try_get_compiler().map_err(|e| PrepareError(e.to_string()))?;

        let dst = output_directory(self.out_dir.as_deref(), parent_cwd, || {
            PathBuf::from(getenv_unwrap("OUT_DIR"))
        })?;
        let build = dst.join("build");

        let cmake_prefix_path = self.resolve_prefix_paths(&build, preparing)?;

        // Build up the first cmake command to build the build system.
        let mut cmd = self.cmake_configure_command(&target);

        let mut version = if preparing {
            Version::default()
        } else {
            Version::from_command(cmd.get_program()).unwrap_or_default()
        };

        if self.verbose_cmake {
            cmd.arg("-Wdev");
            cmd.arg("--debug-output");
        }

        cmd.arg(&self.path).current_dir(&build);
        let mut is_ninja = false;
        if let Some(ref generator) = generator {
            is_ninja = generator.to_string_lossy().contains("Ninja");
        }
        if target.contains("windows-gnu") {
            if host.contains("windows") {
                // On MinGW we need to coerce cmake to not generate a visual
                // studio build system but instead use makefiles that MinGW can
                // use to build.
                if generator.is_none() {
                    // If make.exe isn't found, that means we may be using a MinGW
                    // toolchain instead of a MSYS2 toolchain. If neither is found,
                    // the build cannot continue.
                    let has_msys2 = Command::new("make")
                        .arg("--version")
                        .output()
                        .err()
                        .map(|e| e.kind() != ErrorKind::NotFound)
                        .unwrap_or(true);
                    let has_mingw32 = Command::new("mingw32-make")
                        .arg("--version")
                        .output()
                        .err()
                        .map(|e| e.kind() != ErrorKind::NotFound)
                        .unwrap_or(true);

                    let generator = match (has_msys2, has_mingw32) {
                        (true, _) => "MSYS Makefiles",
                        (false, true) => "MinGW Makefiles",
                        (false, false) => fail(
                            "no valid generator found for GNU toolchain; MSYS or MinGW must be installed",
                        ),
                    };

                    cmd.arg("-G").arg(generator);
                }
            } else {
                // If we're cross compiling onto windows, then set some
                // variables which will hopefully get things to succeed. Some
                // systems may need the `windres` or `dlltool` variables set, so
                // set them if possible.
                if !self.defined("CMAKE_RC_COMPILER") {
                    let exe = find_exe(c_compiler.path());
                    if let Some(name) = exe.file_name().unwrap().to_str() {
                        let name = name.replace("gcc", "windres");
                        let windres = exe.with_file_name(name);
                        if windres.is_file() {
                            let mut arg = OsString::from("-DCMAKE_RC_COMPILER=");
                            arg.push(&windres);
                            cmd.arg(arg);
                        }
                    }
                }
            }
        } else if msvc {
            // If we're on MSVC we need to be sure to use the right generator or
            // otherwise we won't get 32/64 bit correct automatically.
            // This also guarantees that NMake generator isn't chosen implicitly.
            let using_nmake_generator = if let Some(g) = &generator {
                g == "NMake Makefiles" || g == "NMake Makefiles JOM"
            } else {
                cmd.arg("-G").arg(self.visual_studio_generator(&target));
                false
            };
            if !is_ninja && !using_nmake_generator {
                if target.contains("x86_64") {
                    if self.generator_toolset.is_none() {
                        cmd.arg("-Thost=x64");
                    }
                    cmd.arg("-Ax64");
                } else if target.contains("thumbv7a") {
                    if self.generator_toolset.is_none() {
                        cmd.arg("-Thost=x64");
                    }
                    cmd.arg("-Aarm");
                } else if target.contains("aarch64") {
                    if self.generator_toolset.is_none() {
                        cmd.arg("-Thost=x64");
                    }
                    cmd.arg("-AARM64");
                } else if target.contains("i686") {
                    if self.generator_toolset.is_none() {
                        cmd.arg("-Thost=x86");
                    }
                    cmd.arg("-AWin32");
                } else {
                    panic!("unsupported msvc target: {}", target);
                }
            }
        } else if target.contains("darwin") && !self.defined("CMAKE_OSX_ARCHITECTURES") {
            if target.contains("x86_64") {
                cmd.arg("-DCMAKE_OSX_ARCHITECTURES=x86_64");
            } else if target.contains("aarch64") {
                cmd.arg("-DCMAKE_OSX_ARCHITECTURES=arm64");
            } else {
                panic!("unsupported darwin target: {}", target);
            }
        }
        if let Some(ref generator) = generator {
            cmd.arg("-G").arg(generator);
        }
        if let Some(ref generator_toolset) = self.generator_toolset {
            cmd.arg("-T").arg(generator_toolset);
        }
        let profile = self.get_profile().to_string();
        let cleanup_opaque = self.cleanup_is_opaque();
        if let Some(parent_cwd) = parent_cwd {
            self.bind_input_programs(parent_cwd, c_compiler.env())?;
        }
        let execution_configure_args = self.append_definitions(&mut cmd);

        if !self.defined("CMAKE_INSTALL_PREFIX") {
            let mut dstflag = OsString::from("-DCMAKE_INSTALL_PREFIX=");
            dstflag.push(&dst);
            cmd.arg(dstflag);
        }

        let build_type = self
            .defines
            .iter()
            .find(|&(a, _)| a == "CMAKE_BUILD_TYPE")
            .map(|x| x.1.to_str().unwrap())
            .unwrap_or(&profile);
        let build_type_upcase =
            build_type.chars().flat_map(|c| c.to_uppercase()).collect::<String>();

        {
            // let cmake deal with optimization/debuginfo
            let skip_arg = |arg: &OsStr| match arg.to_str() {
                Some(s) => s.starts_with("-O") || s.starts_with("/O") || s == "-g",
                None => false,
            };
            let mut set_compiler = |kind: &str, compiler: &cc::Tool, extra: &OsString| {
                let flag_var = format!("CMAKE_{}_FLAGS", kind);
                let tool_var = format!("CMAKE_{}_COMPILER", kind);
                if !self.defined(&flag_var) {
                    let mut flagsflag = OsString::from("-D");
                    flagsflag.push(&flag_var);
                    flagsflag.push("=");
                    flagsflag.push(extra);
                    for arg in compiler.args() {
                        if skip_arg(arg) {
                            continue;
                        }
                        flagsflag.push(" ");
                        flagsflag.push(arg);
                    }
                    cmd.arg(flagsflag);
                }

                // The visual studio generator apparently doesn't respect
                // `CMAKE_C_FLAGS` but does respect `CMAKE_C_FLAGS_RELEASE` and
                // such. We need to communicate /MD vs /MT, so set those vars
                // here.
                //
                // Note that for other generators, though, this *overrides*
                // things like the optimization flags, which is bad.
                if generator.is_none() && msvc {
                    let flag_var_alt = format!("CMAKE_{}_FLAGS_{}", kind, build_type_upcase);
                    if !self.defined(&flag_var_alt) {
                        let mut flagsflag = OsString::from("-D");
                        flagsflag.push(&flag_var_alt);
                        flagsflag.push("=");
                        flagsflag.push(extra);
                        for arg in compiler.args() {
                            if skip_arg(arg) {
                                continue;
                            }
                            flagsflag.push(" ");
                            flagsflag.push(arg);
                        }
                        cmd.arg(flagsflag);
                    }
                }

                // Apparently cmake likes to have an absolute path to the
                // compiler as otherwise it sometimes thinks that this variable
                // changed as it thinks the found compiler, /usr/bin/cc,
                // differs from the specified compiler, cc. Not entirely sure
                // what's up, but at least this means cmake doesn't get
                // confused?
                //
                // Also specify this on Windows only if we use MSVC with Ninja,
                // as it's not needed for MSVC with Visual Studio generators and
                // for MinGW it doesn't really vary.
                if !self.defined("CMAKE_TOOLCHAIN_FILE")
                    && !self.defined(&tool_var)
                    && (env::consts::FAMILY != "windows" || (msvc && is_ninja))
                {
                    let mut ccompiler = OsString::from("-D");
                    ccompiler.push(&tool_var);
                    ccompiler.push("=");
                    ccompiler.push(find_exe(compiler.path()));
                    #[cfg(windows)]
                    {
                        // CMake doesn't like unescaped `\`s in compiler paths
                        // so we either have to escape them or replace with `/`s.
                        use std::os::windows::ffi::{OsStrExt, OsStringExt};
                        let wchars = ccompiler
                            .encode_wide()
                            .map(|wchar| if wchar == b'\\' as u16 { '/' as u16 } else { wchar })
                            .collect::<Vec<_>>();
                        ccompiler = OsString::from_wide(&wchars);
                    }
                    cmd.arg(ccompiler);
                }
            };

            set_compiler("C", &c_compiler, &self.cflags);
            set_compiler("CXX", &cxx_compiler, &self.cxxflags);
            set_compiler("ASM", &asm_compiler, &self.asmflags);
        }

        if !self.defined("CMAKE_BUILD_TYPE") {
            cmd.arg(format!("-DCMAKE_BUILD_TYPE={}", profile));
        }

        if self.verbose_make {
            cmd.arg("-DCMAKE_VERBOSE_MAKEFILE:BOOL=ON");
        }

        for (k, v) in c_compiler.env().iter().chain(&self.env) {
            cmd.env(k, v);
        }

        cmd.args(&self.configure_args);
        cmd.env("CMAKE_PREFIX_PATH", cmake_prefix_path);
        let mut configure = cmd;
        let original_program = configure.get_program().to_owned();
        let mut cmd = self.cmake_build_command(&target);
        cmd.current_dir(&build);
        for (k, v) in c_compiler.env().iter().chain(&self.env) {
            cmd.env(k, v);
        }
        cmd.arg("--build").arg(&build);
        if !self.no_build_target {
            cmd.arg("--target").arg(self.cmake_target.as_deref().unwrap_or("install"));
        }
        cmd.arg("--config").arg(&profile);
        let mut cache_inputs = None;
        let mut cleanup_inputs = None;
        if let Some(parent_cwd) = parent_cwd {
            let mut selection = Vec::new();
            let roots = &self.cache_roots;
            let bound = freeze_program_relocated(&mut configure, &mut selection, parent_cwd, roots)
                && freeze_program_relocated(&mut cmd, &mut selection, parent_cwd, roots);
            if bound && !cleanup_opaque && reusable_configuration(self, &generator, &target) {
                let mut paths = self
                    .input_paths
                    .iter()
                    .map(|(_, path)| path.clone())
                    .chain(self.selected_paths.iter().cloned())
                    .collect::<Vec<_>>();
                paths.extend([configure.get_program().into(), cmd.get_program().into()]);
                let mut tools_bound = paths.iter().all(|path| path.is_absolute());
                for tool in [&c_compiler, &cxx_compiler, &asm_compiler] {
                    // cc may select a wrapper separately from the compiler itself.
                    // cc exposes this same selected Apple SDK as an explicit Tool env path.
                    paths.extend(
                        tool.env()
                            .iter()
                            .filter(|(key, _)| key == "SDKROOT")
                            .map(|(_, value)| PathBuf::from(value)),
                    );
                    let mut selected = tool.to_command();
                    if selected.get_program() != tool.path().as_os_str() {
                        let expected = std::iter::once(tool.path().as_os_str())
                            .chain(tool.args().iter().map(OsString::as_os_str))
                            .collect::<Vec<_>>();
                        tools_bound &= selected.get_args().collect::<Vec<_>>() == expected;
                    }
                    selected.envs(self.env.iter().map(|(key, value)| (key, value)));
                    tools_bound &= freeze_program(&mut selected, &mut Vec::new(), parent_cwd);
                    paths.push(PathBuf::from(selected.get_program()));
                    let mut compiler = Command::new(tool.path());
                    compiler
                        .envs(tool.env().iter().chain(&self.env).map(|(key, value)| (key, value)));
                    tools_bound &= freeze_program(&mut compiler, &mut Vec::new(), parent_cwd);
                    paths.push(PathBuf::from(compiler.get_program()));
                }
                if tools_bound && paths.iter().all(|path| path.is_absolute()) {
                    cleanup_inputs = Some(paths);
                }
            }
            let mut observation = None;
            if bound {
                // Version probing historically runs from the parent's cwd, not the
                // not-yet-created build directory. Preserve that context explicitly.
                let mut probe = Command::new(configure.get_program());
                probe.envs(c_compiler.env().iter().chain(&self.env).map(|(k, v)| (k, v)));
                probe.current_dir(parent_cwd);
                observation = VersionObservation::from_query(&mut probe);
                if let Some(observed) = &observation {
                    version = observed.api;
                }
            }
            if let Some(observation) = &observation {
                cache_inputs = snapshot_inputs(
                    self,
                    &configure,
                    &cmd,
                    &generator,
                    &target,
                    observation,
                    [&c_compiler, &cxx_compiler, &asm_compiler],
                    &execution_configure_args,
                );
            }
            if !bound {
                // Unknown search binding disables reuse, not ordinary build
                // behavior: preserve the upstream parent-context version query.
                let mut probe = Command::new(&original_program);
                probe.current_dir(parent_cwd);
                version = Version::from_query(&mut probe).unwrap_or_default();
            }
            if let Some(bytes) = &mut cache_inputs {
                frame(bytes, &selection);
            }
        }
        Ok(Prepared {
            config: self.clone(),
            configure,
            command: cmd,
            dst,
            build,
            version,
            cache_inputs,
            cleanup_inputs,
        })
    }

    fn append_definitions(&self, command: &mut Command) -> Vec<usize> {
        let mut execution = Vec::new();
        for (index, (key, value)) in self.defines.iter().enumerate() {
            if self.execution_defines.contains(&index) {
                execution.push(command.get_args().count());
            }
            let mut argument = OsString::from("-D");
            argument.push(key);
            argument.push("=");
            argument.push(value);
            command.arg(argument);
        }
        execution
    }

    fn resolve_prefix_paths(
        &mut self,
        build: &Path,
        preparing: bool,
    ) -> Result<OsString, PrepareError> {
        let mut prefixes = Vec::new();
        for dep in &self.deps {
            let dep = dep.to_uppercase().replace('-', "_");
            if let Some(root) = env::var_os(format!("DEP_{}_ROOT", dep)) {
                prefixes.push(PathBuf::from(root));
            }
        }
        let system_prefix = self.getenv_target_os("CMAKE_PREFIX_PATH").unwrap_or_default();
        prefixes.extend(env::split_paths(&system_prefix));
        if preparing {
            for prefix in &prefixes {
                if !prefix.as_os_str().is_empty() {
                    self.selected_paths.push(if prefix.is_absolute() {
                        prefix.clone()
                    } else {
                        build.join(prefix)
                    });
                }
            }
        }
        env::join_paths(&prefixes).map_err(|error| PrepareError(error.to_string()))
    }

    fn cleanup_is_opaque(&self) -> bool {
        self.cleanup_opaque
            || self.defined("CMAKE_TOOLCHAIN_FILE")
            || !self
                .input_programs
                .iter()
                .any(|(index, _)| self.defines[*index].0 == "CMAKE_MAKE_PROGRAM")
            || self
                .input_paths
                .iter()
                .map(|(index, _)| *index)
                .chain(self.input_programs.iter().map(|(index, _)| *index))
                .any(|index| {
                    self.defines[index + 1..].iter().any(|(key, _)| key == &self.defines[index].0)
                })
    }

    fn bind_input_programs(
        &mut self,
        parent_cwd: &Path,
        tool_env: &[(OsString, OsString)],
    ) -> Result<(), PrepareError> {
        for (index, candidates) in self.input_programs.clone() {
            if self.defines[index + 1..].iter().any(|(key, _)| key == &self.defines[index].0) {
                continue;
            }
            let selected = candidates
                .iter()
                .find_map(|candidate| {
                    let mut command = Command::new(candidate);
                    command.envs(tool_env.iter().chain(&self.env).map(|(key, value)| (key, value)));
                    freeze_program(&mut command, &mut Vec::new(), parent_cwd)
                        .then(|| PathBuf::from(command.get_program()))
                })
                .ok_or_else(|| {
                    PrepareError("selected input program has unavailable namespace evidence".into())
                })?;
            self.defines[index].1 = selected.as_os_str().to_owned();
            self.input_paths.push((index, selected));
        }
        Ok(())
    }

    fn cmake_executable(&mut self) -> OsString {
        self.getenv_target_os("CMAKE").unwrap_or_else(|| OsString::from("cmake"))
    }

    // If we are building for Emscripten, wrap the calls to CMake
    // as "emcmake cmake ..." and "emmake cmake --build ...".
    // https://emscripten.org/docs/compiling/Building-Projects.html

    fn cmake_configure_command(&mut self, target: &str) -> Command {
        if target.contains("emscripten") {
            let emcmake =
                self.getenv_target_os("EMCMAKE").unwrap_or_else(|| OsString::from("emcmake"));
            let mut cmd = Command::new(emcmake);
            cmd.arg(self.cmake_executable());
            cmd
        } else {
            Command::new(self.cmake_executable())
        }
    }

    fn cmake_build_command(&mut self, target: &str) -> Command {
        if target.contains("emscripten") {
            let emmake =
                self.getenv_target_os("EMMAKE").unwrap_or_else(|| OsString::from("emmake"));
            let mut cmd = Command::new(emmake);
            cmd.arg(self.cmake_executable());
            cmd
        } else {
            Command::new(self.cmake_executable())
        }
    }

    fn getenv_os_with(
        &mut self,
        v: &str,
        lookup: &mut impl FnMut(&str) -> Option<OsString>,
    ) -> Option<OsString> {
        if let Some(val) = self.env_cache.get(v) {
            return val.clone();
        }
        let r = lookup(v);
        println!("{} = {:?}", v, r);
        self.env_cache.insert(v.to_string(), r.clone());
        r
    }

    fn getenv_target_os(&mut self, var_base: &str) -> Option<OsString> {
        self.getenv_target_os_with(var_base, &mut |name| env::var_os(name))
    }

    // One selector implementation serves normal process lookup and isolated
    // read-only data fixtures. Only actually queried candidates are observed.
    fn getenv_target_os_with(
        &mut self,
        var_base: &str,
        lookup: &mut impl FnMut(&str) -> Option<OsString>,
    ) -> Option<OsString> {
        let host = self.host.clone().unwrap_or_else(|| getenv_unwrap("HOST"));
        let target = self.target.clone().unwrap_or_else(|| getenv_unwrap("TARGET"));
        let kind = if host == target { "HOST" } else { "TARGET" };
        let target_u = target.replace('-', "_");
        self.getenv_os_with(&format!("{}_{}", var_base, target), lookup)
            .or_else(|| self.getenv_os_with(&format!("{}_{}", var_base, target_u), lookup))
            .or_else(|| self.getenv_os_with(&format!("{}_{}", kind, var_base), lookup))
            .or_else(|| self.getenv_os_with(var_base, lookup))
    }

    fn visual_studio_generator(&self, target: &str) -> String {
        use cc::windows_registry::{VsVers, find_vs_version};

        let base = match find_vs_version() {
            Ok(VsVers::Vs17) => "Visual Studio 17 2022",
            Ok(VsVers::Vs16) => "Visual Studio 16 2019",
            Ok(VsVers::Vs15) => "Visual Studio 15 2017",
            Ok(VsVers::Vs14) => "Visual Studio 14 2015",
            // This was deprecated recently (2024-07). Ignore the warning for now.
            #[allow(deprecated)]
            Ok(VsVers::Vs12) => "Visual Studio 12 2013",
            Ok(_) => panic!(
                "Visual studio version detected but this crate \
                 doesn't know how to generate cmake files for it, \
                 can the `cmake` crate be updated?"
            ),
            Err(msg) => panic!("{}", msg),
        };
        if ["i686", "x86_64", "thumbv7a", "aarch64"].iter().any(|t| target.contains(t)) {
            base.to_string()
        } else {
            panic!("unsupported msvc target: {}", target);
        }
    }

    fn defined(&self, var: &str) -> bool {
        self.defines.iter().any(|(a, _)| a == var)
    }

    // If a cmake project has previously been built (e.g. CMakeCache.txt already
    // exists), then cmake will choke if the source directory for the original
    // project being built has changed. Detect this situation through the
    // `CMAKE_HOME_DIRECTORY` variable that cmake emits and if it doesn't match
    // we blow away the build directory and start from scratch (the recommended
    // solution apparently [1]).
    //
    // [1]: https://cmake.org/pipermail/cmake/2012-August/051545.html
    fn maybe_clear(&self, dir: &Path) {
        // CMake will apparently store canonicalized paths which normally
        // isn't relevant to us but we canonicalize it here to ensure
        // we're both checking the same thing.
        let path = fs::canonicalize(&self.path).unwrap_or_else(|_| self.path.clone());
        let mut f = match File::open(dir.join("CMakeCache.txt")) {
            Ok(f) => f,
            Err(..) => return,
        };
        let mut u8contents = Vec::new();
        match f.read_to_end(&mut u8contents) {
            Ok(f) => f,
            Err(..) => return,
        };
        let contents = String::from_utf8_lossy(&u8contents);
        drop(f);
        for line in contents.lines() {
            if line.starts_with("CMAKE_HOME_DIRECTORY") {
                let needs_cleanup = match line.split('=').next_back() {
                    Some(cmake_home) => fs::canonicalize(cmake_home)
                        .ok()
                        .map(|cmake_home| cmake_home != path)
                        .unwrap_or(true),
                    None => true,
                };
                if needs_cleanup {
                    println!(
                        "detected home dir change, cleaning out entire build \
                         directory"
                    );
                    fs::remove_dir_all(dir).unwrap();
                }
                break;
            }
        }
    }
}

// Select the output exactly once. Legacy calls retain their relative spelling;
// preparation anchors it lexically without requiring an existing output tree.
fn output_directory(
    explicit: Option<&Path>,
    parent_cwd: Option<&Path>,
    fallback: impl FnOnce() -> PathBuf,
) -> Result<PathBuf, PrepareError> {
    let directory = explicit.map(Path::to_path_buf).unwrap_or_else(fallback);
    let Some(parent_cwd) = parent_cwd else {
        return Ok(directory);
    };
    if directory.is_absolute() {
        return Ok(directory);
    }
    let anchored = parent_cwd.join(directory);
    if !anchored.is_absolute() {
        return Err(PrepareError("output requires unsupported drive-relative context".into()));
    }
    Ok(anchored)
}

/// An unavailable input during transactional preparation.
#[derive(Debug)]
pub struct PrepareError(String);
impl std::fmt::Display for PrepareError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}
impl std::error::Error for PrepareError {}

/// A single-use resolution of the commands and tools selected for a build.
pub struct Prepared {
    config: Config,
    configure: Command,
    command: Command,
    dst: PathBuf,
    build: PathBuf,
    version: Version,
    cache_inputs: Option<Vec<u8>>,
    cleanup_inputs: Option<Vec<PathBuf>>,
}
impl Prepared {
    /// Framed requested/selected inputs, or none when this context is opaque.
    /// These bytes do not identify executable contents or a toolchain closure.
    pub fn cache_inputs(&self) -> Option<&[u8]> {
        self.cache_inputs.as_deref()
    }

    /// Selected executable and explicitly declared input paths, or none for opaque resolution.
    /// Namespace data only: callers must validate these against their output immediately
    /// before cleanup. This is not executable identity or arbitrary CMake hermeticity.
    pub fn cleanup_inputs(&self) -> Option<&[PathBuf]> {
        self.cleanup_inputs.as_deref()
    }

    /// Execute this resolution once without selecting configuration inputs again.
    pub fn build(mut self) -> PathBuf {
        self.config.maybe_clear(&self.build);
        let _ = fs::create_dir_all(&self.build);
        if self.config.always_configure || !self.build.join("CMakeCache.txt").exists() {
            run(&mut self.configure, "cmake");
        } else {
            println!("CMake project was already configured. Skipping configuration step.");
        }
        let build = &self.build;
        let dst = self.dst;
        let version = self.version;
        let cmd = &mut self.command;
        // If the generated project is Makefile based we should carefully transfer corresponding CARGO_MAKEFLAGS
        let mut use_jobserver = false;
        if fs::metadata(build.join("Makefile")).is_ok() {
            match env::var_os("CARGO_MAKEFLAGS") {
                // Only do this on non-windows, non-bsd, and non-macos (unless a named pipe
                // jobserver is available)
                // * On Windows, we could be invoking make instead of
                //   mingw32-make which doesn't work with our jobserver
                // * bsdmake also does not work with our job server
                // * On macOS, CMake blocks propagation of the jobserver's file descriptors to make
                //   However, if the jobserver is based on a named pipe, this will be available to
                //   the build.
                Some(ref makeflags)
                    if !(cfg!(windows)
                        || cfg!(target_os = "openbsd")
                        || cfg!(target_os = "netbsd")
                        || cfg!(target_os = "freebsd")
                        || cfg!(target_os = "dragonfly")
                        || (cfg!(target_os = "macos")
                            && !uses_named_pipe_jobserver(makeflags))) =>
                {
                    use_jobserver = true;
                    cmd.env("MAKEFLAGS", makeflags);
                }
                _ => {}
            }
        }

        // --parallel requires CMake 3.12:
        // https://cmake.org/cmake/help/latest/release/3.12.html#command-line
        if version >= Version::new(3, 12) && !use_jobserver {
            if let Ok(s) = env::var("NUM_JOBS") {
                // See https://cmake.org/cmake/help/v3.12/manual/cmake.1.html#build-tool-mode
                cmd.arg("--parallel").arg(s);
            }
        }

        if !&self.config.build_args.is_empty() {
            cmd.arg("--").args(&self.config.build_args);
        }

        run(cmd, "cmake");

        println!("cargo:root={}", dst.display());
        dst
    }
}

fn frame(bytes: &mut Vec<u8>, value: &[u8]) {
    bytes.extend_from_slice(&(value.len() as u64).to_le_bytes());
    bytes.extend_from_slice(value);
}

/// `value` with each of `roots` written as its token `\0trust-cmake-root-<index>\0` where it
/// stands as a whole path: the byte after it is absent or ends a path component (`/`, or any
/// byte but an ASCII letter, digit, `.`, `_` or `-`), and the byte before it is absent or is no
/// such byte and no `/` either. A root that is empty or `/` alone is never replaced.
fn relocated<'a>(value: &'a [u8], roots: &[PathBuf]) -> std::borrow::Cow<'a, [u8]> {
    let continues = |byte: u8| byte.is_ascii_alphanumeric() || b"._-".contains(&byte);
    let mut out = std::borrow::Cow::Borrowed(value);
    for (index, root) in roots.iter().enumerate() {
        let root = root.as_os_str().as_encoded_bytes();
        let root = root.strip_suffix(b"/").unwrap_or(root);
        if root.is_empty() {
            continue;
        }
        let token = format!("\0trust-cmake-root-{index}\0").into_bytes();
        let data = out.as_ref();
        let mut next = Vec::with_capacity(data.len());
        let (mut at, mut copied, mut changed) = (0, 0, false);
        while let Some(found) = data[at..].windows(root.len()).position(|window| window == root) {
            let start = at + found;
            let end = start + root.len();
            let before = start.checked_sub(1).map(|i| data[i]);
            let whole = before.is_none_or(|byte| !continues(byte) && byte != b'/')
                && data.get(end).is_none_or(|&byte| !continues(byte));
            if whole {
                next.extend_from_slice(&data[copied..start]);
                next.extend_from_slice(&token);
                copied = end;
                changed = true;
                at = end;
            } else {
                at = start + 1;
            }
            if at + root.len() > data.len() {
                break;
            }
        }
        if changed {
            next.extend_from_slice(&data[copied..]);
            out = std::borrow::Cow::Owned(next);
        }
    }
    out
}

fn execution_only_build_args(args: &[OsString]) -> bool {
    fn positive_jobs(jobs: &str) -> bool {
        !jobs.is_empty()
            && jobs.bytes().all(|byte| byte.is_ascii_digit())
            && jobs.parse::<u32>().is_ok_and(|jobs| jobs > 0)
    }
    let mut args = args.iter();
    while let Some(arg) = args.next() {
        if arg == "--quiet" {
            continue;
        }
        let Some(arg) = arg.to_str() else {
            return false;
        };
        if arg == "-j" {
            if !args.next().and_then(|jobs| jobs.to_str()).is_some_and(positive_jobs) {
                return false;
            }
        } else if !arg.strip_prefix("-j").is_some_and(positive_jobs) {
            return false;
        }
    }
    true
}

fn reusable_configuration(
    config: &Config,
    generator: &Option<OsString>,
    resolved_target: &str,
) -> bool {
    generator.as_deref() == Some(OsStr::new("Ninja"))
        && !config.defined("CMAKE_TOOLCHAIN_FILE")
        && config.configure_args.is_empty()
        && execution_only_build_args(&config.build_args)
        && !resolved_target.contains("emscripten")
}

fn frame_selected_args(
    bytes: &mut Vec<u8>,
    command: &Command,
    execution: &[usize],
    roots: &[PathBuf],
) {
    let selected = command
        .get_args()
        .enumerate()
        .filter(|(index, _)| !execution.contains(index))
        .map(|(_, value)| value)
        .collect::<Vec<_>>();
    frame(bytes, &(selected.len() as u64).to_le_bytes());
    for value in selected {
        frame(bytes, &relocated(value.as_encoded_bytes(), roots));
    }
}

fn snapshot_inputs(
    config: &Config,
    configure: &Command,
    build: &Command,
    generator: &Option<OsString>,
    resolved_target: &str,
    version: &VersionObservation,
    tools: [&cc::Tool; 3],
    execution_configure_args: &[usize],
) -> Option<Vec<u8>> {
    if !reusable_configuration(config, generator, resolved_target) {
        return None;
    }
    let roots = &config.cache_roots;
    // A value is framed as the request names it, each root written as its token
    // ([`Config::cache_root`]); counts and flags are framed as they are.
    let named = |bytes: &mut Vec<u8>, text: &[u8]| frame(bytes, &relocated(text, roots));
    let mut bytes = b"trust-cmake:resolved-request:v2".to_vec();
    // Upstream find_exe uses the parent search context, independently of
    // explicit child PATH overrides. Record that request, not binary identity.
    let parent_path = env::var_os("PATH");
    bytes.push(u8::from(parent_path.is_some()));
    if let Some(path) = parent_path {
        named(&mut bytes, path.as_encoded_bytes());
    }
    // Record the selector observations themselves, including absent higher-priority
    // candidates. Shadowed lower-priority candidates are never queried.
    let mut observations: Vec<_> = config.env_cache.iter().collect();
    observations.sort_by_key(|(key, _)| *key);
    frame(&mut bytes, &(observations.len() as u64).to_le_bytes());
    for (key, value) in observations {
        named(&mut bytes, key.as_bytes());
        bytes.push(u8::from(value.is_some()));
        if let Some(value) = value {
            named(&mut bytes, value.as_encoded_bytes());
        }
    }
    for (index, command) in [configure, build].into_iter().enumerate() {
        named(&mut bytes, command.get_program().as_encoded_bytes());
        frame_selected_args(
            &mut bytes,
            command,
            if index == 0 { execution_configure_args } else { &[] },
            roots,
        );
        frame(&mut bytes, &(command.get_envs().count() as u64).to_le_bytes());
        for (key, value) in command.get_envs() {
            named(&mut bytes, key.as_encoded_bytes());
            bytes.push(u8::from(value.is_some()));
            if let Some(value) = value {
                named(&mut bytes, value.as_encoded_bytes());
            }
        }
        named(&mut bytes, command.get_current_dir()?.as_os_str().as_encoded_bytes());
    }
    for tool in tools {
        named(&mut bytes, tool.path().as_os_str().as_encoded_bytes());
        frame(&mut bytes, &(tool.args().len() as u64).to_le_bytes());
        for arg in tool.args() {
            named(&mut bytes, arg.as_encoded_bytes());
        }
        frame(&mut bytes, &(tool.env().len() as u64).to_le_bytes());
        for (key, value) in tool.env() {
            named(&mut bytes, key.as_encoded_bytes());
            named(&mut bytes, value.as_encoded_bytes());
        }
        bytes.extend_from_slice(&[
            u8::from(tool.is_like_gnu()),
            u8::from(tool.is_like_clang()),
            u8::from(tool.is_like_msvc()),
            u8::from(tool.is_like_clang_cl()),
        ]);
    }
    version.append_cache_inputs(&mut bytes);
    Some(bytes)
}

fn freeze_program(command: &mut Command, observations: &mut Vec<u8>, parent_cwd: &Path) -> bool {
    freeze_program_relocated(command, observations, parent_cwd, &[])
}

/// [`freeze_program`], recording its observations with `roots` written as tokens
/// ([`Config::cache_root`]).
fn freeze_program_relocated(
    command: &mut Command,
    observations: &mut Vec<u8>,
    parent_cwd: &Path,
    roots: &[PathBuf],
) -> bool {
    let frame = |bytes: &mut Vec<u8>, value: &[u8]| frame(bytes, &relocated(value, roots));
    // Portable unsupported search contexts stay nonreusable. No executable byte
    // identity is inferred from this lexical selection.
    if cfg!(windows) {
        return false;
    }
    let requested = command.get_program().to_owned();
    let path = Path::new(&requested);
    let effective_path = command
        .get_envs()
        .find(|(key, _)| *key == "PATH")
        .map(|(_, value)| value.map(OsStr::to_owned))
        .unwrap_or_else(|| env::var_os("PATH"));
    let selected = if path.is_absolute() {
        path.to_owned()
    } else {
        if path.components().count() != 1 {
            return false;
        }
        let Some(search) = effective_path.as_ref() else {
            return false;
        };
        let Some(selected) = env::split_paths(search)
            .filter(|dir| dir.is_absolute())
            .map(|dir| dir.join(path))
            .find(|path| executable(path))
        else {
            return false;
        };
        // Relative/empty earlier search directories could select something else.
        if env::split_paths(search).any(|dir| !dir.is_absolute()) {
            return false;
        }
        selected
    };
    if !executable(&selected) {
        return false;
    }
    let mut frozen = Command::new(selected);
    frozen.args(command.get_args());
    for (key, value) in command.get_envs() {
        if let Some(value) = value {
            frozen.env(key, value);
        } else {
            frozen.env_remove(key);
        }
    }
    if let Some(dir) = command.get_current_dir() {
        frozen.current_dir(dir);
    }
    match &effective_path {
        Some(path) => {
            frozen.env("PATH", path);
        }
        None => {
            frozen.env_remove("PATH");
        }
    }
    frame(observations, requested.as_encoded_bytes());
    frame(observations, parent_cwd.as_os_str().as_encoded_bytes());
    observations.push(u8::from(effective_path.is_some()));
    if let Some(search) = effective_path {
        frame(observations, search.as_encoded_bytes());
    }
    *command = frozen;
    true
}

fn executable(path: &Path) -> bool {
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        fs::metadata(path)
            .is_ok_and(|metadata| metadata.is_file() && metadata.permissions().mode() & 0o111 != 0)
    }
    #[cfg(not(unix))]
    {
        path.is_file()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Version {
    major: u32,
    minor: u32,
}

impl Version {
    fn new(major: u32, minor: u32) -> Self {
        Self { major, minor }
    }

    fn parse(s: &str) -> Option<Self> {
        // As of 3.22, the format of the version output is "cmake version <major>.<minor>.<patch>".
        // ```
        // $ cmake --version
        // cmake version 3.22.2
        //
        // CMake suite maintained and supported by Kitware (kitware.com/cmake).
        // ```
        let version = s.lines().next()?.strip_prefix("cmake version ")?;
        let mut digits = version.splitn(3, '.'); // split version string to major minor patch
        let major = digits.next()?.parse::<u32>().ok()?;
        let minor = digits.next()?.parse::<u32>().ok()?;
        // Ignore the patch version because it does not change the API.
        Some(Version::new(major, minor))
    }

    fn from_command(executable: &OsStr) -> Option<Self> {
        Self::from_query(&mut Command::new(executable))
    }

    fn from_query(command: &mut Command) -> Option<Self> {
        VersionObservation::from_query(command).map(|observation| observation.api)
    }
}

// API capability and reported tool selection are different observations: patch
// releases share the former, but must not silently share a request cache key.
#[derive(Debug, PartialEq, Eq)]
struct VersionObservation {
    api: Version,
    reported_line: String,
}

impl VersionObservation {
    fn from_query(command: &mut Command) -> Option<Self> {
        let output = command.arg("--version").output().ok()?;
        Self::from_response(output.status.success(), &output.stdout)
    }

    fn from_response(success: bool, stdout: &[u8]) -> Option<Self> {
        if !success {
            return None;
        }
        // Preserve the legacy whole-output UTF8 requirement, even for body
        // text which is not part of the version observation or key.
        let stdout = core::str::from_utf8(stdout).ok()?;
        let api = Version::parse(stdout)?;
        let reported_line = stdout.lines().next()?.to_owned();
        Some(Self { api, reported_line })
    }

    fn append_cache_inputs(&self, bytes: &mut Vec<u8>) {
        frame(bytes, &self.api.major.to_le_bytes());
        frame(bytes, &self.api.minor.to_le_bytes());
        frame(bytes, self.reported_line.as_bytes());
    }
}

impl Default for Version {
    fn default() -> Self {
        // If the version parsing fails, we assume that it is the latest known
        // version. This is because the failure of version parsing may be due to
        // the version output being changed.
        Self::new(3, 22)
    }
}

fn run(cmd: &mut Command, program: &str) {
    println!("running: {:?}", cmd);
    let status = match cmd.status() {
        Ok(status) => status,
        Err(ref e) if e.kind() == ErrorKind::NotFound => {
            fail(&format!("failed to execute command: {}\nis `{}` not installed?", e, program));
        }
        Err(e) => fail(&format!("failed to execute command: {}", e)),
    };
    if !status.success() {
        if status.code() == Some(127) {
            fail(&format!(
                "command did not execute successfully, got: {}, is `{}` not installed?",
                status, program
            ));
        }
        fail(&format!("command did not execute successfully, got: {}", status));
    }
}

fn find_exe(path: &Path) -> PathBuf {
    env::split_paths(&env::var_os("PATH").unwrap_or_default())
        .map(|p| p.join(path))
        .find(|p| fs::metadata(p).is_ok())
        .unwrap_or_else(|| path.to_owned())
}

fn getenv_unwrap(v: &str) -> String {
    match env::var(v) {
        Ok(s) => s,
        Err(..) => fail(&format!("environment variable `{}` not defined", v)),
    }
}

fn fail(s: &str) -> ! {
    panic!("\n{}\n\nbuild script failed, must exit now", s)
}

/// Returns whether the given MAKEFLAGS indicate that there is an available
/// jobserver that uses a named pipe (fifo)
fn uses_named_pipe_jobserver(makeflags: &OsStr) -> bool {
    makeflags
        .to_string_lossy()
        // auth option as defined in
        // https://www.gnu.org/software/make/manual/html_node/POSIX-Jobserver.html#POSIX-Jobserver
        .contains("--jobserver-auth=fifo:")
}

#[cfg(test)]
mod tests {
    use super::{Version, uses_named_pipe_jobserver};

    #[test]
    fn test_cmake_version() {
        let text = "cmake version 3.22.2

CMake suite maintained and supported by Kitware (kitware.com/cmake).
";
        let v = Version::parse(text).unwrap();
        assert_eq!(v, Version::new(3, 22));
        assert!(Version::new(3, 22) > Version::new(3, 21));
        assert!(Version::new(3, 22) < Version::new(3, 23));

        // Actual program execution is covered by the maintained manual NONE
        // project, not an unowned external smoke in the default pure suite.
    }

    #[test]
    fn test_uses_fifo_jobserver() {
        assert!(uses_named_pipe_jobserver("-j --jobserver-auth=fifo:/foo".as_ref()));
        assert!(!uses_named_pipe_jobserver("-j --jobserver-auth=8:9".as_ref()));
    }
}

#[cfg(test)]
mod prepared_tests {
    use super::*;

    fn selector() -> Config {
        let mut config = Config::new(".");
        config.host("host-triple").target("target-triple");
        config
    }

    #[test]
    fn selector_observes_absent_predecessors_and_ignores_shadowed_values() {
        let names = ["CMAKE_target-triple", "CMAKE_target_triple", "TARGET_CMAKE", "CMAKE"];
        for winner in 0..names.len() {
            let mut config = selector();
            let selected = config.getenv_target_os_with("CMAKE", &mut |name| {
                names
                    .iter()
                    .position(|candidate| *candidate == name)
                    .filter(|index| *index >= winner)
                    .map(|index| OsString::from(format!("selected-{index}")))
            });
            assert_eq!(selected, Some(OsString::from(format!("selected-{winner}"))));
            assert_eq!(config.env_cache.len(), winner + 1);
            for absent in &names[..winner] {
                assert_eq!(config.env_cache.get(*absent), Some(&None));
            }
            for shadowed in &names[winner + 1..] {
                assert!(!config.env_cache.contains_key(*shadowed));
            }
        }
        let mut config = selector();
        assert_eq!(
            config.getenv_target_os_with("CMAKE", &mut |_| Some(OsString::new())),
            Some(OsString::new())
        );
        assert_eq!(config.env_cache.len(), 1);
        let mut host = selector();
        host.target("host-triple");
        assert_eq!(
            host.getenv_target_os_with("CMAKE", &mut |name| (name == "HOST_CMAKE")
                .then(|| "host-program".into())),
            Some("host-program".into())
        );
    }

    #[test]
    fn a_cache_root_is_written_as_a_token_only_where_it_stands_as_a_whole_path() {
        let roots = [PathBuf::from("/w/one"), PathBuf::from("/w/one/build/")];
        let token = |text: &str| relocated(text.as_bytes(), &roots).into_owned();
        // The same request in two trees: equal once each names its own root.
        let other = [PathBuf::from("/elsewhere/two"), PathBuf::from("/elsewhere/two/build")];
        assert_eq!(
            token("-DCMAKE_INSTALL_PREFIX=/w/one/build/llvm;/w/one"),
            relocated(b"-DCMAKE_INSTALL_PREFIX=/elsewhere/two/build/llvm;/elsewhere/two", &other)
                .into_owned()
        );
        assert_eq!(token("/w/one/src"), b"\0trust-cmake-root-0\0/src".to_vec());
        // Another directory that only begins with the root's spelling keeps it.
        for kept in ["/w/one-two/src", "/w/oneself", "/x/w/one", "/w/one.d"] {
            assert_eq!(token(kept), kept.as_bytes().to_vec(), "{kept}");
        }
        assert_eq!(relocated(b"/", &[PathBuf::from("/")]).into_owned(), b"/".to_vec());
        // No root, no change: the key of a configuration that names none is as before.
        assert!(matches!(relocated(b"/w/one", &[]), std::borrow::Cow::Borrowed(_)));
    }

    #[test]
    fn invalid_prepare_does_not_mutate_the_original_configuration() {
        let mut config = selector();
        config.target("").profile("Release").out_dir("output-never-created");
        config.define("CMAKE_BUILD_TYPE", "Release");
        let defines = config.defines.clone();
        let observations = config.env_cache.clone();
        assert!(config.try_prepare().is_err());
        assert_eq!(config.defines, defines);
        assert_eq!(config.env_cache, observations);
    }

    #[test]
    fn resolver_failure_after_auto_defines_is_transactional() {
        let mut config = selector();
        // cc rejects the unsupported target architecture before selecting or
        // probing a compiler. The redox branch first adds CMAKE_SYSTEM_NAME.
        config
            .target("unsupported-redox-target")
            .host("x86_64-unknown-linux-gnu")
            .profile("Release")
            .out_dir("transaction-output-must-not-exist");
        let defines = config.defines.clone();
        let observations = config.env_cache.clone();
        let error = config.try_prepare();
        assert!(error.is_err());
        assert_eq!(config.defines, defines);
        assert_eq!(config.env_cache, observations);
    }

    #[test]
    fn opaque_configuration_disables_reuse_without_changing_its_operations() {
        let mut config = selector();
        let ninja = Some(OsString::from("Ninja"));
        assert!(reusable_configuration(&config, &ninja, "native-target"));
        config.target = None;
        assert!(!reusable_configuration(&config, &ninja, "wasm32-unknown-emscripten"));
        assert!(reusable_configuration(&config, &ninja, "native-target"));
        config.build_arg("-j1").build_arg("--quiet");
        assert!(reusable_configuration(&config, &ninja, "native-target"));
        assert!(!reusable_configuration(&config, &None, "native-target"));
        config.define("CMAKE_TOOLCHAIN_FILE", "toolchain.cmake");
        assert!(!reusable_configuration(&config, &ninja, "native-target"));
        assert_eq!(config.defines.last().unwrap().1, "toolchain.cmake");
        let mut custom = selector();
        custom.configure_arg("-Cinitial-cache.cmake");
        assert!(!reusable_configuration(&custom, &ninja, "native-target"));
        let mut semantic = selector();
        semantic.build_arg("semantic-target-option");
        assert!(!reusable_configuration(&semantic, &ninja, "native-target"));
    }

    #[test]
    fn production_job_pair_is_execution_only_but_malformed_or_semantic_args_are_not() {
        let args =
            |values: &[&str]| values.iter().map(|value| OsString::from(*value)).collect::<Vec<_>>();
        for values in
            [&["-j", "1"][..], &["--quiet", "-j", "1"][..], &["-j1"][..], &["-j4294967295"][..]]
        {
            let mut config = selector();
            for value in values {
                config.build_arg(value);
            }
            assert!(reusable_configuration(&config, &Some("Ninja".into()), "native-target"));
            assert_eq!(config.build_args, args(values));
        }
        for values in [
            &["-j"][..],
            &["-j", "--quiet"][..],
            &["-j", "no"][..],
            &["-j", "0"][..],
            &["-j0"][..],
            &["-j4294967296"][..],
            &["-j", "4294967296"][..],
            &["semantic-target-option"][..],
        ] {
            assert!(!execution_only_build_args(&args(values)), "{values:?}");
        }
    }

    #[test]
    fn actual_output_selection_anchors_explicit_and_fallback_only_during_preparation() {
        let parent_cwd = env::current_dir().unwrap();
        let relative = Path::new("not-created/../relative-output");
        let explicit = output_directory(Some(relative), Some(&parent_cwd), || {
            panic!("explicit output must not query OUT_DIR")
        })
        .unwrap();
        assert_eq!(explicit, parent_cwd.join(relative));
        assert!(explicit.is_absolute());
        let fallback =
            output_directory(None, Some(&parent_cwd), || relative.to_path_buf()).unwrap();
        assert_eq!(fallback, explicit);
        let absolute = parent_cwd.join("absolute-output");
        assert_eq!(
            output_directory(Some(&absolute), Some(&parent_cwd), || panic!("unused fallback"))
                .unwrap(),
            absolute
        );
        assert_eq!(
            output_directory(Some(relative), None, || panic!("unused fallback")).unwrap(),
            relative
        );
        assert_eq!(output_directory(None, None, || relative.to_path_buf()).unwrap(), relative);
    }

    #[test]
    fn reported_patch_and_suffix_changes_keys_without_changing_api_capability() {
        // These are decoder inputs, not executed program-query evidence.
        let observed =
            |text: &str| VersionObservation::from_response(true, text.as_bytes()).unwrap();
        let key = |observation: &VersionObservation| {
            let mut bytes = Vec::new();
            observation.append_cache_inputs(&mut bytes);
            bytes
        };
        let base = observed("cmake version 4.4.5\nCopyright body\n");
        for report in
            ["cmake version 4.4.6\n", "cmake version 4.4.5-rc1\n", "cmake version 4.4.5+vendor\n"]
        {
            let changed = observed(report);
            assert_eq!(base.api, changed.api);
            assert_ne!(key(&base), key(&changed));
        }
        let crlf = observed("cmake version 4.4.5\r\nDifferent copyright body\r\n");
        assert_eq!(base, crlf);
        assert_eq!(key(&base), key(&crlf));
        assert_eq!(base.api, Version::new(4, 4));
        let trailing_space = observed("cmake version 4.4.5 \n");
        assert_ne!(key(&base), key(&trailing_space));
    }

    #[test]
    fn failed_or_malformed_full_response_cannot_supply_version_evidence() {
        assert!(VersionObservation::from_response(false, b"cmake version 4.4.5\n").is_none());
        for bytes in [
            &b""[..],
            &b"other version 4.4.5\n"[..],
            &b"cmake version x.4.5\n"[..],
            &b"cmake version 4.x.5\n"[..],
            &b"cmake version 4294967296.4.5\n"[..],
            &b"cmake version 4.4.5\ninvalid body \xff"[..],
        ] {
            assert!(VersionObservation::from_response(true, bytes).is_none(), "{bytes:?}");
        }
    }

    #[test]
    fn frames_distinguish_sequence_boundaries_and_non_utf8_bytes() {
        let mut left = Vec::new();
        frame(&mut left, b"a");
        frame(&mut left, b"bc");
        let mut right = Vec::new();
        frame(&mut right, b"ab");
        frame(&mut right, b"c");
        assert_ne!(left, right);
        let mut other = Vec::new();
        frame(&mut other, &[0xff]);
        assert_ne!(other, vec![0xff]);
    }

    #[cfg(unix)]
    #[test]
    fn search_selection_is_frozen_with_its_request_without_global_env_mutation() {
        use std::os::unix::fs::PermissionsExt;
        use std::sync::atomic::{AtomicU64, Ordering};
        static NEXT: AtomicU64 = AtomicU64::new(0);
        struct Scratch(PathBuf);
        impl Drop for Scratch {
            fn drop(&mut self) {
                let _ = fs::remove_dir_all(&self.0);
            }
        }
        let scratch = Scratch(env::temp_dir().join(format!(
            "trust-cmake-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        )));
        let first = scratch.0.join("first");
        let second = scratch.0.join("second");
        fs::create_dir_all(&first).unwrap();
        fs::create_dir_all(&second).unwrap();
        for dir in [&first, &second] {
            let path = dir.join("cmake");
            fs::write(&path, b"metadata-only executable selection fixture").unwrap();
            fs::set_permissions(&path, fs::Permissions::from_mode(0o700)).unwrap();
        }
        let parent_cwd = env::current_dir().unwrap();
        let mut command = Command::new("cmake");
        command.env("PATH", &first);
        let mut observation = Vec::new();
        assert!(freeze_program(&mut command, &mut observation, &parent_cwd));
        assert_eq!(command.get_program(), first.join("cmake").as_os_str());
        command.env("PATH", &second);
        assert_eq!(command.get_program(), first.join("cmake").as_os_str());
        let mut other = Command::new("cmake");
        other.env("PATH", &second);
        let mut changed = Vec::new();
        assert!(freeze_program(&mut other, &mut changed, &parent_cwd));
        assert_ne!(observation, changed);
        let mut unsupported = Command::new("cmake");
        unsupported.env("PATH", ".");
        assert!(!freeze_program(&mut unsupported, &mut Vec::new(), &parent_cwd));
    }
    #[cfg(unix)]
    #[test]
    fn typed_program_binding_uses_effective_environment_and_later_overrides_are_opaque() {
        use std::os::unix::fs::PermissionsExt;
        let root = env::temp_dir().join(format!("trust-cmake-inputs-{}", std::process::id()));
        fs::create_dir(&root).unwrap();
        struct Scratch(PathBuf);
        impl Drop for Scratch {
            fn drop(&mut self) {
                let _ = fs::remove_dir_all(&self.0);
            }
        }
        let _scratch = Scratch(root.clone());
        let tool = root.join("tool");
        let explicit = root.join("explicit");
        fs::create_dir_all(&tool).unwrap();
        fs::create_dir_all(&explicit).unwrap();
        for dir in [&tool, &explicit] {
            let path = dir.join("ninja");
            fs::write(&path, b"inert namespace fixture").unwrap();
            fs::set_permissions(path, fs::Permissions::from_mode(0o700)).unwrap();
        }
        let mut config = Config::new(&root);
        config.define_input_program("CMAKE_MAKE_PROGRAM", &[OsStr::new("ninja")]);
        config.env("PATH", &explicit);
        config.bind_input_programs(&root, &[("PATH".into(), tool.as_os_str().to_owned())]).unwrap();
        assert_eq!(config.defines[0].1, explicit.join("ninja").as_os_str());
        assert!(!config.cleanup_is_opaque());
        config.define("CMAKE_MAKE_PROGRAM", tool.join("ninja"));
        assert!(
            config.cleanup_is_opaque(),
            "untyped last definition can replace the selected program"
        );
        let mut shadowed = Config::new(&root);
        shadowed.define_input_program(
            "CMAKE_MAKE_PROGRAM",
            &[OsStr::new("unavailable-shadowed-program")],
        );
        shadowed.define("CMAKE_MAKE_PROGRAM", explicit.join("ninja"));
        shadowed.env("PATH", &explicit);
        shadowed.bind_input_programs(&root, &[]).unwrap();
        assert!(shadowed.cleanup_is_opaque());
        assert_eq!(shadowed.defines[0].1, "unavailable-shadowed-program");
    }

    #[test]
    fn consumed_prefix_paths_are_retained_and_toolchains_are_opaque() {
        let cwd = env::current_dir().unwrap();
        let mut config = Config::new(&cwd);
        config.target("x86_64-unknown-linux-gnu").host("x86_64-unknown-linux-gnu");
        let prefix = cwd.join("selected-prefix");
        config.env_cache.insert(
            "CMAKE_PREFIX_PATH_x86_64-unknown-linux-gnu".into(),
            Some(prefix.as_os_str().to_owned()),
        );
        assert_eq!(
            config.resolve_prefix_paths(&cwd.join("build"), true).unwrap(),
            prefix.as_os_str()
        );
        assert_eq!(config.selected_paths, [prefix]);
        config.define_input_program("CMAKE_MAKE_PROGRAM", &[OsStr::new("ninja")]);
        assert!(!config.cleanup_is_opaque());
        config.define("CMAKE_TOOLCHAIN_FILE", "opaque.cmake");
        assert!(config.cleanup_is_opaque());
    }
    #[test]
    fn execution_budget_arguments_keep_commands_but_normalize_selected_identity() {
        let request = |jobs: &str| {
            let mut config = Config::new(".");
            config.define("SEMANTIC_INPUT", "ON").define_execution_budget("CAPACITY", jobs);
            config
        };
        let observe = |config: &Config| {
            let mut command = Command::new("cmake");
            command.arg("source");
            let execution = config.append_definitions(&mut command);
            let mut bytes = Vec::new();
            frame_selected_args(&mut bytes, &command, &execution, &[]);
            (command, bytes)
        };
        let first = request("1");
        let second = request("2");
        let (one, one_key) = observe(&first);
        let (two, two_key) = observe(&second);
        assert_ne!(one.get_args().collect::<Vec<_>>(), two.get_args().collect::<Vec<_>>());
        assert_eq!(one_key, two_key);
        let mut extra_budget = request("2");
        extra_budget.define_execution_budget("LINK_CAPACITY", "3");
        let (extra, extra_key) = observe(&extra_budget);
        assert_eq!(extra.get_args().count(), one.get_args().count() + 1);
        assert_eq!(
            one_key, extra_key,
            "the normalized argument count excludes tagged positions too"
        );
        assert_eq!(one.get_args().last(), Some(OsStr::new("-DCAPACITY=1")));
        let mut user_last = request("1");
        user_last.define("CAPACITY", "user-last");
        let (_, changed) = observe(&user_last);
        assert_ne!(one_key, changed, "untyped user definitions remain requested configuration");
        let mut semantic = request("1");
        semantic.define("SEMANTIC_INPUT", "OFF");
        assert_ne!(one_key, observe(&semantic).1);
    }
}
