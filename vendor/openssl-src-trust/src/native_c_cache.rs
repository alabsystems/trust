mod compiler;
mod runtime;
mod store;

use compiler::Compiler;
use sha2::{Digest, Sha256};
use std::ffi::{OsStr, OsString};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use store::Store;

#[derive(Debug)]
pub(crate) enum Decline {
    UnsupportedProfile(&'static str),
    CustomInput(String),
    CompilerCustody(String),
    StoreCustody(String),
    InputCustody(String),
}
impl std::fmt::Display for Decline {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let (code, detail) = match self {
            Self::UnsupportedProfile(detail) => ("unsupported-profile", *detail),
            Self::CustomInput(detail) => ("custom-native-input", detail.as_str()),
            Self::CompilerCustody(detail) => ("compiler-custody", detail.as_str()),
            Self::StoreCustody(detail) => ("store-custody", detail.as_str()),
            Self::InputCustody(detail) => ("input-custody", detail.as_str()),
        };
        write!(f, "{code}:{detail}")
    }
}
impl From<String> for Decline {
    fn from(value: String) -> Self {
        Self::InputCustody(value)
    }
}
impl From<&str> for Decline {
    fn from(value: &str) -> Self {
        Self::InputCustody(value.into())
    }
}

/// Live, non-serializable native action-cache custody. Clang still regenerates
/// its include tree for every action; the Rust wrapper's fingerprint is never
/// used as the identity of a C compilation.
pub(crate) struct Session {
    compiler: Compiler,
    store: Store,
    removed_environment: Vec<OsString>,
    environment: std::collections::BTreeMap<OsString, OsString>,
}

impl Session {
    pub fn prepare(
        target: &str,
        host: &str,
        source: &str,
        command: &Command,
        compiler_args: &[OsString],
    ) -> Result<Self, Decline> {
        if target != "aarch64-apple-darwin" || host != target {
            return Err(Decline::UnsupportedProfile("unsupported-native-target"));
        }
        // This supported source profile excludes external assembler file
        // directives, compiler plugins and custom Configure recipes. Changed
        // bundles continue to compile normally until separately qualified.
        if source != "d5d281dd021deccf64a2516567c42c76ba50d14c8587ac24c9bb4373854a2f90" {
            return Err(Decline::UnsupportedProfile(
                "unqualified-native-source-profile",
            ));
        }
        for (key, _) in std::env::vars_os() {
            let key = key.to_string_lossy();
            if key == "CFLAGS"
                || key.starts_with("CFLAGS_")
                || key.ends_with("_CFLAGS")
                || key == "CPPFLAGS"
                || key == "ASFLAGS"
                || key == "CC"
                || key.starts_with("CC_")
                || key.ends_with("_CC")
                || key == "PERL5OPT"
                || key == "PERL5LIB"
                || key == "CROSS_COMPILE"
                || key == "AR"
                || key.starts_with("AR_")
                || key.ends_with("_AR")
                || key == "ARFLAGS"
                || key == "RANLIB"
                || key.starts_with("RANLIB_")
                || key.ends_with("_RANLIB")
                || key == "RANLIBFLAGS"
                || key == "PERL"
                || key == "OPENSSL_SRC_PERL"
                || key == "DEVELOPER_DIR"
                || key == "TOOLCHAINS"
            {
                return Err(Decline::CustomInput(key.into_owned()));
            }
        }
        if !compiler_argument_profile(compiler_args) {
            return Err(Decline::UnsupportedProfile(
                "unqualified-native-compiler-arguments",
            ));
        }
        let cc = command
            .get_envs()
            .find_map(|(key, value)| (key == "CC").then_some(value).flatten())
            .ok_or("native compiler absent")?;
        let path = command
            .get_envs()
            .find_map(|(key, value)| (key == "PATH").then_some(value))
            .map(|value| value.map(OsStr::to_owned).unwrap_or_default())
            .unwrap_or_else(|| std::env::var_os("PATH").unwrap_or_default());
        if compiler::resolve_candidate(Path::new(command.get_program()), &path)?
            != Path::new("/usr/bin/perl")
                .canonicalize()
                .map_err(|e| e.to_string())?
            || compiler::resolve_candidate(Path::new("make"), &path)?
                != Path::new("/usr/bin/make")
                    .canonicalize()
                    .map_err(|e| e.to_string())?
        {
            return Err(Decline::UnsupportedProfile(
                "custom-generator-or-make-recipe",
            ));
        }
        let compiler =
            Compiler::capture(Path::new(cc), command).map_err(Decline::CompilerCustody)?;
        let mut hash = Sha256::new();
        hash.update(b"trust.openssl-native-c-store.v2\0");
        hash.update(source.as_bytes());
        hash.update(target.as_bytes());
        hash.update(compiler.digest);
        // Define the actual child environment instead of guessing that
        // arbitrary inherited inputs cannot affect this fixed compiler.
        // Rust unit metadata is removed from the native recipe itself. Every
        // remaining value is bound, except actual owned scheduling transports.
        let mut environment = std::env::vars_os().collect::<std::collections::BTreeMap<_, _>>();
        for (key, value) in command.get_envs() {
            match value {
                Some(value) => {
                    environment.insert(key.to_owned(), value.to_owned());
                }
                None => {
                    environment.remove(key);
                }
            }
        }
        environment.insert("CC".into(), compiler.path.clone().into_os_string());
        let mut removed_environment = environment
            .keys()
            .filter(|key| wrapper_environment(key))
            .cloned()
            .collect::<Vec<_>>();
        removed_environment.extend(
            command
                .get_envs()
                .filter_map(|(key, value)| value.is_none().then(|| key.to_owned())),
        );
        for key in &removed_environment {
            environment.remove(key);
        }
        for key in [
            "CARGO_MAKEFLAGS",
            "MAKEFLAGS",
            "MFLAGS",
            jobserver_utils::DESCENDANT_HANDOFF_ENV,
        ] {
            environment.remove(OsStr::new(key));
        }
        let mut diagnostic = format!("compiler {:02x?}\n", compiler.digest);
        for (key, value) in &environment {
            hash.update((key.as_encoded_bytes().len() as u64).to_le_bytes());
            hash.update(key.as_encoded_bytes());
            hash.update((value.as_encoded_bytes().len() as u64).to_le_bytes());
            hash.update(value.as_encoded_bytes());
            diagnostic.push_str(&format!(
                "{key:?} {:02x?}\n",
                Sha256::digest(value.as_encoded_bytes())
            ));
        }
        let key: String = hash.finalize().iter().map(|b| format!("{b:02x}")).collect();
        let home = std::env::var_os("CARGO_HOME")
            .map(PathBuf::from)
            .or_else(|| std::env::var_os("HOME").map(|p| PathBuf::from(p).join(".cargo")))
            .ok_or("native cache has no owned home")?;
        let root = home.join("trust/native-c/openssl-v1").join(key);
        if !root.is_absolute()
            || root.to_str().is_none()
            || root.components().any(|part| {
                matches!(
                    part,
                    std::path::Component::ParentDir | std::path::Component::CurDir
                )
            })
            || !root
                .as_os_str()
                .as_encoded_bytes()
                .iter()
                .all(|b| b.is_ascii_alphanumeric() || matches!(b, b'/' | b'.' | b'_' | b'-'))
        {
            return Err("native cache root requires Configure-safe path".into());
        }
        let store = Store::acquire(root).map_err(Decline::StoreCustody)?;
        // Private diagnostic only; neither this description nor its persisted
        // hashes can mint cache, compiler or proof authority.
        use std::io::Write;
        use std::os::unix::fs::OpenOptionsExt;
        match fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o600)
            .custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC)
            .open(store.root.join("recipe-inputs.diagnostic"))
        {
            Ok(mut file) => file
                .write_all(diagnostic.as_bytes())
                .map_err(|e| e.to_string())?,
            Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => {}
            Err(e) => return Err(e.to_string().into()),
        }
        compiler.check_current()?;
        let session = Self {
            compiler,
            store,
            removed_environment,
            environment,
        };
        session.probe()?;
        Ok(session)
    }

    fn probe(&self) -> Result<(), String> {
        use std::io::Write;
        use std::os::unix::fs::OpenOptionsExt;
        let source = self.store.root.join("capability.c");
        match fs::remove_file(&source) {
            Ok(()) => {}
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
            Err(e) => return Err(e.to_string()),
        }
        let mut file = fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o600)
            .custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC)
            .open(&source)
            .map_err(|e| e.to_string())?;
        file.write_all(b"int trust_native_cache_capability(void) { return 17; }\n")
            .map_err(|e| e.to_string())?;
        drop(file);
        let output = self.store.root.join("capability.o");
        match fs::remove_file(&output) {
            Ok(()) => {}
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
            Err(e) => return Err(e.to_string()),
        }
        let mut command = Command::new(&self.compiler.path);
        command
            .args([
                "--no-default-config",
                "-fdepscan=inline",
                "-Xclang=-fcache-compile-job",
                "-Xclang=-fcas-path",
            ])
            .arg(format!("-Xclang={}", self.store.root.join("cas").display()))
            .args(["-Rcompile-job-cache", "-x", "c", "-c"])
            .arg(&source)
            .arg("-o")
            .arg(output);
        self.command(&mut command)?;
        let remarks = compiler::bounded_selection(command, true)?;
        self.check_current()?;
        println!("Trust native C cache capability: two driver-plan checks, one fresh dependency/compiler action; {}",
            String::from_utf8_lossy(&remarks).trim());
        Ok(())
    }

    pub fn install(&self) -> PathBuf {
        self.store.root.join("install")
    }
    pub fn source(&self) -> PathBuf {
        self.store.root.join("build/src")
    }

    pub fn configure(&self, command: Command) -> Result<Command, String> {
        let mut args = command.get_args().map(OsStr::to_owned).collect::<Vec<_>>();
        if args.first().is_none_or(|a| a != "./Configure")
            || args
                .get(1)
                .is_none_or(|a| !a.as_encoded_bytes().starts_with(b"--prefix="))
        {
            return Err("native Configure prefix slot changed".into());
        }
        args[1] = format!("--prefix={}", self.install().display()).into();
        let mut admitted = Command::new(command.get_program());
        admitted.args(args);
        for (key, value) in command.get_envs() {
            match value {
                Some(value) => {
                    admitted.env(key, value);
                }
                None => {
                    admitted.env_remove(key);
                }
            }
        }
        admitted
            .env("CC", &self.compiler.path)
            .args([
                "--no-default-config",
                "-fdepscan=inline",
                "-Xclang=-fcache-compile-job",
                "-Xclang=-fcas-path",
            ])
            .arg(format!("-Xclang={}", self.store.root.join("cas").display()))
            .arg("-Rcompile-job-cache");
        Ok(admitted)
    }

    pub fn stage(&self, input: &Path, source_hash: &str) -> Result<(), String> {
        self.check_current()?;
        for path in [self.store.root.join("build"), self.install()] {
            if path.exists() {
                fs::remove_dir_all(path).map_err(|e| e.to_string())?;
            }
        }
        fs::create_dir_all(self.source()).map_err(|e| e.to_string())?;
        let copied = crate::native_recipe::copy_source(input, &self.source())?;
        if copied != source_hash {
            return Err("native source changed while entering owned recipe root".into());
        }
        self.check_current()
    }

    pub fn command(&self, command: &mut Command) -> Result<(), String> {
        self.check_current()?;
        freeze_native_environment(command, &self.environment, &self.removed_environment);
        self.store.configure(command)
    }

    pub fn check_current(&self) -> Result<(), String> {
        self.store.check_current()?;
        self.compiler.check_current()
    }

    pub fn finish(&self) -> Result<(), String> {
        self.check_current()?;
        let digest = self.store.finish()?;
        println!("Trust native C action cache: previous={} closed_store={} reset={} (fresh dependency scans; native hit/miss remarks report codegen reuse)",
            self.store.previous, digest, self.store.reset_reason.as_deref().unwrap_or("none"));
        Ok(())
    }
}

fn compiler_argument_profile(arguments: &[OsString]) -> bool {
    let mut arguments = arguments.iter();
    while let Some(argument) = arguments.next() {
        let Some(argument) = argument.to_str() else {
            return false;
        };
        if argument == "-arch" {
            if arguments.next().is_none_or(|arg| arg != "arm64") {
                return false;
            }
        } else if matches!(
            argument,
            "-O0"
                | "-O1"
                | "-O2"
                | "-O3"
                | "-Os"
                | "-Oz"
                | "-ffunction-sections"
                | "-fdata-sections"
                | "-fPIC"
                | "-g"
                | "-w"
                | "-gdwarf-2"
                | "-gdwarf-3"
                | "-gdwarf-4"
                | "-gdwarf-5"
                | "-fno-omit-frame-pointer"
                | "-mno-omit-leaf-frame-pointer"
                | "--target=arm64-apple-macosx"
        ) {
        } else if let Some(version) = argument.strip_prefix("-mmacosx-version-min=") {
            if version.is_empty()
                || version.len() > 32
                || !version.bytes().all(|b| b.is_ascii_digit() || b == b'.')
            {
                return false;
            }
        } else {
            return false;
        }
    }
    true
}

fn freeze_native_environment(
    command: &mut Command,
    environment: &std::collections::BTreeMap<OsString, OsString>,
    removed: &[OsString],
) {
    let owned_transport = command
        .get_envs()
        .filter(|(key, _)| transport_environment(key))
        .map(|(key, value)| (key.to_owned(), value.map(OsStr::to_owned)))
        .collect::<Vec<_>>();
    command.env_clear().envs(environment);
    for key in removed {
        command.env_remove(key);
    }
    // Configure/probes have no GNU scheduling handoff. Make receives only
    // the caller's explicit actual transport, never stale ambient FD strings.
    for key in [
        "CARGO_MAKEFLAGS",
        "MAKEFLAGS",
        "MFLAGS",
        jobserver_utils::DESCENDANT_HANDOFF_ENV,
    ] {
        command.env_remove(key);
    }
    for (key, value) in owned_transport {
        match value {
            Some(value) => {
                command.env(key, value);
            }
            None => {
                command.env_remove(key);
            }
        }
    }
}

fn transport_environment(key: &OsStr) -> bool {
    key == "CARGO_MAKEFLAGS"
        || key == "MAKEFLAGS"
        || key == "MFLAGS"
        || key == jobserver_utils::DESCENDANT_HANDOFF_ENV
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unqualified_plugin_lto_and_external_assembler_flags_decline_before_cache_effects() {
        let command = Command::new("perl");
        for argument in [
            "-fplugin=/unbound/plugin.dylib",
            "-flto",
            "-fno-integrated-as",
            "-Xclang=-load",
        ] {
            let reason = Session::prepare(
                "aarch64-apple-darwin",
                "aarch64-apple-darwin",
                "d5d281dd021deccf64a2516567c42c76ba50d14c8587ac24c9bb4373854a2f90",
                &command,
                &[argument.into()],
            )
            .err()
            .unwrap();
            assert!(
                matches!(
                    reason,
                    Decline::UnsupportedProfile("unqualified-native-compiler-arguments")
                ),
                "{reason}"
            );
        }
    }

    #[test]
    fn custom_cross_compile_declines_before_cache_effects_and_retains_ordinary_environment() {
        const CHILD: &str = "TRUST_NATIVE_CUSTOM_CROSS_TEST";
        if std::env::var_os(CHILD).is_some() {
            assert_eq!(
                std::env::var("CROSS_COMPILE").unwrap(),
                "custom-original-prefix-"
            );
            let mut configure = Command::new("perl");
            configure.arg("./Configure").env("CC", "cc");
            let reason = Session::prepare(
                "aarch64-apple-darwin",
                "aarch64-apple-darwin",
                "d5d281dd021deccf64a2516567c42c76ba50d14c8587ac24c9bb4373854a2f90",
                &configure,
                &[],
            )
            .err()
            .unwrap();
            assert!(
                matches!(reason, Decline::CustomInput(ref key) if key == "CROSS_COMPILE"),
                "{reason}"
            );
            assert_eq!(
                std::env::var("CROSS_COMPILE").unwrap(),
                "custom-original-prefix-"
            );
            assert!(!PathBuf::from(std::env::var_os("CARGO_HOME").unwrap())
                .join("trust")
                .exists());
            return;
        }
        let temp = tempfile::tempdir().unwrap();
        let output = Command::new(std::env::current_exe().unwrap())
            .args(["--exact", "native_c_cache::tests::custom_cross_compile_declines_before_cache_effects_and_retains_ordinary_environment"])
            .env(CHILD, "1").env("CARGO_HOME", temp.path())
            .env("CROSS_COMPILE", "custom-original-prefix-").output().unwrap();
        assert!(
            output.status.success(),
            "{}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }

    #[test]
    fn actual_native_child_excludes_agent_metadata_and_retains_bound_inputs() {
        let ambient = std::collections::BTreeMap::from([
            (
                OsString::from("CODEX_TOOL_CALL_ID"),
                OsString::from("per-command-random-context"),
            ),
            (
                OsString::from("OUT_DIR"),
                OsString::from("foreign-rust-unit"),
            ),
            (OsString::from("SOURCE_DATE_EPOCH"), OsString::from("17")),
            (
                OsString::from("BOUND_NATIVE_INPUT"),
                OsString::from("exact value"),
            ),
        ]);
        let removed = ambient
            .keys()
            .filter(|key| wrapper_environment(key))
            .cloned()
            .collect::<Vec<_>>();
        assert!(removed.contains(&OsString::from("CODEX_TOOL_CALL_ID")));
        let retained = ambient
            .into_iter()
            .filter(|(key, _)| !wrapper_environment(key))
            .collect();
        let mut child = Command::new("/usr/bin/env");
        freeze_native_environment(&mut child, &retained, &removed);
        let output = child.output().unwrap();
        assert!(output.status.success());
        let text = String::from_utf8(output.stdout).unwrap();
        assert!(text.contains("SOURCE_DATE_EPOCH=17\n"));
        assert!(text.contains("BOUND_NATIVE_INPUT=exact value\n"));
        assert!(!text.contains("CODEX_TOOL_CALL_ID="));
        assert!(!text.contains("OUT_DIR="));
        assert!(!text.contains("CARGO_MAKEFLAGS="));
    }
}

fn wrapper_environment(key: &OsStr) -> bool {
    if key == "CARGO_MAKEFLAGS" || key == jobserver_utils::DESCENDANT_HANDOFF_ENV {
        return false;
    }
    let key = key.as_encoded_bytes();
    [
        b"CARGO_".as_slice(),
        b"TARGO_",
        b"TRUST_",
        b"BUILD_SLOT_",
        b"ATERM_",
        b"ATPKG_",
        b"CODEX_",
        b"CLAUDE",
        b"ANTHROPIC_",
        b"COPILOT_",
        b"ANTIGRAVITY_",
        b"GEMINI_",
        b"CURSOR_",
        b"GROK_",
        b"XAI_",
        b"KIMI_",
        b"MOONSHOT_",
        b"AI_",
        b"_DEVTOOL_",
    ]
    .iter()
    .any(|prefix| key.starts_with(prefix))
        || matches!(
            key,
            b"OUT_DIR"
                | b"TARGET"
                | b"HOST"
                | b"OPT_LEVEL"
                | b"DEBUG"
                | b"NUM_JOBS"
                | b"PWD"
                | b"OLDPWD"
                | b"SHLVL"
                | b"_"
        )
}
