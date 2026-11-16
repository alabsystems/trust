//! Trust: qualify the pinned WP workspace with its own maintained private-driver wrapper.
//!
//! This operation consumes an already installed, read-only current compiler. It
//! does not freeze a live stage2 tree or claim verified execution/read closure.

use std::borrow::Cow;
use std::collections::{BTreeMap, BTreeSet};
use std::ffi::{OsStr, OsString};
use std::path::{Component, Path, PathBuf};
use std::{env, fs};

use sha2::{Digest, Sha256};

use super::{Metadata, add_parsed_configs, cache, cargo_config_inputs, resolve_tool, tools};
use crate::core::builder::Builder;
use crate::utils::exec::{BootstrapCommand, command};

const WORKSPACE: &str = "first-party/trust-wp";
const WRAPPER: &str = "scripts/trustc-private-wrapper.sh";
const BUILD: &[&str] = &[
    "--unverified",
    "build",
    "--release",
    "--locked",
    "--offline",
    "-p",
    "trust-wp-driver",
    "-p",
    "targo-trust-wp",
    "-p",
    "trust-wp-cli",
];
const TEST: &[&str] = &[
    "--unverified",
    "test",
    "--locked",
    "--offline",
    "-p",
    "trust-wp-driver",
    "-p",
    "trust-wp-test-utils",
    "--lib",
    "--bins",
];

fn competing_environment(name: &str) -> bool {
    // Targo's native configuration feeds the Cargo parser snapshot. The
    // process-level validator below applies explicit Cargo-name precedence.
    let name = cargo_config_name(name);
    let name = name.as_ref();
    (name.starts_with("CARGO_BUILD_")
        && !matches!(name, "CARGO_BUILD_JOBS" | "CARGO_BUILD_BUILD_DIR"))
        || (name.starts_with("CARGO_TARGET_") && name != "CARGO_TARGET_DIR")
        || matches!(name, "CARGO_ENCODED_RUSTFLAGS")
        || matches!(
            name,
            "TRUST_PRIVATE_DRIVER_CRATES"
                | "TRUST_WP_CROSS_NATIVE_LIB"
                | "DYLD_LIBRARY_PATH"
                | "DYLD_FALLBACK_LIBRARY_PATH"
                | "LD_LIBRARY_PATH"
        )
}

pub(super) fn validate_environment() -> Result<(), String> {
    validate_environment_values(&env::vars_os().collect())
}

fn cargo_config_name(name: &str) -> Cow<'_, str> {
    match name.strip_prefix("TARGO_") {
        Some(suffix) => Cow::Owned(format!("CARGO_{suffix}")),
        None => Cow::Borrowed(name),
    }
}

// Trust: the installation producer shares this exact native Cargo authority boundary.
pub(super) fn validate_environment_values(
    environment: &BTreeMap<OsString, OsString>,
) -> Result<(), String> {
    // Cargo's home inventory is rooted independently of the child cwd. A
    // relative/empty home cannot name the same configuration under both.
    if let Some(home) = environment.get(OsStr::new("CARGO_HOME")) {
        if home.is_empty() || !Path::new(home).is_absolute() {
            return Err("WP qualification requires an absolute explicit CARGO_HOME".into());
        }
    }
    for (name, value) in environment {
        let Some(text) = name.to_str() else { continue };
        let canonical = cargo_config_name(text);
        if canonical.as_ref() != text && environment.contains_key(OsStr::new(canonical.as_ref())) {
            // Match Targo's entry.or_insert rule, including an explicit empty
            // compatibility value. The compatibility entry is checked itself.
            continue;
        }
        if text == "TARGO_HOME" {
            return Err("effective TARGO_HOME is outside the declared Cargo home inventory; select an absolute CARGO_HOME explicitly".into());
        }
        if value.is_empty() {
            continue;
        }
        if competing_environment(text) {
            return Err(format!(
                "WP qualification cannot accept competing environment input {}",
                name.to_string_lossy()
            ));
        }
    }
    Ok(())
}

pub(super) struct Installation {
    root: PathBuf,
    targo: PathBuf,
    trustc: PathBuf,
    trustdoc: PathBuf,
}

// Trust: the producer reuses these exact refusals before and after publication.
pub(super) fn check_installation(builder: &Builder<'_>, selected: &Path) -> Result<(), String> {
    let source = fs::canonicalize(&builder.src).map_err(|e| e.to_string())?;
    let output = fs::canonicalize(&builder.out).map_err(|e| e.to_string())?;
    Installation::open(selected, &source, &output)?.check_identity(builder)
}

impl Installation {
    fn open(path: &Path, source: &Path, output: &Path) -> Result<Self, String> {
        if !path.is_absolute() {
            return Err("WP installation must be an absolute immutable installation path".into());
        }
        let root = fs::canonicalize(path).map_err(|e| e.to_string())?;
        if root.starts_with(source)
            || root.starts_with(output)
            || root.components().any(|part| {
                matches!(part, Component::Normal(name)
                if name == "build" || name == "stage1" || name == "stage2"
                    || name == "rustc-private-sysroots")
            })
        {
            return Err("WP installation cannot name a live compiler build tree".into());
        }
        readonly_installation(&root)?;
        let tool = |name| {
            let path = root.join("bin").join(name);
            let resolved = fs::canonicalize(&path).map_err(|e| e.to_string())?;
            if !resolved.starts_with(&root) || !resolved.is_file() {
                return Err(format!("WP installation tool escapes its installation: {name}"));
            }
            Ok(path)
        };
        Ok(Self {
            targo: tool("targo")?,
            trustc: tool("trustc")?,
            trustdoc: tool("trustdoc")?,
            root,
        })
    }

    fn check_identity(&self, builder: &Builder<'_>) -> Result<(), String> {
        readonly_installation(&self.root)?;
        let version = tools::query(&self.targo, &["--unverified", "--version", "--verbose"])?;
        if !version.starts_with("targo ") {
            return Err("selected WP build tool did not identify as genuine Targo".into());
        }
        let expected_commit = builder
            .version_info()
            .sha()
            .ok_or("WP qualification requires a source-named current compiler commit")?;
        targo_identity(
            &version,
            &builder.rust_release(),
            expected_commit,
            &builder.host_target.triple,
        )?;
        let version = tools::query(&self.trustc, &["-vV"])?;
        compiler_identity(
            &version,
            &builder.rust_release(),
            expected_commit,
            &builder.host_target.triple,
        )?;
        let sysroot = tools::query(&self.trustc, &["--print", "sysroot"])?;
        if fs::canonicalize(sysroot).map_err(|e| e.to_string())? != self.root {
            return Err(
                "selected WP compiler does not resolve its own immutable installation".into()
            );
        }
        let target_libdir = tools::query(&self.trustc, &["--print", "target-libdir"])?;
        self_contained_private_view(
            &self.root,
            Path::new(&target_libdir),
            &builder.host_target.triple,
        )?;
        Ok(())
    }
}

// Force the unchanged wrapper's self-contained HOST fast path. Otherwise it
// could consult sibling private sysroots or its external-path environment cache.
fn self_contained_private_view(root: &Path, libdir: &Path, host: &str) -> Result<(), String> {
    let expected = root.join("lib/rustlib").join(host).join("lib");
    if fs::canonicalize(libdir).map_err(|e| e.to_string())? != expected {
        return Err("WP target-libdir must be the native installed library directory".into());
    }
    let names = fs::read_dir(libdir)
        .map_err(|e| e.to_string())?
        .map(|entry| entry.map(|entry| entry.path()).map_err(|e| e.to_string()))
        .collect::<Result<Vec<_>, _>>()?;
    for (prefix, suffix) in [
        ("libstd-", ".rlib"),
        ("libcore-", ".rlib"),
        ("libtest-", ".rlib"),
        ("librustc_middle-", ".rmeta"),
    ] {
        if !names.iter().any(|path| {
            path.file_name()
                .and_then(|name| name.to_str())
                .is_some_and(|name| name.starts_with(prefix) && name.ends_with(suffix))
                && fs::metadata(path).is_ok_and(|metadata| metadata.is_file() && metadata.len() > 0)
        }) {
            return Err(format!(
                "WP installation needs its self-contained native {prefix}*{suffix} view"
            ));
        }
    }
    let drivers = fs::read_dir(root.join("lib"))
        .map_err(|e| e.to_string())?
        .map(|entry| entry.map(|entry| entry.path()).map_err(|e| e.to_string()))
        .collect::<Result<Vec<_>, _>>()?
        .into_iter()
        .filter(|path| {
            path.file_name().and_then(|name| name.to_str()).is_some_and(|name| {
                name.strip_prefix("librustc_driver-")
                    .and_then(|name| {
                        name.strip_suffix(".dylib").or_else(|| name.strip_suffix(".so"))
                    })
                    .is_some_and(|hash| {
                        !hash.is_empty() && hash.bytes().all(|byte| byte.is_ascii_hexdigit())
                    })
            })
        })
        .collect::<Vec<_>>();
    let [driver] = drivers.as_slice() else {
        return Err(
            "WP installation must contain exactly one installed rustc_driver runtime".into()
        );
    };
    let private = libdir.join(driver.file_name().unwrap());
    if cache::file_digest(&private)? != cache::file_digest(driver)? {
        return Err("WP installed private metadata view does not carry the selected runtime's exact driver bytes".into());
    }
    Ok(())
}

// Match the maintained wrapper's native -L selection. These directories can
// contain link inputs absent from the compiler's own current loader closure.
fn native_link_directories(root: &Path) -> Result<BTreeSet<PathBuf>, String> {
    let (llvm, native) = if let Ok(brew) = resolve_tool(Path::new("brew")) {
        let llvm = PathBuf::from(tools::query(&brew, &["--prefix", "llvm"])?).join("lib");
        let native = PathBuf::from(tools::query(&brew, &["--prefix"])?).join("lib");
        (
            if llvm.is_dir() { llvm } else { PathBuf::from("/opt/homebrew/opt/llvm/lib") },
            if native.is_dir() { native } else { PathBuf::from("/opt/homebrew/lib") },
        )
    } else {
        let llvm = root.parent().ok_or("WP installation has no parent")?.join("llvm/lib");
        (if llvm.is_dir() { llvm } else { PathBuf::from("/usr/lib") }, PathBuf::from("/usr/lib"))
    };
    let mut directories = BTreeSet::new();
    for path in [llvm, native] {
        // The linker also ignores a missing -L directory. Bind the name and
        // its absence at the call site, so appearance during a run is detected.
        directories.insert(path);
    }
    Ok(directories)
}

fn compiler_identity(verbose: &str, release: &str, commit: &str, host: &str) -> Result<(), String> {
    identity_fields(verbose, &[("release: ", release), ("commit-hash: ", commit), ("host: ", host)])
}

fn targo_identity(verbose: &str, release: &str, commit: &str, host: &str) -> Result<(), String> {
    // The ordinary Cargo commit field is diagnostic. Bootstrap's explicit
    // Trust-root field is the provenance required for this installed tool.
    identity_fields(
        verbose,
        &[("release: ", release), ("trust-repo-commit-hash: ", commit), ("host: ", host)],
    )
}

fn identity_fields(verbose: &str, expected: &[(&str, &str)]) -> Result<(), String> {
    for &(key, expected) in expected {
        let values = verbose.lines().filter_map(|line| line.strip_prefix(key)).collect::<Vec<_>>();
        if values.as_slice() != [expected] {
            return Err(format!("WP tool {key}must match this checkout ({expected})"));
        }
    }
    Ok(())
}

// Read-only names/contents plus full before/after content identities are the
// supported installation boundary. This is not a kernel immutability proof.
fn readonly_installation(root: &Path) -> Result<(), String> {
    if !root.is_dir() {
        return Err("WP installation is not a directory".into());
    }
    for entry in walkdir::WalkDir::new(root).follow_links(false) {
        let entry = entry.map_err(|e| e.to_string())?;
        let metadata = fs::symlink_metadata(entry.path()).map_err(|e| e.to_string())?;
        if metadata.file_type().is_symlink() {
            let target = fs::canonicalize(entry.path()).map_err(|e| e.to_string())?;
            if !target.starts_with(root) {
                return Err(format!(
                    "WP installation link escapes its read-only namespace: {}",
                    entry.path().display()
                ));
            }
            continue;
        }
        #[cfg(unix)]
        let writable = {
            use std::os::unix::fs::PermissionsExt;
            metadata.permissions().mode() & 0o222 != 0
        };
        #[cfg(not(unix))]
        let writable = !metadata.permissions().readonly();
        if writable || !(metadata.is_file() || metadata.is_dir()) {
            return Err(format!(
                "WP installation must contain only read-only regular files/directories: {}",
                entry.path().display()
            ));
        }
    }
    installation_bin_namespace(&root.join("bin"))?;
    Ok(())
}

// The selected bin directory precedes PATH for nested Trust tools. It must
// not change what `brew`, shell interpreters, native compilers or any other
// system helper mean relative to the parent's inventory/native-link queries.
fn installation_bin_namespace(bin: &Path) -> Result<(), String> {
    use crate::core::build_steps::tool;

    // Trust: derive ordinary tools (including ty and trustup) from the same
    // declarations as sysroot assembly. Accept the complete enabled surface,
    // independent of which subset this particular installation contains.
    let installed_tools = tool::restored_sysroot_bins_for_tool_settings(true, None, true, true);
    // Compiler/debugger, WP and Lean tools have separate installation owners.
    const ADDITIONAL_TOOLS: &[&str] = &[
        "trustc",
        "rustc",
        "trust-gdb",
        "trust-gdbgui",
        "trust-lldb",
        "trust-wp",
        "trust-wp-driver",
        "trust-wp-rustc",
        "targo-trust-wp",
        "cargo-trust-wp",
        "lean",
        "lake",
    ];
    for entry in fs::read_dir(bin).map_err(|e| e.to_string())? {
        let name = entry.map_err(|e| e.to_string())?.file_name();
        let text = name.to_str().ok_or("non-UTF-8 name in the selected WP installation bin")?;
        let text = text.strip_suffix(".exe").unwrap_or(text);
        let declared_tool = installed_tools.iter().any(|&(source, destination)| {
            text == destination || tool::upstream_compat_bin_for_tool_source(source) == Some(text)
        });
        if !declared_tool && !ADDITIONAL_TOOLS.contains(&text) {
            return Err(format!(
                "selected WP installation bin contains an undeclared helper that can shadow PATH: {}",
                name.to_string_lossy()
            ));
        }
    }
    Ok(())
}

fn workspace(source: &Path) -> Result<PathBuf, String> {
    let source = fs::canonicalize(source).map_err(|e| e.to_string())?;
    let path = source.join(WORKSPACE);
    if fs::canonicalize(&path).map_err(|e| e.to_string())? != path
        || !path.join("Cargo.lock").is_file()
        || !path.join(WRAPPER).is_file()
    {
        return Err("WP qualification requires the materialized, confined pinned workspace".into());
    }
    let target = path.join("target");
    if target.exists() && fs::canonicalize(&target).map_err(|e| e.to_string())? != target {
        return Err("WP target must not redirect into another namespace".into());
    }
    Ok(path)
}

fn workspace_command(installation: &Installation, workspace: &Path, jobs: u32) -> BootstrapCommand {
    let mut path = vec![installation.root.join("bin")];
    path.extend(env::split_paths(&env::var_os("PATH").unwrap_or_default()));
    let mut cmd = command(&installation.targo);
    cmd.current_dir(workspace)
        .env("PATH", env::join_paths(path).expect("valid inherited PATH"))
        .env("RUSTC", &installation.trustc)
        .env("RUSTDOC", &installation.trustdoc)
        .env("CARGO", &installation.targo)
        .env("CARGO_TARGET_DIR", workspace.join("target"))
        .env("CARGO_BUILD_BUILD_DIR", workspace.join("target"))
        .env("CARGO_BUILD_JOBS", jobs.to_string())
        .env("RUST_TEST_THREADS", jobs.min(4).to_string())
        .env("RAYON_NUM_THREADS", jobs.to_string());
    // Empty ambient wrapper variables also override Cargo configuration. The
    // owning WP config, validated and bound below, must select its real wrapper.
    for key in ["RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER", "RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS"]
    {
        cmd.env_remove(key);
    }
    cmd
}

fn workspace_metadata_command(
    installation: &Installation,
    workspace: &Path,
    jobs: u32,
) -> BootstrapCommand {
    let mut cmd = workspace_command(installation, workspace, jobs);
    // Trust: metadata inventories inputs without compiling. Targo refuses
    // --unverified here; the explicit lane belongs to BUILD and TEST above.
    cmd.args(["metadata", "--locked", "--offline", "--all-features", "--format-version", "1"]);
    cmd
}

pub(super) fn run(builder: &Builder<'_>, selected: &Path) -> Result<(), String> {
    if builder.config.dry_run() {
        builder.info("native WP qualification: installed current compiler prerequisite; release build and all driver/test-utils library and binary unit suites; no proof claim");
        return Ok(());
    }
    let workspace = workspace(&builder.src)?;
    let source = fs::canonicalize(&builder.src).map_err(|e| e.to_string())?;
    let output = fs::canonicalize(&builder.out).map_err(|e| e.to_string())?;
    let installation = Installation::open(selected, &source, &output)?;
    installation.check_identity(builder)?;
    fs::create_dir_all(workspace.join("target")).map_err(|e| e.to_string())?;
    let mut task = Sha256::new();
    cache::add(&mut task, b"trust.native-repo-wp/v1");
    cache::add(&mut task, installation.root.as_os_str().as_encoded_bytes());
    let directory = builder.out.join("trust-repo").join(cache::finish(task));
    let outcome = cache::run_wp(
        &directory,
        cache::OutputNamespace::TrustWp { repository: &builder.src },
        || super::inputs(builder, Some(&installation)),
        || {
            let mut build = workspace_command(&installation, &workspace, builder.jobs());
            build.args(BUILD).arg("--jobs").arg(builder.jobs().to_string());
            if !build.allow_failure().run(builder) {
                return Err(
                    "maintained WP release build failed; no tests or success receipt".into()
                );
            }
            let mut test = workspace_command(&installation, &workspace, builder.jobs());
            test.args(TEST).arg("--jobs").arg(builder.jobs().to_string());
            let result = test.allow_failure().run_capture_stdout(builder);
            let text = result.stdout_if_present().unwrap_or_default();
            print!("{text}");
            if !result.is_success() {
                return Err(
                    "maintained WP library/binary unit tests failed; no success receipt".into()
                );
            }
            completed_suites(&text)
        },
    )?;
    builder.info(&format!("native WP qualification: {outcome:?}; unverified workspace build and library/binary unit tests only; no proof claim"));
    Ok(())
}

fn completed_suites(output: &str) -> Result<(), String> {
    let mut suites = 0;
    for line in output.lines().filter_map(|line| line.strip_prefix("test result: ")) {
        let line = line.strip_prefix("ok. ").ok_or("a WP unit suite did not pass")?;
        let mut counts = Vec::new();
        for field in line.split(';').take(5) {
            let mut words = field.split_whitespace();
            counts.push((words.next().and_then(|word| word.parse::<u64>().ok()), words.next()));
        }
        if counts.len() != 5
            || counts[0].0.is_none_or(|count| count == 0)
            || counts[0].1 != Some("passed")
            || counts[1..]
                != [
                    (Some(0), Some("failed")),
                    (Some(0), Some("ignored")),
                    (Some(0), Some("measured")),
                    (Some(0), Some("filtered")),
                ]
        {
            return Err("WP unit suites must execute nonzero tests, with no failures, ignored or filtered cases".into());
        }
        suites += 1;
    }
    // driver lib, both maintained bin aliases, and test-utils lib. A changed
    // target population needs a reviewed declaration, never a zero-suite pass.
    if suites != 4 {
        return Err(format!(
            "WP qualification expected four declared unit suites, observed {suites}"
        ));
    }
    Ok(())
}

fn nested_config(path: &Path) -> Result<(), String> {
    let text = fs::read_to_string(path).map_err(|e| e.to_string())?;
    let value: toml::Value = toml::from_str(&text).map_err(|e| e.to_string())?;
    let build = value
        .get("build")
        .and_then(toml::Value::as_table)
        .ok_or("WP Cargo config must declare its maintained private wrapper")?;
    if value
        .as_table()
        .is_none_or(|table| table.keys().any(|key| !matches!(key.as_str(), "build" | "env")))
        || build.len() != 1
        || build.get("rustc-wrapper").and_then(toml::Value::as_str) != Some(WRAPPER)
    {
        return Err("WP Cargo config must retain only its declared build.rustc-wrapper, without alternate compiler/target inputs".into());
    }
    if let Some(environment) = value.get("env") {
        let environment = environment.as_table().ok_or("WP Cargo env must be a table")?;
        for (name, value) in environment {
            let expected = match name.as_str() {
                "RUST_TEST_THREADS" => "4",
                "RUST_MIN_STACK" => "16777216",
                _ => {
                    return Err(format!(
                        "WP Cargo config contains an undeclared environment input: {name}"
                    ));
                }
            };
            let text = if let Some(text) = value.as_str() {
                Some(text)
            } else {
                let table =
                    value.as_table().ok_or("WP Cargo env entry must be a string or table")?;
                if table.keys().any(|key| !matches!(key.as_str(), "value" | "force"))
                    || table.get("force").is_some_and(|force| force.as_bool() != Some(false))
                {
                    return Err(
                        "WP Cargo env may not override the admitted execution environment".into()
                    );
                }
                table.get("value").and_then(toml::Value::as_str)
            };
            if text != Some(expected) {
                return Err(format!("WP Cargo config has an undeclared default for {name}"));
            }
        }
    }
    Ok(())
}

fn ancestor_environment(path: &Path) -> Result<(), String> {
    let text = fs::read_to_string(path).map_err(|e| e.to_string())?;
    let value: toml::Value = toml::from_str(&text).map_err(|e| e.to_string())?;
    if value.get("env").and_then(toml::Value::as_table).is_some_and(|environment| {
        environment.keys().any(|name| {
            let canonical = cargo_config_name(name);
            competing_environment(name)
                || matches!(
                    canonical.as_ref(),
                    "RUSTC"
                        | "RUSTDOC"
                        | "RUSTFLAGS"
                        | "CARGO_ENCODED_RUSTFLAGS"
                        | "RUSTC_WRAPPER"
                        | "RUSTC_WORKSPACE_WRAPPER"
                        | "RUST_TEST_THREADS"
                        | "RAYON_NUM_THREADS"
                        | "CARGO_TARGET_DIR"
                        | "CARGO_BUILD_BUILD_DIR"
                        | "CARGO_HOME"
                )
        })
    }) {
        return Err(format!("{} overrides the declared WP execution environment", path.display()));
    }
    Ok(())
}

pub(super) fn add_inputs(
    builder: &Builder<'_>,
    hash: &mut Sha256,
    installation: &Installation,
) -> Result<(), String> {
    cache::add(hash, b"trust.native-repo-wp-inputs/v1");
    installation.check_identity(builder)?;
    cache::add(
        hash,
        tools::selected_tool_installation_digest(&installation.root, &installation.trustc)?,
    );
    for tool in [&installation.targo, &installation.trustdoc] {
        cache::add(hash, tools::tool_digest(tool)?);
    }
    for path in native_link_directories(&installation.root)? {
        cache::add(hash, path.as_os_str().as_encoded_bytes());
        match fs::symlink_metadata(&path) {
            Ok(_) => cache::add(hash, cache::tree_digest(&path)?),
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
                cache::add(hash, b"missing-native-link-directory")
            }
            Err(error) => return Err(error.to_string()),
        }
    }
    let workspace = workspace(&builder.src)?;
    // Ancestor/CARGO_HOME configs keep the existing bounded refusals. Only
    // this exact nested wrapper declaration is additionally supported.
    for path in cargo_config_inputs(workspace.parent().unwrap())? {
        ancestor_environment(&path)?;
        cache::add(hash, cache::tree_digest(&path)?);
    }
    let config = workspace.join(".cargo/config.toml");
    if workspace.join(".cargo/config").exists() {
        return Err("WP qualification does not accept a competing legacy Cargo config".into());
    }
    nested_config(&config)?;
    cache::add(hash, cache::tree_digest(&config)?);
    cache::add(hash, tools::tool_digest(&workspace.join(WRAPPER))?);
    add_parsed_configs(hash, &builder.config.native_repo_config_inputs)?;
    let metadata = workspace_metadata_command(installation, &workspace, builder.jobs());
    let output = metadata.allow_failure().run_capture_stdout(builder);
    let text = output
        .stdout_if_ok()
        .ok_or("cannot resolve the WP workspace's locked offline dependency closure")?;
    let metadata: Metadata = serde_json::from_str(&text).map_err(|e| e.to_string())?;
    let mut roots = BTreeSet::new();
    let source = fs::canonicalize(&builder.src).map_err(|e| e.to_string())?;
    for package in metadata.packages {
        let root = package.manifest_path.parent().ok_or("WP manifest has no directory")?;
        let root = fs::canonicalize(root).map_err(|e| e.to_string())?;
        if !root.starts_with(&source) {
            roots.insert(root);
        }
    }
    for identity in cache::hash_leaves(
        &roots.into_iter().collect::<Vec<_>>(),
        builder.jobs() as usize,
        cache::tree_digest,
    )? {
        cache::add(hash, identity);
    }
    for name in ["bash", "env", "awk", "sed", "sort", "tr", "head", "basename", "dirname", "cmp"] {
        cache::add(hash, tools::tool_digest(&resolve_tool(Path::new(name))?)?);
    }
    for name in ["brew", "otool", "objdump"] {
        if let Ok(path) = resolve_tool(Path::new(name)) {
            cache::add(hash, tools::tool_digest(&path)?);
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests;
