//! Trust: one bounded native repository workflow in bootstrap's existing graph.

use std::collections::BTreeSet;
use std::path::{Component, Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};
use std::{env, fs};

use serde_derive::Deserialize;
use sha2::{Digest, Sha256};

use crate::core::build_steps::{check, compile, test};
use crate::core::builder::{Builder, Step};
use crate::core::compiler::Compiler;
use crate::core::config::Config;
use crate::utils::exec::command;
use crate::utils::{trust_repo_cache as cache, trust_repo_tools as tools, trust_source_identity};

// Trust: fixed workspace qualification, sharing this workflow's admission and leases.
mod wp;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Selection<'a> {
    Ui,
    Wp(&'a Path),
}

fn selection(config: &Config) -> Result<Selection<'_>, String> {
    if config.paths.as_slice() == [PathBuf::from("first-party/trust-wp")] {
        return config.cmd.trust_repo_wp_installation().map(Selection::Wp).ok_or_else(|| {
            "WP qualification requires --trust-repo-wp-installation with an immutable current installation".into()
        });
    }
    if config.cmd.trust_repo_wp_installation().is_some() {
        return Err(
            "--trust-repo-wp-installation requires the first-party/trust-wp selection".into()
        );
    }
    Ok(Selection::Ui)
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct Check;

impl Step for Check {
    type Output = ();

    fn run(self, builder: &Builder<'_>) {
        validate(&builder.config)
            .unwrap_or_else(|error| panic!("native repository check: {error}"));
        if let Selection::Wp(installation) = selection(&builder.config).unwrap() {
            wp::run(builder, installation)
                .unwrap_or_else(|error| panic!("native WP qualification: {error}"));
            return;
        }
        let target = builder.host_target;
        let actions = || {
            check::Rustc::ensure_repo_check(builder, target);
            test::ensure_repo_ui(builder, target);
            if builder.config.exec_ctx().has_delayed_failures() {
                return Err("compiler check or UI execution failed; no success was saved".into());
            }
            Ok(())
        };
        // Bootstrap's mandatory dry-run sanity pass must remain side-effect free.
        if builder.config.dry_run() {
            actions().unwrap_or_else(|error| panic!("native repository check: {error}"));
            return;
        }
        let selected = &builder.config.paths[0];
        let mut task = Sha256::new();
        cache::add(&mut task, selected.as_os_str().as_encoded_bytes());
        let directory = builder.out.join("trust-repo").join(cache::finish(task));
        // Trust: use the same declaration as the owning Sysroot step, including
        // stage0-sysroot's rustc-src and both stage1 source aliases.
        let outputs = builder.out.join(target);
        let source_aliases = [0, 1]
            .into_iter()
            .flat_map(|stage| {
                let sysroot = compile::local_sysroot_dir(builder, Compiler::new(stage, target));
                compile::sysroot_source_aliases(stage, builder.download_rustc())
                    .iter()
                    .map(move |relative| sysroot.join(relative))
            })
            .collect::<Vec<_>>();
        // Trust: arbitrary UI/build-script reads are not a mechanically complete
        // input closure. Persist inner execution facts, but always execute again.
        let outcome = cache::run(
            cache::ReusePolicy::RecordOnly,
            &directory,
            cache::OutputNamespace::GeneratedHost {
                root: &outputs,
                repository: &builder.src,
                source_aliases: &source_aliases,
            },
            || inputs(builder, None),
            actions,
        )
        .unwrap_or_else(|error| panic!("native repository check: {error}"));
        builder.info(&format!(
            "native repository check: {outcome:?}; compiler targets and {}; inner bootstrap execution facts only, no proof claim",
            selected.display(),
        ));
    }
}

pub(crate) fn validate(config: &Config) -> Result<(), String> {
    let selected = selection(config)?;
    let stage = if matches!(selected, Selection::Wp(_)) { 2 } else { 1 };
    if config.stage != stage
        || config.hosts.as_slice() != [config.host_target]
        || config.targets.as_slice() != [config.host_target]
        || config.download_rustc()
        || config.bypass_bootstrap_lock
        || !config.keep_stage.is_empty()
        || !config.keep_stage_std.is_empty()
        || !config.skip.is_empty()
        || config.include_default_paths
        || !config.free_args.is_empty()
        || config.compile_time_deps
        || config
            .target_config
            .get(&config.host_target)
            .is_some_and(|target| target.runner.is_some())
    {
        return Err(format!(
            "requires direct execution on one local stage-{stage} host/target, ordinary build locks and no runner/kept/skipped/default/extra targets"
        ));
    }
    if config.paths.len() != 1 {
        return Err("select exactly one tests/ui/trust/*.rs file or first-party/trust-wp".into());
    }
    if !config.dry_run() {
        let root = fs::canonicalize(&config.src).map_err(|e| e.to_string())?;
        let out = fs::canonicalize(&config.out).map_err(|e| e.to_string())?;
        if out == root || !out.starts_with(root) {
            return Err("native repository output must stay inside its own checkout".into());
        }
        let share = env::var("CARGO_BUILD_JOBS")
            .ok()
            .and_then(|share| share.parse::<u32>().ok())
            .filter(|share| *share > 0)
            .ok_or(
                "native repository execution requires an admitted positive CARGO_BUILD_JOBS share",
            )?;
        if env::var_os("BUILD_SLOT_HELD").as_deref() != Some(std::ffi::OsStr::new("1"))
            || config.jobs.is_none_or(|jobs| jobs == 0 || jobs > share)
        {
            return Err("native repository execution requires build-slot admission and --jobs within its share".into());
        }
    }
    if matches!(selected, Selection::Ui) {
        validate_test_path(&config.src, &config.paths[0])?;
    } else {
        wp::validate_environment()?;
    }
    for key in ["RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS", "RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER"]
    {
        if env::var_os(key).is_some_and(|value| !value.is_empty()) {
            return Err(format!(
                "the bounded native input closure does not yet support ambient {key}"
            ));
        }
    }
    Ok(())
}

fn validate_test_path(root: &Path, path: &Path) -> Result<(), String> {
    if path.is_absolute()
        || path.components().any(|part| !matches!(part, Component::Normal(_)))
        || !path.starts_with("tests/ui/trust")
        || path.extension().is_none_or(|extension| extension != "rs")
        || !root.join(path).is_file()
    {
        return Err("the UI selection must be an existing relative tests/ui/trust/*.rs file".into());
    }
    let canonical = fs::canonicalize(root.join(path)).map_err(|e| e.to_string())?;
    let suite = fs::canonicalize(root.join("tests/ui/trust")).map_err(|e| e.to_string())?;
    if !canonical.starts_with(suite) {
        return Err("the selected UI file resolves outside tests/ui/trust".into());
    }
    Ok(())
}

// Trust: installation and qualification share the actual input observation owners.
pub(crate) fn installation_inputs(builder: &Builder<'_>) -> Result<cache::InputSnapshot, String> {
    inputs(builder, None)
}

// Trust: actual completed-runtime construction additionally binds the selected
// external Lean CONTENTS, not only the environment's library pathname. The
// existing input observer binds parsed configuration, all ambient inputs,
// native recipe/source, seed, dependency/tool closures and external LLVM/SDK.
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
pub(crate) fn completed_frontend_runtime_inputs(
    builder: &Builder<'_>,
) -> Result<(cache::InputSnapshot, String), String> {
    let original = inputs(builder, None)?;
    if env::var_os("CLEAN_OLEAN_REQUIRE_PINNED_LEAN").as_deref() != Some(std::ffi::OsStr::new("1"))
    {
        return Err("completed runtime requires explicit pinned Lean selection".into());
    }
    let library = env::var_os("CLEAN_OLEAN_PINNED_LEAN_LIB")
        .ok_or("completed runtime requires the actual pinned Lean library")?;
    let library = fs::canonicalize(library).map_err(|error| error.to_string())?;
    if !library.join("Init/Prelude.olean").is_file() {
        return Err("completed runtime pinned Lean library is incomplete".into());
    }
    let mut hash = Sha256::new();
    cache::add(&mut hash, b"trust.completed-frontend-runtime-inputs/v1");
    cache::add(&mut hash, original.digest());
    cache::add(&mut hash, cache::tree_digest(&library)?);
    // Preserve the actual observed repository value; no digest-to-owner path.
    Ok((original, cache::finish(hash)))
}

pub(crate) fn check_wp_installation(builder: &Builder<'_>, path: &Path) -> Result<(), String> {
    wp::check_installation(builder, path)
}

// Trust: a native initial Targo may read its native home/target aliases too.
// UI behavior remains unchanged; this is the new installation's bounded mode.
pub(crate) fn check_installation_environment(
    environment: &std::collections::BTreeMap<std::ffi::OsString, std::ffi::OsString>,
) -> Result<(), String> {
    wp::validate_environment_values(environment)?;
    for key in [
        "RUSTFLAGS",
        "CARGO_ENCODED_RUSTFLAGS",
        "RUSTC_WRAPPER",
        "RUSTC_WORKSPACE_WRAPPER",
        "RUSTC_WRAPPER_REAL",
    ] {
        if environment.get(std::ffi::OsStr::new(key)).is_some_and(|value| !value.is_empty()) {
            return Err(format!("the bounded native installation does not support ambient {key}"));
        }
    }
    Ok(())
}

fn inputs(
    builder: &Builder<'_>,
    wp: Option<&wp::Installation>,
) -> Result<cache::InputSnapshot, String> {
    let jobs = builder.jobs() as usize;
    let mut hash = Sha256::new();
    cache::add(&mut hash, b"trust.native-repo-inputs/v2");
    let repository = cache::RepositorySnapshot::observe(&builder.src, jobs)?;
    cache::add(&mut hash, repository.digest());
    add_parsed_configs(&mut hash, &builder.config.native_repo_config_inputs)?;
    cache::add(
        &mut hash,
        trust_source_identity::config_digest(builder.config.config.as_deref(), &builder.config.src),
    );
    cache::add(
        &mut hash,
        env::current_dir().map_err(|e| e.to_string())?.as_os_str().as_encoded_bytes(),
    );
    for argument in env::args_os() {
        cache::add(&mut hash, argument.as_encoded_bytes());
    }
    let mut environment = env::vars_os().collect::<Vec<_>>();
    environment.sort();
    for (key, value) in environment {
        cache::add(&mut hash, key.as_encoded_bytes());
        cache::add(&mut hash, value.as_encoded_bytes());
    }
    cache::add(&mut hash, env::consts::OS);
    cache::add(&mut hash, env::consts::ARCH);
    cache::add(
        &mut hash,
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map_err(|e| e.to_string())?
            .as_secs()
            .div_euclid(86400)
            .to_le_bytes(),
    );
    // Trust: hash independent roots within the same admitted CPU share. Each
    // tree/loader closure keeps its descriptor checks; fold in inventory order.
    let mut toolchain = vec![env::current_exe().map_err(|e| e.to_string())?];
    // Trust: WP consumes its explicit installation, not Bootstrap's seed/shims.
    if wp.is_none() {
        toolchain.extend([
            builder.bootstrap_out.join(crate::utils::helpers::exe("rustc", builder.host_target)),
            builder.bootstrap_out.join(crate::utils::helpers::exe("rustdoc", builder.host_target)),
            builder.initial_sysroot.clone(),
            builder.initial_cargo.clone(),
            builder.initial_rustc.clone(),
            builder.initial_rustdoc.clone(),
        ]);
    }
    add_toolchain_inputs(&mut hash, &toolchain, jobs)?;
    for path in cargo_config_inputs(&builder.src)? {
        cache::add(&mut hash, cache::tree_digest(&path)?);
    }
    let dependencies = if wp.is_none() { dependency_roots(builder)? } else { BTreeSet::new() }
        .into_iter()
        .filter(|root| !root.starts_with(&builder.src))
        .collect::<Vec<_>>();
    for identity in cache::hash_leaves(&dependencies, jobs, cache::tree_digest)? {
        cache::add(&mut hash, identity);
    }
    let target = builder.host_target;
    let mut tools = vec![builder.cc(target)];
    tools.extend(builder.cxx(target));
    tools.extend(builder.ar(target));
    tools.extend(builder.ranlib(target));
    tools.extend(builder.linker(target));
    tools.extend(builder.python.clone());
    tools.extend(builder.rustc_default_linker.as_ref().map(PathBuf::from));
    tools.extend(builder.llvm_use_linker.as_ref().map(PathBuf::from));
    for tool in tools {
        let path = resolve_tool(&tool)?;
        cache::add(&mut hash, tools::tool_digest(&path)?);
    }
    for name in ["git", "cmake", "ninja", "make", "python3", "sh", "bash"] {
        if let Ok(path) = resolve_tool(Path::new(name)) {
            cache::add(&mut hash, tools::tool_digest(&path)?);
        }
    }
    if let Some(config) = builder.target_config.get(&target) {
        if let Some(llvm) = &config.llvm_config {
            let llvm = resolve_tool(llvm)?;
            let prefix = tools::query(&llvm, &["--prefix"])?;
            cache::add(
                &mut hash,
                tools::installation_digest(&fs::canonicalize(prefix).map_err(|e| e.to_string())?)?,
            );
        }
        for tool in [&config.llvm_filecheck, &config.default_linker] {
            if let Some(tool) = tool {
                cache::add(&mut hash, tools::tool_digest(&resolve_tool(tool)?)?);
            }
        }
    }
    if let Some(ccache) = &builder.ccache {
        let ccache = resolve_tool(Path::new(ccache))?;
        cache::add(&mut hash, tools::tool_digest(&ccache)?);
        let configuration = tools::query(&ccache, &["--show-config"])?;
        for line in configuration.lines() {
            for key in ["prefix_command = ", "prefix_command_cpp = "] {
                if line.split_once(key).is_some_and(|(_, value)| !value.trim().is_empty()) {
                    return Err(
                        "the first native slice cannot bind opaque ccache prefix commands".into()
                    );
                }
            }
            if let Some((_, compiler)) = line.split_once("compiler = ") {
                if !compiler.trim().is_empty() {
                    cache::add(
                        &mut hash,
                        tools::tool_digest(&resolve_tool(Path::new(compiler.trim()))?)?,
                    );
                }
            }
        }
        cache::add(&mut hash, configuration);
    }
    // Bind loader overrides as directories, including all alternate library bytes.
    for name in ["DYLD_LIBRARY_PATH", "DYLD_FALLBACK_LIBRARY_PATH", "LD_LIBRARY_PATH"] {
        if let Some(value) = env::var_os(name) {
            for directory in env::split_paths(&value) {
                cache::add(&mut hash, cache::tree_digest(&directory)?);
            }
        }
    }
    // A selected external SDK is an input, including headers and libraries.
    if let Some(path) = env::var_os("SDKROOT") {
        cache::add(&mut hash, cache::tree_digest(Path::new(&path))?);
    } else if cfg!(target_os = "macos") {
        let sdk = tools::query(Path::new("/usr/bin/xcrun"), &["--show-sdk-path"])?;
        cache::add(&mut hash, cache::tree_digest(Path::new(&sdk))?);
    }
    if cfg!(target_os = "macos") {
        cache::add(&mut hash, tools::query(Path::new("/usr/bin/sw_vers"), &["-buildVersion"])?);
        let clang = tools::query(Path::new("/usr/bin/xcrun"), &["--find", "clang"])?;
        let directory = Path::new(&clang)
            .parent()
            .and_then(Path::parent)
            .ok_or("the selected developer compiler has no installation")?;
        cache::add(
            &mut hash,
            tools::selected_tool_installation_digest(directory, Path::new(&clang))?,
        );
    }
    if let Some(installation) = wp {
        wp::add_inputs(builder, &mut hash, installation)?;
    }
    Ok(cache::InputSnapshot::new(cache::finish(hash), repository))
}

fn add_toolchain_inputs(hash: &mut Sha256, paths: &[PathBuf], jobs: usize) -> Result<(), String> {
    for identity in cache::hash_leaves(paths, jobs, |path| {
        if path.is_dir() { cache::tree_digest(path) } else { tools::tool_digest(path) }
    })? {
        cache::add(hash, identity);
    }
    Ok(())
}

fn add_parsed_configs(hash: &mut Sha256, inputs: &[(PathBuf, String)]) -> Result<(), String> {
    for (path, parsed) in inputs {
        if cache::file_digest(path)? != *parsed {
            return Err(format!(
                "{} moved after bootstrap parsed it; refusing mixed configuration inputs",
                path.display()
            ));
        }
        cache::add(hash, path.as_os_str().as_encoded_bytes());
        cache::add(hash, parsed);
    }
    Ok(())
}

fn resolve_tool(tool: &Path) -> Result<PathBuf, String> {
    if tool.is_absolute() || tool.components().count() > 1 {
        return fs::canonicalize(tool).map_err(|e| e.to_string());
    }
    env::split_paths(&env::var_os("PATH").unwrap_or_default())
        .map(|directory| directory.join(tool))
        .find(|path| path.is_file())
        .ok_or_else(|| format!("cannot bind native repository tool {}", tool.display()))
        .and_then(|path| fs::canonicalize(path).map_err(|e| e.to_string()))
}

fn cargo_config_inputs(root: &Path) -> Result<BTreeSet<PathBuf>, String> {
    let mut directories = root.ancestors().map(|path| path.join(".cargo")).collect::<Vec<_>>();
    if let Some(home) =
        env::var_os("CARGO_HOME").map(PathBuf::from).or_else(|| home::cargo_home().ok())
    {
        directories.push(home);
    }
    let mut inputs = BTreeSet::new();
    for directory in directories {
        for name in ["config", "config.toml"] {
            let path = directory.join(name);
            if !path.exists() {
                continue;
            }
            let text = fs::read_to_string(&path).map_err(|e| e.to_string())?;
            let value: toml::Value = toml::from_str(&text).map_err(|e| e.to_string())?;
            if value.get("include").is_some()
                || value.get("target").is_some()
                || value.get("build").and_then(|build| build.as_table()).is_some_and(|build| {
                    [
                        "rustflags",
                        "rustc",
                        "rustc-wrapper",
                        "rustc-workspace-wrapper",
                        "rustdoc",
                        "target-dir",
                    ]
                    .iter()
                    .any(|key| build.contains_key(*key))
                })
            {
                return Err(format!(
                    "{} uses Cargo inputs outside this bounded native slice",
                    path.display()
                ));
            }
            inputs.insert(path);
        }
    }
    Ok(inputs)
}

#[derive(Deserialize)]
struct Metadata {
    packages: Vec<Package>,
}

#[derive(Deserialize)]
struct Package {
    manifest_path: PathBuf,
}

fn dependency_roots(builder: &Builder<'_>) -> Result<BTreeSet<PathBuf>, String> {
    let mut roots = BTreeSet::new();
    // Cargo resolves packages; this is an input inventory, never another task graph.
    for manifest in ["Cargo.toml", "library/Cargo.toml"] {
        let output = command(&builder.initial_cargo)
            .allow_failure()
            .current_dir(&builder.src)
            .env("RUSTC_BOOTSTRAP", "1")
            .env("CARGO_NET_OFFLINE", "true")
            .args([
                "metadata",
                "--format-version",
                "1",
                "--all-features",
                "--locked",
                "--offline",
                "--manifest-path",
            ])
            .arg(builder.src.join(manifest))
            .run_capture_stdout(builder);
        let text = output.stdout_if_ok().ok_or_else(|| {
            format!("cannot resolve native dependency inputs for {manifest} offline and locked")
        })?;
        let metadata: Metadata = serde_json::from_str(&text).map_err(|e| e.to_string())?;
        for package in metadata.packages {
            let path = package.manifest_path.parent().ok_or("manifest has no directory")?;
            roots.insert(fs::canonicalize(path).map_err(|e| e.to_string())?);
        }
    }
    Ok(roots)
}

#[cfg(test)]
mod tests;
