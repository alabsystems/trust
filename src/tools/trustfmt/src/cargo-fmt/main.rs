// Inspired by Paul Woolcock's cargo-fmt (https://github.com/pwoolcoc/cargo-fmt/).

#![deny(warnings)]
#![allow(clippy::match_like_matches_macro)]

use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::ffi::OsString;
use std::fs;
use std::hash::{Hash, Hasher};
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus};
use std::str;

use cargo_metadata::Edition;
use clap::{CommandFactory, Parser};

#[path = "test/mod.rs"]
#[cfg(test)]
mod cargo_fmt_tests;

#[derive(Parser)]
#[command(
    disable_version_flag = true,
    bin_name = "targo fmt",
    about = "This utility formats all bin and lib files of \
             the current crate using trustfmt."
)]
#[command(styles = clap_cargo::style::CLAP_STYLING)]
pub struct Opts {
    /// No output printed to stdout
    #[arg(short = 'q', long = "quiet")]
    quiet: bool,

    /// Use verbose output
    #[arg(short = 'v', long = "verbose")]
    verbose: bool,

    /// Print trustfmt version and exit
    #[arg(long = "version")]
    version: bool,

    /// Specify package to format
    #[arg(
        short = 'p',
        long = "package",
        value_name = "package",
        num_args = 1..
    )]
    packages: Vec<String>,

    /// Specify path to Cargo.toml
    #[arg(long = "manifest-path", value_name = "manifest-path")]
    manifest_path: Option<String>,

    /// Specify message-format: short|json|human
    #[arg(long = "message-format", value_name = "message-format")]
    message_format: Option<String>,

    /// Options passed to trustfmt
    // 'raw = true' to make `--` explicit.
    #[arg(id = "rustfmt_options", raw = true)]
    rustfmt_options: Vec<String>,

    /// Format all packages, and also their local path-based dependencies
    #[arg(long = "all")]
    format_all: bool,

    /// Run trustfmt in check mode
    #[arg(long = "check")]
    check: bool,
}

fn main() {
    let mut exit_status = execute();
    if std::io::stdout().flush().is_err() {
        exit_status = FAILURE;
    }
    std::process::exit(exit_status);
}

const SUCCESS: i32 = 0;
const FAILURE: i32 = 1;

fn execute() -> i32 {
    let current_exe = env::current_exe().ok();
    let args = formatter_command_args(env::args_os(), current_exe.as_deref());
    let opts = Opts::parse_from(args);

    let verbosity = match (opts.verbose, opts.quiet) {
        (false, false) => Verbosity::Normal,
        (false, true) => Verbosity::Quiet,
        (true, false) => Verbosity::Verbose,
        (true, true) => {
            print_usage_to_stderr("quiet mode and verbose mode are not compatible");
            return FAILURE;
        }
    };

    if opts.version {
        return handle_command_status(get_rustfmt_info(&[String::from("--version")]));
    }
    if opts.rustfmt_options.iter().any(|s| {
        ["--print-config", "-h", "--help", "-V", "--version"].contains(&s.as_str())
            || s.starts_with("--help=")
            || s.starts_with("--print-config=")
    }) {
        return handle_command_status(get_rustfmt_info(&opts.rustfmt_options));
    }

    let strategy = CargoFmtStrategy::from_opts(&opts);
    let mut rustfmt_args = opts.rustfmt_options;
    if opts.check {
        let check_flag = "--check";
        if !rustfmt_args.iter().any(|o| o == check_flag) {
            rustfmt_args.push(check_flag.to_owned());
        }
    }
    if let Some(message_format) = opts.message_format {
        if let Err(msg) = convert_message_format_to_rustfmt_args(&message_format, &mut rustfmt_args)
        {
            print_usage_to_stderr(&msg);
            return FAILURE;
        }
    }

    if let Some(specified_manifest_path) = opts.manifest_path {
        if !specified_manifest_path.ends_with("Cargo.toml") {
            print_usage_to_stderr("the manifest-path must be a path to a Cargo.toml file");
            return FAILURE;
        }
        let manifest_path = PathBuf::from(specified_manifest_path);
        handle_command_status(format_crate(
            verbosity,
            &strategy,
            rustfmt_args,
            Some(&manifest_path),
        ))
    } else {
        handle_command_status(format_crate(verbosity, &strategy, rustfmt_args, None))
    }
}

/// Remove Cargo/Targo's external-subcommand marker without consuming a user
/// value that merely happens to equal `fmt`.
///
/// Cargo places the marker at exactly `argv[1]`. The previous search-and-drop
/// filter removed the first `fmt` anywhere before one had been seen, so a
/// direct `targo-fmt --package fmt` invocation lost its package value.
fn formatter_command_args(
    args: impl IntoIterator<Item = OsString>,
    current_exe: Option<&Path>,
) -> Vec<OsString> {
    let mut args = args.into_iter().collect::<Vec<_>>();
    let executable_stem = current_exe
        .and_then(Path::file_stem)
        .and_then(|stem| stem.to_str())
        .or_else(|| {
            current_exe.is_none().then(|| {
                args.first()
                    .and_then(|arg| Path::new(arg).file_stem())
                    .and_then(|stem| stem.to_str())
            })?
        });
    if matches!(executable_stem, Some("cargo-fmt" | "targo-fmt"))
        && args.get(1).is_some_and(|arg| arg == "fmt")
    {
        args.remove(1);
    }
    args
}

fn rustfmt_command() -> Command {
    let rustfmt = match env::var_os("TRUSTFMT") {
        Some(formatter) => PathBuf::from(formatter),
        None => sibling_tool("trustfmt").unwrap_or_else(|| PathBuf::from("trustfmt")),
    };

    Command::new(rustfmt)
}

fn sibling_tool(tool: &str) -> Option<PathBuf> {
    let mut path = env::current_exe().ok()?.with_file_name(tool);
    if cfg!(windows) {
        path.set_extension("exe");
    }
    path.exists().then_some(path)
}

fn convert_message_format_to_rustfmt_args(
    message_format: &str,
    rustfmt_args: &mut Vec<String>,
) -> Result<(), String> {
    let mut contains_emit_mode = false;
    let mut contains_check = false;
    let mut contains_list_files = false;
    for arg in rustfmt_args.iter() {
        if arg.starts_with("--emit") {
            contains_emit_mode = true;
        }
        if arg == "--check" {
            contains_check = true;
        }
        if arg == "-l" || arg == "--files-with-diff" {
            contains_list_files = true;
        }
    }
    match message_format {
        "short" => {
            if !contains_list_files {
                rustfmt_args.push(String::from("-l"));
            }
            Ok(())
        }
        "json" => {
            if contains_emit_mode {
                return Err(String::from(
                    "cannot include --emit arg when --message-format is set to json",
                ));
            }
            if contains_check {
                return Err(String::from(
                    "cannot include --check arg when --message-format is set to json",
                ));
            }
            rustfmt_args.push(String::from("--emit"));
            rustfmt_args.push(String::from("json"));
            Ok(())
        }
        "human" => Ok(()),
        _ => Err(format!(
            "invalid --message-format value: {message_format}. Allowed values are: short|json|human"
        )),
    }
}

fn print_usage_to_stderr(reason: &str) {
    eprintln!("{reason}");
    let app = Opts::command();
    let help = app.after_help("").render_help();
    eprintln!("{help}");
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Verbosity {
    Verbose,
    Normal,
    Quiet,
}

fn handle_command_status(status: Result<i32, io::Error>) -> i32 {
    match status {
        Err(e) => {
            print_usage_to_stderr(&e.to_string());
            FAILURE
        }
        Ok(status) => status,
    }
}

fn child_exit_code(status: &ExitStatus) -> i32 {
    if status.success() {
        SUCCESS
    } else {
        // `ExitStatus::code()` is `None` when the formatter was terminated by
        // a signal. That is a failed formatting run, never a successful one.
        status.code().unwrap_or(FAILURE)
    }
}

fn get_rustfmt_info(args: &[String]) -> Result<i32, io::Error> {
    let mut command = rustfmt_command();
    command.stdout(std::process::Stdio::inherit()).args(args);
    wait_for_formatter(&mut command)
}

fn wait_for_formatter(command: &mut Command) -> Result<i32, io::Error> {
    let mut child = command.spawn().map_err(|e| match e.kind() {
        io::ErrorKind::NotFound => io::Error::new(
            io::ErrorKind::Other,
            "Could not run trustfmt, please make sure it is in your PATH.",
        ),
        _ => e,
    })?;
    let result = child.wait()?;
    Ok(child_exit_code(&result))
}

fn format_crate(
    verbosity: Verbosity,
    strategy: &CargoFmtStrategy,
    rustfmt_args: Vec<String>,
    manifest_path: Option<&Path>,
) -> Result<i32, io::Error> {
    let targets = get_targets(strategy, manifest_path)?;

    // Currently only bin and lib files get formatted.
    run_rustfmt(&targets, &rustfmt_args, verbosity)
}

/// Target uses a `path` field for equality and hashing.
#[derive(Debug)]
pub struct Target {
    /// A path to the main source file of the target.
    path: PathBuf,
    /// A kind of target (e.g., lib, bin, example, ...).
    kind: String,
    /// Rust edition for this target.
    edition: Edition,
}

impl Target {
    pub fn from_target(target: &cargo_metadata::Target) -> Self {
        let path = PathBuf::from(&target.src_path);
        let canonicalized = fs::canonicalize(&path).unwrap_or(path);

        Target {
            path: canonicalized,
            kind: target.kind[0].clone(),
            edition: target.edition,
        }
    }
}

impl PartialEq for Target {
    fn eq(&self, other: &Target) -> bool {
        self.path == other.path
    }
}

impl PartialOrd for Target {
    fn partial_cmp(&self, other: &Target) -> Option<Ordering> {
        Some(self.path.cmp(&other.path))
    }
}

impl Ord for Target {
    fn cmp(&self, other: &Target) -> Ordering {
        self.path.cmp(&other.path)
    }
}

impl Eq for Target {}

impl Hash for Target {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.path.hash(state);
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum CargoFmtStrategy {
    /// Format every packages and dependencies.
    All,
    /// Format packages that are specified by the command line argument.
    Some(Vec<String>),
    /// Format the root packages only.
    Root,
}

impl CargoFmtStrategy {
    pub fn from_opts(opts: &Opts) -> CargoFmtStrategy {
        match (opts.format_all, opts.packages.is_empty()) {
            (false, true) => CargoFmtStrategy::Root,
            (true, _) => CargoFmtStrategy::All,
            (false, false) => CargoFmtStrategy::Some(opts.packages.clone()),
        }
    }
}

/// Based on the specified `CargoFmtStrategy`, returns a set of main source files.
fn get_targets(
    strategy: &CargoFmtStrategy,
    manifest_path: Option<&Path>,
) -> Result<BTreeSet<Target>, io::Error> {
    let mut targets = BTreeSet::new();

    match *strategy {
        CargoFmtStrategy::Root => get_targets_root_only(manifest_path, &mut targets)?,
        CargoFmtStrategy::All => {
            get_targets_recursive(manifest_path, &mut targets, &mut BTreeSet::new())?
        }
        CargoFmtStrategy::Some(ref hitlist) => {
            get_targets_with_hitlist(manifest_path, hitlist, &mut targets)?
        }
    }

    if targets.is_empty() {
        Err(io::Error::new(
            io::ErrorKind::Other,
            "Failed to find targets".to_owned(),
        ))
    } else {
        Ok(targets)
    }
}

fn get_targets_root_only(
    manifest_path: Option<&Path>,
    targets: &mut BTreeSet<Target>,
) -> Result<(), io::Error> {
    let metadata = get_cargo_metadata(manifest_path)?;
    let workspace_root_path = PathBuf::from(&metadata.workspace_root).canonicalize()?;
    let (in_workspace_root, current_dir_manifest) = if let Some(target_manifest) = manifest_path {
        (
            workspace_root_path == target_manifest,
            target_manifest.canonicalize()?,
        )
    } else {
        let current_dir = env::current_dir()?.canonicalize()?;
        (
            workspace_root_path == current_dir,
            current_dir.join("Cargo.toml"),
        )
    };

    let package_targets = match metadata.packages.len() {
        1 => metadata.packages.into_iter().next().unwrap().targets,
        _ => metadata
            .packages
            .into_iter()
            .filter(|p| {
                in_workspace_root
                    || PathBuf::from(&p.manifest_path)
                        .canonicalize()
                        .unwrap_or_default()
                        == current_dir_manifest
            })
            .flat_map(|p| p.targets)
            .collect(),
    };

    for target in package_targets {
        targets.insert(Target::from_target(&target));
    }

    Ok(())
}

fn get_targets_recursive(
    manifest_path: Option<&Path>,
    targets: &mut BTreeSet<Target>,
    visited: &mut BTreeSet<PathBuf>,
) -> Result<(), io::Error> {
    if let Some(manifest_path) = manifest_path {
        let manifest_path =
            fs::canonicalize(manifest_path).unwrap_or_else(|_| manifest_path.to_path_buf());
        visited.insert(manifest_path);
    }
    let metadata = get_cargo_metadata(manifest_path)?;

    // Record every package Cargo loaded before following any path dependency.
    // Dependency names are not identities: two packages can use the same name
    // at different paths, and one package can be reached through multiple
    // symlink spellings.  The old name-based set missed the latter and could
    // recurse through a workspace's self-alias until Cargo rejected a package
    // as belonging to two workspaces.  Canonical manifest paths provide the
    // filesystem identity Cargo is actually going to load.
    for package in &metadata.packages {
        let manifest_path = PathBuf::from(package.manifest_path.as_str());
        visited.insert(fs::canonicalize(&manifest_path).unwrap_or(manifest_path));
    }

    for package in &metadata.packages {
        add_targets(&package.targets, targets);

        // Look for local dependencies using information available since cargo v1.51
        // It's theoretically possible someone could use a newer version of rustfmt with
        // a much older version of `cargo`, but we don't try to explicitly support that scenario.
        // If someone reports an issue with path-based deps not being formatted, be sure to
        // confirm their version of `cargo` (not `cargo-fmt`) is >= v1.51
        // https://github.com/rust-lang/cargo/pull/8994
        for dependency in &package.dependencies {
            let Some(dependency_path) = dependency.path.as_ref() else {
                continue;
            };

            let manifest_path = PathBuf::from(dependency_path.as_str()).join("Cargo.toml");
            if !manifest_path.exists() {
                continue;
            }
            let package_manifest = fs::canonicalize(&manifest_path).unwrap_or(manifest_path);
            let traversal_manifest = cargo_workspace_manifest(&package_manifest)
                .unwrap_or_else(|| package_manifest.clone());
            if visited.insert(traversal_manifest.clone()) {
                get_targets_recursive(Some(&traversal_manifest), targets, visited)?;
            }
        }
    }

    Ok(())
}

/// Return the workspace manifest Cargo assigns to `package_manifest`.
///
/// Asking `cargo metadata` through a member manifest is not equivalent to
/// asking through its workspace root when nested/overlapping development
/// workspaces are present: Cargo can reject otherwise valid members as owned by
/// the wrong workspace. `cargo locate-project --workspace` performs the cheap
/// ownership lookup without loading the workspace graph. Recursing through the
/// returned root both avoids that ambiguity and lets one metadata call cover
/// all of the workspace's packages.
fn cargo_workspace_manifest(package_manifest: &Path) -> Option<PathBuf> {
    let cargo = env::var_os("CARGO").unwrap_or_else(|| OsString::from("cargo"));
    let output = Command::new(cargo)
        .args([
            "locate-project",
            "--workspace",
            "--message-format",
            "plain",
            "--offline",
            "--manifest-path",
        ])
        .arg(package_manifest)
        .output()
        .ok()?;
    if !output.status.success() {
        return None;
    }
    let path = str::from_utf8(&output.stdout).ok()?.trim();
    if path.is_empty() {
        return None;
    }
    let path = PathBuf::from(path);
    Some(fs::canonicalize(&path).unwrap_or(path))
}

fn get_targets_with_hitlist(
    manifest_path: Option<&Path>,
    hitlist: &[String],
    targets: &mut BTreeSet<Target>,
) -> Result<(), io::Error> {
    let metadata = get_cargo_metadata(manifest_path)?;
    let mut workspace_hitlist: BTreeSet<&String> = BTreeSet::from_iter(hitlist);

    for package in metadata.packages {
        if workspace_hitlist.remove(&package.name) {
            for target in package.targets {
                targets.insert(Target::from_target(&target));
            }
        }
    }

    if workspace_hitlist.is_empty() {
        Ok(())
    } else {
        let package = workspace_hitlist.iter().next().unwrap();
        Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!("package `{package}` is not a member of the workspace"),
        ))
    }
}

fn add_targets(target_paths: &[cargo_metadata::Target], targets: &mut BTreeSet<Target>) {
    for target in target_paths {
        targets.insert(Target::from_target(target));
    }
}

fn run_rustfmt(
    targets: &BTreeSet<Target>,
    fmt_args: &[String],
    verbosity: Verbosity,
) -> Result<i32, io::Error> {
    let by_edition = targets
        .iter()
        .inspect(|t| {
            if verbosity == Verbosity::Verbose {
                println!("[{} ({})] {:?}", t.kind, t.edition, t.path)
            }
        })
        .fold(BTreeMap::new(), |mut h, t| {
            h.entry(&t.edition).or_insert_with(Vec::new).push(&t.path);
            h
        });

    let mut status = vec![];
    for (edition, files) in by_edition {
        let stdout = if verbosity == Verbosity::Quiet {
            std::process::Stdio::null()
        } else {
            std::process::Stdio::inherit()
        };

        if verbosity == Verbosity::Verbose {
            print!("trustfmt");
            print!(" --edition {edition}");
            fmt_args.iter().for_each(|f| print!(" {}", f));
            files.iter().for_each(|f| print!(" {}", f.display()));
            println!();
        }

        let mut command = rustfmt_command();
        command
            .stdout(stdout)
            .args(files)
            .args(["--edition", edition.as_str()])
            .args(fmt_args);

        status.push(wait_for_formatter(&mut command)?);
    }

    Ok(status
        .into_iter()
        .find(|status| *status != SUCCESS)
        .unwrap_or(SUCCESS))
}

fn get_cargo_metadata(manifest_path: Option<&Path>) -> Result<cargo_metadata::Metadata, io::Error> {
    let mut cmd = cargo_metadata::MetadataCommand::new();
    cmd.no_deps();
    if let Some(manifest_path) = manifest_path {
        cmd.manifest_path(manifest_path);
    }
    cmd.other_options(vec![String::from("--offline")]);

    match cmd.exec() {
        Ok(metadata) => Ok(metadata),
        Err(_) => {
            cmd.other_options(vec![]);
            match cmd.exec() {
                Ok(metadata) => Ok(metadata),
                Err(error) => Err(io::Error::new(io::ErrorKind::Other, error.to_string())),
            }
        }
    }
}
