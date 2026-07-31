// trustup: Trust-owned local toolchain selector.
//
// This tool deliberately manages only TRUSTUP_HOME. It never reads or writes
// host Rust installer state.

use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};
use std::{env, fs};

const VERSION: &str = env!("CARGO_PKG_VERSION");

const CANONICAL_TOOLS: &[&str] = &[
    "trustc",
    "targo", // Trust: produced frontend binary is targo
    "targo-trust",
    "trustdoc",
    "trustfmt",
    "tippy",
    "targo-tippy",
    "tippy-driver",
    "trust-analyzer",
    "trust-miri",
    "targo-miri", // Trust: produced component binary is targo-miri
];

const REQUIRED_TOOLS: &[&str] = &["trustc", "targo", "targo-trust"];

const INHERITED_PUBLIC_NAMES: &[&str] = &[
    "rustc",
    "cargo",
    "rustdoc",
    "rustfmt",
    "clippy",
    "cargo-clippy",
    "clippy-driver",
    "targo-clippy",
    "trust-clippy",
    "trust-clippy-driver",
    "rust-analyzer",
    "miri",
    "cargo-miri",
];

/// The only inherited public names a Trust root may expose, and the canonical
/// Trust binaries each one is permitted to be an alias *of*.
///
/// This mirrors `STOCK_ALIAS_TARGETS` in `scripts/off_stock_rust_audit.py` — the
/// existing encoding of "a stock spelling is legitimate only when it is an alias
/// of the corresponding Trust frontend in the same toolchain directory" — and is
/// deliberately a strict *subset* of it on both axes, so nothing trustup admits
/// could be rejected by that audit:
///
///  * Fewer names. The audit also maps `rustdoc`/`rustfmt`/`cargo-clippy`/
///    `clippy-driver`, because it must grade arbitrary third-party trees. A
///    Trust sysroot never materializes those: `tool::upstream_compat_bin_for_tool_source`
///    emits `cargo` and nothing else, and `rustc` is materialized separately by
///    `materialize_local_compiler_aliases`. Those two exist solely because
///    rustup refuses to register a toolchain whose `bin/` lacks them. Any other
///    inherited spelling in a Trust root is still an unconditional rejection.
///  * A stricter identity test. The audit accepts same-inode **or** equal
///    size-and-SHA-256, since it audits paths it did not produce and that may
///    have been copied across filesystems. Here the aliases are produced by
///    bootstrap in one directory, so same-device/same-inode is both sufficient
///    and the fail-closed choice: it cannot admit a distinct executable that
///    merely happens to hash the same as a sibling at audit time.
const INHERITED_ALIAS_TARGETS: &[(&str, &[&str])] =
    &[("rustc", &["trustc"]), ("cargo", &["targo", "tcargo"])];

fn main() -> ExitCode {
    match run(env::args_os().skip(1).collect()) {
        Ok(code) => code,
        Err(message) => {
            eprintln!("trustup: error: {message}");
            ExitCode::from(2)
        }
    }
}

fn run(args: Vec<OsString>) -> Result<ExitCode, String> {
    let Some(command) = args.first().and_then(|arg| arg.to_str()) else {
        print_usage();
        return Ok(ExitCode::SUCCESS);
    };

    match command {
        "-h" | "--help" | "help" => {
            print_usage();
            Ok(ExitCode::SUCCESS)
        }
        "-V" | "--version" | "version" => {
            println!("trustup {VERSION}");
            Ok(ExitCode::SUCCESS)
        }
        "home" => {
            println!("{}", trustup_home()?.display());
            Ok(ExitCode::SUCCESS)
        }
        "toolchain" => toolchain_command(&args[1..]),
        "default" => default_command(&args[1..]),
        "which" => which_command(&args[1..]),
        "run" => run_command(&args[1..]),
        "doctor" => doctor_command(),
        "capability" => capability_command(&args[1..]),
        other => Err(format!("unknown command `{other}`")),
    }
}

fn print_usage() {
    println!(
        "trustup {VERSION}

Usage:
  trustup toolchain link <name> <root>
  trustup toolchain list
  trustup default <name>
  trustup which <trust-tool>
  trustup run <trust-tool> [args...]
  trustup capability verify
  trustup doctor

Environment:
  TRUSTUP_HOME       Trustup state root (default: ~/.trustup)
  TRUSTUP_TOOLCHAIN  Selected Trust toolchain name (default: default file)
"
    );
}

fn trustup_home() -> Result<PathBuf, String> {
    if let Some(home) = env::var_os("TRUSTUP_HOME") {
        return Ok(PathBuf::from(home));
    }
    let home = env::var_os("HOME")
        .or_else(|| env::var_os("USERPROFILE"))
        .ok_or_else(|| "HOME is not set; set TRUSTUP_HOME".to_string())?;
    Ok(PathBuf::from(home).join(".trustup"))
}

fn toolchains_dir() -> Result<PathBuf, String> {
    Ok(trustup_home()?.join("toolchains"))
}

fn default_file() -> Result<PathBuf, String> {
    Ok(trustup_home()?.join("default"))
}

fn toolchain_command(args: &[OsString]) -> Result<ExitCode, String> {
    match args.first().and_then(|arg| arg.to_str()) {
        Some("link") => {
            if args.len() != 3 {
                return Err("usage: trustup toolchain link <name> <root>".to_string());
            }
            let name = valid_toolchain_name(&args[1])?;
            let root = PathBuf::from(&args[2]);
            link_toolchain(name, &root)?;
            Ok(ExitCode::SUCCESS)
        }
        Some("list") => {
            list_toolchains()?;
            Ok(ExitCode::SUCCESS)
        }
        _ => Err("usage: trustup toolchain <link|list> ...".to_string()),
    }
}

fn valid_toolchain_name(name: &OsString) -> Result<&str, String> {
    let name = name.to_str().ok_or_else(|| "toolchain name must be UTF-8".to_string())?;
    if name.is_empty() || name.contains('/') || name.contains('\\') || name == "." || name == ".." {
        return Err("toolchain name must be a plain Trustup name".to_string());
    }
    Ok(name)
}

fn link_toolchain(name: &str, root: &Path) -> Result<(), String> {
    let root = root
        .canonicalize()
        .map_err(|error| format!("toolchain root {} is not usable: {error}", root.display()))?;
    validate_toolchain_root(&root)?;

    let toolchains = toolchains_dir()?;
    fs::create_dir_all(&toolchains).map_err(|error| {
        format!("failed to create Trustup toolchain directory {}: {error}", toolchains.display())
    })?;

    let link = toolchains.join(name);
    if link.exists() {
        return Err(format!("toolchain `{name}` already exists at {}", link.display()));
    }
    symlink_dir(&root, &link).map_err(|error| {
        format!("failed to link Trust toolchain `{name}` to {}: {error}", root.display())
    })?;
    println!("linked {name} -> {}", root.display());
    Ok(())
}

#[cfg(unix)]
fn symlink_dir(target: &Path, link: &Path) -> std::io::Result<()> {
    std::os::unix::fs::symlink(target, link)
}

#[cfg(windows)]
fn symlink_dir(target: &Path, link: &Path) -> std::io::Result<()> {
    std::os::windows::fs::symlink_dir(target, link)
}

fn list_toolchains() -> Result<(), String> {
    let toolchains = toolchains_dir()?;
    if !toolchains.is_dir() {
        return Ok(());
    }
    let selected = selected_name().ok();
    for entry in fs::read_dir(&toolchains)
        .map_err(|error| format!("failed to read {}: {error}", toolchains.display()))?
    {
        let entry = entry.map_err(|error| format!("failed to read toolchain entry: {error}"))?;
        let name = entry.file_name();
        let name = name.to_string_lossy();
        let marker = if selected.as_deref() == Some(name.as_ref()) { "*" } else { " " };
        println!("{marker} {name}\t{}", entry.path().display());
    }
    Ok(())
}

fn default_command(args: &[OsString]) -> Result<ExitCode, String> {
    if args.len() != 1 {
        return Err("usage: trustup default <name>".to_string());
    }
    let name = valid_toolchain_name(&args[0])?;
    let root = toolchains_dir()?.join(name);
    validate_toolchain_root(&root)?;
    let default = default_file()?;
    if let Some(parent) = default.parent() {
        fs::create_dir_all(parent).map_err(|error| {
            format!("failed to create Trustup state directory {}: {error}", parent.display())
        })?;
    }
    fs::write(&default, format!("{name}\n"))
        .map_err(|error| format!("failed to write {}: {error}", default.display()))?;
    println!("default {name}");
    Ok(ExitCode::SUCCESS)
}

fn selected_name() -> Result<String, String> {
    if let Ok(name) = env::var("TRUSTUP_TOOLCHAIN") {
        if name.trim().is_empty() {
            return Err("TRUSTUP_TOOLCHAIN is empty".to_string());
        }
        return Ok(name);
    }
    let default = default_file()?;
    let name = fs::read_to_string(&default)
        .map_err(|_| "no Trustup default toolchain selected".to_string())?
        .trim()
        .to_string();
    if name.is_empty() {
        return Err(format!("{} is empty", default.display()));
    }
    Ok(name)
}

fn selected_root() -> Result<PathBuf, String> {
    let name = selected_name()?;
    let root = toolchains_dir()?.join(&name);
    validate_toolchain_root(&root)?;
    Ok(root)
}

fn which_command(args: &[OsString]) -> Result<ExitCode, String> {
    if args.len() != 1 {
        return Err("usage: trustup which <trust-tool>".to_string());
    }
    let tool = args[0].to_str().ok_or_else(|| "tool name must be UTF-8".to_string())?;
    let path = selected_tool_path(tool)?;
    println!("{}", path.display());
    Ok(ExitCode::SUCCESS)
}

fn run_command(args: &[OsString]) -> Result<ExitCode, String> {
    if args.is_empty() {
        return Err("usage: trustup run <trust-tool> [args...]".to_string());
    }
    let tool = args[0].to_str().ok_or_else(|| "tool name must be UTF-8".to_string())?;
    let path = selected_tool_path(tool)?;
    let status = Command::new(&path)
        .args(&args[1..])
        .status()
        .map_err(|error| format!("failed to run {}: {error}", path.display()))?;
    Ok(status.code().map_or(ExitCode::FAILURE, |code| {
        u8::try_from(code).map_or(ExitCode::FAILURE, ExitCode::from)
    }))
}

fn capability_command(args: &[OsString]) -> Result<ExitCode, String> {
    match args.first().and_then(|arg| arg.to_str()) {
        Some("verify") if args.len() == 1 => {
            let root = selected_root()?;
            print_capability_report(&root);
            Ok(ExitCode::SUCCESS)
        }
        _ => Err("usage: trustup capability verify".to_string()),
    }
}

fn doctor_command() -> Result<ExitCode, String> {
    let root = selected_root()?;
    println!("Trustup home: {}", trustup_home()?.display());
    println!("Trust root: {}", root.display());
    print_capability_report(&root);
    Ok(ExitCode::SUCCESS)
}

fn selected_tool_path(tool: &str) -> Result<PathBuf, String> {
    if !CANONICAL_TOOLS.contains(&tool) {
        return Err(format!("`{tool}` is not a canonical Trust tool name"));
    }
    let path = selected_root()?.join("bin").join(exe_name(tool));
    if !path.is_file() {
        return Err(format!("selected Trust root does not expose `{tool}`"));
    }
    Ok(path)
}

fn validate_toolchain_root(root: &Path) -> Result<(), String> {
    let bin = root.join("bin");
    if !bin.is_dir() {
        return Err(format!("Trust root has no bin directory: {}", root.display()));
    }
    for tool in REQUIRED_TOOLS {
        let path = bin.join(exe_name(tool));
        if !path.is_file() {
            return Err(format!("Trust root is missing canonical `{tool}` at {}", path.display()));
        }
    }
    for inherited in INHERITED_PUBLIC_NAMES {
        let path = bin.join(exe_name(inherited));
        // `Path::exists` follows symlinks and so reports a *dangling* alias as
        // absent, which would skip the check entirely for the one shape most
        // likely to be a leftover pointing outside the root. Ask about the link
        // itself; a dangling link then also fails the alias test below, because
        // it has no resolvable inode to match a canonical sibling with.
        if fs::symlink_metadata(&path).is_err() {
            continue;
        }
        if inherited_alias_is_authenticated(&bin, inherited, &path) {
            continue;
        }
        return Err(format!(
            "Trust root exposes inherited public name `{inherited}` at {}; use a Trust-only root",
            path.display()
        ));
    }
    Ok(())
}

/// True when `path` is one of the two rustup-required inherited spellings *and*
/// is the very same on-disk artifact as a canonical Trust binary sitting beside
/// it in `bin`. See `INHERITED_ALIAS_TARGETS`.
fn inherited_alias_is_authenticated(bin: &Path, inherited: &str, path: &Path) -> bool {
    let Some(targets) = INHERITED_ALIAS_TARGETS
        .iter()
        .find(|(name, _)| *name == inherited)
        .map(|(_, targets)| *targets)
    else {
        return false;
    };
    targets.iter().any(|target| same_artifact(path, &bin.join(exe_name(target))))
}

/// Same regular file, reached by two names: a hardlink or a symlink within the
/// same toolchain directory. Both metadata calls follow symlinks, so the
/// `cargo -> targo` symlink form and the `cargo`/`targo` hardlink form (which is
/// what this tree's bootstrap actually produces) are both recognised.
#[cfg(unix)]
fn same_artifact(left: &Path, right: &Path) -> bool {
    use std::os::unix::fs::MetadataExt;

    let (Ok(left), Ok(right)) = (fs::metadata(left), fs::metadata(right)) else {
        return false;
    };
    left.is_file()
        && right.is_file()
        && left.dev() == right.dev()
        && left.ino() == right.ino()
}

/// Non-Unix hosts have no stable-Rust inode identity (`MetadataExt::file_index`
/// is behind `windows_by_handle`), so there is no way to *prove* two names are
/// one artifact here. Fail closed: no inherited spelling is admitted, which is
/// exactly the behaviour these platforms had before same-inode admission
/// existed. A Windows Trust root must be Trust-only.
#[cfg(not(unix))]
fn same_artifact(_left: &Path, _right: &Path) -> bool {
    false
}

fn print_capability_report(root: &Path) {
    let bin = root.join("bin");
    for tool in CANONICAL_TOOLS {
        let path = bin.join(exe_name(tool));
        let status = if path.is_file() { "present" } else { "missing" };
        println!("{tool}: {status}");
    }
}

fn exe_name(tool: &str) -> String {
    format!("{tool}{}", env::consts::EXE_SUFFIX)
}

#[cfg(test)]
mod tests;
