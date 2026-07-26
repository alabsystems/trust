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
        if path.exists() {
            return Err(format!(
                "Trust root exposes inherited public name `{inherited}` at {}; use a Trust-only root",
                path.display()
            ));
        }
    }
    Ok(())
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
