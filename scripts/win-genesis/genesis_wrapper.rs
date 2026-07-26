// Generic Windows genesis stage0 wrapper for Trust.
//
// One compiled exe, copied to bin/<trust-name>.exe. Each copy reads its sidecar
// `<exe-dir>/<trust-name>.wrap` (key=value lines) to learn what real tool to
// drive. Mirrors scripts/create_local_genesis_stage0.py's #!/bin/sh wrapper:
//   * strips Trust-only `-Ztrust-verify=off` and `-Ztrust-*` flags (both split
//     and joined forms) that a stock rustc cannot parse;
//   * otherwise forwards all args to the real tool and propagates its exit code.
// `mode=stub` entries (e.g. targo-trust) have no inherited equivalent.

use std::io::{self, Write as _};
use std::process::{Command, exit};
use std::{env, fs};

fn read_wrap(dir: &std::path::Path, stem: &str) -> std::collections::HashMap<String, String> {
    let mut m = std::collections::HashMap::new();
    if let Ok(s) = fs::read_to_string(dir.join(format!("{stem}.wrap"))) {
        for line in s.lines() {
            if let Some((k, v)) = line.split_once('=') {
                m.insert(k.trim().to_string(), v.trim().to_string());
            }
        }
    }
    m
}

fn is_trust_z_flag(value: &str) -> bool {
    value == "trust-verify=off" || value.starts_with("trust-")
}

fn is_product_version_query(args: &[String], preserve_compiler_info: bool) -> bool {
    matches!(args, [flag] if matches!(flag.as_str(), "--version" | "-V"))
        || (!preserve_compiler_info
            && matches!(args, [flag] if matches!(flag.as_str(), "-vV" | "-Vv")))
        || matches!(
            args,
            [first, second]
                if matches!(
                    (first.as_str(), second.as_str()),
                    ("--version", "--verbose") | ("--verbose", "--version")
                )
        )
}

fn run_version_query(cfg: &std::collections::HashMap<String, String>, real: &str) -> ! {
    let mut command = Command::new(real);
    if let Some(prefix) = cfg.get("version_prefix") {
        command.arg(prefix);
    }
    let output = command.arg("--version").output().expect("spawn real tool version query");
    let source = cfg.get("source").map(String::as_str).unwrap_or_default();
    let version = cfg.get("version").map(String::as_str).unwrap_or_default();
    let binary = cfg.get("trust").map(String::as_str).unwrap_or_default();
    let stdout = String::from_utf8_lossy(&output.stdout);
    for (index, line) in stdout.lines().enumerate() {
        let version_rest = if index == 0 {
            line.strip_prefix(source).and_then(|rest| rest.strip_prefix(' '))
        } else {
            None
        };
        if let Some(rest) = version_rest {
            println!("{version} {rest}");
        } else if line.starts_with("binary: ") {
            println!("binary: {binary}");
        } else {
            println!("{line}");
        }
    }
    let _ = io::stderr().write_all(&output.stderr);
    exit(output.status.code().unwrap_or(1));
}

fn main() {
    let exe = env::current_exe().expect("current_exe");
    let dir = exe.parent().expect("exe parent").to_path_buf();
    let stem = exe.file_stem().unwrap().to_string_lossy().to_string();
    let cfg = read_wrap(&dir, &stem);
    let mut args: Vec<String> = env::args().skip(1).collect();

    if cfg.get("marker").is_some_and(|marker| args.first() == Some(marker)) {
        args.remove(0);
    }

    if cfg.get("mode").map(|s| s.as_str()) == Some("stub") {
        let name = cfg.get("name").cloned().unwrap_or_else(|| stem.clone());
        if args.len() == 1 && (args[0] == "--version" || args[0] == "-V") {
            println!("{name} local-genesis-adapter");
            exit(0);
        }
        let msg = cfg.get("msg").cloned().unwrap_or_default();
        eprintln!("{msg}; build a real Trust stage0 artifact before invoking {name}");
        exit(127);
    }

    let real = match cfg.get("real") {
        Some(r) => r.clone(),
        None => {
            eprintln!("genesis wrapper: no `real` configured for {stem}");
            exit(2);
        }
    };
    // Compiler version strings remain inherited: build scripts such as libc
    // assert that `rustc --version` starts with "rustc". Tippy wrappers opt in
    // through their sidecars because their public product identity must be
    // canonical even in the local genesis adapter.
    let preserve_compiler_info = cfg.get("compiler_info").is_some_and(|value| value == "1");
    if cfg.contains_key("version") && is_product_version_query(&args, preserve_compiler_info) {
        run_version_query(&cfg, &real);
    }

    // Strip only Trust-owned -Z flags; a stock or third-party flag may contain
    // the word "trust" in its value and still must be forwarded verbatim.
    let mut filtered: Vec<String> = Vec::with_capacity(args.len());
    let mut i = 0;
    while i < args.len() {
        let a = &args[i];
        if a == "-Z" {
            if i + 1 < args.len() {
                let val = &args[i + 1];
                if !is_trust_z_flag(val) {
                    filtered.push("-Z".to_string());
                    filtered.push(val.clone());
                }
                i += 2;
                continue;
            }
            filtered.push(a.clone());
            i += 1;
        } else if a.strip_prefix("-Z").is_some_and(is_trust_z_flag) {
            i += 1;
        } else {
            if cfg.get("arg_from") == Some(a) {
                filtered.push(
                    cfg.get("arg_to").cloned().expect("genesis wrapper arg_from requires arg_to"),
                );
            } else {
                filtered.push(a.clone());
            }
            i += 1;
        }
    }

    let mut command = Command::new(&real);
    if let Some(prefix) = cfg.get("prefix") {
        command.arg(prefix);
    }
    let status = command.args(&filtered).status().expect("spawn real tool");
    exit(status.code().unwrap_or(1));
}
