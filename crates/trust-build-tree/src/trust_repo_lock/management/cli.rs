//! Shared native administrative front door for Targo and Bootstrap.

use std::ffi::{OsStr, OsString};
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::time::Duration;

use super::{Acquire, Acquisition, Kind, Liveness, Manager, Release, Status};

mod incremental;

pub const PROTOCOL: &str = "trust-build-tree-manager-v2";
const USAGE: &str = "\
Usage: targo trust repo lock acquire --kind build|measurement --pid PID [--purpose TEXT] [--wait SECONDS] [--repo-root DIR] [--contract TEXT] [--break --reason TEXT]
       targo trust repo lock release TOKEN [--repo-root DIR]
       targo trust repo lock status [--repo-root DIR]
       targo trust repo lock break --reason TEXT [--repo-root DIR]
       targo trust repo lock reclaim-incremental [--apply] [--quiet] [--max-gib N] [--min-free-gib N] [--repo-root DIR]

The named owner must span the protected work. --pid is required: a transient
Targo frontend or helper must never become a holder that is stale at birth.
Acquisition prints only its token. Exit 0 succeeds, 3 means busy, 4 means a
foreign or parent-managed holder was retained, and 2 means an invalid request
or unavailable observation. Status returns 0 only when the tree is free.
TRUST_REPO, TRUST_BUILD_LOCK_WAIT and TRUST_BUILD_LOCK_TOKEN supply defaults;
destructive recovery always requires an explicit --reason argument.
This command coordinates participating actors; it grants no proof authority.
";

#[derive(Debug, PartialEq, Eq)]
enum Operation {
    Help,
    Protocol,
    Acquire {
        kind: Kind,
        pid: u32,
        purpose: String,
        contract: String,
        wait: Option<u64>,
        reason: Option<String>,
    },
    Release(String),
    Status,
    Break(String),
}
#[derive(Debug, PartialEq, Eq)]
struct Arguments {
    operation: Operation,
    root: Option<PathBuf>,
}

#[derive(Default)]
pub(super) struct Environment {
    pub(super) root: Option<OsString>,
    wait: Option<OsString>,
    token: Option<OsString>,
    incremental_max: Option<OsString>,
    incremental_min_free: Option<OsString>,
}

fn text(value: &OsStr) -> Result<String, String> {
    value.to_str().map(str::to_owned).ok_or_else(|| "this option requires UTF-8 text".into())
}
fn integer(value: &OsStr) -> Result<u64, String> {
    let value = value
        .to_str()
        .filter(|value| !value.is_empty() && value.bytes().all(|byte| byte.is_ascii_digit()))
        .ok_or("expected a nonnegative integer")?;
    value.parse().map_err(|_| "integer exceeds its supported range".into())
}

fn parse(args: &[OsString]) -> Result<Arguments, String> {
    if args.len() > 32 || args.iter().any(|arg| arg.as_encoded_bytes().len() > 32768) {
        return Err("build-tree request exceeds its argument bound".into());
    }
    if args.is_empty() || args == [OsString::from("--help")] || args == [OsString::from("-h")] {
        return Ok(Arguments { operation: Operation::Help, root: None });
    }
    if args == [OsString::from("--protocol")] {
        return Ok(Arguments { operation: Operation::Protocol, root: None });
    }
    let verb = text(&args[0])?;
    if !matches!(verb.as_str(), "acquire" | "release" | "status" | "break") {
        return Err(format!("unknown build-tree operation {verb}"));
    }
    let mut values = std::collections::BTreeMap::new();
    let mut release = None;
    let mut break_flag = false;
    let mut index = 1;
    while index < args.len() {
        let flag = &args[index];
        if matches!(flag.to_str(), Some("--help" | "-h")) {
            if index + 1 != args.len() {
                return Err("help must be the final argument".into());
            }
            return Ok(Arguments { operation: Operation::Help, root: None });
        }
        if flag == "--break" && verb == "acquire" && !break_flag {
            break_flag = true;
            index += 1;
            continue;
        }
        let key = flag.to_str().unwrap_or("");
        let allowed = key == "--repo-root"
            || match verb.as_str() {
                "acquire" => matches!(
                    key,
                    "--kind" | "--pid" | "--purpose" | "--contract" | "--wait" | "--reason"
                ),
                "break" => key == "--reason",
                _ => false,
            };
        if allowed {
            let value = args.get(index + 1).ok_or_else(|| format!("{key} requires a value"))?;
            if values.insert(key.to_owned(), value.clone()).is_some() {
                return Err(format!("repeated option {key}"));
            }
            index += 2;
        } else if verb == "release" && release.is_none() && !key.starts_with('-') {
            release = Some(text(flag)?);
            index += 1;
        } else {
            return Err(format!("unexpected build-tree argument {}", flag.to_string_lossy()));
        }
    }
    let root = values.remove("--repo-root").map(PathBuf::from);
    let operation = match verb.as_str() {
        "acquire" => {
            let kind = match values.remove("--kind").as_deref().and_then(OsStr::to_str) {
                Some("build") => Kind::Build,
                Some("measurement") => Kind::Measurement,
                _ => return Err("acquire requires --kind build|measurement".into()),
            };
            let pid = values
                .remove("--pid")
                .ok_or("acquire requires --pid of the durable batch owner")?;
            let pid = u32::try_from(integer(&pid)?)
                .ok()
                .filter(|pid| *pid > 1 && *pid <= i32::MAX as u32)
                .ok_or("--pid must name a durable positive process, not init or a process group")?;
            let reason = values.remove("--reason").map(|reason| text(&reason)).transpose()?;
            if break_flag && reason.as_ref().is_none_or(|reason| reason.trim().is_empty()) {
                return Err("--break requires an explicit meaningful --reason".into());
            }
            Operation::Acquire {
                kind,
                pid,
                purpose: values
                    .remove("--purpose")
                    .map(|value| text(&value))
                    .transpose()?
                    .unwrap_or_else(|| "unspecified".into()),
                contract: values
                    .remove("--contract")
                    .map(|value| text(&value))
                    .transpose()?
                    .unwrap_or_else(|| "the build tree is exclusive".into()),
                wait: values.remove("--wait").map(|value| integer(&value)).transpose()?,
                reason,
            }
        }
        "release" => Operation::Release(
            release
                .filter(|token| !token.is_empty())
                .ok_or("release requires the original token")?,
        ),
        "status" => Operation::Status,
        "break" => Operation::Break(
            values
                .remove("--reason")
                .map(|value| text(&value))
                .transpose()?
                .filter(|reason| !reason.trim().is_empty())
                .ok_or("break requires an explicit meaningful --reason")?,
        ),
        _ => unreachable!(),
    };
    Ok(Arguments { operation, root })
}

pub(super) fn default_root(environment: &Environment) -> io::Result<PathBuf> {
    if let Some(root) = &environment.root {
        if !root.is_empty() {
            return Ok(PathBuf::from(root));
        }
    }
    let current = std::env::current_dir()?;
    current
        .ancestors()
        .find(|root| root.join("x.py").is_file() && root.join("src/bootstrap/Cargo.toml").is_file())
        .map(Path::to_owned)
        .ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::InvalidInput,
                "select --repo-root or run inside a Trust checkout",
            )
        })
}

/// The native administrative entry point; no shell facade or subprocess runs.
pub fn run(args: &[OsString]) -> u8 {
    let environment = Environment {
        root: std::env::var_os("TRUST_REPO"),
        wait: std::env::var_os("TRUST_BUILD_LOCK_WAIT"),
        token: std::env::var_os("TRUST_BUILD_LOCK_TOKEN"),
        incremental_max: std::env::var_os("TRUST_INCREMENTAL_MAX_GIB"),
        incremental_min_free: std::env::var_os("TRUST_INCREMENTAL_MIN_FREE_GIB"),
    };
    execute(args, &environment, &mut io::stdout().lock(), &mut io::stderr().lock())
}

fn execute(
    args: &[OsString],
    environment: &Environment,
    output: &mut dyn Write,
    diagnostics: &mut dyn Write,
) -> u8 {
    match checked(args, environment, output, diagnostics) {
        Ok(code) => code,
        Err(error) => {
            let _ = writeln!(diagnostics, "trust build-tree lock: {error}");
            2
        }
    }
}

fn checked(
    args: &[OsString],
    environment: &Environment,
    output: &mut dyn Write,
    diagnostics: &mut dyn Write,
) -> Result<u8, String> {
    if args.first().is_some_and(|arg| arg == "exec") {
        return Err("native exec requires the early `targo --unverified resource fixed -- repo-lock-exec` entry; no late descriptor reimport or fallback".into());
    }
    if args.first().is_some_and(|arg| arg == "reclaim-incremental") {
        return incremental::checked(&args[1..], environment, output, diagnostics);
    }
    let args = parse(args)?;
    if args.operation == Operation::Help {
        output.write_all(USAGE.as_bytes()).map_err(|error| error.to_string())?;
        return Ok(0);
    }
    if args.operation == Operation::Protocol {
        writeln!(output, "{PROTOCOL}").map_err(|error| error.to_string())?;
        return Ok(0);
    }
    let root = args
        .root
        .map(Ok)
        .unwrap_or_else(|| default_root(environment))
        .map_err(|error| error.to_string())?;
    let manager = Manager::open(&root).map_err(|error| error.to_string())?;
    let result = match args.operation {
        Operation::Acquire { kind, pid, purpose, contract, wait, reason } => {
            let wait = wait
                .map(Ok)
                .unwrap_or_else(|| environment.wait.as_deref().map(integer).unwrap_or(Ok(0)))?;
            let inherited_token = environment
                .token
                .as_deref()
                .filter(|token| !token.is_empty())
                .map(text)
                .transpose()?;
            match manager
                .acquire(&Acquire {
                    kind,
                    owner_pid: pid,
                    purpose,
                    contract,
                    wait: Duration::from_secs(wait),
                    inherited_token,
                    break_reason: reason,
                })
                .map_err(|error| error.to_string())?
            {
                Acquisition::Acquired(token) => {
                    // Maintenance belongs to the native owner, before token
                    // delivery. It never spawns a detached helper or leaves a
                    // second process holding the caller's output pipes open.
                    incremental::on_acquired(&root, environment, diagnostics);
                    if let Err(error) = writeln!(output, "{token}") {
                        // No successful complete reply escaped. Cancel our
                        // acquisition; a surviving writer is still adopted.
                        let release = manager.release(&token);
                        return Err(format!(
                            "token delivery failed: {error}; acquisition rollback: {release:?}"
                        ));
                    }
                    0
                }
                Acquisition::Borrowed(token) => {
                    writeln!(output, "{token}").map_err(|error| error.to_string())?;
                    0
                }
                Acquisition::Busy(status) => {
                    describe(&status, diagnostics).map_err(|error| error.to_string())?;
                    3
                }
            }
        }
        Operation::Release(token) => {
            match manager.release(&token).map_err(|error| error.to_string())? {
                Release::AlreadyFree | Release::Released => 0,
                Release::HandedOver(writer) => {
                    writeln!(
                        diagnostics,
                        "tree retained for surviving {:?} writer pid {:?}",
                        writer.kind, writer.pid
                    )
                    .map_err(|error| error.to_string())?;
                    0
                }
                Release::ForeignHolder | Release::ParentManaged => {
                    writeln!(diagnostics, "original foreign or parent-managed holder retained")
                        .map_err(|error| error.to_string())?;
                    4
                }
            }
        }
        Operation::Status => {
            let status = manager.status().map_err(|error| error.to_string())?;
            if status.is_free() {
                writeln!(output, "trust build-tree lock: free")
                    .map_err(|error| error.to_string())?;
                0
            } else {
                describe(&status, diagnostics).map_err(|error| error.to_string())?;
                3
            }
        }
        Operation::Break(reason) => {
            manager.break_holder(&reason).map_err(|error| error.to_string())?;
            0
        }
        Operation::Help | Operation::Protocol => unreachable!(),
    };
    Ok(result)
}

fn describe(status: &Status, output: &mut dyn Write) -> io::Result<()> {
    if let Some(holder) = &status.holder {
        let live = match holder.liveness {
            Liveness::Live => "alive",
            Liveness::Gone => "gone",
            Liveness::Unknown => "unknown",
        };
        writeln!(
            output,
            "trust build-tree lock: {} ({}, pid {}, {live})",
            if holder.is_withheld() { "WITHHELD" } else { "held" },
            holder.kind,
            holder.pid
        )?;
        writeln!(
            output,
            "  since: {}",
            holder.fields.get("started").map_or("unknown", String::as_str)
        )?;
        writeln!(
            output,
            "  purpose: {}\n  command: {}\n  contract: {}",
            holder.purpose, holder.command, holder.contract
        )?;
        if holder.parent_managed {
            writeln!(output, "  actual native outer cleanup owns release")?;
        }
    } else if status.malformed_holder {
        writeln!(output, "trust build-tree lock: incomplete holder retained")?;
    }
    for writer in &status.writers {
        writeln!(
            output,
            "  {} {:?} writer pid {:?}: {}",
            if writer.covered { "covered" } else { "unwrapped" },
            writer.kind,
            writer.pid,
            writer.command
        )?;
    }
    Ok(())
}

#[cfg(test)]
mod tests;
