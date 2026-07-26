// trustd: Trust memory-coordination daemon.
//
// Repurposed (2026-06-18) from the dead SMT-echo daemon into the IN-MEMORY
// LIVE-AUTHORITY version of the `memory_jobserver` flock token bucket. It admits
// participating clients against one daemon-local configured ledger. It was
// introduced after concurrent `trustc` workers summed to 143 GB on a 36 GB box
// on 2026-06-17; it is not a measurement or hard ceiling for machine-wide RSS.
//
// The admission algorithm, the wire grammar, and the STATUS JSON schema all live
// in `trust_router::coordinator` so that this binary (the server) and the client
// (`coordinator::reserve`/`status`) share ONE definition and cannot drift. This
// file is the executable shell: parse `--socket <path>`, then `coordinator::serve`.
//
// Transport: one Unix-domain stream socket in a private per-euid runtime
// directory, NOT TCP 127.0.0.1:7878 and not one endpoint per Cargo target.
// Every normal verified build for the user therefore shares the same admission
// budget. Endpoints are born private and stale entries are reclaimed only by the
// next lock owner.
//
// Protocol (newline-delimited UTF-8, one request/response per line):
//   RESERVE <bytes> <pid> <label>  -> GRANTED <token> | DEGRADED
//   RELEASE <owned-token>          -> OK | ERR unowned-token
//   STATUS                         -> {...} one-line JSON (trustd.status.v1)
//   IDENTITY                       -> {...} one-line JSON (trustd.identity.v1)
//   PING                           -> PONG          (liveness / targo handshake)
// STATUS, IDENTITY, and PING are observational: none mutates budget state or
// refreshes the idle-shutdown clock, so a monitoring client cannot keep trustd
// alive.
//
// Admission is DEADLOCK-FREE: the mutex is never held while a RESERVE waiter
// sleeps (Condvar::wait_timeout releases it atomically), an impossible request
// (> budget / budget==0) returns DEGRADED immediately, and every connection
// owns its grants, so only that connection's RELEASE or connection loss returns
// capacity; STATUS token visibility confers no release authority. Client PIDs are
// diagnostic only because PID numbers are not globally meaningful across Linux
// namespaces. Age never expires legitimate long proofs. The daemon self-shuts
// down after an idle interval so a `targo`-spawned daemon does not outlive the
// build. A clean idle exit durably records CLEAN and leaves the socket stale for
// locked restart recovery. Any unclean exit leaves DIRTY and automatic restart
// is refused until explicit operator-attested solver quiescence recovery.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::ffi::OsString;
use std::path::PathBuf;

use trust_router::coordinator;

#[derive(Debug, PartialEq, Eq)]
enum Command {
    Serve(PathBuf),
    RecoverAfterCrash(PathBuf),
    Version,
    Help,
}

/// Parse trustd's deliberately small command line. Unknown or malformed
/// arguments are errors: silently accepting a typo can otherwise start a
/// long-lived daemon at an unintended socket (and made `trustd --version`
/// start the daemon before this parser existed).
fn parse_command(args: &[OsString]) -> Result<Command, String> {
    let mut socket = None;
    let mut informational = None;
    let mut recover_after_crash = false;
    let mut confirm_no_solvers = false;
    let mut it = args.iter();
    while let Some(arg) = it.next() {
        match arg.to_str() {
            Some("--socket") => {
                if socket.is_some() {
                    return Err("--socket may be specified only once".to_string());
                }
                let Some(path) = it.next() else {
                    return Err("--socket requires a non-empty path".to_string());
                };
                if path.is_empty() || path.to_string_lossy().starts_with('-') {
                    return Err("--socket requires a non-empty path".to_string());
                }
                socket = Some(PathBuf::from(path.as_os_str()));
            }
            Some("--version") | Some("-V") => {
                if informational.replace(Command::Version).is_some() {
                    return Err("only one of --version or --help may be specified".to_string());
                }
            }
            Some("--help") | Some("-h") => {
                if informational.replace(Command::Help).is_some() {
                    return Err("only one of --version or --help may be specified".to_string());
                }
            }
            Some("--recover-after-crash") => {
                if recover_after_crash {
                    return Err("--recover-after-crash may be specified only once".to_string());
                }
                recover_after_crash = true;
            }
            Some("--confirm-no-solvers") => {
                if confirm_no_solvers {
                    return Err("--confirm-no-solvers may be specified only once".to_string());
                }
                confirm_no_solvers = true;
            }
            value => {
                if let Some(path) = value.and_then(|value| value.strip_prefix("--socket=")) {
                    if socket.is_some() {
                        return Err("--socket may be specified only once".to_string());
                    }
                    if path.is_empty() {
                        return Err("--socket requires a non-empty path".to_string());
                    }
                    socket = Some(PathBuf::from(path));
                } else {
                    return Err(format!("unknown argument: {}", arg.to_string_lossy()));
                }
            }
        }
    }

    if let Some(command) = informational {
        if socket.is_some() || recover_after_crash || confirm_no_solvers {
            return Err(
                "recovery and --socket cannot be combined with --version or --help".to_string()
            );
        }
        return Ok(command);
    }

    match (recover_after_crash, confirm_no_solvers) {
        (false, true) => {
            return Err("--confirm-no-solvers requires --recover-after-crash".to_string());
        }
        (true, false) => {
            return Err(
                "--recover-after-crash requires the explicit --confirm-no-solvers assertion"
                    .to_string(),
            );
        }
        _ => {}
    }

    let socket = match socket {
        Some(socket) => socket,
        None => default_socket()?,
    };
    if recover_after_crash {
        Ok(Command::RecoverAfterCrash(socket))
    } else {
        Ok(Command::Serve(socket))
    }
}

/// Resolve the no-argument compatibility default: the orchestrator-provided
/// environment first, then the same private per-user endpoint normal verified
/// builds use. An explicit `--socket` remains available for tests/manual use.
fn default_socket() -> Result<PathBuf, String> {
    if let Some(path) = configured_default_socket(std::env::var_os(coordinator::SOCK_ENV))? {
        return Ok(path);
    }
    #[cfg(unix)]
    {
        coordinator::host_socket_path()
            .map_err(|error| format!("cannot establish private runtime endpoint: {error}"))
    }
    #[cfg(not(unix))]
    {
        Err("the trustd memory authority requires Unix-domain sockets".to_string())
    }
}

fn configured_default_socket(value: Option<OsString>) -> Result<Option<PathBuf>, String> {
    match value {
        Some(path) if path.is_empty() => {
            Err(format!("{} is configured with an empty path", coordinator::SOCK_ENV))
        }
        Some(path) => Ok(Some(PathBuf::from(path))),
        None => Ok(None),
    }
}

fn version_text() -> String {
    let release = option_env!("CFG_RELEASE").unwrap_or(env!("CARGO_PKG_VERSION"));
    let commit = option_env!("CFG_VER_HASH").filter(|value| !value.is_empty()).unwrap_or("unbound");
    format!(
        "trustd {release}\n\
         trust.identity=trustd\n\
         trust.package={}\n\
         trust.version={}\n\
         trust.protocol={}\n\
         commit-hash: {commit}\n\
         trust-repo-commit-hash: {commit}\n",
        env!("CARGO_PKG_NAME"),
        env!("CARGO_PKG_VERSION"),
        coordinator::STATUS_VERSION,
    )
}

fn help_text() -> &'static str {
    "Trust memory-coordination daemon\n\n\
     Usage: trustd [--socket <path>]\n\
            /absolute/path/to/selected/sysroot/bin/trustd --recover-after-crash --confirm-no-solvers [--socket <path>]\n\
            trustd --version\n\
            trustd --help\n\n\
     Options:\n\
       --socket <path>  Unix-domain socket to own\n\
       --recover-after-crash\n\
                        Clear an unclean epoch only after every prior solver is gone\n\
       --confirm-no-solvers\n\
                        Required operator attestation; not mechanically verified\n\
       Recovery path   Use the absolute trustd sibling of selected, validated Targo;\n\
                       never ambient PATH. This path relation is not packaged-byte proof.\n\
       -V, --version    Print build and protocol identity\n\
       -h, --help       Print this help\n"
}

fn main() {
    let args: Vec<OsString> = std::env::args_os().skip(1).collect();
    let (sock, recover_after_crash) = match parse_command(&args) {
        Ok(Command::Version) => {
            print!("{}", version_text());
            return;
        }
        Ok(Command::Help) => {
            print!("{}", help_text());
            return;
        }
        Ok(Command::Serve(sock)) => (sock, false),
        Ok(Command::RecoverAfterCrash(sock)) => (sock, true),
        Err(message) => {
            eprintln!("trustd: {message}\nTry 'trustd --help' for usage.");
            std::process::exit(2);
        }
    };

    // The daemon transport is a Unix-domain stream socket (see the module header),
    // and `coordinator::serve` is `#[cfg(unix)]`. On non-Unix hosts there is no
    // daemon authority. Verified crate mode rejects that platform before worker
    // fan-out; a direct trustd invocation fails here too.
    #[cfg(unix)]
    {
        if recover_after_crash {
            match coordinator::recover_dirty_epoch_after_quiescence(&sock) {
                Ok(true) => {
                    eprintln!(
                        "trustd: crash epoch recovered for {}; automatic startup is enabled",
                        sock.display()
                    );
                    return;
                }
                Ok(false) => {
                    eprintln!("trustd: epoch is already clean for {}", sock.display());
                    return;
                }
                Err(error) => {
                    eprintln!(
                        "trustd: fatal: cannot recover crash epoch {}: {error}",
                        sock.display()
                    );
                    std::process::exit(1);
                }
            }
        }
        eprintln!("trustd: memory-coordination daemon binding {}", sock.display());
        if let Err(e) = coordinator::serve(&sock) {
            eprintln!("trustd: fatal: cannot bind socket {}: {e}", sock.display());
            std::process::exit(1);
        }
        // `serve` returns only when the listener closes (the accept loop ended);
        // normal shutdown is the idle-timeout `exit(0)` inside `serve`.
    }
    #[cfg(not(unix))]
    {
        let _ = (&sock, recover_after_crash);
        eprintln!(
            "trustd: memory-coordination daemon is Unix-only (its transport is a \
             Unix-domain socket); no memory authority can run on {}.",
            std::env::consts::OS
        );
        std::process::exit(1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_socket_flag_space_form() {
        let args = vec![OsString::from("--socket"), OsString::from("/tmp/x.sock")];
        assert_eq!(parse_command(&args), Ok(Command::Serve(PathBuf::from("/tmp/x.sock"))));
    }

    #[test]
    fn parse_socket_flag_eq_form() {
        let args = vec![OsString::from("--socket=/tmp/y.sock")];
        assert_eq!(parse_command(&args), Ok(Command::Serve(PathBuf::from("/tmp/y.sock"))));
    }

    #[cfg(unix)]
    #[test]
    fn parse_socket_flag_preserves_non_utf8_path() {
        use std::os::unix::ffi::OsStringExt as _;

        let path = OsString::from_vec(b"/tmp/trustd-\xff.sock".to_vec());
        let args = vec![OsString::from("--socket"), path.clone()];
        assert_eq!(parse_command(&args), Ok(Command::Serve(PathBuf::from(path))));
    }

    #[test]
    fn informational_flags_never_resolve_a_socket() {
        assert_eq!(parse_command(&[OsString::from("--version")]), Ok(Command::Version));
        assert_eq!(parse_command(&[OsString::from("-V")]), Ok(Command::Version));
        assert_eq!(parse_command(&[OsString::from("--help")]), Ok(Command::Help));
        assert_eq!(parse_command(&[OsString::from("-h")]), Ok(Command::Help));
    }

    #[test]
    fn malformed_and_unknown_arguments_are_rejected() {
        for args in [
            vec![OsString::from("--socket")],
            vec![OsString::from("--socket=")],
            vec![OsString::from("--socket"), OsString::from("--version")],
            vec![OsString::from("--wat")],
            vec![OsString::from("--version"), OsString::from("--help")],
            vec![OsString::from("--version"), OsString::from("--socket=/tmp/x.sock")],
            vec![OsString::from("--recover-after-crash")],
            vec![OsString::from("--confirm-no-solvers")],
            vec![
                OsString::from("--recover-after-crash"),
                OsString::from("--confirm-no-solvers"),
                OsString::from("--confirm-no-solvers"),
            ],
        ] {
            assert!(parse_command(&args).is_err(), "accepted malformed args: {args:?}");
        }
    }

    #[test]
    fn recovery_requires_explicit_quiescence_confirmation() {
        let args = vec![
            OsString::from("--recover-after-crash"),
            OsString::from("--confirm-no-solvers"),
            OsString::from("--socket=/tmp/recover.sock"),
        ];
        assert_eq!(
            parse_command(&args),
            Ok(Command::RecoverAfterCrash(PathBuf::from("/tmp/recover.sock")))
        );
    }

    #[test]
    fn recovery_help_rejects_ambient_path_guidance() {
        let text = help_text();
        assert!(text.contains(
            "/absolute/path/to/selected/sysroot/bin/trustd --recover-after-crash"
        ));
        assert!(!text.contains("\n            trustd --recover-after-crash"));
        assert!(text.contains("never ambient PATH"));
        assert!(text.contains("not packaged-byte proof"));
    }

    #[test]
    fn empty_configured_default_socket_fails_instead_of_changing_authority() {
        let error = configured_default_socket(Some(OsString::new()))
            .expect_err("present-empty socket configuration is authoritative and invalid");
        assert!(error.contains(coordinator::SOCK_ENV));
        assert_eq!(
            configured_default_socket(Some(OsString::from("/tmp/explicit.sock"))),
            Ok(Some(PathBuf::from("/tmp/explicit.sock")))
        );
    }

    #[test]
    fn version_reports_release_provenance_and_protocol() {
        let text = version_text();
        let release = option_env!("CFG_RELEASE").unwrap_or(env!("CARGO_PKG_VERSION"));
        let expected_first_line = format!("trustd {release}");
        assert_eq!(text.lines().next(), Some(expected_first_line.as_str()));
        assert!(text.contains("trust.identity=trustd\n"));
        assert!(text.contains(&format!("trust.version={}\n", env!("CARGO_PKG_VERSION"))));
        assert!(text.contains(&format!("trust.protocol={}\n", coordinator::STATUS_VERSION)));
        let commit =
            option_env!("CFG_VER_HASH").filter(|value| !value.is_empty()).unwrap_or("unbound");
        if commit != "unbound" {
            assert_eq!(commit.len(), 40);
            assert!(commit.bytes().all(|byte| byte.is_ascii_hexdigit()));
        }
        assert!(text.contains(&format!("commit-hash: {commit}\n")));
        assert!(text.contains(&format!("trust-repo-commit-hash: {commit}\n")));
    }
}
