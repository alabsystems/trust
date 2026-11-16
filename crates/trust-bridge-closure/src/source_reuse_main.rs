//! Lightweight source-input verifier; it imports no Clean kernel or olean reader.
use std::ffi::OsStr;
use std::path::PathBuf;
use std::process::ExitCode;

const USAGE: &str = "usage: bridge_source_reuse --verify-source-reuse <repo> <INDEX|CHECKOUT|commit> | --prepare-source-reuse <repo> <original-artifact-commit> | --refresh-source-reuse <repo>";

fn main() -> ExitCode {
    let mut args = std::env::args_os().skip(1);
    let first = args.next();
    if matches!(first.as_deref(), Some(x) if x == OsStr::new("--verify-source-reuse") || x == OsStr::new("--prepare-source-reuse") || x == OsStr::new("--refresh-source-reuse"))
    {
        let Some(repo) = args.next() else {
            eprintln!("{USAGE}");
            return ExitCode::from(2);
        };
        let repo = PathBuf::from(repo);
        use trust_bridge_closure::source_reuse::{self, Subject};
        let result = if first.as_deref() == Some(OsStr::new("--refresh-source-reuse")) {
            if args.next().is_some() {
                return ExitCode::from(2);
            }
            source_reuse::refresh(&repo).map(Some)
        } else {
            let Some(argument) = args.next() else {
                eprintln!("{USAGE}");
                return ExitCode::from(2);
            };
            if args.next().is_some() {
                return ExitCode::from(2);
            }
            let Some(argument) = argument.to_str() else {
                return ExitCode::from(2);
            };
            if first.as_deref() == Some(OsStr::new("--prepare-source-reuse")) {
                source_reuse::prepare(&repo, argument).map(Some)
            } else {
                let subject = match argument {
                    "INDEX" => Subject::Index,
                    "CHECKOUT" => Subject::Checkout,
                    commit => Subject::Commit(commit),
                };
                source_reuse::verify(&repo, subject)
            }
        };
        return match result {
            Ok(Some(selection)) => {
                println!(
                    "SOURCE_REUSE {} {} {}",
                    selection.trustir_commit, selection.clean_commit, selection.anchor_commit
                );
                ExitCode::SUCCESS
            }
            Ok(None) => {
                eprintln!("bridge_source_reuse: no source reuse record");
                ExitCode::from(1)
            }
            Err(error) => {
                eprintln!("bridge_source_reuse: source reuse refused: {error}");
                ExitCode::from(1)
            }
        };
    }
    eprintln!("{USAGE}");
    ExitCode::from(2)
}
