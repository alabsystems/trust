// Deprecated targo trust examples aliases.

use std::path::Path;
use std::process::ExitCode;

const USAGE: &str = "\
Usage: targo trust examples <command> [args...]

The `targo trust examples verify` alias has been removed.
Use `targo trust verify examples` for verifier example checks.
";

pub(crate) fn run_examples_subcommand(args: &[String]) -> ExitCode {
    match args.first().map(String::as_str) {
        Some("verify") => removed_examples_alias("verify", "targo trust verify examples"),
        Some("help" | "--help" | "-h") | None => {
            print!("{USAGE}");
            ExitCode::SUCCESS
        }
        Some(other) => {
            eprintln!("targo trust examples: unknown command `{other}`");
            eprint!("{USAGE}");
            ExitCode::from(2)
        }
    }
}

fn removed_examples_alias(alias: &str, replacement: &str) -> ExitCode {
    eprintln!("targo trust examples {alias}: removed alias; use `{replacement}`");
    ExitCode::from(2)
}

pub(crate) fn run_verify_metadata_gate(repo_root: &Path) -> bool {
    crate::verify_examples_cli::run_verify_metadata_gate(repo_root)
}
