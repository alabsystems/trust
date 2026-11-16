// targo trust diff: the committed obligation baseline gate, or a developer-only
// non-proof Git source audit
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::Path;
use std::process::ExitCode;

use crate::cli::SubcommandArgs;
use crate::diff_git;
use crate::types::OutputFormat;

#[derive(Debug)]
enum DiffInput {
    Git(diff_git::GitRefRange),
    /// `--baseline <file>`: re-check against the committed obligation baseline.
    Baseline(String),
}

fn resolve_diff_input(sub_args: &SubcommandArgs) -> Result<DiffInput, String> {
    if let Some(baseline) = &sub_args.baseline {
        if sub_args.from_ref.is_some() || sub_args.to_ref.is_some() || sub_args.scope.is_some() {
            return Err("--baseline cannot be combined with git refs or --scope".to_string());
        }
        // Everything else is the live check's: packages, target selection,
        // lane flags. A positional is not.
        if let Some(positional) = sub_args.passthrough.iter().find(|arg| {
            !arg.starts_with('-')
                && !sub_args
                    .passthrough
                    .windows(2)
                    .any(|pair| pair[1] == **arg && takes_a_value(&pair[0]))
        }) {
            return Err(format!(
                "--baseline compares a live check; `{positional}` is not one of its options"
            ));
        }
        return Ok(DiffInput::Baseline(baseline.clone()));
    }

    if sub_args.passthrough.len() > 1 {
        return Err(format!(
            "expected one positional git ref/range, got: {}",
            sub_args.passthrough.join(" ")
        ));
    }

    let positional = sub_args.passthrough.first();
    if let Some(argument) = positional {
        if argument.starts_with('-') {
            return Err(format!("unknown diff option `{argument}`"));
        }
        if argument.ends_with(".json") {
            return Err(format!(
                "`{argument}`: saved reports are not compared; record proofs with `targo trust \
                 check --save-baseline <file>` and compare with `targo trust diff --baseline \
                 <file>`"
            ));
        }
    }

    let positional_range = positional.and_then(|argument| diff_git::parse_ref_range(argument));
    let positional_from = positional.filter(|_| positional_range.is_none());

    if sub_args.from_ref.is_some() && positional.is_some() {
        return Err("--from conflicts with a positional git ref/range".to_string());
    }

    let from = sub_args
        .from_ref
        .clone()
        .or_else(|| positional_range.as_ref().map(|range| range.from.clone()))
        .or_else(|| positional_from.cloned());
    let range_to = positional_range.as_ref().map(|range| range.to.clone());
    if range_to.is_some() && sub_args.to_ref.is_some() {
        return Err("--to conflicts with the destination in a positional ref range".to_string());
    }
    let to = sub_args.to_ref.clone().or(range_to);

    if let Some(from) = from {
        return Ok(DiffInput::Git(diff_git::GitRefRange {
            from,
            to: to.unwrap_or_else(|| "HEAD".to_string()),
        }));
    }

    if to.is_some() {
        return Err("--to requires --from or a positional source ref".to_string());
    }
    Err("diff requires a git ref/range or --baseline <file>".to_string())
}

/// Cargo options whose next token is their value, so it is not a positional.
fn takes_a_value(flag: &str) -> bool {
    matches!(
        flag,
        "-p" | "--package"
            | "--features"
            | "-F"
            | "--bin"
            | "--test"
            | "--example"
            | "--bench"
            | "--target"
            | "--manifest-path"
            | "--exclude"
            | "--target-dir"
            | "--config"
            | "-Z"
    )
}

/// Run the `diff` subcommand: compare a live check against the committed
/// obligation baseline (`--baseline`), or audit source contract inventory
/// between Git refs without claiming verification. Git-ref mode is
/// developer-only and is never release or proof evidence.
///
/// Usage:
///   targo trust diff main..feature                 # non-proof source audit
///   targo trust diff --baseline trust.baseline     # exit 1 on any lost proof
pub(crate) fn run_diff(sub_args: &SubcommandArgs, args: &[String], repo_dir: &Path) -> ExitCode {
    if matches!(sub_args.format, OutputFormat::Html) {
        eprintln!("targo trust diff: HTML output is not implemented; use terminal or json");
        return ExitCode::from(2);
    }
    if sub_args.save_baseline.is_some() {
        eprintln!("targo trust diff: --save-baseline is a `check` option");
        return ExitCode::from(2);
    }
    // Interpret positionals here, where the command is known to be `diff`.
    // The shared parser must leave ref-like Cargo/package arguments untouched
    // for every other subcommand.
    let input = match resolve_diff_input(sub_args) {
        Ok(input) => input,
        Err(error) => {
            eprintln!("targo trust diff: {error}");
            eprintln!("usage: targo trust diff <from>[..<to>] [--to <ref>] [--scope <path>]");
            eprintln!("       targo trust diff --baseline <file> [-p <package>]...");
            return ExitCode::from(2);
        }
    };

    let range = match input {
        DiffInput::Baseline(path) => {
            return crate::baseline::run_baseline_diff(sub_args, args, Path::new(&path));
        }
        DiffInput::Git(range) => range,
    };
    // Non-proof Git source-audit mode.
    match diff_git::run_git_diff(&range, repo_dir, sub_args.scope.as_deref()) {
        Ok(report) => {
            match sub_args.format {
                OutputFormat::Json => report.render_json(),
                OutputFormat::Terminal => report.render_terminal(),
                OutputFormat::Html => unreachable!("HTML rejected before diff rendering"),
            }
            if report.has_regressions() { ExitCode::FAILURE } else { ExitCode::SUCCESS }
        }
        Err(e) => {
            eprintln!("targo trust: git diff failed: {e}");
            ExitCode::from(2)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cli::parse_subcommand_args;

    fn parsed(args: &[&str]) -> SubcommandArgs {
        parse_subcommand_args(&args.iter().map(ToString::to_string).collect::<Vec<_>>())
            .expect("shared arguments should parse")
    }

    #[test]
    fn positional_git_range_and_single_ref_are_wired() {
        let DiffInput::Git(range) =
            resolve_diff_input(&parsed(&["main..feature"])).expect("range should resolve")
        else {
            panic!("expected git input")
        };
        assert_eq!(range.from, "main");
        assert_eq!(range.to, "feature");

        let DiffInput::Git(range) =
            resolve_diff_input(&parsed(&["HEAD~3"])).expect("single ref should resolve")
        else {
            panic!("expected git input")
        };
        assert_eq!(range.from, "HEAD~3");
        assert_eq!(range.to, "HEAD");
    }

    #[test]
    fn baseline_mode_is_wired_and_saved_reports_are_not_inputs() {
        let DiffInput::Baseline(path) =
            resolve_diff_input(&parsed(&["--baseline", "trust.baseline", "-p", "foo", "--lib"]))
                .expect("baseline mode should resolve")
        else {
            panic!("expected baseline input")
        };
        assert_eq!(path, "trust.baseline");
        let error = resolve_diff_input(&parsed(&["baseline.json"])).expect_err("not an input");
        assert!(error.contains("--save-baseline"), "{error}");
        assert!(resolve_diff_input(&parsed(&["--baseline", "b", "stray"])).is_err());
    }

    #[test]
    fn ambiguous_or_incomplete_inputs_fail_loudly() {
        assert!(resolve_diff_input(&parsed(&["--to", "HEAD"])).is_err());
        assert!(resolve_diff_input(&parsed(&["--baseline", "base.json", "main..HEAD"])).is_err());
        assert!(resolve_diff_input(&parsed(&["--scope", "src", "--baseline", "b"])).is_err());
        assert!(resolve_diff_input(&parsed(&["one", "two"])).is_err());
        assert!(resolve_diff_input(&parsed(&["--unknown"])).is_err());
    }
}
