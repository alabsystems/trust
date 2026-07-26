// targo trust diff: saved-proof comparison or developer-only non-proof Git source audit
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
    Reports { baseline: String, current: Option<String> },
}

fn resolve_diff_input(sub_args: &SubcommandArgs) -> Result<DiffInput, String> {
    if sub_args.passthrough.len() > 1 {
        return Err(format!(
            "expected one positional git ref/range or baseline JSON path, got: {}",
            sub_args.passthrough.join(" ")
        ));
    }

    let positional = sub_args.passthrough.first();
    if let Some(argument) = positional {
        if argument.starts_with('-') {
            return Err(format!("unknown diff option `{argument}`"));
        }
    }

    let positional_range = positional.and_then(|argument| diff_git::parse_ref_range(argument));
    let positional_report = positional.filter(|argument| argument.ends_with(".json"));
    let positional_from =
        positional.filter(|_| positional_range.is_none() && positional_report.is_none());

    if sub_args.from_ref.is_some() && positional.is_some() {
        return Err("--from conflicts with a positional git ref/range or report path".to_string());
    }
    if sub_args.baseline.is_some() && positional.is_some() {
        return Err(
            "--baseline conflicts with a positional git ref/range or report path".to_string()
        );
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
        if sub_args.baseline.is_some() || sub_args.current.is_some() || positional_report.is_some()
        {
            return Err(
                "git refs cannot be combined with baseline/current report inputs".to_string()
            );
        }
        return Ok(DiffInput::Git(diff_git::GitRefRange {
            from,
            to: to.unwrap_or_else(|| "HEAD".to_string()),
        }));
    }

    if to.is_some() {
        return Err("--to requires --from or a positional source ref".to_string());
    }
    if sub_args.scope.is_some() {
        return Err("--scope is only valid for git-ref diff mode".to_string());
    }

    let baseline =
        sub_args.baseline.clone().or_else(|| positional_report.cloned()).ok_or_else(|| {
            "diff requires a git ref/range, a baseline JSON path, or --baseline <path>".to_string()
        })?;
    Ok(DiffInput::Reports { baseline, current: sub_args.current.clone() })
}

/// Run the `diff` subcommand: compare saved proof reports, or audit source
/// contract inventory between Git refs without claiming verification. Git-ref
/// mode is developer-only and is never release or proof evidence.
///
/// Enhanced diff with function-level comparison, color-coded
/// terminal output, and CI gate (exit non-zero on regressions).
///
/// Usage:
///   targo trust diff main..feature                            # non-proof source audit
///   targo trust diff --baseline report.json                   # baseline vs empty
///   targo trust diff --baseline base.json --current cur.json  # compare two reports
pub(crate) fn run_diff(sub_args: &SubcommandArgs, repo_dir: &Path) -> ExitCode {
    if matches!(sub_args.format, OutputFormat::Html) {
        eprintln!("targo trust diff: HTML output is not implemented; use terminal or json");
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
            eprintln!(
                "       targo trust diff [<baseline.json> | --baseline <path>] [--current <path>]"
            );
            return ExitCode::from(2);
        }
    };

    // Non-proof Git source-audit mode when refs are provided.
    if let DiffInput::Git(range) = input {
        match diff_git::run_git_diff(&range, repo_dir, sub_args.scope.as_deref()) {
            Ok(report) => {
                match sub_args.format {
                    OutputFormat::Json => report.render_json(),
                    OutputFormat::Terminal => report.render_terminal(),
                    OutputFormat::Html => unreachable!("HTML rejected before diff rendering"),
                }
                if report.has_regressions() {
                    return ExitCode::FAILURE;
                }
                return ExitCode::SUCCESS;
            }
            Err(e) => {
                eprintln!("targo trust: git diff failed: {e}");
                return ExitCode::from(2);
            }
        }
    }

    let DiffInput::Reports { baseline, current } = input else {
        unreachable!("git input returned from the git branch")
    };
    crate::diff::run_diff_command(&baseline, current.as_deref(), sub_args.format)
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
    fn positional_baseline_json_is_wired() {
        let DiffInput::Reports { baseline, current } =
            resolve_diff_input(&parsed(&["baseline.json"])).expect("report should resolve")
        else {
            panic!("expected report input")
        };
        assert_eq!(baseline, "baseline.json");
        assert_eq!(current, None);
    }

    #[test]
    fn ambiguous_or_incomplete_inputs_fail_loudly() {
        assert!(resolve_diff_input(&parsed(&["--to", "HEAD"])).is_err());
        assert!(resolve_diff_input(&parsed(&["--baseline", "base.json", "main..HEAD"])).is_err());
        assert!(resolve_diff_input(&parsed(&["--scope", "src", "base.json"])).is_err());
        assert!(resolve_diff_input(&parsed(&["one", "two"])).is_err());
        assert!(resolve_diff_input(&parsed(&["--unknown"])).is_err());
    }
}
