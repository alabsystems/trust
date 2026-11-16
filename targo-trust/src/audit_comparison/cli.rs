//! Native command adapter for the saved audit comparator.

use std::collections::BTreeSet;
use std::path::PathBuf;
use std::process::ExitCode;

use super::{AuditInputPair, ComparisonMode, ComparisonPolicy, compare};

const USAGE: &str = "\
Usage: targo trust gate compare-audit [--l4 | --obligations] [options] PARENT CANDIDATE

Compare complete saved compiler audit populations. This is diagnostic comparison,
never proof, compiler qualification, or permission to land a candidate.

Options:
  --l4                 Include row digests, cap attribution, stops and parity
  --obligations        Compare published trust.obligations.v1 keys
  --deleted-caps IDS   Comma-separated cap groups: C09d,C11e1,C11e2,C11e3,C12
  --attributed FILE    Explicit crate-level cap attribution TSV
  --oracles NAMES      Require nonempty row,identity,dedup,lowering,size oracles
                       in every candidate corpus (--l4 only)
  -h, --help           Show this help

Default mode is L3. Exit 0 passes, 1 reports violations, 2 rejects usage, and
3 means malformed, missing, unattributed or insufficient comparison evidence.
";

struct Options {
    parent: PathBuf,
    candidate: PathBuf,
    policy: ComparisonPolicy,
}

fn parse(args: &[String]) -> Result<Option<Options>, String> {
    let mut l4 = false;
    let mut obligations = false;
    let mut groups = String::new();
    let mut oracles = String::new();
    let mut attributions = None;
    let mut positional = Vec::new();
    let mut passthrough = false;
    let mut index = 0;
    while let Some(argument) = args.get(index) {
        index += 1;
        if passthrough {
            positional.push(PathBuf::from(argument));
            continue;
        }
        let (name, inline) = argument
            .split_once('=')
            .map_or((argument.as_str(), None), |(name, value)| (name, Some(value)));
        match name {
            "--help" | "-h" if inline.is_none() => return Ok(None),
            "--" if inline.is_none() => passthrough = true,
            "--l4" if inline.is_none() => l4 = true,
            "--obligations" if inline.is_none() => obligations = true,
            "--deleted-caps" | "--attributed" | "--oracles" => {
                let value = match inline {
                    Some(value) => value,
                    None => {
                        let value =
                            args.get(index).ok_or_else(|| format!("{name} requires a value"))?;
                        index += 1;
                        if value.starts_with('-') {
                            return Err(format!("{name} requires a value"));
                        }
                        value
                    }
                };
                match name {
                    "--deleted-caps" => groups = value.into(),
                    "--oracles" => oracles = value.into(),
                    _ => attributions = Some(PathBuf::from(value)),
                }
            }
            _ if argument.starts_with('-') => return Err(format!("unknown argument {argument:?}")),
            _ => positional.push(PathBuf::from(argument)),
        }
    }
    if l4 && obligations {
        return Err("--l4 and --obligations are mutually exclusive".into());
    }
    let [parent, candidate]: [PathBuf; 2] = positional
        .try_into()
        .map_err(|_| "exactly two inputs are required: PARENT CANDIDATE".to_string())?;
    let policy = ComparisonPolicy {
        mode: if l4 {
            ComparisonMode::L4
        } else if obligations {
            ComparisonMode::PublishedObligations
        } else {
            ComparisonMode::L3
        },
        deleted_cap_groups: groups
            .split(',')
            .filter(|group| !group.is_empty())
            .map(str::to_owned)
            .collect::<BTreeSet<_>>(),
        required_oracles: oracles
            .split(',')
            .filter(|oracle| !oracle.is_empty())
            .map(str::to_owned)
            .collect(),
        attributions,
    };
    policy.validate()?;
    Ok(Some(Options { parent, candidate, policy }))
}

/// Both the public command and regression controls use this exact path.
pub(crate) fn run_to_string(args: &[String]) -> (u8, String) {
    match parse(args) {
        Ok(None) => (0, USAGE.into()),
        Ok(Some(options)) => {
            let report = compare(
                AuditInputPair { parent: &options.parent, candidate: &options.candidate },
                &options.policy,
            );
            (report.exit_code(), report.render_terminal())
        }
        Err(error) => (2, format!("targo trust gate compare-audit: {error}\n\n{USAGE}")),
    }
}

pub(crate) fn run_subcommand(args: &[String]) -> ExitCode {
    let (code, text) = run_to_string(args);
    if code == 0 || code == 1 {
        print!("{text}");
    } else {
        eprint!("{text}");
    }
    ExitCode::from(code)
}
