//! `targo trust gate compare-seal`: the command over [`super::state`].

use std::path::PathBuf;
use std::process::ExitCode;

use super::Verdict;
use super::state::{self, Outcome};

const USAGE: &str = "\
Usage: targo trust gate compare-seal --state DIR [--require NAME[,NAME...]]

Decide a cut's consumer check from saved runs: for each consumer, the candidate
seal against the deployed seal, same command, same tree, same budget.

  PASS        the candidate's command exits 0 and loses no proof
  SHARED_RED  the candidate is red, and nothing it shows is new
  NEW_RED     the candidate loses a proof the deployed seal had, names a red
              the deployed seal does not, or ends in a worse way

DIR holds one directory per consumer:
  DIR/<consumer>/deployed/run.json     the deployed seal's run
  DIR/<consumer>/candidate/run.json    the candidate's run
  DIR/<consumer>/verdict.json          written by this command

run.json (schema trust.seal-consumer-run.v1) has consumer, tree, command, seal,
cpus, memory_gib, finished, exit, and optionally stopped_at_bound, obligations
(a trust.obligations.v1 file or directory) and reds (the failing tests named).

A consumer whose runs have not both finished is PENDING. Run the command again
when they have: a recorded verdict whose inputs are unchanged is kept.

Options:
  --state DIR      The comparison's state directory
  --require NAMES  Consumers that must be decided, present in DIR or not
  -h, --help       Show this help

Exit 0 when every consumer is PASS or SHARED_RED, 1 when one is NEW_RED, 2 on a
usage error, and 3 when none is NEW_RED and one is pending or cannot be
compared. This compares saved runs: it is not a proof and grants nothing.
";

struct Options {
    state: PathBuf,
    required: Vec<String>,
}

fn parse(args: &[String]) -> Result<Option<Options>, String> {
    let mut state = None;
    let mut required = Vec::new();
    let mut index = 0;
    while let Some(argument) = args.get(index) {
        index += 1;
        let (name, inline) = argument
            .split_once('=')
            .map_or((argument.as_str(), None), |(name, value)| (name, Some(value)));
        match name {
            "--help" | "-h" if inline.is_none() => return Ok(None),
            "--state" | "--require" => {
                let value = match inline {
                    Some(value) => value,
                    None => {
                        let value =
                            args.get(index).ok_or_else(|| format!("{name} requires a value"))?;
                        index += 1;
                        value
                    }
                };
                if value.is_empty() || value.starts_with('-') {
                    return Err(format!("{name} requires a value"));
                }
                if name == "--state" {
                    if state.replace(PathBuf::from(value)).is_some() {
                        return Err("--state is given twice".into());
                    }
                } else {
                    for consumer in value.split(',') {
                        if consumer.is_empty() || consumer.contains(['/', '\\']) || consumer == ".."
                        {
                            return Err(format!("--require: {consumer:?} is not a consumer name"));
                        }
                        required.push(consumer.to_owned());
                    }
                }
            }
            _ => return Err(format!("unknown argument {argument:?}")),
        }
    }
    let state = state.ok_or("--state is required")?;
    Ok(Some(Options { state, required }))
}

/// The command and its tests use this one path.
pub(crate) fn run_to_string(args: &[String]) -> (u8, String) {
    let options = match parse(args) {
        Ok(None) => return (0, USAGE.into()),
        Ok(Some(options)) => options,
        Err(error) => return (2, format!("targo trust gate compare-seal: {error}\n\n{USAGE}")),
    };
    let consumers = match state::consumers(&options.state, &options.required) {
        Ok(consumers) => consumers,
        Err(error) => {
            return (
                3,
                format!(
                    "COMPARE-SEAL: COULD NOT RUN — cannot read {}: {error}\n",
                    options.state.display()
                ),
            );
        }
    };
    if consumers.is_empty() {
        return (
            3,
            format!(
                "COMPARE-SEAL: COULD NOT RUN — {} holds no consumer\n",
                options.state.display()
            ),
        );
    }
    let mut text = String::new();
    let (mut new_red, mut undecided) = (0_usize, 0_usize);
    for consumer in &consumers {
        match state::decide(&options.state.join(consumer)) {
            Outcome::Decided { verdict, reused, report } => {
                if verdict == Verdict::NewRed {
                    new_red += 1;
                }
                let disclosures = &report["disclosures"];
                text.push_str(&format!(
                    "{}\t{consumer}\t{}proved {} -> {}; candidate-only failed rows {}; vanished {}\n",
                    verdict.label(),
                    if reused { "(recorded verdict kept) " } else { "" },
                    disclosures["proved_deployed"],
                    disclosures["proved_candidate"],
                    disclosures["candidate_only_failed"]
                        .as_object()
                        .map_or(0, |rows| rows.values().filter_map(|n| n.as_u64()).sum::<u64>()),
                    disclosures["vanished"],
                ));
                for row in report["new_reds"].as_array().into_iter().flatten() {
                    text.push_str(&format!("  NEW\t{}\n", row.as_str().unwrap_or_default()));
                }
            }
            Outcome::Pending(why) => {
                undecided += 1;
                text.push_str(&format!("PENDING\t{consumer}\t{why}\n"));
            }
            Outcome::Incomparable(why) => {
                undecided += 1;
                text.push_str(&format!("INCOMPARABLE\t{consumer}\t{why}\n"));
            }
        }
    }
    let code = if new_red > 0 {
        text.push_str(&format!(
            "COMPARE-SEAL: NEW_RED in {new_red} of {} consumer(s)\n",
            consumers.len()
        ));
        1
    } else if undecided > 0 {
        text.push_str(&format!(
            "COMPARE-SEAL: COULD NOT RUN — {undecided} of {} consumer(s) not decided\n",
            consumers.len()
        ));
        3
    } else {
        text.push_str(&format!("COMPARE-SEAL: no new red in {} consumer(s)\n", consumers.len()));
        0
    };
    (code, text)
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
