// trust-js-differential: the TrustJS Channel-A harness binary — CLI dispatch.
//
// Subcommands (hand-rolled arg parsing, no clap):
//   corpus-verify  fail-closed corpus-pin check
//   slice-derive   derive a slice (S0 or --slice-kind async; count +
//                  list_sha256; --out writes the manifest)
//   slice-verify   re-derive and compare against a committed slice manifest
//                  (S0.toml or S-async.toml; kind auto-detected)
//   validate       fail-closed js262 ledger validation (expiring waivers)
//   selftest       negative-control + D1-acceptance gate
//   calibrate      the M0 gate run (scorecard, dashboard, divergences.jsonl;
//                  --sem / --trustjs auxiliary heads)
//   parse-verdict  the M1 D1 parse-verdict differential lane
//                  (trust-js-parse vs node --check)
//   ratchet        the M1 D4 coverage-ratchet check/proposal against
//                  tests/js262/coverage.toml (never writes the ledger)
//   minimize       line-granular ddmin of a divergent case
//   evidence       adopted-execution-report emission
//
// See Cargo.toml for the charter.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

mod calibrate;
mod cases;
mod corpus;
mod evidence;
mod frontmatter;
mod heads;
mod minimize;
mod model;
mod parse_verdict;
mod ratchet;
mod selftest;
mod slice;
mod ts_calibrate;
mod util;
mod validate;

use std::collections::HashMap;
use std::path::PathBuf;
use std::time::Duration;

use util::{resolve_engine, Engine};

const DEFAULT_PIN: &str = "tests/js262/corpus-pin.json";
const DEFAULT_SLICE: &str = "tests/js262/S0.toml";
const DEFAULT_LEDGERS: &str = "tests/js262";
const DEFAULT_OUT_DIR: &str = "build/js262/calibration";
const DEFAULT_PARSE_OUT_DIR: &str = "build/js262/parse-verdict";
const DEFAULT_COVERAGE_LEDGER: &str = "tests/js262/coverage.toml";

const USAGE: &str = "usage: trust-js-differential <subcommand> [flags]
  corpus-verify --corpus <dir> [--pin <path>]
  slice-derive  --corpus <dir> [--slice-kind s0|async] [--out <path>]
  slice-verify  --corpus <dir> --slice <path>
  validate      --ledgers <dir>
  selftest      --corpus <dir> [--node <p>] [--bun <p>]
  calibrate     --corpus <dir> --slice <path> [--node <p>] [--bun <p>] [--sem] [--trustjs]
                [--jobs N] [--timeout-secs N] [--limit N] [--out-dir <dir>] [--ledgers <dir>]
  ts-calibrate  --corpus <dir> [--node <p>] [--bun <p>] [--timeout-secs N] [--limit N] [--out <json>]
  ts-transform-calibrate  (non-erasable enum/namespace tier; Node --experimental-transform-types)
                --corpus <dir> [--node <p>] [--bun <p>] [--timeout-secs N] [--limit N] [--out <json>]
  parse-verdict --corpus <dir> [--slice-kind s0|module] [--slice <path>] [--node <p>]
                [--jobs N] [--limit N] [--out-dir <dir>] [--ledgers <dir>]
  ratchet       --scorecard <path> [--ledger <path>] [--check|--propose]
  minimize      --corpus <dir> --test <rel path> [--node <p>] [--bun <p>] [--mode bare|strict|raw]
  evidence      --scorecard <path> --ledgers <dir> --out <path>
Engine resolution: --node/--bun, else TRUST_JS_NODE / TRUST_JS_BUN, else PATH.
Every route asserts the engine pin (node 24.5.0, bun 1.3.14) and fails closed.";

/// Boolean flags (no value argument).
const BOOL_FLAGS: [&str; 5] = ["sem", "trustjs", "check", "propose", "allow-soundness-decrease"];

fn parse_flags(args: &[String], allowed: &[&str]) -> Result<HashMap<String, String>, String> {
    let mut out = HashMap::new();
    let mut i = 0;
    while i < args.len() {
        let arg = &args[i];
        let Some(key) = arg.strip_prefix("--") else {
            return Err(format!("unexpected positional argument {arg:?}"));
        };
        if !allowed.contains(&key) {
            return Err(format!("unknown flag --{key} (allowed: {})", allowed.join(", ")));
        }
        if BOOL_FLAGS.contains(&key) {
            out.insert(key.to_string(), "true".to_string());
            i += 1;
            continue;
        }
        let Some(value) = args.get(i + 1) else {
            return Err(format!("--{key} requires a value"));
        };
        out.insert(key.to_string(), value.clone());
        i += 2;
    }
    Ok(out)
}

fn required(flags: &HashMap<String, String>, key: &str) -> Result<PathBuf, String> {
    flags.get(key).map(PathBuf::from).ok_or_else(|| format!("--{key} is required"))
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let code = match dispatch(&args) {
        Ok(code) => code,
        Err(e) => {
            eprintln!("trust-js-differential: {e}");
            eprintln!("{USAGE}");
            2
        }
    };
    std::process::exit(code);
}

fn dispatch(args: &[String]) -> Result<i32, String> {
    let Some(sub) = args.first() else {
        return Err("missing subcommand".to_string());
    };
    let rest = &args[1..];
    match sub.as_str() {
        "corpus-verify" => {
            let flags = parse_flags(rest, &["corpus", "pin"])?;
            let corpus = required(&flags, "corpus")?;
            let pin = flags.get("pin").map(PathBuf::from).unwrap_or_else(|| PathBuf::from(DEFAULT_PIN));
            let findings = corpus::corpus_verify(&corpus, &pin);
            if findings.is_empty() {
                println!(
                    "corpus-verify: OK — {} matches pin {}",
                    corpus.display(),
                    pin.display()
                );
                Ok(0)
            } else {
                for f in &findings {
                    eprintln!("corpus-verify finding: {}", f.render());
                }
                Ok(1)
            }
        }
        "slice-derive" => {
            let flags = parse_flags(rest, &["corpus", "out", "slice-kind"])?;
            let corpus = required(&flags, "corpus")?;
            let kind = parse_slice_kind(&flags)?;
            let derived = slice::derive(&corpus, kind).map_err(|e| e.to_string())?;
            println!(
                "{} slice: count={} list_sha256={}",
                kind.id(),
                derived.paths.len(),
                derived.list_sha256
            );
            println!("{} rules_sha256={}", kind.id(), kind.rules_sha256());
            if let Some(out) = flags.get("out") {
                let revision =
                    util::git_head(&corpus).unwrap_or_else(|| "unknown".to_string());
                // The committed S-async slice is payload-external (S0.toml's
                // shape); S0 --out keeps its historical embedded form.
                let text = match kind {
                    slice::SliceKind::S0 => toml::to_string_pretty(&slice::build_manifest(
                        &revision, &derived,
                    ))
                    .map_err(|e| format!("serialize {}: {e}", kind.id()))?,
                    // S-async and S-module share the payload-external form.
                    slice::SliceKind::SAsync | slice::SliceKind::SModule => {
                        slice::build_external_manifest(kind, &revision, &derived)
                    }
                };
                let out = PathBuf::from(out);
                if let Some(parent) = out.parent() {
                    if !parent.as_os_str().is_empty() {
                        std::fs::create_dir_all(parent).map_err(|e| e.to_string())?;
                    }
                }
                std::fs::write(&out, text).map_err(|e| e.to_string())?;
                println!("wrote {}", out.display());
            }
            Ok(0)
        }
        "slice-verify" => {
            let flags = parse_flags(rest, &["corpus", "slice"])?;
            let corpus = required(&flags, "corpus")?;
            let slice_path = required(&flags, "slice")?;
            let loaded = slice::load_slice(&slice_path).map_err(|e| e.to_string())?;
            let mut findings = loaded.findings.clone();
            // Re-derive against the slice's self-declared kind (S0 vs S-async).
            let derived = slice::derive(&corpus, loaded.kind).map_err(|e| e.to_string())?;
            findings.extend(slice::verify_derived(&loaded, &derived));
            if findings.is_empty() {
                println!(
                    "slice-verify: OK — {} count={} list_sha256={} (rules match canonical contract, rules_sha256={})",
                    loaded.kind.id(),
                    loaded.count,
                    loaded.list_sha256,
                    loaded.kind.rules_sha256()
                );
                Ok(0)
            } else {
                for f in &findings {
                    eprintln!("slice-verify finding: {}", f.render());
                }
                Ok(1)
            }
        }
        "validate" => {
            let flags = parse_flags(rest, &["ledgers"])?;
            let ledgers = required(&flags, "ledgers")?;
            let date = util::validation_date();
            let (findings, summary) = validate::validate_ledgers(&ledgers, &date);
            println!(
                "validate: date={date} active_test_exceptions={} active_audit_entries={}",
                summary.active_test_exceptions.len(),
                summary.active_audit_entries.len()
            );
            if findings.is_empty() {
                println!("validate: OK");
                Ok(0)
            } else {
                for f in &findings {
                    eprintln!("validate finding: {}", f.render());
                }
                Ok(1)
            }
        }
        "selftest" => {
            let flags = parse_flags(rest, &["corpus", "node", "bun"])?;
            let opts = selftest::SelftestOpts {
                corpus: required(&flags, "corpus")?,
                node: resolve_engine(Engine::Node, flags.get("node").map(String::as_str))?,
                bun: resolve_engine(Engine::Bun, flags.get("bun").map(String::as_str))?,
            };
            selftest::run_selftest(&opts).map_err(|e| e.to_string())
        }
        "calibrate" => {
            let flags = parse_flags(
                rest,
                &[
                    "corpus", "slice", "node", "bun", "sem", "trustjs", "jobs", "timeout-secs",
                    "limit", "out-dir", "ledgers",
                ],
            )?;
            let opts = calibrate::CalibrateOpts {
                corpus: required(&flags, "corpus")?,
                slice: flags
                    .get("slice")
                    .map(PathBuf::from)
                    .unwrap_or_else(|| PathBuf::from(DEFAULT_SLICE)),
                node: resolve_engine(Engine::Node, flags.get("node").map(String::as_str))?,
                bun: resolve_engine(Engine::Bun, flags.get("bun").map(String::as_str))?,
                sem: flags.contains_key("sem"),
                trustjs: flags.contains_key("trustjs"),
                jobs: parse_num(&flags, "jobs", 16)?,
                timeout: Duration::from_secs(parse_num(&flags, "timeout-secs", 60)? as u64),
                limit: match flags.get("limit") {
                    Some(v) => Some(v.parse().map_err(|_| format!("--limit: bad number {v:?}"))?),
                    None => None,
                },
                out_dir: flags
                    .get("out-dir")
                    .map(PathBuf::from)
                    .unwrap_or_else(|| PathBuf::from(DEFAULT_OUT_DIR)),
                ledgers: flags
                    .get("ledgers")
                    .map(PathBuf::from)
                    .unwrap_or_else(|| PathBuf::from(DEFAULT_LEDGERS)),
            };
            calibrate::run_calibrate(&opts).map_err(|e| e.to_string())
        }
        "ts-calibrate" | "ts-transform-calibrate" => {
            let transform = sub == "ts-transform-calibrate";
            let flags =
                parse_flags(rest, &["corpus", "node", "bun", "timeout-secs", "limit", "out"])?;
            let default_corpus =
                if transform { "tests/ts-transform-corpus" } else { "tests/ts-corpus" };
            let opts = ts_calibrate::TsCalibrateOpts {
                corpus: flags
                    .get("corpus")
                    .map(PathBuf::from)
                    .unwrap_or_else(|| PathBuf::from(default_corpus)),
                node: resolve_engine(Engine::Node, flags.get("node").map(String::as_str))?,
                bun: resolve_engine(Engine::Bun, flags.get("bun").map(String::as_str))?,
                timeout: Duration::from_secs(parse_num(&flags, "timeout-secs", 30)? as u64),
                limit: match flags.get("limit") {
                    Some(v) => Some(v.parse().map_err(|_| format!("--limit: bad number {v:?}"))?),
                    None => None,
                },
                out: flags.get("out").map(PathBuf::from),
                transform,
            };
            let card = ts_calibrate::run_ts_calibrate(&opts).map_err(|e| e.to_string())?;
            ts_calibrate::print_scorecard(&card);
            // The bar: zero wrong traces (a covered trace matching neither engine).
            if card.trustts_divergent == 0 {
                Ok(0)
            } else {
                Ok(1)
            }
        }
        "parse-verdict" => {
            let flags = parse_flags(
                rest,
                &["corpus", "slice", "slice-kind", "node", "jobs", "limit", "out-dir", "ledgers"],
            )?;
            // The parse-verdict lane judges either the S0 (script goal) or the
            // S-module (module goal) slice; the async slice has no parse lane.
            let slice_kind = match flags.get("slice-kind") {
                Some(v) => {
                    let k = slice::SliceKind::parse_cli(v)
                        .ok_or_else(|| format!("--slice-kind: want s0|module, got {v:?}"))?;
                    if k == slice::SliceKind::SAsync {
                        return Err(
                            "--slice-kind async is not supported by parse-verdict (want s0|module)"
                                .to_string(),
                        );
                    }
                    k
                }
                None => slice::SliceKind::S0,
            };
            // Default slice manifest follows the kind, so `--slice-kind module`
            // alone re-derives against S-module.toml.
            let default_slice = match slice_kind {
                slice::SliceKind::SModule => "tests/js262/S-module.toml",
                _ => DEFAULT_SLICE,
            };
            let opts = parse_verdict::ParseVerdictOpts {
                corpus: required(&flags, "corpus")?,
                slice: flags
                    .get("slice")
                    .map(PathBuf::from)
                    .unwrap_or_else(|| PathBuf::from(default_slice)),
                slice_kind,
                node: resolve_engine(Engine::Node, flags.get("node").map(String::as_str))?,
                jobs: parse_num(&flags, "jobs", 16)?,
                limit: match flags.get("limit") {
                    Some(v) => Some(v.parse().map_err(|_| format!("--limit: bad number {v:?}"))?),
                    None => None,
                },
                out_dir: flags
                    .get("out-dir")
                    .map(PathBuf::from)
                    .unwrap_or_else(|| PathBuf::from(DEFAULT_PARSE_OUT_DIR)),
                ledgers: flags
                    .get("ledgers")
                    .map(PathBuf::from)
                    .unwrap_or_else(|| PathBuf::from(DEFAULT_LEDGERS)),
            };
            parse_verdict::run_parse_verdict(&opts).map_err(|e| e.to_string())
        }
        "ratchet" => {
            let flags = parse_flags(
                rest,
                &["scorecard", "ledger", "check", "propose", "allow-soundness-decrease"],
            )?;
            if flags.contains_key("check") && flags.contains_key("propose") {
                return Err("--check and --propose are mutually exclusive".to_string());
            }
            let opts = ratchet::RatchetOpts {
                scorecard: required(&flags, "scorecard")?,
                ledger: flags
                    .get("ledger")
                    .map(PathBuf::from)
                    .unwrap_or_else(|| PathBuf::from(DEFAULT_COVERAGE_LEDGER)),
                propose: flags.contains_key("propose"),
                allow_soundness_decrease: flags.contains_key("allow-soundness-decrease"),
            };
            ratchet::run_ratchet(&opts).map_err(|e| e.to_string())
        }
        "minimize" => {
            let flags = parse_flags(rest, &["corpus", "test", "node", "bun", "mode", "timeout-secs"])?;
            let mode = match flags.get("mode") {
                Some(m) => Some(
                    heads::RunMode::parse(m)
                        .ok_or_else(|| format!("--mode: want bare|strict|raw, got {m:?}"))?,
                ),
                None => None,
            };
            let opts = minimize::MinimizeOpts {
                corpus: required(&flags, "corpus")?,
                test: flags.get("test").cloned().ok_or("--test is required")?,
                node: resolve_engine(Engine::Node, flags.get("node").map(String::as_str))?,
                bun: resolve_engine(Engine::Bun, flags.get("bun").map(String::as_str))?,
                mode,
                timeout: Duration::from_secs(parse_num(&flags, "timeout-secs", 60)? as u64),
            };
            minimize::run_minimize(&opts).map_err(|e| e.to_string())
        }
        "evidence" => {
            let flags = parse_flags(rest, &["scorecard", "ledgers", "out"])?;
            let scorecard = required(&flags, "scorecard")?;
            let ledgers = required(&flags, "ledgers")?;
            let out = required(&flags, "out")?;
            evidence::run_evidence(&scorecard, &ledgers, &out).map_err(|e| e.to_string())
        }
        other => Err(format!("unknown subcommand {other:?}")),
    }
}

fn parse_num(flags: &HashMap<String, String>, key: &str, default: usize) -> Result<usize, String> {
    match flags.get(key) {
        Some(v) => v.parse().map_err(|_| format!("--{key}: bad number {v:?}")),
        None => Ok(default),
    }
}

/// `--slice-kind s0|async` (default s0).
fn parse_slice_kind(flags: &HashMap<String, String>) -> Result<slice::SliceKind, String> {
    match flags.get("slice-kind") {
        Some(v) => slice::SliceKind::parse_cli(v)
            .ok_or_else(|| format!("--slice-kind: want s0|async, got {v:?}")),
        None => Ok(slice::SliceKind::S0),
    }
}
