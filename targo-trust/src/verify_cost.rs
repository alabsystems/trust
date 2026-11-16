// `targo trust benchmark verify-cost`: what verifying a crate of trivial functions costs.
//
// docs/PLAN.md PKG-C5d: verification costs milliseconds per function. This
// command generates one `lib` crate of N trivial functions, compiles it with an
// EXISTING trustc with verification on, and reads two numbers from that one
// compiler process: wall time and peak resident memory (`wait4`'s `ru_maxrss`).
// It passes only if both are within budget AND the run was a real verification
// of every function: a cost met by not verifying is not a result.
//
// Wall clock and memory here are measurements. They are never a verdict input,
// a cache key or proof authority (docs/DECISION_QUEUE.md BUDGET-1).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::fmt::Write as _;
use std::fs::{self, File};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use serde_json::{Value, json};

use crate::benchmark_cli::{CommandRun, run_command_with_resource_usage};

pub(crate) const USAGE: &str = "\
Usage: targo trust benchmark verify-cost [options]

Generate a crate of N trivial functions, compile it once with verification on
(`--emit=metadata`, overflow checks on) and once with it off, and judge the
verification-on run against a wall-clock and a peak-memory budget. The run
fails unless every generated function has exactly one result row, every
eligible body was processed and every obligation was proved, none from a proof
cache.

Options:
  --trustc PATH       the trustc to measure (default: build/host/stage1/bin/trustc,
                      relative to the current directory)
  --functions N       functions in the crate (default 500, at least 8)
  --max-wall-s S      wall-clock budget in seconds (default 5)
  --max-rss-mb M      peak resident memory budget in MB (default 400)
  --runs K            verification-on repeats; the median wall and the largest
                      RSS are judged (default 1)
  --by-shape          also measure each function shape alone (diagnostic only:
                      its numbers and problems print on its shape lines and
                      never change the verdict)
  --out-dir DIR       an empty or absent directory for the crates (default: a
                      fresh temporary directory)
  --json FILE         write the full record to FILE, after the verdict prints
  --timeout-s S       per-compile timeout in seconds (default 1800, at most
                      604800)
  -h, --help          print this text (as an option, not as an option's value)

Exit status: 0 within budget and fully verified, or -h/--help; 1 when a FAIL
line names why: over budget, not a real verification, no peak RSS reported (the
memory budget cannot be judged; always so off unix), or a compile of the whole
crate (not a --by-shape one) that failed, timed out or did not run to an exit
status; 2 a usage error, a --out-dir that is not empty, or a step outside the
compiles that failed: the trustc cannot be found or its -vV fails, the out-dir
or a file in it cannot be read, made or written, or the --json FILE cannot be
written (the PASS or FAIL lines have then printed).

Python is not used by this benchmark command.
";

const DEFAULT_TRUSTC: &str = "build/host/stage1/bin/trustc";
const DEFAULT_FUNCTIONS: usize = 500;
const DEFAULT_MAX_WALL_S: f64 = 5.0;
const DEFAULT_MAX_RSS_MB: f64 = 400.0;
const DEFAULT_TIMEOUT_S: u64 = 1800;
/// A week. A deadline past what the clock can represent would stop every compile
/// at once (run_command_wait4's invalid-timeout arm), so the bound is checked here.
const MAX_TIMEOUT_S: u64 = 7 * 24 * 3600;
const JSON_PREFIX: &str = "TRUST_JSON:";
const CRATE_NAME: &str = "verify_cost";
/// Decimal megabytes, as docs/PLAN.md states the budget: the stricter reading of "400 MB".
const MB: f64 = 1_000_000.0;
const MAX_REPORTED_PROBLEMS: usize = 12;
const RECORD_SCHEMA: &str = "trust.verify-cost.v1";

/// One function shape: its name, the safety obligations each function of it
/// carries, and its body. The template's constants are computed here, not
/// written as arithmetic in the source, so a function carries only the check
/// its own operation needs: `{k}` is the function's index mod 200, `{s}` a
/// shift amount below 64, `{i}` an index below 4.
struct Shape {
    name: &'static str,
    obligations: usize,
    template: &'static str,
}

const SHAPES: &[Shape] = &[
    Shape { name: "masked_add", obligations: 1, template: "(x: u32) -> u32 { (x & 0xff) + {k} }" },
    Shape { name: "identity", obligations: 0, template: "(x: u32) -> u32 { x }" },
    Shape { name: "const_index", obligations: 1, template: "(x: [u8; 4]) -> u8 { x[{i}] }" },
    Shape {
        name: "guarded_sub",
        obligations: 1,
        template: "(a: u32, b: u32) -> u32 { if a > b { a - b } else { {k} } }",
    },
    Shape { name: "const_shift", obligations: 1, template: "(x: u64) -> u64 { x >> {s} }" },
    Shape { name: "widening_mul", obligations: 1, template: "(x: u8) -> u32 { x as u32 * {k} }" },
    Shape { name: "compare", obligations: 0, template: "(x: u32) -> bool { x == {k} }" },
    Shape {
        name: "widening_add",
        obligations: 1,
        template: "(a: u8, b: u8) -> u16 { a as u16 + b as u16 }",
    },
];

/// Every outcome field of the crate summary that is not `proved`.
const NOT_PROVED_FIELDS: &[&str] =
    &["total_failed", "total_unknown", "total_timed_out", "total_skipped", "total_runtime_checked"];

#[derive(Debug)]
struct Args {
    trustc: PathBuf,
    functions: usize,
    max_wall_s: f64,
    max_rss_mb: f64,
    runs: usize,
    by_shape: bool,
    out_dir: Option<PathBuf>,
    json: Option<PathBuf>,
    timeout_s: u64,
}

pub(crate) fn run_verify_cost_subcommand(args: &[String]) -> ExitCode {
    let args = match parse_args(args) {
        Ok(None) => {
            print!("{USAGE}");
            return ExitCode::SUCCESS;
        }
        Ok(Some(args)) => args,
        Err(error) => {
            eprintln!("verify-cost benchmark: {error}");
            eprint!("{USAGE}");
            return ExitCode::from(2);
        }
    };
    match run(&args) {
        Ok(true) => ExitCode::SUCCESS,
        Ok(false) => ExitCode::from(1),
        Err(error) => {
            eprintln!("verify-cost benchmark: {error}");
            ExitCode::from(2)
        }
    }
}

/// The arguments, or `None` when `-h`/`--help` is read as an option. Arguments are
/// read in order, so an unknown option, a missing value or an unreadable number
/// before the help word is refused instead; the range checks come after the
/// whole list and do not apply to a help request. A help word in a value
/// position (`--out-dir --help`) is that option's value.
fn parse_args(args: &[String]) -> Result<Option<Args>, String> {
    let mut parsed = Args {
        trustc: PathBuf::from(DEFAULT_TRUSTC),
        functions: DEFAULT_FUNCTIONS,
        max_wall_s: DEFAULT_MAX_WALL_S,
        max_rss_mb: DEFAULT_MAX_RSS_MB,
        runs: 1,
        by_shape: false,
        out_dir: None,
        json: None,
        timeout_s: DEFAULT_TIMEOUT_S,
    };
    let mut iter = args.iter();
    while let Some(flag) = iter.next() {
        let mut value =
            |name: &str| iter.next().cloned().ok_or_else(|| format!("{name} needs a value"));
        match flag.as_str() {
            "--trustc" => parsed.trustc = PathBuf::from(value("--trustc")?),
            "--functions" => {
                parsed.functions = parse_number(&value("--functions")?, "--functions")?
            }
            "--max-wall-s" => {
                parsed.max_wall_s = parse_float(&value("--max-wall-s")?, "--max-wall-s")?
            }
            "--max-rss-mb" => {
                parsed.max_rss_mb = parse_float(&value("--max-rss-mb")?, "--max-rss-mb")?
            }
            "--runs" => parsed.runs = parse_number(&value("--runs")?, "--runs")?,
            "--by-shape" => parsed.by_shape = true,
            "--out-dir" => parsed.out_dir = Some(PathBuf::from(value("--out-dir")?)),
            "--json" => parsed.json = Some(PathBuf::from(value("--json")?)),
            "--timeout-s" => {
                parsed.timeout_s = parse_number(&value("--timeout-s")?, "--timeout-s")?
            }
            "-h" | "--help" => return Ok(None),
            other => return Err(format!("unknown argument `{other}`")),
        }
    }
    if parsed.functions < SHAPES.len() {
        return Err(format!("--functions must be at least {} (one of each shape)", SHAPES.len()));
    }
    if parsed.runs == 0 {
        return Err("--runs must be at least 1".to_string());
    }
    if parsed.timeout_s == 0 {
        return Err("--timeout-s must be at least 1".to_string());
    }
    if parsed.timeout_s > MAX_TIMEOUT_S {
        return Err(format!("--timeout-s must be at most {MAX_TIMEOUT_S} (a week)"));
    }
    Ok(Some(parsed))
}

fn parse_number<T>(text: &str, name: &str) -> Result<T, String>
where
    T: std::str::FromStr<Err = std::num::ParseIntError>,
{
    text.parse().map_err(|error: std::num::ParseIntError| match error.kind() {
        std::num::IntErrorKind::PosOverflow => format!("{name} is too large: `{text}`"),
        _ => format!("{name} expects a whole number, not `{text}`"),
    })
}

fn parse_float(text: &str, name: &str) -> Result<f64, String> {
    match text.parse::<f64>() {
        Ok(value) if value.is_finite() && value > 0.0 => Ok(value),
        _ => Err(format!("{name} expects a positive number, not `{text}`")),
    }
}

/// The crate's text and how many functions of each shape it holds.
fn crate_source(functions: usize, only: Option<&str>) -> (String, BTreeMap<&'static str, usize>) {
    let shapes: Vec<&Shape> =
        SHAPES.iter().filter(|shape| only.is_none_or(|name| shape.name == name)).collect();
    let mut source = String::from("#![crate_type = \"lib\"]\n#![allow(dead_code)]\n");
    let mut counts: BTreeMap<&'static str, usize> =
        shapes.iter().map(|shape| (shape.name, 0)).collect();
    for index in 0..functions {
        let shape = shapes[index % shapes.len()];
        *counts.get_mut(shape.name).expect("every selected shape is counted") += 1;
        let k = index % 200;
        let body = shape
            .template
            .replace("{k}", &k.to_string())
            .replace("{s}", &(k % 64).to_string())
            .replace("{i}", &(k % 4).to_string());
        let _ = writeln!(source, "pub fn {}{body}", function_name(shape.name, index));
    }
    (source, counts)
}

fn function_name(shape: &str, index: usize) -> String {
    format!("{shape}_{index:04}")
}

/// The name of every function `crate_source(functions, only)` generates.
fn generated_names(functions: usize, only: Option<&str>) -> BTreeSet<String> {
    let shapes: Vec<&Shape> =
        SHAPES.iter().filter(|shape| only.is_none_or(|name| shape.name == name)).collect();
    (0..functions).map(|index| function_name(shapes[index % shapes.len()].name, index)).collect()
}

fn shape_of(function: &str) -> Option<&'static str> {
    let short = function.rsplit("::").next()?;
    let (shape, index) = short.rsplit_once('_')?;
    if index.len() < 4 || !index.bytes().all(|byte| byte.is_ascii_digit()) {
        return None;
    }
    SHAPES.iter().map(|known| known.name).find(|known| *known == shape)
}

fn parse_rows(stderr: &str) -> Vec<Value> {
    stderr
        .lines()
        .filter_map(|line| line.strip_prefix(JSON_PREFIX))
        .filter_map(|row| serde_json::from_str::<Value>(row).ok())
        .filter(Value::is_object)
        .collect()
}

#[derive(Debug, Default)]
struct Facts {
    obligations: u64,
    proved: u64,
    engines: BTreeMap<String, u64>,
    by_shape: BTreeMap<&'static str, (usize, usize)>,
}

fn field(row: &Value, name: &str) -> u64 {
    row.get(name).and_then(Value::as_u64).unwrap_or(0)
}

/// Why this run is not a real verification of every generated function. Empty
/// means it is. `names` is every generated function (`generated_names`), and
/// each must have exactly one `function_result` row: equal counts per shape do
/// not show that the same functions were verified.
fn judge_verification(
    rows: &[Value],
    counts: &BTreeMap<&'static str, usize>,
    names: &BTreeSet<String>,
) -> (Vec<String>, Facts) {
    let functions: usize = counts.values().sum();
    let functions_u64 = functions as u64;
    let of_crate = |kind: &str| -> Vec<&Value> {
        rows.iter()
            .filter(|row| {
                row.get("type").and_then(Value::as_str) == Some(kind)
                    && row.get("crate_name").and_then(Value::as_str) == Some(CRATE_NAME)
            })
            .collect()
    };
    let summary = of_crate("crate_summary");
    let coverage = of_crate("coverage_summary");
    let results = of_crate("function_result");
    let mut problems = Vec::new();
    let mut facts = Facts::default();
    for (kind, found) in [("crate_summary", summary.len()), ("coverage_summary", coverage.len())] {
        match found {
            1 => {}
            0 => problems.push(format!("no {kind} row: verification did not report")),
            _ => problems.push(format!(
                "{found} {kind} rows for this crate where one is expected: the report is malformed"
            )),
        }
    }
    if !problems.is_empty() {
        return (problems, facts);
    }
    let (summary, coverage) = (summary[0], coverage[0]);
    facts.obligations = field(summary, "total_obligations");
    facts.proved = field(summary, "total_proved");
    for name in ["eligible", "processed"] {
        if field(coverage, name) < functions_u64 {
            problems.push(format!(
                "coverage_summary {name} = {}, below the {functions} functions generated",
                field(coverage, name)
            ));
        }
    }
    // The producer's contract (trust-types CoverageTransportSummary): processed
    // other than eligible is incomplete or malformed accounting.
    if field(coverage, "processed") != field(coverage, "eligible") {
        problems.push(format!(
            "coverage_summary processed = {} of eligible = {}: the coverage accounting is \
             incomplete or malformed",
            field(coverage, "processed"),
            field(coverage, "eligible")
        ));
    }
    for name in ["functions_analyzed", "functions_verified"] {
        if field(summary, name) < functions_u64 {
            problems.push(format!(
                "crate_summary {name} = {}, below the {functions} functions generated",
                field(summary, name)
            ));
        }
    }
    for name in NOT_PROVED_FIELDS {
        if field(summary, name) != 0 {
            problems.push(format!(
                "crate_summary {name} = {}: not every obligation was proved",
                field(summary, name)
            ));
        }
    }
    if facts.proved != facts.obligations {
        problems.push(format!("{} proved of {} obligations", facts.proved, facts.obligations));
    }
    let mut seen: BTreeMap<&'static str, usize> = counts.keys().map(|name| (*name, 0)).collect();
    let mut real: BTreeMap<&'static str, usize> = seen.clone();
    let mut unseen: BTreeSet<&str> = names.iter().map(String::as_str).collect();
    let mut cached = 0;
    for row in results {
        let function = row.get("function").and_then(Value::as_str).unwrap_or("");
        let Some(shape) = shape_of(function).filter(|shape| counts.contains_key(shape)) else {
            continue;
        };
        let short = function.rsplit("::").next().unwrap_or(function);
        if !unseen.remove(short) {
            problems.push(if names.contains(short) {
                format!("{function}: more than one function_result row")
            } else {
                format!(
                    "{function}: a function_result row for a function this crate does not define"
                )
            });
            continue;
        }
        *seen.get_mut(shape).expect("counted shape") += 1;
        cached += field(row, "cached");
        for result in row.get("results").and_then(Value::as_array).into_iter().flatten() {
            let outcome = result.get("outcome").and_then(Value::as_str).unwrap_or("absent");
            let kind = result.get("kind").and_then(Value::as_str).unwrap_or("absent");
            if outcome != "proved" {
                problems.push(format!("{function}: {kind} is {outcome}"));
            }
            if kind == "no_obligations" {
                continue;
            }
            *real.get_mut(shape).expect("counted shape") += 1;
            let engine = result
                .get("native_trust_ir")
                .and_then(|native| native.get("backend"))
                .and_then(Value::as_str)
                .or_else(|| result.get("solver").and_then(Value::as_str))
                .unwrap_or("unknown");
            *facts.engines.entry(engine.to_string()).or_default() += 1;
        }
    }
    for (shape, count) in counts {
        let want =
            SHAPES.iter().find(|known| known.name == *shape).expect("known shape").obligations
                * count;
        let (seen, real) = (seen[shape], real[shape]);
        // A shape with a function missing is named below (`unseen`): its
        // obligation count then says nothing about the checks generated.
        let complete = seen == *count;
        if complete && real < want {
            problems.push(format!(
                "shape {shape}: {real} obligations reported, {want} expected: a check was not \
                 generated"
            ));
        } else if complete && real > want {
            problems.push(format!(
                "shape {shape}: {real} obligations reported, {want} expected: the crate carries \
                 checks this command does not describe"
            ));
        }
        facts.by_shape.insert(shape, (*count, real));
    }
    if let Some(first) = unseen.first() {
        problems.push(format!(
            "{} of the {functions} generated functions have no function_result row (first: \
             {CRATE_NAME}::{first})",
            unseen.len()
        ));
    }
    if cached > 0 {
        problems.push(format!(
            "{cached} obligations were answered from a proof cache: this run did not measure \
             proving"
        ));
    }
    problems.truncate(MAX_REPORTED_PROBLEMS);
    (problems, facts)
}

struct Compile {
    run: CommandRun,
    stderr: String,
}

impl Compile {
    fn wall_s(&self) -> f64 {
        self.run.elapsed_seconds
    }

    fn rss_bytes(&self) -> Option<u64> {
        self.run.resource_usage.get("peak_rss_bytes").and_then(Value::as_u64)
    }

    /// The compiler's own exit status: none when it timed out or the runner
    /// reported a failure of its own (see `failure`), and negative for a signal.
    fn exit_status(&self) -> Option<i32> {
        let usage = &self.run.resource_usage;
        let own = self.run.timed_out
            || usage.get("lifecycle_error").is_some()
            || !usage.get("source").and_then(Value::as_str).is_some_and(runner_exited);
        if own { None } else { self.run.exit_code }
    }

    /// Why this compile is not a measurement. The runner
    /// (run_command_with_resource_usage) reports its own failures (the compiler
    /// not started, not waited for, or stopped for writing too much) as exit 127
    /// with a `source` that is not one of a run that exited (`runner_exited`) or
    /// with a `lifecycle_error`, so those are named before any exit status is read.
    fn failure(&self) -> Option<String> {
        if self.run.timed_out {
            return Some("the compiler timed out".to_string());
        }
        let usage = &self.run.resource_usage;
        let text = |name: &str| usage.get(name).and_then(Value::as_str);
        if let Some(error) = text("lifecycle_error") {
            return Some(format!("targo-trust stopped the compiler: {error}"));
        }
        if let Some(source) = text("source").filter(|source| !runner_exited(source)) {
            let detail = text("error").map(|error| format!(": {error}")).unwrap_or_default();
            return Some(format!("the compiler did not run to an exit status ({source}{detail})"));
        }
        match self.run.exit_code {
            Some(0) => None,
            Some(code) if code < 0 => Some(format!(
                "the compiler was killed by signal {}: {}",
                -code,
                last_line(&self.stderr)
            )),
            Some(code) => Some(format!("the compiler exited {code}: {}", last_line(&self.stderr))),
            None => Some("the compiler's exit status is unknown".to_string()),
        }
    }
}

/// The `source` of a run the runner waited to its exit: `os.wait4` from
/// run_command_wait4 on unix, `std` from run_command_poll elsewhere.
fn runner_exited(source: &str) -> bool {
    matches!(source, "os.wait4" | "std")
}

fn last_line(text: &str) -> String {
    text.lines()
        .rfind(|line| !line.trim().is_empty() && !line.starts_with(JSON_PREFIX))
        .map(|line| line.chars().take(200).collect())
        .unwrap_or_else(|| "(no output)".to_string())
}

fn compile_once(
    args: &Args,
    trustc: &Path,
    dir: &Path,
    source: &str,
    verify: bool,
) -> Result<Compile, String> {
    fs::create_dir(dir).map_err(|error| format!("cannot create {}: {error}", dir.display()))?;
    let source_path = dir.join(format!("{CRATE_NAME}.rs"));
    fs::write(&source_path, source)
        .map_err(|error| format!("cannot write {}: {error}", source_path.display()))?;
    let mut command = vec![
        trustc.display().to_string(),
        "--edition=2021".to_string(),
        "--crate-name".to_string(),
        CRATE_NAME.to_string(),
        "--emit=metadata".to_string(),
        "-Coverflow-checks=on".to_string(),
        "-o".to_string(),
        format!("{CRATE_NAME}.rmeta"),
    ];
    command.push(if verify { "-Ztrust-verify-output=json" } else { "-Ztrust-verify=off" }.into());
    command.push(format!("{CRATE_NAME}.rs"));
    let stdout_path = dir.join("stdout.txt");
    let stderr_path = dir.join("stderr.txt");
    let open = |path: &Path| {
        File::create(path).map_err(|error| format!("cannot create {}: {error}", path.display()))
    };
    let mut env_map: BTreeMap<String, String> = env::vars().collect();
    env_map.insert("RUST_BACKTRACE".to_string(), "0".to_string());
    let run = run_command_with_resource_usage(
        &command,
        dir,
        &env_map,
        args.timeout_s,
        open(&stdout_path)?,
        open(&stderr_path)?,
    );
    let stderr = fs::read(&stderr_path)
        .map(|bytes| String::from_utf8_lossy(&bytes).into_owned())
        .map_err(|error| format!("cannot read {}: {error}", stderr_path.display()))?;
    Ok(Compile { run, stderr })
}

#[derive(Debug, Default)]
struct Measurement {
    shape: String,
    functions: usize,
    off_wall_s: f64,
    off_rss_bytes: Option<u64>,
    runs: Vec<(f64, Option<u64>, Option<i32>)>,
    problems: Vec<String>,
    facts: Facts,
}

impl Measurement {
    fn wall_s(&self) -> Option<f64> {
        let mut walls: Vec<f64> = self.runs.iter().map(|run| run.0).collect();
        if walls.is_empty() {
            return None;
        }
        walls.sort_by(f64::total_cmp);
        let middle = walls.len() / 2;
        Some(if walls.len() % 2 == 1 {
            walls[middle]
        } else {
            (walls[middle - 1] + walls[middle]) / 2.0
        })
    }

    fn rss_bytes(&self) -> Option<u64> {
        self.runs.iter().filter_map(|run| run.1).max()
    }

    fn to_json(&self) -> Value {
        json!({
            "shape": self.shape,
            "functions": self.functions,
            "verification_off": { "wall_s": self.off_wall_s, "peak_rss_bytes": self.off_rss_bytes },
            "runs": self.runs.iter().map(|(wall, rss, exit)| json!({
                "wall_s": wall, "peak_rss_bytes": rss, "exit": exit,
            })).collect::<Vec<_>>(),
            "wall_s": self.wall_s(),
            "peak_rss_bytes": self.rss_bytes(),
            "obligations": self.facts.obligations,
            "proved": self.facts.proved,
            "engines": self.facts.engines,
            "by_shape": self.facts.by_shape.iter().map(|(shape, (functions, obligations))| {
                (shape.to_string(), json!({ "functions": functions, "obligations": obligations }))
            }).collect::<BTreeMap<_, _>>(),
            "problems": self.problems,
        })
    }
}

fn measure(
    args: &Args,
    trustc: &Path,
    out_dir: &Path,
    tag: &str,
    runs: usize,
    only: Option<&str>,
) -> Result<Measurement, String> {
    let (source, counts) = crate_source(args.functions, only);
    let names = generated_names(args.functions, only);
    let mut record = Measurement {
        shape: only.unwrap_or("mixed").to_string(),
        functions: args.functions,
        ..Measurement::default()
    };
    let off = compile_once(args, trustc, &out_dir.join(format!("{tag}-off")), &source, false)?;
    record.off_wall_s = off.wall_s();
    record.off_rss_bytes = off.rss_bytes();
    if let Some(failure) = off.failure() {
        record.problems.push(format!("the verification-off compile failed: {failure}"));
        return Ok(record);
    }
    for run in 0..runs {
        let on =
            compile_once(args, trustc, &out_dir.join(format!("{tag}-on{run}")), &source, true)?;
        record.runs.push((on.wall_s(), on.rss_bytes(), on.exit_status()));
        if let Some(failure) = on.failure() {
            record.problems.push(format!("run {run}: {failure}"));
            continue;
        }
        if on.rss_bytes().is_none() {
            record.problems.push(format!("run {run}: no peak RSS was reported for the compiler"));
        }
        let (problems, facts) = judge_verification(&parse_rows(&on.stderr), &counts, &names);
        record.problems.extend(problems.into_iter().map(|problem| format!("run {run}: {problem}")));
        record.facts = facts;
    }
    Ok(record)
}

fn mb(bytes: Option<u64>) -> String {
    bytes.map_or_else(|| "unknown".to_string(), |bytes| format!("{:.0}", bytes as f64 / MB))
}

fn trustc_version(trustc: &Path) -> Result<String, String> {
    let output = std::process::Command::new(trustc)
        .arg("-vV")
        .output()
        .map_err(|error| format!("cannot run {} -vV: {error}", trustc.display()))?;
    if !output.status.success() {
        return Err(format!("{} -vV failed: {}", trustc.display(), output.status));
    }
    let stdout = String::from_utf8_lossy(&output.stdout);
    match stdout.lines().next() {
        Some(line) if !line.trim().is_empty() => Ok(line.to_string()),
        _ => Err(format!("{} -vV printed no version line", trustc.display())),
    }
}

/// `value` with the fewest decimals, from `decimals` up to 9, at which it stands
/// on the same side of `limit` as the value itself (above it, or at or below
/// it): a FAIL line never shows a measurement within its budget, and a PASS
/// line never shows one over it.
fn shown_against(value: f64, limit: f64, decimals: usize) -> String {
    let over = value > limit;
    (decimals..=9)
        .map(|places| format!("{value:.places$}"))
        .find(|shown| shown.parse::<f64>().is_ok_and(|shown| (shown > limit) == over))
        .unwrap_or_else(|| value.to_string())
}

fn host_line() -> String {
    let cpus = std::thread::available_parallelism().map(|cpus| cpus.get()).unwrap_or(0);
    let host = std::process::Command::new("hostname")
        .arg("-s")
        .output()
        .ok()
        .and_then(|output| String::from_utf8(output.stdout).ok())
        .map(|name| name.trim().to_string())
        .filter(|name| !name.is_empty())
        .unwrap_or_else(|| "unknown-host".to_string());
    format!("{host} ({}, {}, {cpus} CPUs)", env::consts::ARCH, env::consts::OS)
}

fn prepare_out_dir(requested: Option<&Path>) -> Result<PathBuf, String> {
    if let Some(dir) = requested {
        if dir.exists() {
            let mut entries = fs::read_dir(dir)
                .map_err(|error| format!("cannot read {}: {error}", dir.display()))?;
            if entries.next().is_some() {
                return Err(format!(
                    "{} is not empty: a measurement starts from nothing",
                    dir.display()
                ));
            }
        } else {
            fs::create_dir_all(dir)
                .map_err(|error| format!("cannot create {}: {error}", dir.display()))?;
        }
        return fs::canonicalize(dir).map_err(|error| format!("{}: {error}", dir.display()));
    }
    let dir = tempfile::Builder::new()
        .prefix("trust-verify-cost-")
        .tempdir()
        .map_err(|error| format!("cannot create a temporary directory: {error}"))?;
    Ok(dir.keep())
}

/// Run the benchmark. `Ok(true)` passed and `Ok(false)` failed. `Err` is USAGE's
/// exit 2: a --out-dir that is not empty, or a step outside the compiles that
/// failed, the last of which is the --json write after the verdict printed.
fn run(args: &Args) -> Result<bool, String> {
    let trustc = fs::canonicalize(&args.trustc)
        .map_err(|error| format!("{}: {error}", args.trustc.display()))?;
    let version = trustc_version(&trustc)?;
    let out_dir = prepare_out_dir(args.out_dir.as_deref())?;
    let mixed = measure(args, &trustc, &out_dir, "mixed", args.runs, None)?;
    let mut shapes = Vec::new();
    if args.by_shape {
        for shape in SHAPES {
            shapes.push(measure(args, &trustc, &out_dir, shape.name, 1, Some(shape.name))?);
        }
    }

    println!("trustc: {version}");
    println!("host: {}", host_line());
    println!(
        "crate: {} trivial functions, {} shapes in rotation; out-dir {}",
        args.functions,
        SHAPES.len(),
        out_dir.display()
    );
    println!(
        "verification off: {:.2} s wall, {} MB peak RSS",
        mixed.off_wall_s,
        mb(mixed.off_rss_bytes)
    );
    for (index, (wall, rss, exit)) in mixed.runs.iter().enumerate() {
        let exit = match exit {
            Some(code) if *code < 0 => format!("signal {}", -code),
            Some(code) => format!("exit {code}"),
            None => "no exit status".to_string(),
        };
        println!(
            "verification on, run {index}: {wall:.2} s wall, {} MB peak RSS, {exit}",
            mb(*rss)
        );
    }
    if !mixed.runs.is_empty() {
        let engines = if mixed.facts.engines.is_empty() {
            "none".to_string()
        } else {
            mixed
                .facts
                .engines
                .iter()
                .map(|(engine, count)| format!("{engine} {count}"))
                .collect::<Vec<_>>()
                .join(", ")
        };
        let real: usize = mixed.facts.by_shape.values().map(|(_, real)| real).sum();
        println!(
            "obligations: {} proved of {} reported ({real} safety checks); engines: {engines}",
            mixed.facts.proved, mixed.facts.obligations
        );
    }
    for record in &shapes {
        match record.wall_s() {
            Some(wall) => {
                let per_function = (wall - record.off_wall_s) * 1000.0 / record.functions as f64;
                let note = record
                    .problems
                    .first()
                    .map(|problem| format!("  (not a clean measurement: {problem})"))
                    .unwrap_or_default();
                println!(
                    "shape {}: {wall:.2} s wall, {per_function:.2} ms per function over \
                     verification off, {} MB peak RSS{note}",
                    record.shape,
                    mb(record.rss_bytes())
                );
            }
            None => {
                println!("shape {}: not measured: {}", record.shape, record.problems.join("; "))
            }
        }
    }

    let mut failures = mixed.problems.clone();
    match (mixed.wall_s(), mixed.rss_bytes()) {
        (Some(wall), rss) => {
            if wall > args.max_wall_s {
                failures.push(format!(
                    "wall {} s is over the {} s budget",
                    shown_against(wall, args.max_wall_s, 2),
                    args.max_wall_s
                ));
            }
            if let Some(rss) = rss.filter(|rss| *rss as f64 / MB > args.max_rss_mb) {
                failures.push(format!(
                    "peak RSS {} MB is over the {} MB budget",
                    shown_against(rss as f64 / MB, args.max_rss_mb, 0),
                    args.max_rss_mb
                ));
            }
        }
        (None, _) if failures.is_empty() => {
            failures.push("no verification-on run was measured".to_string())
        }
        (None, _) => {}
    }
    if failures.is_empty() {
        let rss_mb = mixed.rss_bytes().unwrap_or_default() as f64 / MB;
        println!(
            "PASS: {} s wall (budget {} s), {} MB peak RSS (budget {} MB)",
            shown_against(mixed.wall_s().unwrap_or_default(), args.max_wall_s, 2),
            args.max_wall_s,
            shown_against(rss_mb, args.max_rss_mb, 0),
            args.max_rss_mb
        );
    }
    for failure in &failures {
        println!("FAIL: {failure}");
    }
    // After the verdict prints, so a record that cannot be written loses no
    // verdict line; the exit is then 2, as the caller asked for a record.
    if let Some(path) = &args.json {
        let record = json!({
            "schema": RECORD_SCHEMA,
            "trustc": version,
            "host": host_line(),
            "budget": { "max_wall_s": args.max_wall_s, "max_rss_mb": args.max_rss_mb },
            "mixed": mixed.to_json(),
            "by_shape": shapes.iter().map(Measurement::to_json).collect::<Vec<_>>(),
            "failures": failures,
        });
        let text = serde_json::to_string_pretty(&record).expect("a JSON value serializes") + "\n";
        fs::write(path, text)
            .map_err(|error| format!("cannot write {}: {error}", path.display()))?;
    }
    Ok(failures.is_empty())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The rows an honest verifying compiler prints for `crate_source(n, None)`.
    fn honest_rows(functions: usize) -> Vec<Value> {
        let (_, counts) = crate_source(functions, None);
        let mut rows = Vec::new();
        let mut obligations = 0;
        for index in 0..functions {
            let shape = &SHAPES[index % SHAPES.len()];
            let result = if shape.obligations == 1 {
                obligations += 1;
                json!({"kind": "overflow:add", "outcome": "proved",
                       "native_trust_ir": {"backend": "trust-mc"}})
            } else {
                obligations += 1;
                json!({"kind": "no_obligations", "outcome": "proved", "solver": "trust-structural"})
            };
            rows.push(json!({
                "type": "function_result", "crate_name": CRATE_NAME,
                "function": format!("{CRATE_NAME}::{}", function_name(shape.name, index)),
                "results": [result], "cached": 0,
            }));
        }
        let total: usize = counts.values().sum();
        rows.push(json!({"type": "coverage_summary", "crate_name": CRATE_NAME,
                         "eligible": total, "processed": total}));
        rows.push(json!({"type": "crate_summary", "crate_name": CRATE_NAME,
            "functions_analyzed": total, "functions_verified": total,
            "total_proved": obligations, "total_failed": 0, "total_unknown": 0,
            "total_timed_out": 0, "total_skipped": 0, "total_runtime_checked": 0,
            "total_obligations": obligations}));
        rows
    }

    fn judge(rows: &[Value]) -> Vec<String> {
        let (_, counts) = crate_source(16, None);
        judge_verification(rows, &counts, &generated_names(16, None)).0
    }

    fn summary_mut(rows: &mut [Value]) -> &mut Value {
        rows.iter_mut().find(|row| row["type"] == "crate_summary").expect("summary row")
    }

    #[test]
    fn crate_is_deterministic_and_covers_every_shape() {
        let (first, counts) = crate_source(500, None);
        let (second, _) = crate_source(500, None);
        assert_eq!(first, second);
        assert_eq!(counts.values().sum::<usize>(), 500);
        assert_eq!(counts.len(), SHAPES.len());
        assert_eq!(first.matches("pub fn ").count(), 500);
        for hole in ["{k}", "{s}", "{i}"] {
            assert!(!first.contains(hole), "unfilled {hole}");
        }
        let (only, only_counts) = crate_source(40, Some("masked_add"));
        assert_eq!(only_counts, BTreeMap::from([("masked_add", 40)]));
        assert_eq!(only.matches("& 0xff").count(), 40);
    }

    #[test]
    fn shapes_name_their_own_functions() {
        for shape in SHAPES {
            let name = format!("{CRATE_NAME}::{}", function_name(shape.name, 7));
            assert_eq!(shape_of(&name), Some(shape.name));
        }
        assert_eq!(shape_of("verify_cost::masked_add"), None);
        assert_eq!(shape_of("verify_cost::other_0001"), None);
    }

    #[test]
    fn an_honest_run_is_a_real_verification() {
        let rows = honest_rows(16);
        let (_, counts) = crate_source(16, None);
        let (problems, facts) = judge_verification(&rows, &counts, &generated_names(16, None));
        assert!(problems.is_empty(), "{problems:?}");
        assert_eq!(facts.engines.get("trust-mc"), Some(&12));
        assert_eq!(facts.by_shape["masked_add"], (2, 2));
        assert_eq!(facts.by_shape["identity"], (2, 0));
    }

    #[test]
    fn every_way_of_not_verifying_fails() {
        let expect = |rows: Vec<Value>, needle: &str| {
            let problems = judge(&rows);
            assert!(
                problems.iter().any(|problem| problem.contains(needle)),
                "{needle:?} not in {problems:?}"
            );
        };
        expect(Vec::new(), "verification did not report");

        let mut rows = honest_rows(16);
        rows.retain(|row| row["type"] != "coverage_summary");
        expect(rows, "no coverage_summary row");

        let mut rows = honest_rows(16);
        let summary = summary_mut(&mut rows).clone();
        rows.push(summary);
        expect(rows, "2 crate_summary rows for this crate where one is expected");

        let mut rows = honest_rows(16);
        rows.remove(3);
        expect(rows, "1 of the 16 generated functions have no function_result row");

        // Equal counts per shape are not the same functions: a second row for
        // one function stands in for another's missing one.
        let mut rows = honest_rows(16);
        rows[8] = rows[0].clone();
        expect(rows, "verify_cost::masked_add_0000: more than one function_result row");
        let mut rows = honest_rows(16);
        rows[8]["function"] = json!("verify_cost::masked_add_9999");
        expect(rows, "masked_add_9999: a function_result row for a function this crate does not");

        let mut rows = honest_rows(16);
        rows.iter_mut().find(|row| row["type"] == "coverage_summary").unwrap()["eligible"] =
            json!(17);
        expect(rows, "processed = 16 of eligible = 17");

        let mut rows = honest_rows(16);
        rows.iter_mut().find(|row| row["type"] == "coverage_summary").unwrap()["processed"] =
            json!(15);
        expect(rows, "coverage_summary processed = 15");

        let mut rows = honest_rows(16);
        rows[0]["results"][0]["outcome"] = json!("unknown");
        expect(rows, "overflow:add is unknown");

        let mut rows = honest_rows(16);
        summary_mut(&mut rows)["total_runtime_checked"] = json!(1);
        expect(rows, "total_runtime_checked = 1");

        let mut rows = honest_rows(16);
        summary_mut(&mut rows)["total_proved"] = json!(15);
        expect(rows, "15 proved of 16 obligations");

        let mut rows = honest_rows(16);
        rows[0]["results"][0]["kind"] = json!("no_obligations");
        expect(rows, "a check was not generated");

        let mut rows = honest_rows(16);
        rows[1]["results"]
            .as_array_mut()
            .unwrap()
            .push(json!({"kind": "overflow:add", "outcome": "proved"}));
        expect(rows, "checks this command does not describe");

        let mut rows = honest_rows(16);
        rows[1]["cached"] = json!(1);
        expect(rows, "answered from a proof cache");
    }

    #[test]
    fn rows_of_another_crate_do_not_count() {
        let mut rows = honest_rows(16);
        for row in &mut rows {
            row["crate_name"] = json!("someone_else");
        }
        assert!(judge(&rows)[0].contains("verification did not report"));
    }

    #[test]
    fn arguments_are_checked() {
        let parse =
            |args: &[&str]| parse_args(&args.iter().map(|s| s.to_string()).collect::<Vec<_>>());
        assert!(parse(&["--functions", "7"]).unwrap_err().contains("at least 8"));
        assert!(parse(&["--runs", "0"]).unwrap_err().contains("at least 1"));
        assert!(parse(&["--max-wall-s", "0"]).unwrap_err().contains("positive"));
        assert!(parse(&["--max-rss-mb", "nan"]).unwrap_err().contains("positive"));
        assert!(parse(&["--trustc"]).unwrap_err().contains("needs a value"));
        assert!(parse(&["--bogus"]).unwrap_err().contains("unknown argument"));
        assert!(parse(&["--timeout-s", "604801"]).unwrap_err().contains("at most 604800"));
        assert!(parse(&["--timeout-s", "604800"]).unwrap().is_some());
        assert!(parse(&["--timeout-s", "99999999999999999999"]).unwrap_err().contains("too large"));
        assert!(parse(&["--runs", "x"]).unwrap_err().contains("expects a whole number"));
        let args = parse(&["--functions", "64", "--by-shape", "--runs", "3"]).unwrap().unwrap();
        assert_eq!((args.functions, args.by_shape, args.runs), (64, true, 3));
        assert_eq!(args.trustc, PathBuf::from(DEFAULT_TRUSTC));
    }

    #[test]
    fn help_is_an_option_and_never_an_options_value() {
        let parse =
            |args: &[&str]| parse_args(&args.iter().map(|s| s.to_string()).collect::<Vec<_>>());
        assert!(parse(&["--help"]).unwrap().is_none());
        assert!(parse(&["--runs", "2", "-h"]).unwrap().is_none());
        let args = parse(&["--out-dir", "--help", "--json", "-h"]).unwrap().unwrap();
        assert_eq!(args.out_dir, Some(PathBuf::from("--help")));
        assert_eq!(args.json, Some(PathBuf::from("-h")));
        assert!(parse(&["help"]).unwrap_err().contains("unknown argument"));
        // Arguments are read in order: a refused one before -h is the answer.
        assert!(parse(&["--bogus", "-h"]).unwrap_err().contains("unknown argument"));
    }

    fn compile(exit_code: Option<i32>, timed_out: bool, usage: Value) -> Compile {
        Compile {
            run: CommandRun { exit_code, timed_out, elapsed_seconds: 1.0, resource_usage: usage },
            stderr: "error: boom\n".to_string(),
        }
    }

    #[test]
    fn a_failure_of_the_runner_is_not_read_as_the_compilers_exit() {
        let waited = json!({"source": "os.wait4", "peak_rss_bytes": 1});
        assert_eq!(compile(Some(0), false, waited.clone()).failure(), None);
        assert_eq!(compile(Some(0), false, waited.clone()).exit_status(), Some(0));
        let exited = compile(Some(101), false, waited.clone());
        assert_eq!(exited.failure().unwrap(), "the compiler exited 101: error: boom");
        assert_eq!(exited.exit_status(), Some(101));
        let signal = compile(Some(-11), false, waited.clone()).failure().unwrap();
        assert!(signal.starts_with("the compiler was killed by signal 11"), "{signal}");

        let mut limited = waited;
        limited["lifecycle_error"] = json!("output_limit_exceeded");
        let limited = compile(Some(127), false, limited);
        assert_eq!(
            limited.failure().unwrap(),
            "targo-trust stopped the compiler: output_limit_exceeded"
        );
        assert_eq!(limited.exit_status(), None);
        let started =
            compile(Some(127), false, json!({"source": "startup-error", "error": "nope"}));
        assert_eq!(
            started.failure().unwrap(),
            "the compiler did not run to an exit status (startup-error: nope)"
        );
        assert_eq!(started.exit_status(), None);
        // run_command_poll's ordinary exit off unix.
        let polled = compile(Some(0), false, json!({"source": "std"}));
        assert_eq!((polled.failure(), polled.exit_status()), (None, Some(0)));
        let timed = compile(Some(-9), true, json!({"source": "os.wait4"}));
        assert_eq!(timed.failure().unwrap(), "the compiler timed out");
        assert_eq!(timed.exit_status(), None);
    }

    #[test]
    fn a_value_is_shown_on_its_side_of_the_budget() {
        assert_eq!(shown_against(5.001, 5.0, 2), "5.001");
        assert_eq!(shown_against(13.9, 5.0, 2), "13.90");
        assert_eq!(shown_against(400.4, 400.0, 0), "400.4");
        assert_eq!(shown_against(571.2, 400.0, 0), "571");
        // Within the budget, the shown value never reads as over it.
        assert_eq!(shown_against(4.996, 4.999, 2), "4.996");
        assert_eq!(shown_against(1.234, 5.0, 2), "1.23");
        assert_eq!(shown_against(399.6, 400.0, 0), "400");
    }

    #[test]
    fn the_median_and_the_largest_rss_are_judged() {
        let record = Measurement {
            runs: vec![
                (3.0, Some(10), Some(0)),
                (1.0, Some(30), Some(0)),
                (2.0, Some(20), Some(0)),
            ],
            ..Measurement::default()
        };
        assert_eq!(record.wall_s(), Some(2.0));
        assert_eq!(record.rss_bytes(), Some(30));
        assert_eq!(Measurement::default().wall_s(), None);
    }
}
