//! `targo trust benchmark rival` (docs/PLAN.md PKG-LIVE-11; the edit loop
//! plan, docs/design/2026-11-12-live-edit-loop.md, section 11.6).
//!
//! Times Trust against a rival dev-loop tool (blaze) on the same machine, the
//! same generated crates and the same one-function edits, lane by lane, and
//! prints the number: the subject-axis rows where Trust is at least as good.
//!
//! Each tool and lane gets its own freshly generated crate and target
//! directory, so no run reuses another's state. A lane runs cold, then with
//! nothing changed, then after each of N edits; an edit changes one integer
//! constant in the last function of the middle module, so every edit changes
//! one function body and the program's output. The `run` lane is the control:
//! under `--check` both tools must print the same value after every edit, and
//! every edit must change the value a tool prints, so a tool that serves a
//! stale binary is caught rather than timed.
//!
//! Beside the nine timed axes each subject has three more rows: the memory a
//! tool's processes hold between commands (found by an environment marker
//! every command carries, and stopped once the subject is done unless
//! `--keep-resident`), the bytes its target directories and named store hold,
//! and whether it built and ran every edit.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode, Stdio};
use std::time::{Duration, Instant};

use serde_json::{Value, json};

const REPORT_SCHEMA: &str = "trust.benchmark.rival.v1";
const MARKER: &str = ".trust-benchmark-rival";
const FIRST_EDIT: u64 = 1000;
/// Every command a tool runs carries `<RESIDENT_ENV>=<nonce>.<tool>`, and so
/// does every process it leaves behind, which is how they are found.
const RESIDENT_ENV: &str = "TRUST_BENCHMARK_RIVAL";

pub(crate) const USAGE: &str = "\
Usage: targo trust benchmark rival [OPTIONS]

Time Trust against a rival dev-loop tool on generated crates and one-function
edits, and print the rows where Trust is at least as good.

Options:
  --out <DIR>            Work and report directory (default: target/rival);
                         created, or reused only if an earlier run made it
  --subject <S>          small (4.5k lines), medium (34k), large (170k), or
                         NAME=MODULESxFUNCTIONS; repeatable (default: all three)
  --map <btree|hashmap>  Map type in the generated crates (default: btree)
  --edits <N>            Edits per lane (default: 7)
  --axis <A,..>          Axes to run and judge: {cold,noop,edit}-{check,build,run}
                         (default: all nine)
  --trust <PATH>         Trust's targo (default: `targo` on PATH)
  --blaze <PATH>         The rival's executable (default: `blaze` on PATH)
  --trust-env <K=V>      Environment for Trust's commands; repeatable
  --blaze-env <K=V>      Environment for the rival's commands; repeatable
  --trust-store <DIR>    A store Trust writes outside the target directory;
                         its growth over a subject counts as that subject's disk
  --blaze-store <DIR>    The same for the rival (its records, not its toolchain)
  --keep-resident        Leave the processes a tool keeps running between
                         commands; by default they are stopped after each subject
  --timeout <SECONDS>    Per-command bound (default: 900)
  --check                Exit 1 unless every row has a value for both tools,
                         every command succeeded, both printed the same value
                         after every edit, and every edit changed the value
  --require-faster       Exit 1 unless Trust is at least as good on every row
  -h, --help             Print this help

Rows per subject: the selected axes (median wall ms), resident-mb (most memory
the tool's processes held between two commands), disk-mb (target directories
plus store growth) and runs (1 when the tool built and ran every edit; only
when a run axis is selected). The report is <out>/rival.json (schema
trust.benchmark.rival.v1).
";

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Lane {
    Check,
    Build,
    Run,
}

impl Lane {
    const ALL: [Lane; 3] = [Lane::Check, Lane::Build, Lane::Run];

    fn name(self) -> &'static str {
        match self {
            Lane::Check => "check",
            Lane::Build => "build",
            Lane::Run => "run",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Phase {
    Cold,
    Noop,
    Edit,
}

impl Phase {
    const ALL: [Phase; 3] = [Phase::Cold, Phase::Noop, Phase::Edit];

    fn name(self) -> &'static str {
        match self {
            Phase::Cold => "cold",
            Phase::Noop => "noop",
            Phase::Edit => "edit",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Axis {
    phase: Phase,
    lane: Lane,
}

impl Axis {
    fn name(self) -> String {
        format!("{}-{}", self.phase.name(), self.lane.name())
    }

    fn parse(text: &str) -> Result<Axis, String> {
        let (phase, lane) =
            text.split_once('-').ok_or_else(|| format!("axis `{text}` is not PHASE-LANE"))?;
        let phase = Phase::ALL
            .into_iter()
            .find(|p| p.name() == phase)
            .ok_or_else(|| format!("axis `{text}`: unknown phase `{phase}`"))?;
        let lane = Lane::ALL
            .into_iter()
            .find(|l| l.name() == lane)
            .ok_or_else(|| format!("axis `{text}`: unknown lane `{lane}`"))?;
        Ok(Axis { phase, lane })
    }
}

#[derive(Clone, Debug)]
struct Subject {
    name: String,
    modules: usize,
    functions: usize,
}

impl Subject {
    fn parse(text: &str) -> Result<Subject, String> {
        let standard =
            |name: &str, modules, functions| Subject { name: name.to_string(), modules, functions };
        match text {
            "small" => return Ok(standard("small", 20, 25)),
            "medium" => return Ok(standard("medium", 100, 40)),
            "large" => return Ok(standard("large", 400, 50)),
            _ => {}
        }
        let (name, size) = text
            .split_once('=')
            .ok_or_else(|| format!("subject `{text}` is not small, medium, large or NAME=MxF"))?;
        let (modules, functions) =
            size.split_once('x').ok_or_else(|| format!("subject `{text}`: size is not MxF"))?;
        let number = |value: &str| {
            value
                .parse::<usize>()
                .ok()
                .filter(|n| *n > 0)
                .ok_or_else(|| format!("subject `{text}`: `{value}` is not a positive count"))
        };
        if name.is_empty() || !name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_') {
            return Err(format!("subject `{text}`: the name must be ASCII letters, digits or `_`"));
        }
        Ok(Subject {
            name: name.to_string(),
            modules: number(modules)?,
            functions: number(functions)?,
        })
    }
}

#[derive(Clone, Debug)]
struct Tool {
    name: &'static str,
    program: PathBuf,
    /// Arguments before the lane: Trust's commands are named on the unverified lane.
    prefix: Vec<String>,
    env: Vec<(String, String)>,
    /// This run's `RESIDENT_ENV` value for the tool.
    marker: String,
    store: Option<PathBuf>,
}

#[derive(Debug)]
struct Options {
    out: PathBuf,
    subjects: Vec<Subject>,
    btree: bool,
    edits: usize,
    axes: Vec<Axis>,
    tools: Vec<Tool>,
    missing: Vec<&'static str>,
    timeout: Duration,
    keep_resident: bool,
    check: bool,
    require_faster: bool,
}

fn parse_env(value: &str) -> Result<(String, String), String> {
    let (key, value) =
        value.split_once('=').ok_or_else(|| format!("environment `{value}` is not K=V"))?;
    if key.is_empty() {
        return Err("environment key is empty".to_string());
    }
    Ok((key.to_string(), value.to_string()))
}

fn on_path(name: &str) -> Option<PathBuf> {
    let paths = std::env::var_os("PATH")?;
    std::env::split_paths(&paths).map(|dir| dir.join(name)).find(|candidate| candidate.is_file())
}

fn parse_args(args: &[String]) -> Result<Options, String> {
    let mut out = PathBuf::from("target/rival");
    let mut subjects = Vec::new();
    let mut btree = true;
    let mut edits = 7;
    let mut axes = Vec::new();
    let mut trust = None;
    let mut blaze = None;
    let mut trust_env = Vec::new();
    let mut blaze_env = Vec::new();
    let mut trust_store = None;
    let mut blaze_store = None;
    let mut keep_resident = false;
    let mut timeout = 900;
    let mut check = false;
    let mut require_faster = false;
    let mut iter = args.iter();
    while let Some(arg) = iter.next() {
        let mut value =
            |flag: &str| iter.next().cloned().ok_or_else(|| format!("{flag} needs a value"));
        match arg.as_str() {
            "--out" => out = PathBuf::from(value("--out")?),
            "--subject" => subjects.push(Subject::parse(&value("--subject")?)?),
            "--map" => {
                btree = match value("--map")?.as_str() {
                    "btree" => true,
                    "hashmap" => false,
                    other => return Err(format!("--map `{other}` is not btree or hashmap")),
                }
            }
            "--edits" => {
                edits = value("--edits")?
                    .parse()
                    .ok()
                    .filter(|n| *n > 0)
                    .ok_or("--edits needs a positive count")?
            }
            "--axis" => {
                for axis in value("--axis")?.split(',') {
                    axes.push(Axis::parse(axis.trim())?);
                }
            }
            "--trust" => trust = Some(PathBuf::from(value("--trust")?)),
            "--blaze" => blaze = Some(PathBuf::from(value("--blaze")?)),
            "--trust-env" => trust_env.push(parse_env(&value("--trust-env")?)?),
            "--blaze-env" => blaze_env.push(parse_env(&value("--blaze-env")?)?),
            "--trust-store" => trust_store = Some(PathBuf::from(value("--trust-store")?)),
            "--blaze-store" => blaze_store = Some(PathBuf::from(value("--blaze-store")?)),
            "--keep-resident" => keep_resident = true,
            "--timeout" => {
                timeout = value("--timeout")?
                    .parse()
                    .ok()
                    .filter(|n| *n > 0)
                    .ok_or("--timeout needs a positive number of seconds")?
            }
            "--check" => check = true,
            "--require-faster" => require_faster = true,
            other => return Err(format!("unknown argument `{other}`")),
        }
    }
    if subjects.is_empty() {
        subjects = ["small", "medium", "large"].map(|s| Subject::parse(s).unwrap()).to_vec();
    }
    if axes.is_empty() {
        for lane in Lane::ALL {
            for phase in Phase::ALL {
                axes.push(Axis { phase, lane });
            }
        }
    }
    axes.sort();
    axes.dedup();
    let nonce = format!(
        "{}.{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map_or(0, |since| since.as_nanos())
    );
    let mut tools = Vec::new();
    let mut missing = Vec::new();
    match trust.or_else(|| on_path("targo")) {
        Some(program) => tools.push(Tool {
            name: "trust",
            program,
            prefix: vec!["--unverified".to_string()],
            env: trust_env,
            marker: format!("{nonce}.trust"),
            store: trust_store,
        }),
        None => missing.push("trust"),
    }
    match blaze.or_else(|| on_path("blaze")) {
        Some(program) => tools.push(Tool {
            name: "blaze",
            program,
            prefix: Vec::new(),
            env: blaze_env,
            marker: format!("{nonce}.blaze"),
            store: blaze_store,
        }),
        None => missing.push("blaze"),
    }
    Ok(Options {
        out,
        subjects,
        btree,
        edits,
        axes,
        tools,
        missing,
        timeout: Duration::from_secs(timeout),
        keep_resident,
        check,
        require_faster,
    })
}

/// The generated crate: `modules` modules, each a struct with an impl, a
/// generic helper and a chain of `functions` functions that call each other
/// and the previous module, so the call graph is connected and nothing is
/// dead. Dependency-free.
fn generate(dir: &Path, subject: &Subject, btree: bool) -> std::io::Result<()> {
    let map = if btree { "BTreeMap" } else { "HashMap" };
    let name =
        format!("synth_{}x{}{}", subject.modules, subject.functions, if btree { "b" } else { "" });
    fs::create_dir_all(dir.join("src"))?;
    fs::write(
        dir.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.1.0\"\nedition = \"2021\"\n\n[workspace]\n"
        ),
    )?;
    for i in 0..subject.modules {
        fs::write(dir.join("src").join(format!("m{i:04}.rs")), module(i, subject.functions, map))?;
    }
    let mut main = String::new();
    for i in 0..subject.modules {
        let _ = writeln!(main, "mod m{i:04};");
    }
    let _ = write!(
        main,
        "\nfn main() {{\n    let seed = std::env::args().count() as u64;\n    println!(\"{{}}\", m{:04}::entry(seed));\n}}\n",
        subject.modules - 1
    );
    fs::write(dir.join("src/main.rs"), main)
}

/// `entry` adds rather than xors: the last function's `y` is both the
/// chain's result and the last term added into `acc`, so the result is
/// `2y + A` and moves with every change of `y` below 2^63, where a xor
/// cancelled the low bits `A` lacks and let two edits print the same value.
fn module(i: usize, functions: usize, map: &str) -> String {
    let previous = if i > 0 { format!("crate::m{:04}::entry(x)", i - 1) } else { "x".to_string() };
    let mut out = format!(
        "use std::collections::{map};\n\n\
         #[derive(Debug, Clone, Default)]\n\
         pub struct State {{ pub acc: u64, pub seen: {map}<u64, u64>, pub log: Vec<String> }}\n\n\
         impl State {{\n\
         \x20   pub fn note(&mut self, k: u64, v: u64) {{\n\
         \x20       *self.seen.entry(k % 64).or_insert(0) ^= v;\n\
         \x20       if self.log.len() < 4 {{ self.log.push(format!(\"{{k}}:{{v}}\")); }}\n\
         \x20       self.acc = self.acc.wrapping_mul(6364136223846793005).wrapping_add(v);\n\
         \x20   }}\n\
         }}\n\n\
         pub fn fold<T: Copy + Into<u64>>(xs: &[T], seed: u64) -> u64 {{\n\
         \x20   xs.iter().fold(seed, |a, &b| a.rotate_left(5) ^ b.into())\n\
         }}\n\n"
    );
    for j in 0..functions {
        let next =
            if j + 1 < functions { format!("f{:03}(st, y)", j + 1) } else { "y".to_string() };
        let _ = write!(
            out,
            "pub fn f{j:03}(st: &mut State, x: u64) -> u64 {{\n\
             \x20   let k: u64 = {};\n\
             \x20   let mut y = x.wrapping_add(k);\n\
             \x20   if y % {} == 0 {{ y = fold(&[y as u32, k as u32], y); }}\n\
             \x20   st.note({j}, y);\n\
             \x20   {next}\n\
             }}\n\n",
            1000 + i * 131 + j * 7,
            3 + j % 5,
        );
    }
    let _ = write!(
        out,
        "pub fn entry(x: u64) -> u64 {{\n\
         \x20   let mut st = State::default();\n\
         \x20   let x = {previous};\n\
         \x20   let r = f000(&mut st, x);\n\
         \x20   r.wrapping_add(st.acc).wrapping_add(st.seen.len() as u64 + st.log.len() as u64)\n\
         }}\n"
    );
    out
}

/// Edit `n`: the last `let k: u64 = ...;` of the middle module becomes
/// `900000 + n`. The text after edit `n` does not depend on earlier edits.
fn edit(dir: &Path, subject: &Subject, n: u64) -> Result<(), String> {
    let path = dir.join("src").join(format!("m{:04}.rs", subject.modules / 2));
    let text = fs::read_to_string(&path).map_err(|e| format!("{}: {e}", path.display()))?;
    let needle = "let k: u64 = ";
    let start =
        text.rfind(needle).ok_or_else(|| format!("{}: no constant to edit", path.display()))?;
    let value_start = start + needle.len();
    let end = value_start
        + text[value_start..]
            .find(';')
            .ok_or_else(|| format!("{}: unterminated constant", path.display()))?;
    let edited = format!("{}{}{}", &text[..value_start], 900_000 + n, &text[end..]);
    fs::write(&path, edited).map_err(|e| format!("{}: {e}", path.display()))
}

#[derive(Clone, Debug)]
struct Sample {
    subject: String,
    tool: &'static str,
    axis: Axis,
    index: usize,
    wall_ms: f64,
    status: String,
    succeeded: bool,
    output: Option<String>,
    /// Memory held after the command exited by processes carrying the
    /// tool's marker: what stays resident between this command and the next.
    resident_kb: u64,
    resident_processes: usize,
}

/// Runs one lane; returns the bytes its target directory holds at the end.
fn run_lane(
    options: &Options,
    subject: &Subject,
    tool: &Tool,
    lane: Lane,
    samples: &mut Vec<Sample>,
) -> Result<u64, String> {
    let root = options.out.join(&subject.name).join(format!("{}-{}", tool.name, lane.name()));
    if root.exists() {
        fs::remove_dir_all(&root).map_err(|e| format!("{}: {e}", root.display()))?;
    }
    let crate_dir = root.join("crate");
    generate(&crate_dir, subject, options.btree)
        .map_err(|e| format!("{}: {e}", crate_dir.display()))?;
    let phases = [Phase::Cold, Phase::Noop]
        .into_iter()
        .chain(std::iter::repeat_n(Phase::Edit, options.edits));
    let mut edit_number = FIRST_EDIT;
    for (index, phase) in phases.enumerate() {
        if phase == Phase::Edit {
            edit_number += 1;
            edit(&crate_dir, subject, edit_number)?;
        }
        let mut command = Command::new(&tool.program);
        command
            .args(&tool.prefix)
            .arg(lane.name())
            .current_dir(&crate_dir)
            .env("CARGO_TARGET_DIR", root.join("target"))
            .envs(tool.env.iter().map(|(k, v)| (k, v)))
            .env(RESIDENT_ENV, &tool.marker);
        let log = root.join(format!("{}-{index}", phase.name()));
        let (status, succeeded, wall_ms, stdout) = match timed(&mut command, &log, options.timeout)
        {
            Ok(run) => (run.status, run.succeeded, run.wall_ms, run.stdout),
            Err(error) => (error, false, 0.0, String::new()),
        };
        let output = (lane == Lane::Run)
            .then(|| {
                stdout.lines().rev().find(|l| !l.trim().is_empty()).map(|l| l.trim().to_string())
            })
            .flatten();
        let held = resident(&tool.marker);
        let resident_kb = held.iter().map(|(_, kb)| kb).sum();
        eprintln!(
            "rival: {} {} {}-{} #{index}: {wall_ms:.0} ms ({status}); {} MB resident in {} processes",
            subject.name,
            tool.name,
            phase.name(),
            lane.name(),
            resident_kb / 1024,
            held.len()
        );
        samples.push(Sample {
            subject: subject.name.clone(),
            tool: tool.name,
            axis: Axis { phase, lane },
            index,
            wall_ms,
            status,
            succeeded,
            output,
            resident_kb,
            resident_processes: held.len(),
        });
        if !succeeded {
            break;
        }
    }
    Ok(dir_bytes(&root.join("target")))
}

/// The one-minute load average, where the platform reports one.
fn load_average() -> Option<f64> {
    #[cfg(unix)]
    {
        let mut load = [0.0f64; 3];
        // SAFETY: `load` has room for the three samples requested.
        let got = unsafe { libc::getloadavg(load.as_mut_ptr(), 3) };
        if got >= 1 {
            return Some(load[0]);
        }
    }
    None
}

/// Bytes in regular files under `path`, symbolic links not followed; 0 when
/// it does not exist.
fn dir_bytes(path: &Path) -> u64 {
    let mut total = 0;
    let mut pending = vec![path.to_path_buf()];
    while let Some(dir) = pending.pop() {
        let Ok(entries) = fs::read_dir(&dir) else { continue };
        for entry in entries.flatten() {
            match entry.file_type() {
                Ok(kind) if kind.is_dir() => pending.push(entry.path()),
                Ok(kind) if kind.is_file() => {
                    total += entry.metadata().map_or(0, |metadata| metadata.len())
                }
                _ => {}
            }
        }
    }
    total
}

/// Live processes whose environment holds `RESIDENT_ENV=marker`, with their
/// resident memory in KiB. macOS shows another process's environment to
/// `ps -E` for the same user, except for system binaries, which no tool
/// measured here is; Linux has `/proc/<pid>/environ`. Elsewhere it finds
/// nothing, and the resident row reads 0.
fn resident(marker: &str) -> Vec<(u32, u64)> {
    let wanted = format!("{RESIDENT_ENV}={marker}");
    let mut found = Vec::new();
    if cfg!(target_os = "macos") {
        let Ok(out) =
            Command::new("/bin/ps").args(["-axww", "-E", "-o", "pid=,rss=,command="]).output()
        else {
            return found;
        };
        for line in String::from_utf8_lossy(&out.stdout).lines() {
            let mut words = line.split_whitespace();
            let (Some(pid), Some(rss)) = (words.next(), words.next()) else { continue };
            if !words.any(|word| word == wanted) {
                continue;
            }
            if let (Ok(pid), Ok(rss)) = (pid.parse::<u32>(), rss.parse::<u64>()) {
                if pid != std::process::id() {
                    found.push((pid, rss));
                }
            }
        }
    } else if cfg!(target_os = "linux") {
        let Ok(entries) = fs::read_dir("/proc") else { return found };
        for entry in entries.flatten() {
            let Some(pid) = entry.file_name().to_str().and_then(|name| name.parse::<u32>().ok())
            else {
                continue;
            };
            let Ok(environ) = fs::read(entry.path().join("environ")) else { continue };
            if !environ.split(|byte| *byte == 0).any(|var| var == wanted.as_bytes()) {
                continue;
            }
            let rss = fs::read_to_string(entry.path().join("status"))
                .ok()
                .and_then(|status| {
                    status.lines().find_map(|line| {
                        line.strip_prefix("VmRSS:")?
                            .trim()
                            .trim_end_matches("kB")
                            .trim()
                            .parse()
                            .ok()
                    })
                })
                .unwrap_or(0);
            found.push((pid, rss));
        }
    }
    found
}

/// Stop what `resident` finds for `marker`: SIGTERM, up to ten seconds to
/// exit, then SIGKILL. Every process it signals was started by one of this
/// run's commands, since only they carry this run's marker.
#[cfg(unix)]
fn stop_resident(marker: &str) {
    let signal_all = |signal| {
        for (pid, _) in resident(marker) {
            let Ok(pid) = libc::pid_t::try_from(pid) else { continue };
            // SAFETY: kill(2) takes no pointers; a pid that has exited fails harmlessly.
            unsafe { libc::kill(pid, signal) };
        }
    };
    signal_all(libc::SIGTERM);
    let started = Instant::now();
    while !resident(marker).is_empty() {
        if started.elapsed() > Duration::from_secs(10) {
            signal_all(libc::SIGKILL);
            break;
        }
        std::thread::sleep(Duration::from_millis(100));
    }
}

#[cfg(not(unix))]
fn stop_resident(_marker: &str) {}

fn median(values: &mut [f64]) -> Option<f64> {
    if values.is_empty() {
        return None;
    }
    values.sort_by(f64::total_cmp);
    let mid = values.len() / 2;
    Some(if values.len() % 2 == 1 { values[mid] } else { (values[mid - 1] + values[mid]) / 2.0 })
}

/// One tool's value for a subject and axis: the median of that phase's runs,
/// or `None` if the lane did not reach it or any of its runs failed.
fn value(samples: &[Sample], subject: &str, tool: &str, axis: Axis, edits: usize) -> Option<f64> {
    let runs: Vec<&Sample> = samples
        .iter()
        .filter(|s| s.subject == subject && s.tool == tool && s.axis == axis)
        .collect();
    let expected = if axis.phase == Phase::Edit { edits } else { 1 };
    if runs.len() != expected || runs.iter().any(|s| !s.succeeded) {
        return None;
    }
    median(&mut runs.iter().map(|s| s.wall_ms).collect::<Vec<_>>())
}

/// The `run` lane's printed values, in run order, for one subject and tool.
fn outputs(samples: &[Sample], subject: &str, tool: &str) -> Vec<Option<String>> {
    let mut runs: Vec<&Sample> = samples
        .iter()
        .filter(|s| s.subject == subject && s.tool == tool && s.axis.lane == Lane::Run)
        .collect();
    runs.sort_by_key(|s| s.index);
    runs.iter().map(|s| s.output.clone()).collect()
}

/// One judged row: a subject, what is measured, and each tool's value.
struct Row {
    subject: String,
    axis: String,
    unit: &'static str,
    lower_is_better: bool,
    trust: Option<f64>,
    blaze: Option<f64>,
}

impl Row {
    fn trust_at_least_as_good(&self) -> Option<bool> {
        let (t, b) = (self.trust?, self.blaze?);
        Some(if self.lower_is_better { t <= b } else { t >= b })
    }
}

/// Per subject and tool, after its lanes ran: the target bytes and the
/// store's growth.
#[derive(Default)]
struct Disk {
    target: u64,
    store_growth: u64,
}

fn rows(
    options: &Options,
    samples: &[Sample],
    disk: &BTreeMap<(String, &'static str), Disk>,
) -> Vec<Row> {
    let mut rows = Vec::new();
    let run_selected = options.axes.iter().any(|a| a.lane == Lane::Run);
    for subject in &options.subjects {
        let per_tool =
            |measure: &dyn Fn(&'static str) -> Option<f64>| (measure("trust"), measure("blaze"));
        for axis in &options.axes {
            let (trust, blaze) =
                per_tool(&|tool| value(samples, &subject.name, tool, *axis, options.edits));
            rows.push(Row {
                subject: subject.name.clone(),
                axis: axis.name(),
                unit: "ms",
                lower_is_better: true,
                trust,
                blaze,
            });
        }
        let ran = |tool: &str| samples.iter().any(|s| s.subject == subject.name && s.tool == tool);
        let (trust, blaze) = per_tool(&|tool| {
            ran(tool).then(|| {
                samples
                    .iter()
                    .filter(|s| s.subject == subject.name && s.tool == tool)
                    .map(|s| s.resident_kb)
                    .max()
                    .unwrap_or(0) as f64
                    / 1024.0
            })
        });
        rows.push(Row {
            subject: subject.name.clone(),
            axis: "resident-mb".to_string(),
            unit: "MB",
            lower_is_better: true,
            trust,
            blaze,
        });
        let (trust, blaze) = per_tool(&|tool| {
            disk.get(&(subject.name.clone(), tool))
                .map(|d| (d.target + d.store_growth) as f64 / (1024.0 * 1024.0))
        });
        rows.push(Row {
            subject: subject.name.clone(),
            axis: "disk-mb".to_string(),
            unit: "MB",
            lower_is_better: true,
            trust,
            blaze,
        });
        if run_selected {
            let (trust, blaze) = per_tool(&|tool| {
                let runs: Vec<&Sample> = samples
                    .iter()
                    .filter(|s| {
                        s.subject == subject.name && s.tool == tool && s.axis.lane == Lane::Run
                    })
                    .collect();
                (!runs.is_empty()).then(|| {
                    f64::from(u8::from(
                        runs.len() == options.edits + 2 && runs.iter().all(|s| s.succeeded),
                    ))
                })
            });
            rows.push(Row {
                subject: subject.name.clone(),
                axis: "runs".to_string(),
                unit: "",
                lower_is_better: false,
                trust,
                blaze,
            });
        }
    }
    rows
}

/// The `--check` problems: missing rows, failed commands, output that
/// differs between the tools, and edits whose output did not change.
fn problems(options: &Options, samples: &[Sample], rows: &[Row]) -> Vec<String> {
    let mut problems = Vec::new();
    for missing in &options.missing {
        problems.push(format!("no {missing} executable (pass --{missing} <PATH>)"));
    }
    for sample in samples.iter().filter(|s| !s.succeeded) {
        problems.push(format!(
            "{} {} {} #{}: {}",
            sample.subject,
            sample.tool,
            sample.axis.name(),
            sample.index,
            sample.status
        ));
    }
    // Both tools, found or not: a missing tool leaves every row unjudged.
    for row in rows {
        for (tool, value) in [("trust", row.trust), ("blaze", row.blaze)] {
            if value.is_none() {
                problems.push(format!("{} {}: no {tool} row", row.subject, row.axis));
            }
        }
    }
    for subject in &options.subjects {
        if !options.axes.iter().any(|a| a.lane == Lane::Run) {
            continue;
        }
        let printed: Vec<(&str, Vec<Option<String>>)> = options
            .tools
            .iter()
            .map(|t| (t.name, outputs(samples, &subject.name, t.name)))
            .collect();
        for (tool, values) in &printed {
            if values.len() != options.edits + 2 || values.iter().any(Option::is_none) {
                problems.push(format!(
                    "{} {tool}: the run lane did not print a value every run",
                    subject.name
                ));
                continue;
            }
            if values[0] != values[1] {
                problems.push(format!(
                    "{} {tool}: a no-op run changed the printed value",
                    subject.name
                ));
            }
            for i in 2..values.len() {
                if values[i] == values[i - 1] {
                    problems.push(format!(
                        "{} {tool}: edit {} did not change the printed value (stale program)",
                        subject.name,
                        i - 1
                    ));
                }
            }
        }
        if let [(first, a), rest @ ..] = printed.as_slice() {
            for (other, b) in rest {
                for (i, (x, y)) in a.iter().zip(b).enumerate() {
                    if x != y {
                        problems.push(format!(
                            "{} run #{i}: {first} printed {x:?}, {other} printed {y:?}",
                            subject.name
                        ));
                    }
                }
            }
        }
    }
    problems
}

struct Timed {
    status: String,
    succeeded: bool,
    wall_ms: f64,
    stdout: String,
}

/// Run `command` to its exit under `timeout`, its output in `<log>.stdout`
/// and `<log>.stderr`. The clock stops when the command exits. Output goes
/// to files rather than pipes so a process the tool leaves running on
/// purpose (a rival's resident worker) neither holds the measurement open
/// nor is killed by it; only a command past its timeout is killed. The
/// exit is polled every 200 µs, well under the shortest time measured.
fn timed(command: &mut Command, log: &Path, timeout: Duration) -> Result<Timed, String> {
    let with = |extension: &str| log.with_extension(extension);
    let stdout_path = with("stdout");
    let stderr_path = with("stderr");
    let open = |path: &Path| fs::File::create(path).map_err(|e| format!("{}: {e}", path.display()));
    command.stdin(Stdio::null()).stdout(open(&stdout_path)?).stderr(open(&stderr_path)?);
    let started = Instant::now();
    let mut child =
        command.spawn().map_err(|e| format!("cannot start {:?}: {e}", command.get_program()))?;
    let status = loop {
        match child.try_wait() {
            Ok(Some(status)) => break Ok(status),
            Ok(None) if started.elapsed() >= timeout => {
                let _ = child.kill();
                let _ = child.wait();
                break Err(format!("timed out after {} s", timeout.as_secs()));
            }
            Ok(None) => std::thread::sleep(Duration::from_micros(200)),
            Err(error) => break Err(format!("wait failed: {error}")),
        }
    };
    let wall_ms = started.elapsed().as_secs_f64() * 1000.0;
    let status = status?;
    let stdout = fs::read(&stdout_path).map_err(|e| format!("{}: {e}", stdout_path.display()))?;
    Ok(Timed {
        status: status.to_string(),
        succeeded: status.success(),
        wall_ms,
        stdout: String::from_utf8_lossy(&stdout).into_owned(),
    })
}

fn version(tool: &Tool, out: &Path) -> String {
    let mut command = Command::new(&tool.program);
    command.args(&tool.prefix).arg("--version").envs(tool.env.iter().map(|(k, v)| (k, v)));
    match timed(&mut command, &out.join(format!("{}-version", tool.name)), Duration::from_secs(60))
    {
        Ok(run) if run.succeeded => run.stdout.lines().next().unwrap_or("").trim().to_string(),
        Ok(run) => format!("unknown ({})", run.status),
        Err(error) => format!("unknown ({error})"),
    }
}

fn prepare_out(out: &Path) -> Result<(), String> {
    if out.exists() {
        let empty =
            fs::read_dir(out).map_err(|e| format!("{}: {e}", out.display()))?.next().is_none();
        if !empty && !out.join(MARKER).is_file() {
            return Err(format!(
                "{} exists and was not made by this command; choose another --out",
                out.display()
            ));
        }
    }
    fs::create_dir_all(out).map_err(|e| format!("{}: {e}", out.display()))?;
    fs::write(out.join(MARKER), "targo trust benchmark rival\n")
        .map_err(|e| format!("{}: {e}", out.display()))
}

pub(crate) fn run(args: &[String]) -> ExitCode {
    if args.iter().any(|a| a == "-h" || a == "--help") {
        print!("{USAGE}");
        return ExitCode::SUCCESS;
    }
    let options = match parse_args(args) {
        Ok(options) => options,
        Err(error) => {
            eprintln!("targo trust benchmark rival: {error}");
            eprint!("{USAGE}");
            return ExitCode::from(2);
        }
    };
    if let Err(error) = prepare_out(&options.out) {
        eprintln!("targo trust benchmark rival: {error}");
        return ExitCode::from(2);
    }
    let load_before = load_average();
    let versions: BTreeMap<&str, String> =
        options.tools.iter().map(|t| (t.name, version(t, &options.out))).collect();
    let lanes: Vec<Lane> =
        Lane::ALL.into_iter().filter(|l| options.axes.iter().any(|a| a.lane == *l)).collect();
    let mut samples = Vec::new();
    let mut disk = BTreeMap::new();
    for subject in &options.subjects {
        for tool in &options.tools {
            let store_before = tool.store.as_deref().map(dir_bytes);
            let mut target = 0;
            for lane in &lanes {
                match run_lane(&options, subject, tool, *lane, &mut samples) {
                    Ok(bytes) => target += bytes,
                    Err(error) => {
                        eprintln!("targo trust benchmark rival: {error}");
                        return ExitCode::from(2);
                    }
                }
            }
            let store_growth = match (tool.store.as_deref(), store_before) {
                (Some(store), Some(before)) => dir_bytes(store).saturating_sub(before),
                _ => 0,
            };
            disk.insert((subject.name.clone(), tool.name), Disk { target, store_growth });
        }
        if !options.keep_resident {
            for tool in &options.tools {
                stop_resident(&tool.marker);
            }
        }
    }

    let load_after = load_average();
    let rows = rows(&options, &samples, &disk);
    let mut table = String::new();
    let _ = writeln!(
        table,
        "{:<10} {:<12} {:>10} {:>10} {:>8}",
        "subject", "axis", "trust", "blaze", "ratio"
    );
    let (mut judged, mut good) = (0, 0);
    for row in &rows {
        if let Some(at_least_as_good) = row.trust_at_least_as_good() {
            judged += 1;
            good += usize::from(at_least_as_good);
        }
        let cell = |v: Option<f64>| v.map_or("-".to_string(), |v| format!("{v:.0}"));
        let ratio = match (row.trust, row.blaze) {
            (Some(t), Some(b)) if b > 0.0 && row.lower_is_better => format!("{:.2}", t / b),
            _ => "-".to_string(),
        };
        let _ = writeln!(
            table,
            "{:<10} {:<12} {:>10} {:>10} {:>8}",
            row.subject,
            row.axis,
            cell(row.trust),
            cell(row.blaze),
            ratio
        );
    }
    let rows_total = rows.len();
    let problems = problems(&options, &samples, &rows);
    print!("{table}");
    println!(
        "rival: {good} of {rows_total} rows at least as good as blaze ({judged} judged; trust: {}; blaze: {})",
        versions.get("trust").map_or("absent", String::as_str),
        versions.get("blaze").map_or("absent", String::as_str),
    );
    let load = |load: Option<f64>| load.map_or("unknown".to_string(), |l| format!("{l:.1}"));
    println!(
        "rival: one-minute load average {} before, {} after; other work on the machine moves every row",
        load(load_before),
        load(load_after)
    );

    let report = json!({
        "schema": REPORT_SCHEMA,
        "subjects": options.subjects.iter().map(|s| json!({
            "name": s.name, "modules": s.modules, "functions": s.functions,
        })).collect::<Vec<_>>(),
        "map": if options.btree { "btree" } else { "hashmap" },
        "edits": options.edits,
        "tools": options.tools.iter().map(|t| json!({
            "name": t.name,
            "program": t.program.display().to_string(),
            "version": versions.get(t.name),
        })).collect::<Vec<_>>(),
        "missing": options.missing,
        "machine": {
            "os": std::env::consts::OS,
            "arch": std::env::consts::ARCH,
            "cores": std::thread::available_parallelism().map_or(0, |n| n.get()),
            "load_average_before": load_before,
            "load_average_after": load_after,
        },
        "rows": rows.iter().map(|row| json!({
            "subject": row.subject,
            "axis": row.axis,
            "unit": row.unit,
            "lower_is_better": row.lower_is_better,
            "trust": row.trust,
            "blaze": row.blaze,
            "trust_at_least_as_good": row.trust_at_least_as_good(),
        })).collect::<Vec<_>>(),
        "number": { "at_least_as_good": good, "judged": judged, "rows": rows_total },
        "problems": problems,
        "samples": samples.iter().map(|s| json!({
            "subject": s.subject,
            "tool": s.tool,
            "axis": s.axis.name(),
            "index": s.index,
            "wall_ms": s.wall_ms,
            "status": s.status,
            "succeeded": s.succeeded,
            "output": s.output,
            "resident_kb": s.resident_kb,
            "resident_processes": s.resident_processes,
        })).collect::<Vec<Value>>(),
    });
    let report_path = options.out.join("rival.json");
    match serde_json::to_string_pretty(&report) {
        Ok(text) => {
            if let Err(error) = fs::write(&report_path, text + "\n") {
                eprintln!("targo trust benchmark rival: {}: {error}", report_path.display());
                return ExitCode::from(2);
            }
        }
        Err(error) => {
            eprintln!("targo trust benchmark rival: report: {error}");
            return ExitCode::from(2);
        }
    }

    let mut failed = false;
    if options.check && !problems.is_empty() {
        for problem in &problems {
            eprintln!("rival --check: {problem}");
        }
        failed = true;
    }
    if options.require_faster && (judged != rows_total || good != rows_total) {
        eprintln!(
            "rival --require-faster: Trust is at least as good on {good} of {rows_total} rows ({judged} judged)"
        );
        failed = true;
    }
    if failed { ExitCode::from(1) } else { ExitCode::SUCCESS }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn subjects_and_axes_parse() {
        let small = Subject::parse("small").unwrap();
        assert_eq!((small.modules, small.functions), (20, 25));
        let tiny = Subject::parse("tiny=3x2").unwrap();
        assert_eq!((tiny.name.as_str(), tiny.modules, tiny.functions), ("tiny", 3, 2));
        assert!(Subject::parse("tiny=3").is_err());
        assert!(Subject::parse("tiny=0x2").is_err());
        assert!(Subject::parse("../x=1x1").is_err());
        assert_eq!(Axis::parse("edit-run").unwrap().name(), "edit-run");
        assert!(Axis::parse("warm-run").is_err());
    }

    #[test]
    fn an_edit_changes_one_constant_and_depends_only_on_its_number() {
        let dir = tempfile::tempdir().unwrap();
        let subject = Subject::parse("tiny=3x4").unwrap();
        generate(dir.path(), &subject, true).unwrap();
        let path = dir.path().join("src/m0001.rs");
        let original = fs::read_to_string(&path).unwrap();
        edit(dir.path(), &subject, 1001).unwrap();
        let once = fs::read_to_string(&path).unwrap();
        assert_ne!(original, once);
        assert_eq!(once.matches("let k: u64 = 901001;").count(), 1);
        let changed: Vec<_> = original.lines().zip(once.lines()).filter(|(a, b)| a != b).collect();
        assert_eq!(changed.len(), 1, "exactly one line changes");
        edit(dir.path(), &subject, 1002).unwrap();
        edit(dir.path(), &subject, 1001).unwrap();
        assert_eq!(fs::read_to_string(&path).unwrap(), once);
    }

    #[test]
    fn the_generated_crate_matches_its_size() {
        let dir = tempfile::tempdir().unwrap();
        let subject = Subject::parse("tiny=2x3").unwrap();
        generate(dir.path(), &subject, false).unwrap();
        let main = fs::read_to_string(dir.path().join("src/main.rs")).unwrap();
        assert!(main.contains("mod m0000;") && main.contains("mod m0001;"));
        assert!(main.contains("m0001::entry(seed)"));
        let m1 = fs::read_to_string(dir.path().join("src/m0001.rs")).unwrap();
        assert!(m1.contains("use std::collections::HashMap;"));
        assert!(m1.contains("crate::m0000::entry(x)"));
        assert_eq!(m1.matches("pub fn f0").count(), 3);
    }
}
