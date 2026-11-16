// Trust (2026-09-29): a coroutine's verdicts, the crate call-graph oracles'
// verdicts and the spawn census are a function of the program, not of which
// query first demanded a coroutine's layout.
//
// Before, the layout of a local coroutine was read from its `optimized_mir`. A
// signature const that needs a future's size (`fn g() -> [u8; size_of_ret(&work)]`)
// made wfcheck demand it from inside type computation, and the first
// `inner_optimized_mir` forced the SCC oracle and the spawn census from there:
// that crate did not compile at all (E0391), and where it did, WHERE the oracles
// ran decided which bodies were already stolen. Now the layout is read from the
// pre-steal elaborated MIR (`trust_local_coroutine_layout`) and the oracles are
// forced at one fixed program point (`trust_force_crate_graph_oracles`).
//
// The same crate is compiled twice, with and without such a signature appended
// at the END of the file (so no existing span moves), and the verdict rows of
// every shared function — the coroutine, the spawning `launch`/`wrapper` pair,
// and the mutually recursive `ping`/`pong` SCC — must be identical: every
// result's kind, outcome, solver, reason, description and location.
// Timings and evidence blobs are left out on purpose.

use std::collections::BTreeMap;

use run_make_support::serde_json::{self, Value};
use run_make_support::{bin_name, cmd, rfs, rustc_path};

const TRUST_VANILLA_REAL_RUSTC_ENV: &str = "__COMPILETEST_TRUST_VANILLA_REAL_RUSTC";

const PLAIN: &str = r#"pub async fn work(x: u8) -> u16 { (x as u16) + 1 }
pub fn launch() { let _h = std::thread::spawn(|| {}); }
pub fn wrapper() { launch(); }
pub fn ping(n: u32) -> u32 { if n == 0 { 0 } else { pong(n - 1) } }
pub fn pong(n: u32) -> u32 { if n == 0 { 1 } else { ping(n - 1) } }
"#;

const LAYOUT_SIGNATURE: &str = r#"pub const fn size_of_ret<F: Fn(u8) -> R, R>(_: &F) -> usize { core::mem::size_of::<R>() }
pub fn g() -> [u8; size_of_ret(&work)] { unimplemented!() }
"#;

const SHARED: [&str; 6] = [
    "orderdemo::work::{closure#0}",
    "orderdemo::work",
    "orderdemo::launch",
    "orderdemo::wrapper",
    "orderdemo::ping",
    "orderdemo::pong",
];

/// `function -> [verdict of each result, then the row totals]` for the shared
/// functions. A result's verdict is its kind, outcome, solver, reason,
/// description and location; `time_ms`, digests and evidence blobs are left out.
fn verdicts(stderr: &str) -> BTreeMap<String, Vec<String>> {
    let mut out = BTreeMap::new();
    for line in stderr.lines() {
        let Some(payload) = line.strip_prefix("TRUST_JSON:") else { continue };
        let row: Value = serde_json::from_str(payload).expect("TRUST_JSON payload is JSON");
        if row["type"] != "function_result" {
            continue;
        }
        let function = row["function"].as_str().expect("function row names its function");
        if !SHARED.contains(&function) {
            continue;
        }
        let mut rows: Vec<String> = row["results"]
            .as_array()
            .expect("function row has results")
            .iter()
            .map(|result| {
                ["kind", "outcome", "solver", "reason", "description", "location"]
                    .iter()
                    .map(|key| format!("{key}={}", result[*key]))
                    .collect::<Vec<_>>()
                    .join(" | ")
            })
            .collect();
        rows.push(
            ["proved", "failed", "unknown", "timed_out", "skipped", "runtime_checked", "total"]
                .iter()
                .map(|key| format!("{key}={}", row[*key]))
                .collect::<Vec<_>>()
                .join(" "),
        );
        assert!(out.insert(function.to_string(), rows).is_none(), "duplicate row for {function}");
    }
    out
}

/// Compile `source` as `orderdemo.rs` — the SAME path for both variants, so every
/// row's `location` agrees — into `lib{out}.rmeta`.
fn compile(trustc: &std::path::Path, source: &str, out: &str) -> String {
    rfs::write("orderdemo.rs", source);
    cmd(trustc)
        .arg("--edition=2021")
        .arg("--crate-type=lib")
        .arg("--crate-name=orderdemo")
        .arg("--emit=metadata")
        .arg("-Ztrust-verify=on")
        .arg("-Ztrust-policy=advisory")
        .arg("-Ztrust-verify-output=json")
        .arg("--error-format=human")
        .arg("orderdemo.rs")
        .arg("-o")
        .arg(format!("lib{out}.rmeta"))
        // An inherited nested-process off-switch would beat `-Ztrust-verify=on`.
        .env_remove("TRUST_NO_VERIFY")
        .run()
        .stderr_utf8()
}

/// The human-readable diagnostics of `output`, without the (large) transport rows.
fn diagnostics(output: &str) -> String {
    output.lines().filter(|l| !l.starts_with("TRUST_JSON:")).collect::<Vec<_>>().join("\n")
}

fn main() {
    let rustc = std::path::PathBuf::from(rustc_path());
    let trustc = rustc.with_file_name(bin_name("trustc"));
    let trustc = if trustc.exists() { trustc } else { rustc };
    if std::env::var_os(TRUST_VANILLA_REAL_RUSTC_ENV).is_some() {
        // The upstream compiler does not know Trust's policy/output options.
        return;
    }

    let plain = compile(&trustc, PLAIN, "plain");
    let with_layout = compile(&trustc, &format!("{PLAIN}{LAYOUT_SIGNATURE}"), "layout");
    for (name, output) in [("plain", &plain), ("layout", &with_layout)] {
        for forbidden in ["E0391", "E0733", "cycle detected"] {
            assert!(!output.contains(forbidden), "{name}: `{forbidden}` in:\n{}", diagnostics(output));
        }
    }

    let (a, b) = (verdicts(&plain), verdicts(&with_layout));
    for function in SHARED {
        assert!(a.contains_key(function), "plain: no row for {function}:\n{}", diagnostics(&plain));
        assert!(b.contains_key(function), "layout: no row for {function}:\n{}", diagnostics(&with_layout));
    }
    // The spawn census must SEE the spawn in both: `wrapper` is refused as a
    // transitive spawner, not quiet and not an unknown.
    for (name, output) in [("plain", &plain), ("layout", &with_layout)] {
        assert!(
            output.contains("local callee reaches a std thread spawn through calls and drops"),
            "{name}: the spawn census lost `wrapper`'s edge:\n{}",
            diagnostics(output)
        );
    }
    if a != b {
        let mut diff = String::new();
        for function in SHARED {
            if a[function] != b[function] {
                diff.push_str(&format!(
                    "== {function}\n-- plain\n{}\n-- layout\n{}\n",
                    a[function].join("\n"),
                    b[function].join("\n")
                ));
            }
        }
        panic!("verdicts depend on a layout-demanding signature:\n{diff}");
    }
}
