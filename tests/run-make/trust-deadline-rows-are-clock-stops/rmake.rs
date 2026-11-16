//! Trust (determinism plan §3.7, 2026-10-01): a row a CLOCK left unproved is
//! published as a clock stop — outcome `timeout`, the `[stop:wall-backstop]`
//! token, counted in its function's `timed_out` — never as an `unknown` that
//! states no cause, at `0ms`; and the `timed_out=` the compiler prints in its
//! verifier status note, which a release judge sums, counts it.
//!
//! Measured on the release lane at load ~70: aterm-codec's
//! `base64::encode_padded` fell from 73/81 proved to 0/83, every row
//! `trust-full-verifier, 0ms`, and its note said `timed_out=0`, so the judge
//! could not tell a clock from a regression. The lanes that give up on the
//! per-function deadline filled the rows they had not reached with "no
//! result" and said nothing.
//!
//! A 1 ms per-function budget forces a clock stop on any host. WHICH lane
//! meets the expired deadline first depends on the host: almost always a
//! preprocessing checkpoint (the advisory budget verdict's one row), on a fast
//! enough host the native bundle build, the native dispatch, the ay bridge,
//! kernel certification, S1 or a live mint. Every one of them must publish the
//! rows it leaves as clock stops, so this recipe pins the invariant on the
//! published rows and the printed note rather than on a lane:
//!  * at least one row is left to the clock;
//!  * every row that is neither proved, failed nor skipped is a `timeout`, or
//!    carries the `wall-backstop` token; none is an `unknown` without it;
//!  * the function's `timed_out` counts exactly its `timeout` rows;
//!  * the sum of every `timed_out=<n>` in the log is exactly the number of
//!    rows the clock left: each is counted, once.
//! `-Coverflow-checks=off` keeps the widening add's overflow row without a
//! runtime check, so a clock stop on it publishes `timeout` rather than
//! `runtime_checked`, whichever lane met the deadline. The authority-phase
//! lanes themselves are pinned in-crate
//! (`full_lane_authority_tail_publishes_rows_its_deadline_cut_as_clock_timeouts`
//! and its siblings in `rustc_mir_transform`'s `trust_verify` tests), since no
//! wall-clock budget reaches them deterministically from here.
//!
//! CONTROL: the same function with the budget disabled (`=0`) has `timed_out`
//! 0, no row carrying the token, and no nonzero `timed_out=` in its log, so the
//! assertions above cannot pass by every row having been relabelled.

use run_make_support::{rfs, rustc, serde_json};

const TRUST_NO_VERIFY_ENV: &str = "TRUST_NO_VERIFY";
const TRUST_VANILLA_REAL_RUSTC_ENV: &str = "__COMPILETEST_TRUST_VANILLA_REAL_RUSTC";
const FUNCTION: &str = "deadline::widen_add";
const WALL_BACKSTOP: &str = "[stop:wall-backstop]";

fn function_row(stderr: &str) -> serde_json::Value {
    let function_token = format!("\"function\":\"{FUNCTION}\"");
    let rows: Vec<serde_json::Value> = stderr
        .lines()
        .filter(|line| line.starts_with("TRUST_JSON:") && line.contains(&function_token))
        .map(|line| {
            serde_json::from_str(&line["TRUST_JSON:".len()..])
                .expect("every TRUST_JSON line must be a JSON object")
        })
        .filter(|row: &serde_json::Value| row["type"] == "function_result")
        .collect();
    assert_eq!(rows.len(), 1, "exactly one function_result row for {FUNCTION}:\n{stderr}");
    rows.into_iter().next().expect("one row")
}

/// What a release judge reads off a check's log: every `timed_out=<n>`,
/// summed. (The JSON rows spell the field `"timed_out":`, so they are not read.)
fn judged_timed_out(stderr: &str) -> u64 {
    stderr
        .match_indices("timed_out=")
        .map(|(at, token)| {
            stderr[at + token.len()..]
                .chars()
                .take_while(char::is_ascii_digit)
                .collect::<String>()
                .parse::<u64>()
                .unwrap_or(0)
        })
        .sum()
}

fn verify(budget_ms: u32) -> (serde_json::Value, u64, String) {
    let out = rustc()
        .input("deadline.rs")
        .crate_type("lib")
        .arg("-Ztrust-verify=on")
        .arg("-Ztrust-policy=advisory")
        .arg("-Ztrust-verify-output=json")
        .arg("-Coverflow-checks=off")
        .arg(format!("-Ztrust-verify-function-budget-ms={budget_ms}"))
        .env_remove(TRUST_NO_VERIFY_ENV)
        .run();
    let stderr = out.stderr_utf8();
    (function_row(&stderr), judged_timed_out(&stderr), stderr)
}

fn main() {
    if std::env::var_os(TRUST_VANILLA_REAL_RUSTC_ENV).is_some() {
        // The upstream compiler does not know Trust's verifier options.
        return;
    }
    // A widening add: provable in milliseconds, so with no deadline every row
    // decides and only the 1 ms budget can leave one to a clock.
    rfs::write(
        "deadline.rs",
        "pub fn widen_add(a: u8, b: u8) -> u16 {\n    a as u16 + b as u16\n}\n",
    );

    let (expired, judged, stderr) = verify(1);
    let total = expired["total"].as_u64().expect("total");
    assert!(total >= 1, "the function publishes at least one row: {expired}");
    let (mut timeouts, mut clocked) = (0u64, 0u64);
    for result in expired["results"].as_array().expect("results array") {
        let outcome = result["outcome"].as_str().expect("outcome");
        if matches!(outcome, "proved" | "failed" | "skipped") {
            continue;
        }
        clocked += 1;
        timeouts += u64::from(outcome == "timeout");
        assert!(
            outcome == "timeout"
                || result["reason"].as_str().is_some_and(|reason| reason.contains(WALL_BACKSTOP)),
            "an undecided row under an expired deadline must say a clock stopped it: {result}"
        );
    }
    assert!(clocked >= 1, "a 1 ms budget leaves at least one row to the clock: {expired}");
    assert_eq!(
        expired["timed_out"].as_u64(),
        Some(timeouts),
        "`timed_out` counts exactly the rows published as timeouts: {expired}"
    );
    assert_eq!(
        judged, clocked,
        "the log's `timed_out=` counts each row the clock left unproved, once:\n{stderr}"
    );

    // CONTROL: no deadline, no clock stop.
    let (unbounded, judged, stderr) = verify(0);
    assert_eq!(unbounded["timed_out"].as_u64(), Some(0), "{unbounded}");
    for result in unbounded["results"].as_array().expect("results array") {
        assert!(
            !result["reason"].as_str().unwrap_or("").contains(WALL_BACKSTOP),
            "no clock stopped any row of the control: {result}"
        );
    }
    assert_eq!(judged, 0, "no clock, no lapse in the log:\n{stderr}");
}
