// Trust (assumption ledger, Stage 1): the machine-readable transport contract
// for assumption rows. Compiling an async fn under the nonfatal lame policy with
// -Ztrust-policy=advisory -Ztrust-verify-output=json must emit a TRUST_JSON function_result row with
// kind "assumption:coroutine" and outcome "skipped" — and that row must never
// claim proof or match the full-verifier text markers targo's report layer
// classifies on (is_full_verifier_text). Batteries-on raw compilation is
// strict; the vanilla replay wrapper (-Ztrust-verify=off) emits no TRUST_JSON.

use std::path::PathBuf;

use run_make_support::{bin_name, cmd, rfs, rustc_path};

const TRUST_VANILLA_REAL_RUSTC_ENV: &str = "__COMPILETEST_TRUST_VANILLA_REAL_RUSTC";

fn assert_transport_outcome(output: &str, function: &str, kind: &str, outcome: &str) {
    let function_token = format!("\"function\":\"{function}\"");
    let kind_token = format!("\"kind\":\"{kind}\"");
    let outcome_token = format!("\"outcome\":\"{outcome}\"");
    for line in output
        .lines()
        .filter(|line| line.starts_with("TRUST_JSON:") && line.contains(&function_token))
    {
        if let Some(kind_at) = line.find(&kind_token) {
            let after_kind = &line[kind_at..];
            let actual_outcome =
                after_kind.find("\"outcome\":\"").map(|outcome_at| &after_kind[outcome_at..]);
            assert!(
                actual_outcome.is_some_and(|tail| tail.starts_with(&outcome_token)),
                "transport kind {kind} for {function} did not carry outcome {outcome}: {line}"
            );
            return;
        }
    }
    panic!("missing transport kind {kind} for {function}:\n{output}");
}

fn assert_exactly_one_transport_kind(output: &str, kind: &str) {
    let token = format!("\"kind\":\"{kind}\"");
    let count = output
        .lines()
        .filter(|line| line.starts_with("TRUST_JSON:"))
        .map(|line| line.matches(&token).count())
        .sum::<usize>();
    assert_eq!(count, 1, "expected exactly one {kind} transport row:\n{output}");
}

fn main() {
    let rustc = PathBuf::from(rustc_path());
    let trustc = rustc.with_file_name(bin_name("trustc"));
    let trustc = if trustc.exists() { trustc } else { rustc };

    if std::env::var_os(TRUST_VANILLA_REAL_RUSTC_ENV).is_some() {
        // The upstream compiler does not know Trust's policy/output options.
        return;
    }

    rfs::write("tick.rs", "pub async fn tick(x: u32) -> u32 { x }\nfn main() {}\n");

    let vanilla = cmd(&trustc)
        .arg("--edition")
        .arg("2021")
        .arg("-Ztrust-verify=off")
        .arg("-Ztrust-verify-output=json")
        .arg("tick.rs")
        .arg("-o")
        .arg("tick")
        .run()
        .stderr_utf8();
    assert!(
        !vanilla.contains("TRUST_JSON"),
        "the explicit vanilla lane must emit no verifier transport:\n{vanilla}"
    );

    let out = cmd(&trustc)
        .arg("--edition")
        .arg("2021")
        .arg("-Ztrust-policy=advisory")
        .arg("-Ztrust-verify-output=json")
        .arg("tick.rs")
        .arg("-o")
        .arg("tick-verified")
        .run()
        .stderr_utf8();

    // Optimized MIR visits the coroutine body once; the outer async function is
    // only a constructor and has no independent verifier row. Assert on
    // substrings of matched lines only — never on unrelated rows, time_ms, or
    // host paths.
    // The compiler also mirrors transport through a structured diagnostic
    // (`note: TRUST_JSON:...`) for Cargo's JSON stream. Count only the canonical
    // raw transport line so that one logical row is not mistaken for two.
    let rows: Vec<&str> = out
        .lines()
        .filter(|line| {
            line.starts_with("TRUST_JSON:") && line.contains("\"kind\":\"assumption:coroutine\"")
        })
        .collect();
    assert_eq!(
        rows.len(),
        1,
        "expected exactly one row for the async function's coroutine body:\n{out}"
    );
    for row in &rows {
        assert!(
            row.contains("\"function\":\"tick::tick::{closure#0}\""),
            "assumption row must identify the actual coroutine body: {row}"
        );
        assert!(
            row.contains("\"outcome\":\"skipped\""),
            "assumption row must carry outcome skipped: {row}"
        );
        assert!(
            row.contains("\"solver\":\"trust-classifier\""),
            "assumption row must identify the classifier boundary: {row}"
        );
        assert!(
            !row.contains("\"outcome\":\"proved\""),
            "assumption row must never claim proof: {row}"
        );
        let lower = row.to_lowercase();
        for banned in ["full-verifier", "full verifier", "fullverification::", "trust-verify-full"]
        {
            assert!(
                !lower.contains(banned),
                "assumption row must not match full-verifier text markers ({banned}): {row}"
            );
        }
    }
    assert!(
        !out.contains("UnmodeledSafetyAssert(ResumedAfter"),
        "coroutine executor-protocol sentinels must not become data-safety unknowns:\n{out}"
    );

    // A widening arithmetic operation is a real proved obligation in advisory
    // output, additive to exactly one conditional executor-protocol premise.
    // The same premise is visible but rejected by strict and memory-safe policy:
    // neither lane may synthesize no_obligations proof credit over a hidden
    // TrustIr Assume.
    rfs::write(
        "async_safe.rs",
        "#![crate_type=\"lib\"]\npub async fn widen(x: u8) -> u16 { (x as u16) + 1 }\n",
    );
    let advisory_safe = cmd(&trustc)
        .arg("--edition=2021")
        .arg("-Ztrust-policy=advisory")
        .arg("-Ztrust-verify-output=json")
        .arg("async_safe.rs")
        .arg("-o")
        .arg("libasync_safe_advisory.rlib")
        .run()
        .stderr_utf8();
    assert_exactly_one_transport_kind(&advisory_safe, "assumption:coroutine");
    assert_transport_outcome(
        &advisory_safe,
        "async_safe::widen::{closure#0}",
        "assumption:coroutine",
        "skipped",
    );
    assert_transport_outcome(
        &advisory_safe,
        "async_safe::widen::{closure#0}",
        "overflow:add",
        "proved",
    );

    let strict_safe = cmd(&trustc)
        .arg("--edition=2021")
        .arg("-Ztrust-verify-output=json")
        .arg("async_safe.rs")
        .arg("-o")
        .arg("libasync_safe.rlib")
        .run_fail()
        .stderr_utf8();
    assert_exactly_one_transport_kind(&strict_safe, "assumption:coroutine");
    assert_transport_outcome(
        &strict_safe,
        "async_safe::widen::{closure#0}",
        "overflow:add",
        "proved",
    );
    assert!(
        strict_safe.contains("coroutine executor-protocol premise is unproved"),
        "strict mode must reject the visible protocol premise:\n{strict_safe}"
    );
    assert!(
        !strict_safe.contains("UnmodeledSafetyAssert(ResumedAfter"),
        "strict async verification must classify the executor premise explicitly:\n{strict_safe}"
    );
    assert!(
        !strict_safe.lines().any(|line| line.starts_with("TRUST_JSON:")
            && line.contains("\"function\":\"async_safe::widen::{closure#0}\"")
            && line.contains("\"kind\":\"no_obligations\"")),
        "strict async verification must not mint no_obligations proof credit:\n{strict_safe}"
    );

    let memory_safe = cmd(&trustc)
        .arg("--edition=2021")
        .arg("-Ztrust-policy=memory-safe")
        .arg("-Ztrust-verify-output=json")
        .arg("async_safe.rs")
        .arg("-o")
        .arg("libasync_safe_memory_safe.rlib")
        .run_fail()
        .stderr_utf8();
    assert_exactly_one_transport_kind(&memory_safe, "assumption:coroutine");
    assert!(
        memory_safe.contains("Trust memory-safe verification failed")
            && memory_safe.contains("coroutine executor-protocol premise is unproved"),
        "memory-safe mode must reject the visible protocol premise:\n{memory_safe}"
    );

    // The overflow mutant must retain both independent facts: its real data
    // obligation is unproved — under the fail-closed refutation gate and the
    // effective-kind fallback it stays runtime-checked rather than becoming
    // proof credit or a bare failure — and its executor protocol is still an
    // assumption. Neither may be collapsed into or laundered by the other.
    rfs::write(
        "async_overflow.rs",
        "#![crate_type=\"lib\"]\npub async fn narrow(x: u8) -> u8 { x + 1 }\n",
    );
    let strict_mutant = cmd(&trustc)
        .arg("--edition=2021")
        .arg("-Ztrust-verify-output=json")
        .arg("async_overflow.rs")
        .arg("-o")
        .arg("libasync_overflow.rlib")
        .run_fail()
        .stderr_utf8();
    assert!(strict_mutant.contains("arithmetic overflow"), "{strict_mutant}");
    assert!(
        strict_mutant.contains("coroutine executor-protocol premise is unproved"),
        "the independent protocol premise must stay visible on a data refutation:\n{strict_mutant}"
    );
    assert_exactly_one_transport_kind(&strict_mutant, "assumption:coroutine");
    assert_transport_outcome(
        &strict_mutant,
        "async_overflow::narrow::{closure#0}",
        "overflow:add",
        "failed",
    );
    assert!(
        !strict_mutant.contains("UnmodeledSafetyAssert(ResumedAfter"),
        "the protocol premise must not masquerade as a data-safety VC:\n{strict_mutant}"
    );

    rfs::write(
        "user_skip.rs",
        "#![feature(register_tool)]\n#![register_tool(trust)]\n\
         #[trust::skip]\n#[inline(never)]\npub fn assumed_div<const AUDIT: u32>(x: i32, y: i32) -> i32 { let _ = AUDIT; x / y }\n\
         pub fn calls_assumed_div(x: i32, y: i32) -> i32 { assumed_div::<7>(x, y) }\n",
    );
    let nonfatal_skip = cmd(&trustc)
        .arg("--crate-type=lib")
        .arg("-Ztrust-policy=advisory")
        .arg("-Ztrust-verify-output=json")
        .arg("user_skip.rs")
        .arg("-o")
        .arg("libuser_skip.rlib")
        .run()
        .stderr_utf8();
    let skip_rows: Vec<&str> = nonfatal_skip
        .lines()
        .filter(|line| {
            line.starts_with("TRUST_JSON:") && line.contains("\"kind\":\"assumption:user-opt-out\"")
        })
        .collect();
    assert_eq!(
        skip_rows.len(),
        1,
        "nonfatal #[trust::skip] must emit one structured assumption row:\n{nonfatal_skip}"
    );
    assert!(
        skip_rows[0].contains("\"outcome\":\"skipped\""),
        "a user opt-out must never be reported as proved: {}",
        skip_rows[0]
    );
    let expected_absent_rows: Vec<&str> = nonfatal_skip
        .lines()
        .filter(|line| {
            line.starts_with("TRUST_JSON:")
                && line.contains("\"kind\":\"assumption:expected-absent-callee\"")
        })
        .collect();
    assert_eq!(
        expected_absent_rows.len(),
        1,
        "lame policy must publish the caller's expected-absent assumption exactly once:\n{nonfatal_skip}"
    );
    assert!(expected_absent_rows[0].contains("\"outcome\":\"skipped\""));

    let strict_skip = cmd(&trustc)
        .arg("--crate-type=lib")
        .arg("-Ztrust-verify-output=json")
        .arg("user_skip.rs")
        .arg("-o")
        .arg("libuser_skip_full.rlib")
        .run_fail()
        .stderr_utf8();
    assert!(
        strict_skip.contains("error: Trust full verification skipped `user_skip::assumed_div`"),
        "strict mode must reject the exact opted-out callee:\n{strict_skip}"
    );
    // Ratified drift (feat/panic-freedom-structural-subsumption, merge
    // b499bc60f33): whole-function panic-freedom now models the absent-callee
    // call as a panic-freedom ASSERTION (`"kind":"assert"`) whose panic path is
    // a runtime-checked trap, so the exact caller/callee edge surfaces as a
    // fail-closed `"outcome":"runtime_checked"` row instead of a bare Unknown.
    // Both remain strict build errors (see the `run_fail` above) and the
    // callee's panic is a controlled runtime trap rather than UB, so this is a
    // strictly more precise classification — NOT a fail-open. The fail-closed
    // guardrails are unchanged: exactly one row for the edge, and it is never
    // demoted into a conditional assumption row.
    let strict_caller_rows: Vec<&str> = strict_skip
        .lines()
        .filter(|line| {
            line.starts_with("TRUST_JSON:")
                && line.contains("\"function\":\"user_skip::calls_assumed_div\"")
                && line.contains("\"kind\":\"assert\"")
                && line.contains("\"outcome\":\"runtime_checked\"")
                && line.contains(
                    "[trust-expected-absent-callee-assumption] call to absent callee `user_skip::assumed_div::<7>`",
                )
        })
        .collect();
    assert_eq!(
        strict_caller_rows.len(),
        1,
        "strict mode must retain exactly one fail-closed runtime-checked row for the exact caller/callee edge:\n{strict_skip}"
    );
    assert!(
        !strict_skip.contains("\"kind\":\"assumption:expected-absent-callee\""),
        "strict mode must not demote the absent-callee fail-closed row into an assumption row:\n{strict_skip}"
    );

    // `assume_total` is an explicit, visible user-audited assumption. It keeps
    // strict green only by emitting a skipped ledger row; it never becomes a
    // proof or a silent omission.
    rfs::write(
        "inert_assume_total.rs",
        "#![feature(register_tool)]\n#![register_tool(trust)]\n\
         #[trust::assume_total]\npub fn mislabeled_div(x: i32, y: i32) -> i32 { x / y }\n",
    );
    cmd(&trustc)
        .arg("--crate-type=lib")
        .arg("-Ztrust-verify-output=json")
        .arg("inert_assume_total.rs")
        .arg("-o")
        .arg("libinert_assume_total.rlib")
        .run()
        .assert_stderr_contains("\"function\":\"inert_assume_total::mislabeled_div\"")
        .assert_stderr_contains("\"kind\":\"assumption:assumed-total\"")
        .assert_stderr_contains("\"outcome\":\"skipped\"");
}
