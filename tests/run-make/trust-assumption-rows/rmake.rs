// Trust (assumption ledger, Stage 1): the machine-readable transport contract
// for the coroutine executor-protocol premise. Compiling an async fn under the
// nonfatal lame policy with -Ztrust-policy=advisory -Ztrust-verify-output=json
// must emit a TRUST_JSON function_result row for the premise with outcome
// "skipped" — and that row must never claim proof or match the full-verifier
// text markers targo's report layer classifies on (is_full_verifier_text).
// Batteries-on raw compilation is strict; the vanilla replay wrapper
// (-Ztrust-verify=off) emits no TRUST_JSON.
//
// RETARGETED 2026-08-19 for LOCAL ca53846043 ("coroutine resume as a CHECKED
// caller contract"), whose own message records "NOT MEASURED: the end-to-end
// fixture flips — needs a stage2 rebuild + gate run". This file is invisible to
// the ui suite, so it went red unnoticed. THE RULING IS ACCEPTED, so the
// assertions are retargeted, never deleted:
//
//   * A CLEAN coroutine body's premise now publishes as
//     "contract:coroutine-resume-state" instead of "assumption:coroutine"
//     (`coroutine_protocol_publish_decision`,
//     compiler/rustc_mir_transform/src/trust_verify.rs:41276). It is still
//     outcome "skipped" from solver "trust-classifier" — never proof credit —
//     and every "must never claim proof" guard below is kept verbatim, just
//     re-keyed onto the new kind. The premise must still be exactly one row: if
//     it disappears entirely, `assert_exactly_one_transport_kind` fails.
//   * A clean coroutine DEFINITION therefore no longer aborts strict. That
//     assertion is not dropped, it is MOVED to the two places the fail-closed
//     behaviour actually lives now, both re-measured firing at this HEAD:
//       - the RESUME SITE (`resume_site.rs` below): an in-bundle direct call to
//         a contract-conditional coroutine body is charged a non-demotable
//         precondition (crates/trust-ir-bridge/src/lower.rs:28073), so strict
//         still fails the build. Pinned DIFFERENTIALLY against a twin that
//         builds the same future and takes the same unsafe block but does not
//         resume: 3 unproved obligations vs 2. Lose the charge and both read 2.
//       - the REFUTATION MUTANT (`async_overflow.rs` below): a coroutine whose
//         body carries a real refutation never satisfies the
//         rows_all_statically_proved condition, so it keeps the assumption arm
//         AND the verbatim "coroutine executor-protocol premise is unproved"
//         abort. That lane is UNCHANGED and is the retained pin on the original
//         abort text.
//   * The memory-safe lane still rejects the clean async fn (fail-closed
//     preserved), but with a different reason string; see there.
//
// KNOWN COVERAGE GAP, recorded rather than papered over: the caller-side charge
// is keyed on `ctx.known_function_signatures`, i.e. BUNDLE-LOCAL. `resume_site`
// below is the enforced case. A library that only EXPORTS an `async fn` has no
// enforced discharge site anywhere, and its summary reads "2 proved, 0 failed"
// where it used to read "1 obligation(s) were not proved". The contract row's
// own text still discloses the conditionality; the count does not.

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

fn count_transport_kind(output: &str, kind: &str) -> usize {
    let token = format!("\"kind\":\"{kind}\"");
    output
        .lines()
        .filter(|line| line.starts_with("TRUST_JSON:"))
        .map(|line| line.matches(&token).count())
        .sum::<usize>()
}

fn assert_exactly_one_transport_kind(output: &str, kind: &str) {
    let count = count_transport_kind(output, kind);
    assert_eq!(count, 1, "expected exactly one {kind} transport row:\n{output}");
}

/// The premise of a CLEAN coroutine body must publish as the proved-under-
/// precondition contract row and must NOT fall back to the assumption arm. Both
/// halves are asserted: a missing contract row and a resurrected assumption row
/// are different regressions and neither may pass silently.
fn assert_clean_coroutine_premise_row(output: &str, function: &str) {
    assert_exactly_one_transport_kind(output, "contract:coroutine-resume-state");
    assert_eq!(
        count_transport_kind(output, "assumption:coroutine"),
        0,
        "a clean coroutine body must not also publish the assumption arm:\n{output}"
    );
    assert_transport_outcome(output, function, "contract:coroutine-resume-state", "skipped");
    // Slice the premise row out of its function_result line. Scanning the whole
    // line would be wrong now that the sibling sentinel obligations PROVE and
    // carry kernel evidence blobs: the "never claims proof" and full-verifier
    // guards must see the premise row and nothing else.
    let kind_token = "\"kind\":\"contract:coroutine-resume-state\"";
    let line = output
        .lines()
        .find(|line| line.starts_with("TRUST_JSON:") && line.contains(kind_token))
        .unwrap_or_else(|| panic!("missing contract transport row:\n{output}"));
    assert!(
        line.contains(&format!("\"function\":\"{function}\"")),
        "contract row must identify the actual coroutine body: {line}"
    );
    let row_start = line.find(kind_token).expect("line was selected on this token");
    let row = &line[row_start..];
    let row = &row[..row.find("},{").map_or(row.len(), |end| end + 1)];
    assert!(
        row.contains("\"solver\":\"trust-classifier\""),
        "contract row must identify the classifier boundary: {row}"
    );
    // The contract is CONDITIONAL, so the row is never proof credit. Kept
    // verbatim from the assumption-row era: the kind moved, the guard did not.
    assert!(
        !row.contains("\"outcome\":\"proved\""),
        "the coroutine premise row must never claim proof: {row}"
    );
    let lower = row.to_lowercase();
    for banned in ["full-verifier", "full verifier", "fullverification::", "trust-verify-full"] {
        assert!(
            !lower.contains(banned),
            "the coroutine premise row must not match full-verifier text markers ({banned}): {row}"
        );
    }
    assert!(
        !output.contains("UnmodeledSafetyAssert(ResumedAfter"),
        "coroutine executor-protocol sentinels must not become data-safety unknowns:\n{output}"
    );
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
    assert_clean_coroutine_premise_row(&out, "tick::tick::{closure#0}");

    // A widening arithmetic operation is a real proved obligation in advisory
    // output, additive to exactly one conditional executor-protocol premise.
    // Strict now ACCEPTS this shape (the premise is a proved-under-precondition
    // contract, and the charge lands on callers — none here); memory-safe still
    // rejects it, because a skipped row is not an authenticated memory-safe
    // assumption. Neither lane may synthesize no_obligations proof credit over
    // a hidden TrustIr Assume.
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
    assert_clean_coroutine_premise_row(&advisory_safe, "async_safe::widen::{closure#0}");
    assert_transport_outcome(
        &advisory_safe,
        "async_safe::widen::{closure#0}",
        "overflow:add",
        "proved",
    );

    // RETARGETED: strict no longer aborts on the clean coroutine DEFINITION —
    // this lane is now `run()`. The row and its "never proof credit" guards are
    // unchanged, and the abort this lane used to pin is asserted at the two
    // places it now lives (`resume_site.rs` and `async_overflow.rs` below).
    let strict_safe = cmd(&trustc)
        .arg("--edition=2021")
        .arg("-Ztrust-verify-output=json")
        .arg("async_safe.rs")
        .arg("-o")
        .arg("libasync_safe.rlib")
        .run()
        .stderr_utf8();
    assert_clean_coroutine_premise_row(&strict_safe, "async_safe::widen::{closure#0}");
    assert_transport_outcome(
        &strict_safe,
        "async_safe::widen::{closure#0}",
        "overflow:add",
        "proved",
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

    // Memory-safe is STILL fail-closed on this shape, so this stays `run_fail`.
    // Only the reason string moved: a skipped contract row is not an
    // authenticated memory-safe assumption, which is the same refusal to launder
    // a conditional premise into proof credit that the old wording named.
    let memory_safe = cmd(&trustc)
        .arg("--edition=2021")
        .arg("-Ztrust-policy=memory-safe")
        .arg("-Ztrust-verify-output=json")
        .arg("async_safe.rs")
        .arg("-o")
        .arg("libasync_safe_memory_safe.rlib")
        .run_fail()
        .stderr_utf8();
    assert_clean_coroutine_premise_row(&memory_safe, "async_safe::widen::{closure#0}");
    assert!(
        memory_safe.contains(
            "Trust memory-safe verification failed for `async_safe::widen::{closure#0}`: at least \
             one result is not an authenticated memory-safe assumption"
        ),
        "memory-safe mode must reject the conditional protocol premise:\n{memory_safe}"
    );

    // THE CALLER-SIDE CHARGE, pinned differentially. `resumes` and
    // `does_not_resume` build the same future and take the same unsafe block;
    // only `resumes` polls the coroutine body, and only it is charged the
    // non-demotable COROUTINE_RESUME_PRECONDITION. Strict fails closed on both
    // (the shared unsafe rows), so the guard is the COUNT: lose the charge and
    // `resumes` reads 2 like its twin. `ManuallyDrop` is load-bearing — without
    // it the coroutine's drop-glue row merges into the same whole-function
    // panic-freedom aggregate and the two sides stop being distinguishable.
    rfs::write(
        "resume_site.rs",
        r#"#![crate_type="lib"]
use std::future::Future;
use std::mem::ManuallyDrop;
use std::pin::Pin;
use std::task::{Context, Poll, Waker};
pub async fn tick(x: u32) -> u32 { x }
pub fn resumes(x: u32) -> u32 {
    let mut fut = ManuallyDrop::new(tick(x));
    let pinned = unsafe { Pin::new_unchecked(&mut *fut) };
    let waker = Waker::noop();
    let mut cx = Context::from_waker(waker);
    match pinned.poll(&mut cx) { Poll::Ready(v) => v, Poll::Pending => 0 }
}
pub fn does_not_resume(x: u32) -> u32 {
    let mut fut = ManuallyDrop::new(tick(x));
    let pinned = unsafe { Pin::new_unchecked(&mut *fut) };
    let waker = Waker::noop();
    let cx = Context::from_waker(waker);
    let _ = (&pinned, &cx);
    x
}
"#,
    );
    let resume_site = cmd(&trustc)
        .arg("--edition=2021")
        .arg("-Ztrust-verify-output=json")
        .arg("resume_site.rs")
        .arg("-o")
        .arg("libresume_site.rlib")
        .run_fail()
        .stderr_utf8();
    assert_clean_coroutine_premise_row(&resume_site, "resume_site::tick::{closure#0}");
    assert!(
        resume_site.contains(
            "Trust strict verification failed for `resume_site::resumes`: 3 obligation(s) were \
             not fully verified"
        ),
        "the in-bundle resume site must carry one obligation more than its twin:\n{resume_site}"
    );
    assert!(
        resume_site.contains(
            "Trust strict verification failed for `resume_site::does_not_resume`: 2 obligation(s) \
             were not fully verified"
        ),
        "the non-resuming twin fixes the shared baseline this charge is measured against:\n\
         {resume_site}"
    );

    // The overflow mutant must retain both independent facts: its real data
    // obligation is unproved — under the fail-closed refutation gate and the
    // effective-kind fallback it stays runtime-checked rather than becoming
    // proof credit or a bare failure — and its executor protocol is still an
    // assumption. Neither may be collapsed into or laundered by the other.
    //
    // THIS LANE IS UNCHANGED BY ca53846043 and is deliberately kept verbatim: a
    // body carrying a real refutation never satisfies
    // `coroutine_protocol_publish_decision`'s rows_all_statically_proved
    // condition, so it keeps the assumption arm AND the original
    // "coroutine executor-protocol premise is unproved" abort. Re-measured
    // firing at this HEAD; it is the retained pin on that exact text.
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
