// Trust (assumption ledger, Stage 1): the machine-readable transport contract
// for the coroutine executor-protocol premise. Compiling an async fn under the
// nonfatal lame policy with -Ztrust-policy=advisory -Ztrust-verify-output=json
// must emit a TRUST_JSON function_result row for the premise with outcome
// "skipped" — and that row must never claim proof or match the full-verifier
// text markers targo's report layer classifies on (is_full_verifier_text).
// Batteries-on raw compilation is strict; the vanilla replay wrapper
// (-Ztrust-verify=off) emits no TRUST_JSON.
//
// RETARGETED 2026-09-13 onto D2 (0e9090f03b, 2026-08-20, "close a live false
// PROVE at the Certified tier — coroutine resume premise"), measured on the
// driver at HEAD. History, because this file has now been retargeted twice in
// opposite directions and a reader deserves to know which ruling is live:
//
//   * ca53846043 (2026-08-19) published a CLEAN coroutine body's premise as a
//     `contract:coroutine-resume-state` row and let strict ACCEPT the
//     definition, charging callers instead. ec6fdaa877 re-pinned this recipe
//     onto that ruling.
//   * D2 REVERSED it the next day, with an end-to-end exhibit: the entry
//     `Assume(resume_state == 0)` dominates every block, so the panic-freedom
//     row certified under it was an ex-falso proof — and NO caller-side
//     discharge lane exists (the ca53846043 charge fires only on an in-bundle
//     direct `Call` to the body; the real resumer is the generated
//     `Future::poll` shim, measured uncharged in-crate AND cross-crate). D2
//     therefore (A) makes `PublishContractRow` unreachable under strict /
//     memory-safe, restoring the abort, and (B) STAMPS every row that consumed
//     the premise: `kind` gains the `contract-conditional:coroutine-resume-state:`
//     prefix, `outcome` drops to `skipped`, the Certified grade is stripped.
//     The premise itself publishes as `assumption:coroutine` again (the
//     contract upgrade also requires "no unmarked conditional proof", which no
//     body whose non-sentinel obligations discharge can satisfy — measured:
//     every fixture here publishes the assumption arm in every lane).
//   * D2 re-pinned the five `tests/ui/trust/assumption-rows/*` fixtures and
//     NOT this recipe, and run-make could not execute on a verifying driver
//     until 8bafdcc5e5, so the ca53846043 expectations sat here unmeasured for
//     three weeks. Every "must never claim proof" guard below is kept; the
//     kind it is keyed on moves back, and the strict abort this file used to
//     pin at the DEFINITION is pinned there again.
//
// COVERAGE GAP, disclosed rather than papered over (D2's own finding, and the
// `resume_site.rs` lane below keeps it measured): a hand-rolled in-crate
// executor polling the coroutine through `<… as Future>::poll` is charged NO
// resume-state precondition — the poll edge surfaces only as a fail-closed
// runtime-checked absent-callee row, and the resumer reports exactly as many
// unproved obligations as a twin that never resumes. If that differential ever
// reopens, a caller-side discharge lane has landed: re-pin it POSITIVELY.

use std::path::PathBuf;

use run_make_support::{bin_name, cmd, rfs, rustc_path};

const TRUST_VANILLA_REAL_RUSTC_ENV: &str = "__COMPILETEST_TRUST_VANILLA_REAL_RUSTC";

/// D2 part B's stamp: the prefix every row that consumed the entry `Assume`
/// now carries (the original kind survives after it).
const CONDITIONAL_PREFIX: &str = "contract-conditional:coroutine-resume-state:";

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

/// The `N` in the compiler's per-function "N obligation(s) were not proved"
/// line for `function`, or `None` if the function was reported clean (or not
/// reported at all).
fn unproved_count(output: &str, function: &str) -> Option<usize> {
    let marker = format!("verification incomplete for `{function}`: ");
    let line = output.lines().find(|line| line.contains(&marker))?;
    let rest = &line[line.find(&marker)? + marker.len()..];
    rest.split_whitespace().next()?.parse().ok()
}

/// The premise of a CLEAN coroutine body publishes as the `assumption:coroutine`
/// ledger row — never as proof credit, never as the retired ca53846043 contract
/// row — and every sibling obligation discharged under the entry `Assume` is
/// STAMPED conditional. All halves are asserted: a missing assumption row, a
/// resurrected contract row, an unstamped conditional proof and a stamped row
/// claiming proof are four different regressions and none may pass silently.
fn assert_clean_coroutine_premise_row(output: &str, function: &str) {
    assert_exactly_one_transport_kind(output, "assumption:coroutine");
    assert_eq!(
        count_transport_kind(output, "contract:coroutine-resume-state"),
        0,
        "D2 part A: the ca53846043 contract row must not be published for a body whose \
         premise no caller is obliged to discharge:\n{output}"
    );
    assert_transport_outcome(output, function, "assumption:coroutine", "skipped");
    // Slice the premise row out of its function_result line. Scanning the whole
    // line would be wrong: the sibling sentinel obligations PROVE and carry
    // kernel evidence blobs, and the stamped conditional rows legitimately name
    // the full verifier as their solver. The "never claims proof" and
    // full-verifier guards must see the premise row and nothing else.
    let kind_token = "\"kind\":\"assumption:coroutine\"";
    let line = output
        .lines()
        .find(|line| line.starts_with("TRUST_JSON:") && line.contains(kind_token))
        .unwrap_or_else(|| panic!("missing assumption transport row:\n{output}"));
    assert!(
        line.contains(&format!("\"function\":\"{function}\"")),
        "assumption row must identify the actual coroutine body: {line}"
    );
    let row_start = line.find(kind_token).expect("line was selected on this token");
    let row = &line[row_start..];
    let row = &row[..row.find("},{").map_or(row.len(), |end| end + 1)];
    assert!(
        row.contains("\"solver\":\"trust-classifier\""),
        "assumption row must identify the classifier boundary: {row}"
    );
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
    // D2 part B: the entry `Assume` dominates every block, so every obligation
    // discharged in the body is conditional — and it must SAY so on the row.
    // At least one stamped row exists (the whole-function panic-freedom
    // aggregate at minimum), every stamped row is `skipped`, and none claims
    // `proved`: a stamped row reporting proof would be the exhibit's leak back
    // through a different lane.
    let stamped_token = format!("\"kind\":\"{CONDITIONAL_PREFIX}");
    let mut stamped = 0usize;
    for (at, _) in line.match_indices(&stamped_token) {
        stamped += 1;
        let rest = &line[at..];
        let outcome = rest
            .find("\"outcome\":\"")
            .map(|o| &rest[o + "\"outcome\":\"".len()..])
            .and_then(|tail| tail.split('"').next())
            .unwrap_or("<none>");
        assert_eq!(
            outcome, "skipped",
            "a row stamped conditional on the executor premise must be skipped, not {outcome}:\n\
             {}",
            &rest[..rest.len().min(400)]
        );
        assert!(
            rest[..rest.len().min(2000)].contains("NOT an unconditional proof"),
            "a stamped row must disclose its conditionality in its reason:\n{}",
            &rest[..rest.len().min(400)]
        );
    }
    assert!(stamped >= 1, "a contract-engaged coroutine body must carry stamped rows:\n{line}");
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

    // A widening arithmetic operation is a real data obligation, and under D2
    // it is discharged CONDITIONALLY: the row is stamped
    // `contract-conditional:coroutine-resume-state:overflow:add`, outcome
    // `skipped`, and NO bare `overflow:add` row claims unconditional proof
    // credit. Strict and memory-safe both reject the definition (the premise
    // is unproved and no caller is obliged to discharge it); neither lane may
    // synthesize no_obligations proof credit over the hidden TrustIr Assume.
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
        "contract-conditional:coroutine-resume-state:overflow:add",
        "skipped",
    );
    assert_eq!(
        count_transport_kind(&advisory_safe, "overflow:add"),
        0,
        "the data obligation under the entry Assume must not surface as an unconditional \
         overflow:add row:\n{advisory_safe}"
    );

    // D2 part A: strict aborts on the clean coroutine DEFINITION again. The row
    // and its "never proof credit" guards are unchanged; the abort text is the
    // original one, and it names the premise, not a data obligation.
    let strict_safe = cmd(&trustc)
        .arg("--edition=2021")
        .arg("-Ztrust-verify-output=json")
        .arg("async_safe.rs")
        .arg("-o")
        .arg("libasync_safe.rlib")
        .run_fail()
        .stderr_utf8();
    assert_clean_coroutine_premise_row(&strict_safe, "async_safe::widen::{closure#0}");
    assert!(
        strict_safe.contains(
            "Trust strict verification failed for `async_safe::widen::{closure#0}`: coroutine \
             executor-protocol premise is unproved"
        ),
        "strict must fail closed on the undischargeable premise at the definition:\n{strict_safe}"
    );
    assert!(
        strict_safe.contains("strict and memory-safe policy accept no unproved in-scope premise"),
        "the strict refusal must name the advisory lane as the way to retain the evidence:\n\
         {strict_safe}"
    );
    assert_transport_outcome(
        &strict_safe,
        "async_safe::widen::{closure#0}",
        "contract-conditional:coroutine-resume-state:overflow:add",
        "skipped",
    );
    assert_eq!(count_transport_kind(&strict_safe, "overflow:add"), 0, "{strict_safe}");
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

    // Memory-safe is fail-closed on the same premise, with its own reason: the
    // compiler-generated executor premise is not a memory-safe assumption the
    // policy admits.
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
            "Trust memory-safe verification failed for `async_safe::widen::{closure#0}`: \
             coroutine executor-protocol premise is unproved"
        ),
        "memory-safe mode must reject the conditional protocol premise:\n{memory_safe}"
    );
    assert!(
        memory_safe.contains(
            "memory-safe policy does not admit the compiler-generated \
             ResumedAfterReturn/Panic/Drop executor premise"
        ),
        "the memory-safe refusal must name the premise it declines to admit:\n{memory_safe}"
    );

    // THE RESUME SITE. `resumes` and `does_not_resume` build the same future and
    // take the same unsafe block; only `resumes` polls the coroutine body. Under
    // strict the definition's premise abort fires first (pinned). Under
    // advisory — the lane where both callers are actually reported — the poll
    // goes through the generated `<… as Future>::poll` shim, which is NOT an
    // in-bundle direct `Call` to the body, so the ca53846043 caller-side charge
    // (`[trust-coroutine-resume-precondition]`) does NOT fire: D2's measured
    // finding, disclosed here rather than hidden. What the resumer DOES carry is
    // a fail-closed runtime-checked absent-callee row for exactly that poll
    // edge — the resume site is never reported clean — and it reports no more
    // unproved obligations than its non-resuming twin. That equality IS the
    // coverage gap; a lane that closes it will reopen the differential and must
    // re-pin this block positively.
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
            "Trust strict verification failed for `resume_site::tick::{closure#0}`: coroutine \
             executor-protocol premise is unproved"
        ),
        "strict must refuse the coroutine definition the in-crate executor resumes:\n{resume_site}"
    );
    let resume_site_advisory = cmd(&trustc)
        .arg("--edition=2021")
        .arg("-Ztrust-policy=advisory")
        .arg("-Ztrust-verify-output=json")
        .arg("resume_site.rs")
        .arg("-o")
        .arg("libresume_site_advisory.rlib")
        .run()
        .stderr_utf8();
    assert_clean_coroutine_premise_row(&resume_site_advisory, "resume_site::tick::{closure#0}");
    let poll_edge_rows = resume_site_advisory
        .lines()
        .filter(|line| {
            line.starts_with("TRUST_JSON:")
                && line.contains("\"function\":\"resume_site::resumes\"")
                && line.contains("\"kind\":\"assert\"")
                && line.contains("\"outcome\":\"runtime_checked\"")
                && line.contains(
                    "[trust-absent-callee-assumption] call to absent callee `<{async fn body of \
                     resume_site::tick()} as core::future::future::Future>::poll`",
                )
        })
        .count();
    assert_eq!(
        poll_edge_rows, 1,
        "the resumer's poll edge must surface as exactly one fail-closed runtime-checked \
         absent-callee row:\n{resume_site_advisory}"
    );
    assert!(
        !resume_site_advisory.contains("[trust-coroutine-resume-precondition]"),
        "a caller-side resume-state charge has landed — re-pin this lane POSITIVELY instead of \
         letting the coverage-gap disclosure below rot:\n{resume_site_advisory}"
    );
    let resumes = unproved_count(&resume_site_advisory, "resume_site::resumes");
    let twin = unproved_count(&resume_site_advisory, "resume_site::does_not_resume");
    assert!(
        resumes.is_some_and(|n| n >= 1) && twin.is_some_and(|n| n >= 1),
        "neither twin may be reported clean (resumes={resumes:?}, twin={twin:?}):\n\
         {resume_site_advisory}"
    );
    assert_eq!(
        resumes, twin,
        "the resume site is charged nothing its non-resuming twin is not (D2's disclosed gap); \
         a reopened differential means a caller-side charge landed — pin it:\n{resume_site_advisory}"
    );

    // The overflow mutant must retain both independent facts: its real data
    // obligation is unproved — under the fail-closed refutation gate and the
    // effective-kind fallback it stays runtime-checked rather than becoming
    // proof credit or a bare failure — and its executor protocol is still an
    // assumption. Neither may be collapsed into or laundered by the other.
    // A row carrying a real refutation is never stamped conditional: the bare
    // `overflow:add` row reports `failed`, and the premise abort text is the
    // original one. Unchanged across ca53846043 and D2; measured at HEAD.
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
    // Trust (skip taxonomy, RECORD-THEN-RULE): strict still REFUSES the opt-out
    // (the error above, and `run_fail`), but it now also records the premise
    // it refused, so the largest error class of a strict run is enumerable from
    // the transport. The row is `skipped`, never proof, and it is not a shape
    // targo's strict lane admits as conditional evidence
    // (`strict_policy_publishes_assumption_row`).
    let strict_skip_rows: Vec<&str> = strict_skip
        .lines()
        .filter(|line| {
            line.starts_with("TRUST_JSON:")
                && line.contains("\"kind\":\"assumption:user-opt-out\"")
        })
        .collect();
    assert_eq!(
        strict_skip_rows.len(),
        1,
        "strict must record the refused #[trust::skip] as exactly one assumption row:\n{strict_skip}"
    );
    assert!(
        strict_skip_rows[0].contains("\"outcome\":\"skipped\""),
        "a refused user opt-out must never be reported as proved: {}",
        strict_skip_rows[0]
    );
    assert!(
        strict_skip.contains("this skip is also recorded as an `assumption:user-opt-out` transport row"),
        "the strict error must state the row it recorded:\n{strict_skip}"
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
