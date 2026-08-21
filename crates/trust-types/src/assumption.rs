//! Trust (assumption ledger): shared markers for the compiler↔bridge assumption
//! demotion contract. When the TrustIr bridge cannot statically verify a call's
//! panic-freedom because it dispatches arbitrary USER code (a `Display`/`Debug`
//! impl driven by `println!`/`format!`/`write!`), it models the call as an opaque
//! result plus one honest `PanicFreedom` obligation, and marks that obligation so
//! the explicit memory-safe lane can demote it to a recorded
//! `assumption:extern-call` ledger row (never a proof) instead of hard-aborting.
//! Survey may report assumptions nonfatally, but does not receive the
//! memory-safe source label. Batteries-on strict policy never demotes unless
//! the tracked memory-safe exception applies to a function with no unsafe code.
//!
//! This lives in `trust-types` — the shared dependency of `trust-ir-bridge` (the
//! producer of the marker) and the compiler's verify pass (the consumer that
//! demotes) — so the two ends of the contract cannot drift apart.
//!
//! SOUNDNESS: the marker string must NEVER contain the full-verifier classifier
//! text (`native full verifier`, `full verifier`, `full-verifier`,
//! `trust-verify-full`, `fullverification::`); targo's `is_full_verifier_text`
//! would otherwise misclassify a demoted row as full-verifier evidence. The prefix
//! below is deliberately marker-free.

/// Prefix stamped on a bridge `PanicFreedom` obligation raised for an EXTERN
/// PRINT/FORMAT/WRITE DISPATCH call (`_print`/`_eprint`/`fmt::format`/`write_fmt`/
/// `fmt::write`). Such a call runs a user `Display`/`Debug::fmt` impl (arbitrary
/// code that CAN panic, and whose stdout leg can hit a broken pipe / SIGPIPE), so
/// it is NEVER classified total/no-panic. The compiler's verify pass recognizes
/// this prefix on the reconstructed obligation's description and, under the
/// explicit memory-safe policy for a no-unsafe function, demotes the resulting
/// UNKNOWN panic-freedom row to a recorded `assumption:extern-call` entry.
/// Marker-free by construction (see module doc).
pub const EXTERN_CALL_ASSUMPTION_PREFIX: &str = "[trust-extern-call-assumption] ";

/// The stable machine-readable tag for an extern print/format/write dispatch
/// assumption row (`assumption:extern-call`).
pub const EXTERN_CALL_ASSUMPTION_TAG: &str = "extern-call";

/// Prefix stamped on a bridge `PanicFreedom` obligation raised for a call whose
/// TARGET FUNCTION BODY is absent from the lowered TrustIr bundle (a std/extern
/// callee outside the local-callee closure, or a callee dropped by the
/// fail-soft bundler). The call is modeled exactly like the extern dispatch:
/// `Assert(false)+NoPanic` in-body marker (the panic stays visible to the CHC
/// interpreter on every path through the call site), havoc result, one honest
/// `PanicFreedom` obligation that stays UNKNOWN in the strict lane. The explicit
/// memory-safe lane may demote it to a recorded `assumption:absent-callee` ledger
/// row — never a proof. Marker-free by construction (see module doc).
pub const ABSENT_CALLEE_ASSUMPTION_PREFIX: &str = "[trust-absent-callee-assumption] ";

/// The stable machine-readable tag for an absent-callee assumption row
/// (`assumption:absent-callee`).
pub const ABSENT_CALLEE_ASSUMPTION_TAG: &str = "absent-callee";

/// Prefix for an EXPECTED-absent callee: a target explicitly classified by
/// either a user `#[trust::skip]` or a compiler-authenticated non-unwinding C
/// ABI. Generic unresolved dispatch is deliberately excluded. Advisory
/// survey reporting may rewrite the row to
/// `assumption:expected-absent-callee`; strict and memory-safe policies reject
/// it. The row is never proof and makes no claim that a concrete implementation
/// was separately verified. Marker-free by construction, and not a substring
/// of `ABSENT_CALLEE_ASSUMPTION_PREFIX` (the mutual-non-substring invariant —
/// "expected-" splits the shared stem).
///
/// Trust: completes origin commit 41d8e71340's P0 fail-open fix — trust_verify.rs
/// (the consumer, `transport_row_is_unproved_expected_absent_callee`) and
/// `collect_expected_absent_callees` (the set producer) were committed referencing
/// these two constants + the `lower_to_trust_ir_functions_with_expected_absent`
/// producer, but the definitions were never landed, breaking every clean stage2
/// build. Values are fully determined by the consumer's `.contains(...)` checks.
pub const EXPECTED_ABSENT_CALLEE_ASSUMPTION_PREFIX: &str =
    "[trust-expected-absent-callee-assumption] ";

/// The stable machine-readable tag for an expected-absent-callee assumption row
/// (`assumption:expected-absent-callee`).
pub const EXPECTED_ABSENT_CALLEE_ASSUMPTION_TAG: &str = "expected-absent-callee";

/// Prefix for an ASSUMED-TOTAL callee: a target explicitly marked with the
/// user-audited `#[trust::assume_total]` attribute. Unlike `#[trust::skip]`,
/// this row is recorded non-fatally in every mode, but never receives proof
/// credit. The spelling is mutually non-substring with both absent-callee
/// marker classes.
pub const ASSUMED_TOTAL_CALLEE_ASSUMPTION_PREFIX: &str = "[trust-assumed-total-callee-assumption]";

/// Stable machine-readable tag for `assumption:assumed-total-callee`.
pub const ASSUMED_TOTAL_CALLEE_ASSUMPTION_TAG: &str = "assumed-total-callee";

/// Prefix stamped on a bridge `PanicFreedom` obligation raised for a DROP whose
/// glue's panic-freedom is unproven (a user `Drop` impl, or a std container the
/// panic-free-drop classifier does not recognize). MIR guarantees the dropped
/// value is dead afterward — the ONLY verification-relevant effect is that the
/// glue may PANIC — so the drop lowers like an absent callee: in-body
/// `Assert(false)+NoPanic` marker + one honest `PanicFreedom` obligation. The
/// strict policy keeps it Unknown; the explicit memory-safe lane may demote it
/// to a recorded `assumption:drop-glue` ledger row. Marker-free by construction.
pub const DROP_GLUE_ASSUMPTION_PREFIX: &str = "[trust-drop-glue-assumption] ";

/// The stable machine-readable tag for a drop-glue assumption row
/// (`assumption:drop-glue`).
pub const DROP_GLUE_ASSUMPTION_TAG: &str = "drop-glue";

/// The stable machine-readable tag for a native-TrustIr lowering-gap assumption
/// row (`assumption:native-lowering`) — the compiler backstop for a function the
/// bridge could not lower at all.
pub const NATIVE_LOWERING_ASSUMPTION_TAG: &str = "native-lowering";

/// Compiler-authenticated source label stamped on an assumption row only when
/// `-Z trust-policy=memory-safe` demoted a capability gap in a function proven
/// to contain neither source nor inlined `unsafe` code. Consumers may use this
/// stable label to distinguish that narrow policy exception from assumptions
/// admitted by survey mode or from unconditional boundary assumptions.
///
/// This is a row source, not proof credit: the outcome remains `skipped` and the
/// enclosing compiler transport/envelope must still be authenticated normally.
pub const MEMORY_SAFE_ASSUMPTION_ROW_SOURCE: &str = "trust-memory-safe";

/// Stable row tag for a reachable Rust panic that the explicit memory-safe
/// policy conditionally admits in a function with neither source nor inlined
/// `unsafe` code. The complete wire kind is
/// `assumption:memory-safe-panic`; it remains unproved and must carry
/// [`MEMORY_SAFE_ASSUMPTION_ROW_SOURCE`].
pub const MEMORY_SAFE_PANIC_ASSUMPTION_TAG: &str = "memory-safe-panic";

// ---------------------------------------------------------------------------
// Trust (T9 contract-panic): the vcgen↔compiler↔targo contract-panic contract.
// trust-vcgen (the producer) stamps a marker into a panic-call Assertion VC's
// message when the enclosing fn's `#[trust(contract_panic(message_contains =
// "..."))]` payload is a substring of the panic call's const-str message; the
// compiler's verify pass (the consumer) may rewrite the resulting FAILED row's
// kind to `contract-panic:` only for advisory survey reporting; targo
// partitions those rows into an always-visible `contract_panics` bucket that
// may CONDITIONALLY pass there (never bare-pass, never proof credit). Strict
// fails the obligation, and memory-safe excludes it from safe-panic demotion.
// Shared here so the three ends cannot drift. Same marker-free doctrine as the
// assumption prefixes above.
// ---------------------------------------------------------------------------

/// Marker stamped by trust-vcgen INTO a panic-call `Assertion` VC message when
/// the enclosing function carries a `contract_panic` annotation whose
/// `message_contains` payload matched a const-str operand of THAT panic call
/// (site + message match happen at mint time; marker presence == matched).
/// The VC is still solved normally — the marker never changes a verdict, only
/// how the compiler's verify pass CLASSIFIES a resulting FAILED row.
pub const CONTRACT_PANIC_VC_MARKER: &str = "[trust-contract-panic] ";

/// Marker stamped by trust-vcgen into the always-refuted `Assertion` VC minted
/// when a `contract_panic` annotation matched NO panic call in the function —
/// an annotation on panic-free code is an ERROR (anti-abuse: an annotation can
/// never sit dormant waiting to mask a future panic).
pub const CONTRACT_PANIC_UNUSED_VC_MARKER: &str = "[trust-contract-panic-unused] ";

/// Row-kind prefix for a rewritten contract-panic row (advisory survey only).
/// targo's partition counts `kind.starts_with(this)` into the visible
/// `contract_panics` bucket, fail-closed: such a row claiming Proved /
/// RuntimeChecked is a transport defect counted as a genuine unknown.
pub const CONTRACT_PANIC_ROW_KIND_PREFIX: &str = "contract-panic:";

/// The row kind for a MESSAGE-MATCHED panic CALL refutation.
pub const CONTRACT_PANIC_MATCHED_ROW_KIND: &str = "contract-panic:matched";

/// Row kind for the WHOLE-FUNCTION panic-freedom AGGREGATE obligation once it is
/// established to be covered entirely by declared, message-matched contract
/// panics. The native trust-mc lane cannot lower the function-level
/// `assertion:panic-freedom` aggregate to a typed CHC (it carries a
/// router-placeholder input and defers to a path-sensitive transport that does
/// not model diverging-`Call` panics), so it returns UNKNOWN even when every
/// reachable panic in the function is a declared contract panic. This kind is
/// applied by the compiler's verify pass ONLY when (a) the function has ≥1
/// [`CONTRACT_PANIC_MATCHED_ROW_KIND`] row AND (b) it has NO blocking failure (no
/// `failed` row whose kind is not itself `contract-panic:`), so every reachable
/// panic is provably declared — any UNdeclared panic keeps its OWN failing
/// per-site obligation, which blocks (b). Starts with
/// [`CONTRACT_PANIC_ROW_KIND_PREFIX`] so targo buckets it as a visible
/// conditional pass, never proof credit; strict verification never applies it
/// (the aggregate stays UNKNOWN and fails closed there).
pub const CONTRACT_PANIC_AGGREGATE_ROW_KIND: &str = "contract-panic:aggregate-covered";

/// Stable leading substring of the compiler's canonical whole-function
/// panic-freedom aggregate DESCRIPTION. Used to recognize the UN-enriched
/// aggregate row: when an extern-call / absent-callee / drop-glue gap folds into
/// the aggregate, its description is REPLACED by that gap's text (which does not
/// contain this substring), so matching it excludes those unmodeled-panic gaps
/// from the [`CONTRACT_PANIC_AGGREGATE_ROW_KIND`] reclassification.
pub const PANIC_FREEDOM_AGGREGATE_DESCRIPTION_PREFIX: &str =
    "panic freedom: no assertion, `unreachable!`, or panic is reachable";

/// Row kind for the unused-annotation FAILED row. Deliberately does NOT start
/// with [`CONTRACT_PANIC_ROW_KIND_PREFIX`] (dash, not colon), so targo counts
/// it as a genuine FAILURE — an unused annotation can never conditional-pass.
pub const CONTRACT_PANIC_UNUSED_ROW_KIND: &str = "contract-panic-unused";

/// The `solver`/source stamped on a rewritten contract-panic row.
pub const CONTRACT_PANIC_ROW_SOURCE: &str = "trust-contract";

/// Marker prefix the compiler stamps on a contract predicate it could not
/// lower to a supported spec expression (`unsupported contract predicate
/// expression \`<text>\``). Serialized fail-closed consumers may recognize it
/// to preserve the original diagnostic instead of re-parsing the quoted text.
/// The string is diagnostic provenance only and must never grant proof or
/// compiler-origin authority to an authored opaque body that contains it.
pub const UNSUPPORTED_COMPILER_CONTRACT_PREFIX: &str = "__trust_unsupported_compiler_contract__:";

// ---------------------------------------------------------------------------
// Trust (coroutine resume-state contract): the bridge↔compiler↔targo contract
// for the async/coroutine executor-protocol lane. rustc lowers an `async fn`
// body to a coroutine whose resume ENTRY dispatches on the frame's resume-state
// discriminant, with three compiler-inserted `assert(false, ResumedAfter*)`
// protocol sentinels for the completed/poisoned/dropped states. The executor
// premise ("never resume a completed coroutine") is a genuine CALLER-side
// precondition (Rust's documented `Future::poll` contract), so it can never be
// proved unconditionally. The bridge instead publishes it as a first-class
// CONTRACT: it constrains the entry dispatch read to the LIVE resume states —
// the dispatch `SwitchInt`'s own case set (whose `otherwise -> Unreachable`
// arm is rustc's exhaustiveness certificate) MINUS the reserved RETURNED=1 /
// POISONED=2 ABI discriminants — and re-emits the sentinels as ordinary
// REFUTABLE asserts the solver must prove unreachable under that precondition.
// A wrong live-state set therefore makes the sentinel proof FAIL, never
// silently pass. trust-ir-bridge (producer) stamps the markers below onto the
// sentinel obligations; the compiler's verify pass (consumer) may publish the
// `contract:coroutine-resume-state` row ONLY from the bridge module's
// authenticated evidence plus fully-proved rows; targo classifies the row as
// exported-contract conditional evidence — never proof credit. Shared here so
// the three ends cannot drift. Same marker-free doctrine as the assumption
// prefixes above.
// ---------------------------------------------------------------------------

/// Prefix stamped by the trust-ir bridge on the `PanicFreedom` obligation of a
/// compiler-inserted `ResumedAfter{Return,Panic,Drop}` sentinel that was lowered
/// as a REFUTABLE assert under the coroutine resume-state entry contract
/// (instead of the fail-closed path-scoped `Assume(false)` pruning used when no
/// contract applies). The full description is produced ONLY by
/// [`coroutine_resume_contract_obligation_description`] and consumed ONLY by
/// [`parse_coroutine_resume_contract_obligation_description`], so producer and
/// consumer cannot drift. This marker can appear only on obligations minted
/// from compiler-generated `Terminator::Assert` messages (never user strings),
/// which is what makes it an authenticated channel. Marker-free by
/// construction (see module doc).
pub const COROUTINE_RESUME_CONTRACT_OBLIGATION_PREFIX: &str =
    "[trust-coroutine-resume-state-contract] ";

/// Prefix stamped by the trust-ir bridge on the CALLER-side `PanicFreedom`
/// obligation minted at every in-bundle direct call whose callee is a
/// contract-conditional coroutine resume body (the poll/resume site). WIRED
/// via the audited absent-callee may-panic encoding — in-body `Assert(false)`
/// marker + this marked obligation + the whole-function counted carrier — the
/// only bridge encoding that verifiably reaches a published row (a bare
/// bridge-private obligation is cleared at the public-bundle boundary and
/// surfaces nowhere). No discharge lane exists yet and this prefix is in NO
/// demotion allowlist, so the caller's aggregate stays honestly UNPROVED in
/// every lane and a crate that polls its own coroutine fails closed — an
/// executor that polls after completion can never verify clean on the
/// strength of the callee's exported contract alone. Marker-free by
/// construction, and mutually non-substring with the sentinel marker above
/// ("-precondition]" vs "-state-contract]").
pub const COROUTINE_RESUME_PRECONDITION_PREFIX: &str = "[trust-coroutine-resume-precondition] ";

/// Row kind for the compiler-published coroutine resume-state contract row.
/// Deliberately NOT `assumption:*`: the sentinels were genuinely solver-proved
/// under the exported precondition (verified-modulo-callers, exactly like a
/// `#[trust::requires]` definition-entry row), not skipped as a capability gap.
/// The row still carries `Outcome::Skipped` on the wire — it is a published
/// contract, never solver proof credit.
pub const COROUTINE_RESUME_CONTRACT_ROW_KIND: &str = "contract:coroutine-resume-state";

/// The `solver` label stamped on the published contract row.
pub const COROUTINE_RESUME_CONTRACT_ROW_SOLVER: &str = "trust-classifier";

/// Exact `reason` stamped on the published contract row. Consumers (targo's
/// partition) require this exact string as part of the row-shape check, so a
/// hand-built row that merely claims the kind cannot green.
pub const COROUTINE_RESUME_CONTRACT_ROW_REASON: &str =
    "proved-under-exported-precondition: every compiler-inserted ResumedAfterReturn/Panic/Drop \
     sentinel was discharged by the solver under the coroutine resume-state entry contract; \
     the crate's proof remains conditional on every caller establishing the resume state";

/// Kind PREFIX stamped on a row whose violation formula CONSUMED the bridge's
/// entry resume-state `Assume` without being one of the bridge-marked sentinel
/// rows that the contract exists to describe.
///
/// WHY THIS EXISTS (the D2 false-PROVE). The bridge injects
/// `Assume(resume_state ∈ live_states)` at the coroutine body's ENTRY, and entry
/// DOMINATES every block — so every obligation discharged in that body is
/// conditional on the executor-protocol premise, not just the sentinels. The
/// sentinel rows say so in their description (they carry
/// [`COROUTINE_RESUME_CONTRACT_OBLIGATION_PREFIX`]); the whole-function
/// panic-freedom AGGREGATE did not, and shipped as bare
/// `proved` / `Certified` / `KernelRechecked` / `axiom_closure: Empty` with a
/// CIC term BYTE-IDENTICAL to the sentinel row's — an ex-falso derivation from
/// `resume_state = 0 ∧ resume_state = 1`. The conditionality lived only on a
/// SIBLING `contract:coroutine-resume-state` row with `outcome: skipped`, so
/// nothing linked the aggregate to the premise it had silently consumed.
///
/// The marker therefore belongs on the ROW THAT CONSUMED THE ASSUME. A row
/// carrying this prefix is conditional evidence exactly like the assumption
/// ledger and shares targo's `assumed` bucket; it may never carry
/// `Outcome::Proved` (the producer strips the proof evidence when it stamps
/// this, and targo counts a proved-claiming row as a genuine unknown defect).
pub const COROUTINE_RESUME_CONDITIONAL_ROW_KIND_PREFIX: &str =
    "contract-conditional:coroutine-resume-state:";

/// Exact `reason` stamped on a contract-conditional row, naming the premise the
/// row's formula consumed. Consumers require this exact string as part of the
/// fail-closed row-shape check.
pub const COROUTINE_RESUME_CONDITIONAL_ROW_REASON: &str =
    "conditional-on-exported-precondition: this obligation was discharged under the coroutine \
     resume-state entry assumption injected at function entry, which dominates every block; the \
     result is conditional on every caller establishing the resume state and is NOT an \
     unconditional proof";

/// Stamp `kind` as contract-conditional, preserving the original kind after the
/// prefix so the row keeps its diagnostic identity.
#[must_use]
pub fn coroutine_resume_conditional_row_kind(original_kind: &str) -> String {
    format!("{COROUTINE_RESUME_CONDITIONAL_ROW_KIND_PREFIX}{original_kind}")
}

/// Whether `kind` was stamped by [`coroutine_resume_conditional_row_kind`].
#[must_use]
pub fn is_coroutine_resume_conditional_row_kind(kind: &str) -> bool {
    kind.starts_with(COROUTINE_RESUME_CONDITIONAL_ROW_KIND_PREFIX)
}

/// Reserved coroutine state discriminant: the coroutine has returned/completed.
///
/// Pinned to `rustc_middle::ty::CoroutineArgsExt::RETURNED` (a rustc ABI
/// constant, NOT a heuristic); `trust-mir-extract` carries a compile-time
/// cross-check against the live rustc constant so the two can never drift.
pub const COROUTINE_RESERVED_STATE_RETURNED: u128 = 1;

/// Reserved coroutine state discriminant: the coroutine panicked (poisoned).
/// Pinned to `rustc_middle::ty::CoroutineArgsExt::POISONED`; cross-checked in
/// `trust-mir-extract` like [`COROUTINE_RESERVED_STATE_RETURNED`].
pub const COROUTINE_RESERVED_STATE_POISONED: u128 = 2;

/// The initial coroutine state discriminant (`UNRESUMED`). Every genuine resume
/// dispatch includes it; the live-state recognizer requires it fail-closed.
pub const COROUTINE_STATE_UNRESUMED: u128 = 0;

/// Render a live-state set as the canonical `{0}` / `{0, 3}` spelling used in
/// obligation descriptions and the contract row.
#[must_use]
pub fn coroutine_resume_contract_states_render(states: &[u128]) -> String {
    let inner = states.iter().map(u128::to_string).collect::<Vec<_>>().join(", ");
    format!("{{{inner}}}")
}

/// Whether `states` is a well-formed coroutine LIVE resume-state set: strictly
/// sorted (deduped), non-empty, containing the mandatory `UNRESUMED=0` entry
/// and excluding both reserved terminal discriminants. Every producer AND
/// consumer of the contract validates through this single predicate.
#[must_use]
pub fn coroutine_resume_contract_states_are_valid(states: &[u128]) -> bool {
    !states.is_empty()
        && states.windows(2).all(|w| w[0] < w[1])
        && states.contains(&COROUTINE_STATE_UNRESUMED)
        && !states.contains(&COROUTINE_RESERVED_STATE_RETURNED)
        && !states.contains(&COROUTINE_RESERVED_STATE_POISONED)
}

/// Build the sentinel obligation description the bridge stamps:
/// `"[trust-coroutine-resume-state-contract] live states {0}: resumed after return"`.
#[must_use]
pub fn coroutine_resume_contract_obligation_description(
    states: &[u128],
    sentinel_desc: &str,
) -> String {
    format!(
        "{COROUTINE_RESUME_CONTRACT_OBLIGATION_PREFIX}live states \
         {}: {sentinel_desc}",
        coroutine_resume_contract_states_render(states)
    )
}

/// Parse a sentinel obligation description produced by
/// [`coroutine_resume_contract_obligation_description`]. Returns the live-state
/// set and the trailing sentinel text, or `None` for ANY malformed spelling
/// (fail-closed: a malformed marker is a defect, never evidence). The returned
/// set is guaranteed [`coroutine_resume_contract_states_are_valid`].
#[must_use]
pub fn parse_coroutine_resume_contract_obligation_description(
    desc: &str,
) -> Option<(Vec<u128>, &str)> {
    let rest = desc.strip_prefix(COROUTINE_RESUME_CONTRACT_OBLIGATION_PREFIX)?;
    let rest = rest.strip_prefix("live states {")?;
    let (set, tail) = rest.split_once('}')?;
    let sentinel = tail.strip_prefix(": ")?;
    let mut states = Vec::new();
    for part in set.split(',') {
        states.push(part.trim().parse::<u128>().ok()?);
    }
    coroutine_resume_contract_states_are_valid(&states).then_some((states, sentinel))
}

/// Build the published contract row's description, naming the exact state set.
#[must_use]
pub fn coroutine_resume_contract_row_description(states: &[u128]) -> String {
    format!(
        "coroutine resume-state executor-protocol contract: ResumedAfterReturn/Panic/Drop \
         sentinels proved unreachable under exported precondition `resume state ∈ {}` \
         (reserved RETURNED=1/POISONED=2 excluded per rustc ABI)",
        coroutine_resume_contract_states_render(states)
    )
}

/// Parse the live-state set back out of a contract row description produced by
/// [`coroutine_resume_contract_row_description`]. Fail-closed on any drift.
#[must_use]
pub fn parse_coroutine_resume_contract_row_description(desc: &str) -> Option<Vec<u128>> {
    let rest = desc.strip_prefix(
        "coroutine resume-state executor-protocol contract: ResumedAfterReturn/Panic/Drop \
         sentinels proved unreachable under exported precondition `resume state ∈ {",
    )?;
    let (set, tail) = rest.split_once('}')?;
    if tail != "` (reserved RETURNED=1/POISONED=2 excluded per rustc ABI)" {
        return None;
    }
    let mut states = Vec::new();
    for part in set.split(',') {
        states.push(part.trim().parse::<u128>().ok()?);
    }
    coroutine_resume_contract_states_are_valid(&states).then_some(states)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The forbidden full-verifier classifier substrings (targo
    /// `is_full_verifier_text`). No assumption marker may contain any of them.
    const FULL_VERIFIER_MARKERS: &[&str] = &[
        "native full verifier",
        "full verifier",
        "full-verifier",
        "trust-verify-full",
        "fullverification::",
    ];

    #[test]
    fn extern_call_prefix_is_marker_free() {
        for prefix in [
            EXTERN_CALL_ASSUMPTION_PREFIX,
            ABSENT_CALLEE_ASSUMPTION_PREFIX,
            EXPECTED_ABSENT_CALLEE_ASSUMPTION_PREFIX,
            ASSUMED_TOTAL_CALLEE_ASSUMPTION_PREFIX,
            DROP_GLUE_ASSUMPTION_PREFIX,
            COROUTINE_RESUME_CONTRACT_OBLIGATION_PREFIX,
            COROUTINE_RESUME_PRECONDITION_PREFIX,
        ] {
            let lower = prefix.to_ascii_lowercase();
            for marker in FULL_VERIFIER_MARKERS {
                assert!(
                    !lower.contains(marker),
                    "assumption prefix `{prefix}` must not contain full-verifier marker `{marker}`"
                );
            }
        }
        // The EXPECTED-absent prefix must NOT be a substring of the fatal absent-callee
        // prefix (or vice-versa) — a demotable row must never be mistaken for a fatal one.
        assert!(
            !ABSENT_CALLEE_ASSUMPTION_PREFIX.contains(EXPECTED_ABSENT_CALLEE_ASSUMPTION_PREFIX)
                && !EXPECTED_ABSENT_CALLEE_ASSUMPTION_PREFIX
                    .contains(ABSENT_CALLEE_ASSUMPTION_PREFIX),
            "expected-absent and absent-callee prefixes must be mutually non-substring"
        );
        for other in [ABSENT_CALLEE_ASSUMPTION_PREFIX, EXPECTED_ABSENT_CALLEE_ASSUMPTION_PREFIX] {
            assert!(
                !other.contains(ASSUMED_TOTAL_CALLEE_ASSUMPTION_PREFIX)
                    && !ASSUMED_TOTAL_CALLEE_ASSUMPTION_PREFIX.contains(other),
                "assumed-total and `{other}` prefixes must be mutually non-substring"
            );
        }
    }

    #[test]
    fn assumption_tags_are_pinned() {
        // Pin the wire tags so the compiler, the bridge, and the report ledger
        // stay in lockstep. Changing these breaks the assumption registry.
        assert_eq!(EXTERN_CALL_ASSUMPTION_TAG, "extern-call");
        assert_eq!(NATIVE_LOWERING_ASSUMPTION_TAG, "native-lowering");
        assert_eq!(ABSENT_CALLEE_ASSUMPTION_TAG, "absent-callee");
        assert_eq!(EXPECTED_ABSENT_CALLEE_ASSUMPTION_TAG, "expected-absent-callee");
        assert_eq!(ASSUMED_TOTAL_CALLEE_ASSUMPTION_TAG, "assumed-total-callee");
        assert_eq!(DROP_GLUE_ASSUMPTION_TAG, "drop-glue");
        assert_eq!(MEMORY_SAFE_ASSUMPTION_ROW_SOURCE, "trust-memory-safe");
        assert_eq!(MEMORY_SAFE_PANIC_ASSUMPTION_TAG, "memory-safe-panic");
    }

    #[test]
    fn assumption_tags_are_marker_free() {
        for tag in [
            EXTERN_CALL_ASSUMPTION_TAG,
            NATIVE_LOWERING_ASSUMPTION_TAG,
            ABSENT_CALLEE_ASSUMPTION_TAG,
            ASSUMED_TOTAL_CALLEE_ASSUMPTION_TAG,
            DROP_GLUE_ASSUMPTION_TAG,
            MEMORY_SAFE_ASSUMPTION_ROW_SOURCE,
            MEMORY_SAFE_PANIC_ASSUMPTION_TAG,
        ] {
            let lower = tag.to_ascii_lowercase();
            for marker in FULL_VERIFIER_MARKERS {
                assert!(!lower.contains(marker), "assumption tag `{tag}` must be marker-free");
            }
        }
    }

    #[test]
    fn contract_panic_strings_are_pinned() {
        // Pin the wire strings so trust-vcgen (marker producer), the compiler's
        // verify pass (row rewriter), and targo's partition stay in lockstep.
        assert_eq!(CONTRACT_PANIC_VC_MARKER, "[trust-contract-panic] ");
        assert_eq!(CONTRACT_PANIC_UNUSED_VC_MARKER, "[trust-contract-panic-unused] ");
        assert_eq!(CONTRACT_PANIC_ROW_KIND_PREFIX, "contract-panic:");
        assert_eq!(CONTRACT_PANIC_MATCHED_ROW_KIND, "contract-panic:matched");
        assert_eq!(CONTRACT_PANIC_UNUSED_ROW_KIND, "contract-panic-unused");
        assert_eq!(CONTRACT_PANIC_ROW_SOURCE, "trust-contract");
        assert!(CONTRACT_PANIC_MATCHED_ROW_KIND.starts_with(CONTRACT_PANIC_ROW_KIND_PREFIX));
    }

    #[test]
    fn contract_panic_unused_kind_never_counts_as_contract_panic() {
        // SOUNDNESS: the unused-annotation row must be a genuine FAILURE in
        // targo's partition. If it ever started with the `contract-panic:`
        // prefix it would fall into the conditional-pass bucket — i.e. an
        // annotation on panic-free code could green-light itself.
        assert!(
            !CONTRACT_PANIC_UNUSED_ROW_KIND.starts_with(CONTRACT_PANIC_ROW_KIND_PREFIX),
            "`{CONTRACT_PANIC_UNUSED_ROW_KIND}` must not match the `{CONTRACT_PANIC_ROW_KIND_PREFIX}` partition prefix"
        );
        // The matched VC marker must also never contain the UNUSED marker (or
        // vice versa) — `.contains()`-based row classification must be disjoint.
        assert!(!CONTRACT_PANIC_VC_MARKER.contains(CONTRACT_PANIC_UNUSED_VC_MARKER));
        assert!(
            !CONTRACT_PANIC_UNUSED_VC_MARKER
                .trim_end()
                .contains(CONTRACT_PANIC_VC_MARKER.trim_end())
        );
    }

    #[test]
    fn contract_panic_strings_are_marker_free() {
        for s in [
            CONTRACT_PANIC_VC_MARKER,
            CONTRACT_PANIC_UNUSED_VC_MARKER,
            CONTRACT_PANIC_ROW_KIND_PREFIX,
            CONTRACT_PANIC_MATCHED_ROW_KIND,
            CONTRACT_PANIC_UNUSED_ROW_KIND,
            CONTRACT_PANIC_ROW_SOURCE,
        ] {
            let lower = s.to_ascii_lowercase();
            for marker in FULL_VERIFIER_MARKERS {
                assert!(
                    !lower.contains(marker),
                    "contract-panic string `{s}` must not contain full-verifier marker `{marker}`"
                );
            }
        }
    }

    #[test]
    fn coroutine_resume_contract_markers_are_disjoint_and_marker_free() {
        for s in [
            COROUTINE_RESUME_CONTRACT_OBLIGATION_PREFIX,
            COROUTINE_RESUME_PRECONDITION_PREFIX,
            COROUTINE_RESUME_CONTRACT_ROW_KIND,
            COROUTINE_RESUME_CONTRACT_ROW_REASON,
        ] {
            let lower = s.to_ascii_lowercase();
            for marker in FULL_VERIFIER_MARKERS {
                assert!(
                    !lower.contains(marker),
                    "coroutine contract string `{s}` must not contain full-verifier marker `{marker}`"
                );
            }
        }
        // The sentinel marker and the callsite-precondition marker must be
        // mutually non-substring — `.starts_with()`-based classification of the
        // two obligation families must never conflate them.
        assert!(
            !COROUTINE_RESUME_CONTRACT_OBLIGATION_PREFIX
                .contains(COROUTINE_RESUME_PRECONDITION_PREFIX)
                && !COROUTINE_RESUME_PRECONDITION_PREFIX
                    .contains(COROUTINE_RESUME_CONTRACT_OBLIGATION_PREFIX)
        );
        // The row kind must never read as an assumption row and must never
        // collide with the contract-panic bucket prefix.
        assert!(!COROUTINE_RESUME_CONTRACT_ROW_KIND.starts_with("assumption:"));
        assert!(!COROUTINE_RESUME_CONTRACT_ROW_KIND.starts_with(CONTRACT_PANIC_ROW_KIND_PREFIX));
        // Pin the wire kind: compiler producer, targo consumer.
        assert_eq!(COROUTINE_RESUME_CONTRACT_ROW_KIND, "contract:coroutine-resume-state");
        // Reserved ABI discriminants pinned (cross-checked against the live
        // rustc constants in trust-mir-extract).
        assert_eq!(COROUTINE_STATE_UNRESUMED, 0);
        assert_eq!(COROUTINE_RESERVED_STATE_RETURNED, 1);
        assert_eq!(COROUTINE_RESERVED_STATE_POISONED, 2);
    }

    /// D2 regression pin: the contract-conditional marker is a DISTINCT bucket
    /// from the published contract row, never reads as an assumption row, is
    /// marker-free, and round-trips the original kind it wraps.
    #[test]
    fn coroutine_resume_conditional_kind_is_distinct_and_round_trips() {
        for s in [
            COROUTINE_RESUME_CONDITIONAL_ROW_KIND_PREFIX,
            COROUTINE_RESUME_CONDITIONAL_ROW_REASON,
        ] {
            let lower = s.to_ascii_lowercase();
            for marker in FULL_VERIFIER_MARKERS {
                assert!(
                    !lower.contains(marker),
                    "conditional string `{s}` must not contain full-verifier marker `{marker}`"
                );
            }
        }
        assert!(!COROUTINE_RESUME_CONDITIONAL_ROW_KIND_PREFIX.starts_with("assumption:"));
        assert!(
            !COROUTINE_RESUME_CONDITIONAL_ROW_KIND_PREFIX
                .starts_with(CONTRACT_PANIC_ROW_KIND_PREFIX)
        );
        // The conditional prefix and the published contract kind must be
        // mutually non-substring: a `starts_with` classifier must never read a
        // conditional row as the published contract row (which targo counts
        // through a different, shape-checked path) or vice versa.
        assert!(
            !COROUTINE_RESUME_CONDITIONAL_ROW_KIND_PREFIX
                .starts_with(COROUTINE_RESUME_CONTRACT_ROW_KIND)
                && !COROUTINE_RESUME_CONTRACT_ROW_KIND
                    .starts_with(COROUTINE_RESUME_CONDITIONAL_ROW_KIND_PREFIX)
        );
        let stamped = coroutine_resume_conditional_row_kind("assert");
        assert!(is_coroutine_resume_conditional_row_kind(&stamped));
        assert_eq!(
            stamped.strip_prefix(COROUTINE_RESUME_CONDITIONAL_ROW_KIND_PREFIX),
            Some("assert")
        );
        assert!(!is_coroutine_resume_conditional_row_kind("assert"));
        assert!(!is_coroutine_resume_conditional_row_kind(COROUTINE_RESUME_CONTRACT_ROW_KIND));
    }

    #[test]
    fn coroutine_resume_contract_description_round_trips() {
        let desc = coroutine_resume_contract_obligation_description(&[0], "resumed after return");
        let (states, sentinel) =
            parse_coroutine_resume_contract_obligation_description(&desc).expect("round trip");
        assert_eq!(states, vec![0]);
        assert_eq!(sentinel, "resumed after return");

        let desc =
            coroutine_resume_contract_obligation_description(&[0, 3], "resumed after panic");
        let (states, sentinel) =
            parse_coroutine_resume_contract_obligation_description(&desc).expect("round trip");
        assert_eq!(states, vec![0, 3]);
        assert_eq!(sentinel, "resumed after panic");

        let row = coroutine_resume_contract_row_description(&[0, 3]);
        assert_eq!(parse_coroutine_resume_contract_row_description(&row), Some(vec![0, 3]));
    }

    #[test]
    fn coroutine_resume_contract_parser_fails_closed() {
        // A live set containing a reserved terminal state is a DEFECT: parsing
        // must refuse it even when the spelling is otherwise well-formed —
        // accepting RETURNED=1 as "live" is exactly the by-construction
        // discharge the contract lane exists to forbid.
        let poisoned = format!(
            "{COROUTINE_RESUME_CONTRACT_OBLIGATION_PREFIX}live states {{0, 1}}: resumed after return"
        );
        assert!(parse_coroutine_resume_contract_obligation_description(&poisoned).is_none());
        // Missing the mandatory UNRESUMED=0 entry.
        let no_zero = format!(
            "{COROUTINE_RESUME_CONTRACT_OBLIGATION_PREFIX}live states {{3}}: resumed after return"
        );
        assert!(parse_coroutine_resume_contract_obligation_description(&no_zero).is_none());
        // Unsorted / duplicated sets.
        let unsorted = format!(
            "{COROUTINE_RESUME_CONTRACT_OBLIGATION_PREFIX}live states {{3, 0}}: resumed after drop"
        );
        assert!(parse_coroutine_resume_contract_obligation_description(&unsorted).is_none());
        let dup = format!(
            "{COROUTINE_RESUME_CONTRACT_OBLIGATION_PREFIX}live states {{0, 0}}: resumed after drop"
        );
        assert!(parse_coroutine_resume_contract_obligation_description(&dup).is_none());
        // Empty set, junk payloads, missing prefix.
        let empty = format!(
            "{COROUTINE_RESUME_CONTRACT_OBLIGATION_PREFIX}live states {{}}: resumed after drop"
        );
        assert!(parse_coroutine_resume_contract_obligation_description(&empty).is_none());
        assert!(
            parse_coroutine_resume_contract_obligation_description(
                "live states {0}: resumed after return"
            )
            .is_none()
        );
        assert!(parse_coroutine_resume_contract_row_description("junk").is_none());
    }
}
