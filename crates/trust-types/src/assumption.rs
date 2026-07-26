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
}
