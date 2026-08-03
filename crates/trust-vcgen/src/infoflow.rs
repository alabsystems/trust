//! Experimental information-flow obligation prototype.
//!
//! This module is compiled only for crate tests or with the non-default
//! `prototype-infoflow` feature. It is deliberately not called by
//! `generate_vcs` and must not be used as a compiler acceptance/rejection gate.
//!
//! The prototype operates on the legacy MIR-shaped [`VerifiableFunction`]
//! representation and delegates to `trust_types::analyze_taint`, which walks
//! basic blocks once without predecessor joins or a CFG worklist/fixpoint. Its
//! policy also identifies sources, sinks, and sanitizers using callee-name
//! substring matching. Besides false matches, a similarly named function can
//! therefore be mistaken for a sanitizer and clear taint. These limitations can
//! miss real flows.
//!
//! A production replacement must instead analyze the canonical TrustIR CFG
//! directly, join incoming states and iterate loops to a fixpoint, and match
//! resolved callees by exact stable identity. It also needs an explicit,
//! owner-scoped policy extracted by the front end. Merely wiring compiler
//! attributes into this prototype would not make it sound.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{
    Formula, Sanitizer, SinkKind, TaintLabel, TaintPolicy, TaintSink, TaintSource, VcKind,
    VerifiableFunction, VerificationCondition, analyze_taint,
};

/// The single lattice point this prototype uses for untrusted data.
const UNTRUSTED: &str = "untrusted";
/// The single sink category this prototype uses for verdict calls.
const VERDICT: &str = "verdict";

/// Build an untrusted-to-verdict [`TaintPolicy`] from source, sink, and
/// declassifier callee substrings.
///
/// This substring-based policy is intentionally confined to the prototype. In
/// particular, a substring match must not be treated as a resolved callee
/// identity or trusted declassification boundary.
pub fn untrusted_verdict_policy(
    sources: impl IntoIterator<Item = String>,
    sinks: impl IntoIterator<Item = String>,
    declassifiers: impl IntoIterator<Item = String>,
) -> TaintPolicy {
    TaintPolicy {
        sources: sources
            .into_iter()
            .map(|pattern| TaintSource { label: TaintLabel::Custom(UNTRUSTED.into()), pattern })
            .collect(),
        sinks: sinks
            .into_iter()
            .map(|pattern| TaintSink { label: SinkKind::Custom(VERDICT.into()), pattern })
            .collect(),
        sanitizers: declassifiers
            .into_iter()
            .map(|pattern| Sanitizer { removes: TaintLabel::Custom(UNTRUSTED.into()), pattern })
            .collect(),
    }
}

/// Run the prototype analysis over `func` under `policy` and emit one
/// fail-closed [`VcKind::TaintViolation`] for each reported undeclassified
/// untrusted-to-verdict flow.
///
/// An empty result is not a proof of noninterference: the underlying analysis
/// has no CFG join/fixpoint and its name matching is approximate.
pub fn generate_infoflow_vcs_with_policy(
    func: &VerifiableFunction,
    policy: &TaintPolicy,
) -> Vec<VerificationCondition> {
    // No sinks ⇒ nothing to protect ⇒ skip the walk entirely (the common case).
    if policy.sinks.is_empty() {
        return Vec::new();
    }
    let result = analyze_taint(&func.body, policy);
    result
        .violations
        .into_iter()
        .filter(|v| {
            matches!(&v.sink_kind, SinkKind::Custom(k) if k == VERDICT)
                && matches!(&v.source_label, TaintLabel::Custom(l) if l == UNTRUSTED)
        })
        .map(|v| VerificationCondition {
            kind: VcKind::TaintViolation {
                source_label: UNTRUSTED.to_string(),
                sink_kind: format!("verdict:{}", v.sink_func),
                path_length: v.path.len(),
            },
            function: func.name.as_str().into(),
            location: v.sink_span.clone(),
            // Fail-closed: always SAT ⇒ reported Failed. The dataflow already
            // proved the leak, so the obligation is intentionally undischargeable.
            formula: Formula::Bool(true),
            contract_metadata: None,
            obligation: None,
        })
        .collect()
}
