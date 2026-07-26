#![cfg(feature = "prototype-infoflow")]

// trust_vcgen/tests/infoflow_leak.rs — experimental information-flow prototype.
//
// Synthetic legacy-IR coverage showing that the injectable prototype reports a
// straight-line flow and stays silent when the configured sanitizer is called.
// This is regression coverage for the prototype, not a soundness claim.
//
// This is the general form of the a3d-cert forgery bug: a parsed (untrusted)
// certificate field flowing straight into an accept decision without being
// recomputed from the trusted subject.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{Sanitizer, SinkKind, TaintLabel, TaintPolicy, TaintSink, TaintSource};
use trust_types::*;
use trust_vcgen::infoflow::{generate_infoflow_vcs_with_policy, untrusted_verdict_policy};

fn span(line: usize) -> SourceSpan {
    SourceSpan { file: "infoflow_test.rs".into(), line_start: line as u32, col_start: 1, ..SourceSpan::default() }
}

fn make_func(name: &str, locals: Vec<LocalDecl>, blocks: Vec<BasicBlock>) -> VerifiableFunction {
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("synthetic::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody { locals, blocks, arg_count: 1, return_ty: Ty::Unit },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn call(func: &str, args: Vec<Operand>, dest: usize, at: usize, next: Option<usize>) -> Terminator {
    Terminator::Call {
        func: func.into(),
        args,
        dest: Place::local(dest),
        target: next.map(BlockId),
        unwind: UnwindEdge::Unreachable,
        span: span(at),
        atomic: None,
        is_unsafe_sig: false,
        is_foreign: false,
    }
}

fn block(id: usize, terminator: Terminator) -> BasicBlock {
    BasicBlock { id: BlockId(id), stmts: vec![], terminator }
}

fn locals(n: usize) -> Vec<LocalDecl> {
    (0..n).map(|i| LocalDecl { index: i, ty: Ty::Int { width: 64, signed: true }, name: None }).collect()
}

/// The policy under test: `parse_cert` produces untrusted data; `accept` is the
/// verdict sink; `rederive_from_subject` is the declassifier.
fn policy() -> TaintPolicy {
    untrusted_verdict_policy(
        ["parse_cert".to_string()],
        ["accept".to_string()],
        ["rederive_from_subject".to_string()],
    )
}

// ---------------------------------------------------------------------------
// BAD: parsed field flows straight into the verdict — must produce a violation.
// ---------------------------------------------------------------------------
#[test]
fn untrusted_reaching_verdict_is_a_violation() {
    // L1 = parse_cert(input);  accept(L1)  — no re-derivation.
    let f = make_func(
        "check_forgeable",
        locals(3),
        vec![
            block(0, call("parse_cert", vec![Operand::Copy(Place::local(0))], 1, 10, Some(1))),
            block(1, call("accept", vec![Operand::Copy(Place::local(1))], 2, 20, Some(2))),
            block(2, Terminator::Return),
        ],
    );
    let vcs = generate_infoflow_vcs_with_policy(&f, &policy());
    let taint: Vec<_> = vcs
        .iter()
        .filter(|v| matches!(&v.kind, VcKind::TaintViolation { sink_kind, .. } if sink_kind.starts_with("verdict")))
        .collect();
    assert_eq!(
        taint.len(),
        1,
        "an untrusted value reaching the verdict must emit exactly one TaintViolation; got {:#?}",
        vcs.iter().map(|v| v.kind.description()).collect::<Vec<_>>()
    );
    // Fail-closed: the VC is intentionally undischargeable (always SAT).
    assert_eq!(taint[0].formula, Formula::Bool(true), "the info-flow VC must be fail-closed");
}

// ---------------------------------------------------------------------------
// GOOD: the value is re-derived from the subject before the verdict — no VC.
// ---------------------------------------------------------------------------
#[test]
fn rederived_value_reaching_verdict_is_clean() {
    // L1 = parse_cert(input);
    // L2 = rederive_from_subject(subject);   // declassifier, fresh local
    // accept(L2)                              // feed the RE-DERIVED value
    let f = make_func(
        "check_sound",
        locals(3),
        vec![
            block(0, call("parse_cert", vec![Operand::Copy(Place::local(0))], 1, 10, Some(1))),
            block(1, call("rederive_from_subject", vec![Operand::Copy(Place::local(0))], 2, 15, Some(2))),
            block(2, call("accept", vec![Operand::Copy(Place::local(2))], 0, 20, Some(3))),
            block(3, Terminator::Return),
        ],
    );
    let vcs = generate_infoflow_vcs_with_policy(&f, &policy());
    assert!(
        vcs.iter().all(|v| !matches!(&v.kind, VcKind::TaintViolation { .. })),
        "a re-derived value feeding the verdict must produce NO TaintViolation; got {:#?}",
        vcs.iter().map(|v| v.kind.description()).collect::<Vec<_>>()
    );
}

// ---------------------------------------------------------------------------
// An empty policy (no attributes in the crate) must be a complete no-op.
// ---------------------------------------------------------------------------
#[test]
fn empty_policy_emits_nothing() {
    let f = make_func(
        "unannotated",
        locals(2),
        vec![
            block(0, call("parse_cert", vec![Operand::Copy(Place::local(0))], 1, 10, Some(1))),
            block(1, Terminator::Return),
        ],
    );
    let empty = TaintPolicy { sources: vec![], sinks: vec![], sanitizers: vec![] };
    assert!(generate_infoflow_vcs_with_policy(&f, &empty).is_empty());

    // Sanity: the label/sink/sanitizer types compose as expected (guards against
    // an API drift in trust_types::taint).
    let _p = TaintPolicy {
        sources: vec![TaintSource { label: TaintLabel::Custom("untrusted".into()), pattern: "p".into() }],
        sinks: vec![TaintSink { label: SinkKind::Custom("verdict".into()), pattern: "a".into() }],
        sanitizers: vec![Sanitizer { removes: TaintLabel::Custom("untrusted".into()), pattern: "d".into() }],
    };
}

// Enabling the prototype feature exposes only the injectable API. It must not
// silently change the production VC pipeline's semantics.
#[test]
fn prototype_feature_does_not_wire_infoflow_into_generate_vcs() {
    let f = make_func(
        "feature_only",
        locals(3),
        vec![
            block(0, call("parse_cert", vec![Operand::Copy(Place::local(0))], 1, 10, Some(1))),
            block(1, call("accept", vec![Operand::Copy(Place::local(1))], 2, 20, Some(2))),
            block(2, Terminator::Return),
        ],
    );

    let vcs = trust_vcgen::generate_vcs(&f);
    assert!(
        vcs.iter().all(|vc| !matches!(&vc.kind, VcKind::TaintViolation { .. })),
        "the opt-in prototype feature must not wire information flow into generate_vcs"
    );
}
