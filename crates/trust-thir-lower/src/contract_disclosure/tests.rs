// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0 or the MIT license.

//! WS5.5 step 1: the disclosure row BYTES are pinned across the renderer move.
//!
//! `render_proposition` / `render_predicate` / `kind_tag` / `esc` moved,
//! unchanged, from this module to `crate::contract_render`. The expected rows
//! below are spelled from the PRE-MOVE format strings (`contract_disclosure.rs`
//! at origin/main c132f5a193, `render_row` + `render_proposition`), one row per
//! predicate kind and one proposition per vocabulary variant, so a spelling
//! drift in either consumer of the moved renderer reaches this test.

use rustc_middle::mir::Local;
use rustc_middle::mir::trust_contract::{
    TrustContract, TrustContractKind, TrustContractPayloadType, TrustContractPredicate,
    TrustContractPredicateKind, TrustContractProposition as P, TrustContractPropositionDomain as D,
    TrustContractSource, TrustContractSubject, TrustContractVerifierSort,
};
use rustc_span::{DUMMY_SP, Symbol};
use trust_ir::value::FuncId;

use super::render_row;

fn contract(
    kind: TrustContractKind,
    predicate: TrustContractPredicateKind,
) -> TrustContract<'static> {
    TrustContract {
        citation: None,
        kind,
        source: TrustContractSource::Native,
        subject: TrustContractSubject::Function,
        predicate: TrustContractPredicate {
            ty: TrustContractPayloadType::Verifier(TrustContractVerifierSort::Bool),
            kind: predicate,
            source_bindings: Vec::new(),
            source_place_bindings: None,
        },
        span: DUMMY_SP,
        keyword_span: None,
    }
}

const HEAD: &str = "{\"schema\":\"trust.contract-disclosure.v1\",\"func_id\":3,\
\"def_path\":\"p01::clamp_add\",\"kind\":\"";
const NON_CLAIM: &str = "\",\"non_claim\":\"DesignOnly disclosure: these are the AUTHORED \
clauses, carried unproven; nothing here is a verdict\",\"predicate\":";

fn row(kind: &str, predicate: &str) -> String {
    format!("{HEAD}{kind}{NON_CLAIM}{predicate}}}")
}

fn var(name: &str, domain: D) -> P {
    P::Var { name: Symbol::intern(name), domain }
}

#[test]
fn disclosure_row_bytes_are_pinned_across_the_renderer_move() {
    rustc_span::create_default_session_globals_then(|| {
        let u64d = D::MachineInt { width: 64, signed: false };
        let x = || Box::new(var("x", u64d));
        let one = || Box::new(P::UInt(1));
        // Every vocabulary variant once, inside one typed clause.
        let every = P::And(vec![
            P::Bool(true),
            P::Not(Box::new(P::Or(vec![P::Bool(false)]))),
            P::Implies(Box::new(P::Bool(true)), Box::new(P::Eq(x(), one()))),
            P::Lt(x(), Box::new(P::Int(-2))),
            P::Le(x(), Box::new(P::Add(x(), one()))),
            P::Gt(Box::new(P::Sub(x(), one())), Box::new(P::Mul(x(), one()))),
            P::Ge(Box::new(P::Div(x(), one())), Box::new(P::Rem(x(), one()))),
            P::Eq(Box::new(P::Neg(x())), x()),
            P::Eq(
                Box::new(var("f", D::Float { width: 64 })),
                Box::new(P::Float { bits: 0x8000_0000_0000_0000, width: 64 }),
            ),
            P::Eq(Box::new(var("b", D::Bool)), Box::new(var("m", D::MathematicalInt))),
            P::Eq(Box::new(var("u", D::PointerSizedInt { width: 64, signed: false })), one()),
        ]);
        let xv =
            "{\"var\":{\"name\":\"x\",\"domain\":\"MachineInt { width: 64, signed: false }\"}}";
        let expected_every = format!(
            "{{\"and\":[{{\"bool\":true}},{{\"not\":{{\"or\":[{{\"bool\":false}}]}}}},\
             {{\"implies\":[{{\"bool\":true}},{{\"eq\":[{xv},{{\"uint\":\"1\"}}]}}]}},\
             {{\"lt\":[{xv},{{\"int\":\"-2\"}}]}},\
             {{\"le\":[{xv},{{\"add\":[{xv},{{\"uint\":\"1\"}}]}}]}},\
             {{\"gt\":[{{\"sub\":[{xv},{{\"uint\":\"1\"}}]}},{{\"mul\":[{xv},{{\"uint\":\"1\"}}]}}]}},\
             {{\"ge\":[{{\"div\":[{xv},{{\"uint\":\"1\"}}]}},{{\"rem\":[{xv},{{\"uint\":\"1\"}}]}}]}},\
             {{\"eq\":[{{\"neg\":{xv}}},{xv}]}},\
             {{\"eq\":[{{\"var\":{{\"name\":\"f\",\"domain\":\"Float {{ width: 64 }}\"}}}},\
             {{\"float\":{{\"bits\":\"9223372036854775808\",\"width\":64}}}}]}},\
             {{\"eq\":[{{\"var\":{{\"name\":\"b\",\"domain\":\"Bool\"}}}},\
             {{\"var\":{{\"name\":\"m\",\"domain\":\"MathematicalInt\"}}}}]}},\
             {{\"eq\":[{{\"var\":{{\"name\":\"u\",\"domain\":\"PointerSizedInt {{ width: 64, \
             signed: false }}\"}}}},{{\"uint\":\"1\"}}]}}]}}"
        );

        let cases: Vec<(TrustContract<'static>, String)> = vec![
            (
                contract(
                    TrustContractKind::Requires,
                    TrustContractPredicateKind::Typed {
                        text: Symbol::intern("a \"q\" \\ \n\t\u{1}"),
                        proposition: every,
                    },
                ),
                row(
                    "requires",
                    &format!(
                        "{{\"typed\":{{\"text\":\"a \\\"q\\\" \\\\ \\n\\t\\u0001\",\
                         \"proposition\":{expected_every}}}}}"
                    ),
                ),
            ),
            (
                contract(
                    TrustContractKind::Ensures,
                    TrustContractPredicateKind::Opaque { text: Symbol::intern("result <= hi") },
                ),
                row("ensures", "{\"opaque\":{\"text\":\"result <= hi\"}}"),
            ),
            (
                contract(
                    TrustContractKind::Decreases,
                    TrustContractPredicateKind::MirLocal { local: Local::from_u32(4) },
                ),
                row("decreases", "{\"mir_local\":{\"local\":4}}"),
            ),
            (
                contract(
                    TrustContractKind::LoopInvariant,
                    TrustContractPredicateKind::BoolLiteral { value: false },
                ),
                row("loop-invariant", "{\"bool\":false}"),
            ),
            (
                contract(
                    TrustContractKind::Requires,
                    TrustContractPredicateKind::Unsupported { reason: Symbol::intern("why") },
                ),
                row("requires", "{\"unsupported\":{\"reason\":\"why\"}}"),
            ),
        ];
        for (contract, expected) in cases {
            assert_eq!(render_row(FuncId::new(3), "p01::clamp_add", &contract), expected);
        }
    });
}

#[test]
fn every_kind_tag_is_pinned() {
    rustc_span::create_default_session_globals_then(|| {
        for (kind, tag) in [
            (TrustContractKind::Requires, "requires"),
            (TrustContractKind::Ensures, "ensures"),
            (TrustContractKind::Invariant, "invariant"),
            (TrustContractKind::LoopInvariant, "loop-invariant"),
            (TrustContractKind::Decreases, "decreases"),
            (TrustContractKind::Assumes, "assumes"),
            (TrustContractKind::Asserts, "asserts"),
            (TrustContractKind::Refinement, "refinement"),
            (TrustContractKind::Temporal, "temporal"),
        ] {
            let c = contract(kind, TrustContractPredicateKind::BoolLiteral { value: true });
            assert_eq!(crate::contract_render::kind_tag(&c), tag);
        }
    });
}
