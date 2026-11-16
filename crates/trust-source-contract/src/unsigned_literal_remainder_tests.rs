// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use trust_types::{CompilerContractProposition, CompilerContractValueDomain as Domain};

use super::*;

fn proposition(source: &str) -> (VerifiableFunction, Contract, CompilerContractProposition) {
    let function = VerifiableFunction {
        name: "crc_poly_select".into(),
        def_path: "test::crc_poly_select".into(),
        span: SourceSpan::default(),
        body: trust_types::VerifiableBody {
            locals: vec![
                trust_types::LocalDecl { index: 0, ty: Ty::u32(), name: None },
                trust_types::LocalDecl { index: 1, ty: Ty::u32(), name: Some("crc".into()) },
            ],
            blocks: vec![],
            arg_count: 1,
            return_ty: Ty::u32(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    };
    let contract = Contract {
        kind: TrustTypesContractKind::Ensures,
        span: SourceSpan::default(),
        body: format!("{LOWERED_COMPILER_CONTRACT_PREFIX}{source}"),
    };
    let parsed = trust_types::parse_spec_expr(source).unwrap();
    let mut names: Vec<_> = parsed.free_variables().into_iter().collect();
    names.sort();
    let variable_domains: Vec<_> = names
        .into_iter()
        .map(|name| trust_types::CompilerContractVariableDomain {
            name,
            domain: Domain::MachineInt { width: 32, signed: false },
        })
        .collect();
    let formula =
        trust_types::compiler_contract_formula_with_domains(&parsed, &variable_domains).unwrap();
    let proposition = CompilerContractProposition {
        source_contract_index: 0,
        kind: contract.kind,
        body: contract.body.clone(),
        formula,
        variable_domains,
    };
    (function, contract, proposition)
}

#[test]
fn typed_unsigned_literal_remainder_keeps_original_formula_and_digest() {
    let (function, contract, proposition) =
        proposition("(crc % 2 == 0 && result == 0) || (crc % 2 == 1 && result == 3988292384)");
    let expected = trust_spec_predicate_from_formula(&proposition.formula)
        .unwrap()
        .into_contract_predicate()
        .unwrap();
    let digest = trust_types::typed_contract_proposition_digest(
        &proposition.formula,
        &proposition.variable_domains,
    );
    let contracts = CompilerContractBundle::new(vec![contract.clone()])
        .with_typed_propositions(vec![proposition]);
    assert!(contracts.typed_proposition(0, &contract).is_some());
    let bundle = contract_bundle_to_verifier_api(&function, &contracts);
    assert_eq!(bundle.contracts.len(), 1);
    assert_eq!(bundle.contracts[0].predicate, expected);
    assert!(bundle.contracts[0].metadata.iter().any(|entry| {
        entry.key == "trust.contract.lowering" && entry.value == "typed_proposition"
    }));
    assert!(bundle.contracts[0].metadata.iter().any(|entry| {
        entry.key == TRUST_CONTRACT_TYPED_PROPOSITION_DIGEST_METADATA_KEY && entry.value == digest
    }));
    assert_eq!(bundle.obligations.len(), 1);
    assert!(matches!(bundle.obligations[0].kind, ObligationKind::Postcondition));
    assert!(bundle.obligations[0].metadata.iter().any(|entry| {
        entry.key == TRUST_CONTRACT_TYPED_PROPOSITION_DIGEST_METADATA_KEY && entry.value == digest
    }));
}

#[test]
fn typed_unsigned_literal_remainder_does_not_authorize_undefined_neighbors() {
    for source in
        ["crc % 0 == 0", "crc % -1 == 0", "crc % crc == 0", "crc % 4294967296 == 0", "crc / 2 == 0"]
    {
        let (function, contract, proposition) = proposition(source);
        let (predicate, reason, _) =
            lower_contract_predicate(&function, &contract, Some(&proposition), None);
        assert!(
            matches!(predicate, ContractPredicate::Unsupported { .. }),
            "{source}: {predicate:?}"
        );
        assert!(reason.is_some());
    }
    let (function, contract, mut proposition) = proposition("crc % 2 == 0");
    for domain in [
        Domain::MachineInt { width: 32, signed: true },
        Domain::MachineInt { width: 24, signed: false },
        Domain::PointerSizedInt { width: 64, signed: false },
        Domain::Bool,
        Domain::MathematicalInt,
        Domain::Float { width: 32 },
    ] {
        proposition.variable_domains[0].domain = domain;
        // These domains do not qualify for the original unsigned Int-exact
        // exception. A separately supported Machine{w} reading may still
        // preserve them through explicit signed/unsigned bit-vector nodes.
        assert!(typed_formula_uses_unmodeled_machine_arithmetic(
            &proposition.formula,
            &proposition.variable_domains,
        ));
        let (predicate, _, _) =
            lower_contract_predicate(&function, &contract, Some(&proposition), None);
        if matches!(
            domain,
            Domain::MachineInt { width: 24, .. }
                | Domain::Bool
                | Domain::MathematicalInt
                | Domain::Float { .. }
        ) {
            assert!(matches!(predicate, ContractPredicate::Unsupported { .. }), "{domain:?}");
        } else {
            let (Domain::MachineInt { width, signed } | Domain::PointerSizedInt { width, signed }) =
                domain
            else {
                unreachable!()
            };
            let dividend = Box::new(Formula::Var("crc".into(), Sort::BitVec(width)));
            let divisor = Box::new(Formula::BitVec { value: 2, width });
            let remainder = if signed {
                Formula::BvSRem(dividend, divisor, width)
            } else {
                Formula::BvURem(dividend, divisor, width)
            };
            let expected =
                Formula::Eq(Box::new(remainder), Box::new(Formula::BitVec { value: 0, width }));
            let expected = trust_spec_predicate_from_formula(&expected)
                .unwrap()
                .into_contract_predicate()
                .unwrap();
            assert_eq!(predicate, expected, "{domain:?}");
        }
    }
}

#[test]
fn typed_unsigned_remainder_neighbors_keep_explicit_wrapping_machine_semantics() {
    let variable = || Box::new(Formula::Var("crc".into(), Sort::BitVec(32)));
    let literal = |value| Box::new(Formula::BitVec { value, width: 32 });
    for (source, expected) in [
        (
            "(crc + 1) % 2 == 0",
            Formula::Eq(
                Box::new(Formula::BvURem(
                    Box::new(Formula::BvAdd(variable(), literal(1), 32)),
                    literal(2),
                    32,
                )),
                literal(0),
            ),
        ),
        (
            "crc % 2 + 1 == 1",
            Formula::Eq(
                Box::new(Formula::BvAdd(
                    Box::new(Formula::BvURem(variable(), literal(2), 32)),
                    literal(1),
                    32,
                )),
                literal(1),
            ),
        ),
    ] {
        let (function, contract, proposition) = proposition(source);
        assert!(typed_formula_uses_unmodeled_machine_arithmetic(
            &proposition.formula,
            &proposition.variable_domains,
        ));
        let expected = trust_spec_predicate_from_formula(&expected)
            .unwrap()
            .into_contract_predicate()
            .unwrap();
        let (predicate, reason, lowering) =
            lower_contract_predicate(&function, &contract, Some(&proposition), None);
        assert_eq!(predicate, expected, "{source}");
        assert_eq!(reason, None, "{source}");
        assert_eq!(lowering, "typed_proposition_machine_width", "{source}");
    }
}

#[test]
fn typed_unsigned_literal_remainder_requires_unique_bound_provenance() {
    let (function, contract, original) = proposition("crc % 2 == 0");
    let mut missing = original.clone();
    missing.variable_domains.clear();
    let mut duplicate = original.clone();
    duplicate.variable_domains.push(duplicate.variable_domains[0].clone());
    let mut stale = original.clone();
    stale.body.push_str(" && true");
    let mut wrong_formula = original.clone();
    wrong_formula.formula = Formula::Bool(true);
    for invalid in [missing, duplicate, stale, wrong_formula] {
        let contracts = CompilerContractBundle::new(vec![contract.clone()])
            .with_typed_propositions(vec![invalid]);
        assert!(contracts.typed_proposition(0, &contract).is_none());
        let bundle = contract_bundle_to_verifier_api(&function, &contracts);
        assert!(matches!(bundle.contracts[0].predicate, ContractPredicate::Unsupported { .. }));
    }
    // Raw source has no authenticated variable-domain sidecar.
    let (raw, _, _) = lower_contract_predicate(&function, &contract, None, None);
    assert!(matches!(raw, ContractPredicate::Unsupported { .. }));
    let quantified = Formula::Forall(vec![("crc".into(), Sort::Int)], Box::new(original.formula));
    assert!(typed_formula_uses_unmodeled_machine_arithmetic(
        &quantified,
        &original.variable_domains
    ));
}
