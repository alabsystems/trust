// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Model-four retained consumer. Every replay rebuilds the independently
//! expected whole original bytes, admits the supplied bodies, checks the
//! retained canonical relation, and checks the FINAL source proposition.

use std::collections::BTreeMap;
use std::sync::Arc;

use clean_kernel::name::NameInner;
use clean_kernel::{Declaration, Environment, Expr, ExprKind, Literal, Name};
use trust_ir::proof::{
    decode_clean_expr_dag_v2, decode_island_declarations_v1, encode_clean_expr_dag_v2,
    encode_island_declarations_v1,
};
use trust_types::Formula;

use super::super::{
    CheckedOriginalConjunction, FORMULA_MODEL, FORMULA_RECIPE, FormulaEvidence, MAX_ORIGINAL_BYTES,
    MAX_WIRE_BYTES, OriginalConjunctionPacket, RetainedTerms, SymbolicContext, encoded_hash,
};
use super::{COHORT_SHA256, CheckedTerms, Cohort, admission};

fn context(original: &[(Formula, Formula)]) -> Result<SymbolicContext, String> {
    let mut sorts = BTreeMap::new();
    let mut conflict = false;
    for formula in original.iter().flat_map(|(a, b)| [a, b]) {
        trust_types::smt_logic::check_formula_sort(formula)
            .map_err(|error| format!("FMREL original typed input: {error:?}"))?;
        formula.visit(&mut |node| {
            if let Formula::Var(name, sort) = node {
                if sorts.insert(name.clone(), sort.clone()).is_some_and(|old| old != *sort) {
                    conflict = true;
                }
            }
        });
    }
    if conflict {
        return Err("FMREL: original variable has inconsistent sorts".into());
    }
    Ok(SymbolicContext {
        bits: Default::default(),
        memories: Default::default(),
        sorts,
        exact_byte_arrays: true,
    })
}

fn original_bytes(original: &[(Formula, Formula)]) -> Result<Vec<u8>, String> {
    // Use exactly the existing canonical Formula serde schema. This is the
    // full ordered conjunction, not an arithmetic window or parsed substitute.
    encoded_hash(&original, MAX_ORIGINAL_BYTES)?;
    serde_json::to_vec(original).map_err(|error| error.to_string())
}

fn capture(cohort: &Cohort, checked: &CheckedTerms) -> Result<FormulaEvidence, String> {
    let mut declarations = Vec::with_capacity(checked.strings.len() + checked.declarations.len());
    for (name, value) in &checked.strings {
        declarations.push(Declaration::Definition {
            name: name.clone(),
            level_params: vec![],
            type_: Expr::const_str("String"),
            value: Expr::str_lit(value),
            is_reducible: true,
        });
    }
    declarations.extend(checked.declarations.iter().cloned());
    let Declaration::Theorem { value, .. } = &checked.relation else {
        return Err("FMREL: checked relation is not a theorem".into());
    };
    Ok(FormulaEvidence {
        cohort_sha256: COHORT_SHA256.into(),
        foundations: cohort.foundations.clone(),
        declarations: encode_island_declarations_v1(&declarations)?,
        relation: encode_clean_expr_dag_v2(value)?,
        preconditions: None,
    })
}

fn restore(
    cohort: &Cohort,
    environment: &mut Environment,
    evidence: &FormulaEvidence,
) -> Result<Expr, String> {
    if evidence.cohort_sha256 != COHORT_SHA256 || evidence.foundations != cohort.foundations {
        return Err("FMREL: retained cohort differs from canonical artifact pin".into());
    }
    let declarations = decode_island_declarations_v1(&evidence.declarations)?;
    let mut strings = BTreeMap::new();
    let mut bank = Vec::new();
    for declaration in declarations {
        if let Declaration::Definition { name, level_params, type_, value, is_reducible } =
            &declaration
        {
            if matches!(name.inner(), NameInner::Str(parent, _) if **parent == Name::from_string("Trust.Fmrel.Input"))
            {
                if !bank.is_empty()
                    || !level_params.is_empty()
                    || *type_ != Expr::const_str("String")
                    || !*is_reducible
                {
                    return Err("FMREL: retained String DATA declaration differs".into());
                }
                let ExprKind::Lit(Literal::String(value)) = value.kind() else {
                    return Err("FMREL: retained String DATA is not literal data".into());
                };
                if strings.insert(name.clone(), value.to_string()).is_some() {
                    return Err("FMREL: retained String DATA name repeats".into());
                }
                continue;
            }
        }
        bank.push(declaration);
    }
    admission::admit(environment, &strings, &bank)?;
    decode_clean_expr_dag_v2(&evidence.relation)
}

fn environment_identity(
    environment: &Environment,
    evidence: &FormulaEvidence,
) -> Result<String, String> {
    encoded_hash(&(FORMULA_RECIPE, environment.mode(), evidence), MAX_WIRE_BYTES)
        .map(|(digest, _)| digest)
}

pub(super) fn produce(
    original: &[(Formula, Formula)],
) -> Result<CheckedOriginalConjunction, String> {
    crate::verify_output_instantiate::on_kernel_stack(|| produce_inner(original))
}

fn produce_inner(original: &[(Formula, Formula)]) -> Result<CheckedOriginalConjunction, String> {
    #[cfg(any(test, feature = "test-hooks"))]
    super::super::require_production_allowed();
    let bytes = original_bytes(original)?;
    let context = context(original)?;
    let cohort = Cohort::configured()?;
    let advice = crate::verify_output_instantiate::formula_advice(original, cohort.environment())?;
    let checked = cohort.prove_advice(&bytes, advice)?;
    let evidence = capture(cohort, &checked)?;
    let Declaration::Theorem { type_: goal, value: proof, .. } = &checked.theorem else {
        return Err("FMREL: final source admission did not retain a theorem".into());
    };
    let terms = RetainedTerms::capture_formula(goal, proof)?;
    let (goal_sha256, proof_sha256) = terms.formula_digests()?;
    let packet = OriginalConjunctionPacket {
        model: FORMULA_MODEL,
        original: original.to_vec(),
        original_sha256: encoded_hash(&original, MAX_ORIGINAL_BYTES)?.0,
        context_sha256: encoded_hash(&context, MAX_ORIGINAL_BYTES)?.0,
        context,
        terms,
        goal_sha256,
        proof_sha256,
        environment_sha256: environment_identity(cohort.environment(), &evidence)?,
        environment_mode: format!("{:?}", cohort.environment().mode()),
        environment_recipe: FORMULA_RECIPE.into(),
        kernel_version: clean_kernel::VERSION.into(),
        formula_evidence: Some(evidence),
    };
    packet.validate()?;
    Ok(CheckedOriginalConjunction { label: packet.label(), packet: Arc::new(packet) })
}

pub(super) fn replay(
    packet: &OriginalConjunctionPacket,
    original: &[(Formula, Formula)],
) -> Result<CheckedOriginalConjunction, String> {
    crate::verify_output_instantiate::on_kernel_stack(|| replay_inner(packet, original))
}

fn replay_inner(
    packet: &OriginalConjunctionPacket,
    original: &[(Formula, Formula)],
) -> Result<CheckedOriginalConjunction, String> {
    if packet.context != context(original)? {
        return Err("FMREL: independently expected typed original context differs".into());
    }
    let bytes = original_bytes(original)?;
    let cohort = Cohort::configured()?;
    let evidence = packet.formula_evidence.as_ref().ok_or("FMREL: missing retained evidence")?;
    if packet.environment_sha256 != environment_identity(cohort.environment(), evidence)?
        || packet.environment_mode != format!("{:?}", cohort.environment().mode())
        || packet.kernel_version != clean_kernel::VERSION
    {
        return Err("FMREL: actual canonical kernel/cohort identity differs".into());
    }
    let mut environment = cohort.environment().clone();
    Cohort::install_input(&mut environment, &bytes)?;
    let relation = restore(cohort, &mut environment, evidence)?;
    cohort.check_relation(
        &environment,
        &bytes,
        Name::from_string("Trust.Fmrel.SourceGoalRelation"),
        relation,
    )?;
    let (goal, proof) = packet.terms.restore()?;
    let (expected, _) = Cohort::expected_goals(&environment, &bytes)?;
    let (goal_sha256, proof_sha256) = packet.terms.formula_digests()?;
    if goal != expected || goal_sha256 != packet.goal_sha256 || proof_sha256 != packet.proof_sha256
    {
        return Err("FMREL: retained final goal/proof/original binding differs".into());
    }
    admission::final_theorem(cohort, &environment, &bytes, proof)?;
    Ok(CheckedOriginalConjunction { label: packet.label(), packet: Arc::new(packet.clone()) })
}

/// These are additional universally proved canonical Formula statements,
/// not solver answers or assumptions. The original ordered conjunction stays
/// unchanged. A single auxiliary packet is allowed, with no nested auxiliaries.
pub(super) fn produce_with_preconditions(
    original: &[(Formula, Formula)],
    preconditions: &[(Formula, Formula)],
) -> Result<CheckedOriginalConjunction, String> {
    let conditions = produce(preconditions)?;
    let checked = produce(original)?;
    let mut packet = checked.packet().clone();
    let evidence = packet.formula_evidence.as_mut().ok_or("FMREL: missing evidence")?;
    evidence.preconditions =
        Some(serde_json::to_vec(conditions.packet()).map_err(|error| error.to_string())?);
    packet.environment_sha256 =
        environment_identity(Cohort::configured()?.environment(), evidence)?;
    packet.validate()?;
    Ok(CheckedOriginalConjunction { label: packet.label(), packet: Arc::new(packet) })
}

pub(super) fn replay_with_preconditions(
    packet: &OriginalConjunctionPacket,
    original: &[(Formula, Formula)],
    preconditions: &[(Formula, Formula)],
) -> Result<CheckedOriginalConjunction, String> {
    if packet.original != original {
        return Err("FMREL: independently expected original conjunction differs".into());
    }
    let bytes = packet
        .formula_evidence
        .as_ref()
        .and_then(|evidence| evidence.preconditions.as_ref())
        .ok_or("FMREL: checked retained preconditions are missing")?;
    if bytes.len() > MAX_WIRE_BYTES {
        return Err("FMREL: retained precondition byte bound".into());
    }
    let conditions: OriginalConjunctionPacket =
        serde_json::from_slice(bytes).map_err(|error| error.to_string())?;
    if conditions.model != FORMULA_MODEL
        || conditions
            .formula_evidence
            .as_ref()
            .is_none_or(|evidence| evidence.preconditions.is_some())
    {
        return Err("FMREL: nested or noncanonical retained preconditions".into());
    }
    conditions.replay(preconditions)?;
    replay(packet, original)
}
