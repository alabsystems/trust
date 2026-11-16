// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0 OR MIT.
//! Exact scoped inputs to candidate-only composition. The compiler checks each
//! callee's original-body rows before supplying these values. Synthesis grants
//! no proof authority to the resulting caller.

use super::*;

/// Candidate-only call input. The compiler must check all original callee rows
/// before installation; this carrier itself grants no proof authority.
#[derive(Clone, Debug)]
pub struct InferredReturnCall {
    identity: trust_types::CalleeIdentity,
    inferred: InferredReturn,
}

impl PartialEq for InferredReturnCall {
    fn eq(&self, other: &Self) -> bool {
        self.identity == other.identity
            && self.inferred.def_path == other.inferred.def_path
            && self.inferred.param_names == other.inferred.param_names
            && self.inferred.postcondition == other.inferred.postcondition
            && self.inferred.entry_bindings == other.inferred.entry_bindings
    }
}
impl Eq for InferredReturnCall {}

impl InferredReturnCall {
    /// Input supplied only after the compiler kernel-checks EVERY original-body
    /// row, including exhaustive-match obligations. The identity must be the
    /// extractor's exact monomorphic item identity, never a parsed name.
    pub fn new(identity: trust_types::CalleeIdentity, inferred: &InferredReturn) -> Option<Self> {
        let bindings = inferred.entry_bindings.as_ref()?;
        result_expression(&inferred.postcondition, &crate::sort_for_ty(&bindings.return_ty))?;
        (!inferred.check_vcs.is_empty()).then(|| Self { identity, inferred: inferred.clone() })
    }

    pub fn identity(&self) -> trust_types::CalleeIdentity {
        self.identity
    }
    pub(crate) fn name(&self) -> &str {
        &self.inferred.def_path
    }

    /// Structural check only: replacements checks enum origins using this same
    /// whole-body pure-call scan, so invoking it here would recurse.
    pub(crate) fn admits(&self, function: &VerifiableFunction, call: &Terminator) -> bool {
        let Terminator::Call {
            func,
            args,
            dest,
            target: Some(_),
            is_foreign: false,
            is_unsafe_sig: false,
            callee_identity: Some(identity),
            ..
        } = call
        else {
            return false;
        };
        let Some(bindings) = &self.inferred.entry_bindings else { return false };
        *identity == self.identity
            && *func == self.inferred.def_path
            && dest.projections.is_empty()
            && !(1..=function.body.arg_count).contains(&dest.local)
            && local_ty(function, dest.local) == Some(&bindings.return_ty)
            && args.len() == bindings.parameters.len()
            && args.iter().zip(&bindings.parameters).all(|(actual, (_, expected))| {
                matches!(actual, Operand::Copy(place) | Operand::Move(place)
                    if crate::place_ty(function, place).as_ref() == Some(expected))
                    || bindings.scalar_constant(function, actual, expected).is_some()
            })
    }

    pub(super) fn value(
        &self,
        function: &VerifiableFunction,
        call: &Terminator,
    ) -> Result<Formula, &'static str> {
        if !self.admits(function, call) {
            return Err("call does not match the inferred callee identity and types");
        }
        let Terminator::Call { args, dest, .. } = call else {
            return Err("call does not match the inferred callee identity and types");
        };
        let replacements = self
            .inferred
            .entry_bindings
            .as_ref()
            .and_then(|bindings| bindings.replacements(function, args, dest))
            .ok_or("inferred callee actual is not an immutable typed value")?;
        let bindings = self
            .inferred
            .entry_bindings
            .as_ref()
            .ok_or("inferred callee has no typed entry binding")?;
        let expression = result_expression(
            &self.inferred.postcondition,
            &crate::sort_for_ty(&bindings.return_ty),
        )
        .ok_or("inferred callee has no unique scalar return equation")?;
        Ok(super::super::callsite::substitute_summary_params(expression, &replacements))
    }

    /// Rebind the exact callee expression to the caller's current scalar state.
    /// Both scalar and enum candidates use this one call-composition rule.
    pub(super) fn value_in_state<'a>(
        &self,
        function: &VerifiableFunction,
        call: &Terminator,
        values: impl IntoIterator<Item = (usize, &'a Formula)>,
    ) -> Result<Formula, &'static str> {
        let value = self.value(function, call)?;
        let replacements = values
            .into_iter()
            .filter_map(|(local, value)| {
                let Formula::Var(name, _) =
                    operand_to_formula(function, &Operand::Copy(Place::local(local)))
                else {
                    return None;
                };
                Some((name, value.clone()))
            })
            .collect::<Vec<_>>();
        let value = super::super::callsite::substitute_summary_params(&value, &replacements);
        if node_count_exceeds(&value, INFERRED_RETURN_MAX_NODES) {
            return Err("inferred expression too large");
        }
        Ok(value)
    }

    fn summary(&self) -> crate::FunctionSummary {
        crate::FunctionSummary::new(self.name()).with_body_inferred_return(&self.inferred)
    }
}

fn result_expression<'a>(formula: &'a Formula, expected: &Sort) -> Option<&'a Formula> {
    if let Formula::Eq(lhs, rhs) = formula {
        return matches!(&**lhs, Formula::Var(name, sort) if name == "_0" && sort == expected)
            .then_some(&**rhs);
    }
    let Formula::And(terms) = formula else { return None };
    let mut expressions = terms.iter().filter_map(|term| match term {
        Formula::Eq(lhs, rhs) if matches!(&**lhs, Formula::Var(name, sort) if name == "_0" && sort == expected) => Some(&**rhs),
        _ => None,
    });
    let value = expressions.next()?;
    expressions.next().is_none().then_some(value)
}

pub(crate) fn database(function: &VerifiableFunction) -> Option<crate::SummaryDatabase> {
    let mut database = crate::SummaryDatabase::new();
    let mut names = FxHashMap::default();
    for block in &function.body.blocks {
        if !matches!(block.terminator, Terminator::Call { .. }) {
            continue;
        }
        let call = crate::inferred_return_call_for(function, &block.terminator)?;
        // The downstream database is name-keyed. Even exact per-call identity
        // checks cannot permit two different bodies to overwrite one name.
        if names
            .insert(call.name().to_owned(), call.identity())
            .is_some_and(|previous| previous != call.identity())
        {
            return None;
        }
        // Both candidate evaluation and the ORIGINAL-body injector use the
        // same typed-actual binding gate.
        call.value(function, &block.terminator).ok()?;
        database.insert(call.summary());
    }
    (!database.is_empty()).then_some(database)
}
