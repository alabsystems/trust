// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0 OR MIT.

use super::*;

/// Immutable entry channels inferred from a real callee. The compiler must
/// certify every original-body VC before attaching these to a summary.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct EntryBindings {
    pub(super) parameters: Vec<(String, Ty)>,
    pub(super) return_ty: Ty,
    pub(super) accesses: Vec<EntryAccess>,
    pub(super) postcondition: Formula,
    pub(super) def_path: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct EntryAccess {
    pub(super) formal: usize,
    pub(super) read: EntryRead,
    pub(super) scalar_ty: Ty,
    pub(super) symbol: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum EntryRead {
    Discriminant,
    Projection(Vec<Projection>),
}

impl EntryBindings {
    /// A literal actual must retain its exact declared scalar type and range.
    /// Reuse the ordinary operand checker; symbolic and opaque values do not
    /// gain a type from the callee's expected parameter.
    pub(super) fn scalar_constant(
        &self,
        caller: &VerifiableFunction,
        argument: &Operand,
        expected: &Ty,
    ) -> Option<Formula> {
        (fragment_scalar(expected)
            && matches!(
                argument,
                Operand::Constant(ConstValue::Bool(_) | ConstValue::Int(_) | ConstValue::Uint(..))
            )
            && crate::binary_operand_matches_type(caller, argument, expected))
        .then(|| operand_to_formula(caller, argument))
    }

    /// Public summary fields may be mutated by clients. Such a mutation cannot
    /// keep a projection authorization minted for a different checked clause.
    pub(crate) fn matches_summary(&self, summary: &crate::modular::FunctionSummary) -> bool {
        summary.name == self.def_path
            && summary.preconditions.is_empty()
            && summary.postconditions.len() == 1
            && summary.postconditions.first() == Some(&self.postcondition)
            && summary.param_names.iter().eq(self.parameters.iter().map(|(name, _)| name))
    }

    pub(crate) fn names(&self) -> Vec<String> {
        self.parameters
            .iter()
            .map(|(name, _)| name.clone())
            .chain(self.accesses.iter().map(|access| access.symbol.clone()))
            .collect()
    }

    /// The shared injection/SAT-screen admission. A rejected actual must not
    /// become a determined call result merely because its callee has a summary.
    /// All outputs still pass through the established PRE-argument/POST-result
    /// statement-version oracle; this method does not mint a global fact.
    pub(crate) fn replacements(
        &self,
        caller: &VerifiableFunction,
        args: &[Operand],
        dest: &Place,
    ) -> Option<Vec<(String, Formula)>> {
        if args.len() != self.parameters.len()
            || crate::place_ty_cow(caller, dest).as_deref() != Some(&self.return_ty)
        {
            return None;
        }
        let mut actuals = Vec::with_capacity(args.len());
        let mut replacements = Vec::with_capacity(args.len() + self.accesses.len());
        for ((name, expected), argument) in self.parameters.iter().zip(args) {
            if matches!(argument, Operand::Constant(_)) {
                replacements
                    .push((name.clone(), self.scalar_constant(caller, argument, expected)?));
                actuals.push(None);
                continue;
            }
            let (Operand::Copy(place) | Operand::Move(place)) = argument else {
                // No field projections of an opaque/symbolic/constant carrier.
                return None;
            };
            if !place.projections.iter().all(|projection| {
                matches!(projection, Projection::Field(_) | Projection::Downcast(_))
            }) || crate::place_ty(caller, place).as_ref() != Some(expected)
            {
                return None;
            }
            // The canonical discriminator is a logical side channel rather
            // than a place projection. Admit it only for one immutable,
            // unaliased root: ordinary place SSA must never be mistaken for
            // versioning this separate name across a write or an escape.
            let place = if crate::enum_entry::enum_shape(expected) {
                crate::enum_entry::call_argument_origin(caller, place, expected)?
            } else {
                place.clone()
            };
            replacements
                .push((name.clone(), operand_to_formula(caller, &Operand::Copy(place.clone()))));
            actuals.push(Some(place));
        }
        for access in &self.accesses {
            let mut place = actuals.get(access.formal)?.as_ref()?.clone();
            let value = match &access.read {
                EntryRead::Discriminant => {
                    crate::enum_entry::immutable_constructor_discriminant(caller, &place)
                        .or_else(|| crate::enum_entry::entry_discriminant(caller, &place))?
                }
                EntryRead::Projection(projections) => {
                    place.projections.extend(projections.iter().cloned());
                    if crate::place_ty(caller, &place).as_ref() != Some(&access.scalar_ty) {
                        return None;
                    }
                    operand_to_formula(caller, &Operand::Copy(place))
                }
            };
            if !matches!(&value, Formula::Var(_, sort) if *sort == crate::sort_for_ty(&access.scalar_ty))
                && !matches!((&access.read, &value), (EntryRead::Discriminant, Formula::Int(_)))
            {
                return None;
            }
            replacements.push((access.symbol.clone(), value));
        }
        Some(replacements)
    }
}
