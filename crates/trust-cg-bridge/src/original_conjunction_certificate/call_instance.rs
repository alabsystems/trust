//! Closed, typed instantiation of an already checked original conjunction.
//!
//! This module authenticates no call site and grants no caller verdict. Its
//! input token must already be checked; the call-site owner independently binds
//! the total Formula substitution to actual source/machine inputs and subjects.

use std::collections::BTreeMap;

use trust_types::Formula;

use super::CheckedOriginalConjunction;

#[cfg(not(feature = "kernel-recheck"))]
pub(crate) fn specialize_original_for_call(
    _checked: &CheckedOriginalConjunction,
    _typed_var_subst: &BTreeMap<String, Formula>,
    _reflexive_bindings: &[(Formula, Formula)],
) -> Result<CheckedOriginalConjunction, String> {
    Err("original call instance: kernel-recheck feature unavailable".into())
}

#[cfg(not(feature = "kernel-recheck"))]
pub(crate) fn specialize_original_for_expected_transition(
    _checked: &CheckedOriginalConjunction,
    _typed_var_subst: &BTreeMap<String, Formula>,
    _reflexive_bindings: &[(Formula, Formula)],
    _expected_original: &[(Formula, Formula)],
) -> Result<CheckedOriginalConjunction, String> {
    Err("original tail transition: kernel-recheck feature unavailable".into())
}

#[cfg(feature = "kernel-recheck")]
pub(crate) use kernel::{
    specialize_original_for_call, specialize_original_for_expected_transition,
};

#[cfg(feature = "kernel-recheck")]
mod kernel {
    use std::collections::BTreeSet;

    use clean_kernel::{Expr, ExprFolderOpt, ExprKind, LevelVec, Name};
    use trust_types::Sort;

    use super::*;
    use crate::original_conjunction_certificate::{
        MAX_ORIGINAL_BYTES, SymbolicContext, check_supplied, encoded_hash, environment,
        require_environment,
    };
    use crate::verify_output_instantiate::{
        OriginalParameterRole, original_conjunction_goal, original_parameter_roles,
        original_reflexive_equation, run_recheck_thread,
    };

    fn validate_total_substitution(
        context: &SymbolicContext,
        substitutions: &BTreeMap<String, Formula>,
    ) -> Result<(), String> {
        if context.sorts.len() != substitutions.len()
            || !context.sorts.keys().eq(substitutions.keys())
        {
            return Err(
                "original call instance: substitution must cover exactly every typed variable"
                    .into(),
            );
        }
        for (variable, sort) in &context.sorts {
            let replacement = &substitutions[variable];
            let supported = match (sort, replacement) {
                (Sort::BitVec(width), Formula::Var(_, Sort::BitVec(actual))) => {
                    (1..=128).contains(width) && width == actual
                }
                (Sort::BitVec(width), Formula::BitVec { width: actual, .. }) => {
                    (1..=128).contains(width) && width == actual
                }
                (Sort::Array(address, byte), Formula::Var(_, actual)) => {
                    **address == Sort::BitVec(64) && **byte == Sort::BitVec(8) && sort == actual
                }
                _ => false,
            };
            if !supported {
                return Err(format!(
                    "original call instance: unsupported or wrong-sort substitution for {variable:?}"
                ));
            }
        }
        Ok(())
    }

    fn substitute(formula: &Formula, substitutions: &BTreeMap<String, Formula>) -> Formula {
        // Formula has no binders in this bounded fragment. The renderer checks
        // all original widths/sorts before and after this simultaneous map.
        formula.clone().map(&mut |node| match node {
            Formula::Var(ref variable, _) => substitutions[variable].clone(),
            _ => node,
        })
    }

    fn data_replacements(
        source: &SymbolicContext,
        caller: &SymbolicContext,
        substitutions: &BTreeMap<String, Formula>,
    ) -> Result<BTreeMap<Name, Expr>, String> {
        let source_roles = original_parameter_roles(source)
            .ok_or("original call instance: source data role manifest mismatch")?;
        let caller_roles = original_parameter_roles(caller)
            .ok_or("original call instance: caller data role manifest mismatch")?;
        let caller_names: BTreeMap<_, _> =
            caller_roles.into_iter().map(|(name, role)| (role, name)).collect();
        let mut replacements = BTreeMap::new();
        for (name, role) in &source_roles {
            let replacement = match role {
                OriginalParameterRole::ScalarBit { variable, width, bit } => {
                    match &substitutions[variable] {
                        Formula::Var(actual, _) => {
                            let role = OriginalParameterRole::ScalarBit {
                                variable: actual.clone(),
                                width: *width,
                                bit: *bit,
                            };
                            Expr::const_(
                                caller_names
                                    .get(&role)
                                    .ok_or("original call instance: missing caller scalar bit")?
                                    .clone(),
                                vec![],
                            )
                        }
                        Formula::BitVec { value, .. } => {
                            Expr::const_str(if ((*value >> *bit) & 1) == 1 {
                                "Bool.true"
                            } else {
                                "Bool.false"
                            })
                        }
                        _ => {
                            return Err(
                                "original call instance: unsupported scalar data replacement"
                                    .into(),
                            );
                        }
                    }
                }
                OriginalParameterRole::ArrayBit { variable, bit } => {
                    let Formula::Var(actual, _) = &substitutions[variable] else {
                        return Err(
                            "original call instance: unsupported array data replacement".into()
                        );
                    };
                    let role =
                        OriginalParameterRole::ArrayBit { variable: actual.clone(), bit: *bit };
                    Expr::const_(
                        caller_names
                            .get(&role)
                            .ok_or("original call instance: missing caller array bit")?
                            .clone(),
                        vec![],
                    )
                }
            };
            replacements.insert(name.clone(), replacement);
        }
        validate_data_replacements(&source_roles, caller, &replacements)?;
        Ok(replacements)
    }

    /// Only exact declared data constants can be replaced. The bounded public
    /// Formula API constructs these closed terms; this second guard also makes
    /// accidental open/prelude/role-confused internal replacements decline.
    fn validate_data_replacements(
        source_roles: &BTreeMap<Name, OriginalParameterRole>,
        caller: &SymbolicContext,
        replacements: &BTreeMap<Name, Expr>,
    ) -> Result<(), String> {
        if !source_roles.keys().eq(replacements.keys()) {
            return Err(
                "original call instance: partial or extra data-constant substitution".into()
            );
        }
        let bool_names: BTreeSet<_> =
            caller.bits.iter().map(|name| Name::from_string(name)).collect();
        let array_names: BTreeSet<_> =
            caller.memories.iter().map(|name| Name::from_string(name)).collect();
        for (name, role) in source_roles {
            let expression = &replacements[name];
            if expression.has_loose_bvars_quick() || expression.has_fvar_quick() {
                return Err("original call instance: open data replacement".into());
            }
            let ExprKind::Const(actual, universes) = expression.kind() else {
                return Err("original call instance: unsupported data replacement term".into());
            };
            let typed = universes.is_empty()
                && match role {
                    OriginalParameterRole::ScalarBit { .. } => {
                        bool_names.contains(actual)
                            || *actual == Name::from_string("Bool.true")
                            || *actual == Name::from_string("Bool.false")
                    }
                    OriginalParameterRole::ArrayBit { .. } => array_names.contains(actual),
                };
            if !typed {
                return Err(
                    "original call instance: wrong-sort, prelude or undeclared data replacement"
                        .into(),
                );
            }
        }
        Ok(())
    }

    struct ClosedDataTransport<'a> {
        replacements: &'a BTreeMap<Name, Expr>,
        invalid_universes: bool,
    }
    impl ExprFolderOpt for ClosedDataTransport<'_> {
        fn fold_const_opt(&mut self, name: &Name, universes: &LevelVec) -> Option<Expr> {
            let replacement = self.replacements.get(name)?;
            if !universes.is_empty() {
                self.invalid_universes = true;
                return None;
            }
            // All replacements are closed: no lifting or binder-depth-specific
            // rewrite is needed under the retained proof's Lam/Pi/BVar nodes.
            Some(replacement.clone())
        }
    }

    #[cfg(test)]
    pub(super) fn test_replacement_guards() {
        use clean_kernel::{FVarId, Level};
        let value = Formula::Var("v".into(), Sort::BitVec(8));
        let read = Formula::Select(
            Box::new(Formula::Var(
                "m".into(),
                Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(8))),
            )),
            Box::new(Formula::Var("q".into(), Sort::BitVec(64))),
        );
        let (_, context) =
            original_conjunction_goal(&[(value.clone(), value), (read.clone(), read)]).unwrap();
        let roles = original_parameter_roles(&context).unwrap();
        let valid: BTreeMap<_, _> =
            roles.keys().map(|name| (name.clone(), Expr::const_(name.clone(), vec![]))).collect();
        validate_data_replacements(&roles, &context, &valid).unwrap();
        let scalar = roles
            .iter()
            .find(|(_, role)| matches!(role, OriginalParameterRole::ScalarBit { .. }))
            .unwrap()
            .0;
        let array = roles
            .iter()
            .find(|(_, role)| matches!(role, OriginalParameterRole::ArrayBit { .. }))
            .unwrap()
            .0;
        for expression in [
            Expr::bvar(0),
            Expr::fvar(FVarId::new(99)),
            Expr::const_str("Eq"),
            Expr::const_(array.clone(), vec![]),
            Expr::const_(scalar.clone(), vec![Level::zero()]),
            Expr::app(Expr::const_str("Bool.not"), Expr::const_str("Bool.true")),
        ] {
            let mut mutant = valid.clone();
            mutant.insert(scalar.clone(), expression);
            assert!(validate_data_replacements(&roles, &context, &mutant).is_err());
        }
        let mut mutant = valid.clone();
        mutant.remove(scalar);
        assert!(validate_data_replacements(&roles, &context, &mutant).is_err());
        let mut mutant = valid.clone();
        mutant.insert(Name::from_string("Eq"), Expr::const_str("Bool.true"));
        assert!(validate_data_replacements(&roles, &context, &mutant).is_err());
        let mut mutant = valid;
        mutant.insert(array.clone(), Expr::const_(scalar.clone(), vec![]));
        assert!(validate_data_replacements(&roles, &context, &mutant).is_err());
    }

    #[cfg(test)]
    pub(super) fn test_capture_safety() {
        use clean_kernel::{BinderInfo, Level};

        use crate::verify_output_instantiate::kx;
        let name = Name::from_string("BVC_EQBIT_exact");
        let replacement = Expr::const_str("Bool.true");
        let replacements = BTreeMap::from([(name.clone(), replacement.clone())]);
        let data = Expr::const_(name.clone(), vec![]);
        let term = Expr::lam(BinderInfo::Default, kx::bool_ty(), Expr::app(data, Expr::bvar(0)));
        let mut transport =
            ClosedDataTransport { replacements: &replacements, invalid_universes: false };
        let result = transport.fold_expr_opt(&term).unwrap();
        assert_eq!(
            result,
            Expr::lam(BinderInfo::Default, kx::bool_ty(), Expr::app(replacement, Expr::bvar(0)))
        );
        assert!(!result.has_loose_bvars_quick());
        let wrong = Expr::const_(name, vec![Level::zero()]);
        assert!(transport.fold_expr_opt(&wrong).is_none());
        assert!(transport.invalid_universes);
        // Full Name parts matter, including numeric components.
        let numeric = Expr::const_(Name::anon().str("BVC_EQBIT_exact").num(7), vec![]);
        assert!(transport.fold_expr_opt(&numeric).is_none());
    }

    pub(crate) fn specialize_original_for_call(
        checked: &CheckedOriginalConjunction,
        typed_var_subst: &BTreeMap<String, Formula>,
        reflexive_bindings: &[(Formula, Formula)],
    ) -> Result<CheckedOriginalConjunction, String> {
        specialize_inner(checked, typed_var_subst, reflexive_bindings, None)
    }

    /// The caller owner must independently reconstruct the COMPLETE original
    /// transition. Equality is checked before the single fresh kernel check;
    /// an instance statement or favorable label cannot replace that goal.
    pub(crate) fn specialize_original_for_expected_transition(
        checked: &CheckedOriginalConjunction,
        typed_var_subst: &BTreeMap<String, Formula>,
        reflexive_bindings: &[(Formula, Formula)],
        expected_original: &[(Formula, Formula)],
    ) -> Result<CheckedOriginalConjunction, String> {
        specialize_inner(checked, typed_var_subst, reflexive_bindings, Some(expected_original))
    }

    fn specialize_inner(
        checked: &CheckedOriginalConjunction,
        typed_var_subst: &BTreeMap<String, Formula>,
        reflexive_bindings: &[(Formula, Formula)],
        expected_original: Option<&[(Formula, Formula)]>,
    ) -> Result<CheckedOriginalConjunction, String> {
        let packet = checked.packet();
        packet.validate()?;
        if packet
            .original
            .len()
            .checked_add(reflexive_bindings.len())
            .is_none_or(|count| count > crate::original_conjunction_certificate::MAX_CONJUNCTS)
        {
            return Err("original call instance: conjunction population bound".into());
        }
        validate_total_substitution(&packet.context, typed_var_subst)?;
        let (original_goal, original_context) =
            crate::verify_output_instantiate::original_conjunction_goal_version(
                &packet.original,
                packet.model,
            )
            .ok_or("original call instance: original goal cannot be independently rendered")?;
        if original_context != packet.context {
            return Err("original call instance: original typed context mismatch".into());
        }
        require_environment(packet, &environment(&original_context, packet.model)?)?;
        let (retained_goal, retained_proof) = packet.terms.restore()?;
        if retained_goal != original_goal
            || encoded_hash(&retained_goal, 64 * 1024 * 1024)?.0 != packet.goal_sha256
            || encoded_hash(&retained_proof, 64 * 1024 * 1024)?.0 != packet.proof_sha256
        {
            return Err(
                "original call instance: retained original goal/proof binding mismatch".into()
            );
        }
        let mapped: Vec<_> = packet
            .original
            .iter()
            .map(|(left, right)| {
                (substitute(left, typed_var_subst), substitute(right, typed_var_subst))
            })
            .collect();
        encoded_hash(&mapped, MAX_ORIGINAL_BYTES)?;
        let (mut tail_goal, _) = original_conjunction_goal(&mapped)
            .ok_or("original call instance: mapped leaf goal cannot be rendered")?;
        let mut original = Vec::with_capacity(reflexive_bindings.len() + mapped.len());
        for (left, right) in reflexive_bindings {
            if left != right {
                return Err("original call instance: non-reflexive actual binding".into());
            }
            original.push((left.clone(), right.clone()));
        }
        original.extend(mapped);
        if let Some(expected) = expected_original {
            if expected != original {
                return Err("original tail transition: independently reconstructed complete caller goal differs from retained-proof specialization".into());
            }
        }
        encoded_hash(&original, MAX_ORIGINAL_BYTES)?;
        let (expected, caller_context) = original_conjunction_goal(&original)
            .ok_or("original call instance: full caller goal cannot be rendered")?;
        let replacements = data_replacements(&original_context, &caller_context, typed_var_subst)?;
        let mut transport =
            ClosedDataTransport { replacements: &replacements, invalid_universes: false };
        let mut proof = transport.fold_expr_opt(&retained_proof).unwrap_or(retained_proof);
        if transport.invalid_universes {
            return Err("original call instance: data constant has unexpected universes".into());
        }
        for (left, _) in reflexive_bindings.iter().rev() {
            let (binding_goal, binding_proof) = original_reflexive_equation(left)
                .ok_or("original call instance: reflexive binding cannot be rendered")?;
            proof = Expr::apps(
                Expr::const_str("And.intro"),
                [binding_goal.clone(), tail_goal.clone(), binding_proof, proof],
            );
            tail_goal = Expr::apps(Expr::const_str("And"), [binding_goal, tail_goal]);
        }
        if tail_goal != expected {
            return Err("original call instance: full original binding goal mismatch".into());
        }
        // No production/replayer/solver entry. The exact freshly rendered full
        // goal includes every original equation and every original query bit.
        // For scalar constants, bvfEval of Leaf(bits) and Const(bits) must be
        // established definitionally by this single whole-goal kernel check.
        run_recheck_thread("trust-call-original-CIC", move || {
            #[cfg(test)]
            {
                crate::original_conjunction_certificate::without_production(|| {
                    check_supplied(&original, &expected, &proof)
                })
            }
            #[cfg(not(test))]
            check_supplied(&original, &expected, &proof)
        })
        .map_err(|error| format!("original call instance: checker thread {error:?}"))?
    }
}

#[cfg(all(test, feature = "kernel-recheck"))]
mod tests {
    use trust_types::Sort;

    use super::*;
    use crate::original_conjunction_certificate::without_production;
    use crate::verify_output_instantiate::{
        OriginalParameterRole, original_conjunction_goal, original_parameter_roles,
        try_original_conjunction_discharge,
    };

    fn v(name: &str, width: u32) -> Formula {
        Formula::Var(name.into(), Sort::BitVec(width))
    }
    fn m(name: &str) -> Formula {
        Formula::Var(
            name.into(),
            Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(8))),
        )
    }
    fn read(memory: Formula, query: Formula) -> Formula {
        Formula::Select(Box::new(memory), Box::new(query))
    }
    fn items() -> Vec<(Formula, Formula)> {
        let byte = Formula::BvExtract { inner: Box::new(v("wide", 128)), high: 7, low: 0 };
        let memory = Formula::Store(Box::new(m("memory")), Box::new(v("x", 64)), Box::new(byte));
        let read = read(memory, v("query", 64));
        vec![
            (v("x", 64), v("x", 64)),
            (v("y", 64), v("y", 64)),
            (v("wide", 128), v("wide", 128)),
            (read.clone(), read),
        ]
    }
    fn checked() -> CheckedOriginalConjunction {
        try_original_conjunction_discharge(&items()).expect("actual initial original CIC check")
    }
    fn identity(checked: &CheckedOriginalConjunction) -> BTreeMap<String, Formula> {
        checked
            .variable_sorts()
            .iter()
            .map(|(name, sort)| (name.clone(), Formula::Var(name.clone(), sort.clone())))
            .collect()
    }

    #[test]
    fn original_call_transport_preserves_all_items_aliases_query_and_128bit_constants() {
        let checked = checked();
        let mut substitutions = identity(&checked);
        substitutions.insert("x".into(), v("caller-shared", 64));
        substitutions.insert("y".into(), v("caller-shared", 64));
        substitutions.insert("query".into(), v("caller-fresh-query", 64));
        substitutions.insert("memory".into(), m("caller-memory"));
        substitutions
            .insert("wide".into(), Formula::BitVec { value: i128::MIN | 0x81, width: 128 });
        let bindings = vec![(v("caller-shared", 64), v("caller-shared", 64))];
        let instance = without_production(|| {
            specialize_original_for_call(&checked, &substitutions, &bindings)
        })
        .unwrap();
        assert_eq!(instance.original_equations().len(), checked.original_equations().len() + 1);
        assert_eq!(&instance.original_equations()[..1], bindings);
        assert_eq!(instance.original_equations()[1], instance.original_equations()[2]);
        assert_eq!(
            instance.original_equations()[3],
            (
                Formula::BitVec { value: i128::MIN | 0x81, width: 128 },
                Formula::BitVec { value: i128::MIN | 0x81, width: 128 },
            )
        );
        let roles = original_parameter_roles(&instance.packet().context).unwrap();
        assert_eq!(roles.values().filter(|role| matches!(role,
            OriginalParameterRole::ScalarBit { variable, width: 64, .. } if variable == "caller-fresh-query"
        )).count(), 64);
        assert_eq!(instance.packet().context.memories.len(), 8);
        assert_eq!(instance.variable_sorts().len(), 3);
        assert!(!instance.variable_sorts().contains_key("wide"));
        // Captured full-goal terms remain ordinary bounded replayable evidence.
        without_production(|| instance.packet().replay(instance.original_equations())).unwrap();
    }

    #[test]
    fn original_call_transport_declines_missing_extra_wrong_sort_unsupported_and_nonreflexive() {
        let checked = checked();
        let valid = identity(&checked);
        let mut mutants = Vec::new();
        let mut changed = valid.clone();
        changed.remove("query");
        mutants.push(changed);
        let mut changed = valid.clone();
        changed.insert("extra".into(), v("caller-extra", 64));
        mutants.push(changed);
        for replacement in [
            v("caller-query", 63),
            Formula::BitVec { value: 1, width: 32 },
            Formula::BvAdd(Box::new(v("caller-query", 64)), Box::new(v("other", 64)), 64),
            m("array-in-scalar-slot"),
        ] {
            let mut changed = valid.clone();
            changed.insert("query".into(), replacement);
            mutants.push(changed);
        }
        let mut changed = valid.clone();
        changed.insert("memory".into(), v("scalar-in-array-slot", 64));
        mutants.push(changed);
        for mutant in mutants {
            assert!(
                without_production(|| specialize_original_for_call(&checked, &mutant, &[]))
                    .is_err()
            );
        }
        assert!(
            without_production(|| specialize_original_for_call(
                &checked,
                &valid,
                &[(v("x", 64), v("y", 64))]
            ))
            .is_err()
        );
    }

    #[test]
    fn original_manifest_is_exact_injective_and_keeps_2056_data_parameters_without_telescope() {
        let mut items: Vec<_> = (0..16)
            .map(|index| {
                let value = v(&format!("BVC_EQBIT_odd.name_bit{index}_λ"), 128);
                (value.clone(), value)
            })
            .collect();
        // 2048 scalar bits + eight functions; no Pi/Lam per scalar bit.
        // Use an existing scalar's low64 as the query without adding a
        // separate parameter to this manifest population control.
        let query = Formula::BvExtract {
            inner: Box::new(v("BVC_EQBIT_odd.name_bit0_λ", 128)),
            high: 63,
            low: 0,
        };
        let memory = read(m("array_bit7.λ"), query);
        items.push((memory.clone(), memory));
        let (_, context) = original_conjunction_goal(&items).unwrap();
        let roles = original_parameter_roles(&context).unwrap();
        assert_eq!(roles.len(), 2056);
        assert_eq!(context.bits.len(), 2048);
        assert_eq!(context.memories.len(), 8);
        let mut bad = context.clone();
        bad.bits.pop_first();
        assert!(original_parameter_roles(&bad).is_none());
        let mut bad = context;
        bad.memories.insert("Eq".into());
        assert!(original_parameter_roles(&bad).is_none());
    }

    #[test]
    fn closed_data_transport_rejects_open_prelude_wrongrole_and_nonempty_universes() {
        // Internal raw-map tests do not expose an Expr substitution API.
        kernel::test_replacement_guards();
        kernel::test_capture_safety();
    }
}

#[cfg(all(test, feature = "kernel-recheck"))]
mod expected_transition_tests {
    use trust_types::Sort;

    use super::*;
    use crate::original_conjunction_certificate::without_production;
    use crate::verify_output_instantiate::try_original_conjunction_discharge;
    #[test]
    fn complete_expected_transition_is_checked_without_original_production() {
        let x = Formula::Var("tail_x".into(), Sort::BitVec(64));
        let memory = Formula::Var(
            "tail_m".into(),
            Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(8))),
        );
        let q = Formula::Var("tail_q".into(), Sort::BitVec(64));
        let read = Formula::Select(Box::new(memory), Box::new(q));
        let items = vec![(x.clone(), x.clone()), (read.clone(), read)];
        let checked = try_original_conjunction_discharge(&items).unwrap();
        let substitution = checked
            .variable_sorts()
            .iter()
            .map(|(name, sort)| (name.clone(), Formula::Var(name.clone(), sort.clone())))
            .collect();
        let binding = vec![(x.clone(), x)];
        let expected = [binding.clone(), items].concat();
        let actual = without_production(|| {
            specialize_original_for_expected_transition(
                &checked,
                &substitution,
                &binding,
                &expected,
            )
        })
        .unwrap();
        assert_eq!(actual.original_equations(), expected);
        without_production(|| actual.packet().replay(&expected)).unwrap();
        for mut mutant in [expected[..2].to_vec(), expected[1..].to_vec(), expected.clone()] {
            if mutant == expected {
                mutant.reverse();
            }
            assert!(
                without_production(|| specialize_original_for_expected_transition(
                    &checked,
                    &substitution,
                    &binding,
                    &mutant
                ))
                .is_err()
            );
        }
        let mut mutant = expected;
        mutant.last_mut().unwrap().1 = Formula::BitVec { value: 0, width: 8 };
        assert!(
            without_production(|| specialize_original_for_expected_transition(
                &checked,
                &substitution,
                &binding,
                &mutant
            ))
            .is_err()
        );
    }
}
