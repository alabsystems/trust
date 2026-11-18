// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Shared actual-kernel admission of fresh proof advice. This module never
//! invokes the old producer, a solver, or a serialized admission stamp.

use std::collections::BTreeMap;

use clean_kernel::name::NameInner;
use clean_kernel::{Declaration, Environment, Expr, Name, TypeChecker};

use super::Cohort;

fn fresh_child(name: &Name, namespace: &str) -> bool {
    matches!(name.inner(), NameInner::Str(parent, _) if **parent == Name::from_string(namespace))
}

pub(super) fn admit(
    environment: &mut Environment,
    strings: &BTreeMap<Name, String>,
    declarations: &[Declaration],
) -> Result<(), String> {
    if strings.len() > 1024 || declarations.len() > 4096 {
        return Err("FMREL: advice declaration/data population bound".into());
    }
    let mut total = 0usize;
    for (name, value) in strings {
        total = total.checked_add(value.len()).ok_or("FMREL: String DATA size overflow")?;
        if !fresh_child(name, "Trust.Fmrel.Input")
            || environment.get_const(name).is_some()
            || value.len() > 64 * 1024
            || total > super::super::MAX_ORIGINAL_BYTES
        {
            return Err("FMREL: String DATA identity or byte bound".into());
        }
        environment
            .add_decl(Declaration::Definition {
                name: name.clone(),
                level_params: vec![],
                type_: Expr::const_str("String"),
                value: Expr::str_lit(value),
                is_reducible: true,
            })
            .map_err(|error| format!("FMREL String DATA check: {error:?}"))?;
    }
    for declaration in declarations {
        let name = match declaration {
            Declaration::Definition { name, .. } | Declaration::Theorem { name, .. } => name,
            _ => return Err("FMREL: an advice axiom or opaque declaration is unavailable".into()),
        };
        if !fresh_child(name, "Trust.Fmrel.Advice") || environment.get_const(name).is_some() {
            return Err("FMREL: advice must have a fresh declaration identity".into());
        }
        environment
            .add_decl(declaration.clone())
            .map_err(|error| format!("FMREL advice declaration check {name}: {error:?}"))?;
    }
    Ok(())
}

/// Check a supplied proof of the independently reconstructed FINAL semantic
/// source proposition. No favorable result can arise from GoalB alone.
pub(super) fn final_theorem(
    cohort: &Cohort,
    environment: &Environment,
    bytes: &[u8],
    proof: Expr,
) -> Result<Declaration, String> {
    cohort.require_canonical_source(environment)?;
    let (original, _) = Cohort::expected_goals(environment, bytes)?;
    let audit = environment.audit_certification(&original, &proof);
    if !audit.is_certified() {
        return Err(format!("FMREL final original-source certification: {:?}", audit.issues));
    }
    let theorem = Declaration::Theorem {
        name: Name::from_string("Trust.Fmrel.OriginalConjunction"),
        level_params: vec![],
        type_: original.clone(),
        value: proof.clone(),
    };
    let mut checked = environment.clone();
    checked
        .add_decl(theorem.clone())
        .map_err(|error| format!("FMREL final original-source admission: {error:?}"))?;
    let mut checker = TypeChecker::new(&checked);
    checker.set_allow_unsafe(false);
    checker.set_allow_partial(false);
    checker
        .check_type(&proof, &original)
        .map_err(|error| format!("FMREL final original-source replay: {error:?}"))?;
    Ok(theorem)
}
