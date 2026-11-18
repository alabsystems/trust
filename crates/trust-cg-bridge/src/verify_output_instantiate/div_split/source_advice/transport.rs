// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Untrusted transport advice into the canonical Formula environment. Every
//! transported declaration and the final original-byte goal must still pass
//! the actual reference kernel; this module issues no checked token or grade.

use std::collections::BTreeMap;
use std::sync::Arc;

use clean_kernel::{BinderInfo, Expr, ExprFolderOpt, FVarId, LevelVec, Name};
use trust_types::Formula;

use super::super::super::{add_comm, kx};
use super::shared::{Memo, SharedConstFolder};

pub(crate) struct UniversalAdvice {
    pub(crate) goal: Expr,
    pub(crate) proof: Expr,
    /// Closed String data definitions to admit and retain independently.
    /// These are variable names, never opaque Formula witnesses.
    pub(crate) strings: BTreeMap<Name, String>,
}

struct Transport {
    leaves: BTreeMap<Name, Expr>,
    invalid_universes: bool,
    memo: Memo,
}

impl SharedConstFolder for Transport {
    fn child_memo(&mut self) -> &mut Memo {
        &mut self.memo
    }
}

pub(super) fn canonical_name(name: &Name) -> Name {
    static RENAMES: std::sync::OnceLock<BTreeMap<Name, Name>> = std::sync::OnceLock::new();
    RENAMES
        .get_or_init(|| {
            [
                ("Bool.xor", "TrustIr.Formula.V1.Compat.xor"),
                ("Nat.div_add_mod", "TrustIr.Formula.V1.Compat.Nat.div_add_mod"),
                ("Nat.mul_succ", "TrustIr.Formula.V1.Compat.Nat.mul_succ"),
                ("Nat.succ_mul", "TrustIr.Formula.V1.Compat.Nat.succ_mul"),
            ]
            .into_iter()
            .map(|(source, target)| (Name::from_string(source), Name::from_string(target)))
            .collect()
        })
        .get(name)
        .cloned()
        .unwrap_or_else(|| name.clone())
}

impl ExprFolderOpt for Transport {
    fn fold_expr_arc_opt(&mut self, expr: &Arc<Expr>) -> Option<Arc<Expr>> {
        self.fold_shared(expr)
    }

    fn fold_binder_body_arc_opt(&mut self, expr: &Arc<Expr>) -> Option<Arc<Expr>> {
        self.fold_shared(expr)
    }

    fn fold_const_opt(&mut self, name: &Name, universes: &LevelVec) -> Option<Expr> {
        if let Some(replacement) = self.leaves.get(name) {
            if !universes.is_empty() {
                self.invalid_universes = true;
                return None;
            }
            return Some(replacement.clone());
        }
        let target = canonical_name(name);
        (target != *name).then(|| Expr::const_(target, universes.clone()))
    }
}

/// Propose a universal proof over the canonical Env, replacing every old
/// scalar-bit data parameter by the corresponding actual Env projection.
/// Free-variable insertion followed by abstraction preserves nested binders;
/// this is never a direct de Bruijn substitution into the old proof.
pub(crate) fn propose(original: &[(Formula, Formula)]) -> Result<UniversalAdvice, String> {
    let advice = super::propose(original).map_err(|error| format!("{error:?}"))?;
    if advice.goal.has_fvar_quick() || advice.proof.has_fvar_quick() {
        return Err("source advice transport: unexpected pre-existing free variable".into());
    }
    let rho_id = FVarId::new(u64::MAX);
    let rho = Expr::fvar(rho_id);
    let mut leaves = BTreeMap::new();
    let mut strings = BTreeMap::new();
    for (variable, width) in &advice.leaves {
        if !(1..=64).contains(width) {
            return Err("source advice transport: unsupported variable width".into());
        }
        let string_name =
            Name::from_string("Trust.Fmrel.Input").str(format!("variable{}", strings.len()));
        strings.insert(string_name.clone(), variable.clone());
        let value = Expr::apps(
            Expr::const_str("TrustIr.Formula.V1.Env.bv"),
            [rho.clone(), Expr::const_(string_name, vec![]), kx::nat_lit(*width)],
        );
        for bit in 0..*width {
            leaves.insert(
                add_comm::bit_name(variable, *width, bit),
                Expr::apps(
                    Expr::const_str("BitVec.getLsbD"),
                    [kx::nat_lit(*width), value.clone(), kx::nat_lit(bit)],
                ),
            );
        }
    }
    let mut transport = Transport { leaves, invalid_universes: false, memo: Memo::default() };
    let goal = transport.fold_expr_opt(&advice.goal).unwrap_or(advice.goal);
    let proof = transport.fold_expr_opt(&advice.proof).unwrap_or(advice.proof);
    if transport.invalid_universes {
        return Err("source advice transport: polymorphic scalar-bit parameter".into());
    }
    let environment = Expr::const_str("TrustIr.Formula.V1.Env");
    Ok(UniversalAdvice {
        goal: Expr::pi(BinderInfo::Default, environment.clone(), goal.abstract_fvar(rho_id)),
        proof: Expr::lam(BinderInfo::Default, environment, proof.abstract_fvar(rho_id)),
        strings,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn constant_transport_preserves_changed_sharing_and_binder_identity() {
        let name = Name::from_string("input");
        let id = FVarId::new(777);
        let leaf = Expr::const_(name.clone(), vec![]);
        let body = Expr::app(leaf, Expr::bvar(0));
        let mut input = Expr::lam(BinderInfo::Default, Expr::const_str("Bool"), body);
        for _ in 0..30 {
            let shared = Arc::new(input);
            input = Expr::from_kind(clean_kernel::ExprKind::App(shared.clone(), shared));
        }
        let mut folder = Transport {
            leaves: [(name, Expr::fvar(id))].into(),
            invalid_universes: false,
            memo: Memo::default(),
        };
        let output = folder.fold_expr_opt(&input).unwrap();
        let bytes = trust_ir::proof::encode_clean_expr_dag_v2(&output).unwrap();
        assert!(bytes.len() < 16 * 1024, "changed child sharing must stay compact");
        let mut inside = &output;
        for _ in 0..30 {
            let clean_kernel::ExprKind::App(left, right) = inside.kind() else {
                panic!("the application shape changed")
            };
            assert!(Arc::ptr_eq(left, right));
            inside = left;
        }
        let clean_kernel::ExprKind::Lam(_, _, body) = inside.kind() else {
            panic!("the binder shape changed")
        };
        let clean_kernel::ExprKind::App(value, bound) = body.kind() else {
            panic!("the body shape changed")
        };
        assert_eq!(**value, Expr::fvar(id));
        assert_eq!(**bound, Expr::bvar(0));
        assert!(!folder.invalid_universes);
    }
}
