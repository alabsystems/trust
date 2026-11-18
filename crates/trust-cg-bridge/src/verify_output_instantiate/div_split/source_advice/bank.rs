// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Select and transport old proof bodies as DATA, without borrowing their
//! admission stamps or declaring any axiom. The canonical consumer must check
//! every resulting declaration before it can use the proposed final proof.

use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::sync::Arc;

use clean_kernel::expr::UsedConstants;
use clean_kernel::{ConstantKind, Declaration, Environment, Expr, ExprFolderOpt, LevelVec, Name};
use trust_types::Formula;

use super::super::super::branch_theory;
use super::shared::{Memo, SharedConstFolder};
use super::transport::canonical_name as canonical;

pub(crate) struct Advice {
    pub(crate) proof: Expr,
    pub(crate) declarations: Vec<Declaration>,
    pub(crate) strings: BTreeMap<Name, String>,
}

fn used(expressions: &[&Expr]) -> BTreeSet<Name> {
    let mut names = HashSet::new();
    for expression in expressions {
        expression.used_constants_dag(UsedConstants::ConstantsOnly, &mut names);
    }
    names.into_iter().collect()
}

struct Selection<'a> {
    old: &'a Environment,
    actual: &'a Environment,
    strings: &'a BTreeMap<Name, String>,
    visiting: BTreeSet<Name>,
    finished: BTreeSet<Name>,
    ordered: Vec<Name>,
}

impl Selection<'_> {
    fn canonical_available(&self, name: &Name) -> bool {
        let target = canonical(name);
        let Some(actual) = self.actual.get_const(&target) else {
            return false;
        };
        let Some(old) = self.old.get_const(name) else {
            return true;
        };
        if target != *name || old.kind != ConstantKind::Theorem {
            return true;
        }
        // A shared theorem spelling does not license an old statement about
        // a different function body (notably Bool.xor versus Compat.xor).
        // Keep mismatching theorem bodies as fresh untrusted advice instead.
        let mut rename = Rename { names: BTreeMap::new(), memo: Memo::default() };
        rename.expression(&old.type_) == actual.type_
    }

    fn visit(&mut self, name: &Name, depth: usize) -> Result<(), String> {
        if self.canonical_available(name)
            || self.strings.contains_key(name)
            || self.finished.contains(name)
        {
            return Ok(());
        }
        if depth > 256 || self.ordered.len() >= 4096 || !self.visiting.insert(name.clone()) {
            return Err("source proof advice: dependency depth/population/cycle bound".into());
        }
        let declaration = self
            .old
            .get_const(name)
            .ok_or_else(|| format!("source proof advice: unavailable declaration {name}"))?;
        let value = declaration.value.as_ref().ok_or_else(|| {
            format!("source proof advice: no body for {name}; axioms are refused")
        })?;
        if !matches!(declaration.kind, ConstantKind::Definition | ConstantKind::Theorem) {
            return Err(format!("source proof advice: unavailable declaration kind for {name}"));
        }
        for dependency in used(&[&declaration.type_, value]) {
            self.visit(&dependency, depth + 1)?;
        }
        self.visiting.remove(name);
        self.finished.insert(name.clone());
        self.ordered.push(name.clone());
        Ok(())
    }
}

struct Rename {
    names: BTreeMap<Name, Name>,
    memo: Memo,
}
impl SharedConstFolder for Rename {
    fn child_memo(&mut self) -> &mut Memo {
        &mut self.memo
    }
}
impl ExprFolderOpt for Rename {
    fn fold_expr_arc_opt(&mut self, expr: &Arc<Expr>) -> Option<Arc<Expr>> {
        self.fold_shared(expr)
    }

    fn fold_binder_body_arc_opt(&mut self, expr: &Arc<Expr>) -> Option<Arc<Expr>> {
        self.fold_shared(expr)
    }

    fn fold_const_opt(&mut self, name: &Name, universes: &LevelVec) -> Option<Expr> {
        let target = self.names.get(name).cloned().unwrap_or_else(|| canonical(name));
        (target != *name).then(|| Expr::const_(target, universes.clone()))
    }
}
impl Rename {
    fn expression(&mut self, expression: &Expr) -> Expr {
        self.fold_expr_opt(expression).unwrap_or_else(|| expression.clone())
    }
}

/// The old bank is solely an untrusted source of candidate bodies. Canonical
/// definitions are never replaced, and every missing theorem/definition gets
/// a fresh name so source admission cannot accidentally use an old stamp.
pub(crate) fn propose(
    original: &[(Formula, Formula)],
    actual: &Environment,
) -> Result<Advice, String> {
    let proposal = super::transport::propose(original)?;
    let old = branch_theory::branch_base()?;
    let mut selection = Selection {
        old,
        actual,
        strings: &proposal.strings,
        visiting: BTreeSet::new(),
        finished: BTreeSet::new(),
        ordered: Vec::new(),
    };
    for name in used(&[&proposal.goal, &proposal.proof]) {
        selection.visit(&name, 0)?;
    }
    let mut names = BTreeMap::new();
    let mut reverse = BTreeMap::new();
    for original in &selection.ordered {
        let fresh = Name::from_string("Trust.Fmrel.Advice").str(original.to_string());
        if actual.get_const(&fresh).is_some()
            || reverse.insert(fresh.clone(), original.clone()).is_some()
        {
            return Err("source proof advice: fresh declaration identity collision".into());
        }
        names.insert(original.clone(), fresh);
    }
    let mut rename = Rename { names, memo: Memo::default() };
    let mut declarations = Vec::new();
    for name in &selection.ordered {
        let old = old.get_const(name).ok_or("source proof advice: selected body disappeared")?;
        let value = old.value.as_ref().ok_or("source proof advice: selected axiom")?;
        let fresh =
            rename.names.get(name).ok_or("source proof advice: missing fresh name")?.clone();
        let type_ = rename.expression(&old.type_);
        let value = rename.expression(value);
        let declaration = match old.kind {
            ConstantKind::Theorem => Declaration::Theorem {
                name: fresh,
                level_params: old.level_params.clone(),
                type_,
                value,
            },
            ConstantKind::Definition => Declaration::Definition {
                name: fresh,
                level_params: old.level_params.clone(),
                type_,
                value,
                is_reducible: old.is_reducible,
            },
            _ => return Err("source proof advice: selected non-body declaration".into()),
        };
        declarations.push(declaration);
    }
    Ok(Advice {
        proof: rename.expression(&proposal.proof),
        declarations,
        strings: proposal.strings,
    })
}
