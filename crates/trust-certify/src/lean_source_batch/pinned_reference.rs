// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Source-only orchestration of the existing fenced closed replay. Every
//! admission remains the existing kernel's own judgment. Raw imported records
//! are never promoted, and the original source environment stays unchanged.

use std::collections::BTreeSet;

use clean_kernel::env::{ConstantInfo, ConstantKind, Reducibility, TrustedEnvExt as _};
use clean_kernel::expr::ExprFolderOpt;
use clean_kernel::{Environment, Expr, LevelVec, Name, ReferenceKernel};

pub(crate) struct PinnedSourceReference<'a> {
    original: &'a Environment,
    kernel: Result<ReferenceKernel, String>,
}

impl<'a> PinnedSourceReference<'a> {
    pub(crate) fn new(
        original: &'a Environment,
        owned: &BTreeSet<Name>,
        judgments: &[(&Expr, &Expr)],
    ) -> Self {
        let mut reference = Self { original, kernel: Self::replay(original, owned, judgments) };
        if reference.kernel.is_ok() {
            for name in owned {
                if let Err(error) = reference.check_registered(name) {
                    reference.kernel = Err(format!("original owned declaration `{name}`: {error}"));
                    break;
                }
            }
        }
        reference
    }

    fn replay(
        original: &Environment,
        owned: &BTreeSet<Name>,
        judgments: &[(&Expr, &Expr)],
    ) -> Result<ReferenceKernel, String> {
        let mut candidate = original.clone();
        let mut roots = owned.clone();
        let stem = Name::from_string("_trust_source_reference");
        let mut nonce = 0u64;
        for (goal, value) in judgments {
            let name = loop {
                let name = stem.clone().num(nonce);
                nonce = nonce.checked_add(1).ok_or("source judgment wrapper name exhausted")?;
                if candidate.get_const(&name).is_none()
                    && candidate.get_inductive(&name).is_none()
                    && candidate.get_constructor(&name).is_none()
                    && candidate.get_recursor(&name).is_none()
                    && candidate.get_quot(&name).is_none()
                {
                    break name;
                }
            };
            let wrapper = judgment_candidate(name.clone(), goal, value);
            let refused = candidate.extend_constants_structural(std::iter::once(wrapper));
            if !refused.is_empty() {
                return Err(format!("source judgment candidate refused: {refused:?}"));
            }
            roots.insert(name);
        }
        let replay = clean_olean::reference_base_closed(
            &candidate,
            &roots,
            &clean_olean::recheck_closed::ClosedRecheckOptions::default(),
        )
        .map_err(|error| format!("{error:?}"))?;
        replay.into_kernel().map_err(|report| format!("{report:?}"))
    }

    pub(crate) fn base_error(&self) -> Option<String> {
        self.kernel.as_ref().err().cloned()
    }

    pub(crate) fn check_registered(&self, name: &Name) -> Result<(), String> {
        let kernel = self.kernel.as_ref().map_err(Clone::clone)?;
        let original = self
            .original
            .get_const(name)
            .ok_or_else(|| format!("original source declaration `{name}` is absent"))?;
        if let Some(error) =
            crate::clean_island::strict_registered_theorem_error(kernel.environment(), original)
        {
            return Err(error);
        }
        if let Some(value) = &original.value {
            // Check the original accepted expressions, not a replacement
            // declaration recovered from the rebuilt reference environment.
            crate::reference_mint::check_island_judgment_in(
                kernel.environment(),
                &original.type_,
                value,
            )
            .map(|_| ())
            .map_err(|error| format!("{error:?}"))
        } else {
            // Families and members were regenerated and compared by the
            // closed replay. Reuse the existing generic registered judgment.
            crate::reference_mint::check_registered_in(kernel.environment(), name)
                .map(|_| ())
                .map_err(|error| format!("{error:?}"))
        }
    }

    pub(crate) fn check_judgment(&self, goal: &Expr, value: &Expr) -> Result<(), String> {
        let kernel = self.kernel.as_ref().map_err(Clone::clone)?;
        crate::reference_mint::check_island_judgment_in(kernel.environment(), goal, value)
            .map(|_| ())
            .map_err(|error| format!("{error:?}"))
    }
}

// Untrusted wrapper DATA includes the exact anonymous type/value in the
// closed dependency cone. The wrapper never enters the accepted source
// environment or its owned denominator. The existing kernel checks it and
// the actual original judgment independently, including all universes.
fn judgment_candidate(name: Name, goal: &Expr, value: &Expr) -> ConstantInfo {
    let mut params = JudgmentLevelParams::default();
    let _ = goal.fold_opt_or_clone(&mut params);
    let _ = value.fold_opt_or_clone(&mut params);
    ConstantInfo::new_with_reducibility(
        name,
        params.0,
        goal.clone(),
        Some(value.clone()),
        Reducibility::Opaque,
        ConstantKind::Definition,
    )
}

#[derive(Default)]
struct JudgmentLevelParams(Vec<Name>);

impl ExprFolderOpt for JudgmentLevelParams {
    fn should_descend(&self, expr: &Expr) -> bool {
        expr.has_level_param_quick()
    }

    fn fold_sort_opt(&mut self, level: &clean_kernel::Level) -> Option<Expr> {
        level.collect_params(&mut self.0);
        None
    }

    fn fold_const_opt(&mut self, _: &Name, levels: &LevelVec) -> Option<Expr> {
        for level in levels {
            level.collect_params(&mut self.0);
        }
        None
    }
}
