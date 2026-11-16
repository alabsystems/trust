//! Step 6, increment 2, item 2 (docs/design/DIRECT-LANE-PROOF-AUTHORITY.md):
//! NAMED-VALUE RESOLUTION — the widening of the direct formula capture's
//! operand envelope from params-only to every value the lowering knows under
//! exactly ONE unique source name.
//!
//! THE RULE (mirrored predicate-for-predicate by the model oracle's
//! `convert_operand` in `trust-ir-bridge/src/safety_formulas.rs` — the two
//! carriers cannot literally share code, trust_ir open-block/THIR here vs
//! trust_types MIR there; `grade_real_records` over the production dump is
//! the EXECUTABLE equivalence check): a `ValueId` resolves to
//! `DirectFormulaOperand::Named { name }` iff
//!
//! 1. the set of source names the value is CURRENTLY known under — the
//!    `value_names` params ledger ∪ the current `self.locals` bindings, both
//!    existing `LowerCx` state — has EXACTLY ONE element
//!    (zero -> `unnamed-temp-operand`, the `_N` vocabulary-divergence band;
//!    two or more -> `ambiguous-operand-name`: `let y = x; y + 1` binds one
//!    value under two spellings and the capture cannot know which one MIR's
//!    debug info keeps);
//! 2. that name is bound EXACTLY ONCE in a THIR-WIDE binding-name census
//!    (params, `let` statements, match arms, let-chain `Let` exprs —
//!    INCLUDING bindings after the assert, mirroring MIR's all-named-locals
//!    uniqueness in `collision_safe_local_name`); a recount above one is
//!    `shadowed-operand-name` — the bridge will spell the local `_N`.
//!
//! Fallback-shaped (`_<digits>`) and reserved-namespace names deliberately
//! RESOLVE here and decline at the SHARED mint guard/sweep
//! (`fallback-shaped-var-would-guess-mir-index` / `synthetic-name-collision`)
//! — one decline authority for both lanes, not two.
//!
//! ONE NESTING LEVEL OF KNOWLEDGE is the vouching rule: the resolver answers
//! only from bindings the lowering itself created (params, let/pattern
//! bindings, loop-carried rebinds already reflected in `self.locals`) — it
//! never chases beyond the value's own binding.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use std::collections::BTreeMap;

use rustc_middle::thir::{ExprKind, Pat, PatKind, StmtKind};
use trust_ir::inst::{Inst, OverflowOp};
use trust_ir::value::ValueId;
use trust_ir_bridge::safety_formulas::{DirectFormulaOperand, NestedBinOp, direct_int_width};

use crate::LowerCx;

/// The THIR-wide binding-name census: how many DISTINCT binding sites carry
/// each name (or-pattern duplicates of one var counted once via
/// `is_primary`), plus each var's source name. `LocalVarId` is not `Ord`, so
/// the var map is a small linear vec — bodies hold few bindings and the
/// resolver runs once per assert operand.
#[derive(Default)]
pub(crate) struct ThirBindingCensus {
    name_counts: BTreeMap<String, usize>,
    var_names: Vec<(rustc_middle::thir::LocalVarId, String)>,
}

impl ThirBindingCensus {
    fn var_name(&self, var: rustc_middle::thir::LocalVarId) -> Option<&str> {
        self.var_names.iter().find(|(v, _)| *v == var).map(|(_, n)| n.as_str())
    }
}

fn record_pat<'tcx>(census: &mut ThirBindingCensus, pat: &Pat<'tcx>) {
    pat.walk_always(|p| {
        if let PatKind::Binding { name, var, is_primary, .. } = &p.kind {
            // `is_primary: false` is an or-pattern re-mention of the SAME
            // var; counting it would double-book one MIR local.
            if *is_primary {
                *census.name_counts.entry(name.to_string()).or_insert(0) += 1;
                if !census.var_names.iter().any(|(v, _)| v == var) {
                    census.var_names.push((*var, name.to_string()));
                }
            }
        }
    });
}

impl<'a, 'tcx> LowerCx<'a, 'tcx> {
    /// Walk every pattern position of the body's THIR: params, `let`
    /// statements, match arms, and let-chain `Let` exprs. Closure bodies are
    /// separate THIR (and separate MIR), so their bindings correctly do not
    /// participate.
    pub(crate) fn thir_binding_census(&self) -> ThirBindingCensus {
        let mut census = ThirBindingCensus::default();
        for param in self.thir.params.iter() {
            if let Some(pat) = &param.pat {
                record_pat(&mut census, pat);
            }
        }
        for stmt in self.thir.stmts.iter() {
            if let StmtKind::Let { pattern, .. } = &stmt.kind {
                record_pat(&mut census, pattern);
            }
        }
        for arm in self.thir.arms.iter() {
            record_pat(&mut census, &arm.pattern);
        }
        for expr in self.thir.exprs.iter() {
            if let ExprKind::Let { pat, .. } = &expr.kind {
                record_pat(&mut census, pat);
            }
        }
        census
    }

    /// The widened resolution — `direct_formula_operand`'s miss-path tail.
    /// Every failure is a NAMED enumerated withhold reason (all present in
    /// `trust_ir_bridge::direct_formula_dump::ENUMERATED_WITHHELD_REASONS`),
    /// never a guess and never a panic.
    pub(crate) fn widened_named_operand(
        &self,
        value: ValueId,
    ) -> Result<DirectFormulaOperand, &'static str> {
        let census = self.thir_binding_census();

        // The CURRENT binding of each source var: `self.locals` is a push
        // ledger (last write wins), so replay it var-by-var — a value a var
        // USED to hold is not "currently known" under that var's name.
        let mut current: Vec<(rustc_middle::thir::LocalVarId, ValueId)> = Vec::new();
        for (var, val) in &self.locals {
            match current.iter_mut().find(|(v, _)| v == var) {
                Some(slot) => slot.1 = *val,
                None => current.push((*var, *val)),
            }
        }

        let mut known: Vec<&str> = Vec::new();
        for (vid, name) in &self.value_names {
            if *vid == value && !known.contains(&name.as_str()) {
                known.push(name.as_str());
            }
        }
        for (var, val) in &current {
            if *val == value {
                if let Some(name) = census.var_name(*var) {
                    if !known.contains(&name) {
                        known.push(name);
                    }
                }
            }
        }

        match known.as_slice() {
            [] => Err("unnamed-temp-operand"),
            [name] => {
                if census.name_counts.get(*name).copied().unwrap_or(0) != 1 {
                    // Bound more than once (shadowing, per-arm rebinds): MIR
                    // holds two same-named locals and the bridge spells the
                    // operand `_N`. Zero cannot occur for a name we ourselves
                    // recorded, but a miss fails closed the same way.
                    Err("shadowed-operand-name")
                } else {
                    Ok(DirectFormulaOperand::Named { name: (*name).to_string() })
                }
            }
            _ => Err("ambiguous-operand-name"),
        }
    }

    /// Increment 3 — the DEPTH-2 CHECKED-TRIO chase (honest scope of the
    /// depth-2 widening; casts EXCLUDED, measured: the bridge renders a cast
    /// operand as a `Var` over the cast-result MIR temp, so cast byte-parity
    /// would require the pinned forbidden `_N` guess). Runs only after the
    /// leaf resolution returned `unnamed-temp-operand` (the anonymous band;
    /// naming hazards keep their own reasons).
    ///
    /// The chased shape is `Inst::Overflow` — the checked Add/Sub/Mul, the
    /// ONLY inst the checked trio lowers to — and only its VALUE result
    /// (`results[0]`; `results[1]` is the overflowed bool, MIR's cond var).
    /// Its MIR materialization is a `CheckedBinaryOp` tuple read through a
    /// `Field(0)` projection, which the bridge's `safety_place_var_name`
    /// structurally refuses — so a minted nested formula can never silently
    /// mismatch a bridge formula; the row lands in the enumerated
    /// minted-with-no-comparator band. A PLAIN `Inst::BinOp` result (div/rem
    /// results, wrapping ops, shifts) is deliberately NOT chased: MIR holds it
    /// as a projection-free `_N` temp the bridge DOES reconstruct
    /// (`Var("_N")`), the pinned vocabulary-divergence band — minting a
    /// composed term there manufactures an unclassifiable mismatch (pinned by
    /// the model battery's `plain_temp_binop_stays_unnamed`).
    ///
    /// Leaves resolve via `direct_formula_leaf_operand` — depth 1 only, the
    /// structural one-nesting-level cap. EVERY failure returns
    /// `unnamed-temp-operand`: the outer operand's own truth, never a guess.
    /// The model mirror is `safety_formulas::parity_oracle::
    /// convert_nested_checked`; the shared mint (width guard, BV declines,
    /// placeholder substitution) is the SAME code for both carriers.
    pub(crate) fn nested_checked_operand(
        &self,
        value: ValueId,
    ) -> Result<DirectFormulaOperand, &'static str> {
        let Some(node) = self.cur.iter().rev().find(|node| node.results.contains(&value)) else {
            return Err("unnamed-temp-operand");
        };
        let Inst::Overflow { op, ty, lhs, rhs } = &node.inst else {
            return Err("unnamed-temp-operand");
        };
        if node.results.first() != Some(&value) {
            // The overflowed-bool result — MIR's cond var, not a value.
            return Err("unnamed-temp-operand");
        }
        let Ok((width, signed)) = direct_int_width(ty) else {
            return Err("unnamed-temp-operand");
        };
        let op = match op {
            OverflowOp::AddOverflow => NestedBinOp::Add,
            OverflowOp::SubOverflow => NestedBinOp::Sub,
            OverflowOp::MulOverflow => NestedBinOp::Mul,
        };
        let Ok(lhs) = self.direct_formula_leaf_operand(*lhs) else {
            return Err("unnamed-temp-operand");
        };
        let Ok(rhs) = self.direct_formula_leaf_operand(*rhs) else {
            return Err("unnamed-temp-operand");
        };
        Ok(DirectFormulaOperand::Nested {
            op,
            width,
            signed,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        })
    }
}
