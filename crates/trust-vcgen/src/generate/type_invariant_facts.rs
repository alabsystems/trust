//! TINV step 10.2: the USE-SITE facts of a published type invariant
//! (`docs/design/2026-10-04-type-invariant-tinv.md` §2 P6, §6 step 10).
//!
//! Given the [`TinvUseSet`] installed in the generation context, [`tinv_use_facts`] lists,
//! for one body, every conjunct instance a row of that body may assume, each TAGGED:
//! `And([Var(tag, Bool), I_k(σ)])`, `tag` = [`trust_types::type_invariant_assume_tag`] of
//! the conjunct. Every model sets the tag `true`, so it does not change validity; it is the
//! formula-side disclosure channel, and the kernel refuses every tagged VC (TINV-23).
//!
//! STEP 10.3: the safety walk conjoins them ([`conjoin_tinv_facts_at_point_recorded`]) as a
//! SECOND recorded `ConjoinFactsLast`, right after the user-`requires` conjoin and at the
//! same point, into every ordinary row that carries an obligation record (a row with no
//! record gets none, TINV-25; a `TypeInvariant` row and an unsupported row get none). Each
//! row that received a fact is recorded, with the tags it received, in the GENERATION'S
//! recording scope ([`crate::type_invariant::with_tinv_assumed_rows_scope`]): the
//! disclosure channel the compiler's mint checks the formula's tags against. Facts are
//! given ONLY inside such a scope, for the body it names, so a replay or a probe outside
//! it assumes nothing. A real compile installs a use set only under `-Ztrust-tinv` (step 10.5).
//!
//! THE TWO PLACES A FACT MAY HOLD, and nowhere else:
//! * ENTRY, over the BARE names [`sigma_of_root`] renders, at exactly the roots the mint
//!   assumed at ([`param_roots`]), narrowed: an `S` parameter by value, or the pointee of
//!   an `&S` or `&mut S` parameter (the `&mut` channel is [`TINV_MUT_ENTRY_FACTS`], on
//!   since step 10.6 once the use-site rail-23 test passed, decision TINV-31).
//!   `param_roots` has no `Box<S>` root, so a `Box<S>` parameter gets none.
//!   Sound because every caller is an inventory body that proved C on the argument
//!   (whole-crate induction), or is outside the crate under the privacy premise (G1); the
//!   version oracle re-versions every read after a write (step 0(a)), including a length
//!   term after a `&mut` call or a store (10.3-LEN, `tinv_len_versioning_tests.rs`), so a
//!   bare entry fact binds entry-valued reads only.
//! * POST-CALL, at each [`post_call_assumption_points`] root that is a whole local or the
//!   pointee of one (v1, TINV-24; the mint also admits a field chain), including (step
//!   10.6) the call's DESTINATION when it is a whole non-return local of type exactly
//!   `S`: the call's single-predecessor
//!   normal target `T` of a call into the run's inventory, sealed at `(T, 0)` by the SAME
//!   helper the mint's own rows use ([`tinv_sealed_post_call_hyps`]), kept only where
//!   `(T, 0)` dominates the row and the row's rename leaves the sealed fact unchanged.
//!
//! WHEN THERE ARE NONE ([`tinv_use_facts`] is `None`): no use set is installed; no
//! recording scope for this body is open; the body has a tail call (D5) — decided by the
//! scope on the UNEXPANDED body, because generation expands tail calls before the safety
//! walk (the walk-level check in [`tinv_use_facts_with`] only covers a caller that hands
//! it an unexpanded body); a TINV row request is active for the body (the mint's own walk
//! must never assume what it is proving); or the body is not in the run's
//! `checked_bodies` (the induction never saw it).
use std::collections::BTreeSet;

use trust_types::{BlockId, Formula, Sort, Terminator, Ty, VerifiableFunction};

use super::StmtVersionCtx;
#[cfg(test)]
use super::tinv_rows::tinv_sealed_post_call_hyps;
use crate::type_invariant::obligations::{
    TinvInputs, param_roots, post_call_assumption_points, sigma_of_root,
};
use crate::type_invariant::unwind::SysrootExactModels;
use crate::type_invariant::{Sigma, TinvType, TinvUseSet, instantiate};
use crate::versioned::{Fact, Vc, conjoin};

/// Whether the pointee of an `&mut S` parameter gets ENTRY facts. ON since step 10.6
/// (decision TINV-31): the mint already relies on the entry rename for `&mut` pointees
/// (step 0(a)), and the use-site rail-23 test
/// (`tinv_use_site_tests::rail_23_the_mut_entry_fact_never_binds_the_post_write_read`)
/// shows no entry instance ever names a post-write read and every post-write row stays
/// refuted. A test override can still turn it off.
pub(crate) const TINV_MUT_ENTRY_FACTS: bool = true;

#[cfg(test)]
thread_local! {
    /// Test-only: run the use site as if [`TINV_MUT_ENTRY_FACTS`] were `Some(on)` (the
    /// use-site rail-23 test must exercise the `&mut` entry channel before step 10.6 may
    /// flip the constant). Per thread, so it cannot leak into another test.
    static MUT_ENTRY_FACTS_OVERRIDE: std::cell::Cell<Option<bool>> =
        const { std::cell::Cell::new(None) };
}

/// Whether `&mut S` pointees get entry facts: [`TINV_MUT_ENTRY_FACTS`], or a test override.
fn mut_entry_facts() -> bool {
    #[cfg(test)]
    if let Some(on) = MUT_ENTRY_FACTS_OVERRIDE.with(std::cell::Cell::get) {
        return on;
    }
    TINV_MUT_ENTRY_FACTS
}

/// Test-only: set the `&mut` entry-fact override for this thread until the guard drops.
#[cfg(test)]
pub(crate) fn override_mut_entry_facts(on: bool) -> impl Drop {
    struct Restore(Option<bool>);
    impl Drop for Restore {
        fn drop(&mut self) {
            MUT_ENTRY_FACTS_OVERRIDE.with(|c| c.set(self.0));
        }
    }
    Restore(MUT_ENTRY_FACTS_OVERRIDE.with(|c| c.replace(Some(on))))
}

/// An assumption tag name ([`trust_types::type_invariant_assume_tag`]).
pub(crate) type TagName = String;

/// The tagged facts one body may assume, UNVERSIONED (module doc).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct TinvUseFacts {
    /// Entry facts, bare: `(tag, And([tag, I_k(σ(root))]))`.
    pub(crate) entry: Vec<(TagName, Formula)>,
    /// Per post-call point `T`, in [`post_call_assumption_points`] order: the facts at the
    /// root that call received, unversioned (they are sealed at `(T, 0)` per row).
    pub(crate) post_calls: Vec<(BlockId, Vec<(TagName, Formula)>)>,
}

impl TinvUseFacts {
    pub(crate) fn is_empty(&self) -> bool {
        self.entry.is_empty() && self.post_calls.iter().all(|(_, f)| f.is_empty())
    }

    /// The entry facts as [`Fact::entry`]s: bare names are the entry values.
    #[cfg(test)]
    pub(crate) fn entry_facts(&self) -> Vec<(TagName, Fact)> {
        self.entry.iter().map(|(tag, f)| (tag.clone(), Fact::entry(f.clone()))).collect()
    }

    /// The post-call facts that hold at a row at `(block, end)` (`end` = the row's rename
    /// point), sealed at their call target `(T, 0)` by [`tinv_sealed_post_call_hyps`], the
    /// helper the mint's rows use: only where `(T, 0)` dominates `block` and the row's own
    /// rename leaves the sealed fact unchanged.
    #[cfg(test)]
    pub(crate) fn post_call_facts_at(
        &self,
        func: &VerifiableFunction,
        sv: &StmtVersionCtx,
        block: BlockId,
        end: usize,
    ) -> Vec<(TagName, Fact)> {
        tinv_sealed_post_call_hyps(func, sv, &self.post_calls, |(_, f)| f, block, end)
            .into_iter()
            .map(|((tag, _), target, sealed)| (tag.clone(), Fact::sealed_at(sealed, target, 0)))
            .collect()
    }

    /// Pre-filter entry facts and pre-seal post-call facts once per `(func, sv)` so the
    /// safety walk does not repeat `formula_uses_unmodeled_machine_arithmetic_in_function`
    /// or `(T, 0)` `version_rename_at` + `seal_bare_reads` on every row of the body.
    pub(crate) fn prepare(
        &self,
        func: &VerifiableFunction,
        sv: &StmtVersionCtx,
    ) -> PreparedTinvUseFacts {
        let extract_raw_vars = |f: &Formula, own_tag: &str| -> Vec<String> {
            let mut vars = Vec::new();
            trust_types::visit_formula_nodes(f, &mut |n| {
                if let Formula::Var(name, _) = n
                    && name != own_tag
                    && !vars.contains(name)
                {
                    vars.push(name.clone());
                }
            });
            vars
        };
        let entry = self
            .entry
            .iter()
            .filter(|(_, f)| {
                !crate::contracts::formula_uses_unmodeled_machine_arithmetic_in_function(func, f)
            })
            .map(|(tag, f)| PreparedFactItem {
                tag: tag.clone(),
                fact: Fact::entry(f.clone()),
                raw_vars: extract_raw_vars(f, tag),
            })
            .collect();
        let mut post_calls = Vec::new();
        for (target, facts) in &self.post_calls {
            if facts.is_empty() || !super::tinv_rows::entry_dominates(sv, *target, *target) {
                continue;
            }
            let mut sealed_facts = Vec::with_capacity(facts.len());
            for (tag, f) in facts {
                if let Some(sealed) =
                    super::tinv_rows::seal_fact_at_block_entry(func, sv, *target, f)
                {
                    let raw_vars = extract_raw_vars(&sealed, tag);
                    sealed_facts.push(PreparedFactItem {
                        tag: tag.clone(),
                        fact: Fact::sealed_at(sealed, *target, 0),
                        raw_vars,
                    });
                }
            }
            if !sealed_facts.is_empty() {
                post_calls.push((*target, sealed_facts));
            }
        }
        PreparedTinvUseFacts { entry, post_calls }
    }
}

struct PreparedFactItem {
    tag: TagName,
    fact: Fact,
    raw_vars: Vec<String>,
}

/// Per-walk pre-filtered entry facts and `(T, 0)`-sealed post-call facts for a body.
pub(crate) struct PreparedTinvUseFacts {
    entry: Vec<PreparedFactItem>,
    post_calls: Vec<(BlockId, Vec<PreparedFactItem>)>,
}

/// The tagged fact `And([Var(tag, Bool), instance])`.
#[must_use]
pub(crate) fn tagged(tag: &str, instance: Formula) -> Formula {
    Formula::And(vec![Formula::Var(tag.to_owned(), Sort::Bool), instance])
}

/// The use-site facts of `func` under the use set installed in the active generation
/// context, or `None` (module doc, "WHEN THERE ARE NONE"; also when the body has no
/// fact). Facts are given only inside a recording scope for THIS body
/// ([`crate::type_invariant::with_tinv_assumed_rows_scope`]), so every fact conjoined is
/// recorded and a replay, probe or clone outside the scope assumes nothing.
pub(crate) fn tinv_use_facts(func: &VerifiableFunction) -> Option<TinvUseFacts> {
    if !crate::type_invariant::record_scope_admits(&func.def_path) {
        return None;
    }
    let set = crate::current_type_invariants()?;
    let facts = tinv_use_facts_with(func, &set)?;
    // The record names the set these facts come from (the consumer decodes against it).
    crate::type_invariant::note_scope_use_set(&set);
    Some(facts)
}

/// [`tinv_use_facts`] over an explicit use set.
pub(crate) fn tinv_use_facts_with(
    func: &VerifiableFunction,
    set: &TinvUseSet,
) -> Option<TinvUseFacts> {
    if set.is_empty()
        || super::tinv_rows::active_request(func).is_some()
        || !set.checked_bodies().contains(&func.def_path)
        || func.body.blocks.iter().any(|b| matches!(b.terminator, Terminator::TailCall { .. }))
    {
        return None;
    }
    let mut out = TinvUseFacts::default();
    for ty in set.types().values() {
        for root in entry_roots(func, &ty.def_path) {
            out.entry.extend(instances(set, ty, &sigma_of_root(func, ty, &root)));
        }
        let inp = TinvInputs {
            ty,
            inventory: set.inventory(),
            models: &SysrootExactModels,
            may_run_user_drop: &|_| true,
        };
        // v1 root scope (decision TINV-24): a post-call fact only at a whole local or the
        // pointee of one. The mint's rule also admits a field chain (`feed(&mut self.s)`,
        // design P5), which is sound for the same reason, but the v1 use site is narrower
        // (fail closed, reversible).
        for pc in post_call_assumption_points(func, &inp) {
            if !matches!(pc.root.projections.as_slice(), [] | [trust_types::Projection::Deref]) {
                continue;
            }
            out.post_calls
                .push((pc.target, instances(set, ty, &sigma_of_root(func, ty, &pc.root))));
        }
    }
    (!out.is_empty()).then_some(out)
}

/// The roots that get ENTRY facts: [`param_roots`] (the mint's rule, exactly), minus the
/// `&mut S` pointees while [`TINV_MUT_ENTRY_FACTS`] is off.
pub(crate) fn entry_roots(func: &VerifiableFunction, def_path: &str) -> Vec<trust_types::Place> {
    param_roots(func, def_path)
        .into_iter()
        .filter(|root| {
            if root.projections.is_empty() {
                return true; // `S` by value.
            }
            match crate::local_ty_ref(func, root.local) {
                Some(Ty::Ref { mutable: false, .. }) => true,
                Some(Ty::Ref { mutable: true, .. }) => mut_entry_facts(),
                _ => false,
            }
        })
        .collect()
}

/// Every published conjunct of `ty` instantiated at `sigma`, tagged. A conjunct that does
/// not instantiate (a field term the generator has none for) gives no fact.
fn instances(set: &TinvUseSet, ty: &TinvType, sigma: &Sigma) -> Vec<(TagName, Formula)> {
    ty.conjuncts
        .iter()
        .filter_map(|c| {
            let tag = set.tag_for(&ty.def_path, c.id)?;
            Some((tag.to_owned(), tagged(tag, instantiate(c, sigma)?)))
        })
        .collect()
}

/// STEP 10.3: conjoin the facts of `use_facts` that hold at the row `(block, point)` onto
/// `formula`, which the user-`requires` conjoin ALREADY renamed at this row's rename point
/// (`row_rename_point`). Returns the new formula, the conjoined fact list (for the
/// row's second `ConjoinFactsLast` record; `And(facts.., formula)` is exactly the new
/// formula), and the set of tags of the facts that survived. Nothing is renamed again.
///
/// * ENTRY facts go in bare ([`Fact::entry`]), filtered by
///   `formula_uses_unmodeled_machine_arithmetic_in_function` exactly as the user
///   `requires` are (`conjoin_preconditions_versioned_at_point_recorded`).
/// * POST-CALL facts are sealed at their target `(T, 0)` by the helper the mint's rows use
///   ([`TinvUseFacts::post_call_facts_at`]): kept only where `(T, 0)` dominates `block` on
///   the unwind-inclusive tree and the row's own rename at `end` leaves them unchanged.
/// * RELEVANCE: a fact is kept only if, transitively through the kept facts, it shares a
///   non-tag variable with `formula`. Dropping a hypothesis is sound (PROVE -> FAIL only).
/// * TIES: the entry-sentinel ties for any `#e` name a sealed fact carries, under the
///   consumer clause the semantic-guard conjoin uses
///   ([`super::entry_sentinel_ties_for_exempt_facts`]), minus those `formula` carries.
///   Missing ties cost precision only.
pub(crate) fn conjoin_tinv_facts_at_point_recorded(
    func: &VerifiableFunction,
    sv: &StmtVersionCtx,
    block: BlockId,
    point: usize,
    formula: Formula,
    use_facts: &TinvUseFacts,
) -> (Formula, Vec<Formula>, BTreeSet<String>) {
    use_facts.prepare(func, sv).conjoin_at_point_recorded(func, sv, block, point, formula)
}

impl PreparedTinvUseFacts {
    pub(crate) fn conjoin_at_point_recorded(
        &self,
        func: &VerifiableFunction,
        sv: &StmtVersionCtx,
        block: BlockId,
        point: usize,
        formula: Formula,
    ) -> (Formula, Vec<Formula>, BTreeSet<String>) {
        if self.entry.is_empty() && self.post_calls.is_empty() {
            return (formula, Vec::new(), BTreeSet::new());
        }
        let end = super::row_rename_point(func, block, point);
        let mut candidates: Vec<&PreparedFactItem> = self.entry.iter().collect();
        for (target, sealed_facts) in &self.post_calls {
            if !super::tinv_rows::entry_dominates(sv, *target, block) {
                continue;
            }
            for item in sealed_facts {
                if !super::path_defs::version_rename_needs_rewrite(
                    item.fact.formula(),
                    sv,
                    func,
                    block,
                    end,
                ) {
                    candidates.push(item);
                }
            }
        }
        if candidates.is_empty() {
            return (formula, Vec::new(), BTreeSet::new());
        }
        let tag_names: trust_types::fx::FxHashSet<&str> =
            candidates.iter().map(|item| item.tag.as_str()).collect();
        fn free<'a>(
            f: &'a Formula,
            tag_names: &trust_types::fx::FxHashSet<&str>,
        ) -> trust_types::fx::FxHashSet<&'a str> {
            let mut names = trust_types::fx::FxHashSet::default();
            trust_types::visit_formula_nodes(f, &mut |n| {
                if let Formula::Var(name, _) = n
                    && !tag_names.contains(name.as_str())
                {
                    names.insert(name.as_str());
                }
            });
            names
        }
        let mut reach = free(&formula, &tag_names);
        if reach.is_empty() {
            return (formula, Vec::new(), BTreeSet::new());
        }
        let mut kept = vec![false; candidates.len()];
        loop {
            let mut grew = false;
            for (i, item) in candidates.iter().enumerate() {
                if !kept[i]
                    && item
                        .raw_vars
                        .iter()
                        .any(|n| !tag_names.contains(n.as_str()) && reach.contains(n.as_str()))
                {
                    kept[i] = true;
                    for n in &item.raw_vars {
                        if !tag_names.contains(n.as_str()) {
                            reach.insert(n.as_str());
                        }
                    }
                    grew = true;
                }
            }
            if !grew {
                break;
            }
        }
        let mut tags: BTreeSet<String> = BTreeSet::new();
        let mut facts: Vec<Fact> = Vec::new();
        for (item, keep) in candidates.into_iter().zip(kept) {
            if keep {
                tags.insert(item.tag.clone());
                facts.push(item.fact.clone());
            }
        }
        if facts.is_empty() {
            return (formula, Vec::new(), tags);
        }
        let mut listed: Vec<Formula> = facts.iter().map(|f| f.formula().clone()).collect();
        let ties =
            super::entry_sentinel_ties_for_exempt_facts(func, sv, block, point, &listed, &formula);
        listed.extend(ties.iter().cloned());
        facts.extend(ties.into_iter().map(Fact::entry));
        (conjoin(&facts, Vc::versioned(formula, block)), listed, tags)
    }
}

#[cfg(test)]
#[path = "type_invariant_facts_tests.rs"]
mod tests;
