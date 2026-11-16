// Callsite L0 replay (refutation-only): when a caller's `VcKind::Precondition`
// obligation is REFUTED with a genuine solver witness, the compiler already
// knows the caller can violate the callee's `#[requires]` — but the entailed
// CALLEE-side Level-0 consequence (the bounds/overflow/div panic the requires
// was shielding) has no obligation row of its own, so the build aborts as
// `incomplete` instead of `refuted`. This producer builds the COMPOSED
// refutation candidates: the callee's own L0 violation formulas, regenerated
// WITHOUT the callee's precondition, rebound to the caller's actuals, and
// conjoined with the caller's path condition at the call site.
//
// The lane is STRICTLY refutation-only and fail-closed at every seam:
//   * A candidate is only ever solved for SAT by the DRIVER; a Proved/UNSAT/
//     Unknown replay result appends NOTHING and discharges NOTHING — not the
//     caller's Precondition obligation, not the callee's own rows, and never
//     any authority registry. This producer mints no verdicts at all.
//   * Every gate below DROPS a candidate rather than approximating it: an
//     over-approximated SAT would be a FALSE L0 refutation of possibly-correct
//     code (the cardinal sin's refutation-side twin).
//
// WHAT THE GATES ESTABLISH (exactly, no more): every free variable of an
// emitted composed formula is either caller ENTRY state (a stable, never-
// rewritten parameter dimension — legitimately model-rangeable) or def-pinned
// by the formula's own conjuncts (callee side: `callee_temps_are_def_pinned`;
// caller side: `composed_formula_is_caller_entry_grounded`). A SAT model is
// therefore a counterexample UNDER the conjoined caller model; its ultimate
// genuineness additionally rests on the guard/def/fact assembly capturing
// every constraint that dominates the call site and on `generate_vcs`
// faithfully modeling the callee's violation — properties inherited from
// those builders, not re-established here.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use super::*;

/// σ-namespace prefix shared by [`sigma_actual_formula`]'s aliasing-opaque
/// fallback (`__trust_sigma_opaque__<formal>`) and
/// [`rebind_projected_actual`]'s fail-closed fresh field var
/// (`__trust_sigma_field__<formal><suffix>`). In the PRECONDITION lane a free
/// σ var is deliberately non-dischargeable (fail-closed toward "obligation
/// kept"); in THIS lane a free σ var is an UNCONSTRAINED model dimension, so a
/// SAT model over it denotes no real execution — reject the candidate instead.
const SIGMA_FRESH_VAR_PREFIX: &str = "__trust_sigma_";

/// Capture-proof namespace for the callee's OWN def-pinned temps carried
/// inside a body VC formula (`_3 == Len(a)`-style conjuncts). rustc place
/// names (`_N`, source idents, `.k`/`*` projections) and the σ namespaces can
/// never spell this prefix, so a renamed callee temp cannot be captured by —
/// or capture — any caller-side name once the caller's path facts are
/// conjoined around it.
const REPLAY_TEMP_VAR_PREFIX: &str = "__trust_replay__";

/// Read once: [`composed_formula_is_caller_entry_grounded`] runs per obligation.
fn ground_debug_enabled() -> bool {
    static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ENABLED.get_or_init(|| {
        std::env::var_os("TRUST_GROUND_DEBUG").is_some_and(|v| v != "0" && !v.is_empty())
    })
}

/// Whether every non-σ free var ("callee temp") of `violation` is
/// FUNCTIONALLY PINNED by the formula itself: a top-level `And` conjunct
/// `Eq(temp, rhs)` (either orientation) whose `rhs` free vars resolve — via
/// the fixpoint — to σ-domain names, constants, or already-pinned temps.
///
/// SOUNDNESS (the "block-defs fully conjoined" admission): a model of a
/// conjunction containing `temp == rhs(inputs)` assigns `temp` EXACTLY the
/// value the callee's execution computes from those inputs, so the model's
/// input projection still denotes a real execution. Conversely a temp WITHOUT
/// such a pin is an unconstrained model dimension — a SAT over it is an
/// over-approximation, not a witness — so the candidate must drop. The
/// fixpoint is drop-only: any unhandled shape (non-`And` top with temps,
/// projected temp names) fails the check and loses the refutation, never mints
/// one.
///
/// A temp that is pinned only under a DISJUNCTION is admitted by exactly one
/// extra rule, [`temp_is_repairable_under_one_disjunctive_pin`] — see its own
/// soundness note; every other disjunctive shape still fails closed.
fn callee_temps_are_def_pinned(
    violation: &Formula,
    temps: &FxHashSet<String>,
    in_domain: &dyn Fn(&str) -> bool,
) -> bool {
    if temps.is_empty() {
        return true;
    }
    // The top of the formula must be a conjunction: an `Eq` that is the WHOLE
    // formula is the obligation's violation, not a definition of its own
    // subject, and reading it as a pin would ground the exact
    // `opaque_call_result == 0` shape this gate exists to reject.
    if !matches!(violation, Formula::And(_)) {
        return false;
    }
    // ... but BELOW that top, `∧` is associative: a conjunct nested inside an
    // `And` child of an `And` is a top-level conjunct of the same conjunction.
    // This walk used to read only the DIRECT children, on the stated premise
    // that "the body-VC assemblers emit defs and guards spliced flat beside the
    // violation". MEASURED 2026-08-28 (`TRUST_GROUND_DEBUG=1`, `a / d`): that
    // premise is false for the ordinary body-VC lane — `generate_vcs` emits a
    // nested `And` (a type-range block, then a defs/guards/violation block), so
    // `_3 == (d == 0)` sat two levels down, was invisible here, and EVERY
    // ordinary Level-0 body VC carrying a MIR temp was judged ungrounded.
    // Descent stops at every non-`And` node, so a pin under a disjunction or a
    // negation is still not collected by the fixpoint below.
    let conjuncts = flatten_and_conjuncts(violation);
    let mut resolved: FxHashSet<String> = FxHashSet::default();
    let rhs_grounded = |rhs: &Formula, resolved: &FxHashSet<String>| {
        trust_types::all_free_variable_names(rhs, &mut |v| {
            in_domain(v)
                || resolved.contains(v)
                || matches!(split_projection_base(v), Some((base, _)) if in_domain(base))
        })
    };
    // Monotone fixpoint (chained defs: `_4 == i < _3` after `_3 == 4`).
    loop {
        let mut progressed = false;
        for conjunct in conjuncts.iter().copied() {
            let Formula::Eq(lhs, rhs) = conjunct else {
                continue;
            };
            // Either orientation; the pinned side must be a WHOLE-name temp
            // var (a projected temp is not a value equation for its base).
            for (var_side, def_side) in [(lhs.as_ref(), rhs.as_ref()), (rhs.as_ref(), lhs.as_ref())]
            {
                if let Some(name) = var_side.var_name()
                    && temps.contains(name)
                    && !resolved.contains(name)
                    && rhs_grounded(def_side, &resolved)
                {
                    resolved.insert(name.to_string());
                    if resolved.len() == temps.len() {
                        return true;
                    }
                    progressed = true;
                }
            }
        }
        if !progressed {
            break;
        }
    }
    // Second (and last) admission route, for the one shape the fixpoint cannot
    // see. Applied AFTER the fixpoint so it can only ever add, and its results
    // are deliberately not fed back into the fixpoint — a repaired temp never
    // grounds another temp's def.
    temps.iter().all(|t| {
        resolved.contains(t)
            || temp_is_repairable_under_one_disjunctive_pin(t, &conjuncts, &resolved, &rhs_grounded)
    })
}

/// Flatten the `And` spine of `formula` into its semantic conjunct list.
///
/// Descent stops at every non-`And` node, so an `Or`/`Not`/`Implies` subtree is
/// returned WHOLE and is never mined for conjuncts it does not actually assert.
fn flatten_and_conjuncts(formula: &Formula) -> Vec<&Formula> {
    let mut out: Vec<&Formula> = Vec::new();
    let mut stack: Vec<&Formula> = vec![formula];
    while let Some(node) = stack.pop() {
        match node {
            Formula::And(children) => stack.extend(children.iter().rev()),
            other => out.push(other),
        }
    }
    out
}

/// The single disjunctive admission: `temp` occurs in EXACTLY ONE flattened
/// conjunct, that conjunct is an `Or`, and within it `temp` occurs only in a
/// disjunct `Eq(temp, rhs)` (either orientation) whose `rhs` is grounded and
/// does not itself mention `temp`.
///
/// SOUNDNESS (model repair, not model reading). Take any model of the whole
/// formula and REASSIGN `temp := rhs`, the value the grounded inputs determine.
/// Every other conjunct is untouched, because `temp` occurs in none of them.
/// The one conjunct that does contain it is a disjunction of which `Eq(temp,
/// rhs)` is now TRUE, so it holds too. The repaired assignment therefore still
/// satisfies the formula AND gives `temp` the value a real execution computes,
/// so the model's input projection denotes a real execution — which is exactly
/// what the whole-name pin establishes for the fixpoint case.
///
/// This is what a checked-arithmetic body VC needs and it is why the shape is
/// worth naming: rustc's overflow lowering conditions the destination
/// definition on NOT overflowing, so the emitted conjunct is
/// `(a + b > MAX) ∨ (_0 == a + b)` and `_0` — a local the assert dominates, so
/// no execution has assigned it yet — is pinned nowhere else. Without this
/// rule every `a + b` refutation in the tree is dropped as ungrounded.
///
/// It admits none of the hostile inhabitants the caller-side gate lists: a
/// havoc'd call destination with no summary fact has no `Eq` disjunct at all, a
/// `__r1occ` alias is rejected by name before this runs, and a temp mentioned
/// by any second conjunct (which the repair would break) is rejected by the
/// occurrence count.
fn temp_is_repairable_under_one_disjunctive_pin(
    temp: &str,
    conjuncts: &[&Formula],
    resolved: &FxHashSet<String>,
    rhs_grounded: &dyn Fn(&Formula, &FxHashSet<String>) -> bool,
) -> bool {
    let mentions = |f: &Formula| trust_types::any_free_variable_name(f, &mut |v| v == temp);
    let mut occurrences = conjuncts.iter().copied().filter(|c| mentions(c));
    let Some(only) = occurrences.next() else {
        return false;
    };
    if occurrences.next().is_some() {
        return false;
    }
    let Formula::Or(disjuncts) = only else {
        return false;
    };
    let mut carries_pin = false;
    for disjunct in disjuncts {
        let is_pin = match disjunct {
            Formula::Eq(lhs, rhs) => [(lhs.as_ref(), rhs.as_ref()), (rhs.as_ref(), lhs.as_ref())]
                .iter()
                .any(|(var_side, def_side)| {
                    var_side.var_name() == Some(temp)
                        && !mentions(def_side)
                        && rhs_grounded(def_side, resolved)
                }),
            _ => false,
        };
        if is_pin {
            carries_pin = true;
        } else if mentions(disjunct) {
            // A second, non-pinning occurrence inside the same `Or`: the repair
            // would change that disjunct's truth value. Fail closed.
            return false;
        }
    }
    carries_pin
}

/// Caller-side mirror of [`callee_temps_are_def_pinned`], applied at the
/// emission seam to the fully COMPOSED formula (violation + block/path defs +
/// guards + facts + own preconditions, post `freshen_aliasing_opaque_occurrences`
/// and `normalize_ssa_version_tokens`).
///
/// SOUNDNESS (the caller-side unconstrained-dimension gate): the driver reads a
/// SAT model of a composed candidate as a REAL caller execution, so every free
/// variable of the formula must denote a value a real execution can actually
/// take. Exactly two classifications establish that:
///   * ENTRY STATE: a caller PARAMETER — whole name, field/deref/index
///     projection of it, or its `__slice_len` companion — that provably still
///     holds its entry value at every body read: never statement-written, no
///     call-dest write, `place_source_is_stable` (the exact
///     `local_versions_collapse_to_bare` parameter standard). Entry inputs are
///     universally quantified over real executions, so the model may range
///     freely over them.
///   * DEF-PINNED: functionally determined by the conjoined caller facts — an
///     `Eq` conjunct anywhere on the formula's `And` spine grounding the var,
///     via the same fixpoint the callee-side gate runs, in entry state /
///     constants / already-pinned vars. This is what admits computed actuals
///     (`let k = i + 1; helper(a, k)` carries `k == i + 1` as a block def), the
///     alpha-renamed `__trust_replay__*` callee temps (pinned by their own
///     carried defs), and every ordinary MIR block temp of a body VC. Its one
///     extension for a temp pinned only under a disjunction is
///     [`temp_is_repairable_under_one_disjunctive_pin`].
///
/// EVERYTHING ELSE FAILS THE GATE, dropping the candidate (fail-closed, drop-
/// only). The known hostile inhabitants, each a CONFIRMED false-refutation
/// vector when left free:
///   * a HAVOC'D CALL-DEST temp (`j = ext::clamp3(i); helper(a, j)` with no
///     summary fact): `j`'s value is chosen by the unmodeled callee, not by the
///     model — SAT at `j = 9` refutes a caller that may be perfectly safe;
///   * a `freshen_aliasing_opaque_occurrences` `{name}__r1occ{n}` var: the
///     freshening deliberately SPLITS a fixed-but-unknown constant into
///     independent occurrences (sound for discharge, where it only shrinks the
///     UNSAT set) — but as a free SAT dimension it lets the model pick a
///     different value per occurrence of the SAME constant, weakening guard
///     hypotheses below reality (rejected by NAME, before any pin analysis:
///     no real caller place can be constrained through a per-occurrence alias);
///   * a residual `X#tok` versioned read of a reassigned local, a
///     `__trust_sigma_*` fresh var, or any name that resolves to no unique
///     caller local — unclassifiable, hence unconstrained.
pub(super) fn composed_formula_is_caller_entry_grounded(
    func: &VerifiableFunction,
    formula: &Formula,
) -> bool {
    let entry_stable_param = |base: &str| -> bool {
        // Resolve the base to EXACTLY ONE declared local by the canonical
        // emitter spelling (`place_to_var_name` owns demotion/uniqueness);
        // ambiguity fails closed.
        let Some(local) = crate::fn_memo::whole_local_index_by_base(func, base, |l| {
            crate::place_to_var_name(func, &Place::local(l))
        }) else {
            return false;
        };
        // Parameters only: a never-written non-parameter has no defined value
        // at all, and a written one must earn admission through a def pin.
        (1..=func.body.arg_count).contains(&local) && local_versions_collapse_to_bare(func, local)
    };
    let in_domain = |name: &str| -> bool {
        if name.contains("__r1occ") {
            return false;
        }
        let whole = name.strip_suffix("__slice_len").unwrap_or(name);
        if entry_stable_param(whole) {
            return true;
        }
        matches!(split_projection_base(whole), Some((base, _)) if entry_stable_param(base))
    };
    let mut temps: FxHashSet<String> = FxHashSet::default();
    let mut r1occ_reject: Option<String> = None;
    let _ = trust_types::all_free_variable_names(formula, &mut |name| {
        // A per-occurrence opaque alias is unclassifiable BY CONSTRUCTION —
        // reject by name even if some Eq conjunct would appear to pin it.
        if name.contains("__r1occ") {
            r1occ_reject = Some(name.to_string());
            return false;
        }
        if !in_domain(name) && !temps.contains(name) {
            temps.insert(name.to_string());
        }
        true
    });
    let verdict =
        r1occ_reject.is_none() && callee_temps_are_def_pinned(formula, &temps, &in_domain);
    // `TRUST_GROUND_DEBUG=1` prints one line per gate decision: the function,
    // its parameters and their stability, the formula's free variables, which
    // of them this gate could not classify, and the verdict. A dropped
    // refutation is otherwise INVISIBLE — the row simply reads `runtime-checked`
    // and the build succeeds — and reading the predicate instead of running it
    // is what let the nested-`And` defect above survive its own review.
    if ground_debug_enabled() {
        let mut params: Vec<String> = Vec::new();
        for decl in func.body.locals.iter() {
            if (1..=func.body.arg_count).contains(&decl.index) {
                params.push(format!(
                    "{}({}{})",
                    crate::place_to_var_name(func, &Place::local(decl.index)),
                    decl.index,
                    if local_versions_collapse_to_bare(func, decl.index) {
                        ",stable"
                    } else {
                        ",UNSTABLE"
                    }
                ));
            }
        }
        let mut fv: Vec<String> = formula.free_variables().into_iter().collect();
        fv.sort();
        let mut tv: Vec<String> = temps.iter().cloned().collect();
        tv.sort();
        eprintln!(
            "TRUST_GROUND: fn={} argc={} params=[{}] free=[{}] unpinned_candidates=[{}] r1occ={:?} verdict={} formula={:?}",
            func.name,
            func.body.arg_count,
            params.join(" "),
            fv.join(" "),
            tv.join(" "),
            r1occ_reject,
            verdict,
            formula,
        );
    }
    verdict
}

/// Substitute the callee's L0 violation formula into the caller's namespace,
/// or `None` when the result could not be a faithful witness carrier.
///
/// Gates (each is drop-only — rejection can only LOSE a refutation, never
/// mint one):
///   * `Bool(true)`/`Bool(false)` SENTINELS: a fail-close marker or
///     reconstruction placeholder models NOTHING — "solving" it after
///     substitution would refute (or vacuously pass) a formula about no real
///     operation. Skip before any substitution.
///   * RESIDUAL CALLEE LOCALS: every free var of the violation must either
///     resolve — whole-name or via its projection BASE (`a.0` → `a`) — to a σ
///     formal (incl. the `<formal>__slice_len` length names), or be a
///     WHOLE-name callee temp that is DEF-PINNED by the formula's own
///     conjuncts (`callee_temps_are_def_pinned`). Pinned temps are
///     alpha-renamed into the reserved `__trust_replay__*` namespace so no
///     caller-side name can capture them; anything else is rejected — an
///     unpinned temp would range unconstrained (over-approximated SAT — not a
///     witness of any execution). `Formula::free_variables` is binder-aware,
///     so quantifier-bound names do not trip this gate.
///   * σ-FRESH RESULT VARS: `sigma_actual_formula` maps an aliasing-opaque
///     constant actual to a fresh `__trust_sigma_opaque__*` var and
///     `rebind_projected_actual` falls back to `__trust_sigma_field__*` when a
///     projected formal cannot be soundly reattached to the actual place.
///     Both are deliberately-free vars (sound where the obligation must FAIL
///     CLOSED toward "kept"), but here they are unconstrained model freedom —
///     reject the candidate.
pub(crate) fn replay_substituted_callee_violation(
    violation: &Formula,
    replacements: &[(String, Formula)],
) -> Option<Formula> {
    // Modeling-gap sentinels carry no operation semantics. (The whole-formula
    // match is deliberate: a Bool literal nested under real structure is a
    // genuine subterm, not a sentinel.)
    if matches!(violation, Formula::Bool(_)) {
        return None;
    }
    // Partition the free vars: σ-resolvable (exact formal / length name, or a
    // projection whose BASE is one — the substitution rebinding covers exactly
    // these shapes) versus callee temps.
    let in_domain = |name: &str| replacements.iter().any(|(formal, _)| formal == name);
    let mut temps: FxHashSet<String> = FxHashSet::default();
    if !trust_types::all_free_variable_names(violation, &mut |name| {
        if in_domain(name) {
            return true;
        }
        match split_projection_base(name) {
            Some((base, _)) if in_domain(base) => true,
            // A PROJECTED non-σ name (`_3.0`) is not a whole-name temp the
            // def-pin check can reason about — fail closed.
            Some(_) => false,
            None => {
                if !temps.contains(name) {
                    temps.insert(name.to_string());
                }
                true
            }
        }
    }) {
        return None;
    }
    if !callee_temps_are_def_pinned(violation, &temps, &in_domain) {
        return None;
    }
    // Alpha-rename the pinned temps into the reserved replay namespace BEFORE
    // σ-substitution: temps are disjoint from the σ domain by construction,
    // and the fresh names are unspellable as caller places, so the later
    // caller-fact conjunction cannot capture them. Renaming is semantics-
    // preserving (pure alpha over free names occurring nowhere else); sorts
    // are taken from each temp's own `Var` occurrence.
    let renamed = if temps.is_empty() {
        violation.clone()
    } else {
        let mut sorts: FxHashMap<&str, Sort> =
            FxHashMap::with_capacity_and_hasher(temps.len(), Default::default());
        collect_var_sorts(violation, &temps, &mut sorts);
        let rename: Vec<(String, Formula)> = temps
            .iter()
            .map(|t| {
                let sort = sorts.get(t.as_str()).cloned().unwrap_or(Sort::Int);
                (t.clone(), Formula::var_owned(format!("{REPLAY_TEMP_VAR_PREFIX}{t}"), sort))
            })
            .collect();
        substitute_summary_params(violation, &rename)
    };
    let substituted = substitute_summary_params_owned(renamed, replacements);
    // Post-substitution: no deliberately-free σ var may remain (see the
    // prefix doc above).
    if trust_types::any_free_variable_name(&substituted, &mut |v| {
        v.starts_with(SIGMA_FRESH_VAR_PREFIX)
    }) {
        return None;
    }
    Some(substituted)
}

/// First-seen sort of every `Var` node in `temps` (bound or free — over-collection
/// only affects rename-sort selection for names that ARE free temps, where the
/// occurrences agree).
fn collect_var_sorts<'a>(
    formula: &'a Formula,
    temps: &FxHashSet<String>,
    out: &mut FxHashMap<&'a str, Sort>,
) {
    trust_types::visit_formula_nodes(formula, &mut |node| {
        if let Some(name) = node.var_name()
            && temps.contains(name)
            && let Some(sort) = node.var_sort()
            && !out.contains_key(name)
        {
            out.insert(name, sort.clone());
        }
    });
}

/// Refutation-only candidates for the call-site L0 replay lane: the callee's
/// own strict-L0 violation formulas (regenerated WITHOUT its precondition),
/// σ-rebound to the caller's actuals and conjoined with the caller's path
/// condition at the `callee_name` call site(s) matching `call_location`.
///
/// Returns composed `VerificationCondition`s carrying the callee's REAL L0
/// kind at the CALL span, stamped with the caller's function name. SAT on one
/// of these (decided by the caller of this producer, never here) is a
/// counterexample MODULO the fidelity of the conjoined caller model: the
/// gates guarantee every free var of the composed formula is caller-entry
/// state or def-pinned (`composed_formula_is_caller_entry_grounded`), and the
/// model satisfies every CAPTURED caller-side hypothesis (path guards, block/
/// path defs, global facts, own preconditions — the same assembly the callsite
/// precondition lane uses). What they do NOT independently establish is that
/// the assembly captured EVERY constraint dominating the call, nor that the
/// regenerated callee body VC is a complete model of the violation — those are
/// inherited from the guard/def builders and `generate_vcs` respectively.
///
/// Fail-closed empties (each documented at its gate): malformed caller IR,
/// over-budget caller or callee, self-recursive call sites, a summary without
/// an attached `extracted_body` (cross-crate callee — replay unavailable, the
/// honest `incomplete` residual stands), and arity mismatches.
pub fn generate_callsite_l0_replay_candidates(
    func: &VerifiableFunction,
    summaries: &crate::modular::SummaryDatabase,
    callee_name: &str,
    call_location: &SourceSpan,
) -> Vec<VerificationCondition> {
    // Refutation-only lane: a malformed function yields NO candidates (the
    // precondition lane's malformed-IR VC already fails the build closed).
    if crate::validate_function(func).is_err() {
        return Vec::new();
    }
    // verifier-perf: same whole-function gate as the callsite precondition
    // producer. DROP-ONLY — withholding replay candidates can only leave the
    // build at its existing (already fail-closed) verdict.
    if func_exceeds_vcgen_budget(func) {
        return Vec::new();
    }
    // #5-PRE-A critical scoping: a recursive self-call's precondition remains
    // an ordinary caller-side proof request. This helper is only the optional
    // refutation-replay lane: replaying the caller's own body as its "callee"
    // would recurse into the same body rather than independently strengthen
    // that proof request. Never produce self-call replay candidates. Their
    // absence grants no authority; the ordinary precondition row is still
    // generated and unresolved rows fail closed in the compiler consumer.
    if callee_name == func.name || callee_name == func.def_path {
        return Vec::new();
    }
    let Some(summary) = summaries.get(callee_name) else {
        return Vec::new();
    };
    // The extracted body is the F6b session-local ANALYSIS INPUT (zero proof
    // authority; see `FunctionSummary::extracted_body`). Absent — cross-crate
    // or extraction-refused callee — replay is unavailable and the honest
    // `incomplete` classification stands.
    let Some(extracted_body) = summary.extracted_body.as_deref() else {
        return Vec::new();
    };
    if func_exceeds_vcgen_budget(extracted_body) {
        return Vec::new();
    }
    if !func.body.blocks.iter().any(|block| {
        matches!(
            &block.terminator,
            Terminator::Call { func: block_callee, args, span, .. }
                | Terminator::TailCall { func: block_callee, args, span, .. }
                if block_callee == callee_name
                    && span == call_location
                    && summary.param_names.len() == args.len()
        )
    }) {
        return Vec::new();
    }

    // Regenerate the callee's body VCs WITHOUT its contract hypotheses. The
    // callee proved green by ASSUMING `#[requires]` at entry
    // (`conjoin_preconditions_versioned` over `func.preconditions`); the
    // whole point of the replay is that the refuted caller does NOT establish
    // that assumption, and a real execution checks no requires at runtime —
    // so every requires carrier is stripped from the analysis clone.
    // SOUND: stripping hypotheses is the semantics of the violated contract;
    // the composed formula below re-imposes the TRUE constraints (the
    // caller's actuals, definitions, and path guards) instead.
    let mut callee_without_requires = extracted_body.clone();
    callee_without_requires.preconditions.clear();
    callee_without_requires.spec.requires.clear();
    callee_without_requires.contracts.retain(|c| c.kind != ContractKind::Requires);
    // Generated as cleared: the generator does not restate the callee's parameter type
    // ranges into the emptied hypothesis (`without_stated_param_ranges`); the caller's
    // own entry state is re-imposed below.
    let callee_vcs = without_stated_param_ranges(|| generate_vcs(&callee_without_requires));
    if !callee_vcs.iter().any(|vc| {
        vc.kind.proof_level() == trust_types::ProofLevel::L0Safety
            && !matches!(vc.kind, VcKind::UnsupportedMir { .. })
            && !matches!(vc.formula, Formula::Bool(_))
    }) {
        return Vec::new();
    }

    // The same per-caller assembly the callsite PRECONDITION producer builds —
    // deliberately identical (same sanitized view, same guard/def/fact maps),
    // because those conjuncts are exactly what makes a SAT model denote a real
    // caller execution: path guards keep a guarded caller
    // (`if i < 4 { helper(a, i) }`) UNSAT-safe, block/path defs pin computed
    // actuals, global facts and the caller's own stable preconditions restrict
    // the inputs the caller can actually be entered with.
    let arithmetic_safe_func = without_unmodeled_contract_arithmetic(func);
    let func_view = arithmetic_safe_func.as_ref();
    // The memo scopes, on the caller view the assembly reads (`EntryScope`), opened only
    // now: `generate_vcs` above is a metered entry and must stay outside them.
    let _entry_scope = super::EntryScope::enter(func_view);
    let guard_paths_map: std::cell::OnceCell<std::rc::Rc<super::PathGuardMap>> =
        std::cell::OnceCell::new();
    let semantic_guards: std::cell::OnceCell<std::rc::Rc<FxHashMap<BlockId, Vec<Formula>>>> =
        std::cell::OnceCell::new();
    let path_definition_map: std::cell::OnceCell<std::rc::Rc<FxHashMap<BlockId, Vec<Formula>>>> =
        std::cell::OnceCell::new();
    let sv: std::cell::OnceCell<std::rc::Rc<super::StmtVersionCtx>> = std::cell::OnceCell::new();
    // Filtered per candidate as the production producer filters (`RowGlobalFacts::for_row`).
    let global_facts: std::cell::OnceCell<std::rc::Rc<super::RowGlobalFacts>> =
        std::cell::OnceCell::new();
    let own_preconditions: std::cell::OnceCell<Vec<Formula>> = std::cell::OnceCell::new();

    enum KeptReplaySlot {
        One(usize),
        Many(Vec<usize>),
    }
    fn replay_candidate_hash(kind: &VcKind, formula: &Formula) -> u64 {
        use std::hash::{Hash, Hasher};
        let mut hasher = trust_types::fx::FxHasher::default();
        std::mem::discriminant(kind).hash(&mut hasher);
        formula.hash(&mut hasher);
        hasher.finish()
    }

    let mut candidates: Vec<VerificationCondition> = Vec::new();
    // Duplicate suppression: two callee VCs can substitute to the same
    // composed formula (e.g. twin bounds checks over one index). Emitting the
    // duplicate would double-count one violation in the L0 failed summary.
    let mut seen: FxHashMap<u64, KeptReplaySlot> = FxHashMap::default();

    for block in &func_view.body.blocks {
        let (block_callee, args, span) = match &block.terminator {
            Terminator::Call { func, args, span, .. }
            | Terminator::TailCall { func, args, span, .. } => (func, args, span),
            _ => continue,
        };
        // Exact-site match: name AND span. The driver keys its replay request
        // off the refuted Precondition row's location, which the callsite
        // producer stamped from this same terminator span.
        if block_callee != callee_name || span != call_location {
            continue;
        }
        // Arity mismatch: σ would be partial, leaving formals free (the
        // precondition lane mints `SummaryArityMismatch` for this; the replay
        // lane just declines).
        if summary.param_names.len() != args.len() {
            continue;
        }

        // The SAME σ as the P[σ] construction: per-formal actual rendering
        // (stable copy-chain rooting, opaque-constant freshening) plus the
        // `<formal>__slice_len` length replacements.
        let replacements = build_callsite_sigma_replacements(func_view, summary, args);
        let block_live_path_defs: std::cell::OnceCell<Vec<Formula>> =
            std::cell::OnceCell::new();
        let block_sem_guards: std::cell::OnceCell<Vec<Formula>> =
            std::cell::OnceCell::new();

        for callee_vc in &callee_vcs {
            // Strict-L0 kinds only: the replay claim is "the caller can drive
            // the callee into a Level-0 SAFETY violation". L1 rows
            // (pre/postconditions), temporal rows, and `UnsupportedMir`
            // modeling-gap carriers (whose Bool sentinel the substitution gate
            // would reject anyway) are not that claim.
            if callee_vc.kind.proof_level() != trust_types::ProofLevel::L0Safety {
                continue;
            }
            if matches!(callee_vc.kind, VcKind::UnsupportedMir { .. }) {
                continue;
            }
            let Some(substituted) =
                replay_substituted_callee_violation(&callee_vc.formula, &replacements)
            else {
                continue;
            };

            let guard_paths_map =
                guard_paths_map.get_or_init(|| super::guard_map_for(func_view));
            let semantic_guards =
                semantic_guards.get_or_init(|| super::semantic_guard_map_for(func_view, None));
            let path_definition_map =
                path_definition_map.get_or_init(|| super::path_definition_map_for(func_view));
            let sv = sv.get_or_init(|| super::stmt_versions_for(func_view));
            let global_facts =
                global_facts.get_or_init(|| build_global_invariant_facts(func_view));
            let own_preconditions =
                own_preconditions.get_or_init(|| stable_caller_preconditions(func_view));

            // Caller-side composition — mirrors `generate_callsite_precondition_vcs`
            // conjunct-for-conjunct, with the σ-substituted callee VIOLATION in
            // the structural position of ¬P[σ]. Every splice keeps the violation
            // a DIRECT conjunct of a flat `And` (pure ∧-associativity), exactly
            // like the precondition lane.
            let mut formula = v2_formula_with_block_defs(func_view, block, substituted);

            let live = block_live_path_defs.get_or_init(|| {
                block_live_callsite_path_defs(func_view, block, sv, path_definition_map)
            });
            if !live.is_empty() {
                formula = splice_flat_prefix(live, formula);
            }

            if let Some(block_guard_paths) = guard_paths_map.get(&block.id) {
                formula = v2_formula_with_path_guards(
                    func_view,
                    sv,
                    block.id,
                    block_guard_paths,
                    formula,
                );
            }

            let sem_with_bare = block_sem_guards.get_or_init(|| {
                block_sem_guards_with_bare_variants(func_view, block.id, semantic_guards)
            });
            if !sem_with_bare.is_empty() {
                formula = splice_flat_prefix(sem_with_bare, formula);
            }

            let row_facts = global_facts.for_row(&formula);
            if !row_facts.is_empty() {
                let mut conjuncts = row_facts;
                match formula {
                    Formula::And(inner) => conjuncts.extend(inner),
                    other => conjuncts.push(other),
                }
                formula = Formula::And(conjuncts);
            }

            if !own_preconditions.is_empty() {
                formula = splice_flat_prefix(own_preconditions, formula);
            }

            let occ = std::cell::Cell::new(0u32);
            let formula = freshen_aliasing_opaque_occurrences_owned(formula, &occ);
            let formula = normalize_ssa_version_tokens_owned(func_view, formula);

            // Belt-and-braces σ re-check: the caller-side conjuncts never mint
            // σ-fresh names, but the composed formula is what the driver hands
            // to the solver, so re-check the invariant at the emission seam.
            if trust_types::any_free_variable_name(&formula, &mut |v| {
                v.starts_with(SIGMA_FRESH_VAR_PREFIX)
            }) {
                continue;
            }
            // THE caller-side soundness gate: every free var of the composed
            // formula must be entry-state or def-pinned (see
            // `composed_formula_is_caller_entry_grounded`). Without it, a
            // havoc'd call-dest actual or an `__r1occ` opaque alias is a free
            // SAT dimension and a SAFE caller composes to a false refutation.
            if !composed_formula_is_caller_entry_grounded(func_view, &formula) {
                continue;
            }

            let hash = replay_candidate_hash(&callee_vc.kind, &formula);
            let next_idx = candidates.len();
            match seen.entry(hash) {
                std::collections::hash_map::Entry::Vacant(slot) => {
                    slot.insert(KeptReplaySlot::One(next_idx));
                }
                std::collections::hash_map::Entry::Occupied(mut slot) => match slot.get_mut() {
                    KeptReplaySlot::One(prev) => {
                        let prev = *prev;
                        if candidates[prev].kind == callee_vc.kind
                            && candidates[prev].formula == formula
                        {
                            continue;
                        }
                        *slot.get_mut() = KeptReplaySlot::Many(vec![prev, next_idx]);
                    }
                    KeptReplaySlot::Many(indices) => {
                        if indices.iter().any(|&idx| {
                            candidates[idx].kind == callee_vc.kind
                                && candidates[idx].formula == formula
                        }) {
                            continue;
                        }
                        indices.push(next_idx);
                    }
                },
            }
            candidates.push(VerificationCondition {
                // The callee's REAL L0 kind — the composed row IS the entailed
                // callee-side safety claim, surfaced at the caller's call span.
                kind: callee_vc.kind.clone(),
                function: func_view.name.as_str().into(),
                location: span.clone(),
                formula,
                contract_metadata: None,
                obligation: None,
            });
        }
    }
    candidates
}

/// [`generate_callsite_l0_replay_candidates`] into the caller's context `rows`, the body's
/// (T3 C07p, design D-VC-1): every candidate is interned through the row oracle and the
/// candidates are returned as generated.
pub fn generate_callsite_l0_replay_candidates_rows(
    func: &VerifiableFunction,
    summaries: &crate::modular::SummaryDatabase,
    callee_name: &str,
    call_location: &SourceSpan,
    rows: &mut trust_types::vc_context::VcContext,
) -> Vec<VerificationCondition> {
    let candidates =
        generate_callsite_l0_replay_candidates(func, summaries, callee_name, call_location);
    intern_eager_rows(rows, &candidates);
    candidates
}
