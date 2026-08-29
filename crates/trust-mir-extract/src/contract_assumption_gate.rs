//! Soundness gates for using `#[trust::requires]` predicates as *body
//! assumptions* (hypotheses conjoined onto the function's own safety VCs).
//!
//! A contract precondition is caller-proved, so assuming it inside the body is
//! assume-guarantee sound — but only if the assumed fact really speaks about
//! the function's *entry parameters*. Two live hazards gate-checked here:
//!
//! * **Shadow collision (P0, observed false-PROVE):** the VC variable namespace
//!   is debug names, and `build_debug_name_map` is last-write-wins. A body
//!   `let x = …;` shadowing a parameter `x` makes the predicate's `x > 0`
//!   constrain the *body* local in the formula — proving overflow obligations
//!   about an unconstrained value (probe `t_shadow`, 2026-06-09).
//! * **Vacuity:** an unsatisfiable predicate (`x > 10 && x < 5`) would admit
//!   any body under a false hypothesis. We require a concrete ground witness
//!   before assuming; a found witness is a model, so the check cannot
//!   false-positive.
//!
//! The shadow check is about SOURCE bindings. A debug name in the contract
//! lowerer's own reserved namespace (`__ret` from `#[ensures]`, `__old_*`, `_0`,
//! …) is NOT one: `build_debug_name_map` demotes that whole family, so it never
//! names a local in the extracted body and can never be what a formula variable
//! resolves to. Copy-propagation routinely parks such an entry on a parameter
//! local, and reading that as a user shadow dropped true, caller-proved
//! preconditions and turned provable postconditions into refutations. See
//! `reserved_synthetic_debug_name` — the exemption is confined to the alias
//! scan; a predicate that REFERENCES a reserved spelling is still rejected.
//!
//! Gate failure NEVER rejects the function — it only drops the assumption
//! (assume nothing), which can only weaken PROVE toward FAIL/UNKNOWN. The
//! call-site Precondition VCs are generated from a separate re-parse and are
//! deliberately NOT gated: callers must prove the full declared predicate.
//!
//! # The FORCED PARAMETER RESTATEMENT (`forced_parameter_alias`)
//!
//! One shape reaching the drops above is not an ambiguity at all — it is ONE
//! entity under TWO spellings. For
//!
//! ```ignore
//! #[requires(n >= 0)] #[ensures(|r| *r >= 0)] fn f(n: i32) -> i32 { let x = n; x }
//! ```
//!
//! MIR copy-propagation makes the body's `x` an alias of the parameter local, so
//! BOTH `n` and `x` are `var_debug_info` names on `_1`, and the last-write-wins
//! collapse in `build_debug_name_map` names local 1 `"x"`. The clause is written
//! in the SOURCE's namespace, the body's VCs in the BODY's; the two disagree,
//! every check above reads that as a shadow, and a TRUE, caller-proved
//! precondition is dropped. **`n` is parameter position 1; `x` is what the body
//! calls that same local.** When the correspondence between the two namespaces is
//! FORCED, this gate RESTATES the clause in the body's spelling and keeps it,
//! instead of dropping the set.
//!
//! THIS IS THE ONE PLACE IN THIS FILE THAT CAN MINT A `PROVE`, so the conditions
//! are stated as a proof, not as a heuristic. Write `p` for the target parameter
//! POSITION, `_p` for its local, `s` for the clause's spelling and `b` for the
//! body's. A `var_debug_info` entry is called a ROW; `build_debug_name_multimap`
//! pushes one vector element per row and never dedups, so row MULTIPLICITY is
//! visible here even though `build_debug_name_map`'s collapse hides it.
//!
//! **(I) A parameter position has exactly one body local.** `rustc_mir_build`'s
//! `Builder::args_and_body` allocates one local per parameter, in declaration
//! order, immediately after the return place (`Local::arg(index)`), so locals
//! `1..=arg_count` ARE the parameters in declaration order. `extract_body`
//! preserves `LocalDecl::index` (`validate_codegen_fidelity` rejects any body
//! whose local order changed), so position ↔ local is a bijection in the
//! extracted model too.
//!
//! **(II) The map is UNIQUE and TOTAL, not a preference.** The restatement fires
//! only when EXACTLY ONE clause spelling is unbindable in the body namespace and
//! EXACTLY ONE parameter position is not already named by the clause. With `k` of
//! either there are `k!` candidate maps and no ground to prefer one, so the gate
//! declines and DROPS exactly as before. Same for an unnamed or non-identifier
//! parameter position (it could be the position the clause means), a
//! reserved/synthetic `s`, a sort the clause does not use consistently or that
//! `p`'s declared type does not admit, and any quantifier (`rename_var` is
//! syntactic and does not respect binders, so a rename could capture).
//!
//! **(III) NO CONTRACT-BEARING FUNCTION HAS A PARAMETER IN THE RESERVED FAMILY.**
//! This is the POSITIVE fact the whole identification rests on, and it is a
//! compiler admission gate, not an inference from what happens to be visible:
//!
//!   * `trust_contract_query::trust_contracts` calls
//!     `reject_unrepresentable_contract_parameter_names` BEFORE lowering a single
//!     clause; any parameter-pattern binding for which
//!     `source_contract_synthetic_name_collision` is `Some` gets a hard
//!     `span_err` and the query returns `TrustContractBundle::empty`;
//!   * `extract_contracts` repeats the check (`first_synthetic_contract_parameter`
//!     → `reject_contracts_for_synthetic_parameter`) on BOTH of its sources — the
//!     compiler bundle and the HIR-attribute compatibility seam — because that
//!     seam can run with `compiler_contracts == None`.
//!
//! So a function with a reserved-family parameter name has NO contracts at all,
//! `parse_contract_specs_with_typed` yields no preconditions, and this gate
//! returns on its first line. (The extractor's own check is keyed on
//! `def_id.as_local()`, but a NON-local definition's bundle was produced by the
//! `trust_contracts` query in its OWN crate, where the query-level gate above
//! already ran — so the invariant is crate-independent.) Consequently, for every function that can reach the
//! restatement: **the parameter's own source name is NOT demoted by
//! `build_debug_name_map`**, i.e. it participates in the last-write-wins collapse
//! rather than vanishing from it. (That is also the load-bearing premise of the
//! PRE-EXISTING `reserved_synthetic_debug_name` exemption in the alias scan: a
//! `__` row on a parameter local can only be an artifact of Trust's own lowering
//! or a reserved-spelled BODY binding, never the parameter's own name.)
//!
//! **(IV) `s` really is parameter `p`'s SOURCE name — CHECKED, not argued.** A
//! clause identifier is resolved in the function's SIGNATURE scope, so it is
//! either a parameter of this function or a non-parameter item (a
//! `const`/`static`); it can never be a body `let`, which is not in scope there.
//! Assuming a `const`'s predicate about a parameter would be a false PROVE — the
//! exploit this condition exists to exclude is a module `const n` plus a body
//! `let n = …;` whose row copy-props onto `_p`, which makes `s` LOOK corroborated
//! while denoting something else.
//!
//! The identification is made by ASKING HIR, in one equality:
//!
//! ```text
//!     hir_parameter_source_names(tcx, body)[p - 1] == Some(s)
//! ```
//!
//! `hir_parameter_source_names` (`crates/trust-mir-extract/src/lib.rs`) yields
//! one entry per HIR parameter in declaration order, `Some(name)` iff that
//! parameter's pattern is a plain by-value binding of a simple identifier. So the
//! equality says exactly what the restatement needs — *MIR argument `_p` was
//! declared in source as a simple binding spelled `s`* — with no appeal to row
//! ordering, to `var_debug_info` at all, or to any premise living in another
//! crate. When the vector is absent (no local HIR body) or its length disagrees
//! with `body.arg_count`, the gate declines: an unanswerable question is not a
//! yes.
//!
//! **This replaces a MIR-row ORDERING argument that was unsound.** The previous
//! text closed the identification by claiming a parameter's row precedes every
//! body binding's row on `_p`, so the first non-demoted row on `_p` had to be
//! `s`'s. That step silently presumed `_p` carries a row of the parameter's own,
//! and for a `ref`-bound parameter it does not: `args_and_body`
//! (`compiler/rustc_mir_build/src/builder/mod.rs`) emits an argument's debug row
//! only under `pat.simple_ident()`, which is `None` for `ref q`, while `CopyProp`'s
//! `Replacer::visit_local` still rewrites BODY bindings' rows onto `_p`. The
//! companion claim — that a borrowed local cannot be a merge head — was false
//! twice over: `ssa.rs`'s `borrowed_locals` test applies to the copy's
//! DESTINATION, and an immutably-borrowed `Freeze` local (every integer type) is
//! deliberately kept SSA. The concrete exploit was
//!
//! ```rust,ignore
//! const n: i32 = 5;                                  // TRUE clause
//! #[trust::requires(n >= 0)] #[ensures(|r: &i32| *r >= 0)]
//! fn f(ref q: i32) -> i32 { let n = *q; let x = n; x }   // f(-7) == -7
//! ```
//!
//! where the census saw exactly two non-demoted names on `_1` (`n` and `x`, both
//! ordinary body `let`s), restated `n >= 0` as `x >= 0`, and PROVED a false
//! postcondition. The HIR equality above refuses it at the first step, because
//! `ref q` is not a simple by-value binding and its entry is `None`. `_` and
//! `q @ sub` are refused by the same entry for the same reason, so the three
//! pattern cases that the old text handled with three separate MIR-pass arguments
//! now collapse into one check that cannot silently rot when a MIR pass changes.
//!
//! The row-census conditions below are RETAINED, but their job is now narrower:
//! they establish that the assumed fact lands on a name the VC actually reads,
//! and they refuse ambiguity. They no longer carry the identification.
//!
//!   1. `s` has EXACTLY ONE row, and it is on `_p`;
//!   2. `b` has EXACTLY ONE row, and it is on `_p`; and `b` names exactly one
//!      EXTRACTED local, or `place_to_var_name` would demote it to the
//!      `_<local>` fallback and the assumed fact would bind nothing the VC reads;
//!   3. every OTHER row on `_p` carries a name that is BOTH demoted and one of
//!      the finite spellings Trust's own contract lowering mints — see
//!      `trust_lowered_contract_debug_name` — and each such name has exactly one
//!      row on `_p`.
//!
//! **(V) The restatement cannot capture or steal a binding.** `b` is chosen from
//! the parameter positions the clause does NOT mention, so the rename never merges
//! two distinct clause variables; `s` is not a body-namespace spelling, so nothing
//! in the body binds it; and no clause carries a quantifier.
//!
//! **(VI) The entry fact cannot go STALE — and the protection follows the RENAMED
//! name, not the source one.** `trust-vcgen` conjoins preconditions through
//! `conjoin_preconditions_versioned`, which version-renames every PLACE variable
//! of the VC body to its value at the read point (`version_rename_at` /
//! `StmtVersionCtx::version_token_at`) and leaves the preconditions at the bare
//! ENTRY spelling. A precondition about a place the body reassigned therefore
//! names a different SMT variable from the renamed read and cannot constrain it —
//! the retired `formula_survives_redefs` kill's drop, achieved by
//! name-disjointness (`flip_matches_kill_stmt` is the statement-granular
//! equivalence witness). That machinery is keyed on the names `place_to_var_name`
//! mints, i.e. on `b` — so restating the clause as `b` puts it INSIDE the
//! staleness discipline, whereas the source spelling `s` is not a place name at
//! all and would receive none of it. The rename is what makes the protection
//! apply, and the assumed fact is about `_p`'s ENTRY value, which is the caller's
//! argument by (I) whatever the body later does to `_p`.
//!
//! **(VII) Everything else is unchanged.** The restatement runs BEFORE the checks
//! above and the renamed set then passes through ALL of them (shadow scan,
//! multiplicity, ground witness); only `s` itself is exempted from the alias scan,
//! and only because (IV) established it is the same entity as `b`, never a
//! competing binding. Any failure of any condition returns `None` and the set
//! drops byte-identically to before.

use trust_types::fx::{FxHashMap, FxHashSet};
use trust_types::{Formula, Rvalue, Statement, Terminator, Ty, VerifiableBody};

/// Why contract-derived preconditions were not assumed for body verification.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum AssumeSkipReason {
    /// Predicate uses syntax outside the v1 integer/boolean fragment.
    UnsupportedSyntax,
    /// Predicate references a variable that is not a parameter debug name.
    NonParamVariable(String),
    /// A non-parameter local shares a debug name with a referenced parameter,
    /// so the formula-level fact would bind the wrong variable.
    ShadowedParamName(String),
    /// No concrete ground witness found — the predicate is (or may be)
    /// unsatisfiable; assuming it could vacuously verify the body.
    NoSatisfiableWitness,
}

impl AssumeSkipReason {
    pub fn describe(&self) -> String {
        match self {
            AssumeSkipReason::UnsupportedSyntax => {
                "predicate uses syntax outside the assumable integer fragment".to_string()
            }
            AssumeSkipReason::NonParamVariable(name) => {
                format!("predicate references `{name}`, which is not a parameter")
            }
            AssumeSkipReason::ShadowedParamName(name) => format!(
                "a body local shadows parameter `{name}`; the assumed fact would bind the wrong variable"
            ),
            AssumeSkipReason::NoSatisfiableWitness => {
                "no satisfiable witness found for the predicate; refusing a possibly-vacuous assumption"
            }
            .to_string(),
        }
    }
}

/// Gate contract-derived preconditions before they become body hypotheses.
///
/// `debug_name_locals` is the RAW debug-info name → locals multimap (every
/// `var_debug_info` entry, no last-write-wins collapse). The collapsed
/// per-local names on `body.locals` are NOT sufficient: optimized MIR
/// copy-propagates `let x = z;` so the shadow's debug entry lands on `z`'s own
/// param local — invisible to an index-based scan, observed still-false-proving
/// in build #32 validation.
///
/// On ANY gate failure, drops ALL contract-derived preconditions (collective
/// drop — partial assumption sets are harder to reason about) and returns the
/// reasons for diagnostics. Synthetic always-true facts (enum-discriminant
/// ranges) are appended by the caller AFTER this gate and are not affected.
pub fn gate_contract_preconditions(
    preconditions: &mut Vec<Formula>,
    body: &VerifiableBody,
    debug_name_locals: &FxHashMap<String, Vec<usize>>,
    hir_param_source_names: Option<&[Option<String>]>,
) -> Vec<AssumeSkipReason> {
    if preconditions.is_empty() {
        return Vec::new();
    }

    let param_names: FxHashSet<&str> = body
        .locals
        .iter()
        .filter(|local| local.index >= 1 && local.index <= body.arg_count)
        .filter_map(|local| local.name.as_deref())
        .collect();

    // Parameters that are SHARED references (`&T`, not `&mut T`). The pointee of
    // a `&T` is immutable for the parameter's lifetime, so a caller-proved entry
    // fact over `*a` (`#[requires(*a <= 100)]`) holds at every body read — assuming
    // it is assume-guarantee sound. A `&mut T` pointee CAN be mutated in the body,
    // which would stale the entry fact (a false-PROVE hazard), so those derefs are
    // NOT assumable. See `assumable_param_base`.
    let shared_ref_params: FxHashSet<&str> = body
        .locals
        .iter()
        .filter(|local| local.index >= 1 && local.index <= body.arg_count)
        .filter(|local| matches!(&local.ty, Ty::Ref { mutable: false, .. }))
        .filter_map(|local| local.name.as_deref())
        .collect();

    // Trust (piece #8 — length-relationship preconditions): the LENGTH symbols
    // admissible for THIS body's slice/array PARAMETERS. A precondition like
    // `n <= arr__slice_len` speaks about the length of a slice/array parameter
    // `arr`, which is an ENTRY fact the caller can render (σ-length rendering) and
    // discharge — exactly the caller-supplied-loop-bound family (`for i in 0..n {
    // arr[i] }`). The admitted solver spellings are:
    //   * `<param_debug_name>__slice_len` — a runtime `&[T]`/`&mut [T]`/`*mut [T]`
    //     slice parameter's canonical length var, and
    //   * `__trust_constparam_{index}_{name}` — a const-generic array parameter's
    //     length (`&[T; N]`, `[T; N]` with N a const param).
    // Exact source parsing lowers `arr.len()` to the projection leaf `arr__len`.
    // That leaf is NEVER admitted as an independent free variable: for one
    // unique, length-stable runtime-slice parameter only, `admissible_lengths`
    // rebinds it to canonical `arr__slice_len` before validation and witness
    // search. Thus the source contract, bounds VC, and modular σ summary all
    // consume one Formula term rather than relying on a free-variable coincidence.
    // Admitting a length symbol is sound ONLY when the parameter's length is
    // STABLE for the whole body (INV-1): a `&mut [T]` param that the body reslices
    // to a shorter view (`let arr = &mut arr[..1];`) would make `arr__slice_len`
    // denote the ORIGINAL length while the indexed slice is shorter — a false
    // PROVE. `slice_param_length_is_stable` rejects any reslice/reassign/`&mut`/
    // projected store of the param, so an unstable slice param drops its length
    // symbol from the whitelist (fail-closed: the assumption is dropped, never a
    // false PROVE). An immutable array/SymArray length has no mutation channel at
    // all (INV-3), so it is always admissible.
    let lengths = admissible_lengths(body, debug_name_locals);
    for formula in preconditions.iter_mut() {
        for (source, canonical) in &lengths.source_rebindings {
            if formula.free_variables().contains(source) {
                *formula = formula.rename_var(source, canonical);
            }
        }
    }
    let length_syms = lengths.canonical;

    // Trust (forced parameter restatement): the clause and the body are two
    // SPELLINGS of one entity whenever copy-propagation plus the last-write-wins
    // debug-name collapse renamed a parameter out from under the source. Restate
    // the clause in the body's own spelling when — and ONLY when — the
    // correspondence is FORCED; see the module header (I)–(VII) for the full
    // argument, whose load-bearing step is (III): a contract-bearing function
    // provably has no reserved-family parameter name, so the parameter's own
    // `var_debug_info` row survives the collapse and the row census below pins it
    // to `source`. On `None` nothing is rewritten and the checks below run
    // byte-identically to before, so a genuine ambiguity still drops.
    let forced = forced_parameter_alias(
        preconditions,
        body,
        debug_name_locals,
        &length_syms,
        hir_param_source_names,
    );
    if let Some(alias) = &forced {
        for formula in preconditions.iter_mut() {
            *formula = formula.rename_var(&alias.source, &alias.body_spelling);
        }
    }

    let mut reasons = Vec::new();
    let mut referenced: FxHashSet<String> = FxHashSet::default();

    for formula in preconditions.iter() {
        if !in_assumable_fragment(formula) {
            reasons.push(AssumeSkipReason::UnsupportedSyntax);
            continue;
        }
        for var in formula.free_variables() {
            // Trust (piece #8): a whitelisted slice/array-parameter length symbol is
            // admissible and EXEMPT from the debug-name shadow/witness discipline —
            // it is not a debug name, so it cannot shadow a local or alias a param
            // local. Skip it before `assumable_param_base` (which would reject it as
            // a NonParamVariable). It is NOT added to `referenced`, so the shadow
            // loops below never see it.
            if length_syms.contains(var.as_str()) {
                continue;
            }
            // Normalize each free variable to the PARAMETER it is caller-bound to
            // (bare `a`, or a shared-ref deref `a*` → `a`); anything else is not
            // assumable. The shadow/witness checks below then operate on the base
            // parameter name, so a sound deref term binds the real parameter local.
            match assumable_param_base(&var, &param_names, &shared_ref_params) {
                Some(base) => {
                    referenced.insert(base.to_string());
                }
                None => {
                    // A raw debug name can still point at a parameter local even
                    // when the collapsed per-local name chose a different alias.
                    // Calling that shape merely "non-parameter" loses the more
                    // important fact: the formula namespace is ambiguous.  It is
                    // exactly the copy-propagated-shadow hazard this gate exists
                    // to reject.  Classify it as shadowing and keep it in the
                    // referenced set so the multimap checks below also diagnose
                    // every colliding alias on that local.
                    let raw_base = var.strip_suffix('*').unwrap_or(var.as_str());
                    // If `raw_base` is already the parameter's canonical name,
                    // rejection came from the term shape (for example `a*` on
                    // `a: &mut T`), not from a debug-name alias. Keep that as a
                    // non-parameter term; only the collapsed-name mismatch is
                    // evidence of the copy-propagated shadow hazard.
                    let aliases_param = !param_names.contains(raw_base)
                        && debug_name_locals.get(raw_base).is_some_and(|locals| {
                            locals.iter().any(|local| *local >= 1 && *local <= body.arg_count)
                        });
                    if aliases_param {
                        referenced.insert(raw_base.to_string());
                        reasons.push(AssumeSkipReason::ShadowedParamName(raw_base.to_string()));
                    } else {
                        reasons.push(AssumeSkipReason::NonParamVariable(var.clone()));
                    }
                }
            }
        }
    }

    // Shadow collision. The formula namespace is debug names, so an assumed
    // fact about name N is sound only when N denotes EXACTLY ONE local and
    // that local is a parameter. Two hazard shapes, both fatal:
    //  * a body local carries a referenced param's name (classic shadow);
    //  * copy-prop attached a shadow's debug entry to ANOTHER local (often a
    //    different param's), so N maps to several locals — or a param local
    //    carries several names. Multiplicity in the raw multimap catches both.
    for name in &referenced {
        match debug_name_locals.get(name.as_str()) {
            Some(locals) => {
                let mut distinct: Vec<usize> = locals.clone();
                distinct.sort_unstable();
                distinct.dedup();
                let is_unique_param =
                    distinct.len() == 1 && distinct[0] >= 1 && distinct[0] <= body.arg_count;
                if !is_unique_param {
                    reasons.push(AssumeSkipReason::ShadowedParamName(name.clone()));
                }
            }
            // Referenced but absent from debug info entirely: cannot bind it
            // to a parameter value.
            None => reasons.push(AssumeSkipReason::NonParamVariable(name.clone())),
        }
    }

    // A param local carrying MORE THAN ONE debug name (e.g. its own plus a
    // copy-propagated shadow's) makes any referenced name on it ambiguous.
    for (name, locals) in debug_name_locals {
        if referenced.contains(name) {
            continue;
        }
        // Trust (synthetic-alias over-rejection, 2026-08-06): a name in the
        // contract lowerer's RESERVED namespace is not a user binding and cannot
        // be the alias that steals a referenced parameter's spelling. See
        // `reserved_synthetic_debug_name`: `build_debug_name_map` demotes exactly
        // this family, so such a name NEVER becomes any local's name in the
        // extracted `VerifiableBody` — it is not in the formula namespace at all,
        // and no formula variable can resolve to it. `#[ensures]` lowering mints
        // `__ret`, and copy-propagation lands its `var_debug_info` entry on the
        // parameter local of `fn f(n: i32) -> i32 { n }`; treating that as a shadow
        // dropped the authored `n >= 0` and made a TRUE postcondition refute.
        // NOTE the asymmetry that makes this the right place to fix it: the raw
        // multimap fed to this gate is deliberately UNFILTERED (it needs
        // multiplicity), while the collapsed name map the body is built from is
        // filtered — so only this scan ever sees a reserved name.
        // A reserved name that the predicate itself REFERENCES is untouched: it is
        // rejected by the first loop above (it cannot be in `param_names`, since
        // demotion left the local unnamed) and never reaches this `continue`.
        if reserved_synthetic_debug_name(name) {
            continue;
        }
        // Trust (forced parameter restatement): the SOURCE spelling we just
        // restated is NOT a competing binding on the parameter local — module
        // header (IV) established that it is that parameter's own source name,
        // i.e. the SAME entity the referenced body spelling denotes. Reporting it
        // as a shadow would drop the very assumption the restatement exists to
        // keep. The exemption is exactly one name, is minted only when
        // `forced_parameter_alias` returned `Some`, and that function already
        // pinned `source` to a SINGLE row on the target parameter local and
        // required every OTHER row there to be one of the finite spellings
        // Trust's own contract lowering mints — so no user binding rides in on it.
        if forced.as_ref().is_some_and(|alias| alias.source == *name) {
            continue;
        }
        for local in locals {
            if *local >= 1 && *local <= body.arg_count {
                // Another name aliases a param local; if any referenced name
                // also resolves to this local the binding is ambiguous.
                if debug_name_locals.iter().any(|(other, ls)| {
                    other != name && referenced.contains(other) && ls.contains(local)
                }) {
                    reasons.push(AssumeSkipReason::ShadowedParamName(name.clone()));
                }
            }
        }
    }

    if reasons.is_empty() && !has_ground_witness(preconditions, body, &length_syms) {
        reasons.push(AssumeSkipReason::NoSatisfiableWitness);
    }

    if !reasons.is_empty() {
        preconditions.clear();
    }
    reasons
}

/// Whether `name` is a MIR debug name in the contract lowerer's own reserved
/// synthetic namespace — `__ret` from `#[ensures]` lowering, `__old_*`, the
/// positional `_0`/`_1` spellings, `<p>__slice_len`, `__trust_constparam_*`, the
/// modeled-accessor `__len`/`__discr`/`__value`/`__sign` leaves, and every
/// future addition to the `__` family (`source_contract_synthetic_name_collision`
/// reserves the whole family "rather than chasing a perpetually incomplete
/// prefix list").
///
/// **`build_debug_name_map` filters on a superset of this, and that containment
/// is the soundness argument for skipping such a name in the alias scan.** The
/// extracted body's parameter names come from that map, which drops the whole
/// reserved family; so a `__` name is never a `LocalDecl::name` at an index the
/// gate reads, never a `place_to_var_name` render, and therefore never a
/// spelling a Formula variable can resolve to. It cannot change which local the
/// user's `n` denotes — it can only be an artifact of contract lowering plus
/// copy-propagation parking a compiler-generated debug entry on a parameter
/// local.
///
/// PRECISION ON THAT CLAIM (it was first written too strongly): `LocalDecl::name`
/// is not literally written in one place. `cell_threading::Fx::fresh_local` also
/// writes one, with reserved spellings (`__thread_payload`, `__thread_rem`).
/// Those are appended POST-extraction at indices above `arg_count`, and this
/// gate reads the raw MIR `var_debug_info` multimap, which cannot contain them —
/// so the exemption still holds. The invariant that carries it is the narrower
/// one: no local at index <= `arg_count` in an `extract_body`-produced body
/// carries a reserved name.
///
/// Keep the two call sites on this one function: if the reserved family and the
/// demotion filter ever diverge, a name could be BOTH a live body spelling and
/// exempt from the shadow scan, which is exactly the false-PROVE shape this gate
/// exists to reject.
pub(crate) fn reserved_synthetic_debug_name(name: &str) -> bool {
    // NARROWED to `GeneratedMetadata` — the `__` family — deliberately, and NOT
    // widened to "any reserved spelling". `source_contract_synthetic_name_
    // collision` also reserves `result`, `_0`/`_<digits>`, the predicate
    // vocabulary, and `old_*`. The `old_*` group is ORDINARY LEGAL RUST
    // BINDINGS: `old_count`, `old_n`. Exempting it from the alias scan would
    // make a genuine user shadow invisible to this gate and let an ambiguous
    // entry fact be assumed — a false-PROVE, i.e. the one direction this gate
    // exists to prevent. Only `__` is a namespace Trust's own MIR/Formula producers
    // own outright, and only `__ret` (parked on a parameter local by
    // `#[ensures]` lowering plus copy-propagation) is the artifact this
    // exemption is for.
    matches!(
        trust_types::source_contract_synthetic_name_collision(name),
        Some(trust_types::SourceContractSyntheticNameCollision::GeneratedMetadata)
    )
}

/// The one restatement that puts a contract-derived precondition into the BODY's
/// own namespace: the clause's spelling of a parameter, and the body's spelling
/// of that same parameter local.
#[derive(Debug, Clone, PartialEq, Eq)]
struct ForcedParameterAlias {
    /// The clause's spelling — established to be the parameter's SOURCE name.
    source: String,
    /// The body's spelling of that same parameter local — the name
    /// `place_to_var_name` mints for every read of it, and therefore the name the
    /// staleness/versioning discipline is keyed on.
    body_spelling: String,
}

/// The FORCED `(source spelling → body spelling)` restatement for `preconditions`,
/// or `None` whenever the correspondence is not uniquely determined — in which
/// case nothing is rewritten and the gate's existing checks drop the set exactly
/// as before.
///
/// **The full soundness argument is the module header (I)–(VII); read it before
/// changing any condition here.** In one line: MIR pins a parameter POSITION to
/// one local; the uniqueness conditions make the position↔name map total and
/// singular; the compiler's own parameter-name admission gate proves the
/// parameter's source name cannot be demoted; and the ROW census below (exactly
/// one row per spelling, every other row on that local one Trust's contract
/// lowering minted) plus "parameter rows are emitted first" force `source` to be
/// that parameter's own source name rather than a same-named `const`/`static` or
/// a body binding.
///
/// This is the crate-local twin of `trust_vcgen::generate::entry_hypothesis::
/// forced_parameter_alias`, which recovers the SAME positional correspondence for
/// the dropped-entry-hypothesis tripwire. The two crates share no dependency, so
/// the conditions are duplicated deliberately — but note the asymmetry: that one
/// can only ever REFUSE to emit a refutable row (it returns names, and the only
/// renamed formula is local to a `bool`-returning function), while THIS one mints
/// an assumption. Hence the raw-debug corroborations below, which the vcgen twin
/// does not need and does not have the inputs for.
fn forced_parameter_alias(
    preconditions: &[Formula],
    body: &VerifiableBody,
    debug_name_locals: &FxHashMap<String, Vec<usize>>,
    length_syms: &FxHashSet<String>,
    hir_param_source_names: Option<&[Option<String>]>,
) -> Option<ForcedParameterAlias> {
    if body.arg_count == 0 || preconditions.is_empty() {
        return None;
    }

    // (0) The HIR parameter spellings, in declaration order — module header (IV).
    // This is the ONLY thing that identifies a clause variable as a parameter's
    // own source name, so its absence is a decline rather than a fallback to an
    // inference over MIR rows. A length disagreement with MIR's `arg_count` means
    // the two views of the signature do not correspond position-for-position
    // (e.g. a lowering that splits or synthesizes an argument), and indexing it
    // by a MIR local would then be reading the wrong parameter.
    let hir_param_source_names = hir_param_source_names?;
    if hir_param_source_names.len() != body.arg_count {
        return None;
    }

    // (1) The parameter list in DECLARATION ORDER, with the body spelling, the
    // declared type and the local index of each position. A position missing from
    // `locals`, unnamed, or carrying a non-identifier spelling makes the whole
    // correspondence undetermined — it could be the position the clause means —
    // so all three decline for the WHOLE function, not for that position alone.
    // The unnamed case is also what excludes a `_` or `ref`-bound parameter, whose
    // local can carry no body row at all (module header (IV), last paragraph).
    let mut parameters: Vec<(&str, &Ty, usize)> = Vec::with_capacity(body.arg_count);
    for index in 1..=body.arg_count {
        let decl = body.locals.iter().find(|local| local.index == index)?;
        let name = decl.name.as_deref()?;
        if !plain_source_binding(name) {
            return None;
        }
        parameters.push((name, &decl.ty, index));
    }

    // (2) Only clauses this gate could assume at all, and no binder anywhere:
    // `rename_var` is a SYNTACTIC rewrite with no binder awareness, so a
    // quantified clause could capture. (`in_assumable_fragment` already rejects
    // `Forall`/`Exists` via its catch-all; the explicit check keeps the reason
    // legible and survives any future widening of the fragment.)
    for clause in preconditions {
        if !in_assumable_fragment(clause) || formula_binds_a_variable(clause) {
            return None;
        }
    }

    // (3) EXACTLY ONE clause spelling the body namespace cannot bind. The body
    // namespace is the extracted locals' names plus the admitted length symbols
    // (which are canonical solver leaves, already rebound by the caller). Two
    // unbindable spellings leave `k!` orderings and no ground to pick one.
    let body_names: FxHashSet<&str> =
        body.locals.iter().filter_map(|local| local.name.as_deref()).collect();
    let mut clause_vars: FxHashSet<String> = FxHashSet::default();
    for clause in preconditions {
        clause_vars.extend(clause.free_variables());
    }
    let mut unresolved = clause_vars
        .iter()
        .filter(|name| !body_names.contains(name.as_str()) && !length_syms.contains(name.as_str()));
    let source = unresolved.next()?;
    if unresolved.next().is_some() {
        return None;
    }
    // A model term or a projection (`a*`, `self.0`, `a[_i]`, `x#3`) is not a
    // parameter's own name, and a reserved/synthetic spelling is not a source
    // binding this gate may resolve — `build_debug_name_map` demotes that whole
    // family, so it names nothing in the extracted body either.
    if !plain_source_binding(source)
        || trust_types::source_contract_synthetic_name_collision(source).is_some()
    {
        return None;
    }

    // (4) EXACTLY ONE parameter position the clause does not already name in the
    // body's own spelling. Choosing the target from the UNMENTIONED positions is
    // also what makes the rename collision-free: `body_spelling` cannot already
    // occur in the clause, so two distinct clause variables can never merge.
    let mut unclaimed =
        parameters.iter().copied().filter(|(name, _, _)| !clause_vars.contains(*name));
    let (body_spelling, declared_ty, param_local) = unclaimed.next()?;
    if unclaimed.next().is_some() {
        return None;
    }

    // (4b) THE IDENTIFICATION — module header (IV). HIR must say that MIR argument
    // `_param_local` was declared in source as a plain by-value binding spelled
    // `source`. Everything else in this function establishes that the restatement
    // is unambiguous and lands on a name the VC reads; THIS is what establishes
    // that the clause was talking about that parameter in the first place.
    //
    // `param_local` is a MIR local index (arguments are `1..=arg_count`), so the
    // declaration-ordered HIR vector is indexed at `param_local - 1`. A `None`
    // entry (`ref q`, `_`, `q @ sub`) is a refusal: for those patterns `_p` carries
    // no row of the parameter's own, so any row found there belongs to a body
    // binding and `source` cannot be corroborated from MIR at all.
    if hir_param_source_names.get(param_local - 1)?.as_deref() != Some(source.as_str()) {
        return None;
    }

    // (5) The sort must be unambiguous in the clause AND admitted by the
    // parameter's declared type: a clause reading an `Int` is not a restatement of
    // a `bool`/`f64`/`&[T]` parameter. (`retype_contract_formulas_for_body` runs
    // BEFORE this gate and can only retype a name the body binds, so a Bool
    // parameter whose body spelling diverged keeps the parser's `Int` sentinel
    // here and is declined — fail-closed.) Admitting only `Int`/`Bool` scalars is
    // ALSO what bounds the parameter-pattern case analysis in module header (IV):
    // an integer/boolean parameter's pattern is a binding, `_`, `ref`, or `x @ …`,
    // and nothing else is irrefutable at that type.
    let sort = sole_var_sort(preconditions, source)?;
    if !parameter_ty_admits_sort(declared_ty, &sort) {
        return None;
    }

    // (6) RAW `var_debug_info` corroboration WITH ROW MULTIPLICITY — module
    // header (IV.1–2). MIR's own record must say that the source binding `source`
    // occupies exactly ONE row and that row is on this parameter's local, and the
    // same for the body spelling. Counting distinct locals is NOT enough: for
    // `fn f(x: i32) { let n = x; let x = n; x }` the parameter `x` and the body's
    // second `let x` are TWO rows that both land on `_1`, the collapse still names
    // it `x`, and a distinct-locals test would see `x -> [1]` and wrongly conclude
    // that the FIRST non-demoted row is `n`'s. It is not — it is the parameter's —
    // and restating a clause about a same-named module `const` onto that parameter
    // would be a false PROVE.
    //
    // The `body_spelling` bound is the one the proof NEEDS (its single row must be
    // the LAST non-demoted row on `_p`). The `source` bound is deliberately
    // STRICTER than the proof needs — once `body_spelling` is pinned to one row,
    // the first non-demoted row on `_p` is a `source` row whatever `source`'s
    // multiplicity — because a spelling that names two MIR bindings is exactly the
    // ambiguity this gate exists to refuse, and declining costs only reach.
    let source_rows = debug_name_locals.get(source.as_str())?;
    if source_rows.len() != 1 || source_rows[0] != param_local {
        return None;
    }
    let body_rows = debug_name_locals.get(body_spelling)?;
    if body_rows.len() != 1 || body_rows[0] != param_local {
        return None;
    }
    // ... and the body spelling must name exactly one EXTRACTED local, or
    // `place_to_var_name` demotes it to the `_<local>` fallback and the assumed
    // fact would bind nothing the VC reads.
    if body.locals.iter().filter(|local| local.name.as_deref() == Some(body_spelling)).count() != 1
    {
        return None;
    }

    // (7) The row census on the parameter local — module header (IV.3). Every row
    // there that is neither `source`'s nor `body_spelling`'s must carry a name
    // that TRUST'S OWN contract lowering mints, and must be the only row of that
    // name on this local. Two distinct failures are being excluded:
    //   * an ordinary user binding parked on `_p` (a second `let` in a copy chain,
    //     a genuine shadow) would be a third non-demoted row, so `source` need not
    //     be the earliest one — which is exactly the step that identifies it as
    //     the parameter's own name;
    //   * a reserved-SPELLED user binding (`let __tmp = n;`) is invisible to the
    //     collapse, so it cannot be read off `body.locals` at all. It cannot be
    //     the parameter's own name (module header (III) — the compiler refuses
    //     contracts for such a parameter), but declining is still the honest
    //     answer: this gate does not get to assume a fact whose provenance it
    //     cannot name, and the allowlist keeps the restatement standing on
    //     spellings Trust itself produced rather than on a name-shape family a
    //     user may occupy.
    for (name, locals) in debug_name_locals {
        if name == source || name == body_spelling {
            continue;
        }
        let rows_here = locals.iter().filter(|local| **local == param_local).count();
        if rows_here == 0 {
            continue;
        }
        if rows_here != 1 || !trust_lowered_contract_debug_name(name) {
            return None;
        }
    }

    Some(ForcedParameterAlias { source: source.clone(), body_spelling: body_spelling.to_string() })
}

/// A spelling that TRUST'S OWN CONTRACT LOWERING mints and that copy-propagation
/// can park on a parameter local. The list is CLOSED and enumerated from the
/// lowering itself (`compiler/rustc_ast_lowering/src/contract.rs`), which mints
/// exactly three binder spellings:
///   * `__ret` — `inject_ensures_check`'s `let __ret = { body };`, one per
///     `#[ensures]` clause at each return point; this is the one observed on a
///     parameter local, via copy-propagation of the returned value;
///   * `__requires_checker` — `lower_precond`'s per-`requires` checker binding;
///   * `__ensures_checker`, `__ensures_checker1`, … — `wrap_body_with_contract_checks`'
///     per-`ensures` checker bindings.
///
/// DELIBERATELY A CLOSED LIST, not a prefix family, and deliberately NARROWER
/// than [`reserved_synthetic_debug_name`] (the whole `__` namespace). The census
/// in `forced_parameter_alias` uses it to answer "is this row an artifact of OUR
/// lowering?", and a user CAN legally write `let __tmp = n;` or (outside a
/// contract-bearing function) `fn f(__x: i32)`. A prefix family such as
/// `__trust_*` would read an arbitrary user spelling as an artifact — the exact
/// hole a review found in the first version of this restatement, where a
/// parameter spelled `__trust_v` was demoted out of `body.locals`, skipped by the
/// census as "ours", and let a module `const`'s FALSE clause be restated onto the
/// parameter.
///
/// `__awaitee` (async lowering) and the post-extraction `cell_threading` spellings
/// (`__thread_payload`, `__thread_rem`) are NOT contract lowering and are NOT
/// listed: a row carrying one of them on a parameter local makes this restatement
/// decline, which is the fail-closed direction. If Trust starts minting a new
/// CONTRACT spelling that lands on a parameter local, adding it here restores the
/// restatement; omitting it only costs reach.
fn trust_lowered_contract_debug_name(name: &str) -> bool {
    match name {
        "__ret" | "__requires_checker" | "__ensures_checker" => true,
        _ => name
            .strip_prefix("__ensures_checker")
            .is_some_and(|index| !index.is_empty() && index.bytes().all(|b| b.is_ascii_digit())),
    }
}

/// A plain source-binding spelling: identifier characters only. Rejects every
/// place-rendering shape `place_to_var_name` can produce — the deref suffix `a*`,
/// field/index projections `self.0` / `a[_i]`, and the `x#3` statement-version
/// token — none of which is a parameter's own name. (Twin of
/// `trust_vcgen::generate::entry_hypothesis::plain_source_binding`.)
fn plain_source_binding(name: &str) -> bool {
    let mut chars = name.chars();
    chars.next().is_some_and(|first| first.is_ascii_alphabetic() || first == '_')
        && chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
}

/// Whether any node of `formula` binds a variable. `Formula::rename_var` is a
/// syntactic rename with no binder awareness, so a quantified clause is refused
/// outright rather than risking capture.
fn formula_binds_a_variable(formula: &Formula) -> bool {
    let mut found = false;
    formula.visit(&mut |node| {
        if matches!(node, Formula::Forall(..) | Formula::Exists(..)) {
            found = true;
        }
    });
    found
}

/// The single sort `name` carries across `formulas`, or `None` when it carries
/// none or more than one — an ambiguity this gate refuses to resolve.
fn sole_var_sort(formulas: &[Formula], name: &str) -> Option<trust_types::Sort> {
    let mut sort: Option<trust_types::Sort> = None;
    let mut ambiguous = false;
    for formula in formulas {
        formula.visit(&mut |node| {
            let found = match node {
                Formula::Var(var, var_sort) if var == name => var_sort,
                Formula::SymVar(symbol, var_sort) if symbol.as_str() == name => var_sort,
                _ => return,
            };
            match &sort {
                Some(existing) if existing != found => ambiguous = true,
                Some(_) => {}
                None => sort = Some(found.clone()),
            }
        });
    }
    if ambiguous { None } else { sort }
}

/// Whether a parameter of type `ty` can be what a clause variable of sort `sort`
/// denotes. Deliberately narrow — only the sorts a scalar entry fact can carry,
/// against the types that actually carry them. `Ty::Char` is NOT an integer
/// parameter for this purpose, and every aggregate/reference/float type declines,
/// so a restatement is never proposed across a type boundary.
fn parameter_ty_admits_sort(ty: &Ty, sort: &trust_types::Sort) -> bool {
    match (ty, sort) {
        (Ty::Int { .. } | Ty::PtrSizedInt { .. }, trust_types::Sort::Int) => true,
        (Ty::Bool, trust_types::Sort::Bool) => true,
        _ => false,
    }
}

/// The parameter a precondition free variable is caller-bound to, if any:
///   * a bare parameter name `a` → `a` (the parameter itself);
///   * a shared-reference-parameter deref `a*` → `a` (the `&T` pointee, which
///     `place_to_var_name` renders as the suffix `*`). The pointee of a `&T` is
///     immutable for the parameter's lifetime, so a caller-proved entry fact
///     over it holds at every body read — assume-guarantee sound;
///   * a LITERAL projection chain off a parameter head (see below).
///
/// A `&mut T` deref, a runtime index (`a[_i]`), a `*` anywhere but immediately
/// after the head, or a non-parameter name returns `None`, which drops the
/// whole assumption set (fail-closed — can only weaken PROVE toward
/// FAIL/UNKNOWN, never a false PROVE).
fn assumable_param_base<'a>(
    var: &'a str,
    param_names: &FxHashSet<&str>,
    shared_ref_params: &FxHashSet<&str>,
) -> Option<&'a str> {
    if let Some(base) = var.strip_suffix('*') {
        // A `<base>*` deref is assumable ONLY when `<base>` is a shared-ref param.
        return shared_ref_params.contains(base).then_some(base);
    }
    if param_names.contains(var) {
        return Some(var);
    }
    // Trust (float field-magnitude preconditions): a LITERAL projection chain off
    // a parameter is caller-bound and assumable when the projected value is stable
    // for the parameter's lifetime. The base parameter name is returned so the
    // shadow/witness discipline below runs on that parameter exactly as for a
    // bare scalar param (the full chained name never enters the referenced set).
    // Accepted shape — a small grammar, parsed segment by segment:
    //   <head> ['*'] ( '.' <digits> | '[' <digits> ']' )+
    //   * `<head>` is a plain identifier (no projection token). With the optional
    //     `'*'` it must be a SHARED-ref param: the `&T` pointee is immutable, so a
    //     caller-proved entry fact over any part of it holds at every body read —
    //     the same rationale (and soundness) as the `<p>*` whole-pointee case
    //     above; a `&mut` pointee is NOT admitted, matching the `<p>*` &mut
    //     rejection. Without the `'*'` it must be a BY-VALUE param: a body
    //     reassignment anywhere under the param is handled EXACTLY as for a bare
    //     scalar param — the versioned conjoin renames the written place, leaving
    //     the bare entry fact name-disjoint and inert (the S2c entry-read
    //     exemption), so an assumed chain fact can only ever bind the entry value.
    //   * `.<digits>` — a numeric tuple/struct field (`self.0.2`); `[<digits>]` —
    //     a LITERAL array index (`self.0[3]`). Any depth, in any order. A literal
    //     index selects one fixed element of the entry value, so the field
    //     rationale carries over unchanged; a RUNTIME index (`[_i]`, `[x]`) is
    //     not entry-determined and is rejected.
    // Anything else — a `*` not immediately after the head, empty/non-numeric
    // segments, unclosed brackets — falls through to `None` (fail-closed). The
    // `place_to_var_name` twin renders fields as `.i` and a leading deref as `*`;
    // literal-index body renders are canonicalized to `[k]` by the float-contract
    // matcher before lookup, so an admitted var binds its body place byte-for-byte.
    let head_end = var.find(['.', '*', '['])?;
    let (head, mut rest) = var.split_at(head_end);
    if !is_plain_base_ident(head) {
        return None;
    }
    // Optional deref marker, ONLY directly after the head. (`rest` cannot be empty
    // afterwards: a trailing-`*` var was consumed by the strip_suffix arm above.)
    let starred = match rest.strip_prefix('*') {
        Some(stripped) => {
            rest = stripped;
            true
        }
        None => false,
    };
    if rest.is_empty() {
        return None;
    }
    while !rest.is_empty() {
        if let Some(after_dot) = rest.strip_prefix('.') {
            let digits = leading_ascii_digits_len(after_dot);
            if digits == 0 {
                return None;
            }
            rest = &after_dot[digits..];
        } else if let Some(after_bracket) = rest.strip_prefix('[') {
            let digits = leading_ascii_digits_len(after_bracket);
            if digits == 0 {
                return None;
            }
            match after_bracket[digits..].strip_prefix(']') {
                Some(tail) => rest = tail,
                None => return None,
            }
        } else {
            return None;
        }
    }
    if starred {
        shared_ref_params.contains(head).then_some(head)
    } else {
        param_names.contains(head).then_some(head)
    }
}

/// A bare base identifier carrying no projection token (`.`, `*`, `[`) — the head
/// of a field-projection var name (`self` in `self.0` / `self*.2`).
fn is_plain_base_ident(s: &str) -> bool {
    !s.is_empty() && !s.contains(['.', '*', '['])
}

/// Length of the leading run of ASCII digits — the numeric tuple/struct field
/// index or literal array index that opens a projection segment (0 = malformed).
fn leading_ascii_digits_len(s: &str) -> usize {
    s.bytes().take_while(|b| b.is_ascii_digit()).count()
}

struct AdmissibleLengths {
    /// Canonical solver leaves that may occur in an assumed precondition.
    canonical: FxHashSet<String>,
    /// Exact source projection leaf -> canonical solver leaf. The source leaf
    /// is rewritten and is never admitted as an independent Formula variable.
    source_rebindings: Vec<(String, String)>,
}

/// Trust (piece #8 — length-relationship preconditions): canonical length
/// symbols that a precondition may reference, drawn from THIS body's slice/array
/// PARAMETERS, plus exact source-to-canonical rebindings:
///   * `<param_debug_name>__slice_len` — a runtime slice parameter's canonical
///     length var for `&[T]` / `&mut [T]` / `*mut [T]` / bare `[T]` params.
///     Exact source `<param>.len()` first lowers to `<param>_len`; this function
///     authorizes rewriting that leaf to the canonical spelling. Both operations
///     are allowed ONLY when the parameter is LENGTH-STABLE for the whole body
///     (INV-1): the param must not be resliced/reassigned/`&mut`-reborrowed/
///     projected-stored, because such a reslice would make `<p>__slice_len`
///     denote the ORIGINAL length while the indexed view is shorter (a false
///     PROVE).
///   * `__trust_constparam_{index}_{name}` — a const-generic array parameter's
///     length (`&[T; N]` / `[T; N]` with N a const param). The length is the
///     immutable TYPE parameter — no mutation channel changes it (INV-3) — so it
///     is admitted unconditionally for any array/SymArray param.
///
/// A `<name>_len`/`<name>__slice_len` whose base is not a unique, stable slice
/// parameter is neither rebound nor admitted. A `__trust_constparam_*` symbol is
/// admitted only when some array/SymArray parameter actually produces it. The
/// whitelist is derived from the extracted body plus the raw debug-name
/// multimap, so optimized-MIR aliases cannot bypass the same shadow discipline
/// applied to scalar parameters.
fn admissible_lengths(
    body: &VerifiableBody,
    debug_name_locals: &FxHashMap<String, Vec<usize>>,
) -> AdmissibleLengths {
    // Count collapsed debug-name multiplicity across ALL extracted locals. A
    // runtime length symbol is admissible ONLY when `name` denotes exactly one
    // local — the parameter. If a body local shadows the param name (e.g. INV-1's
    // reslice binds a new `arr`), the failed VC could key on the shorter shadow
    // while σ renders the caller's original length — a false PROVE.
    let mut name_count: FxHashMap<&str, usize> = FxHashMap::default();
    for local in &body.locals {
        if let Some(name) = local.name.as_deref() {
            *name_count.entry(name).or_default() += 1;
        }
    }

    let mut canonical = FxHashSet::default();
    let mut source_rebindings = Vec::new();
    for local in &body.locals {
        if local.index < 1 || local.index > body.arg_count {
            continue;
        }
        // `__trust_constparam_{index}_{name}` is derived from the immutable
        // parameter type, not its debug name, so shadowing cannot change which
        // length it denotes (INV-3).
        if let Some(len_sym) = symarray_len_sym_of(&local.ty) {
            canonical.insert(trust_types::const_param_symbol(len_sym.index, &len_sym.name));
        }
        let Some(name) = local.name.as_deref() else { continue };
        // Require both the collapsed extracted model and the raw MIR debug map
        // to identify exactly this parameter. The raw map catches copy-prop
        // aliases that one last-write-wins local name cannot represent.
        let raw_is_unique_parameter = debug_name_locals.get(name).is_some_and(|locals| {
            let mut distinct = locals.clone();
            distinct.sort_unstable();
            distinct.dedup();
            distinct == [local.index]
        });
        if name_count.get(name).copied().unwrap_or(0) != 1 || !raw_is_unique_parameter {
            continue;
        }
        // Runtime source `<p>.len()` becomes `<p>__len`, then is rebound to the
        // one canonical `<p>__slice_len` term (INV-1: length-stable).
        if ty_is_runtime_slice_param(&local.ty) && slice_param_length_is_stable(body, local.index) {
            let canonical_name = format!("{name}__slice_len");
            canonical.insert(canonical_name.clone());
            source_rebindings.push((format!("{name}__len"), canonical_name));
        }
    }
    AdmissibleLengths { canonical, source_rebindings }
}

/// True for a parameter type whose length is a RUNTIME fat-pointer/slice length,
/// producing a `<name>__slice_len` var: `&[T]`, `&mut [T]`, `*const [T]`,
/// `*mut [T]`, or a bare `[T]` (unsized-place) parameter. Concrete `[T; N]` /
/// `&[T; N]` arrays are NOT here — their length is a compile-time constant, not
/// a `__slice_len` var — so they never contribute a runtime length symbol.
fn ty_is_runtime_slice_param(ty: &Ty) -> bool {
    match ty {
        Ty::Slice { .. } => true,
        Ty::Ref { inner, .. } => matches!(inner.as_ref(), Ty::Slice { .. }),
        Ty::RawPtr { pointee, .. } => matches!(pointee.as_ref(), Ty::Slice { .. }),
        _ => false,
    }
}

/// The const-generic array LENGTH symbol of a parameter type, if it is a
/// `SymArray` (`[T; N]`) or a reference/raw-pointer to one (`&[T; N]`). Mirrors
/// `slice_len_formula`'s SymArray arms. Concrete `Ty::Array` (statically-known
/// `u64` length) has no const-param symbol and returns None.
fn symarray_len_sym_of(ty: &Ty) -> Option<&trust_types::ConstLen> {
    match ty {
        Ty::SymArray { len_sym, .. } => Some(len_sym),
        Ty::Ref { inner, .. } => match inner.as_ref() {
            Ty::SymArray { len_sym, .. } => Some(len_sym),
            _ => None,
        },
        Ty::RawPtr { pointee, .. } => match pointee.as_ref() {
            Ty::SymArray { len_sym, .. } => Some(len_sym),
            _ => None,
        },
        _ => None,
    }
}

/// Trust (piece #8, INV-1): whether the slice PARAMETER `p` (local index) keeps
/// the SAME fat-pointer LENGTH view for the whole body, so `<p>__slice_len`
/// denotes the caller-supplied length at every read. This is the crate-local twin
/// of `trust_vcgen::place_source_is_stable` (the two crates share no dependency),
/// specialized to LENGTH stability — which is about the fat-pointer VALUE, not the
/// pointee ELEMENTS:
///   * NO whole-local reassign of the parameter (`arr = &arr[..k];`) — that
///     installs a shorter/different fat pointer, changing the length view.
///   * NO `&mut`/`&raw mut` reborrow of the WHOLE parameter fat pointer (the
///     channel a reslice-of-arr flows through: `let s = &mut arr; *s = &mut …`).
///   * NO projected store / borrow that overwrites the fat pointer VALUE itself
///     (a projection that does NOT go through `Deref` — e.g. a hypothetical
///     fat-pointer field write; exotic, rejected conservatively), and no
///     SetDiscriminant / Deinit / call-destination store of the whole local.
///
/// An ELEMENT write `arr[i] = v` (which lowers to a store through a DEREF-leading
/// projection `(*arr)[i]`) writes the POINTEE and leaves the fat pointer — and
/// thus the length — unchanged, so it is ALLOWED. Likewise a shared reborrow
/// `&arr[..]` cannot reslice-through-a-shared-ref-to-shorten the caller's view
/// (it borrows immutably), so it is allowed. Any length-changing channel returns
/// false → the length symbol is dropped from the whitelist → the precondition is
/// dropped (fail-closed). INTENTIONALLY conservative: it can only cost
/// completeness, never soundness.
fn slice_param_length_is_stable(body: &VerifiableBody, param_local: usize) -> bool {
    // A projection whose FIRST element is `Deref` addresses THROUGH the parameter's
    // fat pointer into the pointee — it can never overwrite the fat pointer value
    // itself (hence never change the length). Any other projected/whole store to
    // the parameter local writes the fat pointer.
    let writes_fat_pointer = |place: &trust_types::Place| -> bool {
        place.local == param_local
            && !matches!(place.projections.first(), Some(trust_types::Projection::Deref))
    };
    for block in &body.blocks {
        // A call-dest store to the parameter's fat pointer reseats it. A store
        // THROUGH a deref (`f(&mut (*arr)[i])`-style dest) writes the pointee and is
        // fine; a whole/non-deref dest overwrites the fat pointer.
        // (edition 2021 — no let-chains; nest the borrow check.)
        if let Terminator::Call { dest, .. } = &block.terminator {
            if writes_fat_pointer(dest) {
                return false;
            }
        }
        for stmt in &block.stmts {
            match stmt {
                Statement::Assign { place, rvalue, .. } => {
                    if writes_fat_pointer(place) {
                        return false;
                    }
                    // A mutable (re)borrow of the WHOLE parameter fat pointer
                    // (`&mut arr` / `&raw mut arr`, no leading deref) is the channel a
                    // reslice-of-arr flows through. A mutable borrow of the POINTEE or
                    // an ELEMENT (`&mut (*arr)[i]`, deref-leading) cannot change the
                    // fat pointer's length, so it is allowed.
                    if let Rvalue::Ref { mutable: true, place: borrowed }
                    | Rvalue::AddressOf(true, borrowed) = rvalue
                    {
                        if writes_fat_pointer(borrowed) {
                            return false;
                        }
                    }
                }
                Statement::SetDiscriminant { place, .. } | Statement::Deinit { place } => {
                    if place.local == param_local {
                        return false;
                    }
                }
                _ => {}
            }
        }
    }
    true
}

/// The v1 assumable fragment: boolean structure + integer/float comparisons and
/// linear-ish arithmetic over parameters and literals. Everything else —
/// division, bitvectors, quantifiers, function applications — is rejected
/// (the assumption is skipped, never the function).
///
/// A binary64 float literal (`FpConst`) is an admissible LEAF: it is a constant
/// operand of a magnitude-bound comparison (`self.0 <= 1.0e30`), exactly the
/// integer-literal case one sort over. Admitting it does not widen the soundness
/// surface — the assume-guarantee discipline (the referenced var must be an entry
/// parameter, the predicate must have a ground witness, no shadow) runs unchanged;
/// a float constant introduces no variable, no aliasing, no unsat channel. Without
/// this arm every float-magnitude precondition falls to `_ => false`
/// (UnsupportedSyntax) and is dropped, leaving the body's overflow VCs with no
/// input bound to discharge against.
fn in_assumable_fragment(formula: &Formula) -> bool {
    match formula {
        Formula::Bool(_) | Formula::Int(_) | Formula::UInt(_) => true,
        Formula::FpConst { .. } => true,
        Formula::Var(..) | Formula::SymVar(..) => true,
        Formula::Not(inner) | Formula::Neg(inner) => in_assumable_fragment(inner),
        Formula::And(items) | Formula::Or(items) => items.iter().all(in_assumable_fragment),
        Formula::Implies(a, b)
        | Formula::Eq(a, b)
        | Formula::Lt(a, b)
        | Formula::Le(a, b)
        | Formula::Gt(a, b)
        | Formula::Ge(a, b)
        | Formula::Add(a, b)
        | Formula::Sub(a, b)
        | Formula::Mul(a, b) => in_assumable_fragment(a) && in_assumable_fragment(b),
        _ => false,
    }
}

/// Search for a concrete ground model of `AND(preconditions)` by exact i128
/// evaluation over a small candidate set per variable: 0, ±1, every literal
/// occurring in the predicates, and each literal ±1. The cross-product is
/// capped; over cap (or no witness) we refuse the assumption. A returned
/// witness is a genuine model, so this check cannot admit an unsatisfiable
/// predicate.
fn has_ground_witness(
    preconditions: &[Formula],
    body: &VerifiableBody,
    length_symbols: &FxHashSet<String>,
) -> bool {
    const MAX_ASSIGNMENTS: usize = 4096;

    let mut var_set: FxHashSet<String> = FxHashSet::default();
    for f in preconditions {
        var_set.extend(f.free_variables());
    }
    let mut vars: Vec<String> = var_set.into_iter().collect();
    vars.sort();
    if vars.is_empty() {
        // Ground predicate: just evaluate it.
        let env = FxHashMap::default();
        return preconditions.iter().all(|f| eval_bool(f, &env) == Some(true));
    }

    let mut candidates: Vec<i128> = vec![0, 1, -1];
    for f in preconditions {
        collect_literals(f, &mut candidates);
    }
    let mut expanded = Vec::with_capacity(candidates.len() * 3);
    for &c in &candidates {
        expanded.push(c);
        if let Some(v) = c.checked_add(1) {
            expanded.push(v);
        }
        if let Some(v) = c.checked_sub(1) {
            expanded.push(v);
        }
    }
    expanded.sort_unstable();
    expanded.dedup();

    let domains = witness_domains(body, length_symbols, preconditions);

    // Fast accept: the all-zeros / all-false assignment. Per-field magnitude
    // preconditions (`|self.0| <= C && |self.1| <= C && …`, centered at 0) are
    // satisfied by it, and 0 is a representable value of every integer/float
    // type — so this IS a genuine ground model. It admits such conjunctions
    // WITHOUT the cross-product enumeration below, whose `MAX_ASSIGNMENTS` cap
    // would otherwise bail to a spurious "no witness" for 4+ independent field
    // variables (8^4 = 4096). SOUNDNESS: it accepts only on a concrete satisfying
    // assignment, so it can never admit an unsatisfiable predicate; and it only
    // ADDS accepts — a predicate the enumeration would reject at zero simply
    // evaluates to false here and falls through to the unchanged search.
    let zero_env: FxHashMap<&str, WitnessValue> = vars
        .iter()
        .map(|name| {
            let value = match domains.get(name) {
                Some(WitnessDomain::Bool) => WitnessValue::Bool(false),
                _ => WitnessValue::Int(0),
            };
            (name.as_str(), value)
        })
        .collect();
    if preconditions.iter().all(|f| eval_bool(f, &zero_env) == Some(true)) {
        return true;
    }

    let candidates_by_var: Vec<Vec<WitnessValue>> = vars
        .iter()
        .map(|name| match domains.get(name) {
            Some(WitnessDomain::Bool) => vec![WitnessValue::Bool(false), WitnessValue::Bool(true)],
            Some(WitnessDomain::Int { min, max }) => {
                let mut values = expanded
                    .iter()
                    .copied()
                    .filter(|value| value >= min && value <= max)
                    .collect::<Vec<_>>();
                values.extend([*min, *max]);
                values.sort_unstable();
                values.dedup();
                values.into_iter().map(WitnessValue::Int).collect()
            }
            None => expanded.iter().copied().map(WitnessValue::Int).collect(),
        })
        .collect();
    if candidates_by_var.iter().any(Vec::is_empty) {
        return false;
    }
    let total = candidates_by_var
        .iter()
        .try_fold(1usize, |product, candidates| product.checked_mul(candidates.len()))
        .unwrap_or(usize::MAX);
    if total > MAX_ASSIGNMENTS {
        return false;
    }

    let mut indices = vec![0usize; vars.len()];
    loop {
        let env: FxHashMap<&str, WitnessValue> = vars
            .iter()
            .zip(indices.iter())
            .enumerate()
            .map(|(position, (variable, &index))| {
                (variable.as_str(), candidates_by_var[position][index])
            })
            .collect();
        if preconditions.iter().all(|f| eval_bool(f, &env) == Some(true)) {
            return true;
        }
        // Odometer increment.
        let mut pos = 0;
        loop {
            if pos == indices.len() {
                return false;
            }
            indices[pos] += 1;
            if indices[pos] < candidates_by_var[pos].len() {
                break;
            }
            indices[pos] = 0;
            pos += 1;
        }
    }
}

#[derive(Debug, Clone, Copy)]
enum WitnessValue {
    Bool(bool),
    Int(i128),
}

#[derive(Debug, Clone, Copy)]
enum WitnessDomain {
    Bool,
    Int { min: i128, max: i128 },
}

fn witness_domains(
    body: &VerifiableBody,
    length_symbols: &FxHashSet<String>,
    preconditions: &[Formula],
) -> FxHashMap<String, WitnessDomain> {
    let mut domains = FxHashMap::default();
    for local in &body.locals {
        if local.index < 1 || local.index > body.arg_count {
            continue;
        }
        let Some(name) = local.name.as_ref() else { continue };
        if let Some(domain) = witness_domain_for_ty(&local.ty) {
            domains.insert(name.clone(), domain);
        }
        if let Ty::Ref { inner, .. } = &local.ty {
            if let Some(domain) = witness_domain_for_ty(inner) {
                domains.insert(format!("{name}*"), domain);
            }
        }
    }
    // Runtime slice lengths and const-generic array lengths are usize values.
    // Restricting to the current compiler target's representable usize subset
    // makes every found witness a real Rust value; an architecture mismatch can
    // only drop a satisfiable assumption (fail closed).
    let usize_max = usize::MAX as i128;
    for symbol in length_symbols {
        domains.insert(symbol.clone(), WitnessDomain::Int { min: 0, max: usize_max });
    }
    // Signature typing may have supplied Bool sorts even when a synthetic test
    // body lacks a precise Ty. Formula evidence can refine Int -> Bool, never
    // widen an exact integer range.
    for formula in preconditions {
        formula.visit(&mut |node| match node {
            Formula::Var(name, trust_types::Sort::Bool) => {
                domains.insert(name.clone(), WitnessDomain::Bool);
            }
            Formula::SymVar(symbol, trust_types::Sort::Bool) => {
                domains.insert(symbol.as_str().to_string(), WitnessDomain::Bool);
            }
            _ => {}
        });
    }
    domains
}

fn witness_domain_for_ty(ty: &Ty) -> Option<WitnessDomain> {
    match ty {
        Ty::Bool => Some(WitnessDomain::Bool),
        Ty::Int { width, signed } if *width > 0 && *width <= 128 => {
            let (min, max) = if *signed {
                if *width == 128 {
                    (i128::MIN, i128::MAX)
                } else {
                    (-(1i128 << (*width - 1)), (1i128 << (*width - 1)) - 1)
                }
            } else if *width >= 127 {
                // The evaluator is exact i128. Searching this representable
                // subset is safe: every returned witness is still a real value.
                (0, i128::MAX)
            } else {
                (0, (1i128 << *width) - 1)
            };
            Some(WitnessDomain::Int { min, max })
        }
        _ => None,
    }
}

fn collect_literals(formula: &Formula, out: &mut Vec<i128>) {
    match formula {
        Formula::Int(v) => out.push(*v),
        Formula::UInt(v) => {
            if let Ok(v) = i128::try_from(*v) {
                out.push(v);
            }
        }
        Formula::Bool(_) | Formula::Var(..) | Formula::SymVar(..) => {}
        Formula::Not(inner) => collect_literals(inner, out),
        // Trust: a negative literal parses as `Neg(Int(n))`, so recursing alone
        // seeds the MAGNITUDE `n` and never the value `-n` the predicate names.
        // `requires x == -3` therefore searched {0,±1,3} ±1 — which reaches -2
        // but not -3 — and refused a plainly satisfiable precondition as
        // "no satisfiable witness". Measured: `x == -1`/`x == -2` were admitted
        // and everything from `x == -3` down was refused, purely because -1/-2
        // fall inside the ±1 expansion of the {0,1,-1} seeds.
        //
        // Contribute the negation of each literal found under the `Neg`, which
        // is the smallest set that fixes the actual defect: negating every
        // literal unconditionally would roughly double each variable's
        // candidate list, and the per-variable lists feed a cross product
        // capped by `MAX_ASSIGNMENTS`, so it could push wide predicates over
        // the cap and manufacture NEW spurious refusals.
        //
        // SOUNDNESS: this only ADDS candidates. Every accept still comes from
        // evaluating the whole precondition set to `true` under one concrete
        // assignment, so a found witness remains a genuine model and an
        // unsatisfiable predicate can never be admitted.
        Formula::Neg(inner) => {
            let start = out.len();
            collect_literals(inner, out);
            // The range is built from the length BEFORE these pushes, so the
            // negations appended below are not themselves re-negated.
            for index in start..out.len() {
                let value = out[index];
                if let Some(negated) = value.checked_neg() {
                    out.push(negated);
                }
            }
        }
        Formula::And(items) | Formula::Or(items) => {
            for item in items {
                collect_literals(item, out);
            }
        }
        Formula::Implies(a, b)
        | Formula::Eq(a, b)
        | Formula::Lt(a, b)
        | Formula::Le(a, b)
        | Formula::Gt(a, b)
        | Formula::Ge(a, b)
        | Formula::Add(a, b)
        | Formula::Sub(a, b)
        | Formula::Mul(a, b) => {
            collect_literals(a, out);
            collect_literals(b, out);
        }
        _ => {}
    }
}

fn eval_bool(formula: &Formula, env: &FxHashMap<&str, WitnessValue>) -> Option<bool> {
    match formula {
        Formula::Bool(b) => Some(*b),
        Formula::Var(name, trust_types::Sort::Bool) => match env.get(name.as_str()) {
            Some(WitnessValue::Bool(value)) => Some(*value),
            _ => None,
        },
        Formula::SymVar(symbol, trust_types::Sort::Bool) => match env.get(symbol.as_str()) {
            Some(WitnessValue::Bool(value)) => Some(*value),
            _ => None,
        },
        Formula::Not(inner) => eval_bool(inner, env).map(|b| !b),
        Formula::And(items) => {
            let mut all = true;
            for item in items {
                all &= eval_bool(item, env)?;
            }
            Some(all)
        }
        Formula::Or(items) => {
            let mut any = false;
            for item in items {
                any |= eval_bool(item, env)?;
            }
            Some(any)
        }
        Formula::Implies(a, b) => Some(!eval_bool(a, env)? || eval_bool(b, env)?),
        Formula::Eq(a, b) => {
            // Boolean equality first, then integer.
            if let (Some(x), Some(y)) = (eval_bool_opt(a, env), eval_bool_opt(b, env)) {
                return Some(x == y);
            }
            Some(eval_int(a, env)? == eval_int(b, env)?)
        }
        // Float-sorted magnitude bounds (`self.0 <= 1.0e30`) evaluate with IEEE f64
        // semantics; a non-float comparison falls through to the exact-i128 path.
        Formula::Lt(a, b) => match (eval_float(a, env), eval_float(b, env)) {
            (Some(x), Some(y)) => Some(x < y),
            _ => Some(eval_int(a, env)? < eval_int(b, env)?),
        },
        Formula::Le(a, b) => match (eval_float(a, env), eval_float(b, env)) {
            (Some(x), Some(y)) => Some(x <= y),
            _ => Some(eval_int(a, env)? <= eval_int(b, env)?),
        },
        Formula::Gt(a, b) => match (eval_float(a, env), eval_float(b, env)) {
            (Some(x), Some(y)) => Some(x > y),
            _ => Some(eval_int(a, env)? > eval_int(b, env)?),
        },
        Formula::Ge(a, b) => match (eval_float(a, env), eval_float(b, env)) {
            (Some(x), Some(y)) => Some(x >= y),
            _ => Some(eval_int(a, env)? >= eval_int(b, env)?),
        },
        _ => None,
    }
}

/// Evaluate a float-sorted term to an f64 under a witness assignment, for the
/// magnitude-bound witness search. A witness value (an integer, e.g. the
/// all-zeros probe's `0`) stands in for the field's f64 value (`v as f64`); a
/// binary64 float literal contributes its exact value. `None` for any non-float
/// term, so a comparison with a non-float operand falls back to the exact-i128
/// evaluator. SOUND for the gate: it only ever CONFIRMS that a concrete
/// assignment satisfies a predicate (IEEE semantics), so it cannot admit an
/// unsatisfiable predicate; a satisfiable-only-off-the-integer-grid predicate is
/// simply not found by this search and is dropped (fail-closed).
///
/// Compound arms (Add/Sub/Mul/Neg) evaluate with plain IEEE f64 arithmetic over
/// recursively float-evaluated operands. That IS the check's semantics — the
/// predicate is an FP-sorted formula, so a concrete assignment satisfies it
/// exactly when the IEEE evaluation of the comparison holds. A NaN/±inf result
/// simply fails the comparison honestly (NaN compares false; an infinite
/// magnitude fails a finite bound), which can only miss a witness, never
/// fabricate one. Difference bounds (`(near) - (far) <= -1.0e-6`) reach the
/// gate Float-sorted at any depth (the retype map is recursive), so without
/// the Sub arm the whole precondition set would drop as NoSatisfiableWitness.
fn eval_float(formula: &Formula, env: &FxHashMap<&str, WitnessValue>) -> Option<f64> {
    match formula {
        Formula::FpConst { bits, eb: 11, sb: 53 } => {
            let v = f64::from_bits(*bits as u64);
            if v.is_finite() { Some(v) } else { None }
        }
        Formula::Var(name, trust_types::Sort::Float { .. }) => match env.get(name.as_str()) {
            Some(WitnessValue::Int(value)) => Some(*value as f64),
            _ => None,
        },
        Formula::SymVar(symbol, trust_types::Sort::Float { .. }) => {
            match env.get(symbol.as_str()) {
                Some(WitnessValue::Int(value)) => Some(*value as f64),
                _ => None,
            }
        }
        Formula::Add(a, b) => Some(eval_float(a, env)? + eval_float(b, env)?),
        Formula::Sub(a, b) => Some(eval_float(a, env)? - eval_float(b, env)?),
        Formula::Mul(a, b) => Some(eval_float(a, env)? * eval_float(b, env)?),
        // Negation over ANY float-evaluable operand (literal, var, or compound).
        Formula::Neg(inner) => Some(-eval_float(inner, env)?),
        _ => None,
    }
}

/// Like `eval_bool` but used only for the Eq disambiguation: returns None when
/// the node is not obviously boolean, without treating that as failure.
fn eval_bool_opt(formula: &Formula, env: &FxHashMap<&str, WitnessValue>) -> Option<bool> {
    match formula {
        Formula::Bool(_)
        | Formula::Not(_)
        | Formula::And(_)
        | Formula::Or(_)
        | Formula::Implies(..)
        | Formula::Lt(..)
        | Formula::Le(..)
        | Formula::Gt(..)
        | Formula::Ge(..)
        | Formula::Var(_, trust_types::Sort::Bool)
        | Formula::SymVar(_, trust_types::Sort::Bool) => eval_bool(formula, env),
        _ => None,
    }
}

fn eval_int(formula: &Formula, env: &FxHashMap<&str, WitnessValue>) -> Option<i128> {
    match formula {
        Formula::Int(v) => Some(*v),
        Formula::UInt(v) => i128::try_from(*v).ok(),
        Formula::Var(name, sort) if *sort != trust_types::Sort::Bool => {
            match env.get(name.as_str()) {
                Some(WitnessValue::Int(value)) => Some(*value),
                _ => None,
            }
        }
        Formula::SymVar(symbol, sort) if *sort != trust_types::Sort::Bool => {
            match env.get(symbol.as_str()) {
                Some(WitnessValue::Int(value)) => Some(*value),
                _ => None,
            }
        }
        Formula::Add(a, b) => eval_int(a, env)?.checked_add(eval_int(b, env)?),
        Formula::Sub(a, b) => eval_int(a, env)?.checked_sub(eval_int(b, env)?),
        Formula::Mul(a, b) => eval_int(a, env)?.checked_mul(eval_int(b, env)?),
        Formula::Neg(inner) => eval_int(inner, env)?.checked_neg(),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use trust_types::Sort;

    use super::*;

    fn var(name: &str) -> Formula {
        Formula::Var(name.to_string(), Sort::Int)
    }

    fn int(v: i128) -> Formula {
        Formula::Int(v)
    }

    fn body_with(locals: Vec<(usize, Option<&str>)>, arg_count: usize) -> VerifiableBody {
        VerifiableBody {
            locals: locals
                .into_iter()
                .map(|(index, name)| trust_types::LocalDecl {
                    index,
                    ty: trust_types::Ty::Int { width: 64, signed: true },
                    name: name.map(str::to_string),
                })
                .collect(),
            blocks: Vec::new(),
            arg_count,
            return_ty: trust_types::Ty::Int { width: 64, signed: true },
            datatype_defs: Default::default(),
        }
    }

    fn body_with_param_ty(name: &str, ty: trust_types::Ty) -> VerifiableBody {
        VerifiableBody {
            locals: vec![
                trust_types::LocalDecl { index: 0, ty: trust_types::Ty::unit_ty(), name: None },
                trust_types::LocalDecl { index: 1, ty, name: Some(name.to_string()) },
            ],
            blocks: Vec::new(),
            arg_count: 1,
            return_ty: trust_types::Ty::unit_ty(),
            datatype_defs: Default::default(),
        }
    }

    fn bounded(name: &str, lo: i128, hi: i128) -> Formula {
        Formula::And(vec![
            Formula::Ge(Box::new(var(name)), Box::new(int(lo))),
            Formula::Le(Box::new(var(name)), Box::new(int(hi))),
        ])
    }

    fn multimap(entries: &[(&str, &[usize])]) -> FxHashMap<String, Vec<usize>> {
        entries.iter().map(|(name, locals)| (name.to_string(), locals.to_vec())).collect()
    }

    /// Test shim for every test that is NOT about the forced restatement: the
    /// ORDINARY case, where optimized MIR still carries each parameter's own
    /// source name, so the HIR parameter vector equals the body spellings.
    ///
    /// This is deliberately not `None`. `None` would make the restatement decline
    /// at condition (0) and every "restatement declines because …" test below
    /// would pass vacuously, testing nothing. With the body spellings, condition
    /// (4b) is genuinely evaluated and simply does not hold — the restatement's
    /// `source` is by construction a name the body does NOT bind, so it can never
    /// equal a body spelling — which is the honest reason these functions see no
    /// restatement.
    fn gate_contract_preconditions(
        preconditions: &mut Vec<Formula>,
        body: &VerifiableBody,
        debug_name_locals: &FxHashMap<String, Vec<usize>>,
    ) -> Vec<AssumeSkipReason> {
        let hir: Vec<Option<String>> = (1..=body.arg_count)
            .map(|index| {
                body.locals.iter().find(|local| local.index == index).and_then(|l| l.name.clone())
            })
            .collect();
        super::gate_contract_preconditions(preconditions, body, debug_name_locals, Some(&hir))
    }

    /// Test shim for the forced restatement: `hir` states the HIR parameter
    /// spellings in DECLARATION ORDER — the positive parameter-hood fact module
    /// header (IV) checks. An EMPTY string means that position has no plain
    /// by-value simple-ident binding, i.e. `ref q`, `_`, or `q @ sub`, which is
    /// exactly the shape that carries no debug row of the parameter's own.
    fn gate_restating(
        preconditions: &mut Vec<Formula>,
        body: &VerifiableBody,
        debug_name_locals: &FxHashMap<String, Vec<usize>>,
        hir: &[&str],
    ) -> Vec<AssumeSkipReason> {
        let hir: Vec<Option<String>> =
            hir.iter().map(|n| if n.is_empty() { None } else { Some((*n).to_string()) }).collect();
        super::gate_contract_preconditions(preconditions, body, debug_name_locals, Some(&hir))
    }

    #[test]
    fn honest_bound_passes() {
        let body = body_with(vec![(0, None), (1, Some("x")), (2, Some("tmp"))], 1);
        let names = multimap(&[("x", &[1]), ("tmp", &[2])]);
        let mut pres = vec![bounded("x", -262143, 262143)];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(reasons.is_empty(), "{reasons:?}");
        assert_eq!(pres.len(), 1);
    }

    #[test]
    fn shadowed_param_drops_assumption() {
        // local 2 (body-introduced) shares the debug name "x" with param 1.
        let body = body_with(vec![(0, None), (1, Some("x")), (2, Some("x"))], 1);
        let names = multimap(&[("x", &[1, 2])]);
        let mut pres = vec![bounded("x", 0, 10)];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(matches!(reasons.as_slice(), [AssumeSkipReason::ShadowedParamName(n)] if n == "x"));
        assert!(pres.is_empty());
    }

    #[test]
    fn copy_propagated_shadow_drops_assumption() {
        // Build #32 regression: optimized MIR copy-propagated `let x = z;` so
        // the shadow's debug entry landed on z's PARAM local (_2). Collapsed
        // per-local names show params (1:"x", 2:"x") — no body-indexed local —
        // but the raw multimap exposes "x" -> [1, 2].
        let body = body_with(vec![(0, None), (1, Some("x")), (2, Some("x"))], 2);
        let names = multimap(&[("x", &[1, 2]), ("z", &[2])]);
        let mut pres = vec![bounded("x", 0, 10)];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(
            reasons.iter().any(|r| matches!(r, AssumeSkipReason::ShadowedParamName(n) if n == "x")),
            "{reasons:?}"
        );
        assert!(pres.is_empty());
    }

    #[test]
    fn alias_on_param_local_is_restated_not_dropped() {
        // EXPECTATION CHANGED (forced parameter restatement). This is the minimal
        // form of the copy-propagated-parameter shape: the clause names `x`, MIR's
        // own `var_debug_info` puts the source binding `x` on the parameter local
        // 1 in exactly one row, and the last-write-wins collapse named that same
        // local `w`. Exactly one clause spelling is unbindable, exactly one
        // parameter position is unclaimed, and `_1` carries no third row — the
        // correspondence is FORCED, so the clause is restated as a fact about `w`
        // and KEPT. It used to drop as an ambiguity; see the module header
        // (I)–(VII) and the `..._still_drops` siblings below, which pin every way
        // it can fail to be forced.
        let body = body_with(vec![(0, None), (1, Some("w"))], 1);
        let names = multimap(&[("x", &[1]), ("w", &[1])]);
        let mut pres = vec![bounded("x", 0, 10)];
        let reasons = gate_restating(&mut pres, &body, &names, &["x"]);
        assert!(reasons.is_empty(), "the forced restatement must be kept: {reasons:?}");
        assert_eq!(pres, vec![bounded("w", 0, 10)], "the clause must be restated in `w`");
    }

    #[test]
    fn extra_user_binding_on_the_param_local_still_drops() {
        // SOUNDNESS TWIN of the test above, and the half of the old expectation
        // that must survive: a THIRD, ordinary user binding parked on the
        // parameter local breaks the row census in condition (7). `source` is then
        // no longer forced to be the earliest row on `_1` — i.e. no longer forced
        // to be the parameter's own source name — so the restatement declines and
        // the whole set drops, exactly as before.
        let body = body_with(vec![(0, None), (1, Some("w"))], 1);
        let names = multimap(&[("x", &[1]), ("w", &[1]), ("t", &[1])]);
        let mut pres = vec![bounded("x", 0, 10)];
        let reasons = gate_restating(&mut pres, &body, &names, &["x"]);
        assert!(
            reasons.iter().any(|r| matches!(r, AssumeSkipReason::ShadowedParamName(_))),
            "an unexplained third binding on the param local must still drop: {reasons:?}"
        );
        assert!(pres.is_empty());
    }

    #[test]
    fn contradictory_predicate_drops_assumption() {
        let body = body_with(vec![(0, None), (1, Some("x"))], 1);
        let names = multimap(&[("x", &[1])]);
        let mut pres = vec![Formula::And(vec![
            Formula::Gt(Box::new(var("x")), Box::new(int(10))),
            Formula::Lt(Box::new(var("x")), Box::new(int(5))),
        ])];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert_eq!(reasons, vec![AssumeSkipReason::NoSatisfiableWitness]);
        assert!(pres.is_empty());
    }

    #[test]
    fn u8_out_of_range_witness_cannot_vacuously_discharge_body() {
        let body = body_with_param_ty("x", trust_types::Ty::Int { width: 8, signed: false });
        let names = multimap(&[("x", &[1])]);
        let mut pres = vec![Formula::Gt(Box::new(var("x")), Box::new(int(300)))];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert_eq!(reasons, vec![AssumeSkipReason::NoSatisfiableWitness]);
        assert!(pres.is_empty(), "the impossible hypothesis must not reach any body VC");
    }

    #[test]
    fn i8_out_of_range_witness_cannot_vacuously_discharge_body() {
        let body = body_with_param_ty("x", trust_types::Ty::Int { width: 8, signed: true });
        let names = multimap(&[("x", &[1])]);
        let mut pres = vec![Formula::Lt(Box::new(var("x")), Box::new(int(-128)))];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert_eq!(reasons, vec![AssumeSkipReason::NoSatisfiableWitness]);
        assert!(pres.is_empty());
    }

    /// A negative literal parses as `Neg(Int(n))`. `collect_literals` used to
    /// recurse through the `Neg` and seed only the MAGNITUDE, so the candidate
    /// set for `x == -3` was {0, ±1, 3} expanded by ±1 — which contains -2 but
    /// not -3 — and the gate refused a plainly satisfiable precondition.
    ///
    /// The boundary was measured end-to-end through `trustc -Ztrust-verify=on`:
    /// `requires x == -1` and `x == -2` were admitted (they fall inside the ±1
    /// expansion of the {0,1,-1} seeds) while everything from `x == -3` down
    /// was refused. This pins several values on BOTH sides of that old cliff so
    /// a regression cannot hide behind the two that always worked.
    #[test]
    fn negative_literal_equality_has_a_ground_witness() {
        for value in [-1i128, -2, -3, -4, -7, -16, -100] {
            let body = body_with_param_ty("x", trust_types::Ty::Int { width: 32, signed: true });
            let names = multimap(&[("x", &[1])]);
            // `x == -value`, spelled the way the contract lowerer builds it.
            let mut pres = vec![Formula::Eq(
                Box::new(var("x")),
                Box::new(Formula::Neg(Box::new(int(-value)))),
            )];
            let reasons = gate_contract_preconditions(&mut pres, &body, &names);
            assert!(
                !reasons.contains(&AssumeSkipReason::NoSatisfiableWitness),
                "`x == {value}` is satisfiable and must not be refused for want of a witness; \
                 got {reasons:?}"
            );
            assert!(
                !pres.is_empty(),
                "`x == {value}` must survive the gate and reach the body VCs"
            );
        }
    }

    /// The companion direction: widening the candidate set must not make the
    /// gate admit something unsatisfiable. `x == -3 && x == -4` has no model,
    /// and both literals are now in the candidate set, so this is exactly the
    /// case where a careless "just add more candidates" fix would still be
    /// caught by evaluation rather than by the search being too narrow.
    #[test]
    fn contradictory_negative_literals_still_have_no_witness() {
        let body = body_with_param_ty("x", trust_types::Ty::Int { width: 32, signed: true });
        let names = multimap(&[("x", &[1])]);
        let mut pres = vec![
            Formula::Eq(Box::new(var("x")), Box::new(Formula::Neg(Box::new(int(3))))),
            Formula::Eq(Box::new(var("x")), Box::new(Formula::Neg(Box::new(int(4))))),
        ];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert_eq!(reasons, vec![AssumeSkipReason::NoSatisfiableWitness]);
        assert!(pres.is_empty(), "the impossible hypothesis must not reach any body VC");
    }

    #[test]
    fn typed_bool_requires_has_real_witness_and_contradiction_does_not() {
        let body = body_with_param_ty("flag", trust_types::Ty::Bool);
        let names = multimap(&[("flag", &[1])]);
        let flag = Formula::Var("flag".into(), trust_types::Sort::Bool);
        let mut honest = vec![Formula::Eq(Box::new(flag.clone()), Box::new(Formula::Bool(true)))];
        assert!(gate_contract_preconditions(&mut honest, &body, &names).is_empty());
        assert_eq!(honest.len(), 1);

        let mut impossible = vec![Formula::And(vec![flag.clone(), Formula::Not(Box::new(flag))])];
        assert_eq!(
            gate_contract_preconditions(&mut impossible, &body, &names),
            vec![AssumeSkipReason::NoSatisfiableWitness]
        );
        assert!(impossible.is_empty());
    }

    #[test]
    fn non_param_variable_drops_assumption() {
        let body = body_with(vec![(0, None), (1, Some("x"))], 1);
        let names = multimap(&[("x", &[1])]);
        let mut pres = vec![bounded("y", 0, 10)];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(
            reasons.iter().any(|r| matches!(r, AssumeSkipReason::NonParamVariable(n) if n == "y"))
        );
        assert!(pres.is_empty());
    }

    #[test]
    fn unsupported_syntax_drops_assumption() {
        let body = body_with(vec![(0, None), (1, Some("x"))], 1);
        let names = multimap(&[("x", &[1])]);
        let mut pres = vec![Formula::Eq(
            Box::new(Formula::Div(Box::new(var("x")), Box::new(int(2)))),
            Box::new(int(1)),
        )];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert_eq!(reasons, vec![AssumeSkipReason::UnsupportedSyntax]);
        assert!(pres.is_empty());
    }

    /// A binary64 float literal `1.0e30`.
    fn fp(v: f64) -> Formula {
        Formula::FpConst { bits: u128::from(v.to_bits()), eb: 11, sb: 53 }
    }

    /// A `Float`-sorted field-projection var (`self.0`), as the spec parser's
    /// `coerce_float_comparison_operands` produces for an f64 field bound.
    fn ffield(name: &str) -> Formula {
        Formula::Var(name.to_string(), Sort::Float { eb: 11, sb: 53 })
    }

    /// `-C <= name <= C` over an f64 field: the two-sided magnitude bound a3d-geom
    /// spells `self.x <= 1.0e30 && self.x >= -1.0e30`, lowered to field-index form.
    fn fbounded(name: &str, c: f64) -> Formula {
        Formula::And(vec![
            Formula::Le(Box::new(ffield(name)), Box::new(fp(c))),
            Formula::Ge(Box::new(ffield(name)), Box::new(fp(-c))),
        ])
    }

    #[test]
    fn float_field_magnitude_precondition_is_assumed() {
        // `dot(self: Vec3, o: Vec3)` with `#[requires(|self.i| <= 1e30 && |o.i| <=
        // 1e30)]`, lowered to field-index vars `self.0..self.2`, `o.0..o.2`. The
        // gate MUST assume it: without the `FpConst` arm in `in_assumable_fragment`
        // the whole set is dropped as UnsupportedSyntax and the body's `self.x*o.x`
        // overflow VCs have no input bound to discharge against (the a3d-geom
        // FloatOverflowToInfinity regression). `self`=local 1, `o`=local 2 are the
        // by-value struct params; the field vars normalize to those param bases.
        let body = body_with(vec![(0, None), (1, Some("self")), (2, Some("o"))], 2);
        let names = multimap(&[("self", &[1]), ("o", &[2])]);
        let mut pres = vec![Formula::And(vec![
            fbounded("self.0", 1.0e30),
            fbounded("self.1", 1.0e30),
            fbounded("self.2", 1.0e30),
            fbounded("o.0", 1.0e30),
            fbounded("o.1", 1.0e30),
            fbounded("o.2", 1.0e30),
        ])];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(reasons.is_empty(), "float field-magnitude precond must be assumed: {reasons:?}");
        assert_eq!(pres.len(), 1, "the precondition must survive the gate");
    }

    #[test]
    fn float_precondition_over_nonparam_field_still_dropped() {
        // Soundness guard: admitting FpConst must NOT relax the entry-parameter
        // discipline. A field bound over a NON-parameter base (`ghost.0`) is still
        // rejected — the float literal is fine, but `ghost` is not a param.
        let body = body_with(vec![(0, None), (1, Some("self"))], 1);
        let names = multimap(&[("self", &[1])]);
        let mut pres = vec![fbounded("ghost.0", 1.0e30)];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(
            reasons.iter().any(|r| matches!(r, AssumeSkipReason::NonParamVariable(_))),
            "a float bound over a non-param base must still drop: {reasons:?}"
        );
        assert!(pres.is_empty());
    }

    #[test]
    fn negative_literal_witness_found() {
        // Witness needs a negative candidate (-262143 occurs as a literal).
        let body = body_with(vec![(0, None), (1, Some("y"))], 1);
        let names = multimap(&[("y", &[1])]);
        let mut pres = vec![bounded("y", -262143, -262000)];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(reasons.is_empty(), "{reasons:?}");
    }

    /// A body with a single reference parameter `a` at local 1.
    fn ref_param_body(mutable: bool) -> VerifiableBody {
        VerifiableBody {
            locals: vec![
                trust_types::LocalDecl {
                    index: 0,
                    ty: trust_types::Ty::Int { width: 32, signed: false },
                    name: None,
                },
                trust_types::LocalDecl {
                    index: 1,
                    ty: trust_types::Ty::Ref {
                        mutable,
                        inner: Box::new(trust_types::Ty::Int { width: 32, signed: false }),
                    },
                    name: Some("a".to_string()),
                },
            ],
            blocks: Vec::new(),
            arg_count: 1,
            return_ty: trust_types::Ty::Int { width: 32, signed: false },
            datatype_defs: Default::default(),
        }
    }

    #[test]
    fn shared_ref_deref_is_assumed() {
        // `#[requires(*a <= 100)]` on `a: &u32` — the pointee of a SHARED ref is
        // immutable, so the caller-proved entry fact is assume-guarantee sound.
        // The deref term `a*` must be recognized as caller-bound (audit #4).
        let body = ref_param_body(false);
        let names = multimap(&[("a", &[1])]);
        let mut pres = vec![Formula::Le(Box::new(var("a*")), Box::new(int(100)))];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(reasons.is_empty(), "shared-ref deref must be assumed: {reasons:?}");
        assert_eq!(pres.len(), 1, "the precondition must survive the gate");
    }

    #[test]
    fn mut_ref_deref_drops_assumption() {
        // `#[requires(*a <= 100)]` on `a: &mut u32` — the pointee CAN be mutated
        // in the body, so the entry fact may go stale. Assuming it is a false-
        // PROVE hazard, so the gate must drop it (fail-closed).
        //
        // Trust: the diagnostic is `NonParamVariable("a*")`, NOT
        // `ShadowedParamName("a")`. This comment used to claim the latter, and
        // the guard at `aliases_param` now says why that is wrong in its own
        // words: "If `raw_base` is already the parameter's canonical name,
        // rejection came from the term shape (for example `a*` on `a: &mut T`),
        // not from a debug-name alias." `a` IS the canonical parameter name, so
        // this is a term-shape rejection and reporting a shadow would be the
        // less precise answer.
        //
        // The property this test actually guards — the assumption set is dropped
        // fail-closed — is unchanged, and is the `pres.is_empty()` assertion
        // below. Only the label moved.
        let body = ref_param_body(true);
        let names = multimap(&[("a", &[1])]);
        let mut pres = vec![Formula::Le(Box::new(var("a*")), Box::new(int(100)))];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(
            reasons.iter().any(|r| matches!(r, AssumeSkipReason::NonParamVariable(n) if n == "a*")),
            "mut-ref deref must NOT be assumed, and `a*` is a TERM-SHAPE rejection: {reasons:?}"
        );
        assert!(pres.is_empty());
    }

    // ---- Trust: piece #8 — length-relationship precondition admissibility ----

    fn mut_slice_ty() -> trust_types::Ty {
        trust_types::Ty::Ref {
            mutable: true,
            inner: Box::new(trust_types::Ty::Slice {
                elem: Box::new(trust_types::Ty::Int { width: 32, signed: false }),
            }),
        }
    }

    /// A body `fn fill(arr: &mut [u32], n: usize)` — one slice param `arr` (local
    /// 1), one scalar param `n` (local 2), no reslice. `blocks` is empty, so the
    /// slice param is trivially length-stable.
    fn fill_body() -> VerifiableBody {
        VerifiableBody {
            locals: vec![
                trust_types::LocalDecl { index: 0, ty: trust_types::Ty::unit_ty(), name: None },
                trust_types::LocalDecl { index: 1, ty: mut_slice_ty(), name: Some("arr".into()) },
                trust_types::LocalDecl {
                    index: 2,
                    ty: trust_types::Ty::Int { width: 64, signed: false },
                    name: Some("n".into()),
                },
            ],
            blocks: Vec::new(),
            arg_count: 2,
            return_ty: trust_types::Ty::unit_ty(),
            datatype_defs: Default::default(),
        }
    }

    fn resliced_fill_body() -> VerifiableBody {
        let mut body = fill_body();
        // Simulate a mutable reborrow of the WHOLE param fat pointer (`&mut arr`,
        // no leading deref) — the reslice channel.
        body.blocks = vec![trust_types::BasicBlock {
            id: trust_types::BlockId(0),
            stmts: vec![trust_types::Statement::Assign {
                place: trust_types::Place::local(3),
                rvalue: trust_types::Rvalue::Ref {
                    mutable: true,
                    place: trust_types::Place::local(1),
                },
                span: trust_types::SourceSpan::default(),
            }],
            terminator: trust_types::Terminator::Return,
        }];
        body
    }

    #[test]
    fn length_precond_of_slice_param_admitted() {
        // `P = n <= arr__slice_len` over a slice param `arr` + scalar param `n`.
        let body = fill_body();
        let names = multimap(&[("arr", &[1]), ("n", &[2])]);
        let mut pres = vec![Formula::Le(Box::new(var("n")), Box::new(var("arr__slice_len")))];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(reasons.is_empty(), "slice-param length precond must be admitted: {reasons:?}");
        assert_eq!(pres.len(), 1, "the precondition must survive the gate");
    }

    #[test]
    fn source_length_precond_normalizes_to_canonical_slice_symbol() {
        // Exact source `arr.len()` lowers to `arr__len`, but body bounds VCs and
        // modular σ summaries use `arr__slice_len`. Admission must rewrite to
        // that canonical leaf, never merely whitelist an independent variable.
        let body = fill_body();
        let names = multimap(&[("arr", &[1]), ("n", &[2])]);
        let mut pres = vec![Formula::Le(Box::new(var("n")), Box::new(var("arr__len")))];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(reasons.is_empty(), "source slice length must be admitted: {reasons:?}");
        assert_eq!(
            pres,
            vec![Formula::Le(Box::new(var("n")), Box::new(var("arr__slice_len")),)],
            "source and bounds formulas must share the canonical length leaf",
        );
        assert!(!pres[0].free_variables().contains("arr__len"));
    }

    #[test]
    fn negative_slice_length_witness_is_impossible_and_dropped() {
        let body = fill_body();
        let names = multimap(&[("arr", &[1]), ("n", &[2])]);
        let mut pres = vec![Formula::Lt(Box::new(var("arr__slice_len")), Box::new(int(0)))];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert_eq!(reasons, vec![AssumeSkipReason::NoSatisfiableWitness]);
        assert!(pres.is_empty());
    }

    #[test]
    fn length_of_nonslice_param_rejected() {
        // `x__slice_len` where `x` is a SCALAR param — not a slice, so its
        // `__slice_len` symbol is NOT admitted (NonParamVariable).
        let body = body_with(vec![(0, None), (1, Some("x"))], 1);
        let names = multimap(&[("x", &[1])]);
        let mut pres = vec![Formula::Le(Box::new(var("x")), Box::new(var("x__slice_len")))];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(
            reasons
                .iter()
                .any(|r| matches!(r, AssumeSkipReason::NonParamVariable(n) if n == "x__slice_len")),
            "scalar-param `__slice_len` must be rejected: {reasons:?}"
        );
        assert!(pres.is_empty());
    }

    #[test]
    fn length_of_resliced_slice_param_rejected() {
        // INV-1: the callee reslices `arr` (a mutable reborrow of the whole param
        // fat pointer), so `arr__slice_len` is NOT length-stable → dropped.
        let body = resliced_fill_body();
        let names = multimap(&[("arr", &[1]), ("n", &[2])]);
        let mut pres = vec![Formula::Le(Box::new(var("n")), Box::new(var("arr__slice_len")))];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(
            reasons.iter().any(
                |r| matches!(r, AssumeSkipReason::NonParamVariable(n) if n == "arr__slice_len")
            ),
            "resliced slice param length must be rejected (INV-1): {reasons:?}"
        );
        assert!(pres.is_empty());
    }

    #[test]
    fn source_length_of_resliced_slice_param_rejected() {
        let body = resliced_fill_body();
        let names = multimap(&[("arr", &[1]), ("n", &[2])]);
        let mut pres = vec![Formula::Le(Box::new(var("n")), Box::new(var("arr__len")))];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(
            reasons
                .iter()
                .any(|r| matches!(r, AssumeSkipReason::NonParamVariable(n) if n == "arr__len")),
            "unstable source length must not be rebound or admitted: {reasons:?}",
        );
        assert!(pres.is_empty());
    }

    #[test]
    fn element_write_keeps_slice_param_length_stable() {
        // `arr[i] = 0` lowers to a store THROUGH a deref (`(*arr)[i] = 0`), which
        // writes the pointee, not the fat pointer — the length stays stable, so the
        // length symbol is STILL admitted. (This is the `fill` body's actual shape.)
        let mut body = fill_body();
        body.blocks = vec![trust_types::BasicBlock {
            id: trust_types::BlockId(0),
            stmts: vec![trust_types::Statement::Assign {
                place: trust_types::Place {
                    local: 1,
                    projections: vec![
                        trust_types::Projection::Deref,
                        trust_types::Projection::Index(2),
                    ],
                },
                rvalue: trust_types::Rvalue::Use(trust_types::Operand::Constant(
                    trust_types::ConstValue::Int(0),
                )),
                span: trust_types::SourceSpan::default(),
            }],
            terminator: trust_types::Terminator::Return,
        }];
        let names = multimap(&[("arr", &[1]), ("n", &[2])]);
        let mut pres = vec![Formula::Le(Box::new(var("n")), Box::new(var("arr__slice_len")))];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(
            reasons.is_empty(),
            "element write must not disqualify the slice-param length: {reasons:?}"
        );
        assert_eq!(pres.len(), 1);
    }

    #[test]
    fn shadowed_slice_param_name_length_rejected() {
        // A body local shadows the param name `arr` — the `arr__slice_len` render
        // is ambiguous (could key on the shadow), so it is NOT admitted.
        let mut body = fill_body();
        body.locals.push(trust_types::LocalDecl {
            index: 3,
            ty: mut_slice_ty(),
            name: Some("arr".into()),
        });
        let names = multimap(&[("arr", &[1, 3]), ("n", &[2])]);
        let mut pres = vec![Formula::Le(Box::new(var("n")), Box::new(var("arr__slice_len")))];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(
            reasons.iter().any(
                |r| matches!(r, AssumeSkipReason::NonParamVariable(n) if n == "arr__slice_len")
            ),
            "shadowed slice-param length must be rejected: {reasons:?}"
        );
        assert!(pres.is_empty());
    }

    #[test]
    fn source_length_of_shadowed_slice_param_rejected() {
        let mut body = fill_body();
        body.locals.push(trust_types::LocalDecl {
            index: 3,
            ty: mut_slice_ty(),
            name: Some("arr".into()),
        });
        let names = multimap(&[("arr", &[1, 3]), ("n", &[2])]);
        let mut pres = vec![Formula::Le(Box::new(var("n")), Box::new(var("arr__len")))];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(
            reasons
                .iter()
                .any(|r| matches!(r, AssumeSkipReason::NonParamVariable(n) if n == "arr__len")),
            "shadowed source length must not be rebound or admitted: {reasons:?}",
        );
        assert!(pres.is_empty());
    }

    // ---- Trust: float field-magnitude precondition admissibility ----

    /// `|name| <= c`, the two-sided form a float magnitude `#[requires]` lowers to.
    fn field_bounded(name: &str, c: i128) -> Formula {
        Formula::And(vec![
            Formula::Le(Box::new(var(name)), Box::new(int(c))),
            Formula::Ge(Box::new(var(name)), Box::new(int(-c))),
        ])
    }

    #[test]
    fn byvalue_param_field_bound_admitted() {
        // `#[requires(|self.0|<=C && |self.1|<=C && |o.0|<=C && |o.1|<=C)]` on
        // `dot(self, o)` — by-value params, field-index vars → all survive.
        let body = body_with(vec![(0, None), (1, Some("self")), (2, Some("o"))], 2);
        let names = multimap(&[("self", &[1]), ("o", &[2])]);
        let mut pres = vec![
            field_bounded("self.0", 1_000_000),
            field_bounded("self.1", 1_000_000),
            field_bounded("o.0", 1_000_000),
            field_bounded("o.1", 1_000_000),
        ];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(reasons.is_empty(), "by-value param field bounds must survive: {reasons:?}");
        assert_eq!(pres.len(), 4);
    }

    #[test]
    fn many_field_bounds_admitted_via_all_zeros_witness() {
        // 8 independent field vars (Vec4::dot): the brute-force witness search caps
        // at MAX_ASSIGNMENTS (8^4 = 4096) and would bail to a spurious "no
        // witness"; the all-zeros fast-accept admits the conjunction.
        let body = body_with(vec![(0, None), (1, Some("self")), (2, Some("o"))], 2);
        let names = multimap(&[("self", &[1]), ("o", &[2])]);
        let mut pres: Vec<Formula> =
            ["self.0", "self.1", "self.2", "self.3", "o.0", "o.1", "o.2", "o.3"]
                .iter()
                .copied()
                .map(|n| field_bounded(n, 1_000_000_000))
                .collect();
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(reasons.is_empty(), "8 field bounds must be admitted (all-zeros): {reasons:?}");
        assert_eq!(pres.len(), 8);
    }

    #[test]
    fn shared_ref_param_field_bound_admitted() {
        // `(*self).2` on a `&T` param renders "a*.0" (Deref then Field). The
        // immutable pointee makes the entry fact assumable, like the `<p>*` case.
        let body = ref_param_body(false);
        let names = multimap(&[("a", &[1])]);
        let mut pres = vec![field_bounded("a*.0", 1_000_000)];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(reasons.is_empty(), "shared-ref param field must be admitted: {reasons:?}");
        assert_eq!(pres.len(), 1);
    }

    #[test]
    fn mut_ref_param_field_bound_rejected() {
        // A `&mut` pointee CAN be mutated → its field entry fact may go stale → NOT
        // admitted (fail-closed), matching the `<p>*` &mut rejection.
        let body = ref_param_body(true);
        let names = multimap(&[("a", &[1])]);
        let mut pres = vec![field_bounded("a*.0", 1_000_000)];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(
            reasons
                .iter()
                .any(|r| matches!(r, AssumeSkipReason::NonParamVariable(n) if n == "a*.0")),
            "mut-ref param field must be rejected: {reasons:?}"
        );
        assert!(pres.is_empty());
    }

    #[test]
    fn field_of_non_param_rejected() {
        // `tmp.0` where `tmp` is a BODY local, not a parameter → NonParamVariable.
        let body = body_with(vec![(0, None), (1, Some("self")), (2, Some("tmp"))], 1);
        let names = multimap(&[("self", &[1]), ("tmp", &[2])]);
        let mut pres = vec![field_bounded("tmp.0", 1_000_000)];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(
            reasons
                .iter()
                .any(|r| matches!(r, AssumeSkipReason::NonParamVariable(n) if n == "tmp.0")),
            "field of a non-parameter must be rejected: {reasons:?}"
        );
        assert!(pres.is_empty());
    }

    #[test]
    fn shadowed_base_field_bound_rejected() {
        // A body local shadows the param name `self` → the base "self" maps to two
        // locals → the field precondition's base is ambiguous → dropped (this is the
        // same false-PROVE guard that protects bare-param bounds).
        let body = body_with(vec![(0, None), (1, Some("self")), (2, Some("self"))], 1);
        let names = multimap(&[("self", &[1, 2])]);
        let mut pres = vec![field_bounded("self.0", 1_000_000)];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(
            reasons
                .iter()
                .any(|r| matches!(r, AssumeSkipReason::ShadowedParamName(n) if n == "self")),
            "shadowed field base must be rejected: {reasons:?}"
        );
        assert!(pres.is_empty());
    }

    #[test]
    fn contradictory_field_bound_still_dropped() {
        // The all-zeros probe must NOT paper over vacuity: `self.0 >= 5 && self.0 <= 3`
        // fails at zero and everywhere → still NoSatisfiableWitness.
        let body = body_with(vec![(0, None), (1, Some("self"))], 1);
        let names = multimap(&[("self", &[1])]);
        let mut pres = vec![Formula::And(vec![
            Formula::Ge(Box::new(var("self.0")), Box::new(int(5))),
            Formula::Le(Box::new(var("self.0")), Box::new(int(3))),
        ])];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert_eq!(reasons, vec![AssumeSkipReason::NoSatisfiableWitness]);
        assert!(pres.is_empty());
    }

    // ---- Trust: FLOAT-literal field magnitude preconditions ----

    /// An f64 float-sorted variable, as the retyped contract carries a field var
    /// compared against a float literal. (The float-literal helper `fp` is defined
    /// once, further up — a second copy here would be a duplicate definition.)
    fn float_var(name: &str) -> Formula {
        Formula::Var(name.to_string(), Sort::Float { eb: 11, sb: 53 })
    }
    /// `|name| <= c` with FLOAT-sorted var and float-literal bounds (the a3d shape).
    fn float_field_bounded(name: &str, c: f64) -> Formula {
        Formula::And(vec![
            Formula::Le(Box::new(float_var(name)), Box::new(fp(c))),
            Formula::Ge(Box::new(float_var(name)), Box::new(fp(-c))),
        ])
    }

    #[test]
    fn float_field_magnitude_bound_admitted() {
        // `#[requires(self.0 <= 1.0e30 && self.0 >= -1.0e30)]` — the float-sorted
        // field bound is satisfied by the all-zeros witness (0.0 ∈ [-1e30, 1e30]),
        // which the float-aware `eval_bool` now recognises. It must survive the gate.
        let body = body_with(vec![(0, None), (1, Some("self"))], 1);
        let names = multimap(&[("self", &[1])]);
        let mut pres = vec![float_field_bounded("self.0", 1.0e30)];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(reasons.is_empty(), "float field bound must be admitted: {reasons:?}");
        assert_eq!(pres.len(), 1);
    }

    #[test]
    fn contradictory_float_field_bound_dropped() {
        // SOUNDNESS: `self.0 >= 1e30 && self.0 <= -1e30` is UNSATISFIABLE — the
        // all-zeros probe fails (0.0 !>= 1e30) and no integer-grid witness satisfies
        // it, so it is dropped (fail-closed). The float eval must not false-accept.
        let body = body_with(vec![(0, None), (1, Some("self"))], 1);
        let names = multimap(&[("self", &[1])]);
        let mut pres = vec![Formula::And(vec![
            Formula::Ge(Box::new(float_var("self.0")), Box::new(fp(1.0e30))),
            Formula::Le(Box::new(float_var("self.0")), Box::new(fp(-1.0e30))),
        ])];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert_eq!(reasons, vec![AssumeSkipReason::NoSatisfiableWitness]);
        assert!(pres.is_empty());
    }

    // ---- Trust: full literal projection chains (F4 gate admission) ----

    #[test]
    fn byvalue_chain_with_array_index_admitted() {
        // `self.0[3].1 <= 1e30 && …` on a by-value param `self` (Mat4-style
        // `#[requires(self.cols[3].y <= 1.0e30)]` lowered to positional form).
        // The chain normalizes to base `self`; the full bracketed name never
        // enters the referenced set, and the all-zeros witness satisfies it.
        let body = body_with(vec![(0, None), (1, Some("self"))], 1);
        let names = multimap(&[("self", &[1])]);
        let mut pres = vec![float_field_bounded("self.0[3].1", 1.0e30)];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(
            reasons.is_empty(),
            "literal chain on by-value param must be admitted: {reasons:?}"
        );
        assert_eq!(pres.len(), 1);
    }

    #[test]
    fn shared_ref_chain_admitted() {
        // `a*.0.0` — a nested field of a SHARED-ref parameter's pointee
        // (`(*self).min.x` → `self*.0.0`, the Aabb shape). The immutable pointee
        // makes any depth of the chain an entry fact, like the `<p>*` case.
        let body = ref_param_body(false);
        let names = multimap(&[("a", &[1])]);
        let mut pres = vec![float_field_bounded("a*.0.0", 1.0e30)];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(reasons.is_empty(), "shared-ref nested chain must be admitted: {reasons:?}");
        assert_eq!(pres.len(), 1);
    }

    #[test]
    fn mut_ref_chain_rejected() {
        // SOUNDNESS twin: the SAME chain over a `&mut` param must NOT be assumed —
        // the pointee can be mutated, staling the entry fact (fail-closed).
        let body = ref_param_body(true);
        let names = multimap(&[("a", &[1])]);
        let mut pres = vec![float_field_bounded("a*.0.0", 1.0e30)];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(
            reasons
                .iter()
                .any(|r| matches!(r, AssumeSkipReason::NonParamVariable(n) if n == "a*.0.0")),
            "mut-ref chain must be rejected: {reasons:?}"
        );
        assert!(pres.is_empty());
    }

    #[test]
    fn chain_of_non_param_rejected() {
        // SOUNDNESS twin: a well-formed chain whose HEAD is not a parameter
        // (`ghost.0[1]`) is not caller-bound — still NonParamVariable.
        let body = body_with(vec![(0, None), (1, Some("self"))], 1);
        let names = multimap(&[("self", &[1])]);
        let mut pres = vec![float_field_bounded("ghost.0[1]", 1.0e30)];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(
            reasons
                .iter()
                .any(|r| matches!(r, AssumeSkipReason::NonParamVariable(n) if n == "ghost.0[1]")),
            "chain off a non-param head must be rejected: {reasons:?}"
        );
        assert!(pres.is_empty());
    }

    #[test]
    fn runtime_index_chain_rejected() {
        // SOUNDNESS twin: a NON-LITERAL index (`self.0[x].1`) is not
        // entry-determined. The spec parser cannot produce this name today;
        // the gate still rejects it on its own (defense in depth, fail-closed).
        let body = body_with(vec![(0, None), (1, Some("self"))], 1);
        let names = multimap(&[("self", &[1])]);
        let mut pres = vec![float_field_bounded("self.0[x].1", 1.0e30)];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(
            reasons
                .iter()
                .any(|r| matches!(r, AssumeSkipReason::NonParamVariable(n) if n == "self.0[x].1")),
            "runtime-index chain must be rejected: {reasons:?}"
        );
        assert!(pres.is_empty());
    }

    #[test]
    fn head_index_of_array_param_admitted() {
        // `p[0]` — a literal element of a parameter that IS an array. The head is
        // in param_names and the segment is a literal index, so the same
        // entry-value rationale as `p.0` applies (admission is name-disciplined;
        // the declared Ty is not consulted here).
        let body = body_with(vec![(0, None), (1, Some("p"))], 1);
        let names = multimap(&[("p", &[1])]);
        let mut pres = vec![float_field_bounded("p[0]", 1.0e30)];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(reasons.is_empty(), "literal head-index of a param must be admitted: {reasons:?}");
        assert_eq!(pres.len(), 1);
    }

    #[test]
    fn malformed_chains_rejected() {
        // Shapes the grammar must fall through to None on: a `*` not immediately
        // after the head, an unclosed bracket, an empty segment, digits-then-junk
        // inside a bracket. All fail-closed as NonParamVariable.
        let body = body_with(vec![(0, None), (1, Some("self"))], 1);
        let names = multimap(&[("self", &[1])]);
        for bad in ["self.0*.1", "self.0[3", "self.[0]", "self.0[3x]", "self..0"] {
            let mut pres = vec![float_field_bounded(bad, 1.0e30)];
            let reasons = gate_contract_preconditions(&mut pres, &body, &names);
            assert!(
                reasons
                    .iter()
                    .any(|r| matches!(r, AssumeSkipReason::NonParamVariable(n) if n == bad)),
                "malformed chain `{bad}` must be rejected: {reasons:?}"
            );
            assert!(pres.is_empty(), "malformed chain `{bad}` must drop the set");
        }
    }

    #[test]
    fn many_bracketed_chain_bounds_admitted_via_all_zeros() {
        // 16 independent bracketed-chain vars (Mat4: cols[0..3] × fields 0..3).
        // The cross-product enumeration would blow MAX_ASSIGNMENTS; the all-zeros
        // fast path must satisfy the pure magnitude conjunction (each var misses
        // `witness_domains`, reads Int(0), and evaluates as 0.0 in the float lane).
        let body = body_with(vec![(0, None), (1, Some("self"))], 1);
        let names = multimap(&[("self", &[1])]);
        let mut pres: Vec<Formula> = (0..4)
            .flat_map(|k| (0..4).map(move |f| format!("self.0[{k}].{f}")))
            .map(|n| float_field_bounded(&n, 1.0e30))
            .collect();
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(reasons.is_empty(), "16 chain bounds must be admitted (all-zeros): {reasons:?}");
        assert_eq!(pres.len(), 16);
    }

    // ---- Trust: compound float terms in the witness search ----

    /// A body whose params are genuine f64 locals (`Ty::Float` has no
    /// `witness_domain_for_ty` arm, so the vars take the unconstrained
    /// {0,±1,±2} candidate grid — the a3d difference-bound shape).
    fn f64_params_body(names: &[&str]) -> VerifiableBody {
        let mut locals =
            vec![trust_types::LocalDecl { index: 0, ty: trust_types::Ty::unit_ty(), name: None }];
        for (position, name) in names.iter().enumerate() {
            locals.push(trust_types::LocalDecl {
                index: position + 1,
                ty: trust_types::Ty::Float { width: 64 },
                name: Some((*name).to_string()),
            });
        }
        VerifiableBody {
            locals,
            blocks: Vec::new(),
            arg_count: names.len(),
            return_ty: trust_types::Ty::unit_ty(),
            datatype_defs: Default::default(),
        }
    }

    #[test]
    fn difference_bound_witness_found() {
        // `(near) - (far) <= -1e-6` plus two-sided magnitude bounds — the
        // perspective_rh shape. The all-zeros probe fails (0-0 = 0 > -1e-6); the
        // odometer must find (near=0, far=1): Sub evaluates to -1.0 <= -1e-6 with
        // the new Sub arm. Without it the whole set dropped as NoSatisfiableWitness.
        let body = f64_params_body(&["near", "far"]);
        let names = multimap(&[("near", &[1]), ("far", &[2])]);
        let mut pres = vec![
            Formula::Le(
                Box::new(Formula::Sub(Box::new(float_var("near")), Box::new(float_var("far")))),
                Box::new(fp(-1.0e-6)),
            ),
            float_field_bounded("near", 1.0e15),
            float_field_bounded("far", 1.0e15),
        ];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(reasons.is_empty(), "difference bound must find a witness: {reasons:?}");
        assert_eq!(pres.len(), 3);
    }

    #[test]
    fn contradictory_difference_bound_dropped() {
        // SOUNDNESS twin: `(near) - (far) <= -1e-6 && near - far >= 1e-6` is
        // UNSATISFIABLE — the new Sub arm must not fabricate a witness; every
        // grid assignment fails one conjunct, so the set drops (fail-closed).
        let body = f64_params_body(&["near", "far"]);
        let names = multimap(&[("near", &[1]), ("far", &[2])]);
        let diff = || Formula::Sub(Box::new(float_var("near")), Box::new(float_var("far")));
        let mut pres = vec![Formula::And(vec![
            Formula::Le(Box::new(diff()), Box::new(fp(-1.0e-6))),
            Formula::Ge(Box::new(diff()), Box::new(fp(1.0e-6))),
        ])];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert_eq!(reasons, vec![AssumeSkipReason::NoSatisfiableWitness]);
        assert!(pres.is_empty());
    }

    #[test]
    fn unsat_float_predicate_still_dropped() {
        // SOUNDNESS twin (task-3c): `x <= -1.0 && x >= 1.0` has no model at all —
        // the widened float evaluator must still report NoSatisfiableWitness.
        let body = f64_params_body(&["x"]);
        let names = multimap(&[("x", &[1])]);
        let mut pres = vec![Formula::And(vec![
            Formula::Le(Box::new(float_var("x")), Box::new(fp(-1.0))),
            Formula::Ge(Box::new(float_var("x")), Box::new(fp(1.0))),
        ])];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert_eq!(reasons, vec![AssumeSkipReason::NoSatisfiableWitness]);
        assert!(pres.is_empty());
    }

    #[test]
    fn product_and_negated_difference_evaluate() {
        // Mul arm: `x * x >= 4.0` needs x = ±2 off the grid (zero fails).
        // Neg-over-compound: `-(near - far) >= 1e-6` is the mirrored difference
        // bound; Neg must recurse into the float-evaluated Sub.
        let body = f64_params_body(&["x"]);
        let names = multimap(&[("x", &[1])]);
        let mut pres = vec![Formula::Ge(
            Box::new(Formula::Mul(Box::new(float_var("x")), Box::new(float_var("x")))),
            Box::new(fp(4.0)),
        )];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(reasons.is_empty(), "x*x >= 4 must find x=±2: {reasons:?}");
        assert_eq!(pres.len(), 1);

        let body = f64_params_body(&["near", "far"]);
        let names = multimap(&[("near", &[1]), ("far", &[2])]);
        let mut pres = vec![Formula::Ge(
            Box::new(Formula::Neg(Box::new(Formula::Sub(
                Box::new(float_var("near")),
                Box::new(float_var("far")),
            )))),
            Box::new(fp(1.0e-6)),
        )];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(reasons.is_empty(), "-(near-far) >= 1e-6 must find a witness: {reasons:?}");
        assert_eq!(pres.len(), 1);
    }

    // ---- Trust: the contract lowerer's OWN synthetic locals are not user shadows ----
    //
    // Measured on stage2 (2026-08-06, `-Ztrust-dump=mir-only`) for
    //   #[requires(n >= 0)] #[ensures(|ret| *ret >= 0)] fn f(n: i32) -> i32 { n }
    // the emitted body has ONE named param local — `{"index": 1, "name": "n"}` — and
    // `preconditions` carrying ONLY the synthetic i32 range fact: the authored
    // `n >= 0` was dropped, and the postcondition then refuted with
    // `verified_counterexample = true`. The sole gate reason was
    // ShadowedParamName("__ret"): `#[ensures]` lowering mints the local `__ret` and
    // copy-propagation parks its `var_debug_info` entry on `_1`.

    /// `__ret` must be classified by the SHARED classifier, not an ad-hoc prefix
    /// test — but the alias-scan exemption is the `GeneratedMetadata` (`__`)
    /// family ONLY, a strict subset of what that classifier reserves.
    #[test]
    fn contract_lowering_locals_are_reserved_synthetic_names() {
        for reserved in ["__ret", "__old_x", "__trust_constparam_0_N", "arr__slice_len"] {
            assert!(reserved_synthetic_debug_name(reserved), "`{reserved}` must be reserved");
        }
        for ordinary in ["n", "x", "self", "tmp", "older", "payload_length", "n_len", "max_len"] {
            assert!(!reserved_synthetic_debug_name(ordinary), "`{ordinary}` must be ordinary");
        }
        // RESERVED BY THE CLASSIFIER, BUT DELIBERATELY NOT EXEMPT HERE. These are
        // spellings a user can legally bind (`_0` is also the MIR return place,
        // and `old_n` is a plain identifier). The alias scan must keep
        // gating on them: exempting a name a user can actually write would hide a
        // real shadow and let an ambiguous entry fact be assumed — a false-PROVE.
        for classified_but_not_exempt in ["_0", "_1", "old_n", "result"] {
            assert!(
                trust_types::source_contract_synthetic_name_collision(classified_but_not_exempt)
                    .is_some(),
                "`{classified_but_not_exempt}` is still reserved by the classifier",
            );
            assert!(
                !reserved_synthetic_debug_name(classified_but_not_exempt),
                "`{classified_but_not_exempt}` must NOT be exempt from the alias scan",
            );
        }
    }

    #[test]
    fn synthetic_contract_local_aliasing_param_does_not_gate() {
        // pA, exactly as dumped: param `n` at local 1, plus the `#[ensures]`
        // lowerer's `__ret` copy-propagated onto that same local. `__ret` is
        // demoted by `build_debug_name_map`, so it names nothing in the extracted
        // body and cannot steal `n`'s binding — the authored `n >= 0` must survive.
        let body = body_with(vec![(0, None), (1, Some("n"))], 1);
        let names = multimap(&[("n", &[1]), ("__ret", &[1])]);
        let mut pres = vec![Formula::Ge(Box::new(var("n")), Box::new(int(0)))];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(
            reasons.is_empty(),
            "the contract lowerer's own local is not a shadow: {reasons:?}"
        );
        assert_eq!(pres, vec![Formula::Ge(Box::new(var("n")), Box::new(int(0)))]);
    }

    #[test]
    fn synthetic_alias_exemption_is_the_generated_metadata_family_only() {
        // EXEMPT: the `__` namespace, which Trust's own MIR/Formula producers
        // own outright. `__ret` is the artifact this exists for.
        for reserved in ["__ret", "__old_n", "__trust_constparam_0"] {
            let body = body_with(vec![(0, None), (1, Some("n"))], 1);
            let names = multimap(&[("n", &[1]), (reserved, &[1])]);
            let mut pres = vec![Formula::Ge(Box::new(var("n")), Box::new(int(0)))];
            let reasons = gate_contract_preconditions(&mut pres, &body, &names);
            assert!(reasons.is_empty(), "`{reserved}` must not gate: {reasons:?}");
            assert_eq!(pres.len(), 1, "`{reserved}` must not drop the assumption");
        }
        // NOT EXEMPT, and this is the soundness half. Ordinary legal Rust
        // bindings — `old_n`, `n_len`, `buf_len`, `max_value`, `x_sign`, `_0` —
        // must still gate whether or not the classifier reserves them.
        // Exempting a name a user can write would hide a genuine shadow from
        // this gate and let an ambiguous entry fact be assumed, which is a
        // false-PROVE: the one direction this gate exists to prevent.
        for user_binding in ["old_n", "n_len", "buf_len", "max_value", "x_sign", "_0"] {
            let body = body_with(vec![(0, None), (1, Some("n"))], 1);
            let names = multimap(&[("n", &[1]), (user_binding, &[1])]);
            let mut pres = vec![Formula::Ge(Box::new(var("n")), Box::new(int(0)))];
            let reasons = gate_contract_preconditions(&mut pres, &body, &names);
            assert!(
                !reasons.is_empty(),
                "`{user_binding}` is a legal source binding aliasing the param local \
                 and MUST still gate",
            );
            assert!(pres.is_empty(), "`{user_binding}` must drop the assumption");
        }
    }

    #[test]
    fn copy_propagated_parameter_is_restated_beside_a_synthetic_alias() {
        // EXPECTATION CHANGED (forced parameter restatement) — pE, exactly as
        // dumped on stage2 for
        //   #[requires(n >= 0)] #[ensures(|r| *r >= 0)] fn f(n: i32) -> i32 { let x = n; x }
        // (`arg_count = 1`, `locals[1] = {"index":1,"name":"x"}`). `{ let x = n; x }`
        // copy-props `x` onto the parameter local, the last-write-wins collapse
        // names local 1 `"x"` rather than `"n"`, and `#[ensures]` lowering parks
        // `__ret` there too. This used to drop the authored, caller-proved
        // `n >= 0`, leaving the true postcondition an honest UNKNOWN.
        //
        // `n` and `x` are ONE entity — parameter position 1 — and here the
        // correspondence is FORCED: every parameter position is named with a plain
        // identifier; `n` is the only clause spelling the body namespace cannot
        // bind; `x` is the only parameter position the clause does not name; `n`
        // is a plain, non-reserved identifier carrying one sort the `i32`
        // parameter admits; MIR's own debug record gives `n` and `x` exactly ONE
        // row each, both on local 1; and the only other row there is Trust's own
        // `__ret`. So the clause is RESTATED as `x >= 0` and kept, and the
        // postcondition discharges. `__ret` must still not be reported as a shadow.
        let body = body_with(vec![(0, None), (1, Some("x"))], 1);
        let names = multimap(&[("n", &[1]), ("x", &[1]), ("__ret", &[1])]);
        let mut pres = vec![Formula::Ge(Box::new(var("n")), Box::new(int(0)))];
        let reasons = gate_restating(&mut pres, &body, &names, &["n"]);
        assert!(reasons.is_empty(), "the forced restatement must be kept: {reasons:?}");
        assert_eq!(
            pres,
            vec![Formula::Ge(Box::new(var("x")), Box::new(int(0)))],
            "the entry hypothesis must speak the BODY's spelling of parameter 1",
        );
    }

    #[test]
    fn user_shadow_beside_the_restated_pair_still_gates() {
        // SOUNDNESS TWIN of the test above, and the half of the old
        // `user_shadow_on_a_param_local_still_gates_beside_a_synthetic_alias`
        // expectation that must survive. `t` is an ordinary user binding on the
        // parameter local that is neither the clause's spelling nor the body's, so
        // the row census in condition (7) fails: with three user rows on `_1`,
        // nothing forces `n` to be the earliest one — i.e. nothing forces it to be
        // the parameter's own source name rather than a body binding or a
        // same-named `const`. The restatement declines and the whole assumption
        // set drops, reported as a shadow exactly as before.
        let body = body_with(vec![(0, None), (1, Some("x"))], 1);
        let names = multimap(&[("n", &[1]), ("x", &[1]), ("t", &[1]), ("__ret", &[1])]);
        let mut pres = vec![Formula::Ge(Box::new(var("n")), Box::new(int(0)))];
        let reasons = gate_restating(&mut pres, &body, &names, &["n"]);
        assert!(
            reasons.iter().any(|r| matches!(r, AssumeSkipReason::ShadowedParamName(n) if n == "n")),
            "an unforced correspondence must still gate: {reasons:?}"
        );
        assert!(
            reasons.iter().any(|r| matches!(r, AssumeSkipReason::ShadowedParamName(n) if n == "t")),
            "a genuine user shadow on the param local must still gate: {reasons:?}"
        );
        assert!(
            !reasons
                .iter()
                .any(|r| matches!(r, AssumeSkipReason::ShadowedParamName(n) if n == "__ret")),
            "the lowerer's own local must not be reported as a shadow: {reasons:?}"
        );
        assert!(pres.is_empty(), "a real ambiguity must still drop the assumption");
    }

    // ---- Trust: the forced parameter restatement — every decline condition ----
    //
    // The restatement is the ONLY thing in this file that can turn a drop into a
    // kept assumption, i.e. the only thing here that can mint a PROVE. Each test
    // below removes exactly one of the conditions in `forced_parameter_alias` and
    // pins that the set drops. Removing a condition without deleting its test is
    // therefore impossible.

    /// **THE REVIEWED FALSE PROOF — the explicit negative this restatement was
    /// once rejected for admitting.** For
    ///
    /// ```ignore
    /// #[allow(non_upper_case_globals)] const n: i32 = -1;
    /// #[requires(n >= 0)] #[ensures(|r: &i32| *r >= 0)]
    /// pub fn f(__trust_v: i32) -> i32 { let n = __trust_v; let x = n; x }
    /// ```
    ///
    /// the clause's `n` resolves in SIGNATURE scope to the module `const`, which
    /// is `-1`; the body's `let n` is a different entity that merely shares the
    /// spelling, and copy-propagation parks its row on the parameter local. The
    /// parameter is spelled `__trust_v`, which
    /// `source_contract_synthetic_name_collision` demotes, so it contributes NO
    /// name to `body.locals` and BOTH visible rows on `_1` are body `let`s. The
    /// first version of this restatement skipped `__trust_v` as "a spelling Trust
    /// mints" (it matched a `__trust_*` PREFIX family), every condition passed,
    /// the FALSE clause was restated as `x >= 0`, and `*ret >= 0` proved for a
    /// function where `f(-5) == -5`.
    ///
    /// Two independent things now stop it, and this test pins the LOCAL one:
    /// `trust_lowered_contract_debug_name` is a CLOSED list of the spellings
    /// `rustc_ast_lowering`'s contract lowering actually mints, and `__trust_v` is
    /// not one — so the row census in condition (7) declines and the set drops.
    /// (The other is module header (III): the compiler refuses contracts outright
    /// for a function with a reserved-family parameter name, so this program does
    /// not even reach the gate. Both must hold; neither is allowed to be the only
    /// one.)
    #[test]
    fn a_demoted_parameter_name_on_the_param_local_declines() {
        for demoted_parameter in ["__trust_v", "__x", "__tmp", "a__b", "__awaitee"] {
            let body = body_with(vec![(0, None), (1, Some("x"))], 1);
            let names =
                multimap(&[(demoted_parameter, &[1]), ("n", &[1]), ("x", &[1]), ("__ret", &[1])]);
            let mut pres = vec![Formula::Ge(Box::new(var("n")), Box::new(int(0)))];
            let reasons = gate_restating(&mut pres, &body, &names, &["n"]);
            assert!(
                !reasons.is_empty(),
                "`{demoted_parameter}` is not a spelling Trust's contract lowering mints, \
                 so it may be the parameter's own name and the restatement must decline: \
                 {reasons:?}"
            );
            assert!(
                pres.is_empty(),
                "a clause that may name a module `const` must never be restated onto a \
                 parameter (`{demoted_parameter}`)"
            );
        }
    }

    #[test]
    fn a_second_row_of_the_body_spelling_on_the_param_local_declines() {
        // THE MULTIPLICITY HAZARD, and the reason condition (6) counts ROWS rather
        // than distinct locals. For
        //   `const n: i32 = -1;`
        //   `#[requires(n >= 0)] fn f(x: i32) -> i32 { let n = x; let x = n; x }`
        // the parameter `x` and the body's second `let x` are TWO rows that both
        // land on `_1`; the collapse still names it `x`, so a distinct-locals test
        // sees `x -> [1]` and would conclude that `n`'s row is the earliest — it is
        // not, the parameter's is, and `n` is a body `let` shadowing the `const`.
        // Restating here would be a false PROVE, so the second row must decline.
        let body = body_with(vec![(0, None), (1, Some("x"))], 1);
        let names = multimap(&[("n", &[1]), ("x", &[1, 1]), ("__ret", &[1])]);
        let mut pres = vec![Formula::Ge(Box::new(var("n")), Box::new(int(0)))];
        let reasons = gate_restating(&mut pres, &body, &names, &["n"]);
        assert!(!reasons.is_empty(), "a doubled body-spelling row must decline: {reasons:?}");
        assert!(pres.is_empty());
    }

    #[test]
    fn a_second_row_of_the_clause_spelling_declines() {
        // The mirror of the case above: two rows named `n`, so `n` is not pinned
        // to a single MIR binding and the "earliest row" step has nothing to bite
        // on. Fail closed.
        let body = body_with(vec![(0, None), (1, Some("x"))], 1);
        let names = multimap(&[("n", &[1, 1]), ("x", &[1])]);
        let mut pres = vec![Formula::Ge(Box::new(var("n")), Box::new(int(0)))];
        let reasons = gate_restating(&mut pres, &body, &names, &["n"]);
        assert!(!reasons.is_empty(), "a doubled clause-spelling row must decline: {reasons:?}");
        assert!(pres.is_empty());
    }

    #[test]
    fn a_second_trust_minted_row_on_the_param_local_declines() {
        // A user parameter spelled `__ret` would sit on `_1` ALONGSIDE the
        // `#[ensures]` lowering's own `__ret`, giving that name two rows there.
        // Module header (III) already makes such a function contract-less, but the
        // census refuses it locally too: an allowlisted spelling is credited for
        // exactly ONE row, so a duplicate cannot be laundered as "ours".
        let body = body_with(vec![(0, None), (1, Some("x"))], 1);
        let names = multimap(&[("n", &[1]), ("x", &[1]), ("__ret", &[1, 1])]);
        let mut pres = vec![Formula::Ge(Box::new(var("n")), Box::new(int(0)))];
        let reasons = gate_restating(&mut pres, &body, &names, &["n"]);
        assert!(!reasons.is_empty(), "a doubled `__ret` row must decline: {reasons:?}");
        assert!(pres.is_empty());
    }

    #[test]
    fn restatement_declines_when_two_parameter_positions_are_unclaimed() {
        // Two parameters, and the clause names NEITHER body spelling: `n` could be
        // position 1 or position 2 and there is no ground to prefer either
        // (condition (4) — `k` unclaimed positions leave `k!` maps). Drop.
        let body = body_with(vec![(0, None), (1, Some("x")), (2, Some("y"))], 2);
        let names = multimap(&[("n", &[1]), ("x", &[1]), ("y", &[2])]);
        let mut pres = vec![Formula::Ge(Box::new(var("n")), Box::new(int(0)))];
        let reasons = gate_restating(&mut pres, &body, &names, &["n", "y"]);
        assert!(!reasons.is_empty(), "an ambiguous position must decline: {reasons:?}");
        assert!(pres.is_empty());
    }

    #[test]
    fn restatement_declines_when_two_clause_spellings_are_unresolved() {
        // Two unbindable clause spellings and one unclaimed position: there is no
        // total map at all (condition (3)). Drop.
        let body = body_with(vec![(0, None), (1, Some("x"))], 1);
        let names = multimap(&[("n", &[1]), ("m", &[1]), ("x", &[1])]);
        let mut pres = vec![Formula::Ge(Box::new(var("n")), Box::new(var("m")))];
        let reasons = gate_restating(&mut pres, &body, &names, &["n"]);
        assert!(!reasons.is_empty(), "two unresolved spellings must decline: {reasons:?}");
        assert!(pres.is_empty());
    }

    #[test]
    fn restatement_declines_when_a_parameter_position_is_unnamed() {
        // Parameter position 2 carries no name, so it could be the position the
        // clause means and there would be no spelling to restate into
        // (condition (1)). This is ALSO the shape a `_` or `ref`-bound parameter
        // takes — the local carries no row of its own, so the "the parameter's row
        // is the earliest row on `_p`" step would have no row to point at. Drop.
        let body = body_with(vec![(0, None), (1, Some("x")), (2, None)], 2);
        let names = multimap(&[("n", &[1]), ("x", &[1])]);
        let mut pres = vec![Formula::Ge(Box::new(var("n")), Box::new(int(0)))];
        let reasons = gate_restating(&mut pres, &body, &names, &["n", "y"]);
        assert!(!reasons.is_empty(), "an unnamed position must decline: {reasons:?}");
        assert!(pres.is_empty());
    }

    #[test]
    fn restatement_declines_for_a_clause_name_with_no_debug_entry() {
        // THE `const`/`static` HAZARD in its bare form, and the reason condition
        // (6) exists. A clause identifier is resolved in the SIGNATURE's scope, so
        // it can be a module item rather than a parameter. `LIMIT` has no
        // `var_debug_info` row anywhere, so nothing corroborates that it denotes
        // parameter 1 — and assuming `LIMIT >= 0` as a fact about `x` would be a
        // FALSE PROVE (`#[requires(LIMIT >= 0)] #[ensures(*ret >= 0)]
        // fn f(n: i32) -> i32 { let x = n; x }` is unprovable: `n` may be
        // negative). Drop.
        let body = body_with(vec![(0, None), (1, Some("x"))], 1);
        let names = multimap(&[("x", &[1])]);
        let mut pres = vec![Formula::Ge(Box::new(var("LIMIT")), Box::new(int(0)))];
        let reasons = gate_restating(&mut pres, &body, &names, &["n"]);
        assert!(
            reasons
                .iter()
                .any(|r| matches!(r, AssumeSkipReason::NonParamVariable(n) if n == "LIMIT")),
            "an uncorroborated clause name must decline: {reasons:?}"
        );
        assert!(pres.is_empty());
    }

    #[test]
    fn restatement_declines_when_the_clause_name_is_not_on_the_target_local() {
        // The clause's `n` is a debug name, but on a NON-parameter local (3): MIR
        // says it is not this parameter, so nothing forces the correspondence
        // (condition (6)). Drop.
        let body = body_with(vec![(0, None), (1, Some("x")), (3, Some("n"))], 1);
        let names = multimap(&[("n", &[3]), ("x", &[1])]);
        let mut pres = vec![Formula::Ge(Box::new(var("n")), Box::new(int(0)))];
        let reasons = gate_restating(&mut pres, &body, &names, &["n"]);
        assert!(
            !reasons.is_empty(),
            "a clause name off the target local must decline: {reasons:?}"
        );
        assert!(pres.is_empty());
    }

    #[test]
    fn restatement_declines_when_the_clause_name_is_multi_local() {
        // `n` resolves to TWO locals in the raw multimap — the copy-propagated
        // shadow shape. Which one the clause means is undetermined, so the
        // corroboration in condition (6) fails. Drop.
        let body = body_with(vec![(0, None), (1, Some("x")), (2, Some("y"))], 2);
        let names = multimap(&[("n", &[1, 2]), ("x", &[1]), ("y", &[2])]);
        let mut pres = vec![Formula::And(vec![
            Formula::Ge(Box::new(var("n")), Box::new(int(0))),
            Formula::Ge(Box::new(var("y")), Box::new(int(0))),
        ])];
        let reasons = gate_restating(&mut pres, &body, &names, &["n", "y"]);
        assert!(!reasons.is_empty(), "a multi-local clause name must decline: {reasons:?}");
        assert!(pres.is_empty());
    }

    #[test]
    fn restatement_declines_across_a_type_boundary() {
        // The clause carries the parser's `Int` sentinel but the target parameter
        // is `bool`: a restatement across the sort boundary would be ill-sorted
        // and could not be what the clause says (condition (5)). Drop.
        let body = body_with_param_ty("b", trust_types::Ty::Bool);
        let names = multimap(&[("flag", &[1]), ("b", &[1])]);
        let mut pres = vec![Formula::Ge(Box::new(var("flag")), Box::new(int(0)))];
        let reasons = gate_restating(&mut pres, &body, &names, &["flag"]);
        assert!(!reasons.is_empty(), "a cross-sort restatement must decline: {reasons:?}");
        assert!(pres.is_empty());
    }

    #[test]
    fn restatement_declines_for_a_reserved_clause_spelling() {
        // A reserved/synthetic spelling is not a source binding this gate may
        // resolve to a parameter — `build_debug_name_map` demotes that whole
        // family, so it names nothing in the extracted body (condition (3)). Drop.
        for reserved in ["__ret", "_0", "old_n", "n_len"] {
            let body = body_with(vec![(0, None), (1, Some("x"))], 1);
            let names = multimap(&[(reserved, &[1]), ("x", &[1])]);
            let mut pres = vec![Formula::Ge(Box::new(var(reserved)), Box::new(int(0)))];
            let reasons = gate_restating(&mut pres, &body, &names, &["n"]);
            assert!(!reasons.is_empty(), "`{reserved}` must decline: {reasons:?}");
            assert!(pres.is_empty(), "`{reserved}` must drop the assumption");
        }
    }

    #[test]
    fn restatement_does_not_bypass_the_vacuity_check() {
        // The restatement runs BEFORE the rest of the gate, so the RESTATED set
        // still faces every existing check. An unsatisfiable predicate would
        // vacuously verify the body, and must still be refused — the restatement
        // may never be a way around the witness discipline.
        let body = body_with(vec![(0, None), (1, Some("x"))], 1);
        let names = multimap(&[("n", &[1]), ("x", &[1]), ("__ret", &[1])]);
        let mut pres = vec![Formula::And(vec![
            Formula::Gt(Box::new(var("n")), Box::new(int(10))),
            Formula::Lt(Box::new(var("n")), Box::new(int(5))),
        ])];
        let reasons = gate_restating(&mut pres, &body, &names, &["n"]);
        assert_eq!(reasons, vec![AssumeSkipReason::NoSatisfiableWitness]);
        assert!(pres.is_empty());
    }

    #[test]
    fn restatement_does_not_bypass_the_type_range_witness_check() {
        // Same discipline, one sort over: the restated `x` inherits the TARGET
        // PARAMETER's declared `u8` range, so an out-of-range hypothesis is still
        // impossible and still refused.
        let body = body_with_param_ty("x", trust_types::Ty::Int { width: 8, signed: false });
        let names = multimap(&[("n", &[1]), ("x", &[1])]);
        let mut pres = vec![Formula::Gt(Box::new(var("n")), Box::new(int(300)))];
        let reasons = gate_restating(&mut pres, &body, &names, &["n"]);
        assert_eq!(reasons, vec![AssumeSkipReason::NoSatisfiableWitness]);
        assert!(pres.is_empty(), "the impossible hypothesis must not reach any body VC");
    }

    #[test]
    fn restatement_declines_for_a_projection_or_deref_clause_term() {
        // Only a parameter's OWN name can be restated. A projection/deref term is
        // a place rendering, not a parameter spelling, and rewriting its head
        // would need prefix-aware surgery this gate does not do (condition (3)).
        for term in ["n*", "n.0", "n[0]", "n.0[1].2"] {
            let body = body_with(vec![(0, None), (1, Some("x"))], 1);
            let names = multimap(&[("n", &[1]), ("x", &[1])]);
            let mut pres = vec![Formula::Ge(Box::new(var(term)), Box::new(int(0)))];
            let reasons = gate_restating(&mut pres, &body, &names, &["n"]);
            assert!(!reasons.is_empty(), "`{term}` must decline: {reasons:?}");
            assert!(pres.is_empty(), "`{term}` must drop the assumption");
        }
    }

    #[test]
    fn restatement_is_inert_when_the_clause_already_speaks_the_body_spelling() {
        // No unbindable spelling ⇒ nothing to restate ⇒ byte-identical to the
        // pre-change behaviour.
        let body = body_with(vec![(0, None), (1, Some("n")), (2, Some("tmp"))], 1);
        let names = multimap(&[("n", &[1]), ("tmp", &[2])]);
        let mut pres = vec![bounded("n", -10, 10)];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(reasons.is_empty(), "{reasons:?}");
        assert_eq!(pres, vec![bounded("n", -10, 10)], "an already-bound clause is untouched");
    }

    #[test]
    fn restatement_resolves_one_position_beside_an_already_named_one() {
        // The productive multi-parameter case: the clause names `m` (which the
        // body still spells `m`) and `n` (which copy-propagation renamed to `x`).
        // Exactly one spelling is unbindable and exactly one position unclaimed,
        // so the map is the unique total one and `n` restates to `x`.
        let body = body_with(vec![(0, None), (1, Some("x")), (2, Some("m"))], 2);
        let names = multimap(&[("n", &[1]), ("x", &[1]), ("m", &[2])]);
        let mut pres = vec![Formula::And(vec![
            Formula::Ge(Box::new(var("n")), Box::new(int(0))),
            Formula::Ge(Box::new(var("m")), Box::new(int(0))),
        ])];
        let reasons = gate_restating(&mut pres, &body, &names, &["n", "m"]);
        assert!(reasons.is_empty(), "the forced restatement must be kept: {reasons:?}");
        assert_eq!(
            pres,
            vec![Formula::And(vec![
                Formula::Ge(Box::new(var("x")), Box::new(int(0))),
                Formula::Ge(Box::new(var("m")), Box::new(int(0))),
            ])],
            "only the unbindable spelling is restated",
        );
    }

    #[test]
    fn restatement_target_is_never_a_spelling_the_clause_already_uses() {
        // Capture guard: the target is drawn from the positions the clause does
        // NOT name, so a rename can never merge two distinct clause variables.
        // Here `x` IS named by the clause, so position 1 is claimed and position 2
        // (`y`) is the only candidate — but `y`'s local does not carry `n`, so the
        // corroboration fails and the set drops rather than restating `n` onto a
        // parameter it does not denote.
        let body = body_with(vec![(0, None), (1, Some("x")), (2, Some("y"))], 2);
        let names = multimap(&[("n", &[1]), ("x", &[1]), ("y", &[2])]);
        let mut pres = vec![Formula::And(vec![
            Formula::Ge(Box::new(var("n")), Box::new(int(0))),
            Formula::Ge(Box::new(var("x")), Box::new(int(0))),
        ])];
        let reasons = gate_restating(&mut pres, &body, &names, &["n", "y"]);
        assert!(!reasons.is_empty(), "a mis-targeted restatement must decline: {reasons:?}");
        assert!(pres.is_empty());
    }

    /// **THE `ref`-PATTERN FALSE PROOF — the reviewed exploit that killed the row
    /// ORDERING argument.** Module header (IV) used to close the identification by
    /// claiming a parameter's own debug row precedes every body binding's row on
    /// `_p`, so the first non-demoted row there had to be the clause spelling's.
    /// That silently presumed `_p` carries a parameter row at all. For
    ///
    /// ```rust,ignore
    /// const n: i32 = 5;                                    // TRUE clause
    /// #[trust::requires(n >= 0)] #[ensures(|r: &i32| *r >= 0)]
    /// fn f(ref q: i32) -> i32 { let n = *q; let x = n; x }  // f(-7) == -7
    /// ```
    ///
    /// `args_and_body` emits an argument's row only under `pat.simple_ident()`,
    /// which is `None` for `ref q`, so `_1` carries NO row of the parameter's own —
    /// while `CopyProp` still rewrites the BODY bindings' rows onto it. The census
    /// then sees exactly two non-demoted names on `_1` (`n` and `x`, both ordinary
    /// `let`s), every multiplicity condition passes, and the TRUE clause about the
    /// module `const` is restated as `x >= 0` — proving a postcondition that
    /// `f(-7)` violates.
    ///
    /// The multiplicity conditions cannot see this: the debug multimap is
    /// `{"q":[2], "n":[1], "x":[1]}`, which is byte-for-byte the shape of the
    /// LEGITIMATE pE case. Only HIR distinguishes them, which is why condition (4b)
    /// asks HIR rather than reasoning about rows.
    #[test]
    fn a_ref_bound_parameter_carrying_no_row_of_its_own_declines() {
        // The exploit's multimap EXACTLY: `q` (the `ref` binding) on its own local
        // 2, and the two body `let`s both collapsed onto the parameter local 1.
        let body = body_with(vec![(0, None), (1, Some("x")), (2, Some("q"))], 1);
        let names = multimap(&[("q", &[2]), ("n", &[1]), ("x", &[1])]);
        let mut pres = vec![Formula::Ge(Box::new(var("n")), Box::new(int(0)))];
        // HIR reports NO simple by-value binding at position 1 — that is what a
        // `ref q` pattern yields, and it is the whole defence.
        let reasons = gate_restating(&mut pres, &body, &names, &[""]);
        assert!(
            !reasons.is_empty(),
            "a `ref`-bound parameter has no row of its own, so `n` may be a module \
             `const` and the restatement must decline: {reasons:?}"
        );
        assert!(
            pres.is_empty(),
            "the module `const`'s clause must never become a fact about the caller's argument"
        );

        // CONTROL: the identical multimap with a plain by-value parameter spelled
        // `n` IS the legitimate pE case and still restates. This is what pins that
        // the test above discriminates on HIR and not on the row census.
        let mut pres = vec![Formula::Ge(Box::new(var("n")), Box::new(int(0)))];
        let reasons = gate_restating(&mut pres, &body, &names, &["n"]);
        assert!(reasons.is_empty(), "the legitimate restatement must survive: {reasons:?}");
        assert_eq!(pres, vec![Formula::Ge(Box::new(var("x")), Box::new(int(0)))]);
    }

    /// The second shape the ordering argument admitted: a plain by-value parameter
    /// whose own name is NOT the clause spelling. `fn f(p: i32) { let n = p; let x
    /// = n; x }` beside `const n: i32 = -1;` puts `n` and `x` on `_1` with one row
    /// each, and the census cannot tell that `p`'s row is the earliest.
    #[test]
    fn a_clause_spelling_that_is_not_this_parameters_hir_name_declines() {
        let body = body_with(vec![(0, None), (1, Some("x"))], 1);
        let names = multimap(&[("n", &[1]), ("x", &[1]), ("__ret", &[1])]);
        let mut pres = vec![Formula::Ge(Box::new(var("n")), Box::new(int(0)))];
        let reasons = gate_restating(&mut pres, &body, &names, &["p"]);
        assert!(
            !reasons.is_empty(),
            "`n` is not parameter 1's source name, so it is a module item: {reasons:?}"
        );
        assert!(pres.is_empty());
    }

    /// An unanswerable parameter-hood question is a DECLINE, never a fallback to
    /// the row census. This is the state the two `trust_verify.rs` proposer lanes
    /// pass, and the state any future caller without HIR would pass.
    #[test]
    fn an_absent_hir_parameter_vector_declines_the_restatement() {
        let body = body_with(vec![(0, None), (1, Some("x"))], 1);
        let names = multimap(&[("n", &[1]), ("x", &[1]), ("__ret", &[1])]);
        let mut pres = vec![Formula::Ge(Box::new(var("n")), Box::new(int(0)))];
        let reasons = super::gate_contract_preconditions(&mut pres, &body, &names, None);
        assert!(!reasons.is_empty(), "no HIR evidence must mean no restatement: {reasons:?}");
        assert!(pres.is_empty());

        // A vector whose length disagrees with MIR's `arg_count` is equally
        // unusable: the positions do not correspond, so indexing it would read the
        // wrong parameter.
        let mut pres = vec![Formula::Ge(Box::new(var("n")), Box::new(int(0)))];
        let reasons = gate_restating(&mut pres, &body, &names, &["n", "extra"]);
        assert!(!reasons.is_empty(), "a length mismatch must decline: {reasons:?}");
        assert!(pres.is_empty());
    }

    #[test]
    fn trust_lowered_contract_names_are_a_closed_subset_of_the_reserved_family() {
        // The census in condition (7) asks "is this row an artifact of TRUST'S OWN
        // CONTRACT LOWERING?". The answer must come from a CLOSED list read off
        // `rustc_ast_lowering/src/contract.rs`, never from a name-shape family: a
        // user can legally write `let __tmp = n;`, and (outside a contract-bearing
        // function) `fn f(__x: i32)`. Reading such a name as an artifact is
        // exactly the reviewed false proof — a parameter spelled `__trust_v` was
        // skipped as "ours" and a module `const`'s false clause was restated onto
        // the parameter. Every accepted spelling must also be in the demoted
        // family, so it can never simultaneously be a live body spelling.
        for minted in ["__ret", "__requires_checker", "__ensures_checker", "__ensures_checker7"] {
            assert!(trust_lowered_contract_debug_name(minted), "`{minted}` is Trust-minted");
            assert!(
                reserved_synthetic_debug_name(minted),
                "`{minted}` must also be in the reserved family (containment)",
            );
        }
        for not_ours in [
            // Spellings a user can bind, including the reviewed exploit's.
            "__trust_v",
            "__trust_constparam_0_N",
            "__old_n",
            "__x",
            "__tmp",
            "__",
            "n",
            "x",
            "old_n",
            // Minted by OTHER lowerings, not the contract lowering.
            "__awaitee",
            "__thread_payload",
            "__thread_rem",
            // Near-misses on the `__ensures_checker` family.
            "__ensures_checker_",
            "__ensures_checkerN",
            "__ret2",
        ] {
            assert!(
                !trust_lowered_contract_debug_name(not_ours),
                "`{not_ours}` is not minted by Trust's CONTRACT lowering and must not read as an \
                 artifact",
            );
        }
    }

    #[test]
    fn plain_user_shadow_on_referenced_name_still_gates() {
        // SOUNDNESS twin, minimal form: an ORDINARY body binding `t` parked on the
        // referenced parameter's local is untouched by the exemption (build #32's
        // copy-propagated-shadow shape with the shadow's own spelling).
        let body = body_with(vec![(0, None), (1, Some("n"))], 1);
        let names = multimap(&[("n", &[1]), ("t", &[1]), ("__ret", &[1])]);
        let mut pres = vec![Formula::Ge(Box::new(var("n")), Box::new(int(0)))];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert_eq!(
            reasons,
            vec![AssumeSkipReason::ShadowedParamName("t".to_string())],
            "exactly the user shadow, and nothing about `__ret`"
        );
        assert!(pres.is_empty());
    }

    #[test]
    fn referenced_synthetic_name_still_gates() {
        // SOUNDNESS twin: the exemption lives ONLY in the alias scan. A predicate
        // that itself REFERENCES a reserved spelling is still rejected by the first
        // loop — `__ret` cannot be in `param_names` (demotion left that local
        // unnamed under this spelling), so it is not caller-bound.
        for reserved in ["__ret", "_0", "old_n"] {
            let body = body_with(vec![(0, None), (1, Some("n"))], 1);
            // The reserved name aliases the param local: the sharper
            // ShadowedParamName classification, and it must NOT be exempted.
            let names = multimap(&[("n", &[1]), (reserved, &[1])]);
            let mut pres = vec![Formula::Ge(Box::new(var(reserved)), Box::new(int(0)))];
            let reasons = gate_contract_preconditions(&mut pres, &body, &names);
            assert!(
                reasons
                    .iter()
                    .any(|r| matches!(r, AssumeSkipReason::ShadowedParamName(n) if n == reserved)),
                "a referenced reserved name must still gate: {reserved} {reasons:?}"
            );
            assert!(pres.is_empty());

            // And with no debug entry at all it is simply not a parameter.
            let names = multimap(&[("n", &[1])]);
            let mut pres = vec![Formula::Ge(Box::new(var(reserved)), Box::new(int(0)))];
            let reasons = gate_contract_preconditions(&mut pres, &body, &names);
            assert!(
                reasons
                    .iter()
                    .any(|r| matches!(r, AssumeSkipReason::NonParamVariable(n) if n == reserved)),
                "an unbound reserved name must still gate: {reserved} {reasons:?}"
            );
            assert!(pres.is_empty());
        }
    }

    #[test]
    fn synthetic_alias_on_a_second_param_still_gates_a_multi_local_name() {
        // SOUNDNESS twin: the exemption only ever skips the ALIAS scan. It cannot
        // rescue a referenced name that is itself ambiguous — `n` on two locals is
        // still caught by the first loop, whatever else sits on those locals.
        let body = body_with(vec![(0, None), (1, Some("n")), (2, Some("n"))], 2);
        let names = multimap(&[("n", &[1, 2]), ("__ret", &[1])]);
        let mut pres = vec![Formula::Ge(Box::new(var("n")), Box::new(int(0)))];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert!(
            reasons.iter().any(|r| matches!(r, AssumeSkipReason::ShadowedParamName(n) if n == "n")),
            "a referenced name on two locals must still gate: {reasons:?}"
        );
        assert!(pres.is_empty());
    }

    #[test]
    fn unsat_product_bound_dropped() {
        // SOUNDNESS twin: `x * x <= -1.0` — a real square is never negative; the
        // Mul arm must not fabricate a witness (NaN/rounding cannot help it).
        let body = f64_params_body(&["x"]);
        let names = multimap(&[("x", &[1])]);
        let mut pres = vec![Formula::Le(
            Box::new(Formula::Mul(Box::new(float_var("x")), Box::new(float_var("x")))),
            Box::new(fp(-1.0)),
        )];
        let reasons = gate_contract_preconditions(&mut pres, &body, &names);
        assert_eq!(reasons, vec![AssumeSkipReason::NoSatisfiableWitness]);
        assert!(pres.is_empty());
    }
}
