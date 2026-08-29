// The DROPPED-ENTRY-HYPOTHESIS tripwire: what a postcondition VC is allowed to
// mean when the function's authored `requires` never became a body assumption.
//
// `trust-mir-extract`'s `gate_contract_preconditions` drops the WHOLE
// contract-derived precondition set on any gate failure — a body local
// shadowing a parameter debug name, a predicate outside the assumable fragment,
// a predicate with no ground witness. Dropping is the right call there: assuming
// a fact that binds the wrong variable is a false-PROVE, and the gate can only
// weaken PROVE toward FAIL/UNKNOWN.
//
// But the postcondition lane then assembles its VC over an entry state that
// NOTHING constrains except the always-true synthetic facts (integer/char/
// discriminant ranges, appended AFTER the gate). `¬post` becomes satisfiable at
// an entry state the author's `requires` forbids, the row is reported Failed,
// and the full verifier mints `verified_counterexample = true` against CORRECT
// code. That counterexample is not a counterexample to the function's contract
// at all — it is a counterexample to a DIFFERENT function, the one with no
// precondition.
//
// This module supplies the two questions the tripwire in `contract_vcs.rs` asks:
//
//   1. `dropped_requires_clauses` — did the gate drop this function's authored
//      `requires`? (Authored Requires exist, and NONE of them is carried in
//      `func.preconditions`. Non-emptiness of `func.preconditions` proves
//      nothing: the synthetic range facts are appended after the gate.)
//
//   2. `only_excluded_counterexamples` — of the counterexamples this assembled
//      VC admits, is EVERY one of them an entry state the dropped `requires`
//      excludes?
//
// Question 2 is decided by EXHIBITING models, never by assuming their absence,
// and that asymmetry is the whole soundness argument:
//
//   * The tripwire fires only when a concrete model of the assembled VC has
//     been FOUND and evaluated to `true`. A formula with a model is not
//     provable, so firing can never destroy a proof — the `ensures(*ret >= n)`
//     control over `{ n }` (dropped `requires`, 3 proved) has no model at all,
//     the search finds none, and the row is emitted unchanged.
//   * The tripwire declines whenever a model that ALSO satisfies the dropped
//     `requires` is found, so a genuine bug still refutes: `requires(n >= 0)`
//     with `ensures(*ret >= 5)` over `{ n }` admits `n == 0`, which satisfies
//     the precondition, so that row stays refutable.
//   * Every budget/fragment failure declines to fire. The tripwire is therefore
//     INCOMPLETE by construction (see the caps below) and the false refutation
//     survives in the cases it cannot reach — an honest gap, not a claim.
//
// WHY IT IS LEGITIMATE TO CONSULT A PREDICATE THE GATE REFUSED TO ASSUME. The
// gate refuses to make the `requires` a HYPOTHESIS, because a predicate whose
// debug name binds the wrong local would discharge obligations about an
// unconstrained value — a false PROVE. Nothing here is assumed: the dropped
// clause never enters the emitted formula, and no row is ever discharged by it.
// It is used only to REFUSE to emit a refutable row, and the refusal lands as a
// visible, non-provable `UnsupportedMir` row (never a silent drop — that would
// leave the function with fewer obligations than its source declares). So the
// worst consequence of the dropped clause meaning something other than what the
// author intended is that a row we could have refuted becomes an honest
// coverage gap. The direction of every mistake this module can make is toward
// claiming LESS.
//
// WHY A RELEVANCE TEST ON SPELLINGS IS NOT ENOUGH, AND WHAT REPLACES IT.
// The clause and the VC are written in two different namespaces. The clause is
// written in the SOURCE's namespace — the parameter names the author typed. The
// VC is written in the BODY's namespace — `build_debug_name_map`'s last-write-
// wins collapse of `var_debug_info`. Those agree in the easy case and diverge in
// exactly the case that arms this tripwire: for
//
//   #[requires(n >= 0)] #[ensures(|r| *r >= 0)] fn f(n: i32) -> i32 { let x = n; x }
//
// MIR copy-propagation makes the body's `x` an alias of the parameter local, both
// `n` and `x` land on local 1, and the collapse names local 1 `x`. The gate then
// drops the clause CORRECTLY (the binding is ambiguous, and assuming `n >= 0`
// would constrain a variable the VC never binds — a false-PROVE risk). But the
// assembled row reads `x`/`_0`, the dropped clause reads `n`, the spelling-only
// relevance test finds no overlap, and the tripwire declined — leaving the
// measured `1 proved, 2 FAILED` with `verified_counterexample = true` against
// correct code. `n` and `x` are one entity: PARAMETER POSITION 1.
//
// [`forced_parameter_alias`] recovers that correspondence POSITIONALLY, and
// refuses whenever it is not FORCED. MIR guarantees locals `1..=arg_count` are
// the parameters in declaration order, so a parameter position has exactly one
// body spelling; the search is for the one clause spelling that has none. It
// fires only when
//
//   * every parameter position `1..=arg_count` carries a plain source-binding
//     name (an unnamed position could be the one the clause means, and then the
//     correspondence is not determined);
//   * the clause set has EXACTLY ONE free variable the body namespace cannot
//     bind — two would leave `k!` orderings and no way to pick;
//   * EXACTLY ONE parameter position is not already named by the clause in the
//     body's own spelling — so the map from that one name to that one position
//     is the unique total map, not a preference among candidates;
//   * that name is a plain identifier in no reserved namespace
//     (`source_contract_synthetic_name_collision`: `result`, `_0`, `_<digits>`,
//     the predicate vocabulary, the `__` metadata family, and `old_*`) — the
//     model/projection spellings are NOT parameters;
//   * the sort the clause gives it is unambiguous and the parameter's declared
//     type admits that sort (`Int` sort ↔ integer parameter, `Bool` ↔ `bool`);
//   * no clause carries a quantifier, so the syntactic rename cannot capture.
//
// Anything else returns `None` and the clause is used unrenamed, i.e. exactly as
// before. This is "resolve by position, decline when ambiguous" — NOT "the clause
// mentions a non-parameter name, so guess it is the parameter".
//
// THE RENAMED CLAUSE CAN NEVER BECOME AN ASSUMPTION, BY CONSTRUCTION. That is the
// hazard the gate's drop exists to prevent, and it is foreclosed structurally
// rather than by discipline:
//
//   * [`forced_parameter_alias`] returns a pair of NAMES. It cannot construct a
//     `Formula`, so there is no renamed clause for a caller to get hold of.
//   * The only renamed `Formula` in this crate is built inside
//     [`only_excluded_counterexamples`], in a local binding, and that function
//     returns `bool`. Nothing it builds outlives the call.
//   * Its one caller uses that `bool` to decide whether to push a
//     `spec_unverifiable_vc` — a NON-PROVABLE row. No emitted formula, on any
//     path, contains a renamed clause.
//
// So the renaming is a relevance/evaluation aid for REFUSING, and the direction
// of every mistake it can make stays "claim LESS": a wrong correspondence can
// only cost a refutation we could have reported, never mint a proof.
//
// The evaluator below is deliberately a total function over a small declared
// fragment (`Int`/`Bool` variables, the boolean connectives, the order
// relations, `+`/`-`/`*`/unary `-`, and `Ite`), with a catch-all that answers
// "outside the fragment". Its arithmetic is CHECKED, so an evaluation that
// would overflow `i128` answers `None` rather than wrapping — a wrapped value
// is not the SMT `Int` value and could exhibit a model that does not exist.
// Everything else — bitvectors, floats, arrays, uninterpreted predicates,
// quantifiers, `/`, `%` — is outside the fragment, so no model is ever claimed
// under semantics this module does not implement exactly.

use super::*;

/// At most this many distinct free variables, or the search declines.
const MAX_WITNESS_VARS: usize = 6;
/// At most this many candidate values per variable, or the search declines.
const MAX_WITNESS_CANDIDATES: usize = 32;
/// At most this many total assignments, or the search declines.
const MAX_WITNESS_ASSIGNMENTS: usize = 4096;

/// The authored `requires` clauses of `func` that the assumption gate DROPPED.
///
/// Empty when the function declares none, when none of them parses, or when at
/// least ONE authored clause is still carried in `func.preconditions` — the gate
/// drops the set collectively, so a single surviving clause means the set
/// survived.
///
/// `func.preconditions` is NOT a source-clause provenance carrier: besides
/// authored Requires it holds the always-true synthetic facts appended after the
/// gate (`enum_discriminant_range_preconditions`, `char_range_preconditions`,
/// `integer_param_range_preconditions`). "Non-empty" therefore does not mean the
/// authored predicate survived, which is why presence is decided by MATCHING
/// each authored clause against the carried facts.
///
/// The match is [`parsed_clause_matches_typed`], the same relation the `Ensures`
/// lane uses to recognize its own typed lowering: everything but a variable
/// leaf's sort must agree exactly, and the parser's `Sort::Int` sentinel is
/// allowed to meet the typed sort. A clause that survived but that the matcher
/// fails to recognize is self-correcting rather than dangerous: the surviving
/// fact is then a conjunct of the assembled VC, so every model the search finds
/// already satisfies it and [`only_excluded_counterexamples`] declines.
pub(super) fn dropped_requires_clauses(func: &VerifiableFunction) -> Vec<Formula> {
    let mut authored: Vec<Formula> = Vec::new();
    let mut push_parsed = |text: &str| {
        let body = text.strip_prefix(contracts::LOWERED_CONTRACT_PREFIX).unwrap_or(text);
        if let Some(parsed) = trust_types::parse_spec_expr(body) {
            authored.push(parsed);
        }
    };
    for contract in &func.contracts {
        if matches!(contract.kind, ContractKind::Requires) {
            push_parsed(&contract.body);
        }
    }
    // The compatibility `FunctionSpec` lane spells the same clauses as text and
    // has no assumed-fact carrier of its own, so a `requires` that reaches only
    // this lane is likewise never an entry hypothesis.
    for text in &func.spec.requires {
        push_parsed(text);
    }
    if authored.is_empty() {
        return Vec::new();
    }
    let carried = |clause: &Formula| {
        func.preconditions.iter().any(|pre| parsed_clause_matches_typed(clause, pre))
    };
    if authored.iter().any(carried) {
        return Vec::new();
    }
    let mut seen: FxHashSet<String> = FxHashSet::default();
    authored.retain(|clause| seen.insert(format!("{clause:?}")));
    authored
}

/// Whether every counterexample this search can EXHIBIT for `vc` is an entry
/// state that `dropped` excludes — i.e. the refutation of this row would be a
/// statement about a function that has no precondition, not about this one.
///
/// Returns `false` (decline) whenever:
///   * no model of `vc` was found at all — including because `vc` has none,
///     which is exactly the provable row the tripwire must never touch;
///   * a model of `vc` that ALSO satisfies every dropped clause was found — the
///     refutation is genuine and must be reported;
///   * `dropped` shares no variable with `vc` — an irrelevant hypothesis cannot
///     be what makes the row refutable;
///   * anything is outside the declared fragment or over budget.
///
/// The clause is first restated in the BODY's own spelling when — and only when
/// — [`forced_parameter_alias`] finds the correspondence FORCED; see the module
/// header for why that restatement can never become an assumption. The renamed
/// clauses live in the `restated` local below and this function returns `bool`,
/// so no caller can obtain them.
///
/// Note that the restatement cannot affect whether a model of `vc` exists: it
/// rewrites only `dropped`, and `vc` is passed through untouched. The
/// "a provable row has no model, so firing can never destroy a proof" argument
/// is therefore completely independent of the correspondence being right.
pub(super) fn only_excluded_counterexamples(
    func: &VerifiableFunction,
    vc: &Formula,
    dropped: &[Formula],
) -> bool {
    if dropped.is_empty() {
        return false;
    }
    // Restate the dropped clauses in the body's namespace when the parameter
    // correspondence is forced. `None` (not forced, or nothing to resolve)
    // leaves them exactly as the gate saw them.
    let restated: Option<Vec<Formula>> =
        forced_parameter_alias(func, dropped).map(|(source, body_spelling)| {
            dropped.iter().map(|clause| clause.rename_var(&source, &body_spelling)).collect()
        });
    let dropped: &[Formula] = restated.as_deref().unwrap_or(dropped);

    // Relevance: the dropped hypothesis must speak about a name this row reads.
    let vc_vars = vc.free_variables();
    if !dropped.iter().any(|clause| clause.free_variables().iter().any(|v| vc_vars.contains(v))) {
        return false;
    }

    let Some(sorts) = fragment_var_sorts(vc, dropped) else {
        return false;
    };
    let mut names: Vec<&String> = sorts.keys().collect();
    names.sort();
    if names.len() > MAX_WITNESS_VARS {
        return false;
    }

    let Some(ints) = candidate_ints(vc, dropped) else {
        return false;
    };
    let domains: Vec<Vec<Value>> = names
        .iter()
        .map(|name| match sorts[*name] {
            Sort::Bool => vec![Value::Bool(false), Value::Bool(true)],
            _ => ints.iter().copied().map(Value::Int).collect(),
        })
        .collect();
    if domains.iter().any(Vec::is_empty) {
        return false;
    }
    let total = domains
        .iter()
        .try_fold(1usize, |product, values| product.checked_mul(values.len()))
        .unwrap_or(usize::MAX);
    if total > MAX_WITNESS_ASSIGNMENTS {
        return false;
    }

    let mut found_excluded_counterexample = false;
    let mut indices = vec![0usize; names.len()];
    loop {
        let env: FxHashMap<&str, Value> = names
            .iter()
            .zip(indices.iter())
            .enumerate()
            .map(|(position, (name, &index))| (name.as_str(), domains[position][index]))
            .collect();
        if eval_bool(vc, &env) == Some(true) {
            // A model of the row: the row is REFUTABLE, so it is not a proof we
            // could be discarding. Whether the refutation is honest is decided
            // by the dropped hypothesis.
            //
            // THREE OUTCOMES, and the third is why this is not a two-way test.
            // `eval_bool` is PARTIAL — `None` means "outside the interpreted
            // fragment", NOT "false". Folding `None` into the excluded branch
            // would suppress genuine counterexamples wholesale, because
            // `fragment_var_sorts` screens variable SORTS only, while
            // `gate_contract_preconditions`'s own `in_assumable_fragment`
            // rejects `Div`/`Rem`/`Ite`/`Forall`/`Exists`/`Pred` and all
            // Bv/Fp arithmetic. Those are exactly the clauses that are ALWAYS
            // dropped — i.e. the ones that arm this tripwire — and exactly the
            // ones `eval_bool` cannot interpret, so the two sets nearly
            // coincide. `#[requires(n % 2 == 0)] #[ensures(*ret >= 5)]` over
            // `{ n }` is a REAL bug (`n = 0` satisfies the precondition and
            // violates the postcondition) that a `None`-as-excluded reading
            // would quietly turn into an unsupported row.
            let mut classified_excluded = false;
            for clause in dropped {
                match eval_bool(clause, &env) {
                    // Admitted by the hypothesis: an honest counterexample.
                    Some(true) => {}
                    // Excluded by the hypothesis: keep looking.
                    Some(false) => classified_excluded = true,
                    // Cannot classify this model at all. Decline rather than
                    // guess in either direction — declining leaves the
                    // refutable row exactly as it is today.
                    None => return false,
                }
            }
            if !classified_excluded {
                return false;
            }
            found_excluded_counterexample = true;
        }
        let mut position = 0;
        loop {
            if position == indices.len() {
                return found_excluded_counterexample;
            }
            indices[position] += 1;
            if indices[position] < domains[position].len() {
                break;
            }
            indices[position] = 0;
            position += 1;
        }
    }
}

/// The one `(source spelling, body spelling)` pair that restates `dropped` in
/// the namespace `func`'s VCs are assembled in — or `None` when there is nothing
/// to restate and, crucially, whenever the correspondence is not FORCED.
///
/// This returns NAMES, never a `Formula`, and that is deliberate: a renamed
/// clause is only ever built inside [`only_excluded_counterexamples`], which
/// returns `bool`. See the module header — the gate dropped this clause because
/// its binding was ambiguous, and no restatement of it may ever reach an emitted
/// formula. It is `pub(super)` only so the decline conditions below can be
/// pinned one by one by the tests; a name pair is not a hypothesis, so widening
/// its visibility cannot widen what can be assumed.
///
/// The correspondence is PARAMETER POSITION. MIR guarantees locals
/// `1..=arg_count` are the function's parameters in declaration order, so each
/// position has exactly one body spelling; the clause is written in the source's
/// spelling, and copy-propagation plus the last-write-wins debug-name collapse
/// is what makes the two differ. Every one of the checks below is a way for the
/// map to fail to be UNIQUELY DETERMINED, and each of them declines:
///
///   * a parameter position with no name — it could be the position the clause
///     means, and there would be no spelling to restate into;
///   * more than one clause variable outside the body namespace, or more than
///     one parameter position the clause does not already name in the body's own
///     spelling — with `k` of either there are `k!` maps and no ground to prefer
///     one; only `k == 1` on both sides is a single total map;
///   * a name in a reserved/synthetic namespace, or one that is not a plain
///     identifier (`a*`, `self.0`, `a[_i]`, `x#3`) — those are model terms and
///     projections, not parameters;
///   * a sort the clause does not use consistently, or one the parameter's
///     declared type does not admit;
///   * a quantifier anywhere in the clause set — `Formula::rename_var` is a
///     SYNTACTIC rename that does not respect binders, so a binder could capture.
///
/// The target position is chosen from the parameters the clause does NOT already
/// name, so the rename can never collide with a spelling already in the clause.
pub(super) fn forced_parameter_alias(
    func: &VerifiableFunction,
    dropped: &[Formula],
) -> Option<(String, String)> {
    let body = &func.body;
    if body.arg_count == 0 {
        return None;
    }

    // The parameter list in DECLARATION ORDER, with the body spelling and the
    // declared type of each position. A position missing from `locals`, unnamed,
    // or carrying a non-identifier spelling makes the whole correspondence
    // undetermined, so all three decline for the WHOLE function rather than for
    // that position alone.
    let mut parameters: Vec<(&str, &Ty)> = Vec::with_capacity(body.arg_count);
    for index in 1..=body.arg_count {
        let decl = body.locals.iter().find(|local| local.index == index)?;
        let name = decl.name.as_deref()?;
        if !plain_source_binding(name) {
            return None;
        }
        parameters.push((name, &decl.ty));
    }

    // Every spelling the body namespace can bind — parameters AND body locals.
    // A clause variable that IS a body local is already in this namespace and is
    // not an unresolved parameter alias, whatever it denotes.
    let body_names: FxHashSet<&str> =
        body.locals.iter().filter_map(|local| local.name.as_deref()).collect();

    let mut clause_vars: FxHashSet<String> = FxHashSet::default();
    for clause in dropped {
        if formula_binds_a_variable(clause) {
            return None;
        }
        clause_vars.extend(clause.free_variables());
    }

    // Exactly one clause spelling the body namespace cannot bind.
    let mut unresolved = clause_vars.iter().filter(|name| !body_names.contains(name.as_str()));
    let source = unresolved.next()?;
    if unresolved.next().is_some() {
        return None;
    }
    if !plain_source_binding(source)
        || trust_types::source_contract_synthetic_name_collision(source).is_some()
    {
        return None;
    }

    // Exactly one parameter position the clause does not already name.
    let mut unclaimed = parameters.iter().copied().filter(|(name, _)| !clause_vars.contains(*name));
    let (body_spelling, declared_ty) = unclaimed.next()?;
    if unclaimed.next().is_some() {
        return None;
    }

    // The sort must be unambiguous in the clause AND admitted by the parameter's
    // declared type: a clause reading an `Int` cannot be a restatement of a
    // `&[T]`/`f64`/`bool` parameter. `fragment_var_sorts` re-checks agreement
    // against the VC afterwards, so this is the first of two sort gates.
    let sort = sole_var_sort(dropped, source)?;
    if !parameter_ty_admits_sort(declared_ty, &sort) {
        return None;
    }

    Some((source.clone(), body_spelling.to_string()))
}

/// A plain source binding spelling: identifier characters only. Rejects every
/// place-rendering shape `place_to_var_name` can produce — the deref suffix
/// `a*`, field/index projections `self.0` / `a[_i]`, and the `x#3` statement-
/// version token — none of which is a parameter's own name.
fn plain_source_binding(name: &str) -> bool {
    let mut chars = name.chars();
    chars.next().is_some_and(|first| first.is_ascii_alphabetic() || first == '_')
        && chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
}

/// Whether any node of `formula` binds a variable. `Formula::rename_var` is a
/// syntactic rename with no binder awareness, so a quantified clause is refused
/// outright rather than risking capture. (Such clauses are outside the gate's
/// assumable fragment anyway, and `eval` answers `None` on them, so this costs
/// no reach.)
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
/// none or more than one — an ambiguity this module refuses to resolve.
fn sole_var_sort(formulas: &[Formula], name: &str) -> Option<Sort> {
    let mut sort: Option<Sort> = None;
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
/// denotes. Deliberately narrow: only the two sorts this module's evaluator
/// implements, against the types that actually carry them. `Ty::Char` is NOT an
/// integer parameter for this purpose and every aggregate/reference/float type
/// declines, so a restatement is never proposed across a type boundary.
fn parameter_ty_admits_sort(ty: &Ty, sort: &Sort) -> bool {
    match (ty, sort) {
        (Ty::Int { .. } | Ty::PtrSizedInt { .. }, Sort::Int) => true,
        (Ty::Bool, Sort::Bool) => true,
        _ => false,
    }
}

/// A ground value in the declared fragment.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Value {
    Int(i128),
    Bool(bool),
}

/// Every free variable of `vc` and `dropped` with its sort, or `None` when a
/// variable is outside the fragment (`BitVec`, `Float`, `Array`, datatype, …) or
/// carries two different sorts across the formulas — an ambiguity this module
/// refuses to resolve by guessing.
fn fragment_var_sorts(vc: &Formula, dropped: &[Formula]) -> Option<FxHashMap<String, Sort>> {
    let mut sorts: FxHashMap<String, Sort> = FxHashMap::default();
    let mut ok = true;
    let mut collect = |formula: &Formula| {
        formula.visit(&mut |node| {
            let (name, sort) = match node {
                Formula::Var(name, sort) => (name.clone(), sort),
                Formula::SymVar(symbol, sort) => (symbol.as_str().to_string(), sort),
                _ => return,
            };
            if !matches!(sort, Sort::Int | Sort::Bool) {
                ok = false;
                return;
            }
            match sorts.get(&name) {
                Some(existing) if existing != sort => ok = false,
                Some(_) => {}
                None => {
                    sorts.insert(name, sort.clone());
                }
            }
        });
    };
    collect(vc);
    for clause in dropped {
        collect(clause);
    }
    ok.then_some(sorts)
}

/// The integer candidate grid: every integer literal appearing in the formulas,
/// each literal's immediate neighbours, and `{-1, 0, 1}`. `None` when the grid
/// would exceed [`MAX_WITNESS_CANDIDATES`] — truncating it would silently drop
/// the very value a genuine counterexample needs, which would turn an honest
/// refutation into a fail-closed row.
fn candidate_ints(vc: &Formula, dropped: &[Formula]) -> Option<Vec<i128>> {
    let mut literals: Vec<i128> = vec![-1, 0, 1];
    let mut ok = true;
    let mut collect = |formula: &Formula| {
        formula.visit(&mut |node| match node {
            Formula::Int(value) => literals.push(*value),
            Formula::UInt(value) => match i128::try_from(*value) {
                Ok(value) => literals.push(value),
                Err(_) => ok = false,
            },
            _ => {}
        });
    };
    collect(vc);
    for clause in dropped {
        collect(clause);
    }
    if !ok {
        return None;
    }
    let mut grid: Vec<i128> = Vec::with_capacity(literals.len() * 3);
    for value in literals {
        grid.push(value);
        grid.extend(value.checked_add(1));
        grid.extend(value.checked_sub(1));
    }
    grid.sort_unstable();
    grid.dedup();
    (grid.len() <= MAX_WITNESS_CANDIDATES).then_some(grid)
}

fn eval_bool(formula: &Formula, env: &FxHashMap<&str, Value>) -> Option<bool> {
    match eval(formula, env)? {
        Value::Bool(value) => Some(value),
        Value::Int(_) => None,
    }
}

fn eval_int(formula: &Formula, env: &FxHashMap<&str, Value>) -> Option<i128> {
    match eval(formula, env)? {
        Value::Int(value) => Some(value),
        Value::Bool(_) => None,
    }
}

/// Ground evaluation over the declared fragment. TOTAL by construction: the
/// catch-all answers `None` ("outside the fragment"), so a `Formula` variant
/// added later can never be evaluated under guessed semantics.
fn eval(formula: &Formula, env: &FxHashMap<&str, Value>) -> Option<Value> {
    let compare = |lhs: &Formula, rhs: &Formula, op: fn(i128, i128) -> bool| {
        Some(Value::Bool(op(eval_int(lhs, env)?, eval_int(rhs, env)?)))
    };
    let arith = |lhs: &Formula, rhs: &Formula, op: fn(i128, i128) -> Option<i128>| {
        Some(Value::Int(op(eval_int(lhs, env)?, eval_int(rhs, env)?)?))
    };
    match formula {
        Formula::Bool(value) => Some(Value::Bool(*value)),
        Formula::Int(value) => Some(Value::Int(*value)),
        Formula::UInt(value) => i128::try_from(*value).ok().map(Value::Int),
        Formula::Var(name, _) => env.get(name.as_str()).copied(),
        Formula::SymVar(symbol, _) => env.get(symbol.as_str()).copied(),
        Formula::Not(inner) => Some(Value::Bool(!eval_bool(inner, env)?)),
        Formula::And(conjuncts) => {
            let mut all = true;
            for conjunct in conjuncts {
                all &= eval_bool(conjunct, env)?;
            }
            Some(Value::Bool(all))
        }
        Formula::Or(disjuncts) => {
            let mut any = false;
            for disjunct in disjuncts {
                any |= eval_bool(disjunct, env)?;
            }
            Some(Value::Bool(any))
        }
        Formula::Implies(lhs, rhs) => {
            Some(Value::Bool(!eval_bool(lhs, env)? || eval_bool(rhs, env)?))
        }
        // Equality is sort-uniform: `Int == Int` or `Bool == Bool`. A mixed pair
        // is ill-sorted, not `false`.
        Formula::Eq(lhs, rhs) => match (eval(lhs, env)?, eval(rhs, env)?) {
            (Value::Int(l), Value::Int(r)) => Some(Value::Bool(l == r)),
            (Value::Bool(l), Value::Bool(r)) => Some(Value::Bool(l == r)),
            _ => None,
        },
        Formula::Lt(lhs, rhs) => compare(lhs, rhs, |l, r| l < r),
        Formula::Le(lhs, rhs) => compare(lhs, rhs, |l, r| l <= r),
        Formula::Gt(lhs, rhs) => compare(lhs, rhs, |l, r| l > r),
        Formula::Ge(lhs, rhs) => compare(lhs, rhs, |l, r| l >= r),
        Formula::Add(lhs, rhs) => arith(lhs, rhs, i128::checked_add),
        Formula::Sub(lhs, rhs) => arith(lhs, rhs, i128::checked_sub),
        Formula::Mul(lhs, rhs) => arith(lhs, rhs, i128::checked_mul),
        Formula::Neg(inner) => Some(Value::Int(eval_int(inner, env)?.checked_neg()?)),
        Formula::Ite(condition, then_branch, else_branch) => {
            if eval_bool(condition, env)? {
                eval(then_branch, env)
            } else {
                eval(else_branch, env)
            }
        }
        // Outside the declared fragment: bitvectors, floats, arrays,
        // uninterpreted predicates, quantifiers, `/` and `%` (SMT-LIB `Int`
        // division is Euclidean, not Rust's truncating division — evaluating it
        // as either would be a guess), and any variant added later.
        _ => None,
    }
}
