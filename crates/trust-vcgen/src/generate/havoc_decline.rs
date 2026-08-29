// Reclassification of safety obligations whose REFUTATION is an artifact of an
// unmodelled callee return, not a property of the program.
//
// A `Terminator::Call` whose callee has no model writes its destination with
// nothing constraining it: the destination is a free variable of the violation
// formula. The solver then answers SAT by *choosing* that value, and the row is
// reported REFUTED with a "counterexample" that no execution can produce — the
// census recorded `max(x, 1) = 0` alongside `x = 0`. An unmodelled callee means
// "I do not know", which is UNKNOWN; reporting it as a counterexample is the
// verifier accusing correct code.
//
// This module reclassifies exactly that shape to `VcKind::UnsupportedMir`, which
// `discharge_body_vcs` preclassifies to `Unknown` and never dispatches. It adds
// NO fact and states NOTHING about any callee's return value: the only thing it
// can do to a row is turn it into an Unknown, so it can never produce a proof.
//
// The demotion goes through `unsupported::demote_to_unsupported_mir` so the
// declined row carries the SAME fail-closed (satisfiable) violation formula as
// every other `UnsupportedMir` emitter. That is not cosmetic: `UnsupportedMir`
// has `proof_level() == L0Safety`, so any consumer that selects obligations by
// proof level rather than by kind admits the row and then reads only its
// formula, and an UNSAT one means "no violation". `trust_clean::whole_program`'s
// kernel-discharge gates now refuse a declined row by KIND first, so there the
// polarity is a second defence; for a direct-solver caller it is the only one.
//
// The decline fires only when all four conditions hold, and each one exists to
// stop a different way of losing a decision the verifier can actually make:
//
//   1. the variable's ONLY value source in this body is a `Call` destination
//      (MIR-derived — a parameter or an `Assign`-defined local is never a
//      candidate, which is what keeps an all-local real bug refutable);
//   2. it survives substitution of the hypothesis definitions into the recorded
//      raw violation, i.e. the obligation genuinely depends on it;
//   3. NOTHING in the hypotheses pins it (see `conjunct_restricts`), so a
//      modelled callee or a program guard keeps its row exactly as it is today.
//      The two models measured to reach this seam on the fixture corpus are the
//      `leading_zeros` intrinsic's `0..=32` pin (`hv_div_leading_zeros` keeps its
//      refutation, `hv_idx_leading_zeros` keeps its proof) and the
//      `mem::size_of`/`align_of` layout facts (the four `hv_{div,idx}_*_of`
//      rows prove). NB the `Ord::min`/`max` model is NOT one of them: the
//      compiler emits `core::cmp::max::<u32>` for a monomorphized free-function
//      call and `call_facts::ord_method` does not recognize that spelling — see
//      `ord_method_spelling_tests::turbofish_free_function_spelling_is_not_recognized_today`;
//   4. moving that ONE variable across its declared type range flips the
//      obligation between true and false (see `havoc_flips_obligation`), with
//      every other variable eliminated. That is the operational meaning of "the
//      answer depends on a value I do not know". An obligation that is false at
//      every probed value (`arr[unmodelled() % 4]`) keeps its row and still
//      proves; one that is TRUE at every probed value is a violation whatever
//      the callee returns, and also keeps its row.

use super::*;

/// Cap on the number of top-level conjuncts a formula may have before the pass
/// declines to analyse it. The pinning scan is quadratic in this count (each
/// conjunct is tested against every other for the dead-variable side condition),
/// and giving up means "leave the row exactly as it is", so the cap can only
/// cost precision.
const MAX_CONJUNCTS: usize = 512;

/// Cap on substitution rounds when folding hypothesis definitions into the raw
/// violation. Definitions form a DAG in practice (MIR temps), so a handful of
/// rounds reaches the fixpoint; the cap bounds the pathological case.
const MAX_SUBST_ROUNDS: usize = 8;

/// Node cap on the folded obligation. Substituting a definition replaces a leaf
/// by a whole term, so a chain of them can grow the formula multiplicatively;
/// past this the fold is abandoned and the row keeps its current classification.
const MAX_FOLDED_NODES: usize = 4096;

/// Node count of `f`.
fn formula_node_count(f: &Formula) -> usize {
    1 + f.children().iter().map(|c| formula_node_count(c)).sum::<usize>()
}

/// The base var name of a formula variable — the `#`-version suffix stripped, so
/// `_2#s0_t` and `_2` compare equal. Mirrors the base-name convention used by
/// `conjoin_local_type_ranges_excluding` and `block_def_subject`.
fn var_full_and_base(f: &Formula) -> Option<(String, String)> {
    let name = match f {
        Formula::Var(name, _) => name.clone(),
        Formula::SymVar(sym, _) => sym.as_str().to_string(),
        _ => return None,
    };
    let base = name.split('#').next().unwrap_or(name.as_str()).to_string();
    Some((name, base))
}

/// Every `(full_name, base_name)` variable occurrence in `f`.
fn collect_vars(f: &Formula, out: &mut Vec<(String, String)>) {
    if let Some(pair) = var_full_and_base(f) {
        out.push(pair);
        return;
    }
    for c in f.children() {
        collect_vars(c, out);
    }
}

/// Whether `f` mentions the base var name `base` anywhere.
fn mentions_base(f: &Formula, base: &str) -> bool {
    if let Some((_, b)) = var_full_and_base(f) {
        return b == base;
    }
    f.children().iter().any(|c| mentions_base(c, base))
}

/// Flatten the top-level `And` chain of `f` into its conjuncts.
fn flatten_conjuncts<'a>(f: &'a Formula, out: &mut Vec<&'a Formula>) {
    if let Formula::And(parts) = f {
        for p in parts {
            flatten_conjuncts(p, out);
        }
    } else {
        out.push(f);
    }
}

/// The crate name of a def path — the segment before the first `::`.
fn crate_of(def_path: &str) -> &str {
    def_path.split("::").next().unwrap_or(def_path)
}

/// Type names that are concrete whatever the instantiation, plus the keywords a
/// rendered path may contain inside its angle brackets.
fn is_concrete_path_token(tok: &str) -> bool {
    matches!(
        tok,
        "u8" | "u16"
            | "u32"
            | "u64"
            | "u128"
            | "usize"
            | "i8"
            | "i16"
            | "i32"
            | "i64"
            | "i128"
            | "isize"
            | "f16"
            | "f32"
            | "f64"
            | "f128"
            | "bool"
            | "char"
            | "str"
            | "impl"
            | "dyn"
            | "as"
            | "const"
            | "mut"
            | "true"
            | "false"
    ) || tok.bytes().all(|b| b.is_ascii_digit())
}

/// Whether every generic argument spelled inside `callee`'s angle brackets is
/// CONCRETE — i.e. the callee is monomorphic at this call site.
///
/// `trust-mir-extract` renders a callee path with fully-qualified names for
/// every resolved type (`r3_generic_alias_tmethod_index::Feed`,
/// `core::convert::Into<usize>`), so an identifier inside angle brackets that is
/// neither a primitive/keyword nor part of a `::`-path is a GENERIC PARAMETER
/// still to be substituted — `core::mem::size_of::<T>`. That distinction is the
/// whole point here: `size_of::<T>()` is not an unmodelled deterministic
/// function, it is a value the CALLER of this generic function chooses, so its
/// obligation is genuinely refutable (there is a `T` that violates it) and must
/// keep its refutation. Fails closed: anything unrecognised reads as generic.
fn callee_path_is_monomorphic(callee: &str) -> bool {
    let bytes = callee.as_bytes();
    let mut depth: i32 = 0;
    let mut i = 0usize;
    while i < bytes.len() {
        let c = bytes[i];
        if c == b'<' {
            depth += 1;
            i += 1;
            continue;
        }
        if c == b'>' {
            depth -= 1;
            i += 1;
            continue;
        }
        if c.is_ascii_alphabetic() || c == b'_' {
            let start = i;
            while i < bytes.len() && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
                i += 1;
            }
            if depth > 0 {
                let tok = &callee[start..i];
                let path_tail = start >= 1 && bytes[start - 1] == b':';
                let path_head = i + 1 < bytes.len() && bytes[i] == b':' && bytes[i + 1] == b':';
                if !path_tail && !path_head && !is_concrete_path_token(tok) {
                    return false;
                }
            }
            continue;
        }
        i += 1;
    }
    true
}

/// Whether `callee` is a function whose BODY this compilation does not have and
/// whose path carries no unsubstituted generic parameter.
///
/// A SAME-CRATE callee is excluded even though its result is havocked exactly
/// the same way: its body IS available, so the gap is a missing summary, not the
/// modularity boundary — and the corpus pins that distinction
/// (`mutant/contract_skip_ensures_launder` indexes `a[idx(n)]` with a same-crate
/// `idx` and must keep refuting; deleting this exclusion was measured to turn
/// that row into a decline, i.e. to let the mutant survive). The
/// `same_crate_callee_is_not_reclassified` fixture kills the same deletion. The
/// crate name is tested for CONTAINMENT, not
/// just as a prefix, so a qualified path that reaches back into this crate
/// (`<<S as this_crate::Feed>::Item as core::convert::Into<usize>>::into`) is
/// excluded too.
fn callee_is_foreign_monomorphic(func: &VerifiableFunction, callee: &str) -> bool {
    let home = crate_of(&func.def_path);
    if home.is_empty() || callee.contains(home) {
        return false;
    }
    callee_path_is_monomorphic(callee)
}

/// Locals whose ONLY value source in this body is the destination of a call into
/// a FOREIGN, MONOMORPHIC callee, keyed by base var name and carrying the
/// local's declared integer `(width, signed)`.
///
/// A local qualifies only when nothing else can write it: no `Assign` statement
/// anywhere names it (whole-local or projected), it is not a parameter, and it
/// is neither mutably borrowed nor address-taken — the two channels through
/// which a callee or a later store could give it a value the def scan cannot
/// see. Restricting to fixed-width integer locals is what the probe in
/// [`havoc_flips_obligation`] needs: the declared type is the range the value
/// must lie in, and it is a fact of the input program's type, not an assumption
/// about any callee.
pub(super) fn call_only_int_dest_locals(
    func: &VerifiableFunction,
) -> FxHashMap<String, (u32, bool)> {
    let mut is_call_dest = vec![false; func.body.locals.len()];
    let mut disqualified = vec![false; func.body.locals.len()];
    let mark = |slot: &mut Vec<bool>, local: usize| {
        if local < slot.len() {
            slot[local] = true;
        }
    };
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign { place, rvalue, .. } = stmt {
                mark(&mut disqualified, place.local);
                // A mutable borrow / raw pointer to the local is a write channel
                // the whole-local def scan cannot see (`let p = &mut d; *p = e`),
                // exactly as `is_single_static_assignment` argues.
                if let Rvalue::Ref { mutable: true, place: bp } | Rvalue::AddressOf(_, bp) = rvalue
                {
                    mark(&mut disqualified, bp.local);
                }
            }
        }
        match &block.terminator {
            Terminator::Call { func: callee, dest, target: Some(_), .. } => {
                if dest.projections.is_empty() && callee_is_foreign_monomorphic(func, callee) {
                    mark(&mut is_call_dest, dest.local);
                } else {
                    mark(&mut disqualified, dest.local);
                }
            }
            // Any other terminator that writes a place makes the local's value
            // ambiguous for this pass; leave it out.
            Terminator::Call { dest, .. } => mark(&mut disqualified, dest.local),
            _ => {}
        }
    }
    let mut out: FxHashMap<String, (u32, bool)> = FxHashMap::default();
    for decl in &func.body.locals {
        let i = decl.index;
        if i >= func.body.locals.len() || !is_call_dest[i] || disqualified[i] {
            continue;
        }
        // Parameters carry their own entry hypotheses and are never "only ever
        // written by a call" from the caller's point of view.
        if i >= 1 && i <= func.body.arg_count {
            continue;
        }
        let Some(width) = decl.ty.int_width() else {
            continue;
        };
        out.insert(place_to_var_name(func, &Place::local(i)), (width, decl.ty.is_signed()));
    }
    out
}

/// Whether `conj` is exactly a declared-type range bound on `base` — a fact
/// implied by the local's Rust type and satisfied by every inhabitant of it, so
/// it pins no value. Recognises both spellings the generator emits:
/// `input_range_constraint`'s `And([Le(min, v), Le(v, max)])` and the
/// argument-range lane's `Ge(v, min)` / `Le(v, max)`.
///
/// ORIENTATION IS LOAD-BEARING. Only the four vacuous readings count — `min<=v`,
/// `v<=max`, `v>=min`, `max>=v`. The REVERSED comparisons against the same two
/// literals say something entirely different: `max<=v` and `min>=v` each pin `v`
/// to an endpoint, and treating one as inert would let a genuinely constrained
/// value be mistaken for a free havoc.
fn is_declared_type_range_bound(conj: &Formula, base: &str, width: u32, signed: bool) -> bool {
    let min_f = crate::range::type_min_formula(width, signed);
    let max_f = crate::range::type_max_formula(width, signed);
    let is_var = |f: &Formula| var_full_and_base(f).is_some_and(|(_, b)| b == base);
    match conj {
        Formula::And(parts) => {
            !parts.is_empty()
                && parts.iter().all(|p| is_declared_type_range_bound(p, base, width, signed))
        }
        // `min <= v` / `v <= max`
        Formula::Le(a, b) => (**a == min_f && is_var(b)) || (is_var(a) && **b == max_f),
        // `v >= min` / `max >= v`
        Formula::Ge(a, b) => (is_var(a) && **b == min_f) || (**a == max_f && is_var(b)),
        _ => false,
    }
}

/// The variable a conjunct DEFINES, when the conjunct is an equation
/// `Var(n) = rhs` (or `rhs = Var(n)`) whose right-hand side does not mention
/// `n`. This is the MIR-temp definition shape: `_3 = (_2 == 0)`.
fn defined_var(conj: &Formula) -> Option<String> {
    let Formula::Eq(a, b) = conj else {
        return None;
    };
    if let Some((_, base)) = var_full_and_base(a)
        && !mentions_base(b, &base)
    {
        return Some(base);
    }
    if let Some((_, base)) = var_full_and_base(b)
        && !mentions_base(a, &base)
    {
        return Some(base);
    }
    None
}

/// Whether hypothesis conjunct `conj` RESTRICTS the admissible values of `base`.
///
/// Three shapes provably restrict nothing, and all three are ubiquitous in the
/// generated formulas:
///
///   * a declared-type range bound on `base` itself — every inhabitant of the
///     type satisfies it, so it excludes no value (see
///     [`is_declared_type_range_bound`]);
///   * `Var(f) = rhs` where `f` occurs in no OTHER hypothesis conjunct. `f` is a
///     dead MIR temp: whatever value `base` takes, the equation is satisfied by
///     giving `f` the matching value, so it constrains `base` not at all. (The
///     divisor-is-zero flag `_3 = (_2 == 0)` is this shape: `_3` appears only in
///     the obligation, which is excluded from the hypotheses by the caller.)
///   * `Or([.., Var(f) = rhs, ..])` with the same side condition — the checked-op
///     semantics `(overflow) or (_0 = _2 + 1)`. That disjunct alone is
///     satisfiable for every `base`, so the whole disjunction is.
///
/// Anything else that mentions `base` counts as pinning it — a program guard, a
/// modelled callee's result bound, an intrinsic's value semantics. Misjudging in
/// that direction only leaves a row exactly as it is today.
fn conjunct_restricts(
    conj: &Formula,
    base: &str,
    width: u32,
    signed: bool,
    dead: &dyn Fn(&str) -> bool,
) -> bool {
    if !mentions_base(conj, base) {
        return false;
    }
    if is_declared_type_range_bound(conj, base, width, signed) {
        return false;
    }
    if let Some(def) = defined_var(conj)
        && def != base
        && dead(&def)
    {
        return false;
    }
    if let Formula::Or(disjuncts) = conj
        && disjuncts.iter().any(|d| defined_var(d).is_some_and(|def| def != base && dead(&def)))
    {
        return false;
    }
    true
}

/// A concrete value the partial evaluator can carry.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Val {
    B(bool),
    I(i128),
}

/// Evaluate `f` with `var` (matched by FULL name) bound to `k` and NO other
/// variable assigned. `None` means "not decided here" — a free variable, an
/// unsupported node, or an arithmetic overflow/zero-division in the evaluator
/// itself. Every `None` propagates, so the caller falls back to leaving the row
/// unchanged.
fn eval(f: &Formula, var: &str, k: i128) -> Option<Val> {
    let int = |x: &Formula| match eval(x, var, k) {
        Some(Val::I(v)) => Some(v),
        _ => None,
    };
    let boolean = |x: &Formula| match eval(x, var, k) {
        Some(Val::B(v)) => Some(v),
        _ => None,
    };
    match f {
        Formula::Bool(b) => Some(Val::B(*b)),
        Formula::Int(v) => Some(Val::I(*v)),
        Formula::UInt(v) => i128::try_from(*v).ok().map(Val::I),
        Formula::Var(name, _) => (name == var).then_some(Val::I(k)),
        Formula::SymVar(sym, _) => (sym.as_str() == var).then_some(Val::I(k)),
        Formula::Not(a) => boolean(a).map(|v| Val::B(!v)),
        Formula::And(parts) => {
            let mut acc = true;
            for p in parts {
                acc &= boolean(p)?;
            }
            Some(Val::B(acc))
        }
        Formula::Or(parts) => {
            let mut acc = false;
            for p in parts {
                acc |= boolean(p)?;
            }
            Some(Val::B(acc))
        }
        Formula::Implies(a, b) => Some(Val::B(!boolean(a)? || boolean(b)?)),
        Formula::Eq(a, b) => match (eval(a, var, k)?, eval(b, var, k)?) {
            (Val::I(x), Val::I(y)) => Some(Val::B(x == y)),
            (Val::B(x), Val::B(y)) => Some(Val::B(x == y)),
            _ => None,
        },
        Formula::Lt(a, b) => Some(Val::B(int(a)? < int(b)?)),
        Formula::Le(a, b) => Some(Val::B(int(a)? <= int(b)?)),
        Formula::Gt(a, b) => Some(Val::B(int(a)? > int(b)?)),
        Formula::Ge(a, b) => Some(Val::B(int(a)? >= int(b)?)),
        Formula::Add(a, b) => int(a)?.checked_add(int(b)?).map(Val::I),
        Formula::Sub(a, b) => int(a)?.checked_sub(int(b)?).map(Val::I),
        Formula::Mul(a, b) => int(a)?.checked_mul(int(b)?).map(Val::I),
        Formula::Div(a, b) => int(a)?.checked_div(int(b)?).map(Val::I),
        Formula::Rem(a, b) => int(a)?.checked_rem(int(b)?).map(Val::I),
        Formula::Neg(a) => int(a)?.checked_neg().map(Val::I),
        _ => None,
    }
}

/// The probe points for `havoc_flips_obligation`: the declared type's endpoints
/// and their neighbours, plus the small values every bounds/divisor obligation
/// turns on. Deterministic and duplicate-free.
fn probe_points(width: u32, signed: bool) -> Vec<i128> {
    let min = if signed { crate::range::signed_min(width) } else { 0 };
    let max = if signed {
        crate::range::signed_max(width)
    } else {
        i128::try_from(crate::range::unsigned_max(width)).unwrap_or(i128::MAX)
    };
    let mut pts = vec![min, max];
    for candidate in [min.saturating_add(1), max.saturating_sub(1), -1, 0, 1, 2, 3, 4, 8, 16] {
        if candidate >= min && candidate <= max {
            pts.push(candidate);
        }
    }
    pts.sort_unstable();
    pts.dedup();
    pts
}

/// Whether moving `var` alone across its declared type range flips `raw` between
/// true and false — the operational meaning of "the obligation's answer is the
/// callee's return value, which I do not have".
///
/// Requires a definite verdict at EVERY probe point: a single `None` means some
/// other variable is still live in `raw`, and then the refutation is not
/// attributable to this variable alone. Requires BOTH a true and a false
/// verdict: an obligation that is false everywhere is provable and keeps its
/// row; one that is true everywhere is violated whatever the callee returns and
/// also keeps its row.
fn havoc_flips_obligation(raw: &Formula, var: &str, width: u32, signed: bool) -> bool {
    let mut saw_true = false;
    let mut saw_false = false;
    for k in probe_points(width, signed) {
        match eval(raw, var, k) {
            Some(Val::B(true)) => saw_true = true,
            Some(Val::B(false)) => saw_false = true,
            _ => return false,
        }
    }
    saw_true && saw_false
}

/// Replace every occurrence of `Var(name)` (FULL name, so an SSA version is
/// never conflated with another) by `value`.
fn substitute(f: &Formula, name: &str, value: &Formula) -> Formula {
    if let Some((full, _)) = var_full_and_base(f)
        && full == name
    {
        return value.clone();
    }
    f.clone().map_children(&mut |c| substitute(&c, name, value))
}

/// The kinds this pass may reclassify: the machine-safety obligations whose
/// violation formula is an integer predicate the probe can evaluate.
fn is_reclassifiable_kind(kind: &VcKind) -> bool {
    matches!(
        kind,
        VcKind::DivisionByZero
            | VcKind::RemainderByZero
            | VcKind::ArithmeticOverflow { .. }
            | VcKind::IndexOutOfBounds
    )
}

/// The reason string carried on a declined row. Named so the compiler's report
/// and the tests agree on one spelling.
pub(crate) const HAVOC_DECLINE_KIND: &str = "UnmodeledCalleeReturn";

/// Reclassify every safety row whose refutation would rest on an unmodelled
/// callee return. Returns the number of rows reclassified.
///
/// The recorded [`ObligationRecord::body`] identifies the raw violation, and it
/// is AUTHENTICATED before use: the body must appear verbatim as one of the
/// formula's top-level conjuncts, or the row is left alone. Even an
/// unauthenticated body could only cost a decision, never buy a proof — the sole
/// edit this function makes is `<safety kind>` → `UnsupportedMir`, which
/// `discharge_body_vcs` turns into `Unknown` and never dispatches.
pub(super) fn reclassify_havoc_only_refutations(
    func: &VerifiableFunction,
    vcs: &mut [VerificationCondition],
) -> usize {
    let candidates = call_only_int_dest_locals(func);
    if candidates.is_empty() {
        return 0;
    }
    let mut reclassified = 0usize;
    for vc in vcs.iter_mut() {
        if !is_reclassifiable_kind(&vc.kind) {
            continue;
        }
        let Some(record) = vc.obligation.as_ref() else {
            continue;
        };
        let raw = record.body.clone();
        let mut conjuncts = Vec::new();
        flatten_conjuncts(&vc.formula, &mut conjuncts);
        if conjuncts.len() > MAX_CONJUNCTS {
            continue;
        }
        // Authenticate the recorded body against the formula, and split the
        // hypotheses off it. Exactly ONE occurrence is removed: a body that also
        // appears as a genuine hypothesis keeps that copy, so the pinning scan
        // still sees it.
        let Some(body_at) = conjuncts.iter().position(|c| **c == raw) else {
            continue;
        };
        let hypotheses: Vec<&Formula> =
            conjuncts.iter().enumerate().filter(|(i, _)| *i != body_at).map(|(_, c)| *c).collect();

        // verifier-perf: the base names each hypothesis conjunct mentions,
        // computed ONCE. The dead-variable side condition below asks "does any
        // OTHER conjunct mention this name" for every (candidate, conjunct)
        // pair, which is quadratic in the conjunct count; without this the query
        // re-walks every conjunct's formula each time, and a large body's VC has
        // hundreds of conjuncts of hundreds of nodes.
        let hypothesis_names: Vec<FxHashSet<String>> = hypotheses
            .iter()
            .map(|h| {
                let mut v = Vec::new();
                collect_vars(h, &mut v);
                v.into_iter().map(|(_, base)| base).collect()
            })
            .collect();

        // Fold hypothesis definitions into the raw violation so the obligation is
        // expressed over the values it really depends on. Only definitions whose
        // subject is defined exactly once are used, so no equation is applied in
        // two contradictory directions.
        let mut def_count: FxHashMap<String, usize> = FxHashMap::default();
        for h in &hypotheses {
            if let Some(d) = defined_var(h) {
                *def_count.entry(d).or_insert(0) += 1;
            }
        }
        let mut folded = raw.clone();
        for _ in 0..MAX_SUBST_ROUNDS {
            let before = folded.clone();
            for h in &hypotheses {
                let Formula::Eq(a, b) = h else { continue };
                let Some(subject) = defined_var(h) else { continue };
                if def_count.get(&subject).copied().unwrap_or(0) != 1 {
                    continue;
                }
                let (var_side, value_side) = match var_full_and_base(a) {
                    Some((full, base)) if base == subject => (full, b.as_ref()),
                    _ => match var_full_and_base(b) {
                        Some((full, base)) if base == subject => (full, a.as_ref()),
                        _ => continue,
                    },
                };
                folded = substitute(&folded, &var_side, value_side);
            }
            // Substitution replaces one node by a whole term, so a chain of
            // definitions can grow the folded obligation multiplicatively. Give
            // up (leaving the row untouched) rather than keep expanding.
            if formula_node_count(&folded) > MAX_FOLDED_NODES {
                folded = raw.clone();
                break;
            }
            if folded == before {
                break;
            }
        }

        // The candidate variables the folded obligation actually depends on.
        let mut occurrences = Vec::new();
        collect_vars(&folded, &mut occurrences);
        occurrences.sort();
        occurrences.dedup();

        let mut decline: Option<String> = None;
        for (full, base) in &occurrences {
            let Some(&(width, signed)) = candidates.get(base) else {
                continue;
            };
            // `name` is DEAD in the hypotheses when the only conjunct mentioning
            // it is the one under test (`at`) — the conjunct that would define
            // it. Excluding `at` is what makes the check "does anything ELSE
            // constrain this temp"; without the exclusion every definition would
            // count as an occurrence of its own subject and no conjunct would
            // ever be inert.
            let dead = |name: &str, at: usize| {
                !hypothesis_names
                    .iter()
                    .enumerate()
                    .any(|(i, names)| i != at && names.contains(name))
            };
            if hypotheses.iter().enumerate().any(|(i, h)| {
                conjunct_restricts(h, base, width, signed, &|name: &str| dead(name, i))
            }) {
                continue;
            }
            if havoc_flips_obligation(&folded, full, width, signed) {
                decline = Some(base.clone());
                break;
            }
        }

        if let Some(base) = decline {
            // Demote through the shared constructor so this pass carries the SAME
            // fail-closed violation formula as every other `UnsupportedMir`
            // emitter. `Bool(false)` here would be UNSAT, and the kernel-discharge
            // gates in `trust_clean::whole_program` select rows by
            // `proof_level() == L0Safety` — which `UnsupportedMir` is — then hand
            // `vc.formula` to `check_refute_vc` and treat a refutation as
            // DISCHARGED. That would turn "I do not know" into a certification.
            super::unsupported::demote_to_unsupported_mir(
                vc,
                HAVOC_DECLINE_KIND.to_string(),
                format!(
                    "the obligation's verdict is the return value of an unmodelled call \
                     (`{base}`), which nothing in this body constrains; a solver model over \
                     it is not an execution, so the row is Unknown rather than refuted"
                ),
            );
            reclassified += 1;
        }
    }
    // Post-condition on THIS pass's own rows: nothing it demoted carries a
    // formula a kind-blind consumer could read as discharged. Scoped to
    // `HAVOC_DECLINE_KIND` so it can only ever fire on a regression in this file
    // — it makes no claim about, and cannot be tripped by, another emitter.
    assert!(
        !vcs.iter().any(|vc| matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. }
            if kind == HAVOC_DECLINE_KIND)
            && super::unsupported::is_unsupported_mir_with_wrong_formula(vc)),
        "a declined row must carry the fail-closed (SAT) violation formula; an UNSAT one is \
         read as DISCHARGED by the kind-blind kernel gates in trust_clean::whole_program"
    );
    // NOT asserted here: the same invariant across every OTHER emitter's
    // `UnsupportedMir` rows. This pass has no authority over rows it did not
    // create, and a `debug_assert!` over all of them turns any emitter's
    // polarity bug into a COMPILER PANIC on valid Rust rather than a decline —
    // strictly worse than the invariant it guards, because the rows in question
    // are already fail-honest Unknowns on the compiler path. The emitters own
    // that invariant at their own construction sites; the crate-wide sweep over
    // real MIR lives in `tests/havoc_dest_decline_realmir.rs`.
    reclassified
}

#[cfg(test)]
mod fail_closed_polarity_tests {
    use super::*;

    /// A VC is a VIOLATION formula, so discharge means UNSAT. `Bool(true)` is
    /// SAT and can never be read as a proof; `Bool(false)` is UNSAT and is read
    /// as DISCHARGED by every consumer that selects rows by proof level instead
    /// of by kind — and `UnsupportedMir::proof_level()` is `L0Safety`, which is
    /// exactly what `trust_clean::whole_program`'s kernel gates select.
    #[test]
    fn the_unsupported_mir_formula_is_sat() {
        assert_eq!(
            super::super::unsupported::unsupported_mir_fail_closed_formula(),
            Formula::Bool(true),
            "an UNSAT formula on an `I do not know` row is a proof manufactured from a decline"
        );
    }

    /// `demote_to_unsupported_mir` rewrites the formula rather than leaving the
    /// row's original one in place, and drops the safety payload that no longer
    /// describes it.
    #[test]
    fn demotion_resets_the_formula_and_drops_the_payload() {
        let mut vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::Eq(
                Box::new(Formula::Var("_2".to_string(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            contract_metadata: None,
            obligation: None,
        };
        super::super::unsupported::demote_to_unsupported_mir(
            &mut vc,
            HAVOC_DECLINE_KIND.to_string(),
            "d".to_string(),
        );
        assert!(
            matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. } if kind == HAVOC_DECLINE_KIND)
        );
        assert_eq!(vc.formula, Formula::Bool(true));
        assert!(vc.obligation.is_none() && vc.contract_metadata.is_none());
        assert!(!super::super::unsupported::is_unsupported_mir_with_wrong_formula(&vc));
    }

    /// The oracle used by the pass's post-condition must actually flag an UNSAT
    /// `UnsupportedMir` row — an inert predicate would make the assert useless.
    #[test]
    fn the_polarity_oracle_flags_an_unsat_unsupported_row() {
        let mut vc = VerificationCondition {
            kind: VcKind::UnsupportedMir { kind: "K".to_string(), detail: "d".to_string() },
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
            obligation: None,
        };
        assert!(super::super::unsupported::is_unsupported_mir_with_wrong_formula(&vc));
        vc.formula = Formula::Bool(true);
        assert!(!super::super::unsupported::is_unsupported_mir_with_wrong_formula(&vc));
        // A non-UnsupportedMir row is never flagged, whatever its formula.
        vc.kind = VcKind::DivisionByZero;
        vc.formula = Formula::Bool(false);
        assert!(!super::super::unsupported::is_unsupported_mir_with_wrong_formula(&vc));
    }
}

#[cfg(test)]
mod type_range_orientation_tests {
    use super::*;

    fn v() -> Formula {
        Formula::Var("_2".to_string(), Sort::Int)
    }
    const U32_MAX: i128 = 4_294_967_295;

    /// The four spellings that every `u32` satisfies are inert.
    #[test]
    fn vacuous_u32_bounds_are_inert() {
        for f in [
            Formula::Le(Box::new(Formula::Int(0)), Box::new(v())),
            Formula::Le(Box::new(v()), Box::new(Formula::Int(U32_MAX))),
            Formula::Ge(Box::new(v()), Box::new(Formula::Int(0))),
            Formula::Ge(Box::new(Formula::Int(U32_MAX)), Box::new(v())),
        ] {
            assert!(
                is_declared_type_range_bound(&f, "_2", 32, false),
                "{f:?} holds for every u32 and must not count as pinning"
            );
        }
    }

    /// The REVERSED comparisons against the same literals pin `_2` to an
    /// endpoint. Accepting one would let a constrained value be read as a free
    /// havoc, which is the direction that costs a decision.
    #[test]
    fn reversed_bounds_are_not_inert() {
        for f in [
            Formula::Le(Box::new(Formula::Int(U32_MAX)), Box::new(v())),
            Formula::Ge(Box::new(Formula::Int(0)), Box::new(v())),
            Formula::Le(Box::new(v()), Box::new(Formula::Int(0))),
            Formula::Ge(Box::new(v()), Box::new(Formula::Int(U32_MAX))),
        ] {
            assert!(
                !is_declared_type_range_bound(&f, "_2", 32, false),
                "{f:?} pins _2 to an endpoint and must count as a constraint"
            );
        }
    }

    /// A bound at a value that is NOT the declared type's endpoint is real
    /// information — this is what keeps `leading_zeros`'s modelled `_2 <= 32`
    /// from being mistaken for a `u32` type bound.
    #[test]
    fn a_tighter_bound_is_not_a_type_bound() {
        let f = Formula::Le(Box::new(v()), Box::new(Formula::Int(32)));
        assert!(!is_declared_type_range_bound(&f, "_2", 32, false));
    }

    /// The bound must be about `base` itself, not some other variable.
    #[test]
    fn a_bound_on_another_variable_is_not_inert_for_base() {
        let other = Formula::Var("_9".to_string(), Sort::Int);
        let f = Formula::Le(Box::new(other), Box::new(Formula::Int(U32_MAX)));
        assert!(!is_declared_type_range_bound(&f, "_2", 32, false));
    }
}
