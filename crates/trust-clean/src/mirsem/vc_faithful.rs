// Deciding whether a safety VC the compiler emitted is faithfully modeled
// here. A VC kind with no modeled counterpart must be reported unmodeled: this
// is the gate that stops a whole-function faithfulness claim from covering an
// obligation nothing checked.

use super::*;

/// Build the de-Bruijn grounding map for a list of operand variable names, assigning
/// `names[0] = bvar(n-1)`, …, `names[n-1] = bvar(0)` — the convention `ground_prop`
/// expects (a leading binder is the OUTERMOST, highest index). A non-`Var` operand
/// (a constant, a struct field, …) is NOT mappable here ⇒ `None` (fail closed).
pub(super) fn debruijn_params(names: &[&str]) -> std::collections::HashMap<String, Expr> {
    let n = names.len();
    let mut m = std::collections::HashMap::new();
    for (i, name) in names.iter().enumerate() {
        m.insert((*name).to_string(), Expr::bvar(u32::try_from(n - 1 - i).unwrap_or(0)));
    }
    m
}

/// The variable name of an integer `Formula::Var` leaf (the only operand shape the
/// formula-aware grounder maps to a de-Bruijn binder). A constant / arithmetic /
/// field-projection operand returns `None` ⇒ the VC is outside the formula-aware
/// fragment and the function fails closed.
pub(super) fn formula_var_name(f: &trust_types::Formula) -> Option<&str> {
    match f {
        trust_types::Formula::Var(n, _) => Some(n.as_str()),
        _ => None,
    }
}

/// Which of the two emitter constructions `assert_bound_or_body_core` recovered a
/// core from. The negation arm layers an ADDITIONAL subject gate on the assert route
/// (see the `assert_negation_subject` call there), so the route has to be reported
/// rather than erased.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum CoreRoute {
    /// The peeled body IS the violation core (`v2_divisor_is_zero_formula`'s `Eq(b,0)`,
    /// `v2_build_negation_raw_vc`'s `Eq(v, MIN)`).
    Body,
    /// The peeled body is the bare `Var(_c)` assert-condition local and the core is the
    /// RHS of its MIR-confirmed block definition.
    AssertCondition,
}

/// Trust: SHIFT-CORE SELECTION (2026-07-29) — the SHAPE of a shift VC's emitted
/// violation, destructured: `(amount, threshold W, is_signed_form)`.
///
///   * unsigned amount — `Ge(n, Int W)`
///   * signed amount   — `Or([Lt(n, Int 0), Ge(n, Int W)])`
///
/// Exactly the two forms `trust_vcgen::generate::checked_vcs::v2_shift_violation_formula`
/// builds. `None` for anything else (fail-closed).
pub(super) fn shift_violation_shape(
    invalid: &trust_types::Formula,
) -> Option<(&trust_types::Formula, i128, bool)> {
    use trust_types::Formula as F;
    match invalid {
        F::Ge(n, w) => {
            let F::Int(t) = &**w else { return None };
            Some((&**n, *t, false))
        }
        F::Or(disjuncts) => {
            let [F::Lt(n_lt, zero), F::Ge(n_ge, w)] = disjuncts.as_slice() else { return None };
            if !matches!(&**zero, F::Int(0)) || n_lt != n_ge {
                return None;
            }
            let F::Int(t) = &**w else { return None };
            Some((&**n_ge, *t, true))
        }
        _ => None,
    }
}

/// Trust: BOUNDS-CORE SELECTION (2026-07-31, round-5 defect [4]) — the SHAPE of a
/// bounds VC's emitted violation, destructured: `(index, len, is_signed_index)`.
///
///   * unsigned index — `Ge(i, len)`
///   * signed index   — `Or([Lt(i, Int 0), Ge(i, len)])`
///
/// Exactly the two forms `v2_build_bounds_assert_vc` builds
/// (`generate/checked_vcs.rs:257-265`: the `Or` is emitted whenever
/// `operand_ty_cow(lhs).is_signed()`). `None` for anything else (fail-closed).
///
/// This is the analogue of [`shift_violation_shape`], which has carried the same
/// signed/unsigned discrimination since round 3 — and the asymmetry is the defect:
/// the shift arm refuses a signed-form body under an unsigned `shift_ty`, while the
/// bounds arm read the `Ge` disjunct straight out of the signed `Or` and minted
/// `SafetyVcKind::Bounds`, whose spec `idx_oob len i` says nothing about the `i < 0`
/// half the VC also states.
pub(super) fn bounds_violation_shape(
    violation: &trust_types::Formula,
) -> Option<(&trust_types::Formula, &trust_types::Formula, bool)> {
    use trust_types::Formula as F;
    match violation {
        F::Ge(i, len) => Some((&**i, &**len, false)),
        F::Or(disjuncts) => {
            let [F::Lt(i_lt, zero), F::Ge(i_ge, len)] = disjuncts.as_slice() else { return None };
            if !matches!(&**zero, F::Int(0) | F::UInt(0)) || i_lt != i_ge {
                return None;
            }
            Some((&**i_ge, &**len, true))
        }
        _ => None,
    }
}

/// Whether `f` carries, anywhere, the SIGNED-index bounds violation
/// `Or([Lt(i,0), Ge(i,len)])`.
///
/// Trust: THE DROPPED SIGNED DISJUNCT (2026-07-31, round-5 defect [4]). The bounds arm
/// used to locate a `Ge(i, len)` leaf INSIDE the obligation body, and the locator of the
/// day (`obligation_violation_leaf`, deleted in round 6) descended `Or`s — so for a
/// signed index the located leaf
/// was the SECOND DISJUNCT of the emitted violation and the certificate asserted that the
/// modeled condition IS the emitted one when the emitted one is strictly larger. The
/// direction is over-refutation (the VC states MORE than `idx_oob`), so this is a false
/// ADEQUACY statement and a kind gap rather than a live safety hole — but a certificate
/// whose proposition is not the VC's own is exactly what this tier must never mint.
///
/// CLOSED BY DECLINING, and that is a deliberate choice of the two available directions:
///
///   * Modeling it needs a signed `idx_oob_signed` spec constant AND a
///     `SafetyVcKind::Bounds` signedness variant. `SafetyVcKind` lives in
///     `mirsem/mod.rs` and the spec constants in the MirSem spec module — neither is
///     this file, and minting a signedness-LABELLED certificate whose kernel def-eq is
///     still against the unsigned `idx_oob` would be the forgery itself, not a fix. So
///     the capability gap is recorded as one, exactly as `trustir_safety.rs` records it
///     (`idxOobSigned`, `:815-821`), and this lane declines the same shape the sibling
///     lane declines.
///   * The scan is over the whole located BODY rather than the located leaf alone, so a
///     signed violation nested inside a body this arm would otherwise read fails closed
///     too.
///
/// COST: **zero** — 0 of the 68 bounds VCs over `crates/trust-clean/fixtures` peel to a
/// body carrying a signed-index `Or`, so none of the 33 bounds certificates is
/// withdrawn (`obligation_region_tests::mirsem_corpus_census`, whose command
/// [`discarded_negative_disjunct_is_vacuous`]'s doc block states). That zero is a CORPUS
/// fact, not an emitter fact:
/// `generate/checked_vcs.rs:257-265` builds this `Or` for any signed index operand — the
/// regression test drives it end-to-end through `trust_vcgen::generate_vcs`.
fn carries_signed_index_violation(f: &trust_types::Formula) -> bool {
    use trust_types::Formula as F;
    if bounds_violation_shape(f).is_some_and(|(_, _, signed)| signed) {
        return true;
    }
    match f {
        F::And(v) | F::Or(v) => v.iter().any(carries_signed_index_violation),
        F::Not(a) => carries_signed_index_violation(a),
        F::Implies(a, b) => carries_signed_index_violation(a) || carries_signed_index_violation(b),
        _ => false,
    }
}

/// The base place name of a versioned VC variable — `_6#s3_0` names the same place as
/// `_6`. The staleness machinery stamps `#token` suffixes on both defs and body reads
/// (`version_rename_at` / `version_block_def_at_establish`), so a name comparison that
/// is to recognize "the def OF this local" must be on the base.
fn base_var_name(f: &trust_types::Formula) -> Option<&str> {
    let n = formula_var_name(f)?;
    Some(n.split('#').next().unwrap_or(n))
}

/// Trust: ASSERT-BOUND CORE SELECTION (2026-07-29) — the genuine violation core of an
/// ASSERT-driven safety VC, resolved through the block definition that BINDS the assert's
/// own condition local.
///
/// `v2_build_assert_negation_vc` and the `AssertMessage::DivisionByZero`/
/// `RemainderByZero` arms of `generate_v2_safety_vcs_impl` do NOT emit `Eq(x, MIN)` /
/// `Eq(b, 0)` as their obligation. They emit `v2_assert_failure_formula`, which for the
/// `expected == false` asserts rustc lowers these to is the BARE condition local
/// `Var(c)`; the core reaches the formula only as the RHS of the SSA guard-binding block
/// definition `Eq(Var c, Eq(x, MIN))` / `Eq(Var c, Eq(b, 0))` that
/// `extract_block_definitions_until` emits for `c := (x == MIN)` / `c := (b == 0)`.
/// (`abs_nonneg`'s negation VC is exactly this shape: obligation body `Var("_6", Bool)`;
/// so are `checked_div`/`guarded_div`/`BitArray::get_bit`'s div and rem twins.)
///
/// **ONLY the bare `Var(c)` body is admitted** — see `assert_bound_or_body_core`. For
/// `expected == false` the emitted violation IS `c`, so `c`'s binding RHS is literally
/// the obligation and certifying it is exact. A `Not(Var c)` body (`expected == true`,
/// the shape the BOUNDS assert takes) means the violation is `¬RHS`, which is NOT the
/// modeled core — certifying the RHS there would claim the complement of the obligation.
///
/// The previous `find_violation_leaf_through_eq` reached the negation core by descending
/// into the operands of EVERY `Eq` anywhere in `vc.formula` — which is every block
/// definition in the function, plus any `Eq`-shaped precondition. That was the widest
/// hypothesis surface of the seven sites: the located `Eq(Var, Int)` could be any
/// `let m = i32::MIN;` block-def or a `#[requires] y == -128`, and
/// `swidth_of_signed_min` then read the certified width off it.
///
/// This resolves the def by NAME: the base name of `cond` must be the base name of the
/// def's subject, and the def set so located must be a SINGLETON (two definitions of the
/// assert's condition local give no principled choice ⇒ fail closed). The returned RHS
/// still has to satisfy the caller's own shape test, so a def whose RHS is not a modeled
/// core declines.
///
/// Trust: THE DOC IS NOW THE CODE (2026-07-29, lane A finding [4]). A name-matching scan
/// of `vc.formula` does NOT restrict the match to a block definition, and cannot: once
/// `v2_formula_with_path_guards` FLATTENS the wrapped `And` (`generate/safety.rs:1115`),
/// a block definition `Eq(_3, Eq(b,0))` and an `Eq`-shaped PRECONDITION `Eq(_3, Eq(b,0))`
/// are the same tree in the same position. The singleton rule is not a defense when the
/// genuine def is ABSENT: MEASURED on the tree before this change, an `OverflowNeg`
/// assert whose cond local has no defining statement, plus
/// `#[requires] _3 == (y == -128)`, minted `NegationOverflow(W8)` for an **i32**
/// negation over a variable the body never negates.
///
/// So the located binding is now CONFIRMED against the MIR the emitter itself read
/// ([`mir_assert_condition_core`]): the function must contain an `Assert` on this local
/// in a block that DEFINES it, that definition must be the `c := (x == k)` comparison the
/// `expected == false` lowering produces, and the binding found in the formula must be
/// that definition — operand for operand, through the emitter's own
/// `trust_vcgen::operand_to_formula`, modulo the `#token` version stamps
/// `version_block_def_at_establish` adds. A `#[requires]`/`#[ensures]` cannot manufacture
/// a body statement, so the contract surface is closed rather than merely outnumbered.
///
/// COST: zero on the corpus. All 11 assert-route certificates over the 485 committed
/// dumps (7 `DivByZero` + 3 `RemByZero` + 1 `NegationOverflow`, the VCs whose peeled body
/// is a bare `Var`) survive the MIR confirmation unchanged — real rustc-lowered MIR binds
/// the assert's condition local in the assert's own block, which is precisely what this
/// requires and what a crafted `VerifiableFunction` had been able to skip.
fn assert_condition_binding<'a>(
    func: &trust_types::VerifiableFunction,
    formula: &'a trust_types::Formula,
    cond: &trust_types::Formula,
) -> Option<&'a trust_types::Formula> {
    use trust_types::Formula as F;
    let want = base_var_name(cond)?;
    // The MIR's own binding of this assert's condition local. No statement binds it ⇒
    // the route the doc describes does not exist for this VC ⇒ fail closed.
    let mir_core = mir_assert_condition_core(func, want)?;
    fn collect<'a>(f: &'a F, want: &str, out: &mut Vec<&'a F>) {
        if let F::Eq(lhs, rhs) = f
            && base_var_name(lhs).is_some_and(|n| n == want)
        {
            out.push(rhs);
            return;
        }
        match f {
            // `And`/`Or` only: a binding under a `Not` is a negated fact and one in an
            // `Implies` antecedent is a hypothesis — neither is a block definition.
            F::And(v) | F::Or(v) => v.iter().for_each(|x| collect(x, want, out)),
            _ => {}
        }
    }
    let mut found: Vec<&F> = Vec::new();
    collect(formula, want, &mut found);
    let first = *found.first()?;
    if !found.iter().all(|f| *f == first) {
        return None; // two DIFFERENT bindings of the condition local ⇒ fail closed
    }
    // … and the one binding the formula carries must BE the MIR's definition.
    formula_agrees_modulo_versions(first, &mir_core).then_some(first)
}

/// Trust: ASSERT-BOUND CORE SELECTION (2026-07-29) — the MIR side of
/// [`assert_condition_binding`]: the comparison the assert's condition local is DEFINED
/// by, lowered exactly as the VC emitter lowers it.
///
/// Requires, all of them, or `None`:
///
///   * a block whose terminator is an `expected == false` `Assert` on the local named
///     `want` — the only lowering that makes a bare `Var(c)` the obligation body
///     (`v2_assert_failure_formula` emits `Not(Var c)` for `expected == true`, which this
///     route does not admit at all),
///   * exactly ONE statement in THAT block assigning it (the region
///     `extract_block_definitions_until` reads; SSA, so a second assignment means the
///     name does not identify a unique definition), and
///   * that statement being the `c := (x == k)` comparison the `expected == false`
///     `DivisionByZero` / `RemainderByZero` / `OverflowNeg` lowering emits.
///
/// Two asserts on the same local in different blocks are admitted only if they resolve
/// to the SAME comparison; otherwise the VC's own assert is ambiguous ⇒ fail closed.
fn mir_assert_condition_core(
    func: &trust_types::VerifiableFunction,
    want: &str,
) -> Option<trust_types::Formula> {
    use trust_types::{BinOp, Formula as F, Operand, Rvalue, Statement, Terminator};
    let names = |p: &trust_types::Place| trust_vcgen::place_to_var_name(func, p) == want;
    let mut found: Vec<F> = Vec::new();
    for block in &func.body.blocks {
        let Terminator::Assert { cond, expected: false, .. } = &block.terminator else {
            continue;
        };
        let (Operand::Copy(p) | Operand::Move(p)) = cond else { continue };
        if !names(p) {
            continue;
        }
        let mut defs = block.stmts.iter().filter_map(|s| match s {
            Statement::Assign { place, rvalue, .. } if names(place) => Some(rvalue),
            _ => None,
        });
        let Some(rvalue) = defs.next() else { return None }; // asserted, never defined
        if defs.next().is_some() {
            return None; // two definitions in the assert's own block ⇒ fail closed
        }
        let Rvalue::BinaryOp(BinOp::Eq, a, b) = rvalue else { return None };
        found.push(F::Eq(
            Box::new(trust_vcgen::operand_to_formula(func, a)),
            Box::new(trust_vcgen::operand_to_formula(func, b)),
        ));
    }
    let first = found.first()?.clone();
    found.iter().all(|f| *f == first).then_some(first)
}

/// Trust: NEGATION SUBJECT (2026-07-31, round-5 defects [1]/[8]) — the
/// `(variable name, MIR type)` of EVERY operand this function's MIR actually negates:
/// the subject each `VcKind::NegationOverflow` producer in `trust-vcgen` takes, and the
/// operand whose `crate::operand_ty` becomes that kind's `ty`.
///
/// The three producers, read off the emitter rather than assumed — a claim about a
/// producer is false if any sibling branch admits the case, so all three are listed and
/// all three are covered by ONE scan. THE DENOMINATOR, with the command (2026-07-31, run
/// in this tree, from `crates/`):
///
/// ```text
/// grep -rn "kind: VcKind::NegationOverflow {" --include='*.rs' trust-vcgen/src   # 9 hits
/// grep -rn "Some(VcKind::NegationOverflow"     --include='*.rs' trust-vcgen/src   # 1 hit
/// ```
///
/// Of those 10: 5 are `#[cfg(test)]` fixtures in `abstract_interp/tests.rs`; 4 are
/// `checked_vcs.rs:109/121` (the assert producer's BV and Int paths) and `:817/836` (the
/// raw producer's two); 1 is `unwrap_panic.rs:1385`, the `abs` `kind_override`. So THREE
/// producers, five construction sites, two subject rules. `cross_check/reference_vcgen.rs:112`
/// pushes a bare KIND into a cross-check list and emits no `VerificationCondition` — the
/// round-4 claim audit left a note at that line saying so, and it is excluded here for
/// that reason, not overlooked.
///
/// | producer | subject |
/// |---|---|
/// | `checked_vcs.rs:775` `v2_build_negation_raw_vc` | the `Rvalue::UnaryOp(Neg, operand)` the statement negates |
/// | `checked_vcs.rs:57` `v2_build_assert_negation_vc` | `v2_find_target_neg_operand(func, target)` — the FIRST `Rvalue::UnaryOp(Neg, ..)` statement of the assert's TARGET block (`block_defs.rs:881-895`) |
/// | `unwrap_panic.rs:1382-1387` (`signed_abs_panic_body`, `:138`) | the FIRST argument of a signed `iN::abs` call |
///
/// The first two are both `Rvalue::UnaryOp(UnOp::Neg, ..)` statements, and the second's
/// operand is a member of the first's set by construction (it is one such statement, in
/// one particular block), so a scan over every `Neg` rvalue in the body covers both
/// WITHOUT keying on the route. That is deliberate: round 4 closed this defect on the
/// trust-ir lane by keying its gate on the assert-condition ROUTE, which left the
/// body-route half re-openable from the API (round-5 defect [8]). The gate here is keyed
/// on the SUBJECT — every negation certificate, by whatever route, must name a variable
/// this MIR negates.
///
/// THE `abs` RECOGNIZER IS A DELIBERATELY NARROWER TWIN. `is_signed_abs_call`
/// (`unwrap_panic.rs:123`) is `pub(super)` inside `trust-vcgen`, so it is re-derived
/// here as `<last `::` segment> == "abs"` plus the same `core::num::` / `std::num::`
/// anchor. The emitter's third condition — a SIGNED-int receiver
/// (`signed_abs_panic_body`, `:141-143`) — is not re-tested here but at the USE site:
/// `SWidth::from_mir` returns `None` for an unsigned width (`mirsem/mod.rs:2408-2410`),
/// so an unsigned subject declines there. `trust-vcgen`'s own `method_tail`
/// additionally strips TRAILING turbofish groups (`alloc_bounds.rs:162-196`), which this
/// twin does not: a path ending in a turbofish therefore matches THERE and not HERE, so
/// the twin's recognized set is a SUBSET of the emitter's and the disagreement direction
/// is over-rejection (a lost certificate), never over-acceptance (a subject the emitter
/// never used).
fn negation_subjects(
    func: &trust_types::VerifiableFunction,
) -> Vec<(String, trust_types::Ty)> {
    use trust_types::{Operand, Rvalue, Statement, Terminator, UnOp};
    fn is_signed_abs_call(callee: &str) -> bool {
        callee.trim().rsplit("::").next() == Some("abs")
            && (callee.contains("core::num::") || callee.contains("std::num::"))
    }
    let mut out: Vec<(String, trust_types::Ty)> = Vec::new();
    let mut push = |operand: &Operand| {
        let (Operand::Copy(p) | Operand::Move(p)) = operand else { return };
        let Some(ty) = trust_vcgen::operand_ty(func, operand) else { return };
        out.push((trust_vcgen::place_to_var_name(func, p), ty));
    };
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign { rvalue: Rvalue::UnaryOp(UnOp::Neg, operand), .. } = stmt {
                push(operand);
            }
        }
        if let Terminator::Call { func: callee, args, target: Some(_), .. } = &block.terminator
            && is_signed_abs_call(callee)
            && let Some(arg) = args.first()
        {
            push(arg);
        }
    }
    out
}

/// Trust: THE ASSERT-NEGATION SUBJECT (2026-07-31, round-6 item F2) — the
/// `(variable name, MIR type)` of the operand the ASSERT-NEGATION emitter takes as ITS
/// subject in this function. The consumer-side twin of `v2_find_target_neg_operand`
/// (`block_defs.rs:881-895`), which `v2_build_assert_negation_vc` reads at
/// `checked_vcs.rs:65` and whose `crate::operand_ty` at `checked_vcs.rs:69` becomes
/// `VcKind::NegationOverflow { ty }`.
///
/// For every block whose terminator is an `expected == false`
/// `Assert { msg: AssertMessage::OverflowNeg, target, .. }` — the sole call site of that
/// producer (`safety.rs:177-178`) and the only assert polarity whose body is the bare
/// `Var(_c)` the assert route resolves — take the FIRST `Rvalue::UnaryOp(UnOp::Neg,
/// operand)` statement of `target`, exactly as `v2_find_target_neg_operand`'s `find_map`
/// does. Collapse to the single `(name, ty)` they all agree on; disagreement, a missing
/// negation, or a non-place operand ⇒ `None`, fail closed.
///
/// PORTED FROM `trustir_safety.rs`, AND IT LAYERS ON THE UNION RATHER THAN REPLACING IT.
/// [`negation_subjects`] is the whole-body union over all THREE producers and is keyed on
/// the SUBJECT, so it runs on every route; this one is strictly narrower — it pins the
/// subject to THIS assert's own target block — and is therefore applied ONLY on the
/// assert route, as an ADDITIONAL conjunct. Replacing the union with it would withdraw
/// real rows: 7 of this lane's 12 corpus negation certificates take the assert route
/// (`mirsem_corpus_census`, `neg=12/12 (assert route 7)`), and the other 5 take the body
/// route, where this function has nothing to say. Both survive the pair — `certs=635`
/// and `neg=12/12` unchanged, re-measured in this tree.
fn assert_negation_subject(
    func: &trust_types::VerifiableFunction,
) -> Option<(String, trust_types::Ty)> {
    use trust_types::{AssertMessage, Operand, Rvalue, Statement, Terminator, UnOp};
    let mut found: Option<(String, trust_types::Ty)> = None;
    for block in &func.body.blocks {
        let Terminator::Assert { expected: false, msg: AssertMessage::OverflowNeg, target, .. } =
            &block.terminator
        else {
            continue;
        };
        let target_block = func.body.blocks.get(target.0)?;
        let operand = target_block.stmts.iter().find_map(|stmt| {
            let Statement::Assign { rvalue, .. } = stmt else { return None };
            match rvalue {
                Rvalue::UnaryOp(UnOp::Neg, operand) => Some(operand),
                _ => None,
            }
        })?;
        let (Operand::Copy(p) | Operand::Move(p)) = operand else { return None };
        let entry =
            (trust_vcgen::place_to_var_name(func, p), trust_vcgen::operand_ty(func, operand)?);
        match &found {
            Some(prev) if *prev != entry => return None, // ambiguous ⇒ fail closed
            _ => found = Some(entry),
        }
    }
    found
}

/// The MIR type of the negation subject named `want` ([`negation_subjects`]).
///
/// `None` — fail closed — when this MIR negates nothing named `want` (the certified
/// variable is not the one the obligation is about) or when two negations of that name
/// disagree on the type (ambiguous ⇒ no principled width).
///
/// Trust: THE `#` STRIP IS ONE-SIDED (2026-07-31, round-6 item F3). `want` is the caller's
/// [`base_var_name`] of a FORMULA variable, so the `#token` version stamp is already off
/// that side. This function used to strip `#` off the MIR side too, and that is the
/// base/segment-boundary hazard `place_to_var_name` closed for `.`/`[`/`*`/`@` reopened
/// for `#`: a MIR local whose name is literally `y#s3_0` would have matched a formula
/// variable spelled `y`, letting a negation of one place authenticate a certificate about
/// another. The MIR side is now compared WHOLE.
///
/// WHY THIS SIDE AND NOT THE EMITTER. The alternative F3 named is to demote `#` at the
/// emitter beside `.`/`[`/`*`/`@` — i.e. add it to `trust_vcgen`'s
/// `PROJECTION_SEGMENT_LEAD` (`trust-vcgen/src/lib.rs:4281`) so a source name containing
/// one demotes to the unique `_<local>` spelling. That is the wider fix and it is NOT
/// available from here: `trust-vcgen` is not this lane's file, and the demotion would
/// change the emitted variable VOCABULARY of every consumer at once (the guard-implied
/// assert augmentation in `prove.rs` spells the same names) rather than one certifier's
/// name comparison. Its cost would also not be zero by construction — it renames a local
/// wherever it fires, where this change only ever REFUSES a match.
///
/// WHAT THE OTHER WOULD HAVE COST, MEASURED rather than argued (2026-07-31, in this tree):
/// `obligation_region_tests::mirsem_corpus_census` tallies every `LocalDecl` source name
/// over the whole fixture corpus and asserts `locals=16827 named=4923 named_with_hash=0`,
/// so the emitter-side demotion would fire on 0 locals of this corpus and cost 0 rows —
/// the same zero this side costs. The choice between them is therefore about BLAST RADIUS
/// and ownership, not about corpus cost, and the direction here is over-rejection either
/// way: a genuine `#` in a MIR place name is minted by nothing in the tree
/// (`generate/path_defs.rs:859`'s `format!("{name}#{tok}")` is the only producer of the
/// character and it stamps FORMULA variables, never `place_to_var_name`'s output), so the
/// whole-name comparison loses no real subject.
pub(super) fn negation_subject_ty(
    func: &trust_types::VerifiableFunction,
    want: &str,
) -> Option<trust_types::Ty> {
    let mut found: Option<trust_types::Ty> = None;
    for (name, ty) in negation_subjects(func) {
        if name != want {
            continue;
        }
        match &found {
            Some(prev) if *prev != ty => return None, // ambiguous ⇒ fail closed
            _ => found = Some(ty),
        }
    }
    found
}

/// Structural equality of two `Formula`s that ignores the `#token` version stamps the
/// staleness machinery puts on place variables (`_6#s3_0` and `_6` name the same place).
/// Used to compare a conjunct of the WRAPPED, version-renamed VC formula against a term
/// freshly lowered from the MIR, which carries bare names.
fn formula_agrees_modulo_versions(a: &trust_types::Formula, b: &trust_types::Formula) -> bool {
    use trust_types::Formula as F;
    match (a, b) {
        (F::Var(x, sx), F::Var(y, sy)) => {
            sx == sy
                && x.as_str().split('#').next() == y.as_str().split('#').next()
        }
        (F::And(u), F::And(v)) | (F::Or(u), F::Or(v)) => {
            u.len() == v.len()
                && u.iter().zip(v).all(|(x, y)| formula_agrees_modulo_versions(x, y))
        }
        (F::Not(x), F::Not(y)) | (F::Neg(x), F::Neg(y)) => formula_agrees_modulo_versions(x, y),
        (F::Implies(x1, x2), F::Implies(y1, y2))
        | (F::Eq(x1, x2), F::Eq(y1, y2))
        | (F::Lt(x1, x2), F::Lt(y1, y2))
        | (F::Le(x1, x2), F::Le(y1, y2))
        | (F::Gt(x1, x2), F::Gt(y1, y2))
        | (F::Ge(x1, x2), F::Ge(y1, y2))
        | (F::Add(x1, x2), F::Add(y1, y2))
        | (F::Sub(x1, x2), F::Sub(y1, y2))
        | (F::Mul(x1, x2), F::Mul(y1, y2))
        | (F::Div(x1, x2), F::Div(y1, y2))
        | (F::Rem(x1, x2), F::Rem(y1, y2)) => {
            formula_agrees_modulo_versions(x1, y1) && formula_agrees_modulo_versions(x2, y2)
        }
        // Every other shape (literals, bitvector terms, selects, calls, …) carries no
        // version stamp of its own; exact equality is the right test and anything this
        // arm does not recognize compares unequal unless it is literally identical.
        _ => a == b,
    }
}

/// This VC's own violation core: the emitted body itself when the body IS the core
/// (`locate_violation`), else — for the `expected == false` ASSERT shape, whose body
/// is the BARE condition local — the core that local is BOUND to
/// ([`assert_condition_binding`]). Both routes are the emitter's own construction; a
/// body outside both declines. The `CoreRoute` says which one fired.
///
/// A `Not(Var c)` body is deliberately NOT admitted: there the violation is the
/// COMPLEMENT of the binding, so the binding is not this obligation.
///
/// The certified core from an ALREADY-AUTHENTICATED obligation `body` (the peel is
/// deleted; `body` is always `&ObligationRecord::body`, admitted only after
/// `reconstruct_obligation == formula`). Two routes, both the emitter's own construction:
/// the body IS the core, or it is the bare `expected == false` assert-condition local
/// whose MIR-confirmed binding ([`assert_condition_binding`]) is the core. A `Not(Var c)`
/// body is deliberately NOT admitted: there the violation is the COMPLEMENT of the binding.
/// The `CoreRoute` says which one fired.
fn assert_bound_or_body_core_with<'a>(
    func: &trust_types::VerifiableFunction,
    formula: &'a trust_types::Formula,
    body: &'a trust_types::Formula,
    is_core: &dyn Fn(&trust_types::Formula) -> bool,
) -> Option<(&'a trust_types::Formula, CoreRoute)> {
    if is_core(body) {
        return Some((body, CoreRoute::Body));
    }
    if formula_var_name(body).is_none() {
        return None;
    }
    let bound = assert_condition_binding(func, formula, body)?;
    is_core(bound).then_some((bound, CoreRoute::AssertCondition))
}

/// Trust: AUTHENTICATED-OBLIGATION RECONSTRUCTION (2026-07-31, the consumer half of the
/// emitter's recorded [`trust_types::ObligationRecord`]). Replays every wrapper the
/// emitter recorded — innermost-first — onto the recorded raw violation `body`. This is
/// the CONSUMER's copy of the emitter's own wrapping loop, and it is the load-bearing
/// authenticator: the recorded obligation is a CLAIM (the field is
/// `Serialize`/`Deserialize` and a hostile fixture can set it to anything), admitted ONLY
/// when `reconstruct_obligation(rec) == vc.formula` bit-for-bit, `#token` version stamps
/// included. The closed wrapper vocabulary has NO `Implies`, NO `Not` and NO
/// free-disjunct, so no wrapper-spelling decoy (`Or([core, decoy])`,
/// `Implies(Not(decoy), core)`) can be reconstructed — a formula outside the vocabulary
/// simply fails the equate and the consumer DECLINES (fail-closed; costs certificates,
/// never soundness). Byte-identical to the producer-validated replay (28/28
/// reconstructions over the committed `trust-vcgen` fixtures) and to the trust-ir twin
/// `trustir_safety::reconstruct_obligation`.
pub(super) fn reconstruct_obligation(
    rec: &trust_types::ObligationRecord,
) -> trust_types::Formula {
    use trust_types::{Formula as F, ObligationWrapper as W, PathGuardTerm as P};
    let mut cur = rec.body.clone();
    for w in &rec.wrappers {
        cur = match w {
            W::ConjoinFactsLast { facts } => {
                let mut v = facts.clone();
                v.push(cur);
                F::And(v)
            }
            W::PathGuardOr { paths } => {
                let terms: Vec<F> = paths
                    .iter()
                    .map(|p| match p {
                        P::Raw => cur.clone(),
                        P::Guarded { guards } => {
                            let mut c = guards.clone();
                            match cur.clone() {
                                F::And(inner) => c.extend(inner),
                                other => c.push(other),
                            }
                            F::And(c)
                        }
                    })
                    .collect();
                match terms.len() {
                    0 => cur,
                    1 => terms.into_iter().next().expect("len checked == 1"),
                    _ => F::Or(terms),
                }
            }
        };
    }
    cur
}

/// Trust: THE VERTICAL-SLICE OBLIGATION GATE (2026-07-31, FIELD-REQUIRED). Every safety
/// arm now certifies off the emitter's RECORDED obligation, admitted ONLY when it
/// reconstructs to `vc.formula` bit-for-bit. The two dispositions the fail-closed contract
/// requires:
///
///   * AUTHENTICATED — the emitter RECORDED an obligation and it AUTHENTICATES
///     (`reconstruct_obligation(rec) == vc.formula`). The recorded body is what the arm
///     certifies: a field read no wrapper spelling can fool, because the equate proves
///     `vc.formula` IS that body wrapped by the closed vocabulary (no `Implies`, no `Not`,
///     no free-disjunct ⇒ R17 is structurally closed).
///   * DECLINE — NO obligation was recorded, OR one is recorded but does NOT reconstruct.
///     Both fail closed: the PEEL IS GONE, so an unrecorded (legacy/unmigrated/unmodeled)
///     obligation and a hostile/desynchronised claim alike decline. `None` return ⇒ no
///     certificate, never a fallback that a benign `obligation` paired with a violable
///     `formula` could slip through.
///
/// This REPLACES the former `ObligationSelection`/`select_obligation` three-way, whose
/// `Peel` fallback existed only while producers were being migrated. All five remaining
/// producers are migrated, so the fallback is deleted and the field is REQUIRED.
fn authenticated_record(
    vc: &trust_types::VerificationCondition,
) -> Option<&trust_types::ObligationRecord> {
    let rec = vc.obligation.as_ref()?;
    (reconstruct_obligation(rec) == vc.formula).then_some(rec)
}

/// Whether the record's conjoined FACTS pin `term ≥ 0` — the authenticated replacement for
/// the sibling-conjunct read the deleted peel used for the unsigned-overflow vacuity side
/// condition. The emitter demoted each operand range to a `ConjoinFactsLast` wrapper
/// (`generate/overflow_vc.rs` `v2_arith_overflow_seed_record`), which is INNERMOST and so
/// shared across every path-guard disjunct: one check over the record's facts covers every
/// occurrence the peel's universal used to quantify over, and it is read off the
/// authenticated record rather than off a guessed sibling list.
fn record_pins_nonneg(
    rec: &trust_types::ObligationRecord,
    term: &trust_types::Formula,
) -> bool {
    rec.wrappers.iter().any(|w| match w {
        trust_types::ObligationWrapper::ConjoinFactsLast { facts } => {
            has_nonneg_range_sibling(facts, term)
        }
        trust_types::ObligationWrapper::PathGuardOr { .. } => false,
    })
}

/// Kernel-check that the LIVE grounding of `cg.core` (via `clean_ground::ground_prop`)
/// is def-eq, modulo the 3 foundational axioms, to the spec term `spec` (already built
/// over the SAME de-Bruijn refs). This is the bridge check: it certifies the term the
/// reflection pipeline ACTUALLY grounds equals the pinned machine-semantics condition,
/// not a hand-built shape. Returns `true` ONLY on a real modulo-3 kernel def-eq.
pub(super) fn live_ground_def_eq_spec(cg: &CoreGround<'_>, spec: &Expr, binder_count: usize) -> bool {
    let Ok(mut env) = mirsem_safety_env() else {
        return false;
    };
    let Some(grounded) = crate::clean_ground::ground_prop(cg.core, &cg.params) else {
        return false; // the live grounder declined this core ⇒ no cert (fail closed)
    };
    // Kernel-register `theorem … : @Eq Prop grounded spec := Eq.refl Prop grounded`,
    // under `binder_count` Int binders (the operands). It type-checks IFF `grounded`
    // and `spec` are def-eq; then audit the axiom closure ⊆ the 3 axioms.
    let bd = || BinderData::from(BinderInfo::Default);
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let mut statement = Expr::apps(eq, [Expr::prop(), grounded.clone(), spec.clone()]);
    let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]);
    let mut proof = Expr::apps(eq_refl, [Expr::prop(), grounded]);
    for _ in 0..binder_count {
        statement = Expr::pi(bd(), int_ty(), statement);
        proof = Expr::lam(bd(), int_ty(), proof);
    }
    {
        let tc = TypeChecker::new(&env);
        if tc.check_type(&proof, &statement).is_err() {
            return false; // NOT def-eq ⇒ the emitted core is not the spec ⇒ fail closed
        }
    }
    let name = Name::from_string("Trust.MirSem.FormulaAware.bridge");
    if env
        .add_decl(Declaration::Theorem {
            name: name.clone(),
            level_params: vec![],
            type_: statement,
            value: proof,
        })
        .is_err()
    {
        return false;
    }
    matches!(env.axiom_deps(&name), Some(residue) if residue.is_empty())
}

/// Whether an integer operand `Formula` is in the formula-aware fragment — a bare
/// `Var` (mapped to a de-Bruijn binder) OR an integer CONSTANT `Int(k)` (grounded
/// directly to a closed literal by the live `ground_int`, no binder). These are the
/// operand shapes `x + y`, `x + 1`, `1 + x` produce; a nested arithmetic / field /
/// pointer operand is OUTSIDE the fragment ⇒ the caller fails closed.
pub(super) fn operand_in_fragment(t: &trust_types::Formula) -> bool {
    use trust_types::Formula as F;
    matches!(t, F::Var(_, _) | F::Int(_) | F::UInt(_))
}

/// The two operand `Formula`s of a computed binary sub-term `Add(a,b)` / `Sub(a,b)`,
/// in order — the OVERFLOW-family violation cores carry the operands inside this
/// computed result, not as bare comparison leaves. Each operand may be a `Var` OR an
/// integer constant (`x + 1`); a nested-arithmetic / field operand is OUT of the
/// fragment ⇒ `None` (fail closed).
pub(super) fn binop_operands(
    t: &trust_types::Formula,
) -> Option<(&trust_types::Formula, &trust_types::Formula)> {
    use trust_types::Formula as F;
    match t {
        // `Mul` is included so the formula-aware signed-overflow bridge can extract the
        // operands of a CONSTANT-multiplier mul's LIA `Or([Lt(Mul…),Gt(Mul…)])` core
        // (`ground_int` grounds `F::Mul` to `Int.mul`). A `var*var` mul is NOT emitted as
        // an `F::Mul`-cored disjunction (it is a BV formula), so this never spuriously
        // matches the deferred BV shape.
        F::Add(a, b) | F::Sub(a, b) | F::Mul(a, b)
            if operand_in_fragment(a) && operand_in_fragment(b) =>
        {
            Some((a, b))
        }
        _ => None,
    }
}

/// The term an `input_range_constraint` constrains, with its LOWER bound.
/// `trust_vcgen::range::input_range_constraint` builds VERBATIM
/// `And([Le(Int lo, t), Le(t, Int hi)])` (`range.rs:92-100`) — anything else is not one
/// and returns `None`.
fn range_constraint_parts(
    f: &trust_types::Formula,
) -> Option<(&trust_types::Formula, &trust_types::Formula)> {
    use trust_types::Formula as F;
    let F::And(v) = f else { return None };
    let [F::Le(lo, t_lo), F::Le(t_hi, hi)] = v.as_slice() else { return None };
    let is_lit = |x: &F| matches!(x, F::Int(_) | F::UInt(_));
    (is_lit(lo) && is_lit(hi) && t_lo == t_hi).then(|| (&**t_lo, &**lo))
}

/// Whether some conjunct of `sibs` is an `input_range_constraint` on `term` whose LOWER
/// end is exactly `0` — i.e. the emitter proved `term ≥ 0` alongside the violation, the
/// UNSIGNED operand range.
///
/// The ARITY of `sibs` is deliberately not fixed: a dominating path guard is FLATTENED
/// into the same `And` as the emitter's range/violation group
/// (`v2_formula_with_path_guards`, `generate/safety.rs:1110-1115`), so the group's own
/// conjuncts are siblings of the guards rather than a nested triple.
fn has_nonneg_range_sibling(sibs: &[trust_types::Formula], term: &trust_types::Formula) -> bool {
    use trust_types::Formula as F;
    sibs.iter().any(|s| {
        range_constraint_parts(s)
            .is_some_and(|(t, lo)| t == term && matches!(lo, F::Int(0) | F::UInt(0)))
    })
}

/// Trust: THE UNSIGNED-OVERFLOW BODY, SHAPE-MATCHED (2026-07-31, round-6) — the
/// load-bearing `Gt(a∘b, MAX)` disjunct of an unsigned add/mul obligation, taken from
/// the COLLAPSED body rather than searched for inside it.
///
/// Two admitted body shapes, both the emitter's own:
///
///   * `Gt(a∘b, Int MAX)` — the whole obligation IS the overflow comparison, so nothing
///     is discarded and there is nothing to prove vacuous;
///   * `Or([Lt(a∘b, 0), Gt(a∘b, Int MAX)])` — `generate/overflow_vc.rs:459-465`. Both
///     disjuncts must carry the SAME computed term, the discarded half must be against
///     `0`, and that half must be UNSATISFIABLE at every occurrence
///     ([`discarded_negative_disjunct_is_vacuous`]).
///
/// `head` is the arm's own computed-term test (`F::Add` for unsigned add, `F::Mul` for
/// unsigned mul). It is required in ADDITION to [`binop_operands`], which admits
/// `Add`/`Sub`/`Mul` alike: without it an `ArithmeticOverflow{Add, ..}` kind with a
/// `Gt(a-b, MAX)` body passes the shape test and reaches the def-eq bridge, leaving the
/// kernel as the only thing standing between it and a certificate. Whether the bridge
/// alone rejects it was NOT measured here — the point of the head test is that this arm
/// no longer needs that question answered. The direction is over-rejection, and it costs
/// nothing on the corpus: `certs=635` and the whole per-kind table are unchanged with it
/// in place.
///
/// ANY OTHER BODY DECLINES. In particular `Or([Gt(a∘b, MAX), Gt(z, 5)])` — the round-6
/// decoy — is not this shape, so the umul arm now returns `None` on it where it used to
/// descend and certify.
fn unsigned_overflow_over_disjunct<'a>(
    body: &'a trust_types::Formula,
    head: &dyn Fn(&trust_types::Formula) -> bool,
    vacuous: &dyn Fn(&trust_types::Formula, &trust_types::Formula) -> bool,
) -> Option<&'a trust_types::Formula> {
    use trust_types::Formula as F;
    match body {
        F::Gt(lhs, rhs)
            if head(lhs) && binop_operands(lhs).is_some() && matches!(&**rhs, F::Int(_)) =>
        {
            Some(body)
        }
        F::Or(v) => {
            let [F::Lt(under_t, zero_f), gt @ F::Gt(over_t, max_f)] = v.as_slice() else {
                return None;
            };
            if under_t != over_t || !matches!(&**zero_f, F::Int(0) | F::UInt(0)) {
                return None;
            }
            if !head(over_t) || binop_operands(over_t).is_none() || !matches!(&**max_f, F::Int(_)) {
                return None;
            }
            let (a_op, b_op) = binop_operands(over_t)?;
            vacuous(a_op, b_op).then_some(gt)
        }
        _ => None,
    }
}

/// Trust: MIXED-WIDTH NARROWING (2026-07-30, round-4 defect [2]) — whether an
/// `ArithmeticOverflow` VC whose two `operand_tys` have DIFFERENT widths is entitled to
/// the narrower one, given the operands the located violation core actually carries.
///
/// [`signed_overflow_vc_modeled`] certifies at `min(wa, wb)`. That rule exists for one
/// reason and it is a real one: `generate::type_ranges::int_op_type` (`type_ranges.rs:540-562`) takes
/// the operation's `(width, signed)` from a NON-CONSTANT operand, because
/// `operand_ty` fabricates `Ty::Int { width: 64, signed: true }` for a widthless
/// `ConstValue::Int` (`trust-vcgen/src/lib.rs:1237-1241`) — so `100i8 + x` emits an
/// i8-thresholded body under a kind that reads `(i64, i8)`, and demanding `wa == wb`
/// there would drop a genuine certificate. See the round-3 caveat recorded at
/// [`signed_overflow_vc_modeled`].
///
/// But `min()` makes the `vc.kind`-vs-formula width cross-check VACUOUS in exactly that
/// case: the round-4 verdict's recipe 4 is a kind of `(i64, i8)` with an i8-thresholded
/// body and TWO BARE `Var` operands, which mints `SignedOverflow(Add, W8)` for an
/// obligation nothing narrows. The committed regression tests all use same-width kinds,
/// where `min()` is the identity and the hole is invisible.
///
/// So when the widths differ, require the WIDER POSITION to be an integer LITERAL in the
/// located core — the constant that justifies the narrowing in the first place. The
/// position mapping is the emitter's own. Both producers that build the LIA
/// `Or([Lt(a∘b, MIN), Gt(a∘b, MAX)])` core this arm matches take `operand_tys` and the
/// computed `Add/Sub/Mul` from the SAME `(lhs, rhs)` pair in the SAME order:
/// `generate/overflow_vc.rs:428-434` + `:498` (the direct/checked BinaryOp Int path) and
/// `generate/panic_calls.rs:929-951` + `generate/safety.rs:292` (the
/// `unchecked_{add,sub,mul}` call path). `operand_to_formula` renders `ConstValue::Int(n)`
/// as `F::Int(n)` (`trust-vcgen/src/lib.rs:3253`).
///
/// If some FUTURE producer paired them the other way round, this check would look at the
/// wrong position and REFUSE — over-rejection, never over-acceptance: it can only turn a
/// grant into a decline, because equal widths short-circuit to `true` and the differing-
/// width branch is the only one that can return `false`.
///
/// EQUAL widths return `true` unconditionally — there is nothing to justify, and this
/// must not become a second, silent same-width restriction.
///
/// COST, MEASURED over `crates/trust-clean/fixtures` (2326 functions, 772 safety VCs):
/// **zero**. 49 signed `ArithmeticOverflow` VCs carry differing kind widths; 41 locate a
/// core and in ALL 41 the wider position is an `F::Int` literal, and the remaining 8
/// locate no core at all (they already decline upstream of this check). 0 rows are
/// `wider-position-is-not-a-literal`. Per-VC certificates 635 and functions certified 286,
/// unchanged.
fn mixed_width_narrowing_is_justified(
    kind: &trust_types::VcKind,
    a_op: &trust_types::Formula,
    b_op: &trust_types::Formula,
) -> bool {
    use trust_types::{Formula as F, Ty, VcKind as K};
    let K::ArithmeticOverflow { operand_tys: (a_ty, b_ty), .. } = kind else {
        return false; // not this kind ⇒ the caller has no business here (fail closed)
    };
    let (Ty::Int { width: wa, .. }, Ty::Int { width: wb, .. }) = (a_ty, b_ty) else {
        return false;
    };
    if wa == wb {
        return true; // `min` is the identity; the cross-check already has real content
    }
    let wider = if wa > wb { a_op } else { b_op };
    matches!(wider, F::Int(_) | F::UInt(_))
}

/// The distinct `Var` operand names of a list of operand `Formula`s, in first-
/// appearance order (a constant operand contributes no name — it grounds to a closed
/// literal, not a binder).
pub(super) fn distinct_var_names<'a>(operands: &[&'a trust_types::Formula]) -> Vec<&'a str> {
    let mut names: Vec<&str> = Vec::new();
    for op in operands {
        if let Some(n) = formula_var_name(op) {
            if !names.contains(&n) {
                names.push(n);
            }
        }
    }
    names
}

/// FORMULA-AWARE bridge for an OVERFLOW-family core whose operands appear inside a
/// COMPUTED `Add`/`Sub`/`Eq` sub-term (Lemma 2/5/6/8). Ground the EMITTED `core`
/// through the LIVE `clean_ground::ground_prop` and kernel-check it `is_def_eq`
/// (modulo 3) to `spec(g a, g b)` — where `g a`/`g b` are the operands grounded
/// through the SAME LIVE `ground_int` (a `Var` → its de-Bruijn binder; an integer
/// CONSTANT → its closed literal, NO binder), so the spec is built over the exact
/// operand terms the grounder produces (handling repeated operands `x + x` AND mixed
/// const operands `x + 1` uniformly). `spec_of(&[g_op])` builds the registered
/// per-kind predicate applied to those grounded operands. Returns `true` ONLY on a
/// genuine modulo-3 kernel def-eq; the live grounder declining the core/operand, or a
/// spec/grounder shape mismatch, fails closed.
pub(super) fn overflow_family_live_def_eq(
    core: &trust_types::Formula,
    operands: &[&trust_types::Formula],
    spec_of: &dyn Fn(&[Expr]) -> Expr,
) -> bool {
    // Distinct `Var` operand names → de-Bruijn binders (constants carry no binder).
    let distinct = distinct_var_names(operands);
    let params = debruijn_params(&distinct);
    // Ground each operand POSITION through the SAME live `ground_int`, so the spec is
    // applied to the exact de-Bruijn / literal terms the grounder emits.
    let mut grounded_ops: Vec<Expr> = Vec::with_capacity(operands.len());
    for op in operands {
        match crate::clean_ground::ground_int(op, &params) {
            Some(e) => grounded_ops.push(e),
            None => return false, // the live grounder declined this operand ⇒ fail closed
        }
    }
    let spec = spec_of(&grounded_ops);
    let cg = CoreGround { core, params };
    live_ground_def_eq_spec(&cg, &spec, distinct.len())
}

/// FORMULA-AWARE faithfulness for ONE safety VC: ground the ACTUAL emitted violation
/// core through the LIVE grounder and kernel-check it def-eq to the spec for THAT VC,
/// recovering the width/threshold FROM THE EMITTED FORMULA. Returns the modeled
/// `(kind, AdequacyVerdict)` ONLY when the bridge def-eq holds modulo 3; `None` (fail
/// closed) when the core is outside the formula-aware fragment OR the emitted threshold
/// does not match any modeled spec (e.g. the `1i32<<n` desync — emitted `32 ≤ n`, no
/// def-eq to a 64-width spec).
pub(super) fn safety_vc_is_faithful_formula_aware(
    func: &trust_types::VerifiableFunction,
    vc: &trust_types::VerificationCondition,
) -> Option<(SafetyVcKind, AdequacyVerdict)> {
    use trust_types::{Formula as F, VcKind as K};
    match &vc.kind {
        // BOUNDS (Lemma 3): the emitted core is `Ge(i, len)`. The INDEX is always a
        // variable; the LENGTH is a variable (a SLICE — `Var len`) OR a constant (a
        // FIXED ARRAY — `Int N`). Live-ground the WHOLE core → `Int.le (g len) (g i)`
        // and build the spec `idx_oob (g len) (g i)` over the SAME grounded operands, so
        // the array (`idx_oob (Int.ofNat N) i`) and slice (`idx_oob len i`) cases BOTH
        // certify by the same def-eq. The index binds at bvar 0; a length VARIABLE binds
        // at bvar 1 (so the proof carries 2 binders), a length CONSTANT carries no binder
        // (1 binder — just the index).
        K::IndexOutOfBounds | K::SliceBoundsCheck => {
            // Trust: OBLIGATION-REGION SELECTION (2026-07-29) — read THIS VC's own
            // emitted violation (`v2_build_bounds_assert_vc`'s `Ge(i, len)` /
            // `Or([Lt(i,0), Ge(i,len)])`), not the first `Ge(var, var|int)` anywhere
            // in the wrapped formula. 30 of the corpus's 35 bounds VCs selected a
            // HYPOTHESIS under the old scan — 26 of them the extractor's synthesized
            // `Ge(p, 0)` parameter-domain precondition, which certified `idx_oob 0 p`
            // for functions whose obligation carries no modeled core at all.
            //
            // Trust: THE DROPPED SIGNED DISJUNCT (2026-07-31, round-5 defect [4]). For a
            // SIGNED index the emitted violation is `Or([Lt(i,0), Ge(i,len)])`
            // (`generate/checked_vcs.rs:259`) and the leaf search below descends `Or`s,
            // so it returned the `Ge` disjunct and minted `SafetyVcKind::Bounds` for an
            // obligation strictly larger than `idx_oob len i`. Modeling the signed form
            // needs a spec constant and a kind variant this file does not own, so the
            // shape is DECLINED — the same disposition `trustir_safety.rs` records for
            // it. See [`carries_signed_index_violation`].
            //
            // Trust: THE BODY IS SHAPE-MATCHED, NOT SEARCHED (2026-07-31, round-6 F1).
            // This arm used to hand its `Ge(i, len)` predicate to the since-deleted
            // `obligation_violation_leaf`, which DESCENDED the peeled body. MEASURED on
            // the tree before this change: a body of `Or([Ge(i, len), Gt(z, 5)])` —
            // strictly weaker than `idx_oob len i` — minted `Some(Bounds)`, and so did
            // every blacklisted decoy wrapped in the same disjunction. The predicate is
            // now asked about the COLLAPSED body (`locate_violation`) and that recipe
            // returns `None`, which is what the trust-ir lane has always returned.
            // Trust: AUTHENTICATED OBLIGATION (2026-07-31, FIELD-REQUIRED). The bounds core
            // is the emitter's RECORDED body (`v2_build_bounds_assert_vc`'s `Ge(i, len)` /
            // signed `Or([Lt(i,0), Ge(i,len)])`, block-defs demoted to `ConjoinFactsLast`),
            // admitted only when it reconstructs to `vc.formula`. No peel: an unrecorded or
            // unfaithful obligation declines. The signed `Or` form and the bare
            // assert-condition body fail the `Ge` shape below and decline (the signed shape
            // is the declined kind gap, unchanged).
            let rec = authenticated_record(vc)?;
            let leaf = &rec.body;
            if carries_signed_index_violation(leaf) {
                return None;
            }
            if !matches!(leaf, F::Ge(a, b)
                if formula_var_name(a).is_some()
                    && (formula_var_name(b).is_some() || matches!(&**b, F::Int(_))))
            {
                return None;
            }
            let F::Ge(i_f, len_f) = leaf else { return None };
            let i_name = formula_var_name(i_f)?;
            // Bind the index at bvar 0; the length VARIABLE (if any) at bvar 1.
            let (params, binder_count, len_expr) = match formula_var_name(len_f) {
                Some(len_name) => {
                    let mut m = std::collections::HashMap::new();
                    m.insert(len_name.to_string(), Expr::bvar(1));
                    m.insert(i_name.to_string(), Expr::bvar(0));
                    (m, 2usize, Expr::bvar(1))
                }
                None => {
                    let F::Int(n) = &**len_f else { return None };
                    let mut m = std::collections::HashMap::new();
                    m.insert(i_name.to_string(), Expr::bvar(0));
                    (m, 1usize, int_lit(*n))
                }
            };
            let cg = CoreGround { core: leaf, params };
            // spec `idx_oob (g len) i` over the SAME grounded length term + index bvar.
            let spec = Expr::apps(cst(MIRSEM_IDX_OOB), [len_expr, Expr::bvar(0)]);
            live_ground_def_eq_spec(&cg, &spec, binder_count)
                .then_some((SafetyVcKind::Bounds, AdequacyVerdict::ProvenModulo3))
        }
        // DIV / REM by zero (Lemma 4/9): the emitted core is `Eq(b, 0)` (divisor zero).
        // Live-ground → `@Eq Int b (Int.ofNat 0)`; spec `div_by_zero b` / `rem_by_zero b`.
        K::DivisionByZero | K::RemainderByZero => {
            // Trust: OBLIGATION-REGION SELECTION (2026-07-29) — the statement-driven
            // `v2_divisor_is_zero_formula` emits `Eq(b, 0)` as the body; the
            // ASSERT-driven twin emits the bare condition local `Var(c)` and binds the
            // core in `Eq(Var c, Eq(b, 0))`, resolved by name. Scanning the WHOLE
            // formula instead certified the assert twin off an unrelated block-def
            // (`Eq(__trust_opaque_scalar_u64, 0)` in `bit_field::BitArray::get_bit`,
            // whose own obligation is `Var("_4", Bool)`).
            //
            // Trust: THE BODY IS SHAPE-MATCHED, NOT SEARCHED (2026-07-31, round-6 F1).
            // `assert_bound_or_body_core`'s first route used to descend the peeled
            // body. MEASURED before this change: a body of `Or([Eq(b, 0), Gt(z, 5)])`
            // minted `Some(DivByZero)` / `Some(RemByZero)` for an obligation that says
            // only `b = 0 ∨ z > 5`. The assert route is untouched — it resolves the bare
            // `Var(_c)` body against the MIR's own binding, which is a position, not a
            // search.
            let is_core = |f: &F| {
                matches!(f, F::Eq(a, b) if formula_var_name(a).is_some() && matches!(&**b, F::Int(0)))
            };
            // Trust: AUTHENTICATED OBLIGATION (2026-07-31, vertical slice ARM 1). Read the
            // emitter's RECORDED obligation body instead of guessing it out of the wrapped
            // formula. `Authenticated` ⇒ `reconstruct_obligation == vc.formula`, so the
            // recorded body is provably `vc.formula`'s own core; `Peel` ⇒ no record
            // (legacy dumps / unmigrated producers), fall back to the peel; `Decline` ⇒ a
            // recorded-but-unfaithful (hostile) claim ⇒ fail closed, never peel.
            let rec = authenticated_record(vc)?;
            let (leaf, _) = assert_bound_or_body_core_with(func, &vc.formula, &rec.body, &is_core)?;
            let F::Eq(b_f, _) = leaf else { return None };
            let b_name = formula_var_name(b_f)?;
            let params = debruijn_params(&[b_name]);
            let cg = CoreGround { core: leaf, params };
            let (spec_name, kind) = if matches!(vc.kind, K::DivisionByZero) {
                (MIRSEM_DIV_BY_ZERO, SafetyVcKind::DivByZero)
            } else {
                (MIRSEM_REM_BY_ZERO, SafetyVcKind::RemByZero)
            };
            let spec = Expr::app(cst(spec_name), Expr::bvar(0));
            live_ground_def_eq_spec(&cg, &spec, 1).then_some((kind, AdequacyVerdict::ProvenModulo3))
        }
        // SHIFT-amount OOB (Lemma 7): the emitted core is `Ge(n, Int(W))` (unsigned
        // amount) — W is the EMITTED threshold, read from the formula (NOT operand_ty,
        // which fabricates i64 for a const shifted value). Live-ground → `Int.le W n`;
        // spec `shift_amount_oob_W n`. The width is whatever the formula actually says,
        // so the `1i32<<n` emitted `32 ≤ n` certifies at W32 and NEVER mints a 64-cert.
        // A signed shift amount adds the `Lt(n,0)` disjunct (the `Or` core).
        K::ShiftOverflow { shift_ty, .. } => {
            let amount_signed = matches!(shift_ty, trust_types::Ty::Int { signed: true, .. });
            // Trust: SHIFT-CORE SELECTION (2026-07-29) — take THIS VC's OWN emitted
            // violation, rather than the first `Ge(var|int, Int)` leaf anywhere in the
            // WRAPPED formula. That old scan read the hypothesis side — the function's
            // `preconditions`, its parameters' type bounds, the dominating guards — and
            // so both lost real certificates (`bit_field::get_bit`'s `Ge(bit,0)`
            // precondition, −12) and minted false ones (a `Ge(_,32)` precondition
            // certifying `ShiftOob(W32)` on a `u8` body).
            //
            // Trust: lane A round-3 finding [1]/[2] (2026-07-29) — the region is
            // `emitted_obligation_body`, exactly as at the other seven sites. The
            // interim repair matched the emitter's `And([range, invalid])` PAIR but
            // still scanned the whole `vc.formula` for it (descending `Not` and
            // `Implies` too), and shape without position is forgeable: MEASURED,
            // `And([pair, Bool(true)])` — an obligation whose own body is the emitter's
            // fail-closed `Bool(true)` marker — minted `ShiftOob(W32, false)` off the
            // hypothesis conjunct, as did `Not(pair)` and `Implies(pair, Bool(true))`.
            // The peel is also strictly WIDER: `v2_formula_with_path_guards` FLATTENS
            // an `And`-shaped body into the guarded term (`generate/safety.rs:1115`),
            // destroying the 2-element pair, so a shift under a dominating guard emits
            // `And([guard, And([Le,Le]), Ge(n,W)])` — pair `None`, body `Ge(n,W)`. The
            // pair matcher survives as the `#[cfg(test)]` cross-check
            // `emitted_shift_violation_pair_probe`; the two agree on 77/77 ladder rows.
            //
            // The amount `n` is a VARIABLE (the original Lemma-7 shape) or — Trust: M6
            // rung 6 — a CLOSED LITERAL (`x >> 44`'s emitted `Ge(Int(44), Int(64))`,
            // the `ExprMeta::loose_bvar_range`-class constant shift: the core is a
            // CLOSED Prop, its reflection is `Int.le (ofNat W) (ofNat k)`, and the spec
            // is `shift_amount_oob_W k` applied at the literal — the SAME def-eq
            // bridge, zero binders). UNSIGNED amounts only for the literal arm (a
            // signed literal amount would need the `Or` core located at a literal too —
            // not observed in real MIR, fail-closed).
            // Trust: AUTHENTICATED OBLIGATION (2026-07-31, FIELD-REQUIRED). The shift core
            // is the emitter's RECORDED body (`v2_shift_overflow_seed_record`: atomic
            // `Ge(n,W)` / signed `Or([Lt(n,0), Ge(n,W)])`, `shift_range` demoted to a
            // `ConjoinFactsLast` fact), admitted only when it reconstructs to `vc.formula`.
            let rec = authenticated_record(vc)?;
            let core = &rec.body;
            let (n_f, threshold, signed_form) = shift_violation_shape(core)?;
            // The emitted violation's FORM must agree with the VC's own `shift_ty`: a
            // signed amount emits the `Or([Lt(n,0), Ge(n,W)])` disjunction, an unsigned
            // one the bare `Ge(n,W)`. A disagreement means the located violation is not
            // the one this VcKind describes ⇒ fail closed.
            if signed_form != amount_signed {
                return None;
            }
            // The EMITTED threshold W must be a modeled shift-width literal
            // (`8/16/32/64/128` — the 128-bit value widths ARE in this lane's set).
            //
            // Trust: NO WIDTH CROSS-CHECK HERE — a DELIBERATE, MEASURED omission, and
            // the four OTHER width-from-formula arms do make one (lane A round-3
            // finding [5]). `shift_vc_modeled` reads the width off `operand_ty`, and for
            // a CONSTANT shifted value (`1i32 << bit`) the extractor fabricates i64
            // there, so the kind's width and the emitted threshold disagree on real
            // rows.
            //
            // SCOPE OF THE OMISSION, RE-MEASURED (2026-07-30, round-4 defect [3]) over
            // the LADDER (`fixtures/census-2026-07-06` + `fixtures/census-rung2-2026-07-07`):
            // 77 shift VCs, every one of which locates a `shift_violation_shape`.
            // `(operand_ty width, emitted threshold)`, exhaustively —
            //
            //     agree:    (8,8) 3   (16,16) 3   (32,32) 27   (64,64) 20   (128,128) 12
            //     disagree: (64,8) 3  (64,16) 3   (64,32) 3    (64,128) 3
            //
            // i.e. 12 of 77 disagree. (The previous text's attribution of all twelve to
            // the `bit_field` `<i8|i16|i32|i128 as BitField>::get_bit`/`::set_bit` rows
            // is CARRIED OVER, not re-measured — this pass re-measured the pair census
            // above, not the row identities.) The previous text stopped at the bare
            // "12 of 77"; the DIRECTION matters and is NOT one-sided:
            // 9 rows are KIND-WIDER (64 against 8/16/32) and 3 are KIND-NARROWER
            // (64 against 128, the i128 `BitField` rows). So neither a one-sided
            // `kind_w >= threshold` nor a one-sided `kind_w <= threshold` is available:
            // the first drops the 3 i128 rows, the second drops the other 9, and
            // equality drops all 12 — contradicting `shift_core_selection_tests::
            // bit_field_get_bit_certifies_its_own_shift_width_under_a_ge_spelled_
            // precondition`, which pins the EMITTED threshold as the honest one.
            // (Over the whole `crates/trust-clean/fixtures` tree: 133 shift VCs, of
            // which 12 disagree with the same `(operand_ty width, emitted threshold)`
            // pair distribution. Whether they are literally the same twelve rows was
            // NOT measured — see the CARRIED OVER note above.)
            //
            // Trust: MATCHED DEFERRAL (2026-07-31, round-5 defect [3]). This omission is
            // OPEN IN BOTH CERTIFICATE LANES and is deliberately left open in both, in
            // the same shape, this round: the honest matched deferral the round-5 defect
            // list names as the acceptable outcome for [3], as against an undocumented
            // asymmetry. It was previously documented HERE and not in `trustir_safety.rs`
            // — that asymmetry is what this paragraph closes. Nothing about the omission
            // changed; what changed is that both lanes now say so.
            //
            // WHAT IS AND IS NOT CLAIMED. This is not "the kind and the formula agree";
            // they measurably do not. It is that `operand_ty` is not evidence about the
            // certified width in EITHER direction here, so no sound comparison against
            // it exists — closing the gap needs the EMITTER to record the true shifted
            // width in the `VcKind`, which is a trust-vcgen change and is deliberately
            // NOT attempted from this side. Until then the certified width comes from
            // the emitted threshold and from the region-selected body alone, and the
            // kind cross-check this arm CAN make is signedness, which it makes above.
            let w = ShiftWidth::from_bits(u32::try_from(threshold).ok()?)?;
            // Trust: (D)/(E) AUTHENTICATED SUBJECT/WIDTH (2026-07-31, the [10] fix). The
            // record carries the TRUE shifted-operand width (threaded from MIR by the
            // emitter, NOT the fabricated `operand_ty`) and the shift amount as its subject.
            // The recorded width must equal the emitted threshold `W` — which the emitter
            // records as exactly that true shifted width — and a recorded plain-`Var`
            // subject must name the shift amount. This is the width cross-check the peel era
            // deliberately left open, now closed by the recorded MIR authority; a mismatch
            // is a desynchronised record ⇒ fail closed.
            if let Some(rec_w) = rec.width {
                if i128::from(rec_w) != threshold {
                    return None;
                }
            }
            if let Some(rec_subject) = rec.subject.as_ref() {
                if let (Some(rs), Some(ns)) = (base_var_name(rec_subject), base_var_name(n_f)) {
                    if rs != ns {
                        return None;
                    }
                }
            }
            // Trust: M6 rung 6 — the CLOSED-LITERAL amount arm (unsigned only).
            if let F::Int(k) = n_f {
                if amount_signed {
                    return None; // literal-amount signed shift — outside the arm.
                }
                let cg = CoreGround { core, params: std::collections::HashMap::new() };
                let spec = Expr::app(cst(&shift_amount_oob_name(w, amount_signed)), int_lit(*k));
                return live_ground_def_eq_spec(&cg, &spec, 0).then_some((
                    SafetyVcKind::ShiftOob(w, amount_signed),
                    AdequacyVerdict::ProvenModulo3,
                ));
            }
            let n_name = formula_var_name(n_f)?;
            let params = debruijn_params(&[n_name]);
            let cg = CoreGround { core, params };
            let spec = Expr::app(cst(&shift_amount_oob_name(w, amount_signed)), Expr::bvar(0));
            live_ground_def_eq_spec(&cg, &spec, 1).then_some((
                SafetyVcKind::ShiftOob(w, amount_signed),
                AdequacyVerdict::ProvenModulo3,
            ))
        }
        // ARITHMETIC OVERFLOW / UNDERFLOW (Lemma 2/5/8). The violation core carries a
        // COMPUTED `Add(a,b)`/`Sub(a,b)` sub-term (not bare comparison Vars). We
        // discriminate the three modeled shapes by the EMITTED formula itself —
        // operand signedness from the VC's `operand_tys` only selects WHICH shape to
        // look for; the threshold (hence the certified width) is read FROM THE FORMULA.
        K::ArithmeticOverflow { op, operand_tys: (a_ty, b_ty) } => {
            use trust_types::{BinOp, Ty};
            let (Ty::Int { signed: sa, .. }, Ty::Int { signed: sb, .. }) = (a_ty, b_ty) else {
                return None;
            };
            match op {
                // UNSIGNED-ADD OVERFLOW (Lemma 2): the load-bearing disjunct is
                // `Gt(Add(a,b), Int(MAX))` (MAX = 2^w−1) inside the emitted 2-element
                // `Or`. Read MAX from the formula → the modeled UWidth; ground the
                // overflow disjunct live and check def-eq to `uadd_overflows_uW (g a) (g b)`.
                BinOp::Add if !sa && !sb => {
                    // Trust: OBLIGATION-REGION SELECTION (2026-07-29) — 9 of the
                    // corpus's 36 unsigned-add VCs read a HYPOTHESIS here. `itoa`'s
                    // `<i16 as Sealed>::write` raises a u8 add whose own violation is
                    // `Gt(_63 + 48, 255)`, and the whole-tree scan took the semantic
                    // guard `Gt(_43 + 2, u64::MAX)` — minting `Overflow(U64)` for an
                    // 8-bit addition, on unmodified real library code.
                    //
                    // Trust: PARTIAL ADEQUACY, MADE A CHECK (2026-07-31, round-5
                    // defects [5]/[6]). The emitted violation is the two-disjunct
                    // `Or([Lt(a+b, 0), Gt(a+b, MAX)])` and `uadd_overflows_uW` models
                    // the `Gt` half only, so the body is now matched as a SHAPE — the
                    // discarded half must be `Lt` over the SAME computed sum against
                    // `0` — and the vacuity of that half is a REQUIRED side condition
                    // over EVERY occurrence of the body
                    // ([`discarded_negative_disjunct_is_vacuous`]). This lane previously
                    // read the `Gt` out of the `Or` with the since-deleted
                    // `obligation_violation_leaf` and certified half the proposition at
                    // every uadd row.
                    //
                    // Trust: THIS ARM IS THE ROUND-6 MODEL (2026-07-31). It was already a
                    // SHAPE MATCH on the collapsed body, so it declined the
                    // `Or([<core>, Gt(z,5)])` decoy that the other six arms minted; F1
                    // copies the discipline outward and the match itself is now the
                    // shared [`unsigned_overflow_over_disjunct`], which the unsigned-MUL
                    // arm calls with `F::Mul` in place of `F::Add`.
                    // Trust: AUTHENTICATED OBLIGATION (2026-07-31, FIELD-REQUIRED). The
                    // out-of-range core is the emitter's RECORDED body
                    // (`Or([Lt(a+b,0), Gt(a+b,MAX)])`, operand ranges demoted to
                    // `ConjoinFactsLast`), admitted only when it reconstructs to
                    // `vc.formula`. The vacuity of the discarded `Lt(a+b,0)` half — which
                    // makes the `Gt`-only spec adequate — is checked against the record's
                    // own conjoined operand ranges ([`record_pins_nonneg`]), the innermost
                    // wrapper shared across every path, so the peel's occurrence-universal
                    // collapses to one authenticated check.
                    let rec = authenticated_record(vc)?;
                    let leaf = unsigned_overflow_over_disjunct(
                        &rec.body,
                        &|t| matches!(t, F::Add(_, _)),
                        &|a, b| record_pins_nonneg(rec, a) && record_pins_nonneg(rec, b),
                    )?;
                    let F::Gt(add_t, max_f) = leaf else { return None };
                    let (a_op, b_op) = binop_operands(add_t)?;
                    let F::Int(max) = &**max_f else { return None };
                    let w = UWidth::from_mir(width_of_unsigned_max(*max)?, false)?;
                    // Trust: WIDTH CROSS-CHECK (2026-07-29, lane A round-3 finding [5]).
                    // The certified width is read from the FORMULA's threshold; the VC's
                    // own `operand_tys` carries it INDEPENDENTLY. They must agree, exactly
                    // as the shift arm requires the located form's signedness to agree
                    // with `shift_ty`. Without it, MEASURED against `probe_func()`:
                    // `kind = ArithmeticOverflow{Add, (u8,u8)}` with body
                    // `Gt(a+b, 18446744073709551615)` minted `Some(Overflow(W64))` — a
                    // kernel-checked claim that an 8-bit addition is a 64-bit one.
                    // COST: zero. Over the 486 committed dumps the kind width and the
                    // formula width disagree on 0 of the 265 certificates at all four
                    // width-from-formula arms.
                    if overflow_vc_modeled_width(&vc.kind) != Some(w) {
                        return None;
                    }
                    // Trust: (E) AUTHENTICATED WIDTH (2026-07-31). The record carries the
                    // REAL operand width (`int_op_type`, not `min(wa,wb)`); it must equal the
                    // width recovered from the emitted `MAX` threshold. Fail closed on
                    // mismatch.
                    if let Some(rec_w) = rec.width {
                        if rec_w != w.bits() {
                            return None;
                        }
                    }
                    let name = uadd_overflows_name(w);
                    let ok = overflow_family_live_def_eq(leaf, &[a_op, b_op], &|ops| {
                        Expr::apps(cst(&name), [ops[0].clone(), ops[1].clone()])
                    });
                    ok.then_some((SafetyVcKind::Overflow(w), AdequacyVerdict::ProvenModulo3))
                }
                // SIGNED ADD/SUB/MUL OVERFLOW (Lemma 5): the full out-of-range `Or([Lt(a∘b,
                // MIN), Gt(a∘b, MAX)])`. Read MIN+MAX from the formula → the modeled
                // SWidth (and confirm they agree); ground the whole `Or` live and check
                // def-eq to `s<op>_overflows_iW (g a) (g b)`.
                //
                // MUL is included ADDITIVELY: a CONSTANT-multiplier signed mul (`x * 4`)
                // is emitted by trust-vcgen on the LIA Int-path as the SAME
                // `Or([Lt(Mul(a,b),MIN), Gt(Mul(a,b),MAX)])` disjunction, so it certifies
                // by the identical reflexivity (the spec body just heads `Int.mul`). A
                // `var*var` signed mul is emitted as a BITVECTOR formula instead, which has
                // NO such `Or([Lt(Mul…),Gt(Mul…)])` leaf — `find_violation_leaf` returns
                // `None` below ⇒ this arm declines ⇒ the deferred BV mul fails closed (no
                // false cert; the `mul_*`/`sq_nonneg` corpus stays HONESTLY not-faithful).
                BinOp::Add | BinOp::Sub | BinOp::Mul if *sa && *sb => {
                    let sop = match op {
                        BinOp::Add => SignedOp::Add,
                        BinOp::Sub => SignedOp::Sub,
                        _ => SignedOp::Mul,
                    };
                    // Trust: OBLIGATION-REGION SELECTION (2026-07-29) — the corpus shows
                    // 0 disagreements at this site today, but the shape is reachable
                    // from a hypothesis: `#[requires] a + b < -128 || a + b > 127` on an
                    // i32 body mints `SignedOverflow(Add, W8)` (pinned by
                    // `a_precondition_can_never_supply_the_certified_signed_width`).
                    //
                    // Trust: THE BODY IS SHAPE-MATCHED, NOT SEARCHED (2026-07-31,
                    // round-6 F1). The predicate below used to be handed to the
                    // since-deleted `obligation_violation_leaf`, which descended the
                    // peeled body — so a NESTED `Or`, `Or([Or([Lt(a+b,MIN),
                    // Gt(a+b,MAX)]), Gt(z,5)])`, had its inner disjunction located and
                    // certified. MEASURED before this change: `Some(SignedOverflow(Add,
                    // W8))` for an obligation stating the disjunction OR `z > 5`. Asking
                    // the SAME predicate about the COLLAPSED body declines it: the outer
                    // `Or` has two disjuncts but its first is not an `Lt`.
                    // Trust: AUTHENTICATED OBLIGATION (2026-07-31, FIELD-REQUIRED). The
                    // out-of-range core is the emitter's RECORDED body
                    // (`Or([Lt(a∘b,MIN), Gt(a∘b,MAX)])`, operand ranges demoted to
                    // `ConjoinFactsLast`), admitted only when it reconstructs to
                    // `vc.formula`.
                    let rec = authenticated_record(vc)?;
                    let or = &rec.body;
                    if !matches!(or, F::Or(v) if v.len() == 2
                        && matches!(&v[0], F::Lt(l, r)
                            if binop_operands(l).is_some() && matches!(&**r, F::Int(_)))
                        && matches!(&v[1], F::Gt(l, r)
                            if binop_operands(l).is_some() && matches!(&**r, F::Int(_))))
                    {
                        return None;
                    }
                    let F::Or(v) = or else { return None };
                    let (F::Lt(under_t, min_f), F::Gt(over_t, max_f)) = (&v[0], &v[1]) else {
                        return None;
                    };
                    // Both disjuncts must reference the SAME computed `a∘b` operands.
                    let (a_op, b_op) = binop_operands(under_t)?;
                    if binop_operands(over_t)? != (a_op, b_op) {
                        return None;
                    }
                    let (F::Int(min), F::Int(max)) = (&**min_f, &**max_f) else { return None };
                    let w = swidth_of_signed_bounds(*min, *max)?;
                    // Trust: WIDTH CROSS-CHECK (2026-07-29, lane A round-3 finding [5]).
                    // Without it, MEASURED: `kind = ArithmeticOverflow{Add, (i32,i32)}`
                    // with body `Or([Lt(a+b,-128), Gt(a+b,127)])` minted
                    // `Some(SignedOverflow(Add, W8))`. The comparison is against the WHOLE
                    // `(op, width)` pair, so the located disjunction's op is pinned too.
                    //
                    // MEASURED BEFORE APPLIED, because `signed_overflow_vc_modeled` takes
                    // `min(wa, wb)` on purpose (an untyped integer constant operand
                    // defaults to i64, so the real check type is the narrower one):
                    // over the 486 committed dumps this equality holds for all 22 signed
                    // certificates — 0 disagreements — so the `min` rule and the emitted
                    // threshold are already byte-aligned and the check costs no row.
                    if signed_overflow_vc_modeled(&vc.kind) != Some((sop, w)) {
                        return None;
                    }
                    // Trust: MIXED-WIDTH NARROWING (2026-07-30, round-4 defect [2]).
                    // The cross-check above is satisfied BY CONSTRUCTION when the two
                    // kind widths differ, because `signed_overflow_vc_modeled` narrows
                    // to `min(wa, wb)`: a kind of `(i64, i8)` accepts an i8-thresholded
                    // body whatever the body's operands are. The narrowing is only
                    // legitimate for the reason `int_op_type` narrows — one operand is
                    // an untyped integer CONSTANT whose `operand_ty` fabricates i64 —
                    // so require the WIDER position to actually BE that constant.
                    if !mixed_width_narrowing_is_justified(&vc.kind, a_op, b_op) {
                        return None;
                    }
                    // Trust: (E) AUTHENTICATED WIDTH (2026-07-31). The record carries the
                    // REAL operand width (`int_op_type`, the signed mixed-width fix — NOT
                    // `min(wa,wb)`); it must equal the width recovered from the emitted
                    // `(MIN,MAX)`. Fail closed on mismatch.
                    if let Some(rec_w) = rec.width {
                        if rec_w != w.bits() {
                            return None;
                        }
                    }
                    let name = signed_overflows_name(sop, w);
                    let ok = overflow_family_live_def_eq(or, &[a_op, b_op], &|ops| {
                        Expr::apps(cst(&name), [ops[0].clone(), ops[1].clone()])
                    });
                    ok.then_some((
                        SafetyVcKind::SignedOverflow(sop, w),
                        AdequacyVerdict::ProvenModulo3,
                    ))
                }
                // UNSIGNED-SUB UNDERFLOW (Lemma 8): the single core `Lt(Sub(a,b),
                // Int(0))`. The underflow bound is `0` at EVERY width (the threshold
                // carries no width), and the spec body is width-invariant — so we ground
                // the live core and check def-eq to `usub_underflows_uW (g a) (g b)` for
                // the operand width the VC carries (sound: the def-eq holds at every
                // modeled width; the width only names the per-kind tally bucket).
                BinOp::Sub if !sa && !sb => {
                    let w = usub_underflow_vc_modeled(&vc.kind)?;
                    // Trust: OBLIGATION-REGION SELECTION (2026-07-29) — the width comes
                    // from the VC KIND here, so a hypothesis leaf would not forge the
                    // width; it would forge the OPERANDS, building the spec over a
                    // subtraction the obligation is not about.
                    //
                    // Trust: THE BODY IS SHAPE-MATCHED, NOT SEARCHED (2026-07-31,
                    // round-6 F1). MEASURED before this change: a body of
                    // `Or([Lt(a-b, 0), Gt(z, 5)])` minted
                    // `Some(UnsignedSubUnderflow(W8))`. The emitter's own body for this
                    // kind is the bare `Lt(a-b, 0)` — `overflow_vc.rs`'s unsigned-`Sub`
                    // special case, which is the ONE arm that does not build the
                    // two-disjunct `Or` — so requiring the collapsed body to BE it costs
                    // nothing: all 188 corpus certificates keep theirs.
                    // Trust: AUTHENTICATED OBLIGATION (2026-07-31, FIELD-REQUIRED). The
                    // underflow core is the emitter's RECORDED body (the unsigned-`Sub`
                    // special case's bare `Lt(a-b, 0)`, operand ranges demoted to
                    // `ConjoinFactsLast`), admitted only when it reconstructs to
                    // `vc.formula`.
                    let rec = authenticated_record(vc)?;
                    let leaf = &rec.body;
                    if !matches!(leaf, F::Lt(lhs, rhs)
                        if matches!(&**lhs, F::Sub(_, _))
                            && binop_operands(lhs).is_some()
                            && matches!(&**rhs, F::Int(0)))
                    {
                        return None;
                    }
                    let F::Lt(sub_t, _) = leaf else { return None };
                    let (a_op, b_op) = binop_operands(sub_t)?;
                    // Trust: (E) AUTHENTICATED WIDTH (2026-07-31). The width names the
                    // per-kind tally bucket (the `0` threshold carries none); the recorded
                    // REAL operand width must equal the VC kind's. Fail closed on mismatch.
                    if let Some(rec_w) = rec.width {
                        if rec_w != w.bits() {
                            return None;
                        }
                    }
                    let name = usub_underflows_name(w);
                    let ok = overflow_family_live_def_eq(leaf, &[a_op, b_op], &|ops| {
                        Expr::apps(cst(&name), [ops[0].clone(), ops[1].clone()])
                    });
                    ok.then_some((
                        SafetyVcKind::UnsignedSubUnderflow(w),
                        AdequacyVerdict::ProvenModulo3,
                    ))
                }
                // UNSIGNED-MUL OVERFLOW: the load-bearing disjunct is
                // `Gt(Mul(a,b), Int(MAX))` (MAX = 2^w−1) inside the emitted 2-element
                // `Or([Lt(Mul(a,b),0), Gt(Mul(a,b),MAX)])`. This is EXACTLY the
                // unsigned-ADD shape with `Mul` in place of `Add` — read MAX from the
                // formula → the modeled UWidth; ground the overflow disjunct live and
                // check def-eq to `umul_overflows_uW (g a) (g b)`.
                //
                // MUL is here for the CONSTANT-multiplier LIA emission only: trust-vcgen
                // routes `flag * 32` / `x * 4` (a constant operand, no widening cast) to
                // the Int path where `ground_int` grounds `F::Mul` to `Int.mul`. A
                // `var*var` unsigned mul is emitted as a BITVECTOR formula
                // (`And([a≠0, bvudiv(bvmul(a,b),a)≠b])`) — its body is not this shape at
                // all, so the shape match below returns `None` ⇒ this arm declines ⇒ the
                // deferred BV mul fails closed (no false cert; `wrapping_mul` and every
                // full-range product stay HONESTLY not-faithful). The MODELING here is
                // orthogonal to the DISCHARGE: even a certified-adequate `x*4` VC is
                // discharged only if `x*4 > MAX` refutes under the caller's facts (a
                // full-range `x` leaves it SAT ⇒ undischarged ⇒ SAFETY_GAP, never FF).
                BinOp::Mul if !sa && !sb => {
                    // Trust: OBLIGATION-REGION SELECTION (2026-07-29) — this is also the
                    // gate that keeps the `var*var` BV mul fail-closed: with the whole
                    // tree in scope, a hypothesis `Gt(Mul(a,b), Int MAX)` supplied the
                    // `Gt(Mul..)` leaf the BV obligation does not contain.
                    //
                    // Trust: THE UADD TWIN, FINALLY (2026-07-31, round-6 F1). This arm
                    // was the ONE leaf-under-body population left on this lane: the
                    // emitter's body is the two-disjunct
                    // `Or([Lt(a*b, 0), Gt(a*b, MAX)])` and this arm handed a `Gt(Mul..)`
                    // predicate to the since-deleted `obligation_violation_leaf`, which
                    // descended the `Or` and certified the `Gt` half — the SAME partial
                    // adequacy round 5 closed at unsigned-add and deferred here, plus the
                    // `Or([Gt(a*b, MAX), Gt(z, 5)])` decoy the descent also accepted
                    // (MEASURED: `Some(UnsignedMulOverflow(W8))`). Both close together by
                    // routing through [`unsigned_overflow_over_disjunct`], the unsigned-add
                    // arm's own matcher, with `F::Mul` for `F::Add`. COST: zero — all 51
                    // corpus certificates carry the `Or2-Lt0` shape and satisfy the
                    // vacuity condition, so `certs=635` is unchanged.
                    // Trust: AUTHENTICATED OBLIGATION (2026-07-31, FIELD-REQUIRED). The
                    // out-of-range core is the emitter's RECORDED body
                    // (`Or([Lt(a*b,0), Gt(a*b,MAX)])`, operand ranges demoted to
                    // `ConjoinFactsLast`), admitted only when it reconstructs to
                    // `vc.formula`. Vacuity of the discarded half is checked against the
                    // record's own conjoined ranges, exactly as the unsigned-add twin. A
                    // `var*var` BV mul records no such body ⇒ declines (honest deferral).
                    let rec = authenticated_record(vc)?;
                    let leaf = unsigned_overflow_over_disjunct(
                        &rec.body,
                        &|t| matches!(t, F::Mul(_, _)),
                        &|a, b| record_pins_nonneg(rec, a) && record_pins_nonneg(rec, b),
                    )?;
                    let F::Gt(mul_t, max_f) = leaf else { return None };
                    let (a_op, b_op) = binop_operands(mul_t)?;
                    let F::Int(max) = &**max_f else { return None };
                    let w = UWidth::from_mir(width_of_unsigned_max(*max)?, false)?;
                    // Trust: WIDTH CROSS-CHECK (2026-07-29, lane A round-3 finding [5]).
                    // Without it, MEASURED: `kind = ArithmeticOverflow{Mul, (u32,u32)}`
                    // with body `Gt(a*b, 255)` minted `Some(UnsignedMulOverflow(W8))`.
                    if umul_overflow_vc_modeled(&vc.kind) != Some(w) {
                        return None;
                    }
                    // Trust: (E) AUTHENTICATED WIDTH (2026-07-31). Recorded REAL operand
                    // width must equal the width recovered from the emitted `MAX`. Fail
                    // closed on mismatch.
                    if let Some(rec_w) = rec.width {
                        if rec_w != w.bits() {
                            return None;
                        }
                    }
                    let name = umul_overflows_name(w);
                    let ok = overflow_family_live_def_eq(leaf, &[a_op, b_op], &|ops| {
                        Expr::apps(cst(&name), [ops[0].clone(), ops[1].clone()])
                    });
                    ok.then_some((
                        SafetyVcKind::UnsignedMulOverflow(w),
                        AdequacyVerdict::ProvenModulo3,
                    ))
                }
                _ => None,
            }
        }
        // NEGATION OVERFLOW (Lemma 6): the core `Eq(Var x, Int(MIN))`. Read MIN from the
        // formula → the modeled SWidth; ground the live core and check def-eq to
        // `neg_overflows_iW (g x)`.
        //
        // Trust: NEGATION-CORE SELECTION (2026-07-29) — two emitter shapes, both taken
        // from the emitter's own construction:
        //
        //   * `v2_build_negation_raw_vc` emits `And([input_range(v), Eq(v, MIN)])`, so
        //     the obligation BODY is the core.
        //   * `v2_build_assert_negation_vc` emits the assert failure — the BARE
        //     condition local `Var(c)` for the `expected == false` `OverflowNeg` assert
        //     rustc lowers `-x` to — and leaves the core as the RHS of the SSA
        //     guard-binding block definition `Eq(Var c, Eq(x, MIN))`, resolved by NAME
        //     through `assert_condition_binding`, singleton-or-nothing.
        //
        // The old `find_violation_leaf_through_eq` reached the second case by descending
        // into the operands of EVERY `Eq` in `vc.formula` — i.e. into every block
        // definition in the function and any `Eq`-shaped precondition. That is deleted,
        // not kept as a fallback: a fallback keeps the forgery lane open.
        K::NegationOverflow { .. } => {
            let is_core = |f: &F| match f {
                F::Eq(lhs, rhs) => formula_var_name(lhs).is_some() && matches!(&**rhs, F::Int(_)),
                _ => false,
            };
            // Trust: THE BODY IS SHAPE-MATCHED, NOT SEARCHED (2026-07-31, round-6 F1).
            // `assert_bound_or_body_core`'s body route used to descend the peeled body,
            // so the DECOY `Or([Eq(x, -128), Gt(z, 5)])` — an obligation stating strictly
            // less than `neg_overflows_i8 x` — located the `Eq` and minted
            // `Some(NegationOverflow(W8))`. MEASURED before this change; `None` after.
            // Trust: AUTHENTICATED OBLIGATION (2026-07-31, vertical slice ARM 2). Same
            // three-way gate as div/rem (ARM 1): the recorded body REPLACES the peel when
            // it authenticates (`reconstruct_obligation == vc.formula`), the peel is the
            // legacy fallback when nothing is recorded, and a recorded-but-unfaithful claim
            // fails closed. The subject/width are additionally cross-checked below.
            let rec = authenticated_record(vc)?;
            let (leaf, route) = assert_bound_or_body_core_with(func, &vc.formula, &rec.body, &is_core)?;
            let F::Eq(x_f, min_f) = leaf else { return None };
            if formula_var_name(x_f).is_none() {
                return None;
            }
            let F::Int(min) = &**min_f else { return None };
            let w = swidth_of_signed_min(*min)?;
            // Trust: WIDTH CROSS-CHECK (2026-07-29, lane A round-3 finding [5]). The
            // certified width comes from the formula's `MIN` literal; `NegationOverflow`
            // carries the negated type INDEPENDENTLY. Without this check the MIR
            // confirmation is not enough on its own — `mir_assert_condition_core` checks
            // that the assert's condition local is defined by the located COMPARISON, and
            // nothing in that chain looks at the WIDTH. MEASURED, both routes: the body
            // route, `kind = NegationOverflow{i32}` with body `Eq(y,-128)` ->
            // `Some(NegationOverflow(W8))`; and the assert route, a crafted
            // `VerifiableFunction` with an `expected == false` `OverflowNeg` `Assert` on
            // `_3` plus the single defining statement `_3 := (y == -128)`, which satisfies
            // the whole MIR-confirmation chain and still minted `W8` for an i32 negation.
            // Pinned by
            // `obligation_region_tests::the_certified_width_must_agree_with_the_vc_kinds_own_width`.
            if negation_vc_modeled(&vc.kind) != Some(w) {
                return None;
            }
            // Trust: THE CERTIFIED SUBJECT (2026-07-31, round-5 defects [1]/[8]). Every
            // check above authenticates the SHAPE of the located core and the WIDTH the
            // VC's own kind carries — and `vc.kind`'s `ty` describes whatever local the
            // emitter took as its subject, which the two checks above never compare with
            // the variable being certified. MEASURED on the tree before this arm existed,
            // driven end-to-end through `trust_vcgen::generate_vcs`: a dominating
            // `assert!(!(x == i32::MIN))` over a negation of an UNRELATED `y` minted
            // `NegationOverflow(W32)` about `x`, and `y` — the operand actually negated —
            // appeared nowhere in the formula or in the certified proposition. Narrowing
            // `x` to `i8` still minted a 32-BIT certificate about an i8: a type that can
            // never hold −2³¹.
            //
            // Two witnesses exist and were never brought into contact. The fix brings
            // them into contact on BOTH routes, keyed on the SUBJECT rather than on the
            // route (the trust-ir lane's round-4 half was route-keyed, which left it
            // API-reopenable — round-5 defect [8]):
            //
            //   * the certified variable must BE an operand this MIR negates
            //     ([`negation_subjects`], the consumer-side twin of the emitter's three
            //     producers), and
            //   * the certified width must come from `operand_ty` OF THAT VARIABLE, not
            //     from `vc.kind`'s `ty`.
            //
            // COST: zero — all 12 negation certificates over
            // `crates/trust-clean/fixtures` survive. Their bodies, tallied by
            // `obligation_region_tests::mirsem_corpus_census`:
            // 5 are `Eq(v, MIN)` (the raw-`Neg` and `abs` producers) and 7 are the bare
            // condition local `Var(_c, Bool)` — i.e. 7 of the 12 take the ASSERT route,
            // the very route this check authenticates, and all 7 keep their certificate.
            // That 7 is why this gate is keyed on the SUBJECT and not on the route: on
            // this lane the assert route is where the certificates ARE, so a route-keyed
            // gate would have run on 7 honest rows and on the forgery alike, and left the
            // body route — the other 5 — with no subject check at all.
            let subject = base_var_name(x_f)?;
            let subject_ty = negation_subject_ty(func, subject)?;
            let trust_types::Ty::Int { width: sub_w, signed: sub_signed } = &subject_ty else {
                return None;
            };
            if SWidth::from_mir(*sub_w, *sub_signed) != Some(w) {
                return None;
            }
            // Trust: THE ASSERT ROUTE GETS A SECOND, NARROWER SUBJECT CHECK (2026-07-31,
            // round-6 item F2). The union above is keyed on the SUBJECT and therefore
            // runs on every route, which is what makes it API-closed; what it deliberately
            // does NOT do is pin the subject to the assert this VC came from. Any `Neg` in
            // the whole body satisfies it, so on the assert route a function that negates
            // `y` somewhere and asserts `-x`'s overflow elsewhere still agrees with itself.
            // [`assert_negation_subject`] is the trust-ir lane's narrower twin: the FIRST
            // `Neg` of THIS assert's own TARGET block, exactly the operand
            // `v2_find_target_neg_operand` hands the emitter.
            //
            // IT LAYERS, IT DOES NOT REPLACE. Applying it on every route would withdraw
            // the 5 body-route certificates (the raw-`Neg` and `abs` producers, which have
            // no `OverflowNeg` assert at all and would get `None` from it); applying it
            // INSTEAD of the union on the assert route would drop the union's coverage of
            // the 5. The pair is the union AND, on the assert route only, this. COST:
            // zero — `neg=12/12 (assert route 7)` is unchanged, so all 7 assert-route
            // certificates satisfy both.
            if route == CoreRoute::AssertCondition {
                let (asserted_name, asserted_ty) = assert_negation_subject(func)?;
                if asserted_name != subject || asserted_ty != subject_ty {
                    return None;
                }
            }
            // Trust: THE RECORDED SUBJECT/WIDTH ARE AUTHENTICATED TOO (2026-07-31,
            // vertical-slice design (D)/(E)). When the emitter recorded an obligation (the
            // `Authenticated` branch above — `vc.obligation` is `Some` and reconstructed
            // to `vc.formula`), its `subject`/`width` are CLAIMS, cross-checked here against
            // the values MIR and the authenticated body already fixed: the recorded width
            // must equal the width proven above (which came from the MIR subject type, the
            // [10]-class authority, NOT the body literal alone), and the recorded subject —
            // when it is a plain operand `Var` — must name the certified variable. A
            // mismatch is a desynchronised/hostile record ⇒ fail closed. These run only on
            // the `Some` path (the `Peel` fallback carries no record), so no legacy row is
            // affected; the arm's own soundness rests on the MIR checks above, and this is
            // the recorded field being consumed rather than trusted.
            if let Some(rec) = vc.obligation.as_ref() {
                if let Some(rec_w) = rec.width {
                    if rec_w != w.bits() {
                        return None;
                    }
                }
                if let Some(rec_subject) = rec.subject.as_ref() {
                    if let Some(rec_subject_name) = base_var_name(rec_subject) {
                        if rec_subject_name != subject {
                            return None;
                        }
                    }
                }
            }
            let name = neg_overflows_name(w);
            let ok = overflow_family_live_def_eq(leaf, &[x_f], &|ops| {
                Expr::app(cst(&name), ops[0].clone())
            });
            ok.then_some((SafetyVcKind::NegationOverflow(w), AdequacyVerdict::ProvenModulo3))
        }
        _ => None,
    }
}

/// Map an unsigned-overflow MAX threshold literal `2^w − 1` (read from the emitted
/// `Gt(a+b, Int(MAX))` disjunct) to its bit width — the INVERSE of `UWidth::max_value`,
/// so the certified width is recovered FROM THE FORMULA, not from `operand_ty`. `None`
/// (fail closed) for a threshold that is not exactly some modeled `2^w − 1`.
pub(super) fn width_of_unsigned_max(max: i128) -> Option<u32> {
    [8u32, 16, 32, 64].into_iter().find(|&w| (1i128 << w) - 1 == max)
}

/// Map a signed out-of-range `(MIN, MAX)` threshold pair (read from the emitted
/// `Or([Lt(a∘b,MIN), Gt(a∘b,MAX)])`) to its modeled `SWidth` — requiring BOTH that
/// `MIN = −2^(w−1)` AND `MAX = 2^(w−1) − 1` for the SAME `w` (a mismatched pair is a
/// real shape inconsistency ⇒ fail closed, never a spuriously-certified width).
pub(super) fn swidth_of_signed_bounds(min: i128, max: i128) -> Option<SWidth> {
    for w in [SWidth::W8, SWidth::W16, SWidth::W32, SWidth::W64] {
        if w.min_value() == min && w.max_value() == max {
            return Some(w);
        }
    }
    None
}

/// Map a negation-overflow MIN threshold literal `−2^(w−1)` (read from the emitted
/// `Eq(x, Int(MIN))` core) to its modeled `SWidth`. `None` (fail closed) for a literal
/// that is not exactly some modeled `−2^(w−1)`.
pub(super) fn swidth_of_signed_min(min: i128) -> Option<SWidth> {
    for w in [SWidth::W8, SWidth::W16, SWidth::W32, SWidth::W64] {
        if w.min_value() == min {
            return Some(w);
        }
    }
    None
}

/// Whether a `VcKind` is a SAFETY obligation (a runtime-UB / panic check the §6
/// pipeline must discharge) — as opposed to a postcondition/precondition/contract or
/// a non-safety property (temporal, taint, …). The generalized metric requires EVERY
/// safety VC the emitter raises to classify into a MODELED kind; a safety VC of an
/// unmodeled kind (shift/cast/negation overflow, float div, unreachable, …) makes the
/// function fail closed.
pub(super) fn is_safety_vc_kind(kind: &trust_types::VcKind) -> bool {
    use trust_types::VcKind as K;
    matches!(
        kind,
        K::ArithmeticOverflow { .. }
            | K::ShiftOverflow { .. }
            | K::DivisionByZero
            | K::RemainderByZero
            | K::IndexOutOfBounds
            | K::SliceBoundsCheck
            | K::CastOverflow { .. }
            | K::NegationOverflow { .. }
            | K::FloatDivisionByZero
    )
}

/// Public accessor for [`is_safety_vc_kind`] — the scorecard's straight-line
/// fully-faithful SOUNDNESS GATE (`prove::function_safety_vcs_all_discharged`) uses it
/// to select the safety VCs whose precondition-aware discharge it requires.
#[must_use]
pub fn is_safety_vc_kind_pub(kind: &trust_types::VcKind) -> bool {
    is_safety_vc_kind(kind)
}

/// If an `ArithmeticOverflow` VC is the UNSIGNED-ADD case of a MODELED width Lemma 2
/// certifies (`op == Add`, both operands unsigned with a `u8`/`u16`/`u32`/`u64`
/// width), return that width. `None` for a signed add, a non-Add op (the signed
/// `Div` `MIN/-1` overflow is an `ArithmeticOverflow{op:Div}`), an unmodeled width
/// (`u128`), or mismatched operand widths — those are UNMODELED ⇒ fail-closed.
pub(super) fn overflow_vc_modeled_width(kind: &trust_types::VcKind) -> Option<UWidth> {
    use trust_types::{BinOp, Ty, VcKind as K};
    let K::ArithmeticOverflow { op: BinOp::Add, operand_tys: (a, b) } = kind else {
        return None;
    };
    let (Ty::Int { width: wa, signed: sa }, Ty::Int { width: wb, signed: sb }) = (a, b) else {
        return None;
    };
    if wa != wb {
        return None;
    }
    // BOTH operands must be unsigned at the same modeled width.
    let wa = UWidth::from_mir(*wa, *sa)?;
    let wb = UWidth::from_mir(*wb, *sb)?;
    (wa == wb).then_some(wa)
}

/// If an `ArithmeticOverflow` VC is the UNSIGNED-MUL case of a MODELED width
/// (`op == Mul`, both operands unsigned with a `u8`/`u16`/`u32`/`u64` width), return
/// that width. `None` for a signed mul (that is the Lemma-5 case), a non-Mul op, an
/// unmodeled width (`u128`), or mismatched operand widths — those are UNMODELED ⇒
/// fail-closed. MIRRORS [`overflow_vc_modeled_width`] exactly (Add→Mul), and shares its
/// modeled unsigned width set `{u8,u16,u32,u64}`.
///
/// KIND-level accept is NECESSARY-not-sufficient: the load-bearing gate is the
/// formula-aware def-eq bridge (`safety_vc_is_faithful_formula_aware`), which certifies
/// ONLY the CONSTANT-multiplier LIA emission (`Gt(Mul(a,b), MAX)`) and DECLINES the
/// `var*var` BV mul shape. So a full-range `u8 * u8` VC is kind-modeled here but fails
/// closed at the bridge (and, separately, at the discharge) — `wrapping_mul` and every
/// unbounded product stay honestly not-faithful.
pub(super) fn umul_overflow_vc_modeled(kind: &trust_types::VcKind) -> Option<UWidth> {
    use trust_types::{BinOp, Ty, VcKind as K};
    let K::ArithmeticOverflow { op: BinOp::Mul, operand_tys: (a, b) } = kind else {
        return None;
    };
    let (Ty::Int { width: wa, signed: sa }, Ty::Int { width: wb, signed: sb }) = (a, b) else {
        return None;
    };
    if wa != wb {
        return None;
    }
    // BOTH operands must be UNSIGNED at the same modeled width (a signed mul is Lemma 5).
    let wa = UWidth::from_mir(*wa, *sa)?;
    let wb = UWidth::from_mir(*wb, *sb)?;
    (wa == wb).then_some(wa)
}

/// If an `ArithmeticOverflow` VC is the UNSIGNED-SUB case of a MODELED width Lemma 8
/// certifies (`op == Sub`, both operands unsigned with a `u8`/`u16`/`u32`/`u64` width),
/// return that width. `None` for a signed sub (that is the Lemma-5 case), a non-Sub op,
/// an unmodeled width (`u128`), or mismatched operand widths — those are UNMODELED ⇒
/// fail-closed. The emitter's unsigned-Sub VC is `ArithmeticOverflow{op:Sub, (u_W,u_W)}`
/// whose violation core is the single underflow disjunct `Lt(Sub(a,b), 0)`.
pub(super) fn usub_underflow_vc_modeled(kind: &trust_types::VcKind) -> Option<UWidth> {
    use trust_types::{BinOp, Ty, VcKind as K};
    let K::ArithmeticOverflow { op: BinOp::Sub, operand_tys: (a, b) } = kind else {
        return None;
    };
    let (Ty::Int { width: wa, signed: sa }, Ty::Int { width: wb, signed: sb }) = (a, b) else {
        return None;
    };
    if wa != wb {
        return None;
    }
    // BOTH operands must be UNSIGNED at the same modeled width (a signed sub is Lemma 5).
    let wa = UWidth::from_mir(*wa, *sa)?;
    let wb = UWidth::from_mir(*wb, *sb)?;
    (wa == wb).then_some(wa)
}

/// If an `ArithmeticOverflow` VC is the SIGNED-ADD/SUB/MUL case of a MODELED width Lemma
/// 5 certifies (`op ∈ {Add, Sub, Mul}`, both operands signed), return that `(op, width)`.
/// `None` for an unsigned operand, a non-Add/Sub/Mul op (the signed `Div` `MIN/-1`
/// overflow is an `ArithmeticOverflow{op:Div}`), or an unmodeled check width (`i128`) —
/// those are UNMODELED ⇒ fail-closed. NOTE: signed MUL is kind-modeled here, but the
/// load-bearing gate is the formula-aware def-eq bridge, which certifies only the LIA
/// constant-multiplier shape and declines a `var*var` BV mul (fail-closed).
///
/// The MODELED width is the NARROWER (`min`) of the two operand widths — exactly the
/// type the emitter's overflow check is against (`generate.rs::int_op_type` recovers
/// the true type from the NON-constant operand; an untyped integer constant defaults to
/// the widest `i64`, so when the operand widths differ the real check type is the
/// narrower one, and the emitted `±2^(W−1)` threshold is at that width). For genuine
/// same-width arithmetic (`x:i32 + y:i32`) `min` is just that shared width. This keeps
/// the certified width byte-aligned with the emitted threshold (guarded end-to-end by
/// `signed_overflow_vc_shape_matches_trust_vcgen_emission`).
pub(super) fn signed_overflow_vc_modeled(kind: &trust_types::VcKind) -> Option<(SignedOp, SWidth)> {
    use trust_types::{BinOp, Ty, VcKind as K};
    let K::ArithmeticOverflow { op, operand_tys: (a, b) } = kind else {
        return None;
    };
    let sop = match op {
        BinOp::Add => SignedOp::Add,
        BinOp::Sub => SignedOp::Sub,
        // Signed MUL is now a MODELED kind (Lemma 5 spec heads `Int.mul`). This kind-level
        // accept is NECESSARY-not-sufficient: the load-bearing gate is the formula-aware
        // def-eq bridge (`safety_vc_is_faithful_formula_aware`), which certifies ONLY the
        // LIA constant-multiplier emission and DECLINES the `var*var` BV mul shape. So the
        // BV mul VC is kind-modeled here but fails closed at the bridge — the `mul_*`/
        // `sq_nonneg` corpus stays not-faithful (its product is genuinely unbounded).
        BinOp::Mul => SignedOp::Mul,
        // Every other op (Div/Rem/shift/…) is not a Lemma-5 shape.
        _ => return None,
    };
    let (Ty::Int { width: wa, signed: sa }, Ty::Int { width: wb, signed: sb }) = (a, b) else {
        return None;
    };
    // BOTH operands must be signed. The check width is the narrower of the two (the
    // emitter's `int_op_type` recovers it from the non-constant — real-typed — operand).
    if !sa || !sb {
        return None;
    }
    let check_width = (*wa).min(*wb);
    let w = SWidth::from_mir(check_width, true)?;
    Some((sop, w))
}

/// If a `NegationOverflow` VC is on a MODELED signed width Lemma 6 certifies
/// (`i8`/`i16`/`i32`/`i64`), return that width. `None` for an unsigned type (negation
/// of an unsigned value carries no overflow obligation; `is_signed` is false) or an
/// unmodeled width (`i128` — the deferred bitvector case) — those are UNMODELED ⇒
/// fail-closed.
pub(super) fn negation_vc_modeled(kind: &trust_types::VcKind) -> Option<SWidth> {
    use trust_types::{Ty, VcKind as K};
    let K::NegationOverflow { ty } = kind else {
        return None;
    };
    let Ty::Int { width, signed } = ty else {
        return None;
    };
    SWidth::from_mir(*width, *signed)
}

/// If a `ShiftOverflow` VC is on a MODELED value width Lemma 7 certifies, return that
/// `(value width, amount signedness)`. The MODELED width is the SHIFTED VALUE's width
/// (the `n ≥ W` UB threshold is `W` = the value width); the bool is the shift AMOUNT's
/// signedness (a signed amount adds the `n < 0` disjunct). The modeled set is
/// `8/16/32/64/128` — INCLUDING the `i128`/`u128` value widths (the former "128-bit
/// shift VC width" residue: the threshold is the width literal itself, which stays a
/// closed `Int.ofNat` at 128). `None` for a non-integer value type or any other
/// width — those are UNMODELED ⇒ fail-closed.
pub(super) fn shift_vc_modeled(kind: &trust_types::VcKind) -> Option<(ShiftWidth, bool)> {
    use trust_types::{Ty, VcKind as K};
    let K::ShiftOverflow { operand_ty, shift_ty, .. } = kind else {
        return None;
    };
    let Ty::Int { width, .. } = operand_ty else {
        return None;
    };
    // The shifted-VALUE width drives the `n ≥ W` threshold. Map any integer value
    // width (signed OR unsigned) to the modeled W ∈ {8,16,32,64,128} (the ShiftWidth
    // names the THRESHOLD W, not the value's signedness).
    let w = ShiftWidth::from_bits(*width)?;
    let Ty::Int { signed: amount_signed, .. } = shift_ty else {
        return None;
    };
    Some((w, *amount_signed))
}

/// Whether a SAFETY `VcKind` is one MirSem models an adequacy lemma for (unsigned-add
/// overflow ∨ UNSIGNED-SUB underflow ∨ SIGNED add/sub overflow ∨ bounds ∨ div ∨ rem ∨
/// NEGATION overflow ∨ SHIFT-amount OOB). A safety VC outside this set is UNMODELED ⇒
/// the function fails closed in the generalized metric. For `ArithmeticOverflow` the
/// modeled set is the unsigned-add-of-modeled-width case (`overflow_vc_modeled_width`,
/// Lemma 2), the unsigned-SUB-of-modeled-width case (`usub_underflow_vc_modeled`,
/// Lemma 8), the signed add/sub/mul-of-modeled-width case (`signed_overflow_vc_modeled`,
/// Lemma 5), OR the UNSIGNED-MUL-of-modeled-width case (`umul_overflow_vc_modeled`). Both
/// signed AND unsigned MUL are kind-modeled, but the formula-aware bridge certifies only
/// the LIA constant-multiplier shape (`Gt(Mul(a,b), MAX)`) — a `var*var` BV mul declines
/// there (fail-closed), so the `var*var` corpus stays effectively deferred. `DivisionByZero`
/// (Lemma 4) and `RemainderByZero` (Lemma 9) are modeled; `NegationOverflow` of a
/// modeled width (Lemma 6) and `ShiftOverflow` of a modeled value width — INCLUDING
/// 128 (Lemma 7) — are modeled; a `CastOverflow` / `FloatDivisionByZero` / `i128`
/// negation remains UNMODELED.
pub(super) fn safety_vc_kind_is_modeled(kind: &trust_types::VcKind) -> bool {
    use trust_types::VcKind as K;
    match kind {
        K::ArithmeticOverflow { .. } => {
            overflow_vc_modeled_width(kind).is_some()
                || usub_underflow_vc_modeled(kind).is_some()
                || signed_overflow_vc_modeled(kind).is_some()
                || umul_overflow_vc_modeled(kind).is_some()
        }
        K::DivisionByZero | K::RemainderByZero | K::IndexOutOfBounds | K::SliceBoundsCheck => true,
        K::NegationOverflow { .. } => negation_vc_modeled(kind).is_some(),
        K::ShiftOverflow { .. } => shift_vc_modeled(kind).is_some(),
        _ => false,
    }
}

/// THE GENERALIZED SAFETY-VC-FAITHFULNESS HOOK (Goal #4, generalized
/// `safety_vc_faithful` tier). For a reflected function, mint per-kind safety-VC
/// adequacy certificates iff:
///
///   1. the function raises AT LEAST ONE modeled safety VC (overflow ∨ bounds ∨ div),
///      AND
///   2. EVERY safety VC the emitter (`trust_vcgen::generate_vcs`) raises classifies
///      into a MODELED kind (no unmodeled shift/cast/negation/float safety VC), AND
///   3. each modeled kind's reflected VC is PROVEN (modulo 3) def-eq to its pinned
///      machine-semantics condition (`uadd_overflows_uW` / `idx_oob` / `div_by_zero`).
///
/// Fail-closed (`None`): a function with NO modeled safety VC, a function whose
/// emitter raises an UNMODELED safety VC kind, or any modeled kind whose adequacy
/// proof does not kernel-check modulo 3 — never a false witness.
///
/// A `Some` result means: when the §6 pipeline discharges this function's safety VCs,
/// it is refuting EXACTLY the machine condition for EACH — overflow `(2^w−1)<a+b`,
/// bounds `len≤i`, or div-zero `b=0` — the safety discharge is kernel-certified
/// FAITHFUL across all the function's modeled safety obligations, not merely trusted.
#[must_use]
pub fn function_safety_vcs_faithful(
    func: &trust_types::VerifiableFunction,
) -> Option<FunctionSafetyVcCertificates> {
    // Drive the REAL emitter so the classification is over the VCs that ACTUALLY get
    // raised (the same empirical grounding Lemma 2's value rested on).
    let vcs = trust_vcgen::generate_vcs(func);

    // ALL modeled safety-VC kinds are now FORMULA-AWARE: each cert is minted by
    // grounding the ACTUAL emitted `vc.formula` violation core through the LIVE
    // `clean_ground::ground_prop` and kernel-checking it def-eq to the per-kind spec
    // (recovering the width/threshold from the FORMULA, not from `operand_ty`). The
    // OVERFLOW-family cores (unsigned-add OVERFLOW, signed ADD/SUB OVERFLOW, unsigned-SUB
    // UNDERFLOW, NEGATION) carry a COMPUTED `Add`/`Sub`/`Eq` sub-term whose operands the
    // live grounder DOES ground — closing the model→grounder bridge for them too. Dedup
    // by the `SafetyVcKind` the formula-aware certifier returns.
    let mut certs = FunctionSafetyVcCertificates::default();
    let mut bounds_cert: Option<SafetyVcCertificate> = None;
    let mut div_cert: Option<SafetyVcCertificate> = None;
    let mut rem_cert: Option<SafetyVcCertificate> = None;
    let mut shift_certs: Vec<SafetyVcCertificate> = Vec::new();
    for vc in &vcs {
        if !is_safety_vc_kind(&vc.kind) {
            continue; // a postcondition / contract / non-safety property — not our concern
        }
        if !safety_vc_kind_is_modeled(&vc.kind) {
            return None; // an UNMODELED safety VC kind ⇒ fail closed (cannot certify ALL)
        }
        // FORMULA-AWARE certification for EVERY modeled safety VC: ground the REAL
        // emitted core live and kernel-check def-eq to its spec. Fail-closed if this
        // VC's core is outside the formula-aware fragment OR not def-eq to the spec —
        // even though `safety_vc_kind_is_modeled` accepted the VcKind, the live-grounded
        // def-eq is the stricter (and load-bearing) bridge check.
        let (kind, verdict) = safety_vc_is_faithful_formula_aware(func, vc)?;
        match &kind {
            SafetyVcKind::Overflow(_) => {
                if !certs.overflow.iter().any(|c| c.kind == kind) {
                    certs.overflow.push(SafetyVcCertificate { kind, verdict });
                }
            }
            SafetyVcKind::UnsignedSubUnderflow(_) => {
                if !certs.usub.iter().any(|c| c.kind == kind) {
                    certs.usub.push(SafetyVcCertificate { kind, verdict });
                }
            }
            SafetyVcKind::SignedOverflow(_, _) => {
                if !certs.signed_overflow.iter().any(|c| c.kind == kind) {
                    certs.signed_overflow.push(SafetyVcCertificate { kind, verdict });
                }
            }
            SafetyVcKind::UnsignedMulOverflow(_) => {
                if !certs.umul.iter().any(|c| c.kind == kind) {
                    certs.umul.push(SafetyVcCertificate { kind, verdict });
                }
            }
            SafetyVcKind::NegationOverflow(_) => {
                if !certs.negation.iter().any(|c| c.kind == kind) {
                    certs.negation.push(SafetyVcCertificate { kind, verdict });
                }
            }
            SafetyVcKind::Bounds => {
                if bounds_cert.is_none() {
                    bounds_cert = Some(SafetyVcCertificate { kind, verdict });
                }
            }
            SafetyVcKind::DivByZero => {
                if div_cert.is_none() {
                    div_cert = Some(SafetyVcCertificate { kind, verdict });
                }
            }
            SafetyVcKind::RemByZero => {
                if rem_cert.is_none() {
                    rem_cert = Some(SafetyVcCertificate { kind, verdict });
                }
            }
            SafetyVcKind::ShiftOob(_, _) => {
                if !shift_certs.iter().any(|c| c.kind == kind) {
                    shift_certs.push(SafetyVcCertificate { kind, verdict });
                }
            }
        }
    }

    certs.bounds = bounds_cert;
    certs.div = div_cert;
    certs.rem = rem_cert;
    certs.shift = shift_certs;

    // Require at least one modeled safety VC (an unmodeled body is not certified).
    if certs.any() { Some(certs) } else { None }
}
