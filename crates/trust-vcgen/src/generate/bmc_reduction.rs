// Bounded-model-checking REFUTATION of a statically-sized array reduction whose
// accumulator genuinely overflows.
//
// WHY THIS EXISTS. `loop_bounds::build_accumulator_bound_facts` is the PROVING
// side of the bounded reduction: it emits `acc <= init + K*per_max` and friends,
// and is deliberately SELF-LIMITING — when the bound does not fit the accumulator
// type it emits nothing and the per-add overflow obligation stays undischarged.
// The verifier then DECLINES (the incompleteness header, rc=1). A decline is an
// honest answer, but on the falsification gate's `mutant/` lane it scores as an
// UNCAUGHT MUTANT: the two fixtures
// `tests/trust-falsification/mutant/shift_reduction_overflow.rs` and
// `.../i128_shift_accumulator_overflow.rs` GENUINELY overflow and their own
// header comments record that "there is no refutation engine for reduction
// overflow today".
//
// This module is that engine, for exactly one shape: a single loop that iterates
// a FIXED-SIZE array a statically-known number of times, with a straight-line
// body whose only accumulating operation is one overflow-checked self-add. For
// that shape a BMC unroll is EXACT, so a solver model is a genuine counterexample
// and licenses a refutation.
//
// REFUTATION-ONLY, BY CONSTRUCTION. The producer emits a *candidate* VC whose
// formula is the VIOLATION formula (the router's convention: SAT = counterexample,
// UNSAT = property holds). The consumer in `trust_verify.rs` appends a `Failed`
// row ONLY on an ay SAT verdict that carries a NON-EMPTY model, and DROPS an
// UNSAT/Unknown/Timeout answer entirely — it discharges nothing. So this lane can
// never turn "the prover failed to prove it" into "refuted": no proof authority
// is granted, and no obligation is retired.
//
// THE THREE PREMISES (stated so they are auditable, not buried):
//   P1  `for &x in <fixed array>` runs EXACTLY `LEN` iterations. This is the
//       std-library semantics of `<&[T; N] as IntoIterator>::into_iter`, and it
//       is the SAME premise `total_loop_iterations` already relies on for the
//       proving side — used there as an UPPER bound, used here as a LOWER bound.
//   P2  The iterated array is an unconstrained function INPUT, so its `LEN`
//       elements range INDEPENDENTLY over the whole element type. Enforced by
//       `iterated_array_is_free_parameter` (a parameter local, never written,
//       never mutably/raw borrowed) plus `preconditions_leave_the_input_free`:
//       a hard refusal of any AUTHORED contract (`#[requires]` could constrain
//       the input) and, on top of that, a positive per-formula certification
//       that every remaining body hypothesis is a type tautology of THIS body.
//   P3  Iterations `0..i` are REACHED, i.e. nothing else can panic or branch
//       away first. Enforced by `body_is_straight_line_reduction`: every
//       reachable terminator is on a tiny allowlist, every reachable `Assert`
//       is either the accumulator's own overflow assert or has a statically
//       constant-true condition, and the only `SwitchInt` is the iterator's own
//       `Option` discriminant test. Reachability is `bmc_terminator_succs`,
//       which prunes ONLY the `otherwise` edge of a switch whose scrutinee is a
//       `Discriminant` read of a place whose DECLARED type is an enum, and whose
//       case set is exactly that enum's declared discriminant set. The
//       caller-constructible `exhaustive_enum_unreachable` bit is never read and
//       never prunes an edge; any OTHER reachable `Unreachable` still refuses.
//
// Any doubt about any of the three ⇒ NO CANDIDATE. Withholding a candidate leaves
// the build at exactly today's (already fail-closed) `incomplete` verdict.

use super::*;

/// Hard cap on the unroll. 64 (the `[u8; 64]` fixture) must fit; the formula is
/// LINEAR in `K` (see `build_unrolled_violation`), so this is a work bound, not a
/// blow-up guard. A trip count above the cap DECLINES — a PARTIAL unroll is not
/// built at all, because a partial unroll's UNSAT means nothing and its SAT would
/// need a separate argument that the missing suffix cannot rescue the prefix.
const BMC_MAX_UNROLL: i128 = 256;

/// The recognized reduction, with everything the encoder needs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct BmcReduction {
    /// Accumulator integer type — the width/signedness the overflow check is against.
    acc_width: u32,
    acc_signed: bool,
    /// The accumulator's constant initializer, established OUTSIDE the loop.
    init: i128,
    /// Exact trip count (P1).
    trip: i128,
    /// Element type range `[min, max]` — the free per-iteration input (P2).
    elem_min: i128,
    elem_max: i128,
    /// `Some(k)` for the `t += (x as ACC) << k` shape; `None` for `t += x as ACC`.
    shift: Option<u32>,
    /// The add's source span, so the refuted row points at the real statement.
    location: SourceSpan,
    /// The accumulator type, for the emitted `VcKind::ArithmeticOverflow`.
    acc_ty: Ty,
}

/// `[min, max]` of an `N`-bit integer type, but ONLY when both endpoints are
/// representable as `i128` (every literal this module emits is `Formula::Int`).
/// Unsigned 128 is therefore refused: `2^128 - 1` has no `i128` spelling, and
/// `Formula::UInt` degrades to `0` on the constant-folding path.
fn int_range(width: u32, signed: bool) -> Option<(i128, i128)> {
    if width == 0 || width > 128 {
        return None;
    }
    if signed {
        if width == 128 {
            return Some((i128::MIN, i128::MAX));
        }
        let m = 1i128 << (width - 1);
        Some((-m, m - 1))
    } else {
        if width >= 128 {
            return None;
        }
        if width == 127 {
            return Some((0, i128::MAX));
        }
        Some((0, (1i128 << width) - 1))
    }
}

/// `2^n` as an `i128`, or None when it does not fit (`n >= 127`).
fn pow2(n: u32) -> Option<i128> {
    if n >= 127 { None } else { Some(1i128 << n) }
}

/// Is `[lo, hi]` contained in `[min, max]`? A cast `x as ACC` is VALUE-PRESERVING
/// exactly when the source range fits the destination range; otherwise it wraps
/// and this module refuses the shape (a wrapping cast needs modular semantics the
/// linear encoding below does not have).
fn range_fits(lo: i128, hi: i128, min: i128, max: i128) -> bool {
    lo >= min && hi <= max
}

/// Trace an operand through whole-local `Use` copies to a root local, WITHOUT
/// hopping any projection. Bounded by `fuel`.
fn root_local(func: &VerifiableFunction, op: &Operand, fuel: u32) -> Option<usize> {
    if fuel == 0 {
        return None;
    }
    let (Operand::Copy(p) | Operand::Move(p)) = op else { return None };
    if !p.projections.is_empty() {
        return None;
    }
    match crate::local_defs::unique_value_def(func, p.local) {
        Some(Rvalue::Use(inner)) => root_local(func, inner, fuel - 1).or(Some(p.local)),
        _ => Some(p.local),
    }
}

/// Constant-fold an operand to an integer, hopping whole-local `Use`/`Cast`
/// copies of constants. Used only by the assert allowlist (P3).
fn fold_const_int(func: &VerifiableFunction, op: &Operand, fuel: u32) -> Option<i128> {
    if fuel == 0 {
        return None;
    }
    if let Some(c) = operand_const_int(op) {
        return Some(c);
    }
    let (Operand::Copy(p) | Operand::Move(p)) = op else { return None };
    if !p.projections.is_empty() {
        return None;
    }
    match crate::local_defs::unique_value_def(func, p.local)? {
        Rvalue::Use(inner) | Rvalue::Cast(inner, _) => fold_const_int(func, inner, fuel - 1),
        _ => None,
    }
}

/// Constant-fold an operand to a boolean: a `bool` constant, or a comparison of
/// two folded integer constants (the shape rustc's shift-amount check has before
/// `SimplifyConstCondition` removes it — `assert(Lt(4u32, 8u32))`).
fn fold_const_bool(func: &VerifiableFunction, op: &Operand, fuel: u32) -> Option<bool> {
    if fuel == 0 {
        return None;
    }
    if let Operand::Constant(ConstValue::Bool(b)) = op {
        return Some(*b);
    }
    let (Operand::Copy(p) | Operand::Move(p)) = op else { return None };
    if !p.projections.is_empty() {
        return None;
    }
    match crate::local_defs::unique_value_def(func, p.local)? {
        Rvalue::Use(inner) => fold_const_bool(func, inner, fuel - 1),
        Rvalue::BinaryOp(op_kind, l, r) => {
            let (l, r) = (fold_const_int(func, l, fuel)?, fold_const_int(func, r, fuel)?);
            match op_kind {
                BinOp::Lt => Some(l < r),
                BinOp::Le => Some(l <= r),
                BinOp::Gt => Some(l > r),
                BinOp::Ge => Some(l >= r),
                BinOp::Eq => Some(l == r),
                BinOp::Ne => Some(l != r),
                _ => None,
            }
        }
        _ => None,
    }
}

/// CFG successors for THIS module's reachability walk: `terminator_succs` minus
/// the `otherwise` edge of a `SwitchInt` that is provably exhaustive **from the
/// declared enum type of the place it switches on**.
///
/// WHY AN OVERRIDE IS NEEDED AT ALL. `for &x in <array>` lowers to
/// `SwitchInt(Discriminant(next_result)) { 0 -> exit, 1 -> body, otherwise -> bbU }`
/// with `bbU: Unreachable` — rustc's spelling of "the `Option` tag is 0 or 1".
/// `terminator_succs` chains `otherwise` unconditionally, so `bbU` lands in the
/// reachable set and `body_is_straight_line_reduction`'s terminator allowlist
/// refuses the function. That refusal is right in general (a reachable
/// `Terminator::Unreachable` is `unreachable_unchecked()`-shaped UB, which
/// falsifies P3) and wrong for this one edge, which no execution takes.
///
/// WHY THE EVIDENCE IS THE TYPE AND NOT THE HINT. `Terminator::SwitchInt` also
/// carries `exhaustive_enum_unreachable`. **This function does not read it**, and
/// must not: it is `#[serde(default)]` serialized public input, so a caller can
/// set it on an ordinary integer switch whose default really is reachable, and
/// `trust-mir-extract`'s coroutine lane sets it with no tag-set check at all
/// (computing the tag set there needs the layout query, which cycles inside that
/// MIR pass). `4ca0cb0eac` removed the earlier hint-keyed override for exactly
/// that reason and named the bar for restoring it: *"A future optimization may
/// prune only from locally rederived, subject-bound type/layout evidence; this
/// public hint alone can never erase an edge."* That is what
/// [`switch_otherwise_is_dead_by_declared_enum_type`] supplies — the discriminant
/// is read off a whole local whose DECLARED type is an `enum`, and the case set
/// is exactly that enum's declared discriminant set, so every value the scrutinee
/// can hold is matched by a named case.
///
/// This is deliberately NOT a change to the shared `loop_bounds::terminator_succs`:
/// that function feeds `count_back_edges`, `block_is_on_cycle` and
/// `total_loop_iterations` for every PROVING-side consumer, and this
/// refutation-only module has no business changing the discharge path.
fn bmc_terminator_succs(func: &VerifiableFunction, t: &Terminator) -> Vec<usize> {
    let mut succs = terminator_succs(t);
    let Terminator::SwitchInt { discr, targets, otherwise, .. } = t else {
        return succs;
    };
    if switch_otherwise_is_dead_by_declared_enum_type(func, discr, targets, *otherwise) {
        succs.retain(|b| *b != otherwise.0);
    }
    succs
}

/// Is the `otherwise` edge of this `SwitchInt` taken by NO execution, argued
/// from the switched-on place's own declared type?
///
/// Every conjunct is re-derived from this body; none of them consults
/// `exhaustive_enum_unreachable`, which this module never reads.
///
///   1. `otherwise` really ends in `Terminator::Unreachable`. If it does not, the
///      block is an ordinary successor and pruning it would hide real control
///      flow — there is nothing to argue about and nothing to gain.
///   2. `otherwise` is not ALSO a named case target. A block that some case
///      reaches is genuinely reached, and dropping the edge would hide that.
///   3. The scrutinee is `Rvalue::Discriminant(p)` for a WHOLE local `p` with no
///      projections, and that rvalue is the local's UNIQUE whole-local definition
///      (`local_defs::body_unique_value_def`), so the switch really tests a discriminant
///      read of one identified place — never an ordinary integer temp.
///   4. `p`'s DECLARED type is `Ty::Adt { adt_kind: Enum }` with a non-empty
///      variant list carrying pairwise-distinct discriminants. This is the
///      subject-bound datatype evidence: it is attached to the very place being
///      switched on, and it says what values a `Discriminant` read of that place
///      can produce.
///   5. Every declared discriminant is non-negative (a `#[repr(iN)]` enum with a
///      negative discriminant encodes its tag as a two's-complement bit pattern
///      at the tag width, which this comparison would get wrong — so it declines).
///   6. The case-value set is EXACTLY the declared discriminant set — no missing
///      variant, no extra value.
///
/// Under 3-6 the scrutinee is the discriminant of a value of enum type `E`, every
/// value of `E` carries one of `E`'s declared discriminants, and every one of
/// those has a named case; with 1-2 the `otherwise` block is therefore entered by
/// no execution. The forgery `4ca0cb0eac` named — "an ordinary integer switch
/// whose default remains reachable" — is excluded by 3 and 4 together: such a
/// switch has neither a `Discriminant` definition nor an enum-typed scrutinee.
///
/// Every conjunct failing means only that this OPTIONAL refutation lane declines,
/// leaving the build at its existing fail-closed `incomplete` verdict.
fn switch_otherwise_is_dead_by_declared_enum_type(
    func: &VerifiableFunction,
    discr: &Operand,
    targets: &[(u128, BlockId)],
    otherwise: BlockId,
) -> bool {
    if targets.is_empty() {
        return false;
    }
    // (1) the `otherwise` arm must really be rustc's Unreachable certificate.
    let is_unreachable = func
        .body
        .blocks
        .get(otherwise.0)
        .filter(|b| b.id == otherwise)
        .or_else(|| func.body.blocks.iter().find(|b| b.id == otherwise))
        .is_some_and(|b| matches!(b.terminator, Terminator::Unreachable));
    if !is_unreachable {
        return false;
    }
    // (2) ... and must not also be reached by a named case.
    if targets.iter().any(|(_, b)| *b == otherwise) {
        return false;
    }
    // (3) the scrutinee is a discriminant read of ONE whole local.
    let Some(root) = root_local(func, discr, 8) else { return false };
    // Upstream renamed this resolver during the 1377-commit merge. The pre-seam
    // spelling took the whole FUNCTION; the entry-definition-aware question now
    // lives in `local_defs` and takes the BODY, as called below. The old name is
    // deliberately NOT quoted here: `tests/local_defs_seam_lint.rs` bans it as a
    // SOURCE FACT so a rebase cannot reintroduce a call, and that scan is a plain
    // substring match that does not exclude comments.
    let Some(Rvalue::Discriminant(p)) = crate::local_defs::body_unique_value_def(&func.body, root)
    else {
        return false;
    };
    if !p.projections.is_empty() {
        return false;
    }
    // (4) that local's DECLARED type is an enum with distinct discriminants.
    let Some(Ty::Adt { variants, adt_kind: Some(trust_types::AdtKind::Enum), .. }) =
        crate::local_ty_ref(func, p.local)
    else {
        return false;
    };
    if variants.is_empty() || targets.len() < variants.len() {
        return false;
    }
    // (5) every declared discriminant must be a non-negative `u128` tag.
    let mut declared: Vec<u128> = Vec::with_capacity(variants.len());
    for v in variants {
        let Ok(tag) = u128::try_from(v.discriminant) else { return false };
        declared.push(tag);
    }
    declared.sort_unstable();
    if declared.windows(2).any(|w| w[0] == w[1]) {
        return false;
    }
    // (6) the case set is EXACTLY the declared discriminant set.
    let mut cases: Vec<u128> = targets.iter().map(|(v, _)| *v).collect();
    cases.sort_unstable();
    cases.dedup();
    cases == declared
}

/// Blocks reachable from the entry block along ORDINARY successors
/// (`bmc_terminator_succs`, which excludes unwind/cleanup edges — an unwind sink
/// is only entered from a panic that has already violated something — and the
/// `otherwise` edge of a switch proved exhaustive from the scrutinee's declared
/// enum type).
fn reachable_blocks(func: &VerifiableFunction) -> FxHashSet<usize> {
    let mut seen: FxHashSet<usize> =
        FxHashSet::with_capacity_and_hasher(func.body.blocks.len(), Default::default());
    let Some(entry) = func.body.blocks.first().map(|b| b.id.0) else {
        return seen;
    };
    let mut stack = vec![entry];
    while let Some(b) = stack.pop() {
        if !seen.insert(b) {
            continue;
        }
        let block = func
            .body
            .blocks
            .get(b)
            .filter(|blk| blk.id.0 == b)
            .or_else(|| func.body.blocks.iter().find(|blk| blk.id.0 == b));
        if let Some(blk) = block {
            stack.extend(bmc_terminator_succs(func, &blk.terminator));
        }
    }
    seen
}

/// Does `discr` read the `Option` discriminant of `next_dest` (the `Iterator::next`
/// result)? The for-each desugar's ONLY branch.
fn is_iterator_option_switch(func: &VerifiableFunction, discr: &Operand, next_dest: usize) -> bool {
    let Some(local) = root_local(func, discr, 8) else { return false };
    matches!(
        crate::local_defs::unique_value_def(func, local),
        Some(Rvalue::Discriminant(p)) if p.local == next_dest && p.projections.is_empty()
    )
}

/// P3: every reachable block is a straight-line step of the reduction.
///
/// Allowed terminators: `Goto`, `Return`, the ONE `Iterator::next` driver call
/// and the ONE `IntoIterator::into_iter` construction, the iterator's own
/// `Option` `SwitchInt`, and `Assert`s that are either the accumulator's own
/// overflow assert or statically constant-true. Everything else — another call,
/// a user branch, a `Drop`, an `Opaque`, a reachable `Unreachable`/`Resume` —
/// DECLINES, because any of them could stop the loop before iteration `i` and
/// make a model that assumes iteration `i` runs a FALSE counterexample.
///
/// Statements are allowlisted too: only value-carrying `Assign`s and the
/// no-value-write markers. A `SetDiscriminant`/`Deinit`/`Intrinsic`/`Unsupported`
/// can change state this module does not model.
fn body_is_straight_line_reduction(
    func: &VerifiableFunction,
    reachable: &FxHashSet<usize>,
    next_dest: usize,
    add_tuple_local: usize,
) -> bool {
    let mut next_calls = 0usize;
    for block in &func.body.blocks {
        if !reachable.contains(&block.id.0) {
            continue;
        }
        for stmt in &block.stmts {
            match stmt {
                Statement::Assign { .. }
                | Statement::StorageLive(_)
                | Statement::StorageDead(_)
                | Statement::PlaceMention(_)
                | Statement::Retag { .. }
                | Statement::Coverage
                | Statement::ConstEvalCounter
                | Statement::Nop => {}
                _ => return false,
            }
        }
        match &block.terminator {
            Terminator::Goto(_) | Terminator::Return => {}
            Terminator::Call { func: callee, dest, .. } => {
                if callee_is_iterator_next(callee) {
                    if dest.local != next_dest || !dest.projections.is_empty() {
                        return false;
                    }
                    next_calls += 1;
                } else if !callee_is_into_iter(callee) {
                    // Any other call could panic, diverge, or mutate the input.
                    return false;
                }
            }
            // An arbitrary tail callee can panic or diverge before returning to
            // the original caller, exactly like an unmodelled ordinary call.
            // This refutation-only lane must not assume the full unroll reaches
            // its modeled overflow site, so TailCall is an explicit decline.
            Terminator::TailCall { .. } => return false,
            Terminator::SwitchInt { discr, .. } => {
                if !is_iterator_option_switch(func, discr, next_dest) {
                    return false;
                }
            }
            Terminator::Assert { cond, expected, .. } => {
                // (a) the accumulator's own `CheckedAdd(..).1` overflow assert —
                //     the very obligation being refuted, so it must NOT be
                //     required to hold; the encoding models it explicitly.
                let is_own_overflow_assert = matches!(
                    cond,
                    Operand::Copy(p) | Operand::Move(p)
                        if p.local == add_tuple_local
                            && p.projections.as_slice()
                                == [trust_types::Projection::Field(1)]
                );
                if is_own_overflow_assert {
                    continue;
                }
                // (b) a statically constant-true assert (rustc's shift-amount
                //     check for a CONSTANT shift, `assert(Le(4u32, 7u32))`).
                //     It cannot fail, so it cannot cut the prefix short.
                if fold_const_bool(func, cond, 8) == Some(*expected) {
                    continue;
                }
                // No lane for a `CheckedBinaryOp(Shl|Shr)` overflow flag: that
                // spelling is structurally rejected as MalformedTrustIr by
                // `validate_function` before this walk (only Add/Sub/Mul are
                // admitted checked carriers), so it can never reach here.
                return false;
            }
            _ => return false,
        }
    }
    next_calls == 1
}

// ── P2's precondition channel ───────────────────────────────────────────────
//
// `VerifiableFunction::preconditions` is NOT the authored-contract channel. It
// is the BODY-HYPOTHESIS channel: `trust-mir-extract` seeds it from the parsed
// `#[requires]` contracts and then unconditionally EXTENDS it with three
// synthesized type tautologies — enum-discriminant tag ranges, `char` scalar
// ranges, and integer-PARAMETER type ranges. Every `for &x in <fixed array>`
// lowers to an `Option` discriminant temp, so the discriminant tautology is
// present in EVERY body this module was written to recognize, and a blanket
// `!preconditions.is_empty()` refusal is dead on arrival against real MIR.
//
// The fix is NOT to trust the authored channels (`contracts` / `spec.requires`)
// and wave the rest through: that would make P2 depend on a completeness claim
// about a DIFFERENT crate ("an authored `#[requires]` always leaves a `Contract`
// row"), which this module cannot check and which could drift. Instead each
// surviving precondition must be POSITIVELY certified, from this body alone, as
// a fact that constrains no input beyond its own declared type. Exactly two
// shapes are certifiable locally; everything else — including a fact this module
// simply does not recognize — DECLINES.

/// The variable NAME a formula denotes, for both spellings of an integer-sorted
/// variable.
fn formula_var_name(f: &Formula) -> Option<&str> {
    match f {
        Formula::Var(name, Sort::Int) => Some(name.as_str()),
        Formula::SymVar(sym, Sort::Int) => Some(sym.as_str()),
        _ => None,
    }
}

/// An integer literal, in either spelling the extractor's facts can mint. The
/// enum tag facts are now `Formula::Int` throughout (`discriminant_tag_to_formula`
/// renders an already-DECODED `i128` tag), but the `UInt` arm stays: the
/// `switch_label_to_formula` decode still mints `UInt` for a `u128` label above
/// `i128::MAX`, and other fact producers use the spelling too.
fn formula_const_int(f: &Formula) -> Option<i128> {
    match f {
        Formula::Int(n) => Some(*n),
        Formula::UInt(u) => i128::try_from(*u).ok(),
        _ => None,
    }
}

/// Resolve a fact's variable NAME to the UNIQUE body local it denotes, using
/// exactly the two spellings the extractor's synthesized facts can use: the
/// local's source name (only when that name is unique across all locals — the
/// same uniqueness rule `integer_param_range_preconditions` applies) or the
/// positional `_<index>` fallback. Zero or MORE THAN ONE match ⇒ None; an
/// ambiguous binding is refused, never guessed.
fn resolve_fact_local(func: &VerifiableFunction, name: &str) -> Option<usize> {
    let parsed_local_index = name
        .strip_prefix('_')
        .filter(|rest| !rest.is_empty() && (*rest == "0" || !rest.starts_with('0')))
        .and_then(|rest| rest.parse::<usize>().ok());
    let mut name_is_unique: Option<bool> = None;
    let mut hit: Option<usize> = None;
    for decl in &func.body.locals {
        let named_uniquely = decl.name.as_deref() == Some(name)
            && *name_is_unique.get_or_insert_with(|| {
                func.body.locals.iter().filter(|d| d.name.as_deref() == Some(name)).count() == 1
            });
        if !named_uniquely && parsed_local_index != Some(decl.index) {
            continue;
        }
        if hit.is_some() {
            return None;
        }
        hit = Some(decl.index);
    }
    hit
}

/// Textual write count for a local, counting every channel the extractor's own
/// single-assignment gate counts (assignment, `SetDiscriminant`, `Deinit`, and a
/// call destination).
fn local_write_count(func: &VerifiableFunction, local: usize) -> usize {
    let mut writes = 0usize;
    crate::visit_local_write_candidates(func, &func.body.blocks, local, |block, item| match item {
        Some(stmt) => {
            let written = match stmt {
                Statement::Assign { place, .. }
                | Statement::SetDiscriminant { place, .. }
                | Statement::Deinit { place } => Some(place.local),
                _ => None,
            };
            if written == Some(local) {
                writes += 1;
            }
        }
        None => {
            if let Terminator::Call { dest, .. } = &block.terminator
                && dest.local == local
            {
                writes += 1;
            }
        }
    });
    writes
}

/// SHAPE 1 — the for-each desugar's `Option`-tag fact: `_d == 0 ∨ _d == 1` where
/// `_d` is the single-assignment discriminant temp of THIS loop's
/// `Iterator::next` result.
///
/// Certified entirely from this body: `_d` is a non-return, non-argument local
/// written exactly once, by `Discriminant(next_dest)` with `next_dest` the very
/// local `on_cycle_next_dest` identified as the `next()` destination, and the tag
/// set is literally `{0, 1}`. `Iterator::next` returns `Option<_>`, whose tags
/// ARE `{0, 1}` (the same std-library semantics P1 already rests on), so the fact
/// is a tautology and constrains nothing about the iterated array.
///
/// Pinning the source to `next_dest` and the tags to `{0, 1}` is what makes this
/// local: a tag-set fact about an ARBITRARY discriminant temp would need the
/// enum's full tag set to be a tautology, and that needs a `TyCtxt` this crate
/// does not have — so any other discriminant fact declines.
fn is_iterator_option_tag_fact(
    func: &VerifiableFunction,
    formula: &Formula,
    next_dest: usize,
) -> bool {
    let Formula::Or(disjuncts) = formula else { return false };
    if disjuncts.len() != 2 {
        return false;
    }
    let mut var: Option<&str> = None;
    let mut tags: Vec<i128> = Vec::with_capacity(2);
    for disjunct in disjuncts {
        let Formula::Eq(lhs, rhs) = disjunct else { return false };
        let (Some(name), Some(tag)) = (formula_var_name(lhs), formula_const_int(rhs)) else {
            return false;
        };
        if *var.get_or_insert(name) != name {
            return false;
        }
        tags.push(tag);
    }
    tags.sort_unstable();
    if tags != [0, 1] {
        return false;
    }
    let Some(name) = var else { return false };
    let Some(d) = resolve_fact_local(func, name) else { return false };
    if d == 0 || d <= func.body.arg_count || local_write_count(func, d) != 1 {
        return false;
    }
    if !matches!(crate::local_ty_ref(func, d), Some(Ty::Int { .. })) {
        return false;
    }
    matches!(
        crate::local_defs::unique_value_def(func, d),
        Some(Rvalue::Discriminant(p)) if p.local == next_dest && p.projections.is_empty()
    )
}

/// SHAPE 2 — an integer PARAMETER's own type range, `MIN_T <= p <= MAX_T`.
///
/// Certified entirely from this body: the bounds are compared against
/// `int_range` of the parameter's OWN declared integer type, so a genuinely
/// constraining range (`0 <= p <= 3` on a `u8`) does NOT match and declines. A
/// tautology of a parameter's type excludes no value the parameter can take, so
/// it cannot make a counterexample spurious — and the iterated array is never
/// integer-typed, so this shape can never speak about it at all.
fn is_integer_param_range_fact(func: &VerifiableFunction, formula: &Formula) -> bool {
    let Formula::And(conjuncts) = formula else { return false };
    let [Formula::Ge(lo_var, lo_bound), Formula::Le(hi_var, hi_bound)] = conjuncts.as_slice()
    else {
        return false;
    };
    let (Some(lo_name), Some(hi_name)) = (formula_var_name(lo_var), formula_var_name(hi_var))
    else {
        return false;
    };
    if lo_name != hi_name {
        return false;
    }
    let Some(p) = resolve_fact_local(func, lo_name) else { return false };
    if p == 0 || p > func.body.arg_count {
        return false;
    }
    let Some(Ty::Int { width, signed }) = crate::local_ty_ref(func, p) else { return false };
    // `u128`'s MAX has no `i128` spelling (`int_range` declines it): the generator
    // states that range as `0 <= p <= UInt(u128::MAX)` (INTRINSIC-RESIDUAL-1,
    // `generate::missing_param_type_range_facts`), and only that exact pair is it.
    if *width == 128 && !*signed {
        return matches!(lo_bound.as_ref(), Formula::Int(0))
            && matches!(hi_bound.as_ref(), Formula::UInt(u128::MAX));
    }
    let (Some(min), Some(max)) = (formula_const_int(lo_bound), formula_const_int(hi_bound)) else {
        return false;
    };
    int_range(*width, *signed) == Some((min, max))
}

/// P2's contract gate: no precondition may constrain the iterated input.
///
/// The authored channels (`spec.requires`, `contracts`) are refused, and what
/// survives in the body-hypothesis channel must be positively certified as one of
/// the two locally-checkable type tautologies above; an unrecognized fact
/// declines, so a future extractor change that pushes a new (or a genuinely
/// constraining) formula into `preconditions` closes this lane rather than
/// silently widening it.
///
/// # A TRAIT-INHERITED contract is invisible here, so trait impls are refused
///
/// Checking those three channels is NOT sufficient, and it is worth stating why
/// rather than leaving the reader to trust the list. A `#[trust::requires]`
/// declared on a TRAIT METHOD and inherited by an `impl` does not appear in ANY
/// of them on the impl's `VerifiableFunction`. Measured with the HEAD-matching
/// stage2 trustc (`-Ztrust-dump=mir:`) on
///
/// ```ignore (illustrative)
/// trait R { #[trust::requires(a[0] == 0)] fn f(&self, a: &[i128; 4]) -> i128; }
/// impl R for S { fn f(&self, a: &[i128; 4]) -> i128 { /* reduction */ } }
/// ```
///
/// the extracted function is `def_path: "<tr::S as tr::R>::f"` with
/// `contracts: []`, `spec.requires: []`, and `preconditions` holding ONLY the
/// Option-tag fact. The contract is not inert — Trust enforces it at CALL SITES —
/// so an input violating it is not a reachable execution, and a `Failed` row
/// naming such an input would accuse the callee of behaviour no legal caller can
/// produce. That is a FALSE REFUTATION, which is exactly what this refutation-only
/// lane must never emit.
///
/// Because the contract is invisible, it cannot be detected — so the whole SHAPE
/// is refused instead: a qualified `<Type as Trait>::method` `def_path` declines.
/// This is a spelling test used ONLY to REFUSE, so a false positive costs
/// completeness and never soundness; the inverse test would be unsound and is not
/// made. Both target fixtures are free functions (`shift_reduction_overflow::f`),
/// so this costs the lane nothing today.
fn preconditions_leave_the_input_free(func: &VerifiableFunction, next_dest: usize) -> bool {
    if func.def_path.starts_with('<') || func.def_path.contains(" as ") {
        return false;
    }
    if !func.spec.requires.is_empty() || !func.contracts.is_empty() {
        return false;
    }
    func.preconditions.iter().all(|formula| {
        is_iterator_option_tag_fact(func, formula, next_dest)
            || is_integer_param_range_fact(func, formula)
    })
}

/// P2: the iterated collection is an unconstrained function INPUT.
///
/// The operand must root at a PARAMETER local (`1..=arg_count`, rustc's dense
/// layout) that the body never writes, never `&mut`/raw borrows, and never
/// passes as a call destination. Only then do the array's `LEN` elements range
/// independently over the whole element type, which is what makes the free
/// per-iteration variables in the encoding faithful.
fn iterated_array_is_free_parameter(func: &VerifiableFunction, array_op: &Operand) -> bool {
    let Some(root) = deref_ref_root_local(func, array_op, 8) else { return false };
    if root == 0 || root > func.body.arg_count {
        return false;
    }
    !crate::any_local_write_candidate(func, &func.body.blocks, root, |block, item| match item {
        Some(stmt) => {
            let Statement::Assign { place, rvalue, .. } = stmt else { return false };
            place.local == root
                || matches!(
                    rvalue,
                    Rvalue::Ref { mutable: true, place: p } | Rvalue::AddressOf(_, p)
                        if p.local == root
                )
        }
        None => matches!(&block.terminator, Terminator::Call { dest, .. } if dest.local == root),
    })
}

/// Trace an operand to its root local through whole-local `Use` copies AND
/// through `&place` / `*place` reborrows (`_2 = &(*_1)`), which is how a
/// `&[T; N]` parameter reaches `into_iter`.
fn deref_ref_root_local(func: &VerifiableFunction, op: &Operand, fuel: u32) -> Option<usize> {
    if fuel == 0 {
        return None;
    }
    let (Operand::Copy(p) | Operand::Move(p)) = op else { return None };
    let base = p.local;
    if !p.projections.iter().all(|proj| matches!(proj, trust_types::Projection::Deref)) {
        return None;
    }
    match crate::local_defs::unique_value_def(func, base) {
        Some(Rvalue::Use(inner)) => deref_ref_root_local(func, inner, fuel - 1).or(Some(base)),
        Some(Rvalue::Ref { place, .. } | Rvalue::CopyForDeref(place))
            if place
                .projections
                .iter()
                .all(|proj| matches!(proj, trust_types::Projection::Deref)) =>
        {
            deref_ref_root_local(
                func,
                &Operand::Copy(Place::local(place.local)),
                fuel - 1,
            )
            .or(Some(place.local))
        }
        _ => Some(base),
    }
}

/// The one `Iterator::next` call whose block lies on the loop's cycle.
fn on_cycle_next_dest(func: &VerifiableFunction) -> Option<usize> {
    let mut found = None;
    for block in &func.body.blocks {
        if let Terminator::Call { func: callee, dest, .. } = &block.terminator
            && dest.projections.is_empty()
            && callee_is_iterator_next(callee)
            && block_is_on_cycle(func, block.id.0)
        {
            if found.is_some() {
                return None;
            }
            found = Some(dest.local);
        }
    }
    found
}

/// The single `CheckedBinaryOp(Add, acc, addend)` statement of the function, as
/// `(tuple dest local, accumulator local, addend operand, span, block id)`.
/// More than one ⇒ None: a second add is another obligation this encoding does
/// not model, and it could panic first.
fn sole_checked_add(
    func: &VerifiableFunction,
) -> Option<(usize, usize, Operand, SourceSpan, usize)> {
    let mut found = None;
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            let Statement::Assign {
                place: ck_dest,
                rvalue: Rvalue::CheckedBinaryOp(BinOp::Add, lhs, rhs),
                span,
            } = stmt
            else {
                continue;
            };
            if !ck_dest.projections.is_empty() {
                return None;
            }
            let (Operand::Copy(acc_p) | Operand::Move(acc_p)) = lhs else { return None };
            if !acc_p.projections.is_empty() {
                return None;
            }
            if found.is_some() {
                return None;
            }
            found = Some((ck_dest.local, acc_p.local, rhs.clone(), span.clone(), block.id.0));
        }
    }
    found
}

/// Is `local` defined by a constant EXACTLY ONCE, in a block that is NOT on the
/// loop's cycle? A const init INSIDE the loop would reset the accumulator every
/// iteration and make the unroll (and any refutation from it) wrong.
fn const_init_is_outside_loop(func: &VerifiableFunction, acc: usize) -> bool {
    !crate::any_local_write_stmt(func, &func.body.blocks, acc, |block, stmt| {
        let Statement::Assign { place, rvalue, .. } = stmt else { return false };
        if place.local != acc || !place.projections.is_empty() {
            return false;
        }
        let is_const = matches!(
            rvalue,
            Rvalue::Use(Operand::Constant(ConstValue::Int(_) | ConstValue::Uint(..)))
        );
        is_const && block_is_on_cycle(func, block.id.0)
    })
}

/// Recognize the BMC-refutable bounded reduction, or return None.
///
/// EVERY gate here is a soundness gate; see the module header for P1/P2/P3.
pub(super) fn recognize_bounded_reduction(func: &VerifiableFunction) -> Option<BmcReduction> {
    // rustc's dense local/block layout is assumed positionally by the shared MIR
    // helpers; a hand-built or deserialized body that violates it is refused.
    if !func.spec.requires.is_empty()
        || !func.contracts.is_empty()
        || func.def_path.starts_with('<')
        || func.def_path.contains(" as ")
        || func.body.arg_count == 0
        || func.body.arg_count >= func.body.locals.len()
        || func.body.blocks.len() < 2
        || !super::terminator_presence_for(func).has_bare_dest_call
        || !func.body.locals.iter().enumerate().all(|(i, d)| d.index == i)
        || !func.body.blocks.iter().enumerate().all(|(i, b)| b.id.0 == i)
    {
        return None;
    }
    let (add_tuple, acc_local, addend_op, location, add_block) = sole_checked_add(func)?;
    let acc_ty_ref = crate::local_ty_ref(func, acc_local)?;
    let acc_width = acc_ty_ref.int_width()?;
    if !acc_ty_ref.is_integer() {
        return None;
    }
    let acc_signed = acc_ty_ref.is_signed();
    let (acc_min, acc_max) = int_range(acc_width, acc_signed)?;
    // The addend: either the loop element itself / a value-preserving widening of
    // it, or that value left-shifted by a constant.
    let (elem_local, shift) = recognize_addend(func, &addend_op)?;
    // `acc`'s only two whole-local definitions are a constant init and the
    // self-add's `.0` — and it is neither call-clobbered nor mutably aliased.
    let init = accumulator_init_const(func, acc_local, add_tuple)?;
    if init < acc_min || init > acc_max {
        return None;
    }
    // EXACTLY one loop, with a statically known trip count. `count_back_edges == 1`
    // plus `total_loop_iterations` (which requires #on-cycle-`next` == #back-edges)
    // makes `K` the EXACT trip count of the one loop, not a product over several —
    // for every loop that runs at least once. Trust (2026-10-04, TRIP-ZERO-PRODUCT-1):
    // `total_loop_iterations` reports a zero-trip loop as the factor 1, an UPPER
    // bound that is no longer exact. This lane stays exact without a gate of its own:
    // a zero-trip for-each runs over a `[T; 0]`, and the `elem_len == trip` check below
    // refuses it (0 != 1). (The lane is refutation-only besides: no `trip` it reads
    // can grant a proof.)
    if count_back_edges(func) != 1 {
        return None;
    }
    let trip = total_loop_iterations(func)?;
    if !(1..=BMC_MAX_UNROLL).contains(&trip) {
        return None;
    }
    let next_dest = on_cycle_next_dest(func)?;
    // A contract could constrain the input array, breaking P2's "elements range
    // freely" premise. Refuse any function carrying one, and refuse any body
    // hypothesis this module cannot certify as a type tautology of THIS body.
    // Ordered after `on_cycle_next_dest` only because the certification needs the
    // `next()` destination local; every gate here is drop-only, so order carries
    // no soundness weight.
    if !preconditions_leave_the_input_free(func, next_dest) {
        return None;
    }
    // The accumulation must be INSIDE the loop.
    if !block_is_on_cycle(func, add_block) {
        return None;
    }
    if !const_init_is_outside_loop(func, acc_local) {
        return None;
    }
    let acc_ty = acc_ty_ref.clone();

    // The element must be the for-each element of a FIXED-SIZE array whose length
    // IS the trip count (so `x_j` really is the j-th element of the iterated array).
    let (elem_ty, elem_len, array_op) = for_each_array_source(func, elem_local)?;
    if i128::from(elem_len) != trip {
        return None;
    }
    if !iterated_array_is_free_parameter(func, &array_op) {
        return None;
    }
    let elem_width = elem_ty.int_width()?;
    if !elem_ty.is_integer() {
        return None;
    }
    let (elem_min, elem_max) = int_range(elem_width, elem_ty.is_signed())?;
    // `x as ACC` must be VALUE-PRESERVING: a narrowing/sign-changing cast wraps,
    // and the linear encoding below has no modular semantics for it.
    if !range_fits(elem_min, elem_max, acc_min, acc_max) {
        return None;
    }
    if let Some(k) = shift {
        // The shift lane is UNSIGNED-accumulator only: `(v << k) mod 2^W` is
        // encoded by the `2^(W-k)` split below, which is a statement about the
        // UNSIGNED bit pattern. A signed accumulator would additionally need the
        // two's-complement reinterpretation, so it declines.
        if acc_signed || elem_ty.is_signed() {
            return None;
        }
        if k >= acc_width {
            return None;
        }
        // Every constant the encoder emits must fit `i128`.
        pow2(k)?;
        pow2(acc_width - k)?;
        pow2(acc_width)?;
    }

    let reachable = reachable_blocks(func);
    if !body_is_straight_line_reduction(func, &reachable, next_dest, add_tuple) {
        return None;
    }

    Some(BmcReduction {
        acc_width,
        acc_signed,
        init,
        trip,
        elem_min,
        elem_max,
        shift,
        location,
        acc_ty,
    })
}

/// `(element local, optional constant left-shift)` for the two recognized addend
/// shapes: `t += x` / `t += x as ACC` (no shift), and `t += (x as ACC) << k`.
fn recognize_addend(func: &VerifiableFunction, addend: &Operand) -> Option<(usize, Option<u32>)> {
    let (Operand::Copy(p) | Operand::Move(p)) = addend else { return None };
    if !p.projections.is_empty() {
        return None;
    }
    // Shape B: `(x as ACC) << k`, direct or via a checked `Shl`'s `.0`.
    if let Some((base, shift_op)) = reduction_shl_operands(func, p.local) {
        let k = operand_const_int(&shift_op)?;
        let k = u32::try_from(k).ok()?;
        let elem = cast_or_direct_element(func, &base)?;
        return Some((elem, Some(k)));
    }
    // Shape A: `x` or `x as ACC`.
    let elem = cast_or_direct_element(func, addend)?;
    Some((elem, None))
}

/// The element local under `x` or under `x as ACC` (one cast hop, whole locals only).
fn cast_or_direct_element(func: &VerifiableFunction, op: &Operand) -> Option<usize> {
    let (Operand::Copy(p) | Operand::Move(p)) = op else { return None };
    if !p.projections.is_empty() {
        return None;
    }
    match crate::local_defs::unique_value_def(func, p.local) {
        Some(Rvalue::Cast(Operand::Copy(xp) | Operand::Move(xp), _))
            if xp.projections.is_empty() =>
        {
            Some(xp.local)
        }
        _ => Some(p.local),
    }
}

// ── the encoding ────────────────────────────────────────────────────────────

fn bmc_var(prefix: &str, j: i128) -> Formula {
    Formula::Var(format!("__trust_bmc_{prefix}{j}"), Sort::Int)
}

fn le(l: Formula, r: Formula) -> Formula {
    Formula::Le(Box::new(l), Box::new(r))
}
fn ge(l: Formula, r: Formula) -> Formula {
    Formula::Ge(Box::new(l), Box::new(r))
}
fn eq(l: Formula, r: Formula) -> Formula {
    Formula::Eq(Box::new(l), Box::new(r))
}
fn add(l: Formula, r: Formula) -> Formula {
    Formula::Add(Box::new(l), Box::new(r))
}
fn mul(l: Formula, r: Formula) -> Formula {
    Formula::Mul(Box::new(l), Box::new(r))
}

/// The COMPLETE unroll's violation formula.
///
/// Variables (all `Sort::Int`, all fresh — the `__trust_bmc_` prefix cannot
/// collide with `place_to_var_name`'s `_N` spellings):
///   * `elem{j}` — the j-th array element, `j ∈ [0, K)`.
///   * `acc{j}`  — the MATHEMATICAL running sum after `j` adds, `j ∈ [0, K]`.
///   * `shl_lo{j}` / `shl_hi{j}` — the shift lane's exact split (below).
///
/// Constraints:
///   * `acc0 = init`, and `acc{j+1} = acc{j} + A_j` where `A_j` is the addend.
///     These are UNBOUNDED-integer equations, so `acc{j}` is the TRUE sum, not a
///     wrapped one.
///   * `elem_min <= elem{j} <= elem_max`  (P2: the element is a free input).
///   * Addend `A_j`:
///       - no shift:  `A_j = elem{j}`  (the cast was checked value-preserving).
///       - shift `k`: `(v << k) mod 2^W`. Writing `v = hi*2^(W-k) + lo` with
///         `0 <= lo < 2^(W-k)` gives `v*2^k = hi*2^W + lo*2^k`, hence
///         `(v << k) mod 2^W = lo * 2^k`. So `A_j = 2^k * shl_lo{j}` with
///         `elem{j} = shl_hi{j} * 2^(W-k) + shl_lo{j}`, `0 <= shl_lo{j} < 2^(W-k)`,
///         `shl_hi{j} >= 0`. This is EXACT and purely LINEAR — deliberately NOT
///         the `IntToBv`/`BvShl`/`BvToInt` bridge, which ay leaves Unknown (see
///         `wide_unsigned_accumulator_int2bv_vc_never_panics` in trust-router and
///         the note in `build_accumulator_bound_facts`).
///
/// Goal: `OR_{j<K} (acc{j+1} > ACC_MAX  ∨  acc{j+1} < ACC_MIN)`.
///
/// WHY THE BARE DISJUNCTION IS EXACT (and why no "prefix stayed in range" guard
/// is needed): let `i` be the SMALLEST index with `acc{i+1}` out of range. Every
/// `j <= i` has `acc{j}` in range, so for the first `i` adds the machine value of
/// the accumulator EQUALS the mathematical `acc{j}` — no wrap, no panic, and the
/// loop reaches iteration `i` (P1/P3). At iteration `i` the machine computes
/// `acc{i} + A_i = acc{i+1}`, which is outside the accumulator type: the add
/// overflows. So any model of this formula names concrete array elements on which
/// the program really does overflow. Conversely an overflowing execution makes
/// some `acc{j+1}` out of range, so the formula is also COMPLETE for this shape —
/// but completeness is not relied on anywhere: UNSAT is DROPPED by the consumer.
///
/// SIZE: `O(K)` atoms, each of constant size. `K = 64` is a few hundred atoms.
fn build_unrolled_violation(red: &BmcReduction) -> Option<Formula> {
    let (acc_min, acc_max) = int_range(red.acc_width, red.acc_signed)?;
    let mut conj: Vec<Formula> = Vec::with_capacity(
        2 + (red.trip as usize) * if red.shift.is_some() { 7 } else { 3 },
    );
    conj.push(eq(bmc_var("acc", 0), Formula::Int(red.init)));

    let two_k = match red.shift {
        Some(k) => Some(pow2(k)?),
        None => None,
    };
    let split = match red.shift {
        Some(k) => Some(pow2(red.acc_width - k)?),
        None => None,
    };

    for j in 0..red.trip {
        let x = bmc_var("elem", j);
        conj.push(ge(x.clone(), Formula::Int(red.elem_min)));
        conj.push(le(x.clone(), Formula::Int(red.elem_max)));
        let addend = match (two_k, split) {
            (Some(two_k), Some(split)) => {
                let lo = bmc_var("shl_lo", j);
                let hi = bmc_var("shl_hi", j);
                conj.push(ge(lo.clone(), Formula::Int(0)));
                conj.push(le(lo.clone(), Formula::Int(split - 1)));
                conj.push(ge(hi.clone(), Formula::Int(0)));
                conj.push(eq(x, add(mul(hi, Formula::Int(split)), lo.clone())));
                mul(Formula::Int(two_k), lo)
            }
            _ => x,
        };
        conj.push(eq(bmc_var("acc", j + 1), add(bmc_var("acc", j), addend)));
    }

    let goal = Formula::Or(
        (0..red.trip)
            .map(|j| {
                let acc_next = bmc_var("acc", j + 1);
                Formula::Or(vec![
                    Formula::Gt(Box::new(acc_next.clone()), Box::new(Formula::Int(acc_max))),
                    Formula::Lt(Box::new(acc_next), Box::new(Formula::Int(acc_min))),
                ])
            })
            .collect(),
    );
    conj.push(goal);
    Some(Formula::And(conj))
}

/// REFUTATION-ONLY BMC candidates for a bounded fixed-array reduction whose
/// accumulator can overflow.
///
/// Returns at most ONE candidate. Its `formula` is the VIOLATION formula (the
/// router convention: SAT ⇒ counterexample, UNSAT ⇒ property holds), and its
/// `kind` is the REAL Level-0 obligation the counterexample violates
/// (`ArithmeticOverflow { op: Add }` at the accumulator's type), so a consumer
/// that appends a `Failed` row for it lands in `strict_l0_verification_failure`'s
/// `failed` arm.
///
/// The consumer MUST drop everything except a SAT verdict carrying a non-empty
/// model. An UNSAT answer here is NOT a proof of the surrounding function: the
/// formula speaks only about this one reduction, and this producer deliberately
/// carries no proof authority.
#[must_use]
pub fn generate_bounded_reduction_bmc_refutation_candidates(
    func: &VerifiableFunction,
) -> Vec<VerificationCondition> {
    if crate::validate_function(func).is_err() {
        return Vec::new();
    }
    // verifier-perf: the same whole-function gate every other refute-only
    // producer applies. DROP-ONLY — withholding a candidate leaves the build at
    // its existing (already fail-closed) verdict.
    if func_exceeds_vcgen_budget(func) {
        return Vec::new();
    }
    let Some(red) = recognize_bounded_reduction(func) else {
        return Vec::new();
    };
    let Some(formula) = build_unrolled_violation(&red) else {
        return Vec::new();
    };
    vec![VerificationCondition {
        kind: VcKind::ArithmeticOverflow {
            op: BinOp::Add,
            operand_tys: (red.acc_ty.clone(), red.acc_ty.clone()),
        },
        function: Symbol::intern(&func.def_path),
        location: red.location.clone(),
        formula,
        contract_metadata: None,
        obligation: None,
    }]
}

/// [`generate_bounded_reduction_bmc_refutation_candidates`] into the caller's context
/// `rows`, the body's (T3 C07p, design D-VC-1): every candidate is interned through the row
/// oracle and the candidates are returned as generated.
#[must_use]
pub fn generate_bounded_reduction_bmc_refutation_candidates_rows(
    func: &VerifiableFunction,
    rows: &mut trust_types::vc_context::VcContext,
) -> Vec<VerificationCondition> {
    let candidates = generate_bounded_reduction_bmc_refutation_candidates(func);
    intern_eager_rows(rows, &candidates);
    candidates
}

#[cfg(test)]
mod tests;
