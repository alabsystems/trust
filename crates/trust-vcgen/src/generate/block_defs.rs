// Per-block definitional facts and the versioning that keeps them sound. A
// fact established in one block is only usable at a program point where the
// subject has not been redefined, so every fact is rebound to the SSA version
// live at its use site.

use super::*;

pub(super) fn v2_block_span(func: &VerifiableFunction, block: &trust_types::BasicBlock) -> SourceSpan {
    block
        .stmts
        .iter()
        .find_map(|stmt| match stmt {
            Statement::Assign { span, .. } => Some(span.clone()),
            _ => None,
        })
        .unwrap_or_else(|| func.span.clone())
}

pub(super) fn v2_is_float_operand(func: &VerifiableFunction, operand: &Operand) -> bool {
    matches!(crate::operand_ty_cow(func, operand).as_deref(), Some(trust_types::Ty::Float { .. }))
}

/// Is `divisor` a literal constant guaranteed to be nonzero? If so, we can
/// skip emitting the divzero VC entirely — it's trivially proved-safe.
pub(super) fn v2_divisor_is_nonzero_constant(divisor: &Operand) -> bool {
    match divisor {
        Operand::Constant(ConstValue::Int(v)) => *v != 0,
        Operand::Constant(ConstValue::Uint(v, _)) => *v != 0,
        Operand::Constant(ConstValue::Float(v)) => *v != 0.0,
        Operand::Constant(ConstValue::FloatBits { bits, width }) => {
            !crate::float_bits_magnitude_is_zero(*bits, *width)
        }
        _ => false,
    }
}

/// Ungated mirror of [`v2_divisor_is_nonzero_constant`]'s constant test, callable
/// from the hardened-profile pass. Kept separate so the hardened pass can share
/// the same classification without duplicating the main safety-lane walk.
pub(super) fn divrem_divisor_const_is_nonzero(divisor: &Operand) -> bool {
    match divisor {
        Operand::Constant(ConstValue::Int(v)) => *v != 0,
        Operand::Constant(ConstValue::Uint(v, _)) => *v != 0,
        Operand::Constant(ConstValue::Float(v)) => *v != 0.0,
        Operand::Constant(ConstValue::FloatBits { bits, width }) => {
            !crate::float_bits_magnitude_is_zero(*bits, *width)
        }
        _ => false,
    }
}

/// For a `Div`/`Rem`-by-zero `Assert` terminator at `assert_block`, decide whether
/// the divisor of the guarded `Div`/`Rem` operation is a NONZERO CONSTANT — the
/// exact condition under which the per-statement Div/Rem safety VC is (soundly)
/// suppressed (`v2_divisor_is_nonzero_constant`). The actual `Rvalue::BinaryOp(Div
/// |Rem, _, divisor)` lives in the assert's SUCCESS-TARGET block (the standard
/// `bbN: assert(d != 0) -> bbM; bbM: _x = Div(a, d)` MIR shape), so we scan the
/// target block first, then the assert block itself as a fallback.
///
/// FAIL-CLOSED: if no in-scope `Div`/`Rem` rvalue with a nonzero-constant divisor
/// is found (symbolic divisor, divisor not locatable, or zero constant), returns
/// `false` so the caller KEEPS the hardened twin — a real or unknown
/// division-by-zero stays refutable. Returning `true` only for a provably-nonzero
/// constant divisor can never mask a reachable panic.
pub(crate) fn v2_block_divrem_divisor_is_nonzero_constant(
    func: &VerifiableFunction,
    assert_block: &trust_types::BasicBlock,
) -> bool {
    let Terminator::Assert { target, .. } = &assert_block.terminator else {
        return false;
    };

    let block_has_nonzero_const_divrem = |block: &trust_types::BasicBlock| -> bool {
        block.stmts.iter().any(|stmt| {
            matches!(
                stmt,
                Statement::Assign {
                    rvalue: Rvalue::BinaryOp(BinOp::Div | BinOp::Rem, _, divisor),
                    ..
                } if divrem_divisor_const_is_nonzero(divisor)
            )
        })
    };

    // The divisor must additionally NOT be a nonzero constant in ANY in-scope
    // Div/Rem whose divisor is symbolic — but a symbolic Div/Rem simply yields
    // `false` from the const test, so a block carrying BOTH a const-divisor and a
    // symbolic-divisor div/rem would still be suppressed. That cannot happen here:
    // one assert guards exactly one div/rem operation. We require the located
    // div/rem to have a nonzero-constant divisor.
    if let Some(tb) = func.body.blocks.iter().find(|b| b.id == *target)
        && block_has_nonzero_const_divrem(tb)
    {
        return true;
    }
    block_has_nonzero_const_divrem(assert_block)
}

/// The set of `BoundsCheck` `Assert` blocks whose checked index is PROVABLY in
/// range via a loop-yield bound — a `for i in 0..s.len()` exclusive-range yield
/// ([`build_range_yield_guard_map`]) or a `for (i, _) in s.iter().enumerate()`
/// index yield ([`build_enumerate_yield_guard_map`]) that establishes
/// `index < len` for the SAME length the assert checks. The hardened
/// panic-boundary lane SKIPS emitting its `BoundsCheck` twin for these blocks,
/// mirroring the Div/Rem nonzero-constant skip
/// (`v2_block_divrem_divisor_is_nonzero_constant`): the per-statement bounds VC
/// already PROVES the access via the SAME yield fact — a fact the per-statement
/// lane conjoins onto the bounds VC but the hardened twin does NOT — so without
/// the skip the twin over-refutes a provably-safe guarded index (per-statement
/// PROVED while the hardened twin FAILS).
///
/// Computed once per function (both yield maps are built a single time) and empty
/// when the function has no range/enumerate yield payloads, so this is a no-op for
/// non-looping code.
///
/// SOUND under-approximation: a block is included ONLY when a yield fact of the
/// exact form `Lt(index, len)` — `index` naming the asserted index local and `len`
/// STRUCTURALLY equal to the canonicalized asserted length — is present. An
/// unguarded / constant / derived / projected index, or a loop over a DIFFERENT
/// bound (`for i in 0..K { v[i] }`, `K != v.len()`), is NOT included and keeps its
/// refutable twin; skipping only a genuinely-in-range index can never mask a real
/// out-of-bounds panic.
pub(crate) fn v2_boundscheck_index_in_range_skip_set(
    func: &VerifiableFunction,
) -> std::collections::HashSet<BlockId> {
    let mut skip = std::collections::HashSet::new();
    let range_map = build_range_yield_guard_map(func);
    let enumerate_map = build_enumerate_yield_guard_map(func);
    if range_map.is_empty() && enumerate_map.is_empty() {
        return skip;
    }
    for block in &func.body.blocks {
        if v2_boundscheck_index_provably_in_range(func, block, &range_map, &enumerate_map) {
            skip.insert(block.id);
        }
    }
    skip
}

/// True iff the `BoundsCheck` `Assert` at `assert_block` checks an index that a
/// loop-yield fact (range or enumerate) proves is `< len` for the SAME length the
/// assert checks. See [`v2_boundscheck_index_in_range_skip_set`] for the soundness
/// argument. Returns `false` (fail-closed) for any non-`BoundsCheck` assert, a
/// non-`Lt`/`expected == false` condition, a non-plain-local index, or a length
/// that does not structurally match a yield fact's upper bound.
pub(super) fn v2_boundscheck_index_provably_in_range(
    func: &VerifiableFunction,
    assert_block: &trust_types::BasicBlock,
    range_map: &FxHashMap<BlockId, Vec<Formula>>,
    enumerate_map: &FxHashMap<BlockId, Vec<Formula>>,
) -> bool {
    const TRACE_FUEL: u32 = 16;
    let Terminator::Assert { cond, expected: true, msg: AssertMessage::BoundsCheck, .. } =
        &assert_block.terminator
    else {
        return false;
    };
    // The bounds assert is `assert(Lt(index, len))`; recover the index/len operands
    // from the `_c = Lt(index, len)` definition in this block.
    let Some((BinOp::Lt, index_op, len_op)) = v2_find_condition_binary_operands(assert_block, cond)
    else {
        return false;
    };
    // The index must be a plain (projection-free) local to be a loop-yield payload;
    // a constant or projected index carries no yield bound and stays refutable.
    let index_name = match index_op {
        Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => {
            place_to_var_name(func, p)
        }
        _ => return false,
    };
    // Canonicalize the checked length the SAME way the yield-fact END is
    // canonicalized (a `Len`/`PtrMetadata` temp -> `slice_len_formula(s)`), so the
    // two compare structurally exactly when they name the same slice's length.
    let checked_len = resolve_range_bound_formula(func, len_op, TRACE_FUEL);

    let yields_index_lt_checked_len = |facts: &[Formula]| -> bool {
        facts.iter().any(|fact| match fact {
            Formula::Lt(lo, hi) => {
                matches!(lo.as_ref(), Formula::Var(name, _) if *name == index_name)
                    && hi.as_ref() == &checked_len
            }
            _ => false,
        })
    };

    range_map.get(&assert_block.id).is_some_and(|facts| yields_index_lt_checked_len(facts))
        || enumerate_map
            .get(&assert_block.id)
            .is_some_and(|facts| yields_index_lt_checked_len(facts))
}

/// Build a divisor-is-zero formula for `BinaryOp(Div|Rem, _, divisor)`.
///
/// For constant divisors this reduces to `Bool(divisor == 0)` (always UNSAT
/// for nonzero constants, always SAT for literal zero). For variable divisors
/// it emits `var == 0`, which is satisfiable iff the divisor can be zero —
/// the solver finds a witness assignment and the VC is reported as Failed.
pub(super) fn v2_divisor_is_zero_formula(func: &VerifiableFunction, divisor: &Operand) -> Formula {
    match divisor {
        Operand::Constant(ConstValue::Int(v)) => Formula::Bool(*v == 0),
        Operand::Constant(ConstValue::Uint(v, _)) => Formula::Bool(*v == 0),
        Operand::Constant(ConstValue::Float(v)) => Formula::Bool(*v == 0.0),
        Operand::Constant(ConstValue::FloatBits { bits, width }) => {
            Formula::Bool(crate::float_bits_magnitude_is_zero(*bits, *width))
        }
        // A typed opaque integer constant divisor (const-generic `N`, associated
        // const, `size_of::<T>()` in a generic body) carries NO decidable value, so
        // it MIGHT be zero. Emit the satisfiable `opaque_symbol == 0` — NOT the
        // `Bool(false)` "provably nonzero" below — so the div/rem-by-zero obligation
        // stays Failed/Unknown (never falsely Proved). Reusing `operand_to_formula`'s
        // by-name opaque symbol also lets a dominating `if N != 0 { … }` guard on the
        // same operand legitimately discharge it. THIS ARM MUST PRECEDE the
        // `Operand::Constant(_) => Bool(false)` catch-all below.
        Operand::Constant(ConstValue::OpaqueScalar { .. }) => Formula::Eq(
            Box::new(operand_to_formula(func, divisor)),
            Box::new(v2_zero_formula_for_operand(func, divisor)),
        ),
        // Trust: piece #7a — a const-generic PARAM divisor (`x / N`) carries NO
        // decidable value, so it MIGHT be zero. Emit the satisfiable
        // `constparam_symbol == 0` — NOT the `Bool(false)` "provably nonzero"
        // catch-all below — so `x / N` stays Failed/Unknown, never falsely Proved.
        // Reusing `operand_to_formula`'s per-param symbol also lets a dominating
        // `if N != 0 { … }` guard legitimately discharge it. THIS ARM MUST PRECEDE
        // the `Operand::Constant(_) => Bool(false)` catch-all, exactly like the
        // `OpaqueScalar` arm above. Without it, `x / N` would false-prove.
        Operand::Constant(ConstValue::ConstParam { .. }) => Formula::Eq(
            Box::new(operand_to_formula(func, divisor)),
            Box::new(v2_zero_formula_for_operand(func, divisor)),
        ),
        // Reachability invariant for the catch-all below. `Bool(false)` means
        // "divisor provably nonzero", which discharges the div/rem-by-zero
        // obligation as Proved — so this arm must NEVER see a constant of
        // unknown value, or it would be a false PROVE. It cannot: the
        // non-numeric/unknown-valued constants are `ConstValue::OpaqueConst`
        // — minted solely for (a) f16/f128 scalars (float-typed divisions route
        // to `FloatDivisionByZero` via the `is_float` lhs-gate, never reaching an
        // integer div-by-zero fold) and (b) aggregates, which cannot be a divisor —
        // and `ConstValue::OpaqueScalar` / `ConstValue::ConstParam`, both handled
        // by the explicit arms ABOVE. Divisors with a known value lower to
        // Int/Uint/Float/FloatBits, handled above. So every constant reaching this
        // arm is nonzero by construction.
        Operand::Constant(_) => Formula::Bool(false),
        Operand::Copy(_) | Operand::Move(_) | Operand::Symbolic(_) => {
            let value = match divisor {
                Operand::Copy(_) | Operand::Move(_) => operand_to_formula(func, divisor),
                Operand::Symbolic(formula) => formula.clone(),
                _ => unreachable!(),
            };
            if let Some(Ty::Float { width }) = crate::operand_ty_cow(func, divisor).as_deref() {
                v2_float_is_zero_formula(value, *width)
            } else {
                Formula::Eq(Box::new(value), Box::new(v2_zero_formula_for_operand(func, divisor)))
            }
        }
        _ => Formula::Bool(false),
    }
}

pub(super) fn v2_float_is_zero_formula(value: Formula, width: u32) -> Formula {
    Formula::Eq(
        Box::new(v2_float_magnitude_bits(value, width)),
        Box::new(Formula::BitVec { value: 0, width: width - 1 }),
    )
}

pub(super) fn v2_float_magnitude_bits(value: Formula, width: u32) -> Formula {
    Formula::BvExtract { inner: Box::new(value), high: width - 2, low: 0 }
}

pub(super) fn v2_zero_formula_for_operand(func: &VerifiableFunction, operand: &Operand) -> Formula {
    if v2_is_float_operand(func, operand) {
        Formula::BitVec { value: 0, width: 64 }
    } else if let Some(Sort::BitVec(width)) = crate::operand_sort(func, operand) {
        Formula::BitVec { value: 0, width }
    } else {
        match operand {
            Operand::Symbolic(formula) => v2_zero_formula_for_formula(formula),
            _ => Formula::Int(0),
        }
    }
}

pub(super) fn v2_zero_formula_for_formula(formula: &Formula) -> Formula {
    if let Some(width) = crate::formula_bit_width(formula) {
        Formula::BitVec { value: 0, width }
    } else {
        Formula::Int(0)
    }
}

pub(super) fn v2_guard_targets_matching(
    func: &VerifiableFunction,
    pred: impl Fn(&AssertMessage) -> bool,
) -> std::collections::HashSet<BlockId> {
    func.body
        .blocks
        .iter()
        .filter_map(|bb| match &bb.terminator {
            Terminator::Assert { msg, target, .. } if pred(msg) => Some(*target),
            _ => None,
        })
        .collect()
}

pub(super) fn v2_overflow_guard_targets(func: &VerifiableFunction) -> std::collections::HashSet<BlockId> {
    v2_guard_targets_matching(func, |msg| {
        matches!(msg, AssertMessage::Overflow(BinOp::Div | BinOp::Rem | BinOp::Shl | BinOp::Shr))
    })
}

pub(super) fn v2_bounds_guard_targets(func: &VerifiableFunction) -> std::collections::HashSet<BlockId> {
    v2_guard_targets_matching(func, |msg| matches!(msg, AssertMessage::BoundsCheck))
}

pub(super) fn v2_negation_guard_targets(func: &VerifiableFunction) -> std::collections::HashSet<BlockId> {
    v2_guard_targets_matching(func, |msg| matches!(msg, AssertMessage::OverflowNeg))
}

pub(super) fn v2_formula_with_block_defs(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    formula: Formula,
) -> Formula {
    v2_formula_with_block_defs_at_point(func, block, block.stmts.len(), formula)
}

/// Conjoin same-block definition facts onto a VC `formula`, with both sides
/// versioned at the staleness-class S2c granularity:
///
///   * the VC body (`formula`, the bare obligation goal) is renamed at the
///     USE-POINT `end` (the program point the obligation is taken at);
///   * each block-def is renamed at ITS OWN establish point
///     (`version_block_def_at_establish`).
///
/// A LIVE def carries the same `#token` as the body's reference (nothing rewrote
/// the place between its establish point and `end`), so they unify. A def whose
/// subject is HAVOCED or reassigned before `end` carries a stale `#token` that
/// the body's `#end` reference does not match — the kill's drop, by
/// name-disjointness, at statement granularity. `combine_relevant_block_defs`
/// then prunes the disconnected (stale) def as irrelevant.
pub(super) fn v2_formula_with_block_defs_at_point(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    end: usize,
    formula: Formula,
) -> Formula {
    v2_formula_with_block_defs_at_point_recorded(func, block, end, formula).0
}

/// As [`v2_formula_with_block_defs_at_point`], but also returns the pieces the
/// authenticated-obligation recorder needs: the terminal-versioned `body` (the raw
/// violation as it appears INSIDE the returned formula) and the block-defs KEPT (in
/// conjoin order). Trust: seeding `ObligationRecord.body = renamed_body` and
/// `wrappers = [ConjoinFactsLast { facts: kept }]` (omitted when `kept` is empty)
/// reconstructs the returned formula bit-for-bit — the body is recorded at the
/// point the emitter builds it, NOT re-parsed from the finished formula.
pub(super) fn v2_formula_with_block_defs_at_point_recorded(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    end: usize,
    formula: Formula,
) -> (Formula, Formula, Vec<Formula>) {
    let sv = StmtVersionCtx::build(func);
    let body = version_rename_at(&formula, &sv, func, block.id, end);
    // Trust (ARM-B): the VERSIONED extract keeps pure place-read defs across a
    // later same-block clobber — sound HERE ONLY because every def below is
    // stamped at its establish point (`version_block_def_at_establish`), so the
    // kept def pins the PRE-write value by name. This is what ties a closure's
    // `&mut`-upvar guard read to its use read (`_2 == _1.0*`, `_4 == _1.0*`
    // with no write between) — the last unified read-tie instance.
    let mut defs = guards::extract_block_definitions_until_versioned(func, block, end);
    defs.extend(extract_set_discriminant_definitions_until(func, block, end));
    // The same-block deref-store-havoc kill (`drop_havoced_block_defs`) is DELETED
    // here: the establish-point versioning below subsumes it — a def whose subject
    // is havoced by an opaque deref-store carries a `#establish` token that the
    // terminal-versioned `body` does not match, so it cannot constrain the
    // post-havoc obligation (the drop, by name-disjointness). Proven 0-residual by
    // `block_def_establish_subsumes_kill` across the corpus + battery, and the
    // falsification gate's 65 mutants stay refuted with the kill gone. (The
    // guard-THREADING lane in `build_semantic_guard_map` still uses the kill — that
    // is a separate staleness mechanism, not subsumed by this same-block versioning.)
    let defs: Vec<Formula> = defs
        .into_iter()
        .map(|d| version_block_def_at_establish(&sv, func, block, end, d))
        .collect();
    let (combined, kept) = combine_relevant_block_defs_recorded(defs, body.clone());
    (combined, body, kept)
}

/// The place name a block-definition fact DEFINES: the top-level lhs of an `Eq`
/// or a range comparison (`Lt`/`Le`/`Gt`/`Ge`), with any `#token` stripped.
/// `None` for shapes with no single defined subject.
pub(super) fn block_def_subject(def: &Formula) -> Option<String> {
    let lhs = match def {
        Formula::Eq(l, _)
        | Formula::Lt(l, _)
        | Formula::Le(l, _)
        | Formula::Gt(l, _)
        | Formula::Ge(l, _) => l,
        _ => return None,
    };
    match &**lhs {
        Formula::Var(name, _) => Some(name.split('#').next().unwrap_or(name).to_string()),
        // Float value-definitions wrap the destination var in `FpFromBits` to
        // lift its bit pattern into FP space (lhs = FpFromBits { bits: Var(dest) }).
        // The subject is the inner var — peek through so the staleness /
        // clobber-dedup / versioning machinery recognizes a def of `dest`.
        // (Without this a stale FP def could survive a reassignment of `dest`
        // and discharge a goal about the new value — a false-PROVE.)
        Formula::FpFromBits { bits, .. } => match &**bits {
            Formula::Var(name, _) => Some(name.split('#').next().unwrap_or(name).to_string()),
            _ => None,
        },
        _ => None,
    }
}

/// The statement index in `block` that ESTABLISHES `base`: the latest real
/// Assign/SetDiscriminant in `stmts[..end]` whose destination IS `base`. An
/// opaque deref-store is EXCLUDED — it HAVOCS `base` (the version oracle counts
/// it as a write, via `stmt_writes_name`) but does not textually DEFINE it, so it
/// is not an establish point. `None` when no in-block statement defines `base`.
pub(super) fn block_def_establish_stmt(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    base: &str,
    end: usize,
) -> Option<usize> {
    // `dest` establishes `base` iff it IS `base` or an ANCESTOR of it: a whole-local
    // aggregate write `agg = (..)` establishes the field def `agg.0`. A DESCENDANT
    // write (`agg.0.1 = w`) is deliberately NOT an establish point — it is a later
    // partial update that makes the `agg.0` def stale, which the terminal token
    // already reflects.
    let establishes = |dest: &str| -> bool {
        dest == base
            || (base.len() > dest.len()
                && base.starts_with(dest)
                && matches!(base.as_bytes()[dest.len()], b'.' | b'[' | b'*'))
            // Trust (P0 false-refutation, 2026-07-02): a borrow/raw-pointer write
            // `_6 = &raw const *dst` ESTABLISHES the synthetic metadata def
            // `_6__slice_len == dst__slice_len` that the block-def extraction
            // emits for it. Without this the tie fact has no establish point,
            // stays BARE under establish-versioning, and is name-disjoint from
            // the `#token`-versioned `PtrMetadata` read it must discharge — the
            // guarded `&mut [T]` index false-refutation. Must stay consistent
            // with `stmt_writes_name` (`write_covers_derived_slice_len`), which
            // mints the read token this def must match.
            || write_covers_derived_slice_len(dest, base)
    };
    (0..end.min(block.stmts.len())).rev().find(|&k| match &block.stmts[k] {
        Statement::Assign { place, .. } => {
            let is_opaque_deref =
                matches!(place.projections.first(), Some(trust_types::Projection::Deref))
                    && crate::deref_pointer_is_opaque(func, place.local);
            !is_opaque_deref && establishes(&crate::place_to_var_name(func, place))
        }
        Statement::SetDiscriminant { place, .. } => {
            establishes(&crate::place_to_var_name(func, place))
        }
        _ => false,
    })
}

/// Version a block-definition fact at ITS OWN establish point: every operand READ
/// is renamed to its value just BEFORE the defining statement `k` (read-point
/// `k`), and the DEFINED subject (top-level lhs) is renamed to its value just
/// AFTER `k` (point `k+1`). This pins the fact to the program point that produced
/// it, so the whole-VC terminal rename SKIPS it (already `#`-versioned) and a fact
/// about a subsequently-HAVOCED/reassigned place names a DIFFERENT variable than
/// the terminal-versioned body.
///
/// A self-referential rhs (`x = x + 1`) is handled correctly: the rhs `x` stays
/// at the old value (read-point `k`) while the lhs `x` advances to the new value
/// (`k+1`), so the fact is `x_new = x_old + 1`, never the unsatisfiable `x = x+1`.
///
/// Defs with no recoverable subject, or already-versioned array term defs
/// (`arr$L$vN`, their own version scheme), pass through unchanged.
pub(super) fn version_block_def_at_establish(
    sv: &StmtVersionCtx,
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    end: usize,
    def: Formula,
) -> Formula {
    let Some(subj) = block_def_subject(&def) else { return def };
    if subj.starts_with("arr$") {
        return def;
    }
    // A deref subject `x*` is established by the borrow `x = &..` of its base `x`.
    let base = subj.strip_suffix('*').unwrap_or(&subj).to_string();
    let Some(k) = block_def_establish_stmt(func, block, &base, end) else { return def };
    // 1. all reads at the read-point k (values BEFORE the defining write).
    let read_versioned = version_rename_at(&def, sv, func, block.id, k);
    // 2. re-version the DEFINED subject (top-level lhs) to k+1 (value AFTER it).
    let new_tok = sv.version_token_at(func, block.id, k + 1, &subj);
    rebind_block_def_subject(read_versioned, &subj, new_tok)
}

/// Replace the top-level lhs subject Var of a block-def fact with `subj` carrying
/// `tok` (`subj#tok`, or bare `subj` when `tok` is None). Only the DEFINED
/// position (operand 0 of the top-level Eq/range comparison) is touched; reads in
/// the rhs keep their read-point versions.
pub(super) fn rebind_block_def_subject(def: Formula, subj: &str, tok: Option<String>) -> Formula {
    // Rewrite the subject var to `subj` (optionally version-tokened `subj#tok`),
    // preserving an `FpFromBits` wrapper if the lhs is a float value-definition
    // (`FpFromBits { bits: Var(subj) }`). Rewriting the INNER var (not the
    // wrapper) is required so re-versioning of a reassigned float dest applies to
    // the FP def too — see `block_def_subject`.
    fn rewrite_lhs(l: &Formula, subj: &str, tok: &Option<String>) -> Formula {
        match l {
            Formula::Var(_, s) => match tok {
                Some(t) => Formula::Var(format!("{subj}#{t}"), s.clone()),
                None => Formula::Var(subj.to_string(), s.clone()),
            },
            Formula::FpFromBits { bits, eb, sb } => Formula::FpFromBits {
                bits: Box::new(rewrite_lhs(bits, subj, tok)),
                eb: *eb,
                sb: *sb,
            },
            other => other.clone(),
        }
    }
    match def {
        Formula::Eq(l, r) => Formula::Eq(Box::new(rewrite_lhs(&l, subj, &tok)), r),
        Formula::Lt(l, r) => Formula::Lt(Box::new(rewrite_lhs(&l, subj, &tok)), r),
        Formula::Le(l, r) => Formula::Le(Box::new(rewrite_lhs(&l, subj, &tok)), r),
        Formula::Gt(l, r) => Formula::Gt(Box::new(rewrite_lhs(&l, subj, &tok)), r),
        Formula::Ge(l, r) => Formula::Ge(Box::new(rewrite_lhs(&l, subj, &tok)), r),
        other => other,
    }
}

/// The statement that ESTABLISHES a block's assert-passed semantics: the
/// `CheckedBinaryOp` whose `.1` overflow flag the block's `Assert` terminator
/// tests. Its no-overflow facts are about the operand values READ there.
pub(super) fn assert_passed_establish_stmt(
    _func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
) -> Option<usize> {
    let Terminator::Assert { cond, expected: false, .. } = &block.terminator else {
        return None;
    };
    let p = match cond {
        Operand::Copy(p) | Operand::Move(p) => p,
        _ => return None,
    };
    if !matches!(p.projections.as_slice(), [trust_types::Projection::Field(1)]) {
        return None;
    }
    let tuple_local = p.local;
    block.stmts.iter().position(|s| {
        matches!(s, Statement::Assign { place, rvalue: Rvalue::CheckedBinaryOp(..), .. }
            if place.local == tuple_local && place.projections.is_empty())
    })
}

/// Version a THREADED assert-passed fact at its establish point. A definitional
/// fact (`_N.0 == result`) is pinned via `version_block_def_at_establish`; a purely
/// RELATIONAL fact (`min <= result`, operand ranges) has every operand versioned at
/// the `CheckedBinaryOp` read-point `k`. Entry params stay BARE (and ride the
/// exemption); an operand reassigned afterward names a different variable.
pub(super) fn version_assert_passed_fact(
    sv: &StmtVersionCtx,
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    k: usize,
    fact: Formula,
) -> Formula {
    if block_def_subject(&fact).is_some() {
        version_block_def_at_establish(sv, func, block, block.stmts.len(), fact)
    } else {
        version_rename_at(&fact, sv, func, block.id, k)
    }
}

/// Version a THREADED fact established by the block's TERMINATOR (a modeled
/// total-call / min / max / clamp bound on a `Call` dest). The terminator runs
/// after every statement, so the dest is pinned to the terminator marker `s{b}_t`
/// (matching the terminator-aware OUT in the inter-block oracle); other operands are
/// read at the block terminal. A successor that REASSIGNS the dest reads a distinct
/// token, disconnecting the stale bound.
pub(super) fn version_terminator_dest_fact(
    sv: &StmtVersionCtx,
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    dest_name: &str,
    fact: Formula,
) -> Formula {
    let read_versioned = version_rename_at(&fact, sv, func, block.id, block.stmts.len());
    let term_tok = format!("s{}_t", block.id.0);
    read_versioned.map(&mut |node| match node {
        Formula::Var(name, sort) if name.split('#').next() == Some(dest_name) => {
            Formula::Var(format!("{dest_name}#{term_tok}"), sort)
        }
        other => other,
    })
}

/// SOUNDNESS WITNESS for deleting `drop_havoced_block_defs`. The kill drops every
/// block-def whose free variables overlap a deref-store-havoc name. The
/// establish-point versioning makes that drop redundant for the DANGEROUS case (a
/// def whose SUBJECT is havoced: a stale value that could false-prove a post-havoc
/// obligation) — such a def is name-disjoint from the terminal-versioned body
/// exactly when it is stale (`est ≠ term`), and correctly CONNECTS when it is a
/// fresh post-havoc def (`est == term`). The non-dangerous case (only an RHS read
/// is havoced) is kept by the versioning at the read's pre-havoc value — sound,
/// and strictly more precise than the kill's conservative drop.
///
/// This returns the count of defs the kill drops that the versioning CANNOT pin
/// to an establish point yet whose SUBJECT is havoced — i.e. the residual for
/// which the kill would still be load-bearing. `0` across the corpus + battery ⟹
/// the versioning subsumes the kill and it can be deleted.
#[cfg(test)]
pub(crate) fn block_def_establish_subsumes_kill(func: &VerifiableFunction) -> usize {
    let mut residual = 0usize;
    for block in &func.body.blocks {
        let end = block.stmts.len();
        let havoc: FxHashSet<String> = deref_store_havoc_names(func, block).into_iter().collect();
        if havoc.is_empty() {
            continue;
        }
        let mut defs = guards::extract_block_definitions_until(func, block, end);
        defs.extend(extract_set_discriminant_definitions_until(func, block, end));
        for d in &defs {
            if formula_survives_redefs(d, &havoc) {
                continue; // the kill KEEPS this def — nothing to subsume.
            }
            let Some(subj) = block_def_subject(d) else {
                residual += 1; // kill drops a subject-less def; versioning can't pin it.
                continue;
            };
            let subj_havoced = havoc.iter().any(|h| place_names_overlap(&subj, h));
            if !subj_havoced {
                continue; // RHS-only havoc: versioning keeps the def soundly.
            }
            let base = subj.strip_suffix('*').unwrap_or(&subj).to_string();
            let pinned = !subj.starts_with("arr$")
                && block_def_establish_stmt(func, block, &base, end).is_some();
            if !pinned {
                residual += 1; // havoced subject the versioning could not establish-pin.
            }
        }
    }
    residual
}

// `drop_havoced_block_defs` (the deref-store-havoc staleness kill) was DELETED:
// both the same-block conjoin lane (`v2_formula_with_block_defs_at_point`) and the
// inter-block threading lane (`build_semantic_guard_map`) now establish-version
// their defs (`version_block_def_at_establish`) so a havoced subject is name-
// disjoint from the post-havoc read — the drop, achieved by the statement-granular
// version oracle. Subsumption is proven 0-residual by
// `block_def_establish_subsumes_kill`.
pub(super) fn v2_formula_with_block_defs_before_stmt(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    stmt_index: usize,
    formula: Formula,
) -> Formula {
    // Mid-block obligation: the use-point IS `stmt_index` (defs and body both
    // versioned up to there).
    v2_formula_with_block_defs_at_point(func, block, stmt_index, formula)
}

/// Attach only the block-definition conjuncts whose left-hand-side variables are
/// transitively referenced by the VC formula.
///
/// Block definitions capture the dataflow of an entire basic block, so a typical
/// VC formula sees defs for many locals (including ones it doesn't care about).
/// Irrelevant defs hurt the solver in two ways:
///
///   1. They expand the search space — more variables to reason about.
///   2. When the irrelevant def crosses theories (e.g., a bitwise-AND lowered as
///      `bv2nat(bvand(int2bv(x), int2bv(y)))`), it injects a hard mixed-Int/BV
///      subterm into a formula that would otherwise live in a single theory.
///      ay-incremental returns `unknown` on those mixed formulas (#leb128-shift),
///      so dropping irrelevant defs is the difference between Proved/Failed
///      results and Unknown.
///
/// This is a sound optimization: dropping conjuncts that share no variables with
/// the rest of the formula cannot change satisfiability.
/// Attach the relevant block-defs AND return the ones KEPT, in the exact order they
/// are conjoined (before `formula`). Trust: the
/// authenticated-obligation recorder seeds a `ConjoinFactsLast { facts: kept }`
/// wrapper from this so `reconstruct(body, [wrapper]) == And([kept.., body])`
/// reproduces the combined formula bit-for-bit. An empty `kept` means the combined
/// formula IS `formula` unchanged (no wrapper is recorded).
pub(super) fn combine_relevant_block_defs_recorded(
    defs: Vec<Formula>,
    formula: Formula,
) -> (Formula, Vec<Formula>) {
    if defs.is_empty() {
        return (formula, Vec::new());
    }

    let mut needed: FxHashSet<String> = FxHashSet::default();
    collect_formula_var_names(&formula, &mut needed);

    // Walk defs in reverse so a def of `_4 = _3` pulls in `_3`'s def too.
    let mut keep_rev: Vec<Formula> = Vec::new();
    for def in defs.into_iter().rev() {
        let mut def_vars: FxHashSet<String> = FxHashSet::default();
        collect_formula_var_names(&def, &mut def_vars);
        // Heuristic: a def is relevant iff its destination (the lhs of the top-level Eq, if any)
        // is in `needed`, OR any of its free variables intersects `needed`. Either way we add
        // every free variable of the def to `needed` so deeper dependencies are picked up next.
        let intersects = def_vars.iter().any(|name| needed.contains(name));
        if intersects {
            for name in def_vars {
                needed.insert(name);
            }
            keep_rev.push(def);
        }
    }

    if keep_rev.is_empty() {
        return (formula, Vec::new());
    }

    let kept: Vec<Formula> = keep_rev.into_iter().rev().collect();
    let mut conjuncts: Vec<Formula> = kept.clone();
    conjuncts.push(formula);
    (Formula::And(conjuncts), kept)
}

pub(super) fn collect_formula_var_names(formula: &Formula, out: &mut FxHashSet<String>) {
    match formula {
        Formula::Var(name, _) => {
            out.insert(name.as_str().to_string());
        }
        Formula::Bool(_) | Formula::Int(_) | Formula::UInt(_) | Formula::BitVec { .. } => {}
        Formula::Not(inner) | Formula::Neg(inner) => collect_formula_var_names(inner, out),
        Formula::BvNot(inner, _)
        | Formula::BvToInt(inner, _, _)
        | Formula::IntToBv(inner, _)
        | Formula::BvZeroExt(inner, _)
        | Formula::BvSignExt(inner, _) => collect_formula_var_names(inner, out),
        Formula::BvExtract { inner, .. } => collect_formula_var_names(inner, out),
        Formula::And(children) | Formula::Or(children) => {
            for child in children {
                collect_formula_var_names(child, out);
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
        | Formula::Mul(a, b)
        | Formula::Div(a, b)
        | Formula::Rem(a, b)
        | Formula::Select(a, b)
        | Formula::BvConcat(a, b)
        | Formula::BvAdd(a, b, _)
        | Formula::BvSub(a, b, _)
        | Formula::BvMul(a, b, _)
        | Formula::BvUDiv(a, b, _)
        | Formula::BvSDiv(a, b, _)
        | Formula::BvURem(a, b, _)
        | Formula::BvSRem(a, b, _)
        | Formula::BvAnd(a, b, _)
        | Formula::BvOr(a, b, _)
        | Formula::BvXor(a, b, _)
        | Formula::BvShl(a, b, _)
        | Formula::BvLShr(a, b, _)
        | Formula::BvAShr(a, b, _)
        | Formula::BvULt(a, b, _)
        | Formula::BvULe(a, b, _)
        | Formula::BvSLt(a, b, _)
        | Formula::BvSLe(a, b, _) => {
            collect_formula_var_names(a, out);
            collect_formula_var_names(b, out);
        }
        Formula::Ite(c, t, e) | Formula::Store(c, t, e) => {
            collect_formula_var_names(c, out);
            collect_formula_var_names(t, out);
            collect_formula_var_names(e, out);
        }
        Formula::Forall(bindings, body) | Formula::Exists(bindings, body) => {
            // Skip names introduced by the quantifier; they're locally bound.
            let mut child = FxHashSet::default();
            collect_formula_var_names(body, &mut child);
            for (name, _) in bindings {
                child.remove(name.as_str());
            }
            for name in child {
                out.insert(name);
            }
        }
        // IEEE-754 floating-point nodes: recurse into operands so the inner
        // var names (incl. the dest/operand vars inside `FpFromBits`) are
        // collected. Without this, float value-definitions would collect no
        // vars and be pruned as irrelevant (sound but inert); collecting them
        // lets the relevance filter and clobber-dedup track them correctly.
        Formula::FpNeg(a)
        | Formula::FpAbs(a)
        | Formula::FpIsNaN(a)
        | Formula::FpIsInfinite(a)
        | Formula::FpIsZero(a)
        | Formula::FpIsNormal(a)
        | Formula::FpIsSubnormal(a)
        | Formula::FpIsNegative(a)
        | Formula::FpIsPositive(a) => collect_formula_var_names(a, out),
        Formula::FpFromBits { bits, .. } => collect_formula_var_names(bits, out),
        Formula::FpRem(a, b)
        | Formula::FpMin(a, b)
        | Formula::FpMax(a, b)
        | Formula::FpEq(a, b)
        | Formula::FpLt(a, b)
        | Formula::FpLe(a, b)
        | Formula::FpGt(a, b)
        | Formula::FpGe(a, b)
        | Formula::FpSqrt(a, b) => {
            collect_formula_var_names(a, out);
            collect_formula_var_names(b, out);
        }
        Formula::FpAdd(a, b, c)
        | Formula::FpSub(a, b, c)
        | Formula::FpMul(a, b, c)
        | Formula::FpDiv(a, b, c) => {
            collect_formula_var_names(a, out);
            collect_formula_var_names(b, out);
            collect_formula_var_names(c, out);
        }
        Formula::FpFma(a, b, c, d) => {
            collect_formula_var_names(a, out);
            collect_formula_var_names(b, out);
            collect_formula_var_names(c, out);
            collect_formula_var_names(d, out);
        }
        // FP literals / rounding-mode carry no variables.
        Formula::FpConst { .. }
        | Formula::FpNaN { .. }
        | Formula::FpInf { .. }
        | Formula::FpZero { .. }
        | Formula::FpRoundingMode(_) => {}
        _ => {}
    }
}

pub(super) fn v2_formula_with_block_defs_at(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    stmt_index: Option<usize>,
    formula: Formula,
) -> Formula {
    match stmt_index {
        Some(index) => v2_formula_with_block_defs_before_stmt(func, block, index, formula),
        None => v2_formula_with_block_defs(func, block, formula),
    }
}

pub(super) fn v2_find_target_binary_operands(
    func: &VerifiableFunction,
    target: BlockId,
    op: BinOp,
) -> Option<(&Operand, &Operand)> {
    let block = func.body.blocks.get(target.0)?;
    v2_find_block_binary_operands(block, op)
}

pub(crate) fn v2_find_block_binary_operands(
    block: &trust_types::BasicBlock,
    op: BinOp,
) -> Option<(&Operand, &Operand)> {
    block.stmts.iter().find_map(|stmt| {
        let Statement::Assign { rvalue, .. } = stmt else {
            return None;
        };
        match rvalue {
            Rvalue::BinaryOp(stmt_op, lhs, rhs) | Rvalue::CheckedBinaryOp(stmt_op, lhs, rhs)
                if *stmt_op == op =>
            {
                Some((lhs, rhs))
            }
            _ => None,
        }
    })
}

pub(super) fn v2_find_condition_binary_operands<'a>(
    block: &'a trust_types::BasicBlock,
    cond: &Operand,
) -> Option<(BinOp, &'a Operand, &'a Operand)> {
    let cond_local = match cond {
        Operand::Copy(place) | Operand::Move(place) if place.projections.is_empty() => place.local,
        _ => return None,
    };

    block.stmts.iter().find_map(|stmt| {
        let Statement::Assign { place, rvalue, .. } = stmt else {
            return None;
        };
        if place.local != cond_local || !place.projections.is_empty() {
            return None;
        }
        match rvalue {
            Rvalue::BinaryOp(op, lhs, rhs) => Some((*op, lhs, rhs)),
            _ => None,
        }
    })
}

pub(crate) fn v2_find_target_neg_operand(
    func: &VerifiableFunction,
    target: BlockId,
) -> Option<&Operand> {
    let block = func.body.blocks.get(target.0)?;
    block.stmts.iter().find_map(|stmt| {
        let Statement::Assign { rvalue, .. } = stmt else {
            return None;
        };
        match rvalue {
            Rvalue::UnaryOp(trust_types::UnOp::Neg, operand) => Some(operand),
            _ => None,
        }
    })
}
