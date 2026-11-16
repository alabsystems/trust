// Counterexample GROUNDING: check a refuted row's model against the function's
// own definitions before anybody is shown it, and label it when it is not an
// execution of that function.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

//! Trust: 2026-09-19 — WHEN A BOUND CANNOT BE MINED, THE REFUTATION WAS
//! DELIVERED WITH A COUNTEREXAMPLE THAT CONTRADICTS THE PROGRAM.
//!
//! ```ignore (illustrative)
//! pub fn castu_unminable(a: i64, mut b: i64) -> i64 {
//!     let lim = (-1i32) as u32 as i64;          // lim IS 4294967295
//!     if a > -lim && a < lim && b > -lim && b < lim { b = a * b; }
//!     b
//! }
//! ```
//!
//! `a * b` over `|a|,|b| < 2^32` really can overflow `i64`, so `[overflow:mul]
//! FAILED` is a TRUE refutation. What the strict lane printed beside it was not:
//!
//! ```text
//! counterexample: _4 = 1, _6 = -1, a = 0, b = 0, lim = 1,
//!                 __trust_ovf_bv_lhs_a = 18446744073709551615,
//!                 __trust_ovf_bv_rhs__15 = 9223372036854775808
//! ```
//!
//! `0 * 0` does not overflow; `lim` is 4294967295 and cannot be 1; `_4` is
//! `(-1i32) as u32` and cannot be 1; and `__trust_ovf_bv_lhs_a` — the fresh
//! bitvector variable that STANDS FOR `a` — is `-1` in the same breath as
//! `a = 0`. A user is shown an impossible execution and sent to debug it.
//!
//! WHY THE MODEL LOOKS LIKE THAT — and why it is not a soundness defect. The
//! signed multiply's violation formula is a conjunction of two parts over
//! DISJOINT variable sets: a QF_BV overflow core over fresh
//! `__trust_ovf_bv_{role}_{base}` operand vars, and the Int-sorted rendering of
//! the dominating guards over the program's own locals (the interval backend
//! computes its operand boxes from the Int side; the BV side is what decides the
//! product). ay cannot dispatch that mixture as a whole, so
//! `trust_router::disjoint_components` refutes it COMPONENT-WISE and returns the
//! UNION of the component models — a model of the formula, by a composition that
//! is exactly valid (see that module). The formula, however, is weaker than the
//! program: no fact ties `__trust_ovf_bv_lhs_a` to `a`, and — this is the case
//! this module is named for — when the guard bound cannot be MINED neither side
//! carries a bound at all, so `lim` is free and the composed model is free to
//! contradict the program. (The shape this module was named for, `(-1i32) as
//! u32 as i64`, is no longer one of those: [`crate::const_expr`] models the
//! reinterpretation exactly as of 2026-09-21 and mines it. The un-minable
//! shapes that remain are the ones whose value the machine does not fix — an
//! `&mut`-escaped local above all, where the alias may have written it.)
//!
//! WHAT WAS FIXED, AND WHAT DELIBERATELY WAS NOT.
//!
//! * NOT the verdict. `Failed` stays `Failed`. Making the row `Unknown` would
//!   trade a sound refutation for a lost verdict, and this row's refutation is
//!   true.
//! * NOT by tying the fresh BV operand vars to the source names in the formula
//!   (candidate (a) of the report). The tie has to be a MIXED constraint
//!   (`a == bv2int(__trust_ovf_bv_lhs_a)`), which (i) makes the two components
//!   share a variable, so the disjoint-component lane stops applying and the row
//!   falls back to the whole-query `Unknown` the lane exists to recover — the
//!   forbidden direction — and (ii) is the QF_BV + NIA shape ay has no
//!   combined decision procedure for: it answers `incomplete`, phase
//!   `theory-combination`, with its executor refusal as the detail (recorded
//!   at the umul record in `generate::overflow_vc`). It buys nothing on a
//!   DECLINING row either: when no bound can be mined there is no fact to tie
//!   the operands to.
//! * The DIAGNOSTIC is fixed, at DELIVERY, per v7/D3 — a refusal must name its
//!   fix. Every model is REPLAYED through the function before it is delivered
//!   ([`replay`]), which is the real question and not a proxy for it: run the
//!   function on the inputs the model names and see whether it reaches a failing
//!   `Assert`.
//!
//!     * it does -> delivered as-is, with the fresh BV operand vars PROJECTED
//!       onto the source names they stand for, so the witness reads as an
//!       assignment to the program's own variables and not to the encoding's;
//!     * it does not, but a REPAIR built from those operand vars does -> that
//!       repaired input assignment is delivered instead. This is the "repair it"
//!       half, and it is verified rather than asserted: a candidate is delivered
//!       only after the replay has run the function on it and seen an assert
//!       fail. (`unguarded` above recovers `a = -1, b = i64::MIN`, which really
//!       does overflow, from a model that said `a = 0, b = 0`.)
//!     * neither -> one explicit `UNGROUNDED` entry naming each contradiction
//!       (the value the model named, the value the function's definitions
//!       compute) and naming the fix, and NO assignment at all.
//!
//!   Two NECESSARY conditions are checked first, because they hold even where
//!   the replay cannot decide: a local with a unique definition dominating every
//!   `Assert` carries the value that definition computes, and a
//!   `__trust_ovf_bv_{role}_{base}` var agrees with `{base}` when the model binds
//!   both.
//!
//! EXACTNESS IS THE CONTRACT, and since 2026-09-21 it is the SAME contract as the
//! miner's on the cast. [`crate::const_expr`] mints HYPOTHESES, so it must
//! decline anything whose value it cannot compute exactly — which a
//! reinterpreting `as` between integer types never was: it models that exactly
//! now ([`crate::const_expr::v2_const_expr_cast_int`]), and the row this module
//! is named for mines its bound. This module still carries [`machine_cast_int`]
//! because it answers a slightly different question — the values it folds come
//! back from a MODEL as bit patterns, so it declines every 128-bit unsigned
//! destination rather than narrow one — and `machine_cast_matches_rust_as` pins
//! it against Rust's own `as`. Everything else — the binary operations, the fit
//! checks, the unique-definition walk — is [`crate::const_expr`]'s, called, not
//! re-implemented.
//!
//! OPEN RESIDUAL: with the `Cast` arms agreeing, [`machine_cast_int`] and
//! [`crate::const_expr::v2_const_expr_cast_int`] differ only in that 128-bit
//! unsigned edge, and the `machine_const_*` walk is otherwise a duplicate of the
//! miner's. Collapsing the two is a separate change with its own measurement;
//! until then the two folds are pinned against each other in
//! `grounding_and_the_miner_agree_on_the_cast_that_used_to_be_unminable`.
//!
//! FAIL CLOSED TOWARD KEEPING THE WITNESS. [`Replay::Completes`] is the only
//! answer that withholds one, and it is returned only after the interpreter has
//! modelled every step from the entry block to the return; a call, a reference,
//! an aggregate, a float, an unmodelled projection and the step budget all
//! answer [`Replay::Undecided`], which grounds nothing and changes nothing. A
//! contradiction is likewise reported only where the definitions PROVE one: a
//! unique whole-local definition (asked of the `local_defs` seam, which knows a
//! parameter is defined at ENTRY and that a partial write or an `&mut` escape
//! disqualifies the question) in a block that DOMINATES every `Assert` in the
//! function, whose value folds exactly. A conditionally-defined local is
//! uninitialized on the paths that skip it, so a mismatch there would prove
//! nothing and is never called one. Mislabelling a real witness would cost a
//! user the one actionable thing a refutation carries.
//!
//! WHAT THIS NEVER DOES. Move a verdict. `Failed` stays `Failed`; making the row
//! `Unknown` to avoid an awkward witness would trade a sound refutation for a
//! lost verdict, and `grounding_never_moves_a_verdict` pins that it cannot.

use trust_types::{
    Counterexample, CounterexampleValue, Place, Rvalue, Statement, Terminator, Ty,
    VerifiableFunction, VerificationResult,
};

/// The verdict of evaluating a model against the function's own definitions.
#[derive(Debug, Clone, PartialEq, Eq)]
#[must_use]
pub enum WitnessGrounding {
    /// The model's own inputs, REPLAYED through this function, reach the
    /// panicking `Assert` that terminates block `block`. This is the strong
    /// verdict: the witness is an execution, and it panics.
    Replays { block: usize },
    /// Nothing the function's definitions prove contradicts the model, and the
    /// replay could not decide — the body leaves the fragment this module
    /// interprets (a call, a reference, a float, an unmodelled projection), or a
    /// parameter is unbound by the model or is not an integer or boolean (so a
    /// function over `&[u8]` is never replayed and is grounded by the necessary
    /// conditions alone). `reason` says which.
    Undecided { reason: String },
    /// The model is NOT an execution of this function. Each reason is a complete
    /// sentence naming the value the model gave and the value the program has.
    /// The row's refutation is unaffected.
    Ungrounded { reasons: Vec<String> },
}

impl WitnessGrounding {
    /// TRUE unless the function's own definitions refute the model. `Undecided`
    /// counts as grounded: a witness is withheld only on evidence against it.
    #[must_use]
    pub fn is_grounded(&self) -> bool {
        !matches!(self, Self::Ungrounded { .. })
    }
}

/// The fresh bitvector operand vars the >= 128-bit and multiply overflow cores
/// mint. See `generate::overflow_vc`; the name is `{PREFIX}{role}_{base}` and
/// `{base}` is [`crate::place_to_var_name`] of the operand's place.
const BV_OPERAND_PREFIX: &str = "__trust_ovf_bv_";

/// The roles `generate::overflow_vc` mints. The split requires the role to be
/// followed by `_`, so a `{base}` that merely BEGINS with one of them cannot be
/// mistaken for the role — and since `{base}` is itself a place name that may
/// contain `_` (`_15`, `lim#s1_t`), splitting on the first `_` alone would be
/// wrong. An unrecognized role yields `None` and the name is left alone.
const BV_OPERAND_ROLES: [&str; 4] = ["lhs", "rhs", "amt", "neg"];

/// The largest local table this module will build a name map for. See
/// [`unambiguous_local_names`] for why there is a cap at all; 4096 locals is far
/// past any hand-written body and past every fixture in this crate.
const MAX_GROUNDED_LOCALS: usize = 4096;

/// The label the delivered witness carries when it could not be grounded.
/// Upper-case so it cannot be misread as one of the program's own variables.
pub const UNGROUNDED_LABEL: &str = "UNGROUNDED";

// ---------------------------------------------------------------------------
// The machine-exact fold
// ---------------------------------------------------------------------------

/// Reinterpret `value` as the integer type `width`/`signed` — Rust's `as`
/// between integer types, which TRUNCATES to the destination width and then
/// reads the bits at the destination's signedness.
///
/// AMENDED 2026-09-21: this used to be the ONE place this module computed
/// something [`crate::const_expr::v2_const_expr_operand_int`] refused to. It no
/// longer is — [`crate::const_expr::v2_const_expr_cast_int`] models the same
/// reinterpretation, because an exactly computable cast is a sound hypothesis
/// and the old "value-preserving" rule was standing in for "computable
/// exactly". What survives here is the 128-bit UNSIGNED edge below, which is
/// this module's own and not the miner's.
///
/// 128-bit UNSIGNED declines: a `u128` bit pattern does not fit the `i128` this
/// module carries values in, and a wrong answer here would mislabel a real
/// witness. Declining only means the name is not checked.
fn machine_cast_int(value: i128, width: u32, signed: bool) -> Option<i128> {
    if width == 0 || width > 128 {
        return None;
    }
    if width == 128 {
        return signed.then_some(value);
    }
    let modulus = 1i128 << width;
    let bits = value.rem_euclid(modulus);
    Some(if signed && bits >= (1i128 << (width - 1)) { bits - modulus } else { bits })
}

/// The exact value of `op` as the machine computes it, or `None`.
///
/// [`crate::const_expr::v2_const_expr_operand_int`] with its `Cast` arm replaced
/// by [`machine_cast_int`]; every other arm — the operand shapes, the
/// unique-definition walk, the checked binary operations, the `.0` of a checked
/// tuple, the per-step fit — is that module's, called rather than copied, so
/// there is exactly one place the arithmetic can be got wrong.
fn machine_const_operand_int(
    func: &VerifiableFunction,
    op: &trust_types::Operand,
    fuel: u32,
) -> Option<i128> {
    if fuel == 0 {
        return None;
    }
    let (trust_types::Operand::Copy(place) | trust_types::Operand::Move(place)) = op else {
        return match op {
            trust_types::Operand::Constant(trust_types::ConstValue::Int(value)) => Some(*value),
            trust_types::Operand::Constant(trust_types::ConstValue::Uint(value, _)) => {
                i128::try_from(*value).ok()
            }
            _ => None,
        };
    };
    // PERF-COMPILER-VCGEN-587: parameters have an implicit entry definition, so
    // `unique_value_def` always returns `None` after scanning the body.
    if crate::local_defs::is_parameter(func, place.local) {
        return None;
    }
    match place.projections.as_slice() {
        [] => {
            let dest_ty = crate::local_ty_ref(func, place.local)?;
            let rvalue = crate::local_defs::unique_value_def(func, place.local)?;
            machine_const_rvalue_int(func, rvalue, dest_ty, fuel - 1)
        }
        [trust_types::Projection::Field(0)] => {
            let Rvalue::CheckedBinaryOp(op, lhs, rhs) =
                crate::local_defs::unique_value_def(func, place.local)?
            else {
                return None;
            };
            let dest_ty = crate::place_ty_cow(func, place)?;
            crate::const_expr::v2_const_expr_binop(
                *op,
                machine_const_operand_int(func, lhs, fuel - 1)?,
                machine_const_operand_int(func, rhs, fuel - 1)?,
                dest_ty.as_ref(),
            )
        }
        _ => None,
    }
}

/// See [`machine_const_operand_int`]. `Cast` is the only arm that departs from
/// [`crate::const_expr::v2_const_expr_rvalue_int`].
fn machine_const_rvalue_int(
    func: &VerifiableFunction,
    rvalue: &Rvalue,
    dest_ty: &Ty,
    fuel: u32,
) -> Option<i128> {
    let value = match rvalue {
        Rvalue::Use(inner) => machine_const_operand_int(func, inner, fuel)?,
        Rvalue::Cast(inner, Ty::Int { width, signed }) => {
            // The machine's `as`: the same reinterpretation the miner's
            // `const_expr::v2_const_expr_cast_int` computes, except for the
            // 128-bit unsigned destination `machine_cast_int` declines.
            return machine_cast_int(
                machine_const_operand_int(func, inner, fuel)?,
                *width,
                *signed,
            );
        }
        // `Neg` that would leave the type is a PANIC, not a value: decline, as
        // the miner does. (rustc guards it with its own `OverflowNeg` assert.)
        Rvalue::UnaryOp(trust_types::UnOp::Neg, inner) => {
            machine_const_operand_int(func, inner, fuel)?.checked_neg()?
        }
        Rvalue::BinaryOp(op, lhs, rhs) => crate::const_expr::v2_const_expr_binop(
            *op,
            machine_const_operand_int(func, lhs, fuel)?,
            machine_const_operand_int(func, rhs, fuel)?,
            dest_ty,
        )?,
        _ => return None,
    };
    crate::const_expr::v2_const_expr_int_fits(dest_ty, value)
}

// ---------------------------------------------------------------------------
// Which locals a model may be checked against
// ---------------------------------------------------------------------------

/// The blocks that carry an `Assert` terminator — every block a refutable panic
/// boundary can belong to.
fn assert_blocks(func: &VerifiableFunction) -> Vec<usize> {
    // PERF-COMPILER-VCGEN-587: skip the block scan when the body has no Assert terminator.
    if !crate::generate::terminator_presence_for(func).has_assert {
        return Vec::new();
    }
    func.body
        .blocks
        .iter()
        .filter(|block| matches!(block.terminator, Terminator::Assert { .. }))
        .map(|block| block.id.0)
        .collect()
}

/// The value the function's own definitions compute for `local`, together with
/// the sentence that says how — or `None` when this local is not one a model may
/// be checked against.
///
/// The dominance condition is the whole reason this is not just a fold: a local
/// defined inside a branch is UNINITIALIZED on the paths that skip it, so a
/// model is free to name anything for it and a mismatch would prove nothing.
/// Requiring the defining block to dominate EVERY `Assert` block makes "this
/// local has already been computed, to this value" true for whichever row the
/// model belongs to, without the model having to say which row that is.
fn grounded_local_value(
    func: &VerifiableFunction,
    dominators: &std::cell::OnceCell<crate::termination::Dominators>,
    assert_blocks: &[usize],
    local: usize,
    ty: &Ty,
) -> Option<(i128, String)> {
    // PERF-COMPILER-VCGEN-587: check `is_parameter` and `Ty::Int` in O(1) before
    // running `unique_defining_block` (an O(blocks * stmts) `local_write` scan)
    // and `dominators.dominates(...)`.
    if assert_blocks.is_empty()
        || crate::local_defs::is_parameter(func, local)
        || !matches!(ty, Ty::Int { .. })
    {
        return None;
    }
    // The defining block comes from the `local_defs` SEAM, never from a scan of
    // `body.blocks` here: that seam is the one place that knows a parameter is
    // defined at ENTRY and that a partial write, an `&mut` escape or an opaque
    // call destination disqualifies the question entirely. A local-definition
    // scan written here would be a second answer to keep in sync, and
    // `tests/local_defs_seam_lint.rs` exists because that has gone wrong before.
    let def_block = crate::local_defs::unique_defining_block(func, local)?;
    // PERF-COMPILER-VCGEN-706: compute `dominators` lazily only when a counterexample
    // actually names a non-parameter `Ty::Int` local with a unique defining block.
    let doms = dominators.get_or_init(|| crate::termination::compute_dominators(&func.body));
    if !assert_blocks.iter().all(|&assert_block| doms.dominates(def_block, assert_block)) {
        return None;
    }
    let rvalue = crate::local_defs::unique_value_def(func, local)?;
    let value = machine_const_rvalue_int(func, rvalue, ty, crate::const_expr::V2_CONST_EXPR_FUEL)?;
    Some((value, format!("bb{def_block} defines it as a closed constant expression")))
}

/// Model name -> local, for every local whose name is UNAMBIGUOUS. A name minted
/// by two locals (place canonicalization deliberately converges some aliases) is
/// dropped from the map: grounding must never attribute one local's model value
/// to another local's definition.
fn unambiguous_local_names(func: &VerifiableFunction) -> trust_types::fx::FxHashMap<String, usize> {
    // COST GUARD. `place_to_var_name`'s memo is scoped to VC generation and this
    // runs after it, so each mint is O(locals) and the whole table is
    // O(locals^2). That is nothing on the bodies these rows come from and
    // unbounded on a generated one, so a body past the cap is simply NOT
    // grounded: its model is delivered exactly as the solver returned it, which
    // is the behaviour before this module existed. Declining costs a label,
    // never a verdict.
    if func.body.locals.len() > MAX_GROUNDED_LOCALS {
        return Default::default();
    }
    let mut seen: trust_types::fx::FxHashMap<String, Option<usize>> =
        trust_types::fx::FxHashMap::with_capacity_and_hasher(
            func.body.locals.len(),
            Default::default(),
        );
    for decl in &func.body.locals {
        let name = crate::place_to_var_name(func, &Place::local(decl.index));
        match seen.entry(name) {
            std::collections::hash_map::Entry::Vacant(e) => {
                e.insert(Some(decl.index));
            }
            std::collections::hash_map::Entry::Occupied(mut e) => {
                *e.get_mut() = None;
            }
        }
    }
    seen.into_iter().filter_map(|(name, idx)| Some((name, idx?))).collect()
}

/// `__trust_ovf_bv_lhs_a` -> `("lhs", "a")`, or `None` for any other name.
fn split_bv_operand_name(name: &str) -> Option<(&str, &str)> {
    let rest = name.strip_prefix(BV_OPERAND_PREFIX)?;
    for role in BV_OPERAND_ROLES {
        if let Some(base) = rest.strip_prefix(role).and_then(|r| r.strip_prefix('_')) {
            return Some((role, base));
        }
    }
    None
}

/// The model's value for a name, as the `i128` the machine reads.
///
/// A model names a BITVECTOR by its UNSIGNED bit pattern, so a value that is
/// being compared against a signed local must be reinterpreted at that local's
/// width first — taking `18446744073709551615` at face value against an `i64`
/// would turn `-1` into a huge positive number and manufacture a contradiction.
/// `ty` is the type to read the value AT; `None` reads it as written.
fn model_int(value: &CounterexampleValue, ty: Option<&Ty>) -> Option<i128> {
    match value {
        CounterexampleValue::Bool(b) => Some(i128::from(*b)),
        CounterexampleValue::Int(v) => match ty {
            Some(Ty::Int { width, signed }) => machine_cast_int(*v, *width, *signed),
            _ => Some(*v),
        },
        // A BITVECTOR's model value is its unsigned bit pattern, and at 128 bits
        // that pattern does not fit `i128` at all — `i128::MIN` is spelled
        // `170141183460469231731687303715884105728`. Reinterpreting in `u128`
        // and only then narrowing is the one reading that works at every width;
        // narrowing first silently DROPS the model (measured: it cost the
        // 128-bit negation twin its repaired witness).
        CounterexampleValue::Uint(v) => match ty {
            Some(Ty::Int { width: 128, signed: true }) => Some(*v as i128),
            Some(Ty::Int { width: 128, signed: false }) => i128::try_from(*v).ok(),
            Some(Ty::Int { width, signed }) if *width < 128 && *width > 0 => {
                let bits = *v % (1u128 << width);
                let bits = i128::try_from(bits).ok()?;
                Some(if *signed && bits >= (1i128 << (width - 1)) {
                    bits - (1i128 << width)
                } else {
                    bits
                })
            }
            _ => i128::try_from(*v).ok(),
        },
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// The REPLAY — the oracle that actually answers "does this reach the panic?"
// ---------------------------------------------------------------------------

/// One concrete machine value during a replay.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Value {
    Int(i128),
    Bool(bool),
    Tuple(Vec<Value>),
}

impl Value {
    fn as_int(&self) -> Option<i128> {
        match self {
            Self::Int(v) => Some(*v),
            Self::Bool(b) => Some(i128::from(*b)),
            Self::Tuple(_) => None,
        }
    }

    fn as_bool(&self) -> Option<bool> {
        match self {
            Self::Bool(b) => Some(*b),
            Self::Int(v) => Some(*v != 0),
            Self::Tuple(_) => None,
        }
    }
}

/// What a replay found.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Replay {
    /// Reached a failing `Assert` — an execution that panics.
    Panics { block: usize },
    /// Ran to `Return` without any assert failing.
    Completes {
        /// The return place `_0`'s value at `Return`, when the replay assigned it
        /// (`None` when `_0` was never written, never a fabricated value).
        ///
        /// Trust (2026-09-27): carried for a postcondition check that does not exist
        /// yet. A postcondition violation is a wrong RETURN VALUE, not a failing
        /// `Assert`, so this replay could not witness one while it discarded `_0`.
        /// `docs/DECISION_QUEUE.md` D11 option (b′) would evaluate the `ensures`
        /// clause concretely on (inputs, `ret`) and admit a `Postcondition`
        /// refutation only when it is FALSE — a violation witnessed by executing the
        /// function, independent of any encoding-fidelity argument. That admission is
        /// a refutation-authority decision and is NOT made here: nothing in this module
        /// reads `ret`, so it moves no verdict (`grounding_never_moves_a_verdict`).
        #[allow(dead_code)]
        ret: Option<Value>,
    },
    /// Left the interpreted fragment. The reason names what stopped it; a
    /// replay that cannot decide never decides AGAINST a witness.
    Undecided(String),
}

/// The longest replay this module will run. A body is straight-line arithmetic
/// plus branches here — the shapes these rows come from are tens of steps — and
/// a hard cap keeps the function total on a loop the interpreter would otherwise
/// follow for as long as the witness says to.
const REPLAY_STEP_BUDGET: u32 = 10_000;

/// Execute `func` from its entry block with parameters bound to `params`
/// (keyed by local index), and report whether an `Assert` fails.
///
/// A DELIBERATELY SMALL FRAGMENT: integer and boolean locals, tuple values from
/// `CheckedBinaryOp`, `Goto`/`SwitchInt`/`Assert`/`Return`. Everything else — a
/// call, a reference, a raw pointer, an aggregate, a float, a projection past a
/// tuple field — answers [`Replay::Undecided`], never `Completes`. That
/// asymmetry is the whole safety of this lane: `Completes` is what withholds a
/// witness, so it is only ever returned after the interpreter has modelled every
/// step from the entry block to the return.
fn replay(func: &VerifiableFunction, params: &trust_types::fx::FxHashMap<usize, Value>) -> Replay {
    let mut env: trust_types::fx::FxHashMap<usize, Value> =
        trust_types::fx::FxHashMap::with_capacity_and_hasher(
            func.body.locals.len().max(params.len()),
            Default::default(),
        );
    env.extend(params.iter().map(|(&k, v)| (k, v.clone())));
    let mut block_index = 0usize;
    // The budget is the LOOP BOUND, not a counter tested inside the body: the
    // step count is then a structural, strictly-decreasing bound rather than
    // something a `continue` could skip past.
    for _ in 0..REPLAY_STEP_BUDGET {
        let Some(block) = func.body.blocks.get(block_index) else {
            return Replay::Undecided(format!("bb{block_index} is not in the body"));
        };
        for stmt in &block.stmts {
            match stmt {
                Statement::Assign { place, rvalue, .. } => {
                    let value = match eval_rvalue(func, &env, place, rvalue) {
                        Ok(value) => value,
                        Err(reason) => return Replay::Undecided(reason),
                    };
                    if let Err(reason) = write_place(&mut env, place, value) {
                        return Replay::Undecided(reason);
                    }
                }
                Statement::StorageLive(_)
                | Statement::StorageDead(_)
                | Statement::PlaceMention(_)
                | Statement::Coverage
                | Statement::ConstEvalCounter
                | Statement::Nop => {}
                other => {
                    return Replay::Undecided(format!(
                        "bb{block_index} carries a statement this replay does not model: \
                         {}",
                        statement_kind(other)
                    ));
                }
            }
        }
        match &block.terminator {
            Terminator::Goto(target) => block_index = target.0,
            Terminator::Return => return Replay::Completes { ret: env.get(&0).cloned() },
            Terminator::SwitchInt { discr, targets, otherwise, .. } => {
                // A `SwitchInt` key is the discriminant's UNSIGNED BIT PATTERN
                // at its own type, so a negative `i32` discriminant matches the
                // key `4294967295`, not `-1`. Reading the value as a machine
                // integer and then re-encoding it is the only correspondence
                // that holds for both signs.
                let Some(key) = eval_operand(func, &env, discr)
                    .ok()
                    .and_then(|v| v.as_int())
                    .and_then(|v| switch_key(func, discr, v))
                else {
                    return Replay::Undecided(format!(
                        "bb{block_index}: unreadable switch discriminant"
                    ));
                };
                block_index = targets
                    .iter()
                    .find(|(k, _)| *k == key)
                    .map_or(otherwise.0, |(_, target)| target.0);
            }
            Terminator::Assert { cond, expected, target, .. } => {
                let Some(value) = eval_operand(func, &env, cond).ok().and_then(|v| v.as_bool())
                else {
                    return Replay::Undecided(format!(
                        "bb{block_index}: unreadable assert condition"
                    ));
                };
                if value == *expected {
                    block_index = target.0;
                } else {
                    return Replay::Panics { block: block_index };
                }
            }
            other => {
                return Replay::Undecided(format!(
                    "bb{block_index} ends in a terminator this replay does not model: {}",
                    terminator_kind(other)
                ));
            }
        }
    }
    Replay::Undecided(format!("the replay exceeded its {REPLAY_STEP_BUDGET}-step budget"))
}

/// The `SwitchInt` key for a discriminant whose machine value is `value`: its
/// UNSIGNED bit pattern at its own type. `None` for a type this replay cannot
/// encode (128-bit, or a non-integer/boolean discriminant).
fn switch_key(
    func: &VerifiableFunction,
    discr: &trust_types::Operand,
    value: i128,
) -> Option<u128> {
    match crate::operand_ty_cow(func, discr)?.as_ref() {
        Ty::Bool => u128::try_from(value).ok(),
        Ty::Int { width, .. } if *width < 128 => {
            u128::try_from(value.rem_euclid(1i128 << width)).ok()
        }
        _ => None,
    }
}

fn statement_kind(stmt: &Statement) -> &'static str {
    match stmt {
        Statement::Assign { .. } => "Assign",
        Statement::SetDiscriminant { .. } => "SetDiscriminant",
        Statement::Deinit { .. } => "Deinit",
        _ => "an unmodelled statement",
    }
}

fn terminator_kind(terminator: &Terminator) -> &'static str {
    match terminator {
        Terminator::Call { .. } => "Call",
        Terminator::TailCall { .. } => "TailCall",
        Terminator::Drop { .. } => "Drop",
        Terminator::Unreachable => "Unreachable",
        _ => "an unmodelled terminator",
    }
}

fn read_place(
    env: &trust_types::fx::FxHashMap<usize, Value>,
    place: &Place,
) -> Result<Value, String> {
    let base = env
        .get(&place.local)
        .ok_or_else(|| format!("_{} is read before it is written", place.local))?;
    match place.projections.as_slice() {
        [] => Ok(base.clone()),
        [trust_types::Projection::Field(field)] => match base {
            Value::Tuple(fields) => fields
                .get(*field)
                .cloned()
                .ok_or_else(|| format!("_{}.{field} is out of range", place.local)),
            _ => Err(format!("_{}.{field} is not a tuple", place.local)),
        },
        _ => Err(format!("_{} carries a projection this replay does not model", place.local)),
    }
}

fn write_place(
    env: &mut trust_types::fx::FxHashMap<usize, Value>,
    place: &Place,
    value: Value,
) -> Result<(), String> {
    match place.projections.as_slice() {
        [] => {
            env.insert(place.local, value);
            Ok(())
        }
        _ => Err(format!(
            "_{} is written through a projection this replay does not model",
            place.local
        )),
    }
}

fn eval_operand(
    func: &VerifiableFunction,
    env: &trust_types::fx::FxHashMap<usize, Value>,
    op: &trust_types::Operand,
) -> Result<Value, String> {
    match op {
        trust_types::Operand::Copy(place) | trust_types::Operand::Move(place) => {
            read_place(env, place)
        }
        trust_types::Operand::Constant(trust_types::ConstValue::Int(v)) => Ok(Value::Int(*v)),
        trust_types::Operand::Constant(trust_types::ConstValue::Uint(v, _)) => i128::try_from(*v)
            .map(Value::Int)
            .map_err(|_| "a u128 constant does not fit this replay's value domain".to_string()),
        trust_types::Operand::Constant(trust_types::ConstValue::Bool(b)) => Ok(Value::Bool(*b)),
        _ => {
            let _ = func;
            Err("an operand this replay does not model".to_string())
        }
    }
}

/// The comparison operators, which `const_expr::v2_const_expr_binop` does not
/// cover (it folds VALUES; these produce a boolean).
fn eval_comparison(op: trust_types::BinOp, lhs: i128, rhs: i128) -> Option<bool> {
    Some(match op {
        trust_types::BinOp::Eq => lhs == rhs,
        trust_types::BinOp::Ne => lhs != rhs,
        trust_types::BinOp::Lt => lhs < rhs,
        trust_types::BinOp::Le => lhs <= rhs,
        trust_types::BinOp::Gt => lhs > rhs,
        trust_types::BinOp::Ge => lhs >= rhs,
        _ => return None,
    })
}

fn eval_rvalue(
    func: &VerifiableFunction,
    env: &trust_types::fx::FxHashMap<usize, Value>,
    dest: &Place,
    rvalue: &Rvalue,
) -> Result<Value, String> {
    match rvalue {
        Rvalue::Use(inner) => eval_operand(func, env, inner),
        Rvalue::Cast(inner, Ty::Int { width, signed }) => {
            let value = eval_operand(func, env, inner)?
                .as_int()
                .ok_or_else(|| "a non-integer cast source".to_string())?;
            machine_cast_int(value, *width, *signed)
                .map(Value::Int)
                .ok_or_else(|| format!("a cast to a {width}-bit type this replay does not model"))
        }
        Rvalue::UnaryOp(trust_types::UnOp::Not, inner) => {
            match eval_operand(func, env, inner)? {
                Value::Bool(b) => Ok(Value::Bool(!b)),
                // Integer `!` is width-dependent bitwise negation; decline
                // rather than approximate it.
                _ => Err("integer `!` is not modelled by this replay".to_string()),
            }
        }
        Rvalue::UnaryOp(trust_types::UnOp::Neg, inner) => {
            let value = eval_operand(func, env, inner)?
                .as_int()
                .ok_or_else(|| "a non-integer negation".to_string())?;
            let ty = crate::place_ty_cow(func, dest)
                .ok_or_else(|| "an untyped negation destination".to_string())?;
            // rustc guards `Neg` with its own `OverflowNeg` assert, so a replay
            // that reaches the `Neg` has already passed it; a value that leaves
            // the type here means the replay is off the machine's semantics and
            // must decline rather than wrap.
            value
                .checked_neg()
                .and_then(|v| crate::const_expr::v2_const_expr_int_fits(ty.as_ref(), v))
                .map(Value::Int)
                .ok_or_else(|| "a negation that leaves its type".to_string())
        }
        Rvalue::BinaryOp(op, lhs, rhs) => {
            let l = eval_operand(func, env, lhs)?
                .as_int()
                .ok_or_else(|| "a non-integer binary operand".to_string())?;
            let r = eval_operand(func, env, rhs)?
                .as_int()
                .ok_or_else(|| "a non-integer binary operand".to_string())?;
            if let Some(b) = eval_comparison(*op, l, r) {
                return Ok(Value::Bool(b));
            }
            let ty = crate::place_ty_cow(func, dest)
                .ok_or_else(|| "an untyped binary destination".to_string())?;
            crate::const_expr::v2_const_expr_binop(*op, l, r, ty.as_ref())
                .map(Value::Int)
                .ok_or_else(|| format!("a `{op:?}` this replay cannot evaluate exactly"))
        }
        Rvalue::CheckedBinaryOp(op, lhs, rhs) => {
            let l = eval_operand(func, env, lhs)?
                .as_int()
                .ok_or_else(|| "a non-integer checked operand".to_string())?;
            let r = eval_operand(func, env, rhs)?
                .as_int()
                .ok_or_else(|| "a non-integer checked operand".to_string())?;
            let operand_ty = crate::operand_ty_cow(func, lhs)
                .ok_or_else(|| "an untyped checked operand".to_string())?;
            let Ty::Int { width, signed } = operand_ty.as_ref() else {
                return Err("a non-integer checked operation".to_string());
            };
            // The MATHEMATICAL result in i128, then the machine's wrap. A
            // 128-bit operation can leave i128, and then this replay declines
            // rather than report an overflow flag it cannot compute.
            let exact = match op {
                trust_types::BinOp::Add => l.checked_add(r),
                trust_types::BinOp::Sub => l.checked_sub(r),
                trust_types::BinOp::Mul => l.checked_mul(r),
                _ => None,
            }
            .ok_or_else(|| format!("a checked `{op:?}` this replay cannot evaluate exactly"))?;
            let fits = crate::const_expr::v2_const_expr_int_fits(operand_ty.as_ref(), exact);
            let wrapped = machine_cast_int(exact, *width, *signed)
                .ok_or_else(|| "a checked result this replay cannot wrap".to_string())?;
            Ok(Value::Tuple(vec![Value::Int(wrapped), Value::Bool(fits.is_none())]))
        }
        _ => Err("an rvalue this replay does not model".to_string()),
    }
}

/// The function's parameter locals, in order: local `0` is the return slot and
/// `1..=arg_count` are the parameters.
fn parameter_locals(func: &VerifiableFunction) -> std::ops::RangeInclusive<usize> {
    1..=func.body.arg_count
}

/// Every parameter's value as the model names it, or `Err` naming the first
/// parameter the model leaves unbound (which makes a replay impossible).
fn parameters_from_model(
    func: &VerifiableFunction,
    names: &trust_types::fx::FxHashMap<String, usize>,
    cex: &Counterexample,
) -> Result<trust_types::fx::FxHashMap<usize, Value>, String> {
    if func.body.arg_count == 0 {
        return Ok(trust_types::fx::FxHashMap::default());
    }
    let params = parameter_locals(func);
    let mut by_local: trust_types::fx::FxHashMap<usize, &CounterexampleValue> =
        trust_types::fx::FxHashMap::with_capacity_and_hasher(
            func.body.arg_count,
            Default::default(),
        );
    for (name, value) in &cex.assignments {
        if let Some(&local) = names.get(name.as_str())
            && params.contains(&local)
        {
            by_local.insert(local, value);
        }
    }
    let mut out = trust_types::fx::FxHashMap::with_capacity_and_hasher(
        func.body.arg_count,
        Default::default(),
    );
    for local in params {
        let ty = crate::local_ty_ref(func, local)
            .ok_or_else(|| format!("_{local} has no declared type"))?;
        let Some(raw) = by_local.get(&local) else {
            return Err(format!(
                "the model does not bind `{}`, so there is nothing to replay",
                crate::place_to_var_name(func, &Place::local(local))
            ));
        };
        let value = match ty {
            Ty::Int { .. } => Value::Int(
                model_int(raw, Some(ty)).ok_or_else(|| "an unreadable model value".to_string())?,
            ),
            Ty::Bool => Value::Bool(
                model_int(raw, None).ok_or_else(|| "an unreadable model value".to_string())? != 0,
            ),
            _ => {
                return Err(format!(
                    "`{}` is not an integer or boolean parameter",
                    crate::place_to_var_name(func, &Place::local(local))
                ));
            }
        };
        out.insert(local, value);
    }
    Ok(out)
}

// ---------------------------------------------------------------------------
// The grounding check
// ---------------------------------------------------------------------------

/// The per-function tables grounding reads, built ONCE.
///
/// `compute_dominators` is a fixpoint over the block graph and
/// `unambiguous_local_names` mints a name for every local; a body with many
/// refuted rows would otherwise pay both per row. Nothing here depends on the
/// model, so one table serves every row of one function.
struct Grounder<'a> {
    _scope: crate::RowReplayScope,
    func: &'a VerifiableFunction,
    names: trust_types::fx::FxHashMap<String, usize>,
    dominators: std::cell::OnceCell<crate::termination::Dominators>,
    asserts: Vec<usize>,
}

impl<'a> Grounder<'a> {
    fn new(func: &'a VerifiableFunction) -> Self {
        let scope = crate::row_replay_scope();
        let names = unambiguous_local_names(func);
        // PERF-COMPILER-VCGEN-706: skip `assert_blocks` when `names` is empty, and
        // defer `compute_dominators` to `grounded_local_value` on demand.
        let asserts = if names.is_empty() { Vec::new() } else { assert_blocks(func) };
        Self {
            _scope: scope,
            names,
            dominators: std::cell::OnceCell::new(),
            asserts,
            func,
        }
    }
}

/// The two NECESSARY conditions a model must meet, checked even when the body
/// leaves the replay's fragment:
///
/// 1. **A defined local carries the value its definition computes.** `lim`'s
///    definition is `(-1i32) as u32 as i64` in the entry block, so a model
///    naming `lim = 1` contradicts the program.
/// 2. **A fresh bitvector operand var agrees with the source name it stands
///    for.** `__trust_ovf_bv_lhs_a` IS `a` at the multiply, so a model naming it
///    `-1` while naming `a = 0` contradicts itself about one program value.
///
/// Both compare MACHINE values at the local's own width, so a bitvector's
/// unsigned bit pattern and a signed local's value are never confused.
fn contradicted_definitions(grounder: &Grounder<'_>, cex: &Counterexample) -> Vec<String> {
    let (func, names) = (grounder.func, &grounder.names);
    if names.is_empty() || cex.assignments.is_empty() {
        return Vec::new();
    }
    let asserts = &grounder.asserts;
    let mut reasons = Vec::new();

    if !asserts.is_empty() {
        for (name, value) in &cex.assignments {
            let Some(&local) = names.get(name.as_str()) else { continue };
            let Some(ty) = crate::local_ty_ref(func, local) else { continue };
            let Some(model) = model_int(value, Some(ty)) else { continue };
            let Some((program, why)) =
                grounded_local_value(func, &grounder.dominators, asserts, local, ty)
            else {
                continue;
            };
            if model != program {
                reasons.push(format!(
                    "the model names `{name}` = {model}, but {why}, and that value is {program}"
                ));
            }
        }
    }

    for (name, value) in &cex.assignments {
        let Some((role, base)) = split_bv_operand_name(name) else { continue };
        let Some(&local) = names.get(base) else { continue };
        let Some(ty) = crate::local_ty_ref(func, local) else { continue };
        let Some(model) = model_int(value, Some(ty)) else { continue };
        let Some(source) = cex
            .assignments
            .iter()
            .find(|(other, _)| other == base)
            .and_then(|(_, v)| model_int(v, Some(ty)))
        else {
            continue;
        };
        if model != source {
            reasons.push(format!(
                "the model names `{name}` = {model} — the fresh bitvector variable standing for \
                 the {role} operand `{base}` of this row's operation — while naming `{base}` = \
                 {source}; one program value cannot have two"
            ));
        }
    }

    reasons
}

/// Evaluate `cex` against `func`'s own definitions.
///
/// The necessary conditions first (they hold whatever the body contains), then
/// the REPLAY, which is the real question: run the function on the inputs the
/// model names and see whether it reaches a failing `Assert`.
#[must_use]
pub fn ground_counterexample(func: &VerifiableFunction, cex: &Counterexample) -> WitnessGrounding {
    Grounder::new(func).ground(cex)
}

impl Grounder<'_> {
    fn ground(&self, cex: &Counterexample) -> WitnessGrounding {
        let func = self.func;
        let reasons = contradicted_definitions(self, cex);
        if !reasons.is_empty() {
            return WitnessGrounding::Ungrounded { reasons };
        }
        match parameters_from_model(func, &self.names, cex) {
            Err(reason) => WitnessGrounding::Undecided { reason },
            Ok(params) => match replay(func, &params) {
                Replay::Panics { block } => WitnessGrounding::Replays { block },
                Replay::Completes { .. } => WitnessGrounding::Ungrounded {
                    reasons: vec![format!(
                        "running `{}` on the inputs the model names ({}) reaches the end of the \
                     function without any assertion failing — the model does not describe an \
                     execution that panics",
                        func.def_path,
                        render_parameters(func, &params)
                    )],
                },
                Replay::Undecided(reason) => WitnessGrounding::Undecided { reason },
            },
        }
    }
}

fn render_parameters(
    func: &VerifiableFunction,
    params: &trust_types::fx::FxHashMap<usize, Value>,
) -> String {
    let mut parts = Vec::new();
    for local in parameter_locals(func) {
        let name = crate::place_to_var_name(func, &Place::local(local));
        match params.get(&local) {
            Some(Value::Int(v)) => parts.push(format!("{name} = {v}")),
            Some(Value::Bool(b)) => parts.push(format!("{name} = {b}")),
            _ => {}
        }
    }
    parts.join(", ")
}

/// The parameter a bitvector operand's `{base}` ultimately reads, following a
/// chain of whole-local `Use` copies (`_15 = b`). `None` when the base is not a
/// parameter or the chain leaves that shape.
fn base_parameter_local(func: &VerifiableFunction, mut local: usize) -> Option<usize> {
    let params = parameter_locals(func);
    for _ in 0..crate::const_expr::V2_CONST_EXPR_FUEL {
        if params.contains(&local) {
            return Some(local);
        }
        let Rvalue::Use(trust_types::Operand::Copy(place) | trust_types::Operand::Move(place)) =
            crate::local_defs::unique_value_def(func, local)?
        else {
            return None;
        };
        if !place.projections.is_empty() {
            return None;
        }
        local = place.local;
    }
    None
}

/// THE REPAIR (v7/D3: a refusal names its fix, and where a repair exists it is
/// better than a refusal). The fresh `__trust_ovf_bv_*` operand vars carry the
/// values that actually make this row's violation true — they are the half of
/// the composed model that witnesses the overflow, while the Int half witnesses
/// only the guards. Push them back onto the parameters they stand for and REPLAY:
/// when the result really reaches a failing assert, that assignment is a genuine,
/// replayable witness and is delivered INSTEAD of the label.
///
/// Verified, not asserted: a candidate is delivered only after [`replay`] has run
/// the function on it and seen an assert fail. A candidate the guards exclude
/// (the report's own `castu_unminable`: `b = i64::MIN` fails `b > -lim`) simply
/// does not replay, and the row keeps the label.
fn repaired_parameters(
    func: &VerifiableFunction,
    names: &trust_types::fx::FxHashMap<String, usize>,
    cex: &Counterexample,
) -> Option<trust_types::fx::FxHashMap<usize, Value>> {
    let mut params = parameters_from_model(func, names, cex).ok()?;
    let mut repaired = false;
    for (name, value) in &cex.assignments {
        let Some((_, base)) = split_bv_operand_name(name) else { continue };
        let Some(&base_local) = names.get(base) else { continue };
        let Some(param) = base_parameter_local(func, base_local) else { continue };
        let Some(ty) = crate::local_ty_ref(func, param) else { continue };
        let Some(v) = model_int(value, Some(ty)) else { continue };
        if params.insert(param, Value::Int(v)) != Some(Value::Int(v)) {
            repaired = true;
        }
    }
    if !repaired {
        return None;
    }
    matches!(replay(func, &params), Replay::Panics { .. }).then_some(params)
}

/// The sentence an ungrounded row carries in place of its model.
///
/// Trust (2026-10-01, review of cf9ce551b45): the FIX names what would help THIS row.
/// Respelling a bound helps only where a guard bound was left unmined
/// ([`crate::generate::unmined_guard_bounds`]); on a real overflow whose bounds all fold
/// (`if a >= MIN+1 { a = b; -a }`) that advice sent the reader after a spelling that
/// was never the problem, so the sentence names the operand the model could not tie to
/// an input instead, and says the refutation stands on its own.
fn ungrounded_reason(
    func: &VerifiableFunction,
    reasons: &[String],
    cex: &Counterexample,
) -> String {
    let mut out = format!(
        "no replayable witness could be delivered for this row. The solver's model is not an \
         execution of `{}`: ",
        func.def_path
    );
    out.push_str(&reasons.join("; "));
    out.push_str(
        ". The REFUTATION stands — this row's violation condition is satisfiable, and that is \
         what refutes it. What is missing is a fact tying the row's operands to the program's \
         values: the overflow core is a bitvector query over FRESH operand variables",
    );
    let unmined = crate::generate::unmined_guard_bounds(func);
    if unmined.is_empty() {
        let mut operands: Vec<String> = Vec::new();
        for (name, _) in &cex.assignments {
            if let Some((role, base)) = split_bv_operand_name(name) {
                let described = format!("the {role} operand `{base}`");
                if !operands.contains(&described) {
                    operands.push(described);
                }
            }
        }
        let operands = if operands.is_empty() {
            "the operation's operands".to_string()
        } else {
            operands.join(", ")
        };
        out.push_str(&format!(
            ", and here no repair could push the model's value for {operands} back onto an \
             input of `{}` that reaches this row. Every guard bound in `{}` folds exactly, so \
             respelling one would not change this row: the operand is not the value an input \
             names at the operation (it is a copy of a local the body rewrites, or the value a \
             path through it produces). The refutation stands on its own; only the witness \
             could not be replayed. FIX: the overflow itself — bound the value the operation \
             reads (a guard on a value the body then rewrites bounds nothing the operation \
             sees), or use the type's `checked_*` / `wrapping_*` method where that is the \
             intent.",
            func.def_path, func.def_path
        ));
    } else {
        out.push_str(&format!(
            ", and when the guard bound on them cannot be mined exactly (trust_vcgen::const_expr \
             is exact-or-nothing) nothing constrains them, so a model of the encoding may disagree \
             with the program. Here the bound {} did not fold. FIX: spell the bound so it folds \
             exactly — a literal, or a closed constant expression over literals (integer `as` \
             casts included) held in a local no `&mut` reaches — or bound the operands with a \
             `requires` clause; either gives the row the fact it needs and a replayable witness \
             comes back.",
            unmined.iter().map(|n| format!("`{n}`")).collect::<Vec<_>>().join(", ")
        ));
    }
    out
}

/// The witness as it should be DELIVERED for a row of `func`.
///
/// * Grounded (the model replays to a panic, or nothing refutes it): the model,
///   with each fresh bitvector operand var PROJECTED onto the source name it
///   stands for — replaced by that name when the model does not already bind it,
///   and dropped as redundant when it does. The encoding's own variable names
///   are not the program's and do not belong in a witness.
/// * Ungrounded, and a REPAIR replays to a panic: the repaired parameter
///   assignment, which is a real execution of this function that panics.
/// * Ungrounded with no repair: one [`UNGROUNDED_LABEL`] entry carrying the
///   reason and the fix, and nothing else. An impossible assignment is never
///   handed over as if it were an input.
#[must_use]
pub fn deliver_counterexample(func: &VerifiableFunction, cex: &Counterexample) -> Counterexample {
    Grounder::new(func).deliver(cex)
}

impl Grounder<'_> {
    fn deliver(&self, cex: &Counterexample) -> Counterexample {
        let func = self.func;
        let names = &self.names;
        let grounding = self.ground(cex);
        let WitnessGrounding::Ungrounded { reasons } = &grounding else {
            return project_bitvector_operands(func, names, cex);
        };
        if let Some(params) = repaired_parameters(func, names, cex) {
            let mut assignments = Vec::new();
            for local in parameter_locals(func) {
                let name = crate::place_to_var_name(func, &Place::local(local));
                match params.get(&local) {
                    Some(Value::Int(v)) => assignments.push((name, CounterexampleValue::Int(*v))),
                    Some(Value::Bool(b)) => assignments.push((name, CounterexampleValue::Bool(*b))),
                    _ => {}
                }
            }
            return Counterexample { assignments, trace: None };
        }
        Counterexample {
            assignments: vec![(
                UNGROUNDED_LABEL.to_string(),
                CounterexampleValue::Term(ungrounded_reason(func, reasons, cex)),
            )],
            trace: None,
        }
    }
}

/// Rewrite each fresh bitvector operand var to the source name it stands for.
fn project_bitvector_operands(
    func: &VerifiableFunction,
    names: &trust_types::fx::FxHashMap<String, usize>,
    cex: &Counterexample,
) -> Counterexample {
    if !cex.assignments.iter().any(|(name, _)| split_bv_operand_name(name).is_some()) {
        return cex.clone();
    }
    let bound: trust_types::fx::FxHashSet<&str> =
        cex.assignments.iter().map(|(n, _)| n.as_str()).collect();
    let mut assignments = Vec::with_capacity(cex.assignments.len());
    for (name, value) in &cex.assignments {
        let Some((_, base)) = split_bv_operand_name(name) else {
            assignments.push((name.clone(), value.clone()));
            continue;
        };
        // Not a name this function owns: leave the encoding's spelling alone
        // rather than inventing a source variable.
        let Some(&local) = names.get(base) else {
            assignments.push((name.clone(), value.clone()));
            continue;
        };
        if bound.contains(base) {
            // Redundant with the source binding, which is already there.
            continue;
        }
        let Some(ty) = crate::local_ty_ref(func, local) else {
            assignments.push((name.clone(), value.clone()));
            continue;
        };
        match model_int(value, Some(ty)) {
            Some(projected) => {
                assignments.push((base.to_string(), CounterexampleValue::Int(projected)));
            }
            None => assignments.push((name.clone(), value.clone())),
        }
    }
    Counterexample { assignments, trace: cex.trace.clone() }
}

/// Ground every refuted row of `results` in place, so no consumer — the human
/// diagnostic, the JSON transport, the backprop prompt — can see a witness the
/// function's own definitions refute.
///
/// Touches ONLY the counterexample of a `Failed` row. Verdicts, kinds, timings
/// and every other row are byte-identical, so this cannot move a verdict.
pub fn ground_delivered_counterexamples(
    func: &VerifiableFunction,
    results: &mut [(trust_types::VerificationCondition, VerificationResult)],
) {
    if !results.iter().any(|(_, result)| {
        matches!(result, VerificationResult::Failed { counterexample: Some(_), .. })
    }) {
        return;
    }
    let grounder = Grounder::new(func);
    for (_, result) in results.iter_mut() {
        let VerificationResult::Failed { counterexample: Some(cex), .. } = result else {
            continue;
        };
        *cex = grounder.deliver(cex);
    }
}

#[cfg(test)]
mod tests;
