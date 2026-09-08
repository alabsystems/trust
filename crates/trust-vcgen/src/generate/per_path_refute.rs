// trust-vcgen/generate/per_path_refute: the PER-PATH, refute-only assert lane.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

//! Trust: per-path (under-approximating) `assert!`/`panic!` REFUTATION.
//!
//! # The gap this closes
//!
//! The bidirectional lane ([`super::assert_refutation`]) builds ONE formula per
//! panic block: the CFG-wide path-guard disjunction, with loop-carried values
//! left FREE. That freedom is exactly what makes its UNSAT a real proof — a free
//! loop-carried `i` covers every iteration count, including the ones past the
//! back edge. The price is that the formula is then ungrounded, and the lane
//! refuses to emit it (`if !grounded { continue; }`) rather than refute on an
//! unconstrained variable. So
//!
//! ```ignore
//! pub fn f(n: u8) -> u8 {
//!     let mut t = 0u8; let mut i = 0u8;
//!     while i < 4 { assert!(n != i); t ^= i; i += 1; }
//!     t
//! }
//! ```
//!
//! — which panics for every `n` in `0..4` — is DECLINED, not refuted.
//!
//! # What this lane does instead
//!
//! It enumerates ACYCLIC CFG paths from the entry block to the panic block and
//! SYMBOLICALLY EXECUTES each one: every read resolves to the value written by
//! the last write ON THAT PATH, every branch contributes its exact condition.
//! For the loop above, the zero-iteration path `bb0 → bb1 → bb2 → bb4` yields
//! `t = 0 ∧ i = 0 ∧ 0 < 4 ∧ ¬(n ≠ 0)`, whose only model is `n = 0` — and `f(0)`
//! really does panic on the first iteration.
//!
//! # Direction (the whole reason this is a separate VC class)
//!
//! The formula UNDER-approximates the reachable states:
//!
//! * **SAT is sound**: a model is a complete assignment to the free inputs under
//!   which the concrete, enumerated block sequence executes and reaches the
//!   panic. A witness, not an alarm.
//! * **UNSAT is NOT a proof**: the enumeration stops at the first repeat of a
//!   block, so nothing past a back edge is modeled at all. An UNSAT says only
//!   "not on these paths".
//!
//! The emitted [`RefuteOnlyVc`] carries that asymmetry in its TYPE: a consumer
//! can obtain a refutation from it and literally cannot obtain anything else
//! (see [`trust_types::RefuteOnlyOutcome`]).
//!
//! # The invariant every rule in this file must preserve
//!
//! **Never leave a read unconstrained.** An unconstrained read turns the formula
//! into an OVER-approximation, and SAT under an over-approximation is a SPURIOUS
//! witness — a false refutation, which is strictly worse than declining. So:
//!
//! * a read of a local with no symbolic value on this path DROPS the path;
//! * an rvalue/statement/terminator whose semantics this file cannot reproduce
//!   EXACTLY drops the path;
//! * where an operation is modeled only on a subset of its domain (integer
//!   `Add`/`Sub`/`Mul` restricted to the non-wrapping case, `as` casts restricted
//!   to the value-preserving case), the restricting constraint is CONJOINED, so
//!   the model set shrinks rather than grows. Shrinking is always sound here: it
//!   can only lose refutations, never invent one.
//!
//! Dropping a path, or dropping every path, costs completeness only: the lane
//! then emits nothing and the obligation stays exactly as undischarged as it is
//! today.
//!
//! # The one place this lane consumes an ASSUMPTION
//!
//! Everything above is derived from the function's own TrustIr. The single
//! exception is the `for &x in <&[T; N]>` shape, whose two defining calls
//! (`IntoIterator::into_iter`, `Iterator::next`) are OPAQUE — there is nothing
//! to thread on any path, so the lane declined every such loop outright. The
//! private submodule [`std_iter`] supplies a VALUE summary for exactly those two
//! callees, and is a private `mod` precisely so no other lane in `trust-vcgen`
//! can reach it: an assumption that could reach the bidirectional class would
//! license an UNSAT-based FALSE PROOF, whereas here its worst outcome is a
//! spurious witness. Read that module's header before touching anything below
//! that mentions it.

/// The slice-iterator value summary. PRIVATE on purpose — see its module docs:
/// its content is an assumption about `core`, and confining it to this lane is
/// what keeps that assumption on the refutation side of the verifier.
mod std_iter;

use trust_types::fx::FxHashMap;
use trust_types::{
    BasicBlock, BinOp, BlockId, ConstValue, Formula, Operand, Place, Projection,
    RefuteOnlyProvenance, RefuteOnlyVc, Rvalue, Sort, Statement, Terminator, Ty, UnOp, VcKind,
    VerifiableFunction, VerificationCondition,
};

/// Acyclic paths enumerated per panic block. Each becomes one solver query, so
/// this bounds the added solve cost per panic site.
const MAX_PATHS_PER_BLOCK: usize = 16;

/// Longest acyclic path (in blocks) this lane will symbolically execute.
const MAX_PATH_BLOCKS: usize = 48;

/// Hard bound on DFS expansion per panic block — a fail-closed guard against a
/// combinatorial CFG. Tripping it abandons the block entirely.
const MAX_DFS_STEPS: usize = 20_000;

/// Bound on the total formula-node count of one path's constraint set.
/// Substitution can grow a value quadratically along a path (`x = x + x`); a
/// path that exceeds this is dropped rather than handed to the solver.
const MAX_PATH_FORMULA_NODES: usize = 8_192;

/// The symbolic value of a local along one concrete path.
///
/// Only shapes this file can reproduce EXACTLY are representable. There is
/// deliberately no "unknown" constructor: an unknown value must drop the path,
/// not enter the formula.
#[derive(Debug, Clone)]
enum SymValue {
    /// An `Int`- or `Bool`-sorted term over the function's free inputs.
    Scalar(Formula),
    /// A two-field tuple `(value, flag)` — a `CheckedBinaryOp` result or a
    /// 2-tuple aggregate of scalars.
    Pair(Formula, Formula),
    /// A SHARED reference to a `[T; N]` whose element values are exactly
    /// `elems` (index `i` ↦ `elems[i]`), each an `Int`-sorted free input.
    ///
    /// Created ONLY for a `&[T; N]` PARAMETER, where the `N` element symbols are
    /// genuinely free: for any in-range assignment there is a caller that passes
    /// such an array, so no model is invented. `T` is a scalar integer, which
    /// has no interior mutability, so a shared borrow fixes the values for the
    /// whole body — nothing in the function can change them.
    ArrayRef { elem_ty: Ty, elems: Vec<Formula> },
    /// A `core::slice::iter::Iter<'_, T>` positioned at `cursor` over `elems`.
    /// `cursor == elems.len()` is the exhausted iterator.
    SliceIter { elem_ty: Ty, elems: Vec<Formula>, cursor: usize },
    /// A reference to the WHOLE of local `k`. Created only by `Rvalue::Ref` of a
    /// local that already holds a [`SymValue::SliceIter`], so the only thing it
    /// can be handed to is the summarized `next` — which writes the advanced
    /// iterator back through it.
    LocalRef(usize),
    /// A shared `&T` whose pointee value is exactly this `Int`-sorted term.
    ElemRef(Formula),
    /// An enum value known EXACTLY: variant at INDEX `index` in the declared
    /// type's `variants` list, carrying `payload` for its single field (if any).
    ///
    /// The index — not the tag. `Rvalue::Discriminant` maps it through the
    /// declared `VariantDef::discriminant`, and `Projection::Downcast` compares
    /// against it directly, which is how a niche-encoded `Option<&T>` is handled
    /// without assuming anything about its layout.
    Variant { index: usize, payload: Option<Box<SymValue>> },
}

impl SymValue {
    fn scalar(self) -> Option<Formula> {
        match self {
            SymValue::Scalar(f) => Some(f),
            _ => None,
        }
    }
}

/// Symbolic state threaded along ONE path.
struct PathState {
    /// local -> its value after the writes seen so far on this path. A local
    /// ABSENT here has no known value; reading it drops the path.
    env: FxHashMap<usize, SymValue>,
    /// Accumulated path condition: parameter type ranges, branch conditions, and
    /// the domain restrictions of partially-modeled operations.
    constraints: Vec<Formula>,
    /// Running node budget across `env` values and `constraints`.
    nodes: usize,
}

/// Total node count of a formula (budget accounting only).
fn formula_nodes(f: &Formula) -> usize {
    let mut n = 0usize;
    f.visit(&mut |_| n = n.saturating_add(1));
    n
}

/// Per-function lookup indices, built once.
///
/// `acyclic_paths_to` performs one block lookup per DFS step (up to
/// [`MAX_DFS_STEPS`] per panic block) and the evaluator performs several local
/// lookups per statement; a linear scan for each would make this lane's cost
/// quadratic in the size of exactly the machine-generated bodies the verifier
/// already struggles with. Pure indexing — no semantics.
struct Ctx<'f> {
    func: &'f VerifiableFunction,
    /// BlockId -> position in `func.body.blocks`.
    block_at: FxHashMap<BlockId, usize>,
    /// LocalDecl.index -> position in `func.body.locals`.
    local_at: FxHashMap<usize, usize>,
}

impl<'f> Ctx<'f> {
    /// `None` when a block id or a local index is duplicated — the caller
    /// declines the whole function in that case, because a duplicated key makes
    /// every lookup below ambiguous.
    fn build(func: &'f VerifiableFunction) -> Option<Self> {
        let mut block_at = FxHashMap::default();
        for (position, block) in func.body.blocks.iter().enumerate() {
            if block_at.insert(block.id, position).is_some() {
                return None;
            }
        }
        let mut local_at = FxHashMap::default();
        for (position, decl) in func.body.locals.iter().enumerate() {
            if local_at.insert(decl.index, position).is_some() {
                return None;
            }
        }
        Some(Ctx { func, block_at, local_at })
    }

    fn block(&self, id: BlockId) -> Option<&'f BasicBlock> {
        self.func.body.blocks.get(*self.block_at.get(&id)?)
    }

    /// The declared type of a whole local.
    fn local_ty(&self, local: usize) -> Option<&'f Ty> {
        self.func.body.locals.get(*self.local_at.get(&local)?).map(|d| &d.ty)
    }
}

/// The SMT variable name for parameter local `index`.
///
/// INJECTIVITY (load-bearing: two parameters sharing a name would silently
/// identify two independent inputs, and a model over the merged symbol would not
/// be a real execution): the source name is used only when it is unique among
/// ALL of the function's local names AND is not spelled like any local's
/// `_<index>` fallback. Otherwise every parameter falls back to `_<index>`,
/// which is injective because local indices are unique — `Ctx::build` rejects the
/// function outright when they are not, and it runs before every call here.
fn param_var_name(func: &VerifiableFunction, index: usize) -> String {
    let fallback = format!("_{index}");
    let Some(decl) = func.body.locals.iter().find(|d| d.index == index) else {
        return fallback;
    };
    let Some(name) = decl.name.as_deref() else {
        return fallback;
    };
    if name.is_empty() {
        return fallback;
    }
    let shared = func.body.locals.iter().filter(|d| d.name.as_deref() == Some(name)).count() > 1;
    let looks_like_a_fallback =
        func.body.locals.iter().any(|d| name == format!("_{}", d.index).as_str());
    if shared || looks_like_a_fallback { fallback } else { name.to_string() }
}

/// The `(width, signed)` of a scalar integer type, or `None` for anything else.
fn int_shape(ty: &Ty) -> Option<(u32, bool)> {
    match ty {
        Ty::Int { width, signed } => Some((*width, *signed)),
        _ => None,
    }
}

/// The initial state at function entry: every scalar parameter is a free input
/// symbol constrained to its type range; every other local is ABSENT (so reading
/// it before a write on this path drops the path).
///
/// SOUNDNESS of the range facts: a parameter always holds a value of its type,
/// so `min <= p <= max` holds in every real execution. Conjoining it can only
/// shrink the model set — it can never admit an assignment a real execution
/// could not produce.
fn entry_state(ctx: &Ctx<'_>) -> PathState {
    let func = ctx.func;
    let mut st = PathState { env: FxHashMap::default(), constraints: Vec::new(), nodes: 0 };
    for decl in &func.body.locals {
        if decl.index < 1 || decl.index > func.body.arg_count {
            continue; // local 0 is the return slot; beyond arg_count are temps
        }
        let name = param_var_name(func, decl.index);
        match &decl.ty {
            Ty::Bool => {
                st.env.insert(decl.index, SymValue::Scalar(Formula::var(&name, Sort::Bool)));
            }
            Ty::Int { width, signed } => {
                let v = Formula::var(&name, Sort::Int);
                st.constraints.push(crate::range::input_range_constraint(&v, *width, *signed));
                st.env.insert(decl.index, SymValue::Scalar(v));
            }
            // A SHARED `&[T; N]` parameter with scalar-integer elements is
            // symbolized ELEMENT-WISE — see `array_param_element_symbols` for
            // why that is an exact model rather than an over-approximation.
            Ty::Ref { .. } => {
                if let Some((elem_ty, elems)) = array_param_element_symbols(func, decl.index)
                    && let Some((width, signed)) = int_shape(&elem_ty)
                {
                    for elem in &elems {
                        st.constraints
                            .push(crate::range::input_range_constraint(elem, width, signed));
                    }
                    st.env.insert(decl.index, SymValue::ArrayRef { elem_ty, elems });
                }
            }
            // Any other non-scalar parameter gets NO symbol. Any read of it
            // drops the path — deliberately, because an opaque whole-value
            // symbol plus an independent symbol per field read would decorrelate
            // storage that is really the same storage (an over-approximation).
            _ => {}
        }
    }
    st.nodes = st.constraints.iter().map(formula_nodes).sum();
    st
}

/// The free element symbols of a `&[T; N]` PARAMETER, or `None` if this
/// parameter is not one this lane symbolizes.
///
/// # Why element symbols are an EXACT model, not an over-approximation
///
/// The lane's governing invariant is "never leave a read unconstrained". A whole
/// aggregate handed an opaque symbol would violate it (two reads of the same
/// storage could decorrelate). `N` INDEPENDENT symbols do not: the observable
/// content of a `&[T; N]` with `T` a scalar integer IS exactly `N` independent
/// values, and
///
/// * they are genuinely FREE — for any assignment within the element type's
///   range there exists a caller (`f(&[v0, …, vN-1])`), so a model is realizable
///   as an actual execution rather than merely consistent;
/// * they are genuinely STABLE — `T` is an integer, which contains no
///   `UnsafeCell`, so a SHARED borrow forbids every mutation channel for the
///   whole body. `&mut [T; N]` is therefore NOT admitted here.
///
/// # Naming
///
/// `{ELEM_VAR_PREFIX}{local}_{k}`, and the whole parameter is DECLINED if any
/// minted name collides with a source local name or with a `_<index>` fallback
/// spelling — a collision would merge an element symbol with an unrelated
/// parameter, and a model over a merged symbol is not an execution.
fn array_param_element_symbols(
    func: &VerifiableFunction,
    index: usize,
) -> Option<(Ty, Vec<Formula>)> {
    let decl = func.body.locals.iter().find(|d| d.index == index)?;
    let Ty::Ref { mutable: false, inner } = &decl.ty else {
        return None;
    };
    let Ty::Array { elem, len } = inner.as_ref() else {
        return None;
    };
    if !matches!(elem.as_ref(), Ty::Int { .. })
        || *len == 0
        || *len > std_iter::MAX_MODELED_ARRAY_LEN
    {
        return None;
    }
    let len = usize::try_from(*len).ok()?;
    let mut elems = Vec::with_capacity(len);
    for k in 0..len {
        let name = format!("{}{index}_{k}", std_iter::ELEM_VAR_PREFIX);
        // Fail-closed on any chance of aliasing a parameter symbol.
        let collides =
            func.body.locals.iter().any(|d| {
                d.name.as_deref() == Some(name.as_str()) || name == format!("_{}", d.index)
            });
        if collides {
            return None;
        }
        elems.push(Formula::var_owned(name, Sort::Int));
    }
    Some((elem.as_ref().clone(), elems))
}

/// Evaluate an operand in the current state. `None` = drop the path.
fn eval_operand(st: &PathState, op: &Operand) -> Option<SymValue> {
    match op {
        Operand::Copy(place) | Operand::Move(place) => eval_place(st, place),
        Operand::Constant(cv) => match cv {
            ConstValue::Bool(b) => Some(SymValue::Scalar(Formula::Bool(*b))),
            ConstValue::Int(n) => Some(SymValue::Scalar(Formula::Int(*n))),
            ConstValue::Uint(n, _) => Some(SymValue::Scalar(match i128::try_from(*n) {
                Ok(v) => Formula::Int(v),
                Err(_) => Formula::UInt(*n),
            })),
            // Every remaining constant form is either non-scalar (Str,
            // OpaqueConst, Unit, CallableItem), float, or an UNKNOWN-VALUED
            // scalar (OpaqueScalar, ConstParam). Lowering an unknown-valued
            // constant to a free symbol is precisely the over-approximation this
            // lane must not make, so all of them drop the path.
            _ => None,
        },
        // A lifted `Symbolic` payload carries free variables this lane does not
        // own or constrain; `Unsupported` is unconstrained by definition.
        _ => None,
    }
}

/// Read a place. Whole values, the two fields of a tracked `Pair`, a deref of a
/// tracked reference and the payload of a tracked enum variant are supported;
/// every other projection drops the path.
fn eval_place(st: &PathState, place: &Place) -> Option<SymValue> {
    let value = st.env.get(&place.local)?;
    match place.projections.as_slice() {
        [] => Some(value.clone()),
        [Projection::Field(k)] => match (value, k) {
            (SymValue::Pair(v, _), 0) => Some(SymValue::Scalar(v.clone())),
            (SymValue::Pair(_, f), 1) => Some(SymValue::Scalar(f.clone())),
            _ => None,
        },
        // Deref of a reference this lane MINTED, so the referent is known
        // exactly. `ElemRef` carries the pointee value directly; `LocalRef`
        // resolves to the local's CURRENT value on this path, which is what
        // keeps the summarized `next`'s write-back visible to later reads.
        [Projection::Deref] => match value {
            SymValue::ElemRef(f) => Some(SymValue::Scalar(f.clone())),
            SymValue::LocalRef(k) => st.env.get(k).cloned(),
            _ => None,
        },
        // `((_x as Some).0)`. The downcast index must MATCH the variant this
        // path established — the path condition already forced the discriminant,
        // so a mismatch means the value is not what the projection claims and
        // the path is dropped rather than guessed at.
        [Projection::Downcast(v), Projection::Field(0)] => match value {
            SymValue::Variant { index, payload: Some(p) } if index == v => Some((**p).clone()),
            _ => None,
        },
        _ => None,
    }
}

/// A comparison of two `Int`/`Bool` terms, exact in both theories.
fn compare(op: BinOp, l: Formula, r: Formula, ordered_ok: bool) -> Option<Formula> {
    Some(match op {
        BinOp::Eq => Formula::Eq(Box::new(l), Box::new(r)),
        BinOp::Ne => Formula::Not(Box::new(Formula::Eq(Box::new(l), Box::new(r)))),
        BinOp::Lt if ordered_ok => Formula::Lt(Box::new(l), Box::new(r)),
        BinOp::Le if ordered_ok => Formula::Le(Box::new(l), Box::new(r)),
        BinOp::Gt if ordered_ok => Formula::Gt(Box::new(l), Box::new(r)),
        BinOp::Ge if ordered_ok => Formula::Ge(Box::new(l), Box::new(r)),
        _ => return None,
    })
}

/// Sort of an operand as this lane models it: `Bool` for bools, `Int` for
/// integers, `None` (drop) for everything else.
fn modeled_operand_kind(ctx: &Ctx<'_>, st: &PathState, op: &Operand) -> Option<Sort> {
    match op {
        Operand::Constant(ConstValue::Bool(_)) => Some(Sort::Bool),
        Operand::Constant(ConstValue::Int(_) | ConstValue::Uint(..)) => Some(Sort::Int),
        Operand::Copy(place) | Operand::Move(place) => {
            // A tracked `Pair` field: field 0 carries the arithmetic result
            // (Int), field 1 the overflow flag (Bool).
            match place.projections.as_slice() {
                [] => match ctx.local_ty(place.local)? {
                    Ty::Bool => Some(Sort::Bool),
                    Ty::Int { .. } => Some(Sort::Int),
                    _ => None,
                },
                [Projection::Field(k)] => match (st.env.get(&place.local)?, k) {
                    (SymValue::Pair(..), 0) => Some(Sort::Int),
                    (SymValue::Pair(..), 1) => Some(Sort::Bool),
                    _ => None,
                },
                _ => None,
            }
        }
        _ => None,
    }
}

/// Evaluate an rvalue being assigned to `dest`. `None` = drop the path.
///
/// Every arm is either an EXACT reproduction of the MIR semantics or an exact
/// reproduction on a RESTRICTED domain whose restriction is pushed into
/// `st.constraints`. There is no arm that invents a free symbol.
fn eval_rvalue(
    ctx: &Ctx<'_>,
    st: &mut PathState,
    dest: &Place,
    rvalue: &Rvalue,
) -> Option<SymValue> {
    match rvalue {
        Rvalue::Use(op) => eval_operand(st, op),

        Rvalue::BinaryOp(op, l, r) => {
            let lk = modeled_operand_kind(ctx, st, l)?;
            let rk = modeled_operand_kind(ctx, st, r)?;
            if lk != rk {
                return None;
            }
            let lf = eval_operand(st, l)?.scalar()?;
            let rf = eval_operand(st, r)?.scalar()?;
            match op {
                BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                    compare(*op, lf, rf, lk == Sort::Int).map(SymValue::Scalar)
                }
                // Bitwise ops on BOOLEANS are exactly the logical connectives.
                // On integers they are not expressible in the linear-integer
                // encoding this lane emits, so they drop.
                BinOp::BitAnd if lk == Sort::Bool => {
                    Some(SymValue::Scalar(Formula::And(vec![lf, rf])))
                }
                BinOp::BitOr if lk == Sort::Bool => {
                    Some(SymValue::Scalar(Formula::Or(vec![lf, rf])))
                }
                BinOp::BitXor if lk == Sort::Bool => Some(SymValue::Scalar(Formula::Not(
                    Box::new(Formula::Eq(Box::new(lf), Box::new(rf))),
                ))),
                // Integer Add/Sub/Mul. In an overflow-checks-off body these WRAP,
                // which the unbounded-integer encoding does not express — so the
                // model set is RESTRICTED to executions in which the result fits
                // the destination type, where the unbounded result is the exact
                // machine result. Restricting is sound in the refute direction:
                // it can only drop counterexamples, never manufacture one.
                BinOp::Add | BinOp::Sub | BinOp::Mul if lk == Sort::Int => {
                    let (width, signed) = int_shape(ctx.local_ty(dest.local)?)?;
                    let value = match op {
                        BinOp::Add => Formula::Add(Box::new(lf), Box::new(rf)),
                        BinOp::Sub => Formula::Sub(Box::new(lf), Box::new(rf)),
                        _ => Formula::Mul(Box::new(lf), Box::new(rf)),
                    };
                    st.constraints
                        .push(crate::range::input_range_constraint(&value, width, signed));
                    Some(SymValue::Scalar(value))
                }
                _ => None,
            }
        }

        // `(value, overflow_flag)`. Modeled on the NON-OVERFLOWING domain only:
        // the result is constrained to the destination tuple's integer field
        // range and the flag is `false`. Sound as above (a strict restriction);
        // the cost is that this lane never refutes an overflow panic — those are
        // the bidirectional `ArithmeticOverflow` obligation's business anyway.
        Rvalue::CheckedBinaryOp(op, l, r) => {
            if !matches!(op, BinOp::Add | BinOp::Sub | BinOp::Mul) {
                return None;
            }
            if modeled_operand_kind(ctx, st, l)? != Sort::Int
                || modeled_operand_kind(ctx, st, r)? != Sort::Int
            {
                return None;
            }
            let lf = eval_operand(st, l)?.scalar()?;
            let rf = eval_operand(st, r)?.scalar()?;
            let Ty::Tuple(fields) = ctx.local_ty(dest.local)? else {
                return None;
            };
            let (width, signed) = int_shape(fields.first()?)?;
            let value = match op {
                BinOp::Add => Formula::Add(Box::new(lf), Box::new(rf)),
                BinOp::Sub => Formula::Sub(Box::new(lf), Box::new(rf)),
                _ => Formula::Mul(Box::new(lf), Box::new(rf)),
            };
            st.constraints.push(crate::range::input_range_constraint(&value, width, signed));
            Some(SymValue::Pair(value, Formula::Bool(false)))
        }

        Rvalue::UnaryOp(UnOp::Not, op) => {
            // Boolean negation only. `!x` on an integer is bitwise complement,
            // which the integer encoding cannot express.
            if modeled_operand_kind(ctx, st, op)? != Sort::Bool {
                return None;
            }
            let f = eval_operand(st, op)?.scalar()?;
            Some(SymValue::Scalar(Formula::Not(Box::new(f))))
        }

        Rvalue::UnaryOp(UnOp::Neg, op) => {
            if modeled_operand_kind(ctx, st, op)? != Sort::Int {
                return None;
            }
            let f = eval_operand(st, op)?.scalar()?;
            let (width, signed) = int_shape(ctx.local_ty(dest.local)?)?;
            let value = Formula::Neg(Box::new(f));
            st.constraints.push(crate::range::input_range_constraint(&value, width, signed));
            Some(SymValue::Scalar(value))
        }

        // `as` casts, on the VALUE-PRESERVING domain only.
        //
        // int -> int: the model is `result == source` PLUS `result ∈ range(dest)`.
        // On that restricted domain the `as` conversion IS the identity (a value
        // representable in the destination type is unchanged by truncation /
        // sign reinterpretation), so the model is exact there; every wrapping or
        // reinterpreting execution is simply excluded. Restriction again = sound
        // in the refute direction.
        //
        // bool -> int is total and exact: `Ite(b, 1, 0)`.
        Rvalue::Cast(op, to) => {
            let from = modeled_operand_kind(ctx, st, op)?;
            let f = eval_operand(st, op)?.scalar()?;
            match (from, to) {
                (Sort::Int, Ty::Int { width, signed }) => {
                    st.constraints.push(crate::range::input_range_constraint(&f, *width, *signed));
                    Some(SymValue::Scalar(f))
                }
                (Sort::Bool, Ty::Int { .. }) => Some(SymValue::Scalar(Formula::Ite(
                    Box::new(f),
                    Box::new(Formula::Int(1)),
                    Box::new(Formula::Int(0)),
                ))),
                _ => None,
            }
        }

        // `&mut it` / `&it`, admitted ONLY when the referent already holds a
        // tracked slice iterator. That is the whole `for`-loop receiver shape and
        // nothing else: the resulting `LocalRef` can only be consumed by the
        // summarized `next` (which writes the advanced iterator BACK through it)
        // or by a `Deref` read, both of which resolve to the referent's current
        // value. A reference to anything else would be a handle this lane cannot
        // track through an opaque callee, so it drops the path.
        //
        // NOTE a write THROUGH such a reference is still impossible here:
        // `apply_statement` rejects every projected assignment, so the only
        // mutation channel is the summarized call itself.
        Rvalue::Ref { place, .. } => {
            if !place.projections.is_empty() {
                return None;
            }
            match st.env.get(&place.local) {
                Some(SymValue::SliceIter { .. }) => Some(SymValue::LocalRef(place.local)),
                _ => None,
            }
        }

        // `discriminant(_x)` where `_x` holds a tracked enum value. The tag is
        // read from the DECLARED `VariantDef::discriminant` of the variant this
        // path established — never assumed to equal the variant index, which
        // would be a layout assumption on top of the value summary (and is false
        // in general for `#[repr(iN)]` enums with explicit tags).
        Rvalue::Discriminant(place) => {
            if !place.projections.is_empty() {
                return None;
            }
            let SymValue::Variant { index, .. } = st.env.get(&place.local)? else {
                return None;
            };
            let Ty::Adt { variants, .. } = ctx.local_ty(place.local)? else {
                return None;
            };
            Some(SymValue::Scalar(Formula::Int(variants.get(*index)?.discriminant)))
        }

        // A general tuple `Aggregate` is deliberately NOT modeled. `SymValue::Pair`
        // exists only as a `CheckedBinaryOp` result, which fixes its field sorts at
        // (Int value, Bool flag) — the assumption `modeled_operand_kind` makes when
        // it types a `.0`/`.1` read. Admitting arbitrary 2-tuples would break that
        // assumption and could emit an ILL-SORTED comparison (`Lt` over two boolean
        // terms), whose solver behaviour is not a fact about the program.
        //
        // Raw pointers, lengths, array repeats, pointer arithmetic and the
        // `Unsupported` sentinel are all unmodeled here too.
        _ => None,
    }
}

/// Does `value` carry the sort the local's DECLARED type implies?
///
/// The read side (`modeled_operand_kind`) types an operand from the declared
/// type; this is the write-side half that makes that safe. A `Pair` is only ever
/// a `CheckedBinaryOp` result, so its local must be a `(integer, bool)` tuple.
fn value_matches_declared_sort(ctx: &Ctx<'_>, local: usize, value: &SymValue) -> bool {
    let Some(ty) = ctx.local_ty(local) else {
        return false;
    };
    value_matches_ty(ctx, ty, value)
}

/// The structural half of [`value_matches_declared_sort`], recursive so an enum
/// payload is checked against the field type the DECLARED variant announces.
///
/// Every arm is a hard gate on storing a value: a mismatch drops the path. That
/// is what lets every read be typed from the declared type alone, and what stops
/// an ill-sorted atom (whose satisfiability is not a statement about the
/// program, i.e. a potential SPURIOUS witness) from ever being built.
fn value_matches_ty(ctx: &Ctx<'_>, ty: &Ty, value: &SymValue) -> bool {
    match value {
        SymValue::Scalar(f) => {
            let expected = match ty {
                Ty::Bool => Sort::Bool,
                Ty::Int { .. } => Sort::Int,
                _ => return false,
            };
            crate::formula_sort(f) == Some(expected)
        }
        SymValue::Pair(v, flag) => {
            let Ty::Tuple(fields) = ty else {
                return false;
            };
            fields.len() == 2
                && matches!(fields[0], Ty::Int { .. })
                && matches!(fields[1], Ty::Bool)
                && crate::formula_sort(v) == Some(Sort::Int)
                && crate::formula_sort(flag) == Some(Sort::Bool)
        }
        // The element count and element type must agree with the DECLARED array,
        // so a value built for one array can never be stored as another.
        SymValue::ArrayRef { elem_ty, elems } => {
            let Ty::Ref { mutable: false, inner } = ty else {
                return false;
            };
            let Ty::Array { elem, len } = inner.as_ref() else {
                return false;
            };
            elem.as_ref() == elem_ty
                && usize::try_from(*len).is_ok_and(|n| n == elems.len())
                && elems.iter().all(|f| crate::formula_sort(f) == Some(Sort::Int))
        }
        // Only the ADT identity is checked here, not the iterator's element
        // type: `slice::Iter`'s fields are raw pointers whose spelling is a
        // std-internal layout detail, and depending on it would make this
        // fail-closed on a std refactor for no gain. The element type is pinned
        // where it matters instead — `apply_std_iter_call` requires the `next`
        // destination to be `Option<&elem_ty>` for the SAME `elem_ty` this value
        // carries, so an iterator stored under a mismatched element type can
        // never yield anything.
        SymValue::SliceIter { elems, cursor, .. } => {
            matches!(ty, Ty::Adt { name, .. } if std_iter::is_slice_iter_adt(name))
                && *cursor <= elems.len()
                && elems.iter().all(|f| crate::formula_sort(f) == Some(Sort::Int))
        }
        // A `LocalRef` is only sound while the declared pointee type is the
        // referent local's own type — otherwise a deref would read storage as
        // something it is not.
        SymValue::LocalRef(k) => match (ty, ctx.local_ty(*k)) {
            (Ty::Ref { inner, .. }, Some(referent)) => inner.as_ref() == referent,
            _ => false,
        },
        SymValue::ElemRef(f) => {
            matches!(ty, Ty::Ref { mutable: false, inner } if matches!(inner.as_ref(), Ty::Int { .. }))
                && crate::formula_sort(f) == Some(Sort::Int)
        }
        SymValue::Variant { index, payload } => {
            let Ty::Adt { variants, .. } = ty else {
                return false;
            };
            let Some(variant) = variants.get(*index) else {
                return false;
            };
            match (payload, variant.fields.as_slice()) {
                (None, []) => true,
                (Some(p), [(_, field_ty)]) => value_matches_ty(ctx, field_ty, p),
                _ => false,
            }
        }
    }
}

/// Store `value` into whole local `local`. `false` = drop the path.
///
/// The single write point for the environment, so the two gates below hold for
/// statement writes and for the summarized calls' destination/write-back alike.
fn store_local(ctx: &Ctx<'_>, st: &mut PathState, local: usize, value: SymValue) -> bool {
    // WELL-SORTEDNESS INVARIANT. Every value stored must carry the sort its
    // local's DECLARED type implies, so a later read can be typed from the
    // declared type alone (which is exactly what `modeled_operand_kind` does).
    // Without this a body whose TrustIr types and values disagree could produce
    // an ill-sorted atom (`Lt` over booleans), and an ill-sorted atom's
    // satisfiability is not a statement about the program — i.e. a potential
    // SPURIOUS witness. Fail-closed: a mismatch drops the path.
    if !value_matches_declared_sort(ctx, local, &value) {
        return false;
    }
    // Size budget, charged at the write. Substitution can grow a value
    // super-linearly along a path (`x = x + x` doubles it each time), so the
    // bound is enforced per stored value rather than by rescanning the whole
    // environment after every statement (which would itself be quadratic).
    // Exceeding it drops the path — fail-closed.
    if sym_value_nodes(&value) > MAX_PATH_FORMULA_NODES {
        return false;
    }
    st.env.insert(local, value);
    true
}

/// Apply one statement. `false` = drop the path.
fn apply_statement(ctx: &Ctx<'_>, st: &mut PathState, stmt: &Statement) -> bool {
    match stmt {
        Statement::Assign { place, rvalue, .. } => {
            // A projected WRITE would partially update storage this lane models
            // as a whole value; not attempted.
            if !place.projections.is_empty() {
                return false;
            }
            let Some(value) = eval_rvalue(ctx, st, place, rvalue) else {
                return false;
            };
            store_local(ctx, st, place.local, value)
        }
        // Storage boundaries: the local's contents are indeterminate on both
        // sides, so FORGET the value. A subsequent read before a write then
        // drops the path (fail-closed) instead of reading a stale value.
        Statement::StorageLive(local) | Statement::StorageDead(local) => {
            st.env.remove(local);
            true
        }
        // A pure place mention has no value effect.
        Statement::PlaceMention(_) => true,
        // SetDiscriminant / Deinit / Retag / Intrinsic / CopyNonOverlapping /
        // Unsupported all write storage in ways this lane does not reproduce.
        _ => false,
    }
}

/// Apply the effect of a SUMMARIZED slice-iterator call terminator. `false` =
/// drop the path.
///
/// THE ONE PLACE the value summary enters this lane. Everything it writes is
/// derived from [`std_iter`]'s axiom about `core`, and every step below
/// cross-checks that axiom against the call site's TrustIr TYPES before writing
/// anything — a callee whose rendered path matched but whose types do not line
/// up exactly drops the path instead.
///
/// Called only for terminators [`traversable_successors`] admitted, so a
/// non-summarized `Call` never reaches here.
fn apply_std_iter_call(ctx: &Ctx<'_>, st: &mut PathState, term: &Terminator) -> bool {
    let Terminator::Call { func: callee, args, dest, is_foreign, .. } = term else {
        return false;
    };
    // A foreign import is not `core`'s slice iterator whatever it is called.
    if *is_foreign || !dest.projections.is_empty() {
        return false;
    }
    let Some(kind) = std_iter::recognize(callee) else {
        return false;
    };
    let [arg] = args.as_slice() else {
        return false;
    };
    let value = match kind {
        // `into_iter(&[T; N]) -> Iter<'_, T>` positioned at 0.
        //
        // TYPE CROSS-CHECK: the argument must already carry a tracked
        // `ArrayRef` (i.e. it really is a `&[T; N]` parameter this lane
        // symbolized element-wise), and the destination's declared type must
        // really be `core`/`std`'s slice iterator.
        std_iter::StdIterCall::IntoIterArrayRef => {
            let Some(SymValue::ArrayRef { elem_ty, elems }) = eval_operand(st, arg) else {
                return false;
            };
            if !matches!(ctx.local_ty(dest.local), Some(Ty::Adt { name, .. })
                if std_iter::is_slice_iter_adt(name))
            {
                return false;
            }
            SymValue::SliceIter { elem_ty, elems, cursor: 0 }
        }
        // `next(&mut it) -> Option<&T>`: `Some(&elems[cursor])` while the cursor
        // is in range, `None` once it is not, and the cursor advances (an
        // exhausted slice iterator keeps returning `None`, so it saturates).
        //
        // TYPE CROSS-CHECK: the receiver must resolve to a local holding a
        // tracked `SliceIter`, and the destination's declared type must be an
        // `Option` enum with exactly a field-less `None` and a `Some(&elem_ty)`
        // for the SAME element type the iterator carries.
        std_iter::StdIterCall::SliceIterNext => {
            let Some(SymValue::LocalRef(receiver)) = eval_operand(st, arg) else {
                return false;
            };
            // `_k = next(&mut _k)` cannot arise (borrowck forbids it), and the
            // write-back order below would be ambiguous if it could.
            if receiver == dest.local {
                return false;
            }
            let Some(SymValue::SliceIter { elem_ty, elems, cursor }) =
                st.env.get(&receiver).cloned()
            else {
                return false;
            };
            let Some(shape) =
                std_iter::option_ref_variant_shape(ctx.local_ty(dest.local), &elem_ty)
            else {
                return false;
            };
            let yielded = match elems.get(cursor) {
                Some(elem) => SymValue::Variant {
                    index: shape.some_index,
                    payload: Some(Box::new(SymValue::ElemRef(elem.clone()))),
                },
                None => SymValue::Variant { index: shape.none_index, payload: None },
            };
            let advanced = SymValue::SliceIter {
                elem_ty,
                cursor: cursor.saturating_add(1).min(elems.len()),
                elems,
            };
            if !store_local(ctx, st, receiver, advanced) {
                return false;
            }
            yielded
        }
    };
    store_local(ctx, st, dest.local, value)
}

/// The exact condition under which control leaves `block` for `next`, or `None`
/// if this lane does not model that edge.
fn edge_condition(
    ctx: &Ctx<'_>,
    st: &PathState,
    block: &BasicBlock,
    next: BlockId,
) -> Option<Formula> {
    match &block.terminator {
        Terminator::Goto(t) if *t == next => Some(Formula::Bool(true)),
        // A SUMMARIZED slice-iterator call returns unconditionally to its one
        // target: `into_iter` / `next` on a slice iterator neither panics nor
        // diverges (part of the axiom in [`std_iter`]), so the edge carries no
        // condition. Its VALUE effect is applied by `apply_std_iter_call`, which
        // `execute_path` runs before asking for this condition.
        Terminator::Call { func: callee, target: Some(t), is_foreign: false, .. }
            if *t == next && std_iter::recognize(callee).is_some() =>
        {
            Some(Formula::Bool(true))
        }
        Terminator::SwitchInt { discr, targets, otherwise, .. } => {
            let kind = modeled_operand_kind(ctx, st, discr)?;
            // The scrutinee's DECLARED type, needed to decode the raw arm labels
            // (see [`switch_value_eq`]). `None` drops the path — this lane never
            // guesses a width.
            let discr_ty = crate::operand_ty_cow(ctx.func, discr);
            let discr_ty = discr_ty.as_deref();
            let d = eval_operand(st, discr)?.scalar()?;
            // A value may label several arms; the edge is taken when the
            // discriminant equals ANY of the values labelling it.
            let matching: Vec<u128> =
                targets.iter().filter(|(_, t)| *t == next).map(|(v, _)| *v).collect();
            if !matching.is_empty() {
                let mut arms = Vec::with_capacity(matching.len());
                for v in matching {
                    arms.push(switch_value_eq(&d, &kind, discr_ty, v)?);
                }
                return Some(if arms.len() == 1 {
                    arms.pop().unwrap_or(Formula::Bool(false))
                } else {
                    Formula::Or(arms)
                });
            }
            if *otherwise != next {
                return None;
            }
            // The `otherwise` arm: the discriminant equals none of the labels.
            let mut conj = Vec::with_capacity(targets.len());
            for (v, _) in targets {
                conj.push(Formula::Not(Box::new(switch_value_eq(&d, &kind, discr_ty, *v)?)));
            }
            Some(match conj.len() {
                0 => Formula::Bool(true),
                1 => conj.pop().unwrap_or(Formula::Bool(true)),
                _ => Formula::And(conj),
            })
        }
        // The SUCCESS edge of an `Assert` is taken exactly when the condition
        // holds. The `unwind` (failure) edge is NOT followed: reaching it means
        // the assertion already failed, and this lane never traverses a
        // post-panic cleanup path.
        Terminator::Assert { cond, expected, target, .. } if *target == next => {
            if modeled_operand_kind(ctx, st, cond)? != Sort::Bool {
                return None;
            }
            let f = eval_operand(st, cond)?.scalar()?;
            Some(if *expected { f } else { Formula::Not(Box::new(f)) })
        }
        _ => None,
    }
}

/// `discr == value` for a switch arm label, in the discriminant's modeled sort.
///
/// `ty` is the scrutinee's DECLARED type. The raw MIR label is a two's-
/// complement bit pattern at that type's width, so an `Int`-sorted arm must go
/// through the shared typed decode (`crate::switch_label_to_formula`): reading
/// it as a magnitude put `d == 4294967295` on an `i32` arm, which cannot be the
/// arm's real condition. It was NOT a spurious witness: [`entry_state`] pushes
/// `crate::range::input_range_constraint` for EVERY integer parameter, so
/// `n == 4294967295` conjoined with `n ∈ [-2^31, 2^31-1]` was UNSAT and this
/// lane simply DECLINED the path — a completeness loss. Decoding it makes the
/// path condition the arm's actual meaning.
///
/// `None` for a type the decode cannot establish, which drops the path; per this
/// file's invariant, dropping costs completeness only.
fn switch_value_eq(d: &Formula, kind: &Sort, ty: Option<&Ty>, value: u128) -> Option<Formula> {
    match kind {
        Sort::Bool => match value {
            0 => Some(Formula::Not(Box::new(d.clone()))),
            1 => Some(d.clone()),
            // A bool discriminant can only be 0 or 1, so an arm labelled with
            // anything else is dead. `false` is the exact condition.
            _ => Some(Formula::Bool(false)),
        },
        Sort::Int => Some(Formula::Eq(
            Box::new(d.clone()),
            Box::new(crate::switch_label_to_formula(ty?, value)?),
        )),
        _ => None,
    }
}

/// Symbolically execute one acyclic path, returning its exact feasibility
/// formula, or `None` if any step could not be reproduced exactly.
///
/// `path` is entry-first and ends at the panic block. The panic block's own
/// statements are NOT executed: its terminator is the diverging panic call, and
/// nothing between the block entry and that call can branch away, so reaching
/// the block entry already means the panic happens.
fn execute_path(ctx: &Ctx<'_>, path: &[BlockId]) -> Option<Formula> {
    let mut st = entry_state(ctx);
    for window in path.windows(2) {
        let (here, next) = (window[0], window[1]);
        let block = ctx.block(here)?;
        for stmt in &block.stmts {
            if !apply_statement(ctx, &mut st, stmt) {
                return None;
            }
        }
        // A `Call` terminator only reaches here when `traversable_successors`
        // admitted it, i.e. it is one of the two SUMMARIZED slice-iterator
        // operations. Its destination write (and, for `next`, the cursor
        // write-back through the `&mut` receiver) must land BEFORE the successor
        // block reads them.
        if matches!(block.terminator, Terminator::Call { .. })
            && !apply_std_iter_call(ctx, &mut st, &block.terminator)
        {
            return None;
        }
        let cond = edge_condition(ctx, &st, block, next)?;
        st.nodes = st.nodes.saturating_add(formula_nodes(&cond));
        st.constraints.push(cond);
        if st.nodes > MAX_PATH_FORMULA_NODES {
            return None;
        }
    }
    // Defensive: a path always has at least one edge condition (it has at least
    // two blocks), so this cannot fire today. If it ever could, an empty
    // conjunction would be the vacuous `true` — a claim about nothing — and the
    // right answer is to decline rather than hand the solver a formula whose SAT
    // means nothing.
    if st.constraints.is_empty() {
        return None;
    }
    Some(Formula::And(st.constraints))
}

/// Node cost of one symbolic value (budget accounting only).
fn sym_value_nodes(v: &SymValue) -> usize {
    match v {
        SymValue::Scalar(f) | SymValue::ElemRef(f) => formula_nodes(f),
        SymValue::Pair(a, b) => formula_nodes(a).saturating_add(formula_nodes(b)),
        SymValue::ArrayRef { elems, .. } | SymValue::SliceIter { elems, .. } => {
            elems.iter().map(formula_nodes).fold(0usize, usize::saturating_add)
        }
        SymValue::LocalRef(_) => 1,
        SymValue::Variant { payload, .. } => {
            1usize.saturating_add(payload.as_deref().map_or(0, sym_value_nodes))
        }
    }
}

/// Successors this lane is willing to traverse.
///
/// A general `Call` is excluded even when it has a return target: this lane
/// cannot reproduce a callee's effect on its destination (or on anything
/// reachable through a `&mut` argument), and inventing a free symbol for it is
/// the over-approximation that would make a SAT spurious. `Drop` is excluded for
/// the same reason (drop glue runs arbitrary code). Both exclusions cost
/// completeness only.
///
/// The ONE exception is a call [`std_iter::recognize`] admits, whose effect
/// [`apply_std_iter_call`] does reproduce — and which is then still dropped if
/// the call site's types do not match the summary. Recognition is by name only
/// here, which is fine: naming a successor traversable does not by itself put
/// anything into a formula.
fn traversable_successors(term: &Terminator) -> Vec<BlockId> {
    match term {
        Terminator::Goto(t) => vec![*t],
        Terminator::SwitchInt { targets, otherwise, .. } => {
            let mut out: Vec<BlockId> = targets.iter().map(|(_, t)| *t).collect();
            out.push(*otherwise);
            out
        }
        Terminator::Assert { target, .. } => vec![*target],
        Terminator::Call { func: callee, target: Some(t), is_foreign: false, .. }
            if std_iter::recognize(callee).is_some() =>
        {
            vec![*t]
        }
        _ => Vec::new(),
    }
}

/// Enumerate up to [`MAX_PATHS_PER_BLOCK`] acyclic paths from the entry block to
/// `target`. Each returned path visits no block twice, so it takes no back edge.
fn acyclic_paths_to(ctx: &Ctx<'_>, target: BlockId) -> Vec<Vec<BlockId>> {
    let mut out: Vec<Vec<BlockId>> = Vec::new();
    // The MIR entry block is `bb0`, the same convention `v2_build_path_guard_map`
    // uses. A body without one is declined rather than guessed at: starting the
    // enumeration somewhere other than the entry would model executions that do
    // not begin at the function's start.
    let entry = BlockId(0);
    if ctx.block(entry).is_none() {
        return out;
    }
    let mut steps = 0usize;
    // Explicit stack of (path so far, next successor index to try).
    let mut stack: Vec<(Vec<BlockId>, usize)> = vec![(vec![entry], 0)];
    while let Some((path, idx)) = stack.pop() {
        steps += 1;
        if steps > MAX_DFS_STEPS || out.len() >= MAX_PATHS_PER_BLOCK {
            break;
        }
        let here = match path.last() {
            Some(b) => *b,
            None => continue,
        };
        if here == target {
            if path.len() >= 2 {
                out.push(path);
            }
            continue;
        }
        if path.len() >= MAX_PATH_BLOCKS {
            continue;
        }
        let Some(block) = ctx.block(here) else {
            continue;
        };
        let succs = traversable_successors(&block.terminator);
        if idx >= succs.len() {
            continue;
        }
        // Resume this frame at the next successor, then descend into this one.
        stack.push((path.clone(), idx + 1));
        let next = succs[idx];
        if path.contains(&next) {
            continue; // back edge — the path would stop being acyclic
        }
        let mut extended = path;
        extended.push(next);
        stack.push((extended, 0));
    }
    out
}

/// Is this block's terminator a user `assert!`/`panic!` failure call?
///
/// The SAME predicate the bidirectional lane uses, so the two lanes agree on
/// which sites are refutable and the `unreachable!()` sentinel stays excluded.
fn is_assert_panic_block(block: &BasicBlock) -> bool {
    let Terminator::Call { func: callee, args, .. } = &block.terminator else {
        return false;
    };
    (super::v2_is_assertion_panic_call(callee) || callee.ends_with("::panic"))
        && !super::v2_is_unreachable_sentinel_panic(callee, args)
}

/// Trust: build the PER-PATH, REFUTE-ONLY assert/panic queries for `func`.
///
/// Every returned [`RefuteOnlyVc`] wraps an under-approximating path-feasibility
/// formula: SAT is a witness that a real input drives execution into a real
/// `assert!`/`panic!`; UNSAT means nothing. The type enforces the asymmetry —
/// see [`trust_types::RefuteOnlyOutcome`].
///
/// Returns an empty vector for any function whose panic sites this lane cannot
/// model, which is the fail-closed direction: no query, no verdict, no change.
#[must_use]
pub fn generate_per_path_assert_refutation_vcs(func: &VerifiableFunction) -> Vec<RefuteOnlyVc> {
    if crate::validate_function(func).is_err() {
        return Vec::new();
    }
    // A MIR `TailCall` to a panic entry point is the same terminal panic site
    // as an ordinary call whose continuation immediately returns.  Project it
    // through the shared semantic view before every path/panic consumer below;
    // validation intentionally runs on the source form first so malformed wire
    // input cannot be repaired by the projection.
    let tail_call_expanded = func.with_tail_calls_expanded();
    let func = tail_call_expanded.as_ref();
    // The same whole-function work gate the bidirectional lane uses; an
    // over-budget function emits no claims at all.
    if super::func_exceeds_vcgen_budget(func) {
        return Vec::new();
    }
    // Sanitize the shared function view exactly as the bidirectional lane does
    // at its own boundary, so an authored `requires` whose `Int` arithmetic is
    // not an exact model of the fixed-width Rust expression never becomes a
    // premise here.
    let arithmetic_safe_func = super::without_unmodeled_contract_arithmetic(func);
    let func = arithmetic_safe_func.as_ref();
    // `Ctx::build` REJECTS duplicate local indices and duplicate block ids, and
    // runs FIRST because everything below depends on both. A duplicate local
    // index makes `local_ty` / `param_var_name` ambiguous, and an ambiguous name
    // is a merged symbol — exactly the aliasing this lane must not have; a
    // duplicate block id breaks `acyclic_paths_to`'s visited-set reasoning.
    // Decline the whole function in either case.
    let Some(ctx) = Ctx::build(func) else {
        return Vec::new();
    };
    // CONTRACT CONSUMPTION — a false-refutation guard, not a nicety. Without the
    // declared `#[trust::requires]` conjoined, this lane freely picks inputs the
    // contract EXCLUDES and refutes a panic no admissible caller can reach:
    // `#[requires(n > 4)] fn f(n: u8) { while i < 4 { assert!(n != i); … } }`
    // would be "refuted" at `n == 0`. In THIS lane the argument is one-sided and
    // therefore simple: conjoining a premise can only SHRINK the model set, so
    // it can only drop refutations of contract-violating inputs — exactly the
    // intent — and a surviving model satisfies the contract as well as the path.
    //
    // BINDING IS CHECKED, NOT ASSUMED. Preconditions bind parameters by their
    // BARE debug name. If `param_var_name`'s injectivity fallback had to rename
    // any parameter to `_<index>`, the precondition would bind NOTHING and sit
    // silently inert — which is the false refutation above wearing a conjunct.
    // Decline the function instead.
    let safe_preconditions: Vec<Formula> = func
        .preconditions
        .iter()
        .filter(|pre| {
            !crate::contracts::formula_uses_unmodeled_machine_arithmetic_in_function(func, pre)
        })
        .cloned()
        .collect();
    if !func.preconditions.is_empty() {
        let every_param_binds =
            func.body.locals.iter().filter(|d| d.index >= 1 && d.index <= func.body.arg_count).all(
                |d| match d.name.as_deref() {
                    Some(name) => param_var_name(func, d.index) == name,
                    None => true,
                },
            );
        if !every_param_binds {
            return Vec::new();
        }
        // THE SAME GUARD, for the element symbols of a modeled `&[T; N]`
        // parameter. Those symbols are named `__trust_ppr_elem_*` — a spelling
        // no source-level contract can produce — so a declared
        // `#[trust::requires]` that constrains the ARRAY binds nothing here and
        // would sit inert while the lane freely picks element values the
        // contract excludes. That is precisely the false refutation the conjunct
        // above exists to prevent, so if any precondition so much as MENTIONS a
        // symbol spelled like a modeled array parameter, decline the function.
        // Conservative on purpose: a declined function costs completeness only.
        let mut precondition_symbols: Vec<String> = Vec::new();
        for pre in &func.preconditions {
            pre.visit(&mut |node| {
                if let Some(name) = node.var_name() {
                    precondition_symbols.push(name.to_string());
                }
            });
        }
        let mentions_a_modeled_array = func
            .body
            .locals
            .iter()
            .filter(|d| d.index >= 1 && d.index <= func.body.arg_count)
            .filter(|d| array_param_element_symbols(func, d.index).is_some())
            .any(|d| {
                let base = param_var_name(func, d.index);
                precondition_symbols.iter().any(|name| name.starts_with(&base))
            });
        if mentions_a_modeled_array {
            return Vec::new();
        }
    }
    let panic_blocks: Vec<&BasicBlock> =
        func.body.blocks.iter().filter(|b| is_assert_panic_block(b)).collect();
    if panic_blocks.is_empty() {
        return Vec::new();
    }

    let mut out = Vec::new();
    for block in panic_blocks {
        let Terminator::Call { func: callee, args, span, .. } = &block.terminator else {
            continue;
        };
        for path in acyclic_paths_to(&ctx, block.id) {
            let Some(mut formula) = execute_path(&ctx, &path) else {
                continue;
            };
            if !safe_preconditions.is_empty() {
                let mut conjuncts = safe_preconditions.clone();
                conjuncts.push(formula);
                formula = Formula::And(conjuncts);
            }
            let query = VerificationCondition {
                kind: VcKind::Assertion {
                    message: super::v2_panic_call_vc_message(func, callee, args),
                },
                function: func.name.clone().into(),
                location: span.clone(),
                formula,
                contract_metadata: None,
                obligation: None,
            };
            out.push(RefuteOnlyVc::new(
                query,
                RefuteOnlyProvenance::AcyclicPath { panic_block: block.id, blocks: path },
            ));
        }
    }
    out
}

/// [`generate_per_path_assert_refutation_vcs`] under an explicit function
/// policy, mirroring the bidirectional lane's context-carrying entry point.
#[must_use]
pub fn generate_per_path_assert_refutation_vcs_with_context(
    func: &VerifiableFunction,
    context: &crate::VcgenContext,
) -> Vec<RefuteOnlyVc> {
    crate::with_function_vcgen_context(&func.def_path, context, || {
        generate_per_path_assert_refutation_vcs(func)
    })
}

#[cfg(test)]
mod tests {
    use trust_types::fx::FxHashSet;
    use trust_types::{RefuteOnlyOutcome, Symbol, VerificationResult};

    use super::*;

    /// The REAL `-Ztrust-dump=mir` output of the gate fixture
    /// `tests/trust-falsification/mutant/pf_subsume_loop_assert_sibling.rs`,
    /// produced by the stage2 `trustc` (88b99d681). Using the compiler's own
    /// TrustIr — rather than a hand-built body that agrees with my reading of
    /// it — is what makes this a measurement of the fixture and not of a
    /// restatement.
    const LOOP_ASSERT_MIR: &str = include_str!("per_path_refute_fixture.json");

    /// The REAL `-Ztrust-dump=mir` output of the two `for &x in <&[u8; 4]>` gate
    /// mutants, produced by the stage2 `trustc` (716725c5e). Both functions
    /// panic on `f(&[200, 0, 0, 0])`; both were scored UNCAUGHT because the two
    /// iterator calls are opaque and every path through the loop was dropped.
    const FOREACH_ASSERT_MIR: &str = include_str!("per_path_refute_foreach_assert_fixture.json");
    const FOREACH_PANIC_MIR: &str = include_str!("per_path_refute_foreach_panic_fixture.json");

    /// The stage2 `trustc` TrustIr of a `for &x in <&[u8; 4]>` loop whose
    /// `assert!` is UNREACHABLE because the iteration is already `continue`d for
    /// the only value that could fail it:
    ///
    /// ```ignore
    /// for &x in a { if x == 200 { continue; } assert!(x != 200); t ^= x; }
    /// ```
    ///
    /// Compiler output rather than a hand-edited body, because the point of this
    /// fixture is the FALSE-REFUTATION direction: the lane must build the query
    /// (so the summary really is exercised) and must not refute it.
    const FOREACH_SAFE_MIR: &str = include_str!("per_path_refute_foreach_safe_fixture.json");

    fn loop_assert_fn() -> VerifiableFunction {
        serde_json::from_str(LOOP_ASSERT_MIR).expect("fixture MIR parses")
    }

    fn foreach_assert_fn() -> VerifiableFunction {
        serde_json::from_str(FOREACH_ASSERT_MIR).expect("fixture MIR parses")
    }

    fn foreach_panic_fn() -> VerifiableFunction {
        serde_json::from_str(FOREACH_PANIC_MIR).expect("fixture MIR parses")
    }

    /// The element symbol of `a[k]` for the `&[u8; 4]` parameter (local 1) of
    /// both `foreach` fixtures.
    fn foreach_elem(k: usize) -> String {
        format!("{}1_{k}", std_iter::ELEM_VAR_PREFIX)
    }

    /// Solve one refute-only query with the same in-process ay backend the
    /// compiler's refute lane uses.
    fn refute(vc: RefuteOnlyVc) -> RefuteOnlyOutcome {
        vc.refute_with(Symbol::intern("trust-perpath-refute"), |query| {
            trust_router::Router::deterministic_in_process_ay(5_000)
                .verify_all(std::slice::from_ref(query))
                .into_iter()
                .next()
                .map(|(_, r)| r)
        })
    }

    /// BASELINE: the bidirectional lane emits NOTHING for this function — the
    /// loop-carried `i` leaves the panic-path formula ungrounded, so the assert
    /// is skipped. This is the DECLINE the per-path lane exists to convert.
    #[test]
    fn bidirectional_lane_declines_the_loop_assert() {
        let func = loop_assert_fn();
        let vcs = crate::generate_full_assert_refutation_vcs(&func);
        assert!(
            vcs.is_empty(),
            "expected the bidirectional lane to emit no assert VC here; got {vcs:?}"
        );
    }

    /// The zero-iteration path `bb0 → bb1 → bb2 → bb4` is enumerated and
    /// symbolically executed.
    #[test]
    fn enumerates_the_zero_iteration_path_to_the_panic_block() {
        let func = loop_assert_fn();
        let vcs = generate_per_path_assert_refutation_vcs(&func);
        assert!(!vcs.is_empty(), "expected at least one per-path query");
        let paths: Vec<Vec<BlockId>> = vcs
            .iter()
            .map(|v| match v.provenance() {
                RefuteOnlyProvenance::AcyclicPath { blocks, .. } => blocks.clone(),
                #[allow(unreachable_patterns)]
                _ => Vec::new(),
            })
            .collect();
        assert!(
            paths.contains(&vec![BlockId(0), BlockId(1), BlockId(2), BlockId(4)]),
            "zero-iteration path missing; got {paths:?}"
        );
        // Every enumerated path is acyclic and ends at the panic block.
        for p in &paths {
            let mut seen = FxHashSet::default();
            assert!(p.iter().all(|b| seen.insert(*b)), "path repeats a block: {p:?}");
            assert_eq!(p.last(), Some(&BlockId(4)));
        }
    }

    /// THE MEASUREMENT: the per-path query is SAT, and the model is a real
    /// counterexample (`n ∈ 0..4`, and on the zero-iteration path `n == 0`).
    #[test]
    fn per_path_query_refutes_the_loop_assert_with_a_witness() {
        let func = loop_assert_fn();
        let vcs = generate_per_path_assert_refutation_vcs(&func);
        assert!(!vcs.is_empty());
        let mut refutations = 0;
        for vc in vcs {
            match refute(vc) {
                RefuteOnlyOutcome::Refuted { result, provenance, .. } => {
                    assert_eq!(provenance.panic_block(), BlockId(4));
                    let VerificationResult::Failed { counterexample, .. } = &result else {
                        panic!("a refutation must carry a Failed result");
                    };
                    // The witness must be a REAL input: on the zero-iteration
                    // path the only model is `n == 0`, and `f(0)` panics on the
                    // first iteration of the loop.
                    let model = counterexample.as_ref().expect("witness-backed refutation");
                    assert_eq!(
                        model.assignments,
                        vec![("n".to_string(), trust_types::CounterexampleValue::Int(0))],
                        "expected the concrete witness n = 0"
                    );
                    refutations += 1;
                }
                RefuteOnlyOutcome::NoRefutation => {}
            }
        }
        assert!(refutations > 0, "the per-path lane must refute this genuinely-buggy function");
    }

    /// SOUNDNESS (the direction that matters): the same machinery must NOT
    /// refute a loop whose assert genuinely holds on every path. `assert!(i < 4)`
    /// inside `while i < 4` is true at every iteration, so no acyclic path to
    /// the panic block is feasible and the lane must report nothing.
    #[test]
    fn does_not_refute_a_genuinely_safe_loop_assert() {
        // Same CFG as the fixture, with the assert condition changed from
        // `n != i` to `i < 4` — which the loop guard already establishes.
        let mut func = loop_assert_fn();
        for block in &mut func.body.blocks {
            if block.id != BlockId(2) {
                continue;
            }
            // `_6 = Lt(_7, 4)` instead of `_6 = Ne(_1, _7)`.
            for stmt in &mut block.stmts {
                if let Statement::Assign { place, rvalue, .. } = stmt
                    && place.local == 6
                {
                    *rvalue = Rvalue::BinaryOp(
                        BinOp::Lt,
                        Operand::Copy(Place::local(7)),
                        Operand::Constant(ConstValue::Uint(4, 8)),
                    );
                }
            }
        }
        let vcs = generate_per_path_assert_refutation_vcs(&func);
        assert!(!vcs.is_empty(), "the query must still be built; only its verdict changes");
        for vc in vcs {
            assert!(
                matches!(refute(vc), RefuteOnlyOutcome::NoRefutation),
                "a genuinely-safe assert must never be refuted"
            );
        }
    }

    /// An unmodeled construct on the path DROPS the path rather than leaving a
    /// read free. Replacing the loop-guard computation with an `Rvalue::Len`
    /// (which this lane does not model) must remove every query for the block
    /// that depends on it — not produce one with an unconstrained `_5`.
    #[test]
    fn unmodeled_rvalue_on_the_path_drops_the_path() {
        let mut func = loop_assert_fn();
        for block in &mut func.body.blocks {
            if block.id != BlockId(1) {
                continue;
            }
            for stmt in &mut block.stmts {
                if let Statement::Assign { place, rvalue, .. } = stmt
                    && place.local == 5
                {
                    *rvalue = Rvalue::Len(Place::local(3));
                }
            }
        }
        assert!(
            generate_per_path_assert_refutation_vcs(&func).is_empty(),
            "an unmodeled definition must drop the path, never free the variable"
        );
    }

    /// A read of a local with no value on this path drops the path. Deleting
    /// the `i = 0` initialisation makes `_5 = copy _3` a read of an
    /// unestablished local; the lane must decline rather than mint a free `i`
    /// (a free `i` would be an OVER-approximation, and SAT under it is a
    /// spurious witness — a false refutation).
    #[test]
    fn read_of_an_unestablished_local_drops_the_path() {
        let mut func = loop_assert_fn();
        for block in &mut func.body.blocks {
            if block.id == BlockId(0) {
                block
                    .stmts
                    .retain(|s| !matches!(s, Statement::Assign { place, .. } if place.local == 3));
            }
        }
        assert!(
            generate_per_path_assert_refutation_vcs(&func).is_empty(),
            "an unestablished read must drop the path"
        );
    }

    /// A `Call` on the way to the panic block is not traversed: the lane cannot
    /// reproduce a callee's effect, so it must not enumerate through one.
    #[test]
    fn calls_are_not_traversed() {
        let mut func = loop_assert_fn();
        for block in &mut func.body.blocks {
            if block.id == BlockId(0) {
                block.terminator = Terminator::Call {
                    func: "some::helper".into(),
                    args: Vec::new(),
                    dest: Place::local(9),
                    target: Some(BlockId(1)),
                    span: trust_types::SourceSpan::default(),
                    atomic: None,
                    is_foreign: false,
                    is_unsafe_sig: false,
                    callee_identity: None,
                    unwind: trust_types::UnwindEdge::default(),
                };
            }
        }
        assert!(
            generate_per_path_assert_refutation_vcs(&func).is_empty(),
            "a call edge must not be traversed"
        );
    }

    /// `unreachable!()` is intentional dead-code scaffolding, not a refutable
    /// assert — the same exclusion the bidirectional lane makes.
    #[test]
    fn unreachable_sentinel_is_not_a_refutable_panic() {
        let mut func = loop_assert_fn();
        for block in &mut func.body.blocks {
            if let Terminator::Call { args, .. } = &mut block.terminator {
                *args = vec![Operand::Constant(ConstValue::Str {
                    bytes: b"internal error: entered unreachable code".to_vec(),
                })];
            }
        }
        assert!(generate_per_path_assert_refutation_vcs(&func).is_empty());
    }

    /// A source MIR `TailCall` to the panic entry point retains the exact source
    /// span and is refuted just like the equivalent call-plus-return shape.
    #[test]
    fn tail_call_panic_is_a_refutable_terminal_site() {
        let mut func = loop_assert_fn();
        let panic = func
            .body
            .blocks
            .iter_mut()
            .find(|block| block.id == BlockId(4))
            .expect("fixture panic block");
        let Terminator::Call {
            func: callee,
            args,
            span,
            atomic,
            is_foreign,
            is_unsafe_sig,
            callee_identity,
            ..
        } = panic.terminator.clone()
        else {
            panic!("fixture panic block must be a call")
        };
        panic.terminator = Terminator::TailCall {
            func: callee,
            args,
            span: span.clone(),
            atomic,
            is_foreign,
            is_unsafe_sig,
            callee_identity,
        };

        let vcs = generate_per_path_assert_refutation_vcs(&func);
        assert!(!vcs.is_empty(), "tail-call panic must remain visible to the refute lane");
        assert!(vcs.iter().all(|vc| vc.location() == &span));
        assert!(vcs.into_iter().any(|vc| matches!(refute(vc), RefuteOnlyOutcome::Refuted { .. })));
    }

    /// The CONSUMER SHAPE, compiled and executed against the real APIs.
    ///
    /// This mirrors the hunk added to
    /// `rustc_mir_transform::trust_verify::refute_full_assert_obligations`
    /// statement for statement (only the compiler-local deadline/session helpers
    /// are elided), so the API contract that hunk relies on — `provenance()`,
    /// `location()`, `refute_with` with a router closure, and the two-arm match
    /// that is the ONLY way to get a row out — is exercised here even though the
    /// compiler crate itself needs a stage build to compile.
    #[test]
    fn consumer_shape_yields_only_failed_rows() {
        let func = loop_assert_fn();
        let mut results: Vec<(VerificationCondition, VerificationResult)> = Vec::new();
        let mut refuted_blocks: FxHashSet<BlockId> = FxHashSet::default();
        let context = crate::VcgenContext::for_function(func.def_path.clone());
        for candidate in generate_per_path_assert_refutation_vcs_with_context(&func, &context) {
            let block = candidate.provenance().panic_block();
            if refuted_blocks.contains(&block) {
                continue;
            }
            let _location = candidate.location().clone();
            let outcome = candidate.refute_with(Symbol::intern("trust-perpath-refute"), |query| {
                trust_router::Router::deterministic_in_process_ay(5_000)
                    .verify_all(std::slice::from_ref(query))
                    .into_iter()
                    .next()
                    .map(|(_, res)| res)
            });
            match outcome {
                RefuteOnlyOutcome::Refuted { vc, result, .. } => {
                    refuted_blocks.insert(block);
                    results.push((vc, result));
                }
                RefuteOnlyOutcome::NoRefutation => {}
            }
        }
        assert_eq!(results.len(), 1, "one refutation row for the one panic block");
        // The row the compiler folds into `summary.failed` — never anything else.
        assert!(results.iter().all(|(_, r)| matches!(r, VerificationResult::Failed { .. })));
        assert!(matches!(results[0].0.kind, VcKind::Assertion { .. }));
    }

    /// ADVERSARIAL CORPUS SCAN — the false-refutation check, over real bodies.
    ///
    /// Every fixture under `tests/trust-falsification/proved/` is a function the
    /// verifier MUST accept (exit 0), i.e. one with NO reachable panic. So a
    /// refutation from this lane on any of them is, by construction, a FALSE
    /// REFUTATION. This walks a directory of `-Ztrust-dump=mir` outputs, runs the
    /// per-path lane plus the in-process ay backend over every function it finds,
    /// and fails on the first refutation.
    ///
    /// `#[ignore]`d because it needs a corpus built by a stage2 `trustc`:
    ///
    /// ```text
    /// for f in tests/trust-falsification/proved/*.rs; do
    ///   d=corpus/$(basename "$f" .rs); mkdir -p "$d"
    ///   (cd "$d" && trustc --edition 2021 --crate-type lib --emit=metadata \
    ///       -Cpanic=abort -Ztrust-policy=certify -Ztrust-dump=mir:$(pwd) "$f")
    /// done
    /// TRUST_PERPATH_CORPUS=corpus cargo test -p trust-vcgen --lib \
    ///     perpath_corpus_never_refutes -- --ignored --nocapture
    /// ```
    #[test]
    #[ignore = "needs a -Ztrust-dump=mir corpus; set TRUST_PERPATH_CORPUS"]
    fn perpath_corpus_never_refutes_a_provable_function() {
        let root = std::env::var("TRUST_PERPATH_CORPUS")
            .expect("set TRUST_PERPATH_CORPUS to a directory of -Ztrust-dump=mir output");
        let mut files = Vec::new();
        collect_json(std::path::Path::new(&root), &mut files);
        assert!(!files.is_empty(), "no MIR dumps under {root}");
        let (mut funcs, mut queries, mut refutations) = (0usize, 0usize, Vec::new());
        for path in &files {
            let Ok(text) = std::fs::read_to_string(path) else { continue };
            let Ok(func) = serde_json::from_str::<VerifiableFunction>(&text) else { continue };
            funcs += 1;
            for vc in generate_per_path_assert_refutation_vcs(&func) {
                queries += 1;
                let where_ = format!("{} @ {:?}", func.name, vc.provenance());
                if let RefuteOnlyOutcome::Refuted { vc, .. } = refute(vc) {
                    refutations.push(format!("{where_}\n  formula={:?}", vc.formula));
                }
            }
        }
        eprintln!("[perpath-corpus] files={} functions={funcs} queries={queries}", files.len());
        assert!(
            refutations.is_empty(),
            "FALSE REFUTATION(S) on provable functions:\n{}",
            refutations.join("\n")
        );
    }

    fn collect_json(dir: &std::path::Path, out: &mut Vec<std::path::PathBuf>) {
        let Ok(entries) = std::fs::read_dir(dir) else { return };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                collect_json(&path, out);
            } else if path.extension().is_some_and(|e| e == "json") {
                out.push(path);
            }
        }
    }

    /// CONTRACT CONSUMPTION. A declared `#[trust::requires(n > 4)]` excludes
    /// every input that reaches this panic, so the lane must NOT refute — a
    /// refutation here would be a false refutation of a contract-honouring
    /// program. (Without the precondition conjunct the same body refutes at
    /// `n == 0`; see `per_path_query_refutes_the_loop_assert_with_a_witness`.)
    #[test]
    fn declared_precondition_blocks_the_refutation() {
        let mut func = loop_assert_fn();
        func.preconditions =
            vec![Formula::Gt(Box::new(Formula::var("n", Sort::Int)), Box::new(Formula::Int(4)))];
        let vcs = generate_per_path_assert_refutation_vcs(&func);
        assert!(!vcs.is_empty(), "the query is still built; the contract only shrinks its models");
        for vc in vcs {
            assert!(
                matches!(refute(vc), RefuteOnlyOutcome::NoRefutation),
                "a contract-excluded input must never be reported as a counterexample"
            );
        }
    }

    /// If the injectivity fallback renamed a parameter, a precondition spelled
    /// with the source name would bind NOTHING and sit inert — so the whole
    /// function is declined rather than refuted under a contract that is not
    /// actually being enforced.
    #[test]
    fn precondition_that_cannot_bind_declines_the_function() {
        let mut func = loop_assert_fn();
        // Force the collision fallback for `n` by giving another local the same
        // source name.
        for decl in &mut func.body.locals {
            if decl.index == 2 {
                decl.name = Some("n".into());
            }
        }
        func.preconditions =
            vec![Formula::Gt(Box::new(Formula::var("n", Sort::Int)), Box::new(Formula::Int(4)))];
        assert_eq!(param_var_name(&func, 1), "_1", "the fallback must have fired");
        assert!(
            generate_per_path_assert_refutation_vcs(&func).is_empty(),
            "an unbindable precondition must decline the function, not be ignored"
        );
    }

    /// Parameter naming must be injective: two parameters sharing a source name
    /// must not collapse onto one symbol.
    #[test]
    fn shared_parameter_names_fall_back_to_indices() {
        let mut func = loop_assert_fn();
        for decl in &mut func.body.locals {
            if decl.index == 1 || decl.index == 2 {
                decl.name = Some("x".into());
            }
        }
        assert_eq!(param_var_name(&func, 1), "_1");
        assert_eq!(param_var_name(&func, 2), "_2");
    }

    // ---------------------------------------------------------------------
    // `for &x in <&[T; N]>` — the slice-iterator value summary.
    // ---------------------------------------------------------------------

    /// Rewrite the callee string of the one `Call` terminator whose current
    /// callee contains `needle`. Used to probe the recognizer against the REAL
    /// fixture instead of against a hand-built body.
    fn retarget_callee(func: &mut VerifiableFunction, needle: &str, replacement: &str) {
        let mut hits = 0;
        for block in &mut func.body.blocks {
            if let Terminator::Call { func: callee, .. } = &mut block.terminator
                && callee.contains(needle)
            {
                *callee = replacement.to_string();
                hits += 1;
            }
        }
        assert_eq!(hits, 1, "expected exactly one `{needle}` call in the fixture");
    }

    /// Replace the declared type of one local.
    fn retype_local(func: &mut VerifiableFunction, index: usize, ty: Ty) {
        let mut hits = 0;
        for decl in &mut func.body.locals {
            if decl.index == index {
                decl.ty = ty.clone();
                hits += 1;
            }
        }
        assert_eq!(hits, 1);
    }

    /// The concrete model of a refutation, as `(symbol, value)` pairs.
    fn witness(outcome: &RefuteOnlyOutcome) -> Vec<(String, trust_types::CounterexampleValue)> {
        let RefuteOnlyOutcome::Refuted { result, .. } = outcome else {
            panic!("expected a refutation");
        };
        let VerificationResult::Failed { counterexample, .. } = result else {
            panic!("a refutation must carry a Failed result");
        };
        counterexample.as_ref().expect("witness-backed refutation").assignments.clone()
    }

    /// BASELINE, on the real fixture: the bidirectional lane emits nothing for
    /// the `foreach` mutants either, so the per-path lane is the only thing that
    /// can decide them.
    #[test]
    fn bidirectional_lane_declines_the_foreach_mutants() {
        for func in [foreach_assert_fn(), foreach_panic_fn()] {
            assert!(
                crate::generate_full_assert_refutation_vcs(&func).is_empty(),
                "the bidirectional lane must still decline {}",
                func.def_path
            );
        }
    }

    /// THE MEASUREMENT (`mutant/pf_subsume_foreach_assert.rs`). The only acyclic
    /// path to the panic block is the FIRST iteration
    /// `bb0 → bb1 → bb2 → bb3 → bb5 → bb8`, and its only model puts `200` in
    /// element 0 — i.e. exactly the documented witness `f(&[200, 0, 0, 0])`.
    #[test]
    fn refutes_the_foreach_assert_mutant_with_a_first_element_witness() {
        let func = foreach_assert_fn();
        let vcs = generate_per_path_assert_refutation_vcs(&func);
        assert_eq!(vcs.len(), 1, "one acyclic path reaches the panic block");
        let RefuteOnlyProvenance::AcyclicPath { panic_block, blocks } = vcs[0].provenance().clone()
        else {
            panic!("the per-path lane emits only acyclic-path provenance");
        };
        assert_eq!(panic_block, BlockId(8));
        assert_eq!(
            blocks,
            vec![BlockId(0), BlockId(1), BlockId(2), BlockId(3), BlockId(5), BlockId(8)],
            "the refuted path must be the FIRST loop iteration"
        );
        let model = witness(&refute(vcs.into_iter().next().expect("one query")));
        // The witness must pin the FIRST element — the one the first iteration
        // reads. A model naming a later element would not be an execution of
        // this path.
        assert!(
            model.contains(&(foreach_elem(0), trust_types::CounterexampleValue::Int(200))),
            "expected a[0] = 200 in the witness; got {model:?}"
        );
    }

    /// The same, for the explicit-`panic!()` spelling
    /// (`mutant/pf_subsume_foreach_panic.rs`), whose panic block is reached
    /// through the `otherwise` arm instead of a labelled one.
    #[test]
    fn refutes_the_foreach_panic_mutant_with_a_first_element_witness() {
        let func = foreach_panic_fn();
        let vcs = generate_per_path_assert_refutation_vcs(&func);
        assert_eq!(vcs.len(), 1);
        assert_eq!(vcs[0].provenance().panic_block(), BlockId(7));
        let model = witness(&refute(vcs.into_iter().next().expect("one query")));
        assert!(
            model.contains(&(foreach_elem(0), trust_types::CounterexampleValue::Int(200))),
            "expected a[0] = 200 in the witness; got {model:?}"
        );
    }

    /// SOUNDNESS, on REAL compiler output. The `assert!` in
    /// `if x == 200 { continue; } assert!(x != 200);` is unreachable: the guard
    /// already excluded the only failing value. The lane must still BUILD the
    /// query — proving the summary is exercised rather than the function being
    /// declined for some unrelated reason — and must then find it unsatisfiable.
    #[test]
    fn does_not_refute_a_guarded_foreach_assert() {
        let func: VerifiableFunction =
            serde_json::from_str(FOREACH_SAFE_MIR).expect("fixture MIR parses");
        let vcs = generate_per_path_assert_refutation_vcs(&func);
        assert!(!vcs.is_empty(), "the summary must have produced a query to refute");
        for vc in vcs {
            assert!(
                matches!(refute(vc), RefuteOnlyOutcome::NoRefutation),
                "an unreachable assert must never be refuted"
            );
        }
    }

    /// SOUNDNESS. The same machinery over the same loop must NOT refute an
    /// assert that genuinely holds. `assert!(x <= 255)` on a `u8` element is
    /// true in every execution, and it is true HERE only because the element
    /// symbol carries its type-range constraint — so this also pins that the
    /// range fact is actually emitted for array elements.
    #[test]
    fn does_not_refute_a_genuinely_safe_foreach_assert() {
        let mut func = foreach_assert_fn();
        for block in &mut func.body.blocks {
            if block.id != BlockId(5) {
                continue;
            }
            for stmt in &mut block.stmts {
                if let Statement::Assign { place, rvalue, .. } = stmt
                    && place.local == 9
                {
                    *rvalue = Rvalue::BinaryOp(
                        BinOp::Le,
                        Operand::Copy(Place::local(8)),
                        Operand::Constant(ConstValue::Uint(255, 8)),
                    );
                }
            }
        }
        let vcs = generate_per_path_assert_refutation_vcs(&func);
        assert_eq!(vcs.len(), 1, "the query is still built; only its verdict changes");
        for vc in vcs {
            assert!(
                matches!(refute(vc), RefuteOnlyOutcome::NoRefutation),
                "a genuinely-safe assert must never be refuted"
            );
        }
    }

    /// The summary is keyed on a CLOSED list of `core`/`std` trait paths. A user
    /// trait implemented on the slice iterator has arbitrary semantics, so its
    /// `next` must not be summarized — the whole function then goes back to
    /// being declined, exactly as before this lane existed.
    #[test]
    fn a_user_trait_next_is_not_summarized() {
        let mut func = foreach_assert_fn();
        retarget_callee(
            &mut func,
            "Iterator>::next",
            "<core::slice::iter::Iter<'_, u8> as my_crate::Advance>::next",
        );
        assert!(
            generate_per_path_assert_refutation_vcs(&func).is_empty(),
            "an unrecognized callee must drop every path through it"
        );
    }

    /// Likewise for the constructor hop: without a recognized `into_iter` there
    /// is no tracked iterator for `next` to advance, and the TYPE cross-check in
    /// `apply_std_iter_call` refuses rather than inventing one.
    #[test]
    fn a_user_into_iter_is_not_summarized() {
        let mut func = foreach_assert_fn();
        retarget_callee(
            &mut func,
            "IntoIterator>::into_iter",
            "<&[u8; 4] as my_crate::IntoIterator>::into_iter",
        );
        assert!(generate_per_path_assert_refutation_vcs(&func).is_empty());
    }

    /// THE STRING IS NOT THE GATE. Keeping the real `core` callee spelling but
    /// giving the destination a type that is NOT `Option<&u8>` must still drop
    /// the path: the summary is only applied when the call site's TrustIr types
    /// match the shape it describes.
    #[test]
    fn type_cross_check_rejects_a_mismatched_next_destination() {
        // A different element type in the `Some` payload.
        let mut func = foreach_assert_fn();
        let option_ref_u16 = Ty::Adt {
            name: "core::option::Option".into(),
            fields: Vec::new(),
            variants: vec![
                trust_types::VariantDef {
                    name: "None".into(),
                    discriminant: 0,
                    fields: Vec::new(),
                },
                trust_types::VariantDef {
                    name: "Some".into(),
                    discriminant: 1,
                    fields: vec![(
                        "0".into(),
                        Ty::Ref {
                            mutable: false,
                            inner: Box::new(Ty::Int { width: 16, signed: false }),
                        },
                    )],
                },
            ],
            disc_index_safe: false,
            faithful_enum_repr: None,
            layout: None,
            enum_layout: None,
            adt_kind: Some(trust_types::AdtKind::Enum),
            arbitrary_precision: None,
        };
        retype_local(&mut func, 5, option_ref_u16);
        assert!(
            generate_per_path_assert_refutation_vcs(&func).is_empty(),
            "a `next` whose declared return type is not `Option<&elem>` must drop"
        );

        // A destination that is not the slice iterator at all.
        let mut func = foreach_assert_fn();
        retype_local(&mut func, 3, Ty::Int { width: 8, signed: false });
        assert!(
            generate_per_path_assert_refutation_vcs(&func).is_empty(),
            "an `into_iter` whose declared return type is not `slice::Iter` must drop"
        );
    }

    /// `&mut [T; N]` is NOT symbolized: its elements are not fixed for the
    /// borrow, so element symbols would not be an exact model of the storage.
    #[test]
    fn mutable_array_parameter_is_not_symbolized() {
        let mut func = foreach_assert_fn();
        retype_local(
            &mut func,
            1,
            Ty::Ref {
                mutable: true,
                inner: Box::new(Ty::Array {
                    elem: Box::new(Ty::Int { width: 8, signed: false }),
                    len: 4,
                }),
            },
        );
        assert!(array_param_element_symbols(&func, 1).is_none());
        assert!(generate_per_path_assert_refutation_vcs(&func).is_empty());
    }

    /// The element symbols must never alias a source name. A local spelled
    /// exactly like one of them declines the whole parameter rather than
    /// merging two independent inputs onto one symbol.
    #[test]
    fn element_symbol_collision_declines_the_parameter() {
        let mut func = foreach_assert_fn();
        assert!(array_param_element_symbols(&func, 1).is_some(), "baseline: modeled");
        for decl in &mut func.body.locals {
            if decl.index == 2 {
                decl.name = Some(foreach_elem(2));
            }
        }
        assert!(
            array_param_element_symbols(&func, 1).is_none(),
            "a colliding source name must decline the parameter"
        );
        assert!(generate_per_path_assert_refutation_vcs(&func).is_empty());
    }

    /// CONTRACT CONSUMPTION for an array parameter. A `#[trust::requires]` that
    /// talks about `a` cannot bind the `__trust_ppr_elem_*` symbols, so it would
    /// sit inert while the lane picked element values the contract excludes.
    /// Decline instead — the false-refutation direction.
    #[test]
    fn a_precondition_mentioning_the_array_declines_the_function() {
        let mut func = foreach_assert_fn();
        // The fixture already carries a compiler-injected discriminant fact over
        // `_7`, which must NOT block anything.
        assert!(!func.preconditions.is_empty());
        assert_eq!(generate_per_path_assert_refutation_vcs(&func).len(), 1);
        func.preconditions
            .push(Formula::Gt(Box::new(Formula::var("a", Sort::Int)), Box::new(Formula::Int(0))));
        assert!(
            generate_per_path_assert_refutation_vcs(&func).is_empty(),
            "a contract over the array must decline, never be silently ignored"
        );
    }

    /// THE CONSUMER SHAPE over the foreach fixture, so the row the compiler
    /// would fold into `summary.failed` is produced by the SAME statements as
    /// `rustc_mir_transform::trust_verify::refute_full_assert_obligations`
    /// (only the session/deadline helpers are elided). Without this, the lane
    /// could be correct and still inert at the one seam that turns a refutation
    /// into a build error.
    #[test]
    fn consumer_shape_yields_a_failed_row_for_the_foreach_mutant() {
        for func in [foreach_assert_fn(), foreach_panic_fn()] {
            let mut results: Vec<(VerificationCondition, VerificationResult)> = Vec::new();
            let mut refuted_blocks: FxHashSet<BlockId> = FxHashSet::default();
            let context = crate::VcgenContext::for_function(func.def_path.clone());
            for candidate in generate_per_path_assert_refutation_vcs_with_context(&func, &context) {
                let block = candidate.provenance().panic_block();
                if refuted_blocks.contains(&block) {
                    continue;
                }
                let _location = candidate.location().clone();
                let outcome =
                    candidate.refute_with(Symbol::intern("trust-perpath-refute"), |query| {
                        trust_router::Router::deterministic_in_process_ay(5_000)
                            .verify_all(std::slice::from_ref(query))
                            .into_iter()
                            .next()
                            .map(|(_, res)| res)
                    });
                match outcome {
                    RefuteOnlyOutcome::Refuted { vc, result, .. } => {
                        refuted_blocks.insert(block);
                        results.push((vc, result));
                    }
                    RefuteOnlyOutcome::NoRefutation => {}
                }
            }
            assert_eq!(results.len(), 1, "one refutation row for {}", func.def_path);
            assert!(results.iter().all(|(_, r)| matches!(r, VerificationResult::Failed { .. })));
            assert!(matches!(results[0].0.kind, VcKind::Assertion { .. }));
        }
    }

    /// The refute-only CHANNEL is what bounds the assumption's blast radius, so
    /// pin it on the real fixture: a solver UNSAT on these queries must arrive as
    /// the payload-free `NoRefutation`, byte-identical to an `Unknown`. If this
    /// ever differed, the slice-iterator axiom would be one match arm away from
    /// licensing a proof.
    #[test]
    fn the_foreach_summary_cannot_produce_a_proof() {
        let vcs = generate_per_path_assert_refutation_vcs(&foreach_assert_fn());
        assert_eq!(vcs.len(), 1);
        let query = vcs.into_iter().next().expect("one query");
        let unsat = query.clone().refute_with(Symbol::intern("test"), |_| {
            Some(VerificationResult::Proved {
                solver: Symbol::intern("ay"),
                time_ms: 1,
                strength: trust_types::ProofStrength::smt_unsat_strict_checked(),
                proof_certificate: None,
                solver_warnings: None,
                native_proof_envelope: None,
            })
        });
        let unknown = query.refute_with(Symbol::intern("test"), |_| {
            Some(VerificationResult::Unknown {
                solver: Symbol::intern("ay"),
                time_ms: 1,
                reason: "incomplete".into(),
            })
        });
        assert!(matches!(unsat, RefuteOnlyOutcome::NoRefutation));
        assert_eq!(format!("{unsat:?}"), format!("{unknown:?}"));
    }
}
