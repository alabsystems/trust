//! TINV step 7, increment 7.4: the situated obligation POINTS of one body
//! (`docs/design/2026-10-04-type-invariant-tinv.md` §2 P4, §3 G5-G9/G13, §6 step 7).
//!
//! PURE ENUMERATION. [`obligation_points`] lists, for one candidate type `S` and one body,
//! every point at which `I(S)` is owed — E (establish), C (call), R (return), U (unwind),
//! M (move) and Drop — with the root it is owed on, how the root's terms are rendered
//! ([`SigmaSource`]) and the state it is checked in ([`TinvStateSpec`]). It builds no
//! formula, versions nothing and grants no authority: the rows are turned into VCs inside
//! the safety walk by step 7.5, and only Houdini's certify mint loop (7.6, with the kind
//! admitted by 7.7) can make one authority.
//!
//! THE WINDOW. A root is a canonical `S`-typed place ([`canonical`]). It is DIRTY between
//! a write that may break `I` and the next point that re-establishes it; the analysis is
//! a forward may-dirty dataflow over the NORMAL region (design P4 "window"):
//! * gen: a non-element write to a field of the root, a whole-root store that is not a
//!   clean transfer, a call destination from outside the inventory, a discriminant
//!   write, a `Deinit`, drop glue; and any of these into a place the root lies under;
//! * STICKY gen: a field-level `&mut`/`&raw` borrow, or a whole-root one that is not a
//!   pass-through. A write through such an alias has no finding of its own
//!   (`place_write::resolve_place` cuts hits at a reference), so the root stays dirty for
//!   the rest of every path through the borrow;
//! * pass-through: a whole-root reborrow whose ONLY use is one call argument is a C
//!   point, not a gen; the call gens only if the callee is outside the inventory;
//! * kill: an `S` aggregate into the root (E proves it), `root = move|copy q` with `q`
//!   clean, a call destination from an inventory callee (it owes R on `_0`), and the
//!   normal successor of an inventory call that received the root (it owes R and U on its
//!   parameter). A `None` callee identity never kills.
//!
//! C is owed at every call whose argument reaches `S` (TINV-4), and deliberately NOT at a
//! D2 field alias (`feed(&mut self.k)`, design P4-C "or an alias from D2"): a callee
//! holding `&mut self.k` cannot observe `S` while that borrow is live, and the borrow
//! makes the root sticky-dirty for the caller (TINV-9(g), docs/DECISION_QUEUE.md).
//!
//! Every root starts clean. A parameter root is clean by WHOLE-CRATE INDUCTION: every
//! caller proved C on it. Any other local has no obligation until it is assigned, and
//! every assignment is a gen, a kill or a clean transfer.
//!
//! The inductive arguments (entry cleanliness, the inventory kill, the pass-through
//! reborrow and the inventory U discharge) are sound only when every inventory body's
//! own E/C/R/U/M/Drop obligations are proved under the SAME surviving conjunct set; that
//! is Houdini's job (step 7.6), which derives the inventory from the bodies it checks.

use std::borrow::Cow;
use std::collections::{BTreeMap, BTreeSet, HashSet, VecDeque};

use trust_types::fx::{FxHashMap, FxHashSet};
use trust_types::{
    AggregateKind, BasicBlock, BlockId, CalleeIdentity, ConstValue, Formula, Operand, Place,
    PlaceWriteChannel, PlaceWrites, Projection, Rvalue, Sort, Statement, Terminator, Ty,
    TypeInvariantPoint, TypeInvariantSite, VerifiableBody, VerifiableFunction,
    VerificationCondition,
};

use super::unwind::{
    self, CrossCheckMismatch, ExactCallModels, UFailure, UPoint, URefusal, UState,
};
use super::{Sigma, TinvBodyFacts, TinvType};
use crate::local_defs;
use crate::place_write::{self, Reach, WriteFinding};

/// What one body's enumeration is asked about.
pub struct TinvInputs<'a> {
    /// The candidate type.
    pub ty: &'a TinvType,
    /// The callees whose bodies are checked in the same Houdini run. Only those may
    /// kill a window or discharge a U row (7.6 derives this set from its bodies, so no
    /// identity can be here whose own obligations were not checked).
    pub inventory: &'a HashSet<CalleeIdentity>,
    /// The step-1 nounwind exemptions ([`unwind::u_point`]).
    pub models: &'a dyn ExactCallModels,
    /// Whether dropping a value of this type may run a user `Drop` impl. Asked of the
    /// DROPPED or OWNING type, never of `S` alone; the fail-closed default is `|_| true`.
    pub may_run_user_drop: &'a dyn Fn(&Ty) -> bool,
}

/// The state a point's invariant is checked in.
#[derive(Debug, Clone)]
pub enum TinvStateSpec {
    /// The state at the point (before the statement or terminator).
    At,
    /// The unwind edge of a call: the pre-call state with every place the call may
    /// write havocked by the same summary its normal successor uses. `inventory_passed`
    /// are the roots passed to an inventory callee; they are discharged (no row), not
    /// havocked.
    UnwindCallHavoc { inventory_passed: Vec<Place> },
    /// The unwind edge of a plain drop: the dropped place havocked.
    UnwindDropHavoc(Place),
    /// The unwind edge of a drop-and-replace: the drop's havoc FIRST, then
    /// `place := rvalue`.
    UnwindDropAssign { place: Place, rvalue: Rvalue },
}

/// How a row renders the field terms of its root ([`sigma_of_root`],
/// [`sigma_of_operands`]).
#[derive(Debug, Clone)]
pub enum SigmaSource {
    /// The root place's own fields.
    Root,
    /// The operands of the `S` aggregate at an E point, in field order.
    AggregateOperands(Vec<Operand>),
}

/// One situated obligation.
#[derive(Debug, Clone)]
pub struct TinvPointRow {
    pub point: TypeInvariantPoint,
    /// A terminator row has `statement_index == stmts.len()`.
    pub site: TypeInvariantSite,
    /// The safety walk's row point: the statement index, or `usize::MAX` for a
    /// terminator row (the pre-terminator state).
    pub row_point: usize,
    /// A canonical `S`-typed place.
    pub root: Place,
    pub sigma_src: SigmaSource,
    pub state: TinvStateSpec,
    /// An `Assert` U row: the panic is taken exactly when `cond != expected`.
    pub failure: Option<(Operand, bool)>,
}

/// Why no certificate may be built for the type from this body. Every variant
/// withholds; none is a partial result.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TinvObligationRefusal {
    /// A terminator whose unwind point cannot be classified (Opaque, TailCall, unknown).
    U(URefusal),
    /// A write the classifier cannot attribute (`place_write::tinv_refusal`), or a MIR
    /// form this enumeration does not classify.
    Write(String),
    /// The rustc facts disagree with the model.
    CrossCheck(CrossCheckMismatch),
    /// A value reaching `S` in a shape other than `S`, `&S` or `&mut S` (TINV-9(d)): D3's
    /// type walk is the only thing that could admit it.
    RootShape { site: TypeInvariantSite, ty: Ty },
    /// A root whose identity is not fixed: a reference argument with no unique `Ref`
    /// definition, or a `*r` whose `r` is reassigned.
    UnresolvedRoot { site: TypeInvariantSite },
    /// Two types, two bodies or two conjuncts of one type (`ty#id`) claim one
    /// `def_path` or id; Houdini (7.6) refuses every type.
    DuplicateDefPath(String),
    /// Two Houdini bodies (7.6) claim one `CalleeIdentity`; every type is refused.
    DuplicateIdentity(CalleeIdentity),
    /// Houdini (7.6) reached a fixpoint for the type with no Establish row in any body:
    /// no construction of it was checked, so nothing established what it would assume.
    NoEstablishPoint,
    /// The walk was cut short (step budget, row cap, generation work meter).
    Truncated,
    /// The walk did not emit every requested row undegraded.
    Coverage { expected: usize, got: usize },
    /// The static VC-generation budget refuses the body, or the clock tripped during
    /// the walk (7.5).
    Budget,
    /// The 7.5 row shim could not carry the request: the body is a memory image or
    /// malformed, the request was walked twice or never, or a minted havoc spelling
    /// collides with a local name.
    Shim(String),
    /// Step 10.0: a type-invariant USE SET is visible in the active generation context,
    /// so a row of the induction could assume the invariant through a use-site fact;
    /// Houdini refuses every type (a runtime check, not a `debug_assert!`).
    UseSetVisible,
}

/// A point after an inventory call where `I(root)` may be assumed (design P6, consumed by
/// 7.5's post-call facts and step 10).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PostCall {
    pub call_block: BlockId,
    /// The call's normal target; it has exactly one predecessor over ALL edges.
    pub target: BlockId,
    pub root: Place,
    /// Step 10.6: whether `root` is a root the call RECEIVED (an argument) or the call's
    /// DESTINATION.
    pub kind: PostCallRoot,
}

/// Step 10.6: how a [`PostCall`] root relates to its call.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PostCallRoot {
    /// A root the call received through an argument: the inventory callee owes R and U on
    /// its parameter.
    Arg,
    /// The call's destination, a whole non-return local of type exactly `S`: the
    /// inventory callee owes R on its `_0` (the same fact the dataflow's destination KILL
    /// rests on).
    Dest,
}

// ---------------------------------------------------------------------------------------
// Field terms
// ---------------------------------------------------------------------------------------

fn is_integer(ty: &Ty) -> bool {
    matches!(ty, Ty::Int { .. } | Ty::PtrSizedInt { .. })
}

/// The Value term of a field: only an INTEGER field has one. A `bool`, a `char`, a
/// collection or a reference renders to some symbol too, but not one a G16 Int template
/// may read as the field's value, so it is refused here rather than mis-sorted later.
fn value_term(func: &VerifiableFunction, op: &Operand, ty: Option<&Ty>) -> Option<Formula> {
    ty.filter(|t| is_integer(t)).map(|_| crate::operand_to_formula(func, op))
}

fn value_term_place(func: &VerifiableFunction, place: &Place, ty: Option<&Ty>) -> Option<Formula> {
    ty.filter(|t| is_integer(t))
        .map(|_| Formula::var(&crate::place_to_var_name(func, place), Sort::Int))
}

/// The Len term of a field place: a `Vec` (`Ty::Seq`) is its own Int-sorted name, a
/// `&[T]`/`&str` its `__slice_len` twin. No other type has one, and neither does an
/// unresolved type.
fn len_term(func: &VerifiableFunction, place: &Place, ty: Option<&Ty>) -> Option<Formula> {
    match ty? {
        Ty::Seq { .. } => Some(crate::guards::coll_len_var_place(func, place)),
        Ty::Ref { inner, .. } if matches!(inner.as_ref(), Ty::Slice { .. } | Ty::Str) => {
            let mut name = crate::place_to_var_name(func, place);
            name.push_str(crate::generate::SLICE_LEN_SUFFIX);
            Some(Formula::var_owned(name, Sort::Int))
        }
        _ => None,
    }
}

/// The `(Value, Len)` terms of one field place, as [`sigma_of_root`] renders them. The
/// 7.5 shim reads it for the replacement value of a drop-and-replace.
pub(crate) fn field_terms(
    func: &VerifiableFunction,
    place: &Place,
) -> (Option<Formula>, Option<Formula>) {
    let ty = crate::place_ty_cow(func, place);
    (
        value_term_place(func, place, ty.as_deref()),
        len_term(func, place, ty.as_deref()),
    )
}

/// The field terms of `root`, in the UNVERSIONED spelling the walk's reads mint
/// (`self*.1`). Shared with step 10, which instantiates the certified conjuncts with the
/// same terms.
pub(crate) fn sigma_of_root(func: &VerifiableFunction, ty: &TinvType, root: &Place) -> Sigma {
    let mut sigma = Sigma {
        value: Vec::with_capacity(ty.fields.len()),
        len: Vec::with_capacity(ty.fields.len()),
    };
    let root_ty = crate::place_ty_cow(func, root);
    let mut place = root.clone();
    for i in 0..ty.fields.len() {
        let proj = Projection::Field(i);
        let field_ty = root_ty
            .as_deref()
            .and_then(|rt| crate::place_ty_step(&func.body.datatype_defs, Cow::Borrowed(rt), &proj, &mut None));
        place.projections.push(proj);
        sigma.value.push(value_term_place(func, &place, field_ty.as_deref()));
        sigma.len.push(len_term(func, &place, field_ty.as_deref()));
        place.projections.pop();
    }
    sigma
}

/// The field terms of an `S` aggregate's operands (MIR lists a struct aggregate's
/// operands in field order). An operand count that differs from the field count gives no
/// term at all.
pub(crate) fn sigma_of_operands(
    func: &VerifiableFunction,
    ty: &TinvType,
    ops: &[Operand],
) -> Sigma {
    let n = ty.fields.len();
    if ops.len() != n {
        return Sigma { value: vec![None; n], len: vec![None; n] };
    }
    let mut sigma = Sigma { value: Vec::with_capacity(n), len: Vec::with_capacity(n) };
    for (op, (_, declared)) in ops.iter().zip(&ty.fields) {
        let (value, len) = match op {
            Operand::Copy(p) | Operand::Move(p) => {
                let t = crate::place_ty_cow(func, p);
                (value_term(func, op, t.as_deref()), len_term(func, p, t.as_deref()))
            }
            Operand::Constant(_) => (value_term(func, op, Some(declared)), None),
            _ => (None, None),
        };
        sigma.value.push(value);
        sigma.len.push(len);
    }
    sigma
}

// ---------------------------------------------------------------------------------------
// Roots
// ---------------------------------------------------------------------------------------

fn is_s(ty: &Ty, name: &str) -> bool {
    matches!(ty, Ty::Adt { name: n, .. } | Ty::Datatype { name: n, .. } if n == name)
}

fn type_of(func: &VerifiableFunction, place: &Place) -> Ty {
    crate::place_ty_cow(func, place)
        .map(Cow::into_owned)
        .or_else(|| crate::local_ty_ref(func, place.local).cloned())
        .unwrap_or(Ty::Unit)
}

/// Whether `place` may hold a value of `S` (or a reference to one): its type reaches `S`,
/// or does not resolve while its local's type does not provably avoid `S`.
fn may_hold_s(
    func: &VerifiableFunction,
    place: &Place,
    name: &str,
    opaque: place_write::OpaqueReach,
) -> bool {
    let defs = &func.body.datatype_defs;
    let reaches = |t: &Ty| place_write::type_reaches_with(t, name, defs, opaque) != Reach::No;
    match crate::place_ty_cow(func, place) {
        Some(ty) => reaches(&ty),
        None => crate::local_ty_ref(func, place.local).is_none_or(reaches),
    }
}

const CANONICAL_DEPTH: usize = 16;

fn is_always_scalar_constant(c: &ConstValue) -> bool {
    matches!(
        c,
        ConstValue::Bool(_)
            | ConstValue::Int(_)
            | ConstValue::Uint(..)
            | ConstValue::Float(_)
            | ConstValue::FloatBits { .. }
            | ConstValue::Unit
            | ConstValue::Str { .. }
            | ConstValue::OpaqueScalar { .. }
            | ConstValue::ConstParam { .. }
            | ConstValue::UnitVariantRef { .. }
            // Trust (EMPTY-CLOSURE-REF-VALUE-1): a reference to an upvar-free
            // closure, a ZST, holds no `S`, like a payload-free variant.
            | ConstValue::EmptyClosureRef { .. }
            | ConstValue::CallableItem { .. }
    )
}

fn body_has_non_scalar_constant(body: &VerifiableBody) -> bool {
    let non_scalar = |op: &Operand| matches!(op, Operand::Constant(c) if !is_always_scalar_constant(c));
    for block in &body.blocks {
        for stmt in &block.stmts {
            let Statement::Assign { rvalue, .. } = stmt else { continue };
            let hit = match rvalue {
                Rvalue::Use(op) | Rvalue::Cast(op, _) | Rvalue::Repeat(op, _) => non_scalar(op),
                Rvalue::Aggregate(_, ops) | Rvalue::Unsupported { operands: ops, .. } => {
                    ops.iter().any(non_scalar)
                }
                _ => false,
            };
            if hit {
                return true;
            }
        }
        if block.terminator.call_args().is_some_and(|args| args.iter().any(non_scalar)) {
            return true;
        }
    }
    false
}

/// Whether constant `c` may hold an `S` value, given the type of the position it is
/// used at (`ctx`, when known).
///
/// Optimized MIR folds a struct literal into a constant (`GVN` + `SingleUseConsts`:
/// `use_s(const S { k: -1 })`), which no aggregate, so no E row, ever constructs, and
/// which has no `const` body of its own to owe one (adversarial review, 2026-10-05).
/// Scalars, strings, fn items and payload-free variants hold no `S`; a typed memory image
/// or a scalar-field struct constant is judged by its type or ADT name; an opaque
/// constant is judged by its position's type, and refuses where that is unknown.
fn constant_may_hold_s(
    c: &ConstValue,
    ctx: Option<&Ty>,
    name: &str,
    defs: &trust_types::DatatypeDefs,
) -> bool {
    if is_always_scalar_constant(c) {
        return false;
    }
    match c {
        ConstValue::StructScalarFieldsRef { adt_name, fields, .. } => {
            adt_name == name || fields.iter().any(|f| constant_may_hold_s(f, None, name, defs))
        }
        ConstValue::MemoryImage(image) => {
            place_write::type_reaches(&image.ty, name, defs) != Reach::No
        }
        ConstValue::OpaqueConst(_) => {
            ctx.is_none_or(|t| place_write::type_reaches(t, name, defs) != Reach::No)
        }
        _ => true,
    }
}

/// The first site where a constant that may hold an `S` value is used as a value: an
/// assignment's operand (typed by its destination, or by the aggregate field it fills)
/// or a call argument (untyped here).
///
/// Decision TINV-32: with `constants_clear` (the census proved no constant of the body
/// can hold `S`), a constant is cleared unless the extraction itself says its position or
/// its memory image's type reaches `S` (`Reach::Yes`: a contradiction of the evidence).
fn s_reaching_constant(
    func: &VerifiableFunction,
    name: &str,
    constants_clear: bool,
) -> Option<TypeInvariantSite> {
    let defs = &func.body.datatype_defs;
    let definitely = |t: &Ty| place_write::type_reaches(t, name, defs) == Reach::Yes;
    // `clear`: the evidence applies at this operand (not an `OpaqueConst` that is a whole
    // assignment rvalue, which the extractor may have invented: candidate.rs).
    let constant_may_hold_s = |c: &ConstValue, ctx: Option<&Ty>, name: &str, defs, clear: bool| {
        constant_may_hold_s(c, ctx, name, defs)
            && !(clear
                && !ctx.is_some_and(definitely)
                && !matches!(c, ConstValue::MemoryImage(image) if definitely(&image.ty))
                && !super::candidate::names_s(c, name))
    };
    fn konst(op: &Operand) -> Option<&ConstValue> {
        match op {
            Operand::Constant(c) if !is_always_scalar_constant(c) => Some(c),
            _ => None,
        }
    }
    for block in &func.body.blocks {
        for (k, stmt) in block.stmts.iter().enumerate() {
            let Statement::Assign { place, rvalue, .. } = stmt else { continue };
            let clear = constants_clear && !super::candidate::may_be_invented_opaque(stmt);
            let hit = match rvalue {
                Rvalue::Use(op) | Rvalue::Cast(op, _) | Rvalue::Repeat(op, _) => {
                    konst(op).is_some_and(|c| {
                        let dest_ty = crate::place_ty_cow(func, place);
                        constant_may_hold_s(c, dest_ty.as_deref(), name, defs, clear)
                    })
                }
                Rvalue::Aggregate(kind, ops) => {
                    let mut base_ty: Option<Option<Cow<'_, Ty>>> = None;
                    ops.iter().enumerate().any(|(i, op)| {
                        konst(op).is_some_and(|c| {
                            let field_ty = match kind {
                                AggregateKind::Adt { .. } | AggregateKind::Tuple => base_ty
                                    .get_or_insert_with(|| crate::place_ty_cow(func, place))
                                    .as_deref()
                                    .and_then(|bt| {
                                        crate::place_ty_step(
                                            &func.body.datatype_defs,
                                            Cow::Borrowed(bt),
                                            &Projection::Field(i),
                                            &mut None,
                                        )
                                    }),
                                _ => None,
                            };
                            constant_may_hold_s(c, field_ty.as_deref(), name, defs, clear)
                        })
                    })
                }
                Rvalue::Unsupported { operands, .. } => operands.iter().any(|op| {
                    konst(op).is_some_and(|c| constant_may_hold_s(c, None, name, defs, clear))
                }),
                _ => false,
            };
            if hit {
                return Some(site(block.id, k));
            }
        }
        if let Some(args) = block.terminator.call_args()
            && args.iter().any(|op| {
                konst(op).is_some_and(|c| constant_may_hold_s(c, None, name, defs, constants_clear))
            })
        {
            return Some(site(block.id, block.stmts.len()));
        }
    }
    None
}

/// The canonical identity of a place: `*r` where `r` has a unique `Rvalue::Ref` def
/// `&q` / `&mut q` (`local_defs::unique_value_def`, which refuses parameters, call
/// destinations, partial writes and aliases) becomes `q`, transitively. A write through
/// a reborrow local then dirties the root it aliases.
///
/// FIXED IDENTITY (fail-closed, beyond the plan's text). A `*r` that stays is a root only
/// if `r` holds ONE value for the whole body: an unreassigned parameter, one call
/// destination or one plain definition, with no partial or unlocatable write and no
/// mutable alias of `r`'s OWN storage. Otherwise `*r` names different places at
/// different points — `r = move a; (*r).k = 9; r = move b` would check R on `*b` while
/// the caller's `*a` is the one written — so the root is `UnresolvedRoot`. The question
/// is `local_defs::is_single_static_assignment_modulo_pointee_borrows`: a borrow reached
/// THROUGH `r` (`&mut (*r).k`, the reborrow `&mut *r`) changes the pointee, never which
/// place `r` names, and the pointee's writes are this module's window, not `r`'s
/// identity.
///
/// A `Deref` anywhere but first (a reference stored in a field or a tuple), and an
/// `Index`/`Subslice` (an element chosen by a runtime value, so one spelling names
/// several places), are `RootShape`: only D3's type walk could admit them.
fn canonical(
    func: &VerifiableFunction,
    place: &Place,
    site: TypeInvariantSite,
) -> Result<Place, TinvObligationRefusal> {
    let mut at = place.clone();
    for _ in 0..CANONICAL_DEPTH {
        // A Box-elaborated raw temp (`_t = (<box>.0.0) as *const S`) is a fresh local per
        // deref site, never linked to the box place, so drop or move of the box would miss
        // the dirt written through it (adversarial review, 2026-10-05). v1 refuses an `S`
        // owned through a `Box`.
        if at.projections.first() == Some(&Projection::Deref)
            && place_write::box_temp_source(func, at.local).is_some()
        {
            return Err(TinvObligationRefusal::RootShape { site, ty: type_of(func, &at) });
        }
        if at.projections.first() == Some(&Projection::Deref) {
            if let Some(Rvalue::Ref { place: q, .. }) = local_defs::unique_value_def(func, at.local)
            {
                let mut next = q.clone();
                next.projections.extend(at.projections[1..].iter().cloned());
                at = next;
                continue;
            }
            if !local_defs::is_single_static_assignment_modulo_pointee_borrows(func, at.local) {
                return Err(TinvObligationRefusal::UnresolvedRoot { site });
            }
        }
        let ambiguous = at.projections.iter().enumerate().any(|(i, p)| match p {
            Projection::Deref => i > 0,
            Projection::Index(_) | Projection::Subslice { .. } => true,
            _ => false,
        });
        if ambiguous {
            return Err(TinvObligationRefusal::RootShape { site, ty: type_of(func, &at) });
        }
        return Ok(at);
    }
    Err(TinvObligationRefusal::UnresolvedRoot { site })
}

/// TINV-21 (adversarial review of `fd530b0a54`, 2026-10-06): the identity of a lemma
/// root `*p`, through the SAME gate every TINV root passes ([`canonical`]): `Some(*p)` only
/// when `root` is exactly `*p` for a parameter `p` that is never written
/// (`local_defs::is_single_static_assignment_modulo_pointee_borrows`), else `None` (an
/// `UnresolvedRoot`, a `RootShape`, or a root that is not a parameter's pointee). A lemma
/// proved of `*p` at `Return` is instantiated at the caller's argument for `p`, so `p` must
/// name that argument's pointee for the whole body: `fn g(mut s: &S, t: &S) { s = t; .. }`
/// would otherwise prove `φ(*t)` under `*s`'s name.
pub(crate) fn lemma_param_root(func: &VerifiableFunction, root: &Place) -> Option<Place> {
    if root.projections != [Projection::Deref] || !local_defs::is_parameter(func, root.local) {
        return None;
    }
    // Backstop (2026-10-06, re-review of `bf5f1dc8b5`), fail-closed: the POINTER stays in
    // place too. `local_defs::pointer_is_pinned` (one value, no alias of `p`'s own
    // storage, no partial or unlocatable write) and no escape of `p` or a mutable/raw
    // child of `*p` (`generate::local_pointee_may_escape`: no copy or move of `p`, no
    // `&mut`/`&raw` borrow below it, no drop of it). A moved or copied `p`
    // (`let q = p; q.i = ..`) writes `*p` under another name; the walk's
    // `deref_store_is_opaque` bumps `p*`'s versions there (measured), and this gate does
    // not rely on it. The `Freeze`/pointer-free pointee conditions of the shared-reborrow
    // lane are NOT required here: the lemma reads only `σ(*p)`'s integer and length terms.
    if !local_defs::pointer_is_pinned(func, root.local)
        || crate::generate::local_pointee_may_escape(func, root.local)
    {
        return None;
    }
    canonical(func, root, site(BlockId(0), 0)).ok().filter(|c| c == root)
}

/// How a call argument hands a root to the callee.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Shape {
    ByValue,
    SharedRef,
    MutRef,
}

/// The root a call argument hands over, if its type reaches `S` (design P4-C, TINV-4).
/// * `S` by value: the argument place;
/// * `&S`/`&mut S`: `*_p` for a parameter passed directly, otherwise the unique `Ref`
///   definition followed transitively; none is `UnresolvedRoot`;
/// * any other reaching shape (`&&S`, `Option<&mut S>`, `&mut Vec<S>`, a tuple, a
///   closure, `Box<S>`, a struct with an `S` field) is `RootShape`.
///
/// A constant argument has no place, and an `S` constant's value was established by its
/// own `const` body (an inventory body, P1). An argument the extractor could not
/// represent refuses.
fn call_arg_root(
    func: &VerifiableFunction,
    name: &str,
    arg: &Operand,
    site: TypeInvariantSite,
    opaque: place_write::OpaqueReach,
) -> Result<Option<(Place, Shape)>, TinvObligationRefusal> {
    let p = match arg {
        Operand::Copy(p) | Operand::Move(p) => p,
        Operand::Constant(_) => return Ok(None),
        _ => {
            return Err(TinvObligationRefusal::Write(format!(
                "a call argument the extractor could not represent at {site}"
            )));
        }
    };
    let defs = &func.body.datatype_defs;
    let Some(ty) = crate::place_ty_cow(func, p) else {
        return if may_hold_s(func, p, name, opaque) {
            Err(TinvObligationRefusal::UnresolvedRoot { site })
        } else {
            Ok(None)
        };
    };
    match place_write::type_reaches_with(&ty, name, defs, opaque) {
        Reach::No => return Ok(None),
        Reach::Unknown => {
            return Err(TinvObligationRefusal::RootShape { site, ty: ty.into_owned() });
        }
        Reach::Yes => {}
    }
    if is_s(&ty, name) {
        return Ok(Some((canonical(func, p, site)?, Shape::ByValue)));
    }
    if let Ty::Ref { mutable, inner } = ty.as_ref()
        && is_s(inner, name)
    {
        let shape = if *mutable { Shape::MutRef } else { Shape::SharedRef };
        if p.projections.is_empty() {
            if local_defs::is_parameter(func, p.local) {
                let pointee = Place { local: p.local, projections: vec![Projection::Deref] };
                return Ok(Some((canonical(func, &pointee, site)?, shape)));
            }
            if let Some(Rvalue::Ref { place: q, .. }) = local_defs::unique_value_def(func, p.local)
            {
                return Ok(Some((canonical(func, q, site)?, shape)));
            }
        }
        return Err(TinvObligationRefusal::UnresolvedRoot { site });
    }
    Err(TinvObligationRefusal::RootShape { site, ty: ty.into_owned() })
}

/// Whether the whole-root borrow assigned to `dest` is a PASS-THROUGH: `dest` is a whole
/// local with a unique `Ref` definition, mentioned exactly twice in the body (that
/// definition and one call argument, counted by `place_write::mention_count`, which
/// counts every statement or terminator it cannot list operands for as a mention).
fn borrow_is_pass_through(func: &VerifiableFunction, dest: &Place) -> bool {
    if !dest.projections.is_empty()
        || local_defs::is_parameter(func, dest.local)
        || {
            let tp = crate::generate::terminator_presence_for(func);
            !tp.has_call && !tp.has_tail_call
        }
        || !matches!(local_defs::unique_value_def(func, dest.local), Some(Rvalue::Ref { .. }))
    {
        return false;
    }
    let target_local = dest.local;
    let as_argument = func
        .body
        .blocks
        .iter()
        .filter_map(|b| b.terminator.call_args())
        .flatten()
        .filter(|a| {
            matches!(
                a,
                Operand::Copy(p) | Operand::Move(p)
                    if p.local == target_local && p.projections.is_empty()
            )
        })
        .take(2)
        .count();
    as_argument == 1 && place_write::has_mention_count(func, target_local, 2)
}

fn finding_site(f: &WriteFinding) -> TypeInvariantSite {
    match f {
        WriteFinding::Field { site, .. }
        | WriteFinding::WholeValue { site, .. }
        | WriteFinding::Unresolved { site, .. }
        | WriteFinding::Unlocatable { site, .. }
        | WriteFinding::UnsupportedOperand { site, .. }
        | WriteFinding::CallArg { site, .. } => *site,
    }
}

fn site(block: BlockId, statement_index: usize) -> TypeInvariantSite {
    TypeInvariantSite { block: block.0, statement_index }
}

// ---------------------------------------------------------------------------------------
// The window
// ---------------------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Dirt {
    Dirty,
    Sticky,
}

/// Root index -> dirtiness; a clean root is absent.
type State = BTreeMap<usize, Dirt>;

#[derive(Debug, Clone, Copy)]
enum Effect {
    Gen(usize),
    Sticky(usize),
    Kill(usize),
    /// `dest = move|copy src`: clean iff `src` is clean (`None`: not a root, so never
    /// dirty).
    Transfer {
        dest: usize,
        src: Option<usize>,
    },
}

fn apply(state: &mut State, effect: Effect) {
    let sticky = |s: &State, r: usize| s.get(&r) == Some(&Dirt::Sticky);
    match effect {
        Effect::Gen(r) => {
            state.entry(r).or_insert(Dirt::Dirty);
        }
        Effect::Sticky(r) => {
            state.insert(r, Dirt::Sticky);
        }
        Effect::Kill(r) => {
            if !sticky(state, r) {
                state.remove(&r);
            }
        }
        Effect::Transfer { dest, src } => {
            if !sticky(state, dest) {
                if src.is_some_and(|s| state.contains_key(&s)) {
                    state.insert(dest, Dirt::Dirty);
                } else {
                    state.remove(&dest);
                }
            }
        }
    }
}

/// The effect of a write by `channel` on a root it reaches through a field or a parent.
/// Wildcard-free over [`PlaceWriteChannel`].
fn partial_write_effect(channel: PlaceWriteChannel, r: usize) -> Effect {
    match channel {
        PlaceWriteChannel::Store
        | PlaceWriteChannel::SetDiscriminant
        | PlaceWriteChannel::Deinit
        | PlaceWriteChannel::CallDest
        | PlaceWriteChannel::TailCallReturn
        | PlaceWriteChannel::DropGlue => Effect::Gen(r),
        PlaceWriteChannel::MutBorrow | PlaceWriteChannel::RawBorrow { .. } => Effect::Sticky(r),
    }
}

struct Received {
    root: usize,
    shape: Shape,
}

struct CallInfo {
    /// The callee identity is present and in the inventory.
    inventory: bool,
    received: Vec<Received>,
}

struct Analysis<'f> {
    func: &'f VerifiableFunction,
    name: &'f str,
    /// Decision TINV-33 evidence for `name` ([`place_write::OpaqueReach`]).
    opaque: place_write::OpaqueReach,
    inp: &'f TinvInputs<'f>,
    roots: Vec<Place>,
    root_index: FxHashMap<Place, usize>,
    call_results: &'f FxHashSet<usize>,
    stmt_effects: FxHashMap<(usize, usize), Vec<Effect>>,
    term_effects: FxHashMap<usize, Vec<Effect>>,
    /// Roots a terminator may dirty before its unwind edge is taken (a non-inventory
    /// callee's `&mut` root, drop glue's place).
    unwind_gen: FxHashMap<usize, Vec<usize>>,
    calls: FxHashMap<usize, CallInfo>,
}

impl<'f> Analysis<'f> {
    fn intern(&mut self, p: Place) -> usize {
        if let Some(&i) = self.root_index.get(&p) {
            return i;
        }
        let i = self.roots.len();
        self.root_index.insert(p.clone(), i);
        self.roots.push(p);
        i
    }

    /// The design's ESCAPING roots: any `Deref` (a pointee the caller can see), a
    /// parameter, or a call result (MutexGuard, RefMut, IndexMut).
    fn escaping(&self, r: usize) -> bool {
        let p = &self.roots[r];
        p.projections.contains(&Projection::Deref)
            || local_defs::is_parameter(self.func, p.local)
            || self.call_results.contains(&p.local)
    }

    /// The design's owner-type U rule: a non-escaping root owes U when the drop glue of
    /// its OWNING local may run user code, which would observe the root mid-window during
    /// cleanup (rail 8 on the unwind path). Asked of the local's type, never of `S`.
    fn owner_may_run_user_drop(&self, r: usize) -> bool {
        crate::local_ty_ref(self.func, self.roots[r].local)
            .is_none_or(|t| (self.inp.may_run_user_drop)(t))
    }

    /// Every root that is `place` or lies under it in OWNED storage. A root reached from
    /// `place` through a `Deref` is a pointee, not part of `place`'s value: moving or
    /// reassigning a reference neither moves nor writes the `S` it points at (passing it
    /// is a C point, and storing it elsewhere is D2/D3's census).
    fn roots_under<'a>(&'a self, place: &'a Place) -> impl Iterator<Item = usize> + 'a {
        (0..self.roots.len()).filter(move |&r| {
            let root = &self.roots[r];
            unwind::is_within(root, place)
                && !root.projections[place.projections.len()..].contains(&Projection::Deref)
        })
    }

    /// The effects on roots strictly under a written place that is not itself `S`
    /// (`o = Owner(..)`, `_2 = call()` returning a struct with an `S` field). The
    /// whole-root and in-root cases come from the classifier's findings.
    fn parent_effects(
        &self,
        place: &Place,
        channel: PlaceWriteChannel,
        at: TypeInvariantSite,
        out: &mut Vec<Effect>,
    ) -> Result<Vec<usize>, TinvObligationRefusal> {
        let mut genned = Vec::new();
        // PERF-COMPILER-VCGEN-701: resolve `place_ty_cow(self.func, place)` once and
        // reuse it across both the `may_hold_s` check and the `is_s` exclusion.
        let defs = &self.func.body.datatype_defs;
        let reaches = |t: &Ty| place_write::type_reaches_with(t, self.name, defs, self.opaque) != Reach::No;
        let place_ty = crate::place_ty_cow(self.func, place);
        let holds_s = match &place_ty {
            Some(ty) => reaches(ty),
            None => crate::local_ty_ref(self.func, place.local).is_none_or(reaches),
        };
        if !holds_s || place_ty.as_deref().is_some_and(|t| is_s(t, self.name)) {
            return Ok(genned);
        }
        let cp = canonical(self.func, place, at)?;
        for r in self.roots_under(&cp) {
            if self.roots[r] != cp {
                let e = partial_write_effect(channel, r);
                if let Effect::Gen(r) = e {
                    genned.push(r);
                }
                out.push(e);
            }
        }
        Ok(genned)
    }
}

/// The CFG predecessor count of every block over ALL edges (normal and cleanup), as
/// `unwind::replace_assign` counts them.
fn predecessor_counts(body: &VerifiableBody) -> FxHashMap<BlockId, usize> {
    let mut preds: FxHashMap<BlockId, usize> =
        FxHashMap::with_capacity_and_hasher(body.blocks.len(), Default::default());
    for block in &body.blocks {
        unwind::for_each_all_successor(&block.terminator, |succ| {
            *preds.entry(succ).or_default() += 1;
        });
    }
    preds
}

fn inventory_call(term: &Terminator, inventory: &HashSet<CalleeIdentity>) -> bool {
    matches!(term, Terminator::Call { callee_identity: Some(id), .. } if inventory.contains(id))
}

enum StmtOperands<'a> {
    Empty,
    One(&'a Operand),
    Two([&'a Operand; 2]),
    Slice(&'a [Operand]),
}

impl<'a> StmtOperands<'a> {
    fn for_each_place(self, mut f: impl FnMut(&'a Place)) {
        match self {
            Self::Empty => {}
            Self::One(op) => {
                if let Some(p) = operand_place(op) {
                    f(p);
                }
            }
            Self::Two(ops) => {
                for op in ops {
                    if let Some(p) = operand_place(op) {
                        f(p);
                    }
                }
            }
            Self::Slice(ops) => {
                for op in ops {
                    if let Some(p) = operand_place(op) {
                        f(p);
                    }
                }
            }
        }
    }
}

/// The operands a statement reads and the places it borrows (for M). Statements that
/// write through pointers are refused by `tinv_refusal` before this runs; they and any
/// statement or rvalue variant added later refuse here too.
fn statement_reads(
    stmt: &Statement,
    at: TypeInvariantSite,
) -> Result<(StmtOperands<'_>, Option<&Place>), TinvObligationRefusal> {
    let unclassified =
        || TinvObligationRefusal::Write(format!("a statement TINV does not classify at {at}"));
    let rvalue = match stmt {
        Statement::Assign { rvalue, .. } => rvalue,
        Statement::StorageLive(_)
        | Statement::StorageDead(_)
        | Statement::SetDiscriminant { .. }
        | Statement::Deinit { .. }
        | Statement::Retag { .. }
        | Statement::PlaceMention(_)
        | Statement::Coverage
        | Statement::ConstEvalCounter
        | Statement::Nop => return Ok((StmtOperands::Empty, None)),
        Statement::Intrinsic { .. }
        | Statement::CopyNonOverlapping { .. }
        | Statement::Unsupported { .. } => return Err(unclassified()),
        _ => return Err(unclassified()),
    };
    Ok(match rvalue {
        Rvalue::Use(a) | Rvalue::UnaryOp(_, a) | Rvalue::Cast(a, _) | Rvalue::Repeat(a, _) => {
            (StmtOperands::One(a), None)
        }
        Rvalue::BinaryOp(_, a, b)
        | Rvalue::CheckedBinaryOp(_, a, b)
        | Rvalue::UncheckedBinaryOp(_, a, b) => (StmtOperands::Two([a, b]), None),
        Rvalue::PtrOffset { ptr, count } => (StmtOperands::Two([ptr, count]), None),
        Rvalue::Aggregate(_, ops) | Rvalue::Unsupported { operands: ops, .. } => {
            (StmtOperands::Slice(ops), None)
        }
        Rvalue::Ref { place, .. } | Rvalue::AddressOf(_, place) => {
            (StmtOperands::Empty, Some(place))
        }
        // Reads of a discriminant, a length or a reference value: no `S` value moves.
        Rvalue::Discriminant(_) | Rvalue::Len(_) | Rvalue::CopyForDeref(_) => {
            (StmtOperands::Empty, None)
        }
        _ => return Err(unclassified()),
    })
}

fn operand_place(op: &Operand) -> Option<&Place> {
    match op {
        Operand::Copy(p) | Operand::Move(p) => Some(p),
        _ => None,
    }
}

/// Type-independent body facts shared across all candidate types in a multi-type walk.
pub(crate) struct PreparedBody<'a> {
    has_tail_call: bool,
    expanded: Cow<'a, VerifiableFunction>,
    regions: unwind::BodyRegions,
    cross_check_err: Option<CrossCheckMismatch>,
    findings: Vec<WriteFinding>,
    upoints_res: Result<(FxHashMap<usize, UPoint>, Vec<Place>), URefusal>,
    call_results: FxHashSet<usize>,
    preds: FxHashMap<BlockId, usize>,
    normal_block_indices: Vec<usize>,
    cleanup_block_indices: Vec<usize>,
    normal_block_map: FxHashMap<BlockId, usize>,
    normal_findings_by_site: FxHashMap<(usize, usize), Vec<usize>>,
    cleanup_finding_indices: Vec<usize>,
    has_non_scalar_constant: bool,
}

impl<'a> PreparedBody<'a> {
    pub(crate) fn new(
        func: &'a VerifiableFunction,
        facts: Option<&TinvBodyFacts>,
        models: &dyn ExactCallModels,
    ) -> Self {
        let has_tail_call = crate::generate::terminator_presence_for(func).has_tail_call;
        if has_tail_call {
            return Self {
                has_tail_call: true,
                expanded: Cow::Borrowed(func),
                regions: unwind::BodyRegions::default(),
                cross_check_err: None,
                findings: Vec::new(),
                upoints_res: Ok((FxHashMap::default(), Vec::new())),
                call_results: FxHashSet::default(),
                preds: FxHashMap::default(),
                normal_block_indices: Vec::new(),
                cleanup_block_indices: Vec::new(),
                normal_block_map: FxHashMap::default(),
                normal_findings_by_site: FxHashMap::default(),
                cleanup_finding_indices: Vec::new(),
                has_non_scalar_constant: false,
            };
        }
        let expanded = Cow::Borrowed(func);
        let body = &expanded.body;
        // PERF-COMPILER-VCGEN-698 / PERF-COMPILER-VCGEN-699: build `index` once (zero
        // allocation on canonical `BlockId`s) and share `index` + `preds` across
        // `body_regions_with`, `cross_check_with`, and `u_point_with`.
        let index = unwind::block_index(body);
        let regions = unwind::body_regions_with(&index);
        let mut preds = FxHashMap::default();
        let cross_check_err = facts
            .and_then(|f| unwind::cross_check_with(body, &index, &mut Some(&mut preds), &regions, f).err());
        if cross_check_err.is_some() {
            return Self {
                has_tail_call: false,
                expanded,
                regions,
                cross_check_err,
                findings: Vec::new(),
                upoints_res: Ok((FxHashMap::default(), Vec::new())),
                call_results: FxHashSet::default(),
                preds: FxHashMap::default(),
                normal_block_indices: Vec::new(),
                cleanup_block_indices: Vec::new(),
                normal_block_map: FxHashMap::default(),
                normal_findings_by_site: FxHashMap::default(),
                cleanup_finding_indices: Vec::new(),
                has_non_scalar_constant: false,
            };
        }
        let findings = place_write::classify_writes_expanded(expanded.as_ref());
        if preds.is_empty() && !body.blocks.is_empty() {
            preds = predecessor_counts(&func.body);
        }
        let mut normal_block_indices = Vec::with_capacity(regions.normal.len());
        let mut cleanup_block_indices = Vec::with_capacity(regions.cleanup.len());
        let mut normal_block_map =
            FxHashMap::with_capacity_and_hasher(regions.normal.len(), Default::default());
        for (idx, block) in body.blocks.iter().enumerate() {
            if regions.normal.contains(&block.id) {
                normal_block_indices.push(idx);
                normal_block_map.insert(block.id, idx);
            } else if regions.cleanup.contains(&block.id) {
                cleanup_block_indices.push(idx);
            }
        }
        let mut upoints: FxHashMap<usize, UPoint> =
            FxHashMap::with_capacity_and_hasher(normal_block_indices.len(), Default::default());
        let mut replace_places: Vec<Place> = Vec::new();
        let mut err = None;
        for &bi in &normal_block_indices {
            let block = &body.blocks[bi];
            let point = unwind::u_point_with(body, &index, &preds, block, &regions, models);
            match &point {
                UPoint::Refuse(r) => {
                    err = Some(*r);
                    break;
                }
                UPoint::Owed { state: UState::PreAssign { place, .. }, .. } => {
                    replace_places.push(place.clone());
                }
                UPoint::Owed { .. } | UPoint::None => {}
            }
            upoints.insert(block.id.0, point);
        }
        let upoints_res = match err {
            Some(r) => Err(r),
            None => Ok((upoints, replace_places)),
        };
        let call_results = if crate::generate::terminator_presence_for(expanded.as_ref()).has_call {
            body.blocks
                .iter()
                .filter_map(|b| match &b.terminator {
                    Terminator::Call { dest, .. } => Some(dest.local),
                    _ => None,
                })
                .collect()
        } else {
            FxHashSet::default()
        };
        let mut normal_findings_by_site: FxHashMap<(usize, usize), Vec<usize>> =
            FxHashMap::with_capacity_and_hasher(findings.len(), Default::default());
        let mut cleanup_finding_indices = Vec::new();
        for (fi, f) in findings.iter().enumerate() {
            let at = finding_site(f);
            let bid = BlockId(at.block);
            if regions.normal.contains(&bid) {
                normal_findings_by_site
                    .entry((at.block, at.statement_index))
                    .or_default()
                    .push(fi);
            } else if regions.cleanup.contains(&bid) {
                cleanup_finding_indices.push(fi);
            }
        }
        let has_non_scalar_constant = body_has_non_scalar_constant(body);
        Self {
            has_tail_call: false,
            expanded,
            regions,
            cross_check_err: None,
            findings,
            upoints_res,
            call_results,
            preds,
            normal_block_indices,
            cleanup_block_indices,
            normal_block_map,
            normal_findings_by_site,
            cleanup_finding_indices,
            has_non_scalar_constant,
        }
    }
}

/// Every situated E/C/R/U/M/Drop point of `func` for `inp.ty` (design P4), or why the
/// type must be withheld. Pure: it reads the body and nothing else.
///
/// Preconditions, each a refusal: no `TailCall` (D5: the refusal is v1); the model's
/// regions agree with the rustc facts when they are given; every write is attributable
/// (`place_write::tinv_refusal`); every normal-region terminator has a U classification;
/// no cleanup-region call receives a value reaching `S`; every cleanup-region write of
/// `S` is drop glue or the mirror of a recognised drop-and-replace.
pub fn obligation_points(
    func: &VerifiableFunction,
    facts: Option<&TinvBodyFacts>,
    inp: &TinvInputs<'_>,
) -> Result<Vec<TinvPointRow>, TinvObligationRefusal> {
    let prepared = PreparedBody::new(func, facts, inp.models);
    obligation_points_prepared(&prepared, facts, inp)
}

pub(super) fn obligation_points_prepared(
    prepared: &PreparedBody<'_>,
    facts: Option<&TinvBodyFacts>,
    inp: &TinvInputs<'_>,
) -> Result<Vec<TinvPointRow>, TinvObligationRefusal> {
    // D5. Checked on the body as extracted: the expansion below would turn a tail call
    // into a call and a return, which is the C + R alternative the design defers.
    if prepared.has_tail_call {
        return Err(TinvObligationRefusal::U(URefusal::TailCall));
    }
    if let Some(err) = &prepared.cross_check_err {
        return Err(TinvObligationRefusal::CrossCheck(err.clone()));
    }
    let func = prepared.expanded.as_ref();
    let body = &func.body;
    let name = inp.ty.def_path.as_str();
    let findings = &prepared.findings;

    // Decision TINV-33: the census's crate-level evidence for `dyn` and type parameters
    // (none without facts).
    let opaque = facts.map(|f| f.opaque_reach(name)).unwrap_or_default();
    if let Some(why) = place_write::tinv_refusal_with(func, findings, name, opaque) {
        return Err(TinvObligationRefusal::Write(why));
    }
    let constants_clear = facts.is_some_and(|f| f.constants_clear(name));
    if prepared.has_non_scalar_constant
        && let Some(at) = s_reaching_constant(func, name, constants_clear)
    {
        return Err(TinvObligationRefusal::Write(format!(
            "a constant that may hold an `S` value at {at}"
        )));
    }

    let (upoints, replace_places) = match &prepared.upoints_res {
        Ok(pair) => pair,
        Err(r) => return Err(TinvObligationRefusal::U(*r)),
    };
    let normal: Vec<&BasicBlock> =
        prepared.normal_block_indices.iter().map(|&i| &body.blocks[i]).collect();

    // The cleanup region is covered by the U rows at the panicking terminators. That
    // holds only for what rustc puts there: drop glue and the drop-and-replace mirror.
    for &bi in &prepared.cleanup_block_indices {
        let block = &body.blocks[bi];
        if let Some(args) = block.terminator.call_args() {
            let at = site(block.id, block.stmts.len());
            for arg in args {
                if let Some(p) = operand_place(arg)
                    && may_hold_s(func, p, name, opaque)
                {
                    return Err(TinvObligationRefusal::RootShape {
                        site: at,
                        ty: type_of(func, p),
                    });
                }
            }
        }
    }
    for &fi in &prepared.cleanup_finding_indices {
        let f = &findings[fi];
        let at = finding_site(f);
        let channel = match f {
            WriteFinding::Field { adt, element_only: false, channel, .. }
            | WriteFinding::WholeValue { adt, channel, .. }
                if adt == name =>
            {
                *channel
            }
            _ => continue,
        };
        let mirrored = || {
            let stmt = body
                .blocks
                .get(at.block)
                .filter(|b| b.id.0 == at.block)
                .or_else(|| body.blocks.iter().find(|b| b.id.0 == at.block))
                .and_then(|b| b.stmts.get(at.statement_index));
            matches!(stmt, Some(Statement::Assign { place, .. }) if replace_places.contains(place))
        };
        let allowed = match channel {
            PlaceWriteChannel::DropGlue => true,
            PlaceWriteChannel::Store => mirrored(),
            PlaceWriteChannel::SetDiscriminant
            | PlaceWriteChannel::Deinit
            | PlaceWriteChannel::MutBorrow
            | PlaceWriteChannel::RawBorrow { .. }
            | PlaceWriteChannel::CallDest
            | PlaceWriteChannel::TailCallReturn => false,
        };
        if !allowed {
            return Err(TinvObligationRefusal::Write(format!(
                "a cleanup-region write of {name} at {at}"
            )));
        }
    }

    let mut an = Analysis {
        func,
        name,
        opaque,
        inp,
        roots: Vec::new(),
        root_index: FxHashMap::default(),
        call_results: &prepared.call_results,
        stmt_effects: FxHashMap::default(),
        term_effects: FxHashMap::with_capacity_and_hasher(normal.len(), Default::default()),
        unwind_gen: FxHashMap::with_capacity_and_hasher(normal.len(), Default::default()),
        calls: FxHashMap::default(),
    };

    // Pass 1: intern every root, in body order.
    let by_site = &prepared.normal_findings_by_site;
    for block in &normal {
        if !by_site.is_empty() {
            for k in 0..=block.stmts.len() {
                for &fi in by_site.get(&(block.id.0, k)).into_iter().flatten() {
                    match &findings[fi] {
                        WriteFinding::Field { adt, element_only: false, owner, site, .. }
                        | WriteFinding::WholeValue { adt, owner, site, .. }
                            if adt == name =>
                        {
                            let root = canonical(func, owner, *site)?;
                            an.intern(root);
                        }
                        _ => {}
                    }
                }
            }
        }
        if let Terminator::Call { args, .. } = &block.terminator {
            let at = site(block.id, block.stmts.len());
            let mut received = Vec::new();
            for arg in args {
                if let Some((root, shape)) = call_arg_root(func, name, arg, at, opaque)? {
                    received.push(Received { root: an.intern(root), shape });
                }
            }
            let inventory = inventory_call(&block.terminator, inp.inventory);
            an.calls.insert(block.id.0, CallInfo { inventory, received });
        }
    }

    // Pass 2: the effects of every normal-region statement and terminator.
    for block in &normal {
        let b = block.id.0;
        for (k, stmt) in block.stmts.iter().enumerate() {
            let at = site(block.id, k);
            let mut effects = Vec::new();
            if !by_site.is_empty() {
                for &fi in by_site.get(&(b, k)).into_iter().flatten() {
                    match &findings[fi] {
                        WriteFinding::Field { adt, element_only: false, owner, channel, .. }
                            if adt == name =>
                        {
                            let r = an.root_of(owner, at)?;
                            effects.push(partial_write_effect(*channel, r));
                        }
                        WriteFinding::WholeValue { adt, owner, channel, .. } if adt == name => {
                            let r = an.root_of(owner, at)?;
                            let effect = match channel {
                                PlaceWriteChannel::Store => match stmt {
                                    Statement::Assign {
                                        rvalue:
                                            Rvalue::Aggregate(AggregateKind::Adt { name: n, .. }, _),
                                        ..
                                    } if n == name => Some(Effect::Kill(r)),
                                    Statement::Assign {
                                        rvalue: Rvalue::Use(Operand::Copy(q) | Operand::Move(q)),
                                        ..
                                    } if crate::place_ty_cow(func, q)
                                        .is_some_and(|t| is_s(&t, name)) =>
                                    {
                                        let src = canonical(func, q, at)?;
                                        Some(Effect::Transfer {
                                            dest: r,
                                            src: an.root_index.get(&src).copied(),
                                        })
                                    }
                                    _ => Some(Effect::Gen(r)),
                                },
                                PlaceWriteChannel::MutBorrow => match stmt {
                                    Statement::Assign { place: dest, .. }
                                        if borrow_is_pass_through(func, dest) =>
                                    {
                                        None
                                    }
                                    _ => Some(Effect::Sticky(r)),
                                },
                                PlaceWriteChannel::RawBorrow { .. } => Some(Effect::Sticky(r)),
                                PlaceWriteChannel::SetDiscriminant
                                | PlaceWriteChannel::Deinit
                                | PlaceWriteChannel::CallDest
                                | PlaceWriteChannel::TailCallReturn
                                | PlaceWriteChannel::DropGlue => Some(Effect::Gen(r)),
                            };
                            effects.extend(effect);
                        }
                        _ => {}
                    }
                }
            }
            if let PlaceWrites::Places(writes) = stmt.place_writes() {
                for (place, channel) in writes {
                    an.parent_effects(place, channel, at, &mut effects)?;
                }
            }
            // PERF-COMPILER-VCGEN-700: only store non-empty effect vectors.
            if !effects.is_empty() {
                an.stmt_effects.insert((b, k), effects);
            }
        }

        let at = site(block.id, block.stmts.len());
        let term = &block.terminator;
        let is_drop = matches!(term, Terminator::Drop { .. });
        let inventory = inventory_call(term, inp.inventory);
        let mut effects = Vec::new();
        let mut unwind_gen = Vec::new();
        if let Some(info) = an.calls.get(&b) {
            for rec in &info.received {
                if info.inventory {
                    effects.push(Effect::Kill(rec.root));
                } else if rec.shape == Shape::MutRef {
                    effects.push(Effect::Gen(rec.root));
                    unwind_gen.push(rec.root);
                }
            }
        }
        if !by_site.is_empty() {
            for &fi in by_site.get(&(b, block.stmts.len())).into_iter().flatten() {
                let effect = match &findings[fi] {
                    WriteFinding::Field { adt, element_only: false, owner, channel, .. }
                        if adt == name =>
                    {
                        partial_write_effect(*channel, an.root_of(owner, at)?)
                    }
                    WriteFinding::WholeValue { adt, owner, channel, .. } if adt == name => {
                        let r = an.root_of(owner, at)?;
                        match channel {
                            PlaceWriteChannel::CallDest if inventory => Effect::Kill(r),
                            PlaceWriteChannel::CallDest
                            | PlaceWriteChannel::Store
                            | PlaceWriteChannel::SetDiscriminant
                            | PlaceWriteChannel::Deinit
                            | PlaceWriteChannel::TailCallReturn
                            | PlaceWriteChannel::DropGlue => Effect::Gen(r),
                            PlaceWriteChannel::MutBorrow | PlaceWriteChannel::RawBorrow { .. } => {
                                Effect::Sticky(r)
                            }
                        }
                    }
                    _ => continue,
                };
                if is_drop && let Effect::Gen(r) = effect {
                    unwind_gen.push(r);
                }
                effects.push(effect);
            }
        }
        if let PlaceWrites::Places(writes) = term.place_writes() {
            for (place, channel) in writes {
                let genned = an.parent_effects(place, channel, at, &mut effects)?;
                if is_drop {
                    unwind_gen.extend(genned);
                }
            }
        }
        if !effects.is_empty() {
            an.term_effects.insert(b, effects);
        }
        if !unwind_gen.is_empty() {
            an.unwind_gen.insert(b, unwind_gen);
        }
    }

    // The forward may-dirty fixpoint over the normal region. Finite lattice (each root
    // absent < Dirty < Sticky), monotone transfer: it terminates.
    let normal_block_map = &prepared.normal_block_map;
    let mut entry: FxHashMap<usize, State> =
        FxHashMap::with_capacity_and_hasher(normal.len(), Default::default());
    let mut queue: VecDeque<BlockId> = VecDeque::with_capacity(normal.len());
    let mut in_queue: FxHashSet<BlockId> =
        FxHashSet::with_capacity_and_hasher(normal.len(), Default::default());
    if normal_block_map.contains_key(&BlockId(0)) {
        entry.insert(0, State::new());
        queue.push_back(BlockId(0));
        in_queue.insert(BlockId(0));
    }
    while let Some(id) = queue.pop_front() {
        in_queue.remove(&id);
        let Some(&block_idx) = normal_block_map.get(&id) else {
            continue;
        };
        let block = &body.blocks[block_idx];
        let Some(entry_state) = entry.get(&id.0) else {
            continue;
        };
        let mut state = entry_state.clone();
        if !an.stmt_effects.is_empty() {
            for k in 0..block.stmts.len() {
                if let Some(effects) = an.stmt_effects.get(&(id.0, k)) {
                    for e in effects {
                        apply(&mut state, *e);
                    }
                }
            }
        }
        if let Some(effects) = an.term_effects.get(&id.0) {
            for e in effects {
                apply(&mut state, *e);
            }
        }
        unwind::for_each_normal_successor(&block.terminator, |succ| {
            if !normal_block_map.contains_key(&succ) {
                return;
            }
            let changed = match entry.get_mut(&succ.0) {
                Some(into) => join_into(into, &state),
                None => {
                    entry.insert(succ.0, state.clone());
                    true
                }
            };
            if changed && in_queue.insert(succ) {
                queue.push_back(succ);
            }
        });
    }
    an.rows(&normal, &entry, upoints)
}

/// Join `from` into `into` (pointwise max, absent = clean); whether `into` grew.
fn join_into(into: &mut State, from: &State) -> bool {
    let mut changed = false;
    for (r, d) in from {
        if into.get(r).is_none_or(|cur| cur < d) {
            into.insert(*r, *d);
            changed = true;
        }
    }
    changed
}

impl Analysis<'_> {
    /// The index of an interned root. Every root a row or an effect names was interned
    /// from the same findings in pass 1; a miss is a classification gap and refuses.
    fn root_of(
        &self,
        place: &Place,
        at: TypeInvariantSite,
    ) -> Result<usize, TinvObligationRefusal> {
        let root = canonical(self.func, place, at)?;
        self.root_index.get(&root).copied().ok_or_else(|| {
            TinvObligationRefusal::Write(format!("an S write TINV did not index at {at}"))
        })
    }

    fn rows(
        &self,
        normal: &[&BasicBlock],
        entry: &FxHashMap<usize, State>,
        upoints: &FxHashMap<usize, UPoint>,
    ) -> Result<Vec<TinvPointRow>, TinvObligationRefusal> {
        let func = self.func;
        let mut rows: Vec<TinvPointRow> = Vec::new();
        let mut seen: FxHashSet<(u8, usize, usize, usize)> = FxHashSet::default();
        let mut push = |rows: &mut Vec<TinvPointRow>,
                        point: TypeInvariantPoint,
                        at: TypeInvariantSite,
                        row_point: usize,
                        r: usize,
                        sigma_src: SigmaSource,
                        state: TinvStateSpec,
                        failure: Option<(Operand, bool)>| {
            if seen.insert((point.canonical_byte(), at.block, at.statement_index, r)) {
                rows.push(TinvPointRow {
                    point,
                    site: at,
                    row_point,
                    root: self.roots[r].clone(),
                    sigma_src,
                    state,
                    failure,
                });
            }
        };
        // Dirty roots that are `place` or lie under it (M at a move, copy or whole
        // borrow of a dirty root or of a place containing one, rail 16).
        let moved =
            |place: &Place, state: &State, at| -> Result<Vec<usize>, TinvObligationRefusal> {
                if !may_hold_s(func, place, self.name, self.opaque) {
                    return Ok(Vec::new());
                }
                let cp = canonical(func, place, at)?;
                Ok(self.roots_under(&cp).filter(|r| state.contains_key(r)).collect())
            };

        for block in normal {
            let b = block.id.0;
            let Some(start) = entry.get(&b) else { continue };
            let mut state = start.clone();
            for (k, stmt) in block.stmts.iter().enumerate() {
                let at = site(block.id, k);
                if let Statement::Assign {
                    place,
                    rvalue: Rvalue::Aggregate(AggregateKind::Adt { name: n, .. }, ops),
                    ..
                } = stmt
                    && n == self.name
                {
                    let r = self.root_of(place, at)?;
                    push(
                        &mut rows,
                        TypeInvariantPoint::Establish,
                        at,
                        k,
                        r,
                        SigmaSource::AggregateOperands(ops.clone()),
                        TinvStateSpec::At,
                        None,
                    );
                }
                let (operands, borrowed) = statement_reads(stmt, at)?;
                let mut check_moved = |p: &Place| -> Result<(), TinvObligationRefusal> {
                    for r in moved(p, &state, at)? {
                        push(
                            &mut rows,
                            TypeInvariantPoint::Move,
                            at,
                            k,
                            r,
                            SigmaSource::Root,
                            TinvStateSpec::At,
                            None,
                        );
                    }
                    Ok(())
                };
                let mut move_err = None;
                operands.for_each_place(|p| {
                    if move_err.is_none()
                        && let Err(e) = check_moved(p)
                    {
                        move_err = Some(e);
                    }
                });
                if let Some(e) = move_err {
                    return Err(e);
                }
                if let Some(p) = borrowed {
                    check_moved(p)?;
                }
                if !self.stmt_effects.is_empty()
                    && let Some(effects) = self.stmt_effects.get(&(b, k))
                {
                    for e in effects {
                        apply(&mut state, *e);
                    }
                }
            }

            let at = site(block.id, block.stmts.len());
            let term = &block.terminator;
            let term_operands: &[Operand] = match term {
                Terminator::Goto(_)
                | Terminator::Return
                | Terminator::Unreachable
                | Terminator::Resume
                | Terminator::Drop { .. } => &[],
                Terminator::SwitchInt { discr, .. } => std::slice::from_ref(discr),
                Terminator::Assert { cond, .. } => std::slice::from_ref(cond),
                Terminator::Call { args, .. } => args.as_slice(),
                Terminator::TailCall { .. } => {
                    return Err(TinvObligationRefusal::U(URefusal::TailCall));
                }
                Terminator::Opaque { .. } => {
                    return Err(TinvObligationRefusal::U(URefusal::OpaqueTerminator));
                }
                _ => return Err(TinvObligationRefusal::U(URefusal::UnknownTerminator)),
            };
            for p in term_operands.iter().filter_map(operand_place) {
                for r in moved(p, &state, at)? {
                    push(
                        &mut rows,
                        TypeInvariantPoint::Move,
                        at,
                        usize::MAX,
                        r,
                        SigmaSource::Root,
                        TinvStateSpec::At,
                        None,
                    );
                }
            }

            // C: owed at every call receiving a root, dirty or not (TINV-4).
            let info = self.calls.get(&b);
            for rec in info.map(|i| i.received.as_slice()).unwrap_or_default() {
                push(
                    &mut rows,
                    TypeInvariantPoint::Call,
                    at,
                    usize::MAX,
                    rec.root,
                    SigmaSource::Root,
                    TinvStateSpec::At,
                    None,
                );
            }

            // U.
            if let Some(UPoint::Owed { failure, state: ustate }) = upoints.get(&b)
                && (!state.is_empty() || self.unwind_gen.get(&b).is_some_and(|ug| !ug.is_empty()))
            {
                let passed: Vec<usize> = match info {
                    Some(i) if i.inventory => i.received.iter().map(|rec| rec.root).collect(),
                    Some(_) | None => Vec::new(),
                };
                let failure = match failure {
                    UFailure::AssertFails { cond, expected } => Some((cond.clone(), *expected)),
                    UFailure::Always => None,
                };
                let spec = match ustate {
                    UState::Pre => TinvStateSpec::At,
                    UState::PreCallHavoc => TinvStateSpec::UnwindCallHavoc {
                        inventory_passed: passed.iter().map(|r| self.roots[*r].clone()).collect(),
                    },
                    UState::PreHavoc(p) => TinvStateSpec::UnwindDropHavoc(p.clone()),
                    UState::PreAssign { place, rvalue } => TinvStateSpec::UnwindDropAssign {
                        place: place.clone(),
                        rvalue: rvalue.clone(),
                    },
                };
                let candidates: BTreeSet<usize> = state
                    .keys()
                    .copied()
                    .chain(self.unwind_gen.get(&b).into_iter().flatten().copied())
                    .collect();
                for r in candidates {
                    if passed.contains(&r) {
                        continue;
                    }
                    if self.escaping(r) || self.owner_may_run_user_drop(r) {
                        push(
                            &mut rows,
                            TypeInvariantPoint::Unwind,
                            at,
                            usize::MAX,
                            r,
                            SigmaSource::Root,
                            spec.clone(),
                            failure.clone(),
                        );
                    }
                }
            }

            match term {
                // R: every dirty escaping root, and a dirty root under the return place.
                Terminator::Return => {
                    for (&r, _) in &state {
                        if self.escaping(r) || self.roots[r].local == 0 {
                            push(
                                &mut rows,
                                TypeInvariantPoint::Return,
                                at,
                                usize::MAX,
                                r,
                                SigmaSource::Root,
                                TinvStateSpec::At,
                                None,
                            );
                        }
                    }
                }
                // Drop: user drop glue observes every dirty root under the dropped place.
                Terminator::Drop { place, .. } => {
                    let ty = crate::place_ty_cow(func, place);
                    // `Unknown` reach (a trait object, a coroutine) may hold `S`.
                    let reaches = ty.as_ref().is_none_or(|t| {
                        place_write::type_reaches_with(
                            t,
                            self.name,
                            &func.body.datatype_defs,
                            self.opaque,
                        ) != Reach::No
                    });
                    let user = ty.as_ref().is_none_or(|t| (self.inp.may_run_user_drop)(t));
                    if reaches && user {
                        let cp = canonical(func, place, at)?;
                        for r in self.roots_under(&cp).filter(|r| state.contains_key(r)) {
                            push(
                                &mut rows,
                                TypeInvariantPoint::Drop,
                                at,
                                usize::MAX,
                                r,
                                SigmaSource::Root,
                                TinvStateSpec::At,
                                None,
                            );
                        }
                    }
                }
                _ => {}
            }
        }
        Ok(rows)
    }
}

/// The points after an inventory call at which `I` may be assumed for each root the call
/// received: the call's normal target `T` when `T` has exactly one predecessor over ALL
/// edges (normal and unwind, counted as `unwind::replace_assign` counts them) and is not
/// `bb0` (which has the implicit entry edge). A call whose identity is `None` or outside
/// the inventory gives nothing, and so does a call whose roots do not resolve (the body
/// is refused by [`obligation_points`] then). A body with a tail call gives nothing (D5).
#[must_use]
pub fn post_call_assumption_points(
    func: &VerifiableFunction,
    inp: &TinvInputs<'_>,
) -> Vec<PostCall> {
    if inp.inventory.is_empty() {
        return Vec::new();
    }
    let tp = crate::generate::terminator_presence_for(func);
    if tp.has_tail_call || !tp.has_call {
        return Vec::new();
    }
    let body = &func.body;
    let regions = unwind::body_regions(body);
    let preds = predecessor_counts(body);
    post_call_assumption_points_with(func, inp, &regions, &preds)
}

fn post_call_assumption_points_with(
    func: &VerifiableFunction,
    inp: &TinvInputs<'_>,
    regions: &unwind::BodyRegions,
    preds: &FxHashMap<BlockId, usize>,
) -> Vec<PostCall> {
    // PERF-COMPILER-VCGEN-699: skip scanning `body.blocks` when `inp.inventory` is empty
    // or the body contains no `Terminator::Call`.
    if inp.inventory.is_empty() || !crate::generate::terminator_presence_for(func).has_call {
        return Vec::new();
    }
    let name = inp.ty.def_path.as_str();
    let body = &func.body;
    let mut out = Vec::new();
    for block in body.blocks.iter().filter(|b| regions.normal.contains(&b.id)) {
        let Terminator::Call { args, dest, target: Some(target), .. } = &block.terminator else {
            continue;
        };
        if !inventory_call(&block.terminator, inp.inventory)
            || target.0 == 0
            || preds.get(target).copied() != Some(1)
        {
            continue;
        }
        let at = site(block.id, block.stmts.len());
        let roots: Result<Vec<_>, _> = args
            .iter()
            .filter_map(|a| {
                call_arg_root(func, name, a, at, place_write::OpaqueReach::default()).transpose()
            })
            .collect();
        let Ok(roots) = roots else { continue };
        out.extend(roots.into_iter().map(|(root, _)| PostCall {
            call_block: block.id,
            target: *target,
            root,
            kind: PostCallRoot::Arg,
        }));
        // Step 10.6: the destination, only as a whole non-return local of type exactly
        // `S` (no projection, no `Option<S>`, no `_0`).
        if dest.projections.is_empty()
            && dest.local != 0
            && crate::local_ty_ref(func, dest.local).is_some_and(|ty| is_s(ty, name))
        {
            out.push(PostCall {
                call_block: block.id,
                target: *target,
                root: dest.clone(),
                kind: PostCallRoot::Dest,
            });
        }
    }
    out
}

/// TINV-21: one call site at which a `Some`-arm lemma of the callee may be assumed (see
/// `generate::tinv_rows::ArmFact`): the call's normal target `seal`, the `Some` region
/// `region`, the root the call received at the lemma's parameter, and every lemma `φ`
/// instantiated UNVERSIONED there.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ArmSite {
    pub call_block: BlockId,
    pub seal: BlockId,
    pub region: BlockId,
    pub root: Place,
    pub facts: Vec<Formula>,
    /// The lemmas `facts` instantiate (the callee's identity and the lemma parameter).
    pub dep: super::arm_lemma::ArmLemmaDep,
    /// Index-aligned with `facts`: the lemma (`dep`, `φ`) each fact instantiates, so a row
    /// that assumes it records exactly which lemma it consumed (TINV-21 evidence).
    pub uses: Vec<super::arm_lemma::ArmLemmaUse>,
}

/// TINV-21: the arm-fact sites of `func` for type `inp.ty` (design §6 item 2). A call
/// qualifies exactly when every gate holds, and any miss gives nothing (fail-closed):
/// * the body has no tail call (D5), and the call is in the normal region;
/// * its `callee_identity` is in the inventory AND equals, EXACTLY, the identity of a body
///   `lemmas` were minted from (no lemma, another instance, a trait-item key: nothing);
/// * its normal target `T` has exactly one predecessor over ALL edges and is not `bb0`
///   (the [`post_call_assumption_points`] gates);
/// * its destination is a whole local, and the `Some` region is found from `T`
///   by `guards::option_some_arm` (a clean switch on the destination at `T`, or core's
///   authenticated `Try::branch` at `T` and a clean switch on its result; every hop
///   entered only from the previous one, storage markers only beside each step);
/// * the argument at the lemma's parameter resolves (`call_arg_root`) to a root of
///   `inp.ty` through a `&S`/`&mut S` (never by value, never an unresolved root).
#[must_use]
pub fn arm_fact_sites(
    func: &VerifiableFunction,
    inp: &TinvInputs<'_>,
    lemmas: &super::arm_lemma::ArmLemmas,
) -> Vec<ArmSite> {
    if lemmas.is_empty()
        || inp.inventory.is_empty()
        || {
            let tp = crate::generate::terminator_presence_for(func);
            tp.has_tail_call || !tp.has_call
        }
    {
        return Vec::new();
    }
    let body = &func.body;
    let regions = unwind::body_regions(body);
    let preds = predecessor_counts(body);
    arm_fact_sites_with(func, inp, lemmas, &regions, &preds)
}

fn arm_fact_sites_with(
    func: &VerifiableFunction,
    inp: &TinvInputs<'_>,
    lemmas: &super::arm_lemma::ArmLemmas,
    regions: &unwind::BodyRegions,
    preds: &FxHashMap<BlockId, usize>,
) -> Vec<ArmSite> {
    if lemmas.is_empty()
        || inp.inventory.is_empty()
        || !crate::generate::terminator_presence_for(func).has_call
    {
        return Vec::new();
    }
    let name = inp.ty.def_path.as_str();
    let body = &func.body;
    let mut out = Vec::new();
    for block in body.blocks.iter().filter(|b| regions.normal.contains(&b.id)) {
        let Terminator::Call {
            args, dest, target: Some(target), callee_identity: Some(id), ..
        } = &block.terminator
        else {
            continue;
        };
        if !inventory_call(&block.terminator, inp.inventory)
            || target.0 == 0
            || preds.get(target).copied() != Some(1)
            || !dest.projections.is_empty()
        {
            continue;
        }
        let mut by_param: Vec<(usize, Vec<&Formula>)> = Vec::new();
        for l in lemmas.for_callee(id, name) {
            match by_param.iter_mut().find(|(p, _)| *p == l.param()) {
                Some((_, phis)) => phis.push(l.phi()),
                None => by_param.push((l.param(), vec![l.phi()])),
            }
        }
        if by_param.is_empty() {
            continue;
        }
        let Some(region) =
            crate::guards::option_some_arm_of_call(func, block.id, *target, dest.local)
        else {
            continue;
        };
        let at = site(block.id, block.stmts.len());
        for (param, phis) in by_param {
            let Some(arg) = param.checked_sub(1).and_then(|i| args.get(i)) else { continue };
            let Ok(Some((root, Shape::SharedRef | Shape::MutRef))) =
                call_arg_root(func, name, arg, at, place_write::OpaqueReach::default())
            else {
                continue;
            };
            let sigma = sigma_of_root(func, inp.ty, &root);
            let dep = super::arm_lemma::ArmLemmaDep { ty: name.to_owned(), callee: *id, param };
            let (facts, uses): (Vec<Formula>, Vec<super::arm_lemma::ArmLemmaUse>) = phis
                .into_iter()
                .filter_map(|phi| {
                    let fact = super::instantiate(
                        &super::CandidateConjunct { id: 0, formula: phi.clone() },
                        &sigma,
                    )?;
                    let lemma_use = super::arm_lemma::ArmLemmaUse {
                        dep: dep.clone(),
                        phi: phi.clone(),
                        fact: fact.clone(),
                    };
                    Some((fact, lemma_use))
                })
                .unzip();
            if !facts.is_empty() {
                out.push(ArmSite {
                    call_block: block.id,
                    seal: *target,
                    region,
                    root,
                    facts,
                    dep,
                    uses,
                });
            }
        }
    }
    out
}

// ---------------------------------------------------------------------------------------
// The situated VCs (increment 7.5)
// ---------------------------------------------------------------------------------------

/// The identity of one TINV row of one walk: the type, the conjunct, the point and site,
/// the row's ordinal among the points of that type at that `(point, site)` (two roots
/// can owe the same point at one site, e.g. a call receiving two roots), and the edge
/// part. It is exactly the identity `VcKind::TypeInvariant` carries, field for field,
/// and the coverage match pairs a row with its key by equality of the two.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TinvRowKey {
    pub ty: String,
    pub conjunct: u32,
    pub point: TypeInvariantPoint,
    pub site: TypeInvariantSite,
    pub ordinal: u32,
    /// `Some(p)`: the EDGE PART of the point covering the executions that enter
    /// `site.block` from predecessor block `p` (TINV-9(a)). `None`: an unsplit row.
    pub edge: Option<usize>,
}

/// One body's request for one round: every candidate type with its ALIVE conjuncts.
pub struct BodyTinvPlan<'a> {
    pub types: &'a [TinvType],
    pub facts: Option<&'a TinvBodyFacts>,
    pub inventory: &'a HashSet<CalleeIdentity>,
    pub models: &'a dyn ExactCallModels,
    pub may_run_user_drop: &'a dyn Fn(&Ty) -> bool,
    /// The walk's step budget (`VerifyBudgetGuard`): a count, so the result is
    /// deterministic. The ambient wall-clock deadline is kept as a backstop; a clock trip
    /// is `Budget`, never a partial result.
    pub step_budget: u64,
}

/// What one walk established about one body.
///
/// NOTHING HERE IS A SILENT "NO OBLIGATION". A type in `refused` contributes no row and
/// must be withheld; a key in `uninstantiable` (its conjunct reads a field term the
/// generator has none for) contributes no row and its conjunct must be dropped. Only a
/// type absent from both with all of its keys in `rows` was fully checked.
#[derive(Debug, Clone, Default)]
pub struct TinvBodyRows {
    pub rows: Vec<(TinvRowKey, VerificationCondition)>,
    pub uninstantiable: Vec<TinvRowKey>,
    pub refused: Vec<(String, TinvObligationRefusal)>,
    /// TINV-21: per row key, the arm facts the row ASSUMED (the lemma each instantiates
    /// and the sealed hypothesis it carried). A certificate built from these rows must
    /// carry each named lemma, and its replay ties them together.
    pub row_arm_uses: crate::generate::tinv_rows::RowArmUses,
}

/// The direct parameter roots of `S` in `func`: an `S` parameter by value, or the pointee
/// `*p` of an `&S`/`&mut S` parameter. These start clean (whole-crate induction), so
/// the entry assumption instantiates every alive conjunct at them.
///
/// `pub(crate)` for step 10.2: the use site (`generate::type_invariant_facts`) gives entry
/// facts at a subset of EXACTLY these roots, so the two cannot disagree on the rule.
pub(crate) fn param_roots(func: &VerifiableFunction, name: &str) -> Vec<Place> {
    (1..=func.body.arg_count)
        .filter_map(|l| {
            let ty = crate::local_ty_ref(func, l)?;
            if is_s(ty, name) {
                return Some(Place::local(l));
            }
            match ty {
                Ty::Ref { inner, .. } if is_s(inner, name) => {
                    Some(Place { local: l, projections: vec![Projection::Deref] })
                }
                _ => None,
            }
        })
        .collect()
}

/// The situated TINV VCs of one body for one round: ONE safety walk carrying the rows of
/// every `(type, alive conjunct)` pair of `plan`; the caller filters by `(ty, conjunct)`.
///
/// Per type, [`obligation_points`] lists the points (a refusal lands in `refused`), and
/// each point is checked for each conjunct `c` as `pc ∧ state-binding ∧ hyps ∧ ¬c(σ)`,
/// built by the crate-private row shim (`generate::tinv_rows`) inside the ordinary safety
/// walk. The probe the walk runs on is `func` with:
/// * `preconditions` = the ENTRY assumption: every alive conjunct of every checked type
///   at every direct parameter root ([`param_roots`]), through the audited entry channel
///   (`conjoin_preconditions_versioned_at_point_recorded`, which strips an instance with
///   unmodeled Int arithmetic: precision only);
/// * no postconditions, contracts or spec (the `inferred_return` probe discipline).
///
/// Post-call facts are the alive conjuncts at each [`post_call_assumption_points`] root.
/// Both assumption channels are sound only under whole-crate induction over the SAME
/// alive set, which is the 7.6 Houdini loop's job.
///
/// A walk that does not return every requested row undegraded refuses the body
/// (`Coverage`, `Truncated`, `Budget`, `Shim`); two types with one `def_path`, or two
/// conjuncts of one type with one id, refuse it as `DuplicateDefPath`.
pub fn type_invariant_check_vcs(
    func: &VerifiableFunction,
    plan: &BodyTinvPlan<'_>,
) -> Result<TinvBodyRows, TinvObligationRefusal> {
    type_invariant_check_vcs_with_lemmas(func, plan, &super::arm_lemma::ArmLemmas::default())
}

/// [`type_invariant_check_vcs`] with the TINV-21 arm facts of `lemmas` ([`arm_fact_sites`])
/// attached to each type's rows (`generate::tinv_rows::ArmFact`). Houdini's rounds call
/// this with the lemmas minted before the fixpoint; a lemma probe never does.
pub fn type_invariant_check_vcs_with_lemmas(
    func: &VerifiableFunction,
    plan: &BodyTinvPlan<'_>,
    lemmas: &super::arm_lemma::ArmLemmas,
) -> Result<TinvBodyRows, TinvObligationRefusal> {
    if plan.types.is_empty() {
        return Ok(TinvBodyRows::default());
    }
    let prepared = PreparedBody::new(func, plan.facts, plan.models);
    type_invariant_check_vcs_with_lemmas_prepared(func, &prepared, plan, lemmas)
}

pub(crate) fn type_invariant_check_vcs_with_lemmas_prepared(
    func: &VerifiableFunction,
    prepared: &PreparedBody<'_>,
    plan: &BodyTinvPlan<'_>,
    lemmas: &super::arm_lemma::ArmLemmas,
) -> Result<TinvBodyRows, TinvObligationRefusal> {
    use crate::generate::tinv_rows::{
        ArmFact, Construction, RequestRow, RequestType, TinvRowRequest,
    };

    let mut seen: FxHashSet<&str> =
        FxHashSet::with_capacity_and_hasher(plan.types.len(), Default::default());
    for ty in plan.types {
        if !seen.insert(ty.def_path.as_str()) {
            return Err(TinvObligationRefusal::DuplicateDefPath(ty.def_path.clone()));
        }
        let mut ids: FxHashSet<u32> =
            FxHashSet::with_capacity_and_hasher(ty.conjuncts.len(), Default::default());
        for c in &ty.conjuncts {
            if !ids.insert(c.id) {
                return Err(TinvObligationRefusal::DuplicateDefPath(format!(
                    "{}#{}",
                    ty.def_path, c.id
                )));
            }
        }
    }

    let mut out = TinvBodyRows::default();
    if plan.types.is_empty() {
        return Ok(out);
    }
    let mut entry: Vec<Formula> = Vec::new();
    let mut types: Vec<RequestType> = Vec::with_capacity(plan.types.len());
    let mut rows: Vec<RequestRow> = Vec::new();
    for ty in plan.types {
        let inp = TinvInputs {
            ty,
            inventory: plan.inventory,
            models: plan.models,
            may_run_user_drop: plan.may_run_user_drop,
        };
        let points = match obligation_points_prepared(prepared, plan.facts, &inp) {
            Ok(points) => points,
            Err(refusal) => {
                // A refused type grants no assumption to the other types' rows either.
                out.refused.push((ty.def_path.clone(), refusal));
                continue;
            }
        };
        let mut sigma_cache: FxHashMap<Place, Sigma> = FxHashMap::default();
        let mut sigma_for = |root: &Place| -> Sigma {
            if let Some(s) = sigma_cache.get(root) {
                return s.clone();
            }
            let s = sigma_of_root(func, ty, root);
            sigma_cache.insert(root.clone(), s.clone());
            s
        };
        let instances = |sigma: &Sigma| -> Vec<Formula> {
            ty.conjuncts.iter().filter_map(|c| super::instantiate(c, sigma)).collect()
        };
        for root in param_roots(func, &ty.def_path) {
            entry.extend(instances(&sigma_for(&root)));
        }
        let post_calls =
            post_call_assumption_points_with(func, &inp, &prepared.regions, &prepared.preds)
                .into_iter()
                .map(|pc| (pc.target, instances(&sigma_for(&pc.root))))
                .collect();
        let constructions = points
            .iter()
            .filter(|pt| pt.point == TypeInvariantPoint::Establish)
            .filter_map(|pt| {
                let SigmaSource::AggregateOperands(ops) = &pt.sigma_src else { return None };
                let root = sigma_for(&pt.root);
                let from = sigma_of_operands(func, ty, ops);
                let pairs = |a: &[Option<Formula>], b: &[Option<Formula>]| {
                    a.iter()
                        .zip(b)
                        .filter_map(|(l, r)| Some((l.clone()?, r.clone()?)))
                        .collect::<Vec<_>>()
                };
                let mut all = pairs(&root.value, &from.value);
                all.extend(pairs(&root.len, &from.len));
                Some(Construction {
                    block: BlockId(pt.site.block),
                    stmt: pt.site.statement_index,
                    pairs: all,
                })
            })
            .collect();
        let arm_facts = arm_fact_sites_with(func, &inp, lemmas, &prepared.regions, &prepared.preds)
            .into_iter()
            .map(|a| ArmFact { seal: a.seal, region: a.region, facts: a.facts, uses: a.uses })
            .collect();
        let ti = types.len();
        types.push(RequestType {
            def_path: ty.def_path.clone(),
            post_calls,
            constructions,
            arm_facts,
        });

        let mut ordinals: FxHashMap<(u8, TypeInvariantSite), u32> =
            FxHashMap::with_capacity_and_hasher(points.len(), Default::default());
        for point in points {
            let ordinal = ordinals.entry((point.point.canonical_byte(), point.site)).or_default();
            let this = *ordinal;
            *ordinal += 1;
            let sigma = match &point.sigma_src {
                SigmaSource::Root => sigma_for(&point.root),
                SigmaSource::AggregateOperands(ops) => sigma_of_operands(func, ty, ops),
            };
            for c in &ty.conjuncts {
                let key = TinvRowKey {
                    ty: ty.def_path.clone(),
                    conjunct: c.id,
                    point: point.point,
                    site: point.site,
                    ordinal: this,
                    edge: None,
                };
                match super::instantiate(c, &sigma) {
                    Some(core) => rows.push(RequestRow {
                        key,
                        ty: ti,
                        point: point.clone(),
                        sigma: sigma.clone(),
                        core,
                        edge_guard: None,
                    }),
                    None => out.uninstantiable.push(key),
                }
            }
        }
    }
    if rows.is_empty() {
        return Ok(out);
    }

    let mut probe = func.clone();
    probe.preconditions = entry;
    probe.postconditions.clear();
    probe.contracts.clear();
    probe.spec = Default::default();
    let request = TinvRowRequest::new(probe.def_path.clone(), types, rows);
    let _budget = trust_types::verify_budget::VerifyBudgetGuard::install(
        trust_types::verify_budget::current_deadline(),
        plan.step_budget,
    );
    let (rows, uses) = crate::generate::tinv_rows::tinv_check_rows_recorded(&probe, request)?;
    out.rows = rows;
    out.row_arm_uses = uses;
    Ok(out)
}

#[cfg(test)]
#[path = "obligations_tests.rs"]
mod tests;
