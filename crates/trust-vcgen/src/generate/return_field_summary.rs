// Trust (TRUST-10, 2026-09-25): FIELD-READ return summaries — a same-crate
// callee that returns one integer field of its `&self` pointee (a getter), or a
// `bool` that compares that field with a constant, directly or through such a
// getter.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

//! # The false refutation this closes
//!
//! bit-vec 0.9.1 (`src/lib.rs:1638`):
//!
//! ```text
//! pub fn len(&self) -> usize { self.nbits }
//! pub fn is_empty(&self) -> bool { self.len() == 0 }
//! pub fn pop(&mut self) -> Option<bool> {
//!     self.ensure_invariant();
//!     if self.is_empty() { None } else { let i = self.nbits - 1; .. }
//! }
//! ```
//!
//! `pop`'s `self.nbits - 1` was reported `[overflow:sub] FAILED (ay-in-process)`
//! with `_2 = false, self*.1#e_s0_t = 0`: `is_empty()` false at `nbits == 0`,
//! which no execution produces. Nothing modeled `is_empty`'s result — the
//! bool-predicate family ([`ReturnBoolPredSummary`]) covers enum-TAG predicates
//! only, and the integer return summaries (upper/lower/const-set) need a
//! constant — so the call destination was a free variable of the query.
//!
//! # What is summarized
//!
//! A [`ReturnFieldSummary`] says, of a callee whose parameter `p` is a SHARED
//! reference to a struct:
//!
//! * [`ReturnFieldValue::Field`] — `ret == (*p).k` (`len`), or
//! * [`ReturnFieldValue::Compare`] — `ret ⇔ ((*p).k REL c)` (`is_empty`),
//!
//! where `k` is a direct integer field of the pointee (width < 128) and `c` a
//! constant. It is DERIVED from the callee's own extracted body by a
//! fail-closed symbolic walk ([`function_return_field_summary`]); nothing is
//! declared and nothing is trusted by name. The walk admits a single straight
//! entry→`Return` path of `Goto`s and of `Call`s to callees that ALREADY carry
//! a summary of this family (the `is_empty → len` composition), and statements
//! that are storage markers or whole-local assignments of a copy, a constant,
//! a shared reborrow of the subject, a subject-field read, an integer
//! comparison or a bool `!`. Anything else — a branch, a loop, an `Assert`, a
//! write to any parameter or through any pointer, a second `Return` — records
//! nothing.
//!
//! # Why the summary is TRUE of every returning execution
//!
//! `p` is a shared reference handed to the callee as an ARGUMENT, and the path
//! from `p` to the field crosses no interior-mutability wrapper (a direct
//! integer field of a struct that is not one). Such memory cannot change while
//! the call is in progress. The walked path itself performs NO write (only
//! whole-local assignments, and calls to callees whose own walk admitted none),
//! so nothing on this thread writes it; a write from another thread races with
//! the callee's read, and a write through any other alias is undefined
//! behaviour under the reference's function-argument protector — both are
//! outside every execution the verdict speaks about. Every read of `(*p).k` the
//! walk sees (directly, or inside a summarized nested getter that received a
//! reborrow of `*p`) therefore reads ONE value, and the recorded relation
//! between it and `_0` holds at `Return`. A path that panics never returns, so
//! the claim is vacuous there; the call-site facts reach only the call's
//! SUCCESS edge.
//!
//! What is trusted beyond the shared vcgen base: that the body summarized is
//! the body a call runs. The compiler refuses a body whose symbol can be
//! interposed ([`compute_return_field_summaries_admitting`]), and the call-site
//! key is the rendered callee path, exactly as for the sibling return summaries
//! (upper/lower bound, constant set, bool predicate, discriminant, setter).
//!
//! # The call site ([`return_field_callsite_facts`])
//!
//! The relation is stated over the CALLER's spelling of the same field. The
//! argument must be (a copy of) a pinned shared borrow of a caller place `P`
//! whose denotation cannot move between the borrow and the call's return: a
//! caller LOCAL (its storage), or `*b` for a parameter pointer `b` that is
//! never reseated and never mutably/raw borrowed as a whole. The protector
//! argument above also fixes `P.k` from the moment of the call to its return, so
//! the value the callee saw is BOTH the pre-call and the post-call value of
//! `P.k`. The fact is emitted in both spellings:
//!
//! * PRE-call — the ordinary [`version_terminator_dest_fact`] (reads at the
//!   block terminal, the destination at `s{b}_t`);
//! * POST-call — every name read at the entry of the call's success block,
//!   which must have that edge as its ONLY predecessor, so its entry version of
//!   `P.k` is the value right after the return. This is the spelling a later
//!   read uses when the call's conservative havoc re-versioned `P.k`
//!   (`self*.1#e_s0_t` above: a `&mut self` caller's base name is havocked at
//!   every call), and without it the fact could not reach `pop`'s subtraction.
//!
//! Both are facts about one execution's values, so they are sound in both
//! polarities (a PROVED row and a counterexample alike).

use super::*;

/// What a [`ReturnFieldSummary`] callee returns.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReturnFieldValue {
    /// `ret == (*p).field` — a getter.
    Field,
    /// `ret ⇔ ((*p).field REL rhs)`, `REL` one of `== != < <= > >=`.
    Compare { op: BinOp, rhs: i128 },
}

/// Trust (TRUST-10): the body-derived FIELD-READ contract of a same-crate
/// callee — see the module doc for the recognizer, the soundness argument and
/// the call-site threading. Keyed by `def_path` like its siblings.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReturnFieldSummary {
    /// The callee's formal parameter count (arity check at the call site).
    pub param_count: usize,
    /// 1-based local index of the `&Struct` parameter whose pointee is read.
    pub subject_param: usize,
    /// The pointee struct's name with generic arguments stripped — cross-checked
    /// against the caller's place type, so the summary is never applied to a
    /// different struct whose field `field` means something else.
    pub struct_name: String,
    /// The field index within the pointee.
    pub field: usize,
    /// The field's integer shape `(width, signed)`, `width < 128`.
    pub field_ty: (u32, bool),
    pub value: ReturnFieldValue,
}

/// Rounds of the whole-crate composition fixpoint. A body is summarized only
/// from summaries recorded in an EARLIER round, so the depth of a getter chain
/// the family can see is bounded by this (bit-vec's `is_empty → len` needs 2).
const RETURN_FIELD_MAX_ROUNDS: usize = 4;

/// Trust (TRUST-10): whole-crate map of `def_path` → field-read summary.
///
/// Composition: `is_empty` reads its field THROUGH `len`, so a body may call a
/// callee summarized in an earlier round. Each round only ADDS entries (a
/// missing callee entry fails the walk closed), and a body is never summarized
/// from its own entry, so every recorded summary rests on strictly earlier
/// ones — recursion, direct or mutual, records nothing. A `def_path` that two
/// extracted bodies share names neither of them and is skipped
/// (`summary_candidates`, the rule every body-derived lane shares since
/// SUMMARY-NAME-COLLIDE-1).
pub fn compute_return_field_summaries(
    funcs: &[VerifiableFunction],
) -> FxHashMap<String, ReturnFieldSummary> {
    compute_return_field_summaries_admitting(funcs, |_| true)
}

/// [`compute_return_field_summaries`] under the caller's IDENTITY gate: a body
/// `admit` refuses records nothing, and — because a missing entry fails every
/// walk that calls it — nothing composes through it either. The compiler
/// refuses a body whose symbol can be interposed at link time
/// (`#[no_mangle]`/`#[export_name]`/`#[linkage]`): the body summarized need
/// not be the one a call runs (D5-B's identity gate, for the same reason).
pub fn compute_return_field_summaries_admitting(
    funcs: &[VerifiableFunction],
    admit: impl Fn(&VerifiableFunction) -> bool,
) -> FxHashMap<String, ReturnFieldSummary> {
    let mut map: FxHashMap<String, ReturnFieldSummary> = FxHashMap::default();
    if funcs.is_empty() {
        return map;
    }
    let _work_scope = crate::gen_work_memo_scope_if_unscoped();
    // `summary_candidates` already drops every body whose `def_path` another
    // body in `funcs` shares.
    let candidates: Vec<&VerifiableFunction> =
        summary_candidates(funcs).into_iter().filter(|func| admit(func)).collect();
    if candidates.is_empty() {
        return map;
    }
    for round in 0..RETURN_FIELD_MAX_ROUNDS {
        let mut added = Vec::new();
        for &func in &candidates {
            if map.contains_key(&func.def_path) {
                continue;
            }
            let _analysis_scope = super::FuncAnalysisScope::enter(func);
            if round > 0 && !super::terminator_presence_for(func).has_bare_dest_call {
                continue;
            }
            if let Some(summary) = function_return_field_summary(func, &map) {
                added.push((func.def_path.clone(), summary));
            }
        }
        if added.is_empty() {
            break;
        }
        map.extend(added);
    }
    map
}

/// The integer shape `(width, signed)` of `ty`, `width < 128`.
fn int_shape(ty: &Ty) -> Option<(u32, bool)> {
    match ty {
        Ty::Int { width, signed } if (1..128).contains(width) => Some((*width, *signed)),
        Ty::PtrSizedInt { signed } => Some((64, *signed)),
        _ => None,
    }
}

/// The name of a struct ADT with generic arguments stripped, or `None` for
/// anything that is not a plain (non-interior-mutable) struct.
fn frozen_struct_name(ty: &Ty) -> Option<&str> {
    let Ty::Adt { name, adt_kind: Some(trust_types::AdtKind::Struct), .. } = ty else {
        return None;
    };
    if crate::guards::ty_is_interior_mut_wrapper(ty) {
        return None;
    }
    Some(name.split('<').next().unwrap_or(name).trim())
}

/// The integer shape of field `field` of the struct `ty`.
fn struct_field_shape(ty: &Ty, field: usize) -> Option<(u32, bool)> {
    let Ty::Adt { fields, .. } = ty else { return None };
    int_shape(&fields.get(field)?.1)
}

/// The symbolic value of a local during [`function_return_field_summary`]'s walk.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Sym {
    /// A shared reference to the subject parameter's pointee.
    Subject,
    /// The integer value of `(*subject).field`.
    Field(usize),
    /// An integer constant.
    Const(i128),
    /// `(*subject).field REL rhs`.
    Compare { field: usize, op: BinOp, rhs: i128 },
}

/// `a REL b` ⇔ `b REL' a`.
fn swap_comparison(op: BinOp) -> Option<BinOp> {
    Some(match op {
        BinOp::Eq => BinOp::Eq,
        BinOp::Ne => BinOp::Ne,
        BinOp::Lt => BinOp::Gt,
        BinOp::Le => BinOp::Ge,
        BinOp::Gt => BinOp::Lt,
        BinOp::Ge => BinOp::Le,
        _ => return None,
    })
}

/// `¬(a REL b)` ⇔ `a REL' b`.
fn negate_comparison(op: BinOp) -> Option<BinOp> {
    Some(match op {
        BinOp::Eq => BinOp::Ne,
        BinOp::Ne => BinOp::Eq,
        BinOp::Lt => BinOp::Ge,
        BinOp::Le => BinOp::Gt,
        BinOp::Gt => BinOp::Le,
        BinOp::Ge => BinOp::Lt,
        _ => return None,
    })
}

struct FieldWalk<'a> {
    /// The subject pointee's type (a frozen struct).
    pointee: &'a Ty,
    env: FxHashMap<usize, Sym>,
}

impl FieldWalk<'_> {
    fn read_place(&self, place: &Place) -> Option<Sym> {
        let base = self.env.get(&place.local).copied();
        match place.projections.as_slice() {
            [] => base,
            [Projection::Deref, Projection::Field(k)] if base == Some(Sym::Subject) => {
                struct_field_shape(self.pointee, *k)?;
                Some(Sym::Field(*k))
            }
            _ => None,
        }
    }

    fn operand(&self, op: &Operand) -> Option<Sym> {
        match op {
            Operand::Copy(place) | Operand::Move(place) => self.read_place(place),
            Operand::Constant(_) => Some(Sym::Const(operand_const_int(op)?)),
            _ => None,
        }
    }

    fn rvalue(&self, rvalue: &Rvalue) -> Option<Sym> {
        match rvalue {
            Rvalue::Use(op) => self.operand(op),
            // A shared reborrow of the whole subject pointee (`&(*_1)`).
            Rvalue::Ref { mutable: false, place }
                if place.projections.as_slice() == [Projection::Deref]
                    && self.env.get(&place.local) == Some(&Sym::Subject) =>
            {
                Some(Sym::Subject)
            }
            Rvalue::BinaryOp(op, a, b) => match (self.operand(a)?, self.operand(b)?) {
                (Sym::Field(field), Sym::Const(rhs)) => {
                    swap_comparison(*op)?; // a comparison operator
                    Some(Sym::Compare { field, op: *op, rhs })
                }
                (Sym::Const(rhs), Sym::Field(field)) => {
                    Some(Sym::Compare { field, op: swap_comparison(*op)?, rhs })
                }
                _ => None,
            },
            Rvalue::UnaryOp(trust_types::UnOp::Not, a) => match self.operand(a)? {
                Sym::Compare { field, op, rhs } => {
                    Some(Sym::Compare { field, op: negate_comparison(op)?, rhs })
                }
                _ => None,
            },
            _ => None,
        }
    }
}

/// Trust (TRUST-10): derive the field-read summary of ONE body, consulting the
/// summaries `known` from earlier rounds for its calls. `None` on anything
/// outside the fragment the module doc lists. SOUNDNESS: see the module doc —
/// every gate below either fixes the path (a single straight line, entered only
/// from the entry, the only way to `Return`) or fixes what the path computes.
pub(super) fn function_return_field_summary(
    func: &VerifiableFunction,
    known: &FxHashMap<String, ReturnFieldSummary>,
) -> Option<ReturnFieldSummary> {
    let arg_count = func.body.arg_count;
    // PERF-COMPILER-VCGEN-633: reject entry blocks whose terminator cannot start a
    // straight-line summary path before scanning parameter types or expanding tail calls.
    if arg_count == 0
        || !matches!(
            func.body.blocks.first().map(|b| &b.terminator),
            Some(
                Terminator::Return
                    | Terminator::Goto(_)
                    | Terminator::Call { target: Some(_), .. }
                    | Terminator::TailCall { .. }
            )
        )
        || !(1..=arg_count).any(|subject| {
            matches!(
                crate::local_ty_ref(func, subject),
                Some(Ty::Ref { mutable: false, inner }) if frozen_struct_name(inner).is_some()
            )
        })
    {
        return None;
    }
    let ret_ty = crate::local_ty_ref(func, 0)?;
    if !matches!(ret_ty, Ty::Bool) && int_shape(ret_ty).is_none() {
        return None;
    }
    let expanded = func.with_tail_calls_expanded();
    let func = expanded.as_ref();
    // Exactly one `Return` in the body: check once before trying each parameter.
    if func.body.blocks.iter().filter(|b| matches!(b.terminator, Terminator::Return)).count() != 1 {
        return None;
    }
    let ret_ty = crate::local_ty_ref(func, 0)?;
    (1..=arg_count).find_map(|subject| walk_subject(func, known, subject, ret_ty))
}

fn walk_subject(
    func: &VerifiableFunction,
    known: &FxHashMap<String, ReturnFieldSummary>,
    subject: usize,
    ret_ty: &Ty,
) -> Option<ReturnFieldSummary> {
    let arg_count = func.body.arg_count;
    let Ty::Ref { mutable: false, inner: pointee } = crate::local_ty_ref(func, subject)? else {
        return None;
    };
    let struct_name = frozen_struct_name(pointee)?;
    let mut walk = FieldWalk { pointee, env: FxHashMap::default() };
    walk.env.insert(subject, Sym::Subject);

    // The straight path from the entry, block by block.
    let mut path: Vec<BlockId> = Vec::new();
    let mut cur = func.body.blocks.first()?.id;
    loop {
        if path.contains(&cur) || path.len() > func.body.blocks.len() {
            return None; // a cycle never returns
        }
        path.push(cur);
        let block = func.body.blocks.get(cur.0).filter(|b| b.id == cur)?;
        for stmt in &block.stmts {
            match stmt {
                Statement::StorageLive(_)
                | Statement::StorageDead(_)
                | Statement::Nop
                | Statement::Coverage
                | Statement::ConstEvalCounter => {}
                Statement::Assign { place, rvalue, .. } => {
                    // Whole locals only, and never a parameter: the subject (and
                    // every other formal) keeps its entry value.
                    if !place.projections.is_empty() || (1..=arg_count).contains(&place.local) {
                        return None;
                    }
                    let value = walk.rvalue(rvalue)?;
                    walk.env.insert(place.local, value);
                }
                _ => return None,
            }
        }
        match &block.terminator {
            Terminator::Goto(next) => cur = *next,
            Terminator::Call { func: callee, args, dest, target: Some(next), .. } => {
                let summary = known.get(callee)?;
                if args.len() != summary.param_count
                    || summary.struct_name != struct_name
                    || struct_field_shape(pointee, summary.field) != Some(summary.field_ty)
                    || !dest.projections.is_empty()
                    || (1..=arg_count).contains(&dest.local)
                {
                    return None;
                }
                // The nested callee's subject must be (a reborrow of) OUR subject,
                // so its field IS our field.
                if walk.operand(args.get(summary.subject_param - 1)?)? != Sym::Subject {
                    return None;
                }
                let value = match summary.value {
                    ReturnFieldValue::Field => Sym::Field(summary.field),
                    ReturnFieldValue::Compare { op, rhs } => {
                        Sym::Compare { field: summary.field, op, rhs }
                    }
                };
                walk.env.insert(dest.local, value);
                cur = *next;
            }
            Terminator::Return => break,
            _ => return None,
        }
    }

    // PERF-COMPILER-VCGEN-633: verify the return slot `_0` holds a summarized field or
    // comparison with a valid integer field shape in O(1) before scanning all CFG
    // blocks for off-path branches into `path`.
    let (field, value) = match walk.env.get(&0)? {
        Sym::Field(field) => {
            if int_shape(ret_ty) != struct_field_shape(pointee, *field) {
                return None;
            }
            (*field, ReturnFieldValue::Field)
        }
        Sym::Compare { field, op, rhs } => {
            if !matches!(ret_ty, Ty::Bool) {
                return None;
            }
            (*field, ReturnFieldValue::Compare { op: *op, rhs: *rhs })
        }
        _ => return None,
    };
    let field_ty = struct_field_shape(pointee, field)?;

    // The path is the ONLY way to `Return`: `function_return_field_summary` already
    // verified there is exactly one `Return` in the body, and no block off the path
    // may branch into it (cleanup blocks reached by an unwind edge end in `Resume`,
    // not `Return`).
    for block in &func.body.blocks {
        let on_path = path.iter().position(|id| *id == block.id);
        let mut ok = true;
        let mut check_succ = |s: BlockId| {
            if !ok {
                return;
            }
            let into_path = path.iter().position(|id| *id == s);
            match (on_path, into_path) {
                // A path block's own next hop.
                (Some(i), Some(j)) if j == i + 1 => {}
                (_, None) => {}
                _ => ok = false,
            }
        };
        block.terminator.for_each_in_cfg_successor(&mut check_succ);
        if let Some(s) = block.terminator.unwind_cleanup_target() {
            check_succ(s);
        }
        if !ok {
            return None;
        }
    }

    Some(ReturnFieldSummary {
        param_count: arg_count,
        subject_param: subject,
        struct_name: struct_name.to_string(),
        field,
        field_ty,
        value,
    })
}

/// The caller place `P` whose field a summarized call reads, when `P` cannot
/// denote different memory at the borrow, at the call and right after it (see
/// the module doc). `arg` is the call's subject actual.
fn callsite_subject_place(func: &VerifiableFunction, arg: &Operand) -> Option<Place> {
    let (Operand::Copy(recv) | Operand::Move(recv)) = arg else {
        return None;
    };
    // A pinned shared borrow `&P` (through bare copy hops), or a directly passed,
    // pinned `&Struct` local `r` (`P = *r`).
    let subject = guard_receiver_subject(func, recv)?;
    let root = subject.local;
    match subject.projections.split_first() {
        // A caller-owned place: its storage is the local's own.
        None => {}
        Some((Projection::Field(_), _)) => {}
        // Through a pointer: the pointer must be a parameter that holds its entry
        // value everywhere — no whole write on any channel, and no `&mut`/`&raw`
        // of the pointer ITSELF (a reseat channel). A borrow THROUGH it
        // (`&mut (*self)`, bit-vec's `self.set(..)`) addresses the pointee, which
        // the version oracle already tracks, and cannot rebind the pointer; the
        // seam's narrow-escape SSA question is exactly that.
        Some((Projection::Deref, _)) => {
            if !crate::local_defs::is_parameter(func, root)
                || !crate::local_defs::is_single_static_assignment_modulo_pointee_borrows(
                    func, root,
                )
            {
                return None;
            }
        }
        _ => return None,
    }
    let rest = match subject.projections.first() {
        Some(Projection::Deref) => &subject.projections[1..],
        _ => &subject.projections[..],
    };
    if !rest.iter().all(|p| matches!(p, Projection::Field(_))) {
        return None;
    }
    // Every field hop is into a STRUCT that is not an interior-mutability
    // wrapper (a shared borrow does not freeze one), or into a tuple. A UNION
    // hop is refused: its fields overlap, so a later write to a sibling variant
    // changes `P.k` under a name the version oracle keys per field — a fact
    // over that name could then outlive the value it describes.
    let mut ty = std::borrow::Cow::Borrowed(crate::local_ty_ref(func, root)?);
    for projection in &subject.projections {
        if matches!(projection, Projection::Field(_)) {
            let frozen_field_owner = match ty.as_ref() {
                Ty::Tuple(_) => true,
                owner @ Ty::Adt { adt_kind: Some(trust_types::AdtKind::Struct), .. } => {
                    !crate::guards::ty_is_interior_mut_wrapper(owner)
                }
                _ => false,
            };
            if !frozen_field_owner {
                return None;
            }
        }
        ty = crate::step_place_ty_cow(ty, projection)?;
    }
    Some(subject)
}

/// The unversioned fact of a summarized call terminating `block`, with the
/// call's success block and the destination's name. `None` when any call-site
/// gate fails (no fact, never a wrong one).
fn return_field_callsite_fact(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
) -> Option<(Formula, BlockId, String)> {
    let Terminator::Call { func: callee, args, dest, target: Some(target), .. } = &block.terminator
    else {
        return None;
    };
    let summary = crate::callee_return_field_summary(callee)?;
    if target.0 == 0 || args.len() != summary.param_count || !dest.projections.is_empty() {
        return None;
    }
    let subject_arg = args.get(summary.subject_param - 1)?;
    if !matches!(subject_arg, Operand::Copy(_) | Operand::Move(_)) {
        return None;
    }
    let dest_ty = crate::local_ty_ref(func, dest.local)?;
    let dest_sort = match summary.value {
        ReturnFieldValue::Field if int_shape(dest_ty) == Some(summary.field_ty) => Sort::Int,
        ReturnFieldValue::Compare { .. } if matches!(dest_ty, Ty::Bool) => Sort::Bool,
        _ => return None,
    };
    // PERF-COMPILER-VCGEN-634: the post-call spelling needs the success edge to be the
    // ONLY way into `target` (and `target` not the entry, which the function entry
    // reaches). Verify this cheap CFG edge count before `callsite_subject_place` and
    // `place_ty_cow`.
    let mut incoming = 0usize;
    for b in &func.body.blocks {
        let mut count_succ = |s: BlockId| {
            if s == *target {
                incoming += 1;
            }
        };
        b.terminator.for_each_in_cfg_successor(&mut count_succ);
        if let Some(s) = b.terminator.unwind_cleanup_target() {
            count_succ(s);
        }
        if incoming > 1 {
            return None;
        }
    }
    if incoming != 1 {
        return None;
    }
    let subject = callsite_subject_place(func, subject_arg)?;
    if subject.local == dest.local {
        return None;
    }
    // The use-site cross-check: the SAME struct, and its field `field` has the
    // summarized integer shape.
    let subject_ty = crate::place_ty_cow(func, &subject)?;
    if frozen_struct_name(subject_ty.as_ref())? != summary.struct_name
        || struct_field_shape(subject_ty.as_ref(), summary.field) != Some(summary.field_ty)
    {
        return None;
    }

    let mut field_place = subject;
    field_place.projections.push(Projection::Field(summary.field));
    let field_var = Formula::Var(crate::place_to_var_name(func, &field_place), Sort::Int);
    let dest_name = crate::place_to_var_name(func, dest);
    let dest_var = Formula::Var(dest_name.clone(), dest_sort);
    let fact = match summary.value {
        ReturnFieldValue::Field => Formula::Eq(Box::new(dest_var), Box::new(field_var)),
        ReturnFieldValue::Compare { op, rhs } => {
            let holds = comparison_formula(op, field_var, Formula::Int(rhs))?;
            Formula::Or(vec![
                Formula::And(vec![dest_var.clone(), holds.clone()]),
                Formula::And(vec![Formula::Not(Box::new(dest_var)), Formula::Not(Box::new(holds))]),
            ])
        }
    };
    Some((fact, *target, dest_name))
}

/// Whether the call terminating `block` is modeled by this family — the D5-A
/// screen's mirror (`refutation_scope::unpinned_local_call_dests`). Asked of the
/// CALL, not of the callee: a recorded summary whose call-site gates fail leaves
/// the destination as free as no summary does.
pub(crate) fn return_field_call_is_modeled(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
) -> bool {
    return_field_callsite_fact(func, block).is_some()
}

/// Trust (TRUST-10): the facts a call to a [`ReturnFieldSummary`] callee adds
/// on its success edge — the relation over the caller's field term, spelled
/// PRE-call and POST-call (module doc). Empty when the model does not fire.
pub(super) fn return_field_callsite_facts(
    sv: &StmtVersionCtx,
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
) -> Vec<Formula> {
    let Some((fact, target, dest_name)) = return_field_callsite_fact(func, block) else {
        return Vec::new();
    };
    let mut facts = Vec::new();
    if let Some(pre) = version_terminator_dest_fact(sv, func, block, &dest_name, fact.clone()) {
        facts.push(pre);
    }
    let post = version_rename_at(&fact, sv, func, target, 0);
    if !facts.contains(&post) {
        facts.push(post);
    }
    facts
}

#[cfg(test)]
mod callsite_subject_tests {
    use trust_types::{
        AdtKind, BasicBlock, BlockId, LocalDecl, Operand, Place, Projection, Rvalue, SourceSpan,
        Statement, Terminator, Ty, UnwindEdge, VerifiableBody, VerifiableFunction,
    };

    use super::callsite_subject_place;

    fn kinded(name: &str, fields: Vec<(String, Ty)>, kind: AdtKind) -> Ty {
        match Ty::adt(name, fields) {
            Ty::Adt {
                adt_kind: _,
                name,
                fields,
                variants,
                disc_index_safe,
                faithful_enum_repr,
                layout,
                enum_layout,
                arbitrary_precision,
                validity_wrapper,
            } => Ty::Adt {
                name,
                fields,
                variants,
                disc_index_safe,
                faithful_enum_repr,
                layout,
                enum_layout,
                arbitrary_precision,
                validity_wrapper,
                adt_kind: Some(kind),
            },
            other => other,
        }
    }

    /// `fn f(w: W) -> bool { w.v.is_empty() }` with `W { v: V, x: u64 }` of the
    /// given kind, `V { nbits: usize }`: `_2 = &(_1.0); _3 = is_empty(move _2)`.
    fn caller_through(owner: AdtKind) -> VerifiableFunction {
        let v = kinded("t::V", vec![("nbits".into(), Ty::usize())], AdtKind::Struct);
        let w = kinded("t::W", vec![("v".into(), v.clone()), ("x".into(), Ty::u64())], owner);
        let local =
            |index, ty, name: Option<&str>| LocalDecl { index, ty, name: name.map(str::to_string) };
        VerifiableFunction {
            name: "f".into(),
            def_path: "t::f".into(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    local(0, Ty::Bool, None),
                    local(1, w, Some("w")),
                    local(2, Ty::Ref { mutable: false, inner: Box::new(v) }, None),
                    local(3, Ty::Bool, None),
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::Ref {
                                mutable: false,
                                place: Place { local: 1, projections: vec![Projection::Field(0)] },
                            },
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Call {
                            func: "t::V::is_empty".into(),
                            args: vec![Operand::Move(Place::local(2))],
                            dest: Place::local(3),
                            target: Some(BlockId(1)),
                            span: SourceSpan::default(),
                            atomic: None,
                            is_foreign: false,
                            is_unsafe_sig: false,
                            unwind: UnwindEdge::Unreachable,
                            callee_identity: None,
                            callee_key: None,
                        },
                    },
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Return,
                    },
                ],
                arg_count: 1,
                return_ty: Ty::Bool,
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
            tuple_layouts: Default::default(),
        }
    }

    /// The control: through a STRUCT field the caller place is `w.v`, so the
    /// gate below is not vacuous.
    #[test]
    fn a_struct_field_hop_names_the_caller_place() {
        let func = caller_through(AdtKind::Struct);
        assert_eq!(
            callsite_subject_place(&func, &Operand::Move(Place::local(2))),
            Some(Place { local: 1, projections: vec![Projection::Field(0)] })
        );
    }

    /// Through a UNION field no place is named: `w.x = ..` overwrites the bytes of
    /// `w.v.nbits` under a different name, so a relation stated over `w.v.nbits`
    /// could outlive the value it describes.
    #[test]
    fn a_union_field_hop_names_no_place() {
        let func = caller_through(AdtKind::Union);
        assert_eq!(callsite_subject_place(&func, &Operand::Move(Place::local(2))), None);
    }
}
