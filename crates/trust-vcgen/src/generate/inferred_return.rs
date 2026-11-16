// Trust (D5-B, 2026-09-24): BODY-INFERRED return equalities — the candidate
// side. The kernel check that turns a candidate into a usable fact lives in the
// compiler (`trust_verify::inferred_return`), because only it links
// `trust-certify`.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

//! # What this is
//!
//! ```text
//! pub fn guard(bit: u32) -> bool { bit < 64 }
//! pub fn shift_via_guard(x: u64, bit: u32) -> Option<u64> {
//!     if !guard(bit) { return None; }
//!     Some(x >> bit)
//! }
//! ```
//!
//! `guard`'s result is a free variable of `shift_via_guard`'s shift query
//! unless something models it. D5-A made that honest (the refutation over the
//! free result is HELD as Unknown); this module is half of what makes it
//! PROVE: for a callee body in a small TOTAL fragment it synthesizes the
//! candidate `_0 == E(params)` and the postcondition check VCs that establish
//! it against the callee's OWN extracted body.
//!
//! # What is trusted, and what is not
//!
//! **The synthesizer is NOT trusted.** [`infer_return_candidate`] only ever
//! proposes. The candidate becomes a fact only if the compiler's Clean CIC
//! kernel certifies EVERY row of [`InferredReturn::check_vcs`] — the ordinary
//! body-aware postcondition VCs this crate generates for an authored
//! `ensures`, over a clone of the callee with every entry hypothesis
//! (`preconditions`, contracts, spec) cleared, so the certified lemma is
//! unconditional. A wrong `E` fails that check and mints nothing.
//!
//! What IS trusted is exactly what an authored-`ensures` composition already
//! trusts: the MIR→`VerifiableFunction` extraction of the callee, this crate's
//! postcondition VC generator binding `_0` at every `Return`, and the call-site
//! rebinding (`rebind_callee_postconditions` / `version_terminator_dest_fact`).
//!
//! # The fragment (every gate fails closed with a named reason)
//!
//! * no authored contract of any kind (the inferred clause must never share a
//!   summary with an unproven authored `ensures` — `contract_skip_ensures_launder`);
//! * the return and temporaries are `bool` or a fixed-width integer of width <=
//!   64; parameters may additionally be unused zero-field structs; at most
//!   [`MAX_PARAMS`] parameters;
//! * parameters are never assigned (and nothing can borrow them: no `Ref`,
//!   `AddressOf` or projection is admitted anywhere), so `E` over the
//!   parameters is `E` over the ENTRY values;
//! * statements: whole-local `Assign` of a copy/move/constant, an integer or
//!   bool comparison, bool `!`, bool `&`/`|`/`^`; storage markers and no-ops;
//! * terminators: `Goto`, `SwitchInt` over a bool or integer local, and exactly
//!   one `Return` block; the CFG is acyclic. Calls require exact typed candidate
//!   inputs or the existing wrapping-add/sub primitive model; arbitrary calls,
//!   `Assert`, `Drop`, `Unreachable` and inline asm remain outside the scalar
//!   fragment. Every callee and caller original-body row still needs its own
//!   kernel check before the composed candidate can become a fact.
//!
//! No arithmetic of any kind is admitted, so `E` is exact over mathematical
//! integers (no wrap, no overflow), which is also what lets the call-site
//! injector (`summary_may_inject_postcondition`, which refuses unmodeled machine
//! arithmetic) accept it.
//!
//! The separate enum fragment additionally accepts positively declared scalar
//! payload/fieldless enums and tuple copies used by decision tables. It proposes
//! the exact declared-tag domains and a Bool result relation; every original
//! postcondition AND exhaustive-match `Unreachable` row must kernel-check.
//! Typed, sealed entry bindings use canonical discriminators independently of
//! payload projections. Caller enums must have immutable, unaliased roots;
//! identity and all original compiler mint/use gates remain mandatory.
//! Scalar return candidates retain the same original clause and check rows,
//! with private parameter/result type bindings for this shared call rule.

use super::*;

pub(crate) mod calls;
mod entry_bindings;
mod enum_return;
pub use calls::InferredReturnCall;
pub(crate) use entry_bindings::EntryBindings;

/// Node cap on the synthesized `E` (and hence on the injected clause).
pub const INFERRED_RETURN_MAX_NODES: usize = 256;
/// Parameter cap. Beyond this the lemma is unlikely to be a guard helper.
pub const MAX_PARAMS: usize = 8;
/// Block cap on the callee body.
const MAX_BLOCKS: usize = 32;
/// Cap on block evaluations during symbolic execution (paths are enumerated,
/// so a chain of diamonds is exponential; this bounds it).
const MAX_BLOCK_VISITS: usize = 64;
/// Cap on the number of postcondition check rows a candidate may need.
pub const MAX_CHECK_VCS: usize = 16;

/// Cost preflight for reading a return-dependency body. This deliberately does
/// not classify its return type or grant a call fact: the shared synthesizer,
/// exact item identity and every original-body proof remain mandatory.
/// Contracted callers may request child facts without becoming facts themselves.
#[must_use]
pub fn return_dependency_body_within_budget(function: &VerifiableFunction) -> bool {
    let body = &function.body;
    body.arg_count <= MAX_PARAMS
        && body.locals.len() <= 128
        && body.blocks.len() <= MAX_BLOCKS
        && body
            .blocks
            .iter()
            .try_fold(0usize, |count, block| count.checked_add(block.stmts.len()))
            .is_some_and(|count| count <= 256)
}

/// A candidate body-inferred return equality, with the VCs that establish it.
///
/// Constructible ONLY by [`infer_return_candidate`]: every field is private, so
/// a caller cannot hand the summary builder
/// ([`crate::modular::FunctionSummary::with_body_inferred_return`]) a clause the
/// synthesizer did not produce from a real body. That does not make it a fact —
/// the compiler must still kernel-certify [`Self::check_vcs`] — but it narrows
/// the builder's input to synthesizer output.
#[derive(Debug, Clone)]
pub struct InferredReturn {
    def_path: String,
    param_names: Vec<String>,
    postcondition: Formula,
    check_vcs: Vec<VerificationCondition>,
    entry_bindings: Option<EntryBindings>,
}

impl InferredReturn {
    /// The callee's extracted `def_path`.
    #[must_use]
    pub fn def_path(&self) -> &str {
        &self.def_path
    }

    /// The callee's formal names, positional, exactly as the check VCs and the
    /// postcondition spell them (the extractor's own rendering, not HIR idents).
    #[must_use]
    pub fn param_names(&self) -> &[String] {
        &self.param_names
    }

    /// The candidate `_0 == E(params)`, with checked enum domains when present.
    #[must_use]
    pub fn postcondition(&self) -> &Formula {
        &self.postcondition
    }

    /// The body-aware postcondition VCs over the contract-free callee clone,
    /// including exhaustive-match Unreachable obligations for enum candidates.
    /// Every one must be kernel-certified before the candidate is used.
    #[must_use]
    pub fn check_vcs(&self) -> &[VerificationCondition] {
        &self.check_vcs
    }

    pub(crate) fn entry_bindings(&self) -> Option<&EntryBindings> {
        self.entry_bindings.as_ref()
    }
}

fn fragment_scalar(ty: &Ty) -> bool {
    match ty {
        Ty::Bool => true,
        Ty::Int { width, .. } => (1..=64).contains(width),
        _ => false,
    }
}

/// A dataless argument contributes no value to the inferred expression. This
/// admits only its parameter declaration: temporaries and the result remain
/// scalar, and the ordinary evaluator still rejects its reads, writes, borrows,
/// calls and drops. In particular, a zero-field enum is not a unit struct.
fn fragment_empty_parameter(ty: &Ty) -> bool {
    matches!(ty, Ty::Adt {
        fields,
        variants,
        adt_kind: Some(trust_types::AdtKind::Struct),
        ..
    } if fields.is_empty() && variants.is_empty())
}

/// Scan every block, including unreachable blocks. A declaration-only parameter
/// must not become a hidden value or effect dependency of a later fragment
/// extension. Unknown statement/rvalue/operand/terminator shapes refuse it.
fn empty_parameter_is_unused(func: &VerifiableFunction, local: usize) -> bool {
    let place_omits = |place: &Place| {
        place.local != local
            && !place.projections.iter().any(
                |projection| matches!(projection, trust_types::Projection::Index(i) if *i == local),
            )
    };
    let operand_omits = |operand: &Operand| match operand {
        Operand::Copy(place) | Operand::Move(place) => place_omits(place),
        Operand::Constant(_) => true,
        _ => false,
    };
    func.body.blocks.iter().all(|block| {
        block.stmts.iter().all(|stmt| match stmt {
            Statement::StorageLive(_)
            | Statement::StorageDead(_)
            | Statement::Coverage
            | Statement::ConstEvalCounter
            | Statement::Nop => true,
            Statement::Assign { place, rvalue, .. } => {
                place_omits(place)
                    && match rvalue {
                        Rvalue::Use(op) | Rvalue::UnaryOp(_, op) => operand_omits(op),
                        Rvalue::BinaryOp(_, lhs, rhs) => operand_omits(lhs) && operand_omits(rhs),
                        _ => false,
                    }
            }
            _ => false,
        }) && match &block.terminator {
            Terminator::Goto(_) | Terminator::Return => true,
            Terminator::SwitchInt { discr, .. } => operand_omits(discr),
            Terminator::Call { args, dest, .. } => {
                place_omits(dest) && args.iter().all(operand_omits)
            }
            _ => false,
        }
    })
}

fn local_ty(func: &VerifiableFunction, local: usize) -> Option<&Ty> {
    // A duplicated index is ambiguous: `unique_local_decl` refuses rather than pick one.
    crate::unique_local_decl(func, local).map(|decl| &decl.ty)
}

#[inline]
fn local_ty_with(func: &VerifiableFunction, local: usize, positional_locals: bool) -> Option<&Ty> {
    if positional_locals {
        func.body.locals.get(local).map(|decl| &decl.ty)
    } else {
        local_ty(func, local)
    }
}

fn whole_local(place: &Place) -> Option<usize> {
    place.projections.is_empty().then_some(place.local)
}

/// The fragment type of an operand: a whole local's declared type, or the
/// constant's own kind.
fn operand_ty<'a>(
    func: &'a VerifiableFunction,
    op: &Operand,
    positional_locals: bool,
) -> Option<&'a Ty> {
    match op {
        Operand::Copy(place) | Operand::Move(place) => {
            let ty = local_ty_with(func, whole_local(place)?, positional_locals)?;
            fragment_scalar(ty).then_some(ty)
        }
        _ => None,
    }
}

struct SymExec<'a> {
    func: &'a VerifiableFunction,
    visits: usize,
    positional_locals: bool,
    positional_blocks: bool,
}

type Env = Vec<Option<Formula>>;

impl<'a> SymExec<'a> {
    fn block(&self, id: BlockId) -> Result<&'a trust_types::BasicBlock, &'static str> {
        if self.positional_blocks {
            return self.func.body.blocks.get(id.0).ok_or("missing block");
        }
        let mut found = self.func.body.blocks.iter().filter(|block| block.id == id);
        let block = found.next().ok_or("missing block")?;
        if found.next().is_some() {
            return Err("duplicate block id");
        }
        Ok(block)
    }

    fn read(&self, env: &Env, op: &Operand, want: &Ty) -> Result<Formula, &'static str> {
        match op {
            Operand::Copy(place) | Operand::Move(place) => {
                let local = whole_local(place).ok_or("projected operand")?;
                let ty = local_ty_with(self.func, local, self.positional_locals)
                    .ok_or("undeclared local")?;
                if ty != want {
                    return Err("operand type mismatch");
                }
                env.get(local).cloned().flatten().ok_or("read before write")
            }
            Operand::Constant(value) => {
                let ok = match (value, want) {
                    (ConstValue::Bool(_), Ty::Bool) => true,
                    (ConstValue::Int(_) | ConstValue::Uint(..), Ty::Int { .. }) => true,
                    _ => false,
                };
                if !ok {
                    return Err("constant outside the fragment");
                }
                // The generator's own constant rendering, so the candidate and
                // the check VCs spell the literal identically.
                match operand_to_formula(self.func, op) {
                    f @ (Formula::Bool(_) | Formula::Int(_)) => Ok(f),
                    _ => Err("constant renders outside Int/Bool"),
                }
            }
            _ => Err("operand outside the fragment"),
        }
    }

    fn rvalue(&self, env: &Env, rvalue: &Rvalue, dest_ty: &Ty) -> Result<Formula, &'static str> {
        match rvalue {
            Rvalue::Use(op) => self.read(env, op, dest_ty),
            Rvalue::UnaryOp(trust_types::UnOp::Not, op) => {
                if *dest_ty != Ty::Bool {
                    return Err("integer `!` is bitwise arithmetic");
                }
                Ok(Formula::Not(Box::new(self.read(env, op, &Ty::Bool)?)))
            }
            Rvalue::BinaryOp(op, lhs, rhs) => {
                if *dest_ty != Ty::Bool {
                    return Err("binary op producing a non-bool (arithmetic)");
                }
                // The operand type: a whole local fixes it; two constants are
                // never emitted by rustc for these ops, so refuse that shape.
                let operand_ty = operand_ty(self.func, lhs, self.positional_locals)
                    .or_else(|| operand_ty(self.func, rhs, self.positional_locals))
                    .ok_or("binary op with no typed local operand")?;
                let l = self.read(env, lhs, operand_ty)?;
                let r = self.read(env, rhs, operand_ty)?;
                match (operand_ty, op) {
                    (Ty::Int { .. }, _) => callee_summaries::comparison_formula(*op, l, r)
                        .ok_or("integer non-comparison"),
                    (Ty::Bool, BinOp::Eq) => Ok(Formula::Eq(Box::new(l), Box::new(r))),
                    (Ty::Bool, BinOp::Ne | BinOp::BitXor) => {
                        Ok(Formula::Not(Box::new(Formula::Eq(Box::new(l), Box::new(r)))))
                    }
                    (Ty::Bool, BinOp::BitAnd) => Ok(Formula::And(vec![l, r])),
                    (Ty::Bool, BinOp::BitOr) => Ok(Formula::Or(vec![l, r])),
                    _ => Err("bool op outside the fragment"),
                }
            }
            _ => Err("rvalue outside the fragment"),
        }
    }

    /// The value `_0` holds when `block` (entered with `env`) reaches `Return`.
    fn eval(&mut self, id: BlockId, mut env: Env) -> Result<Formula, &'static str> {
        self.visits += 1;
        if self.visits > MAX_BLOCK_VISITS {
            return Err("path budget exceeded");
        }
        let block = self.block(id)?;
        for stmt in &block.stmts {
            match stmt {
                Statement::StorageLive(_)
                | Statement::StorageDead(_)
                | Statement::Nop
                | Statement::Coverage
                | Statement::ConstEvalCounter => {}
                Statement::Assign { place, rvalue, .. } => {
                    let local = whole_local(place).ok_or("projected assignment")?;
                    if (1..=self.func.body.arg_count).contains(&local) {
                        return Err("parameter reassigned");
                    }
                    let ty = local_ty_with(self.func, local, self.positional_locals)
                        .ok_or("undeclared local")?;
                    let value = self.rvalue(&env, rvalue, ty)?;
                    *env.get_mut(local).ok_or("local index out of range")? = Some(value);
                }
                _ => return Err("statement outside the fragment"),
            }
        }
        match &block.terminator {
            Terminator::Goto(next) => self.eval(*next, env),
            // Trust (W5 Stage 1, 2026-09-25): ONE call form, the wrapping add/sub
            // primitive. Everything else stays outside the fragment.
            //
            // WIDTH IS PER NODE AND CROSS-CHECKED, never ambient. `PrimitiveCallee`
            // supplies the callee's own width and the destination local's declared type
            // must agree; a skew REFUSES. The adversary pass that priced this increment
            // found the false proof in the alternative: a chain folded at one ambient
            // width mints `_0 == 0` for a body that returns 2^32, because
            // `AdmissibleBody::Arithmetic` carries no width at all and nothing forces a
            // chain to be width-uniform. There is no ambient width here to get wrong.
            //
            // The formula is built by the SHARED `wrapping_binop_modular_ite` — never a
            // second spelling of the same semantics. That is load-bearing twice over:
            // the extractor mints the identical term for the same primitive elsewhere,
            // and `machine_faithful_clause_admissible` (which decides whether this
            // clause may be CHECKED rather than declared unverifiable) is
            // constructor-verified against exactly that builder at the resolved domain.
            call @ Terminator::Call { func, args, dest, target, .. } => {
                let Some(next) = target else {
                    return Err("call terminator with no return edge");
                };
                if let Some(callee) = crate::inferred_return_call_for(self.func, call) {
                    let value = callee.value_in_state(
                        self.func,
                        call,
                        env.iter().enumerate().filter_map(|(local, value)| {
                            value.as_ref().map(|value| (local, value))
                        }),
                    )?;
                    *env.get_mut(dest.local).ok_or("local index out of range")? = Some(value);
                    return self.eval(*next, env);
                }
                if !dest.projections.is_empty() {
                    return Err("call destination is not a bare local");
                }
                let (op, width) =
                    match trust_types::admissible_body::PrimitiveCallee::classify(func) {
                        Some(trust_types::admissible_body::PrimitiveCallee::WrappingAdd(w)) => {
                            (BinOp::Add, w)
                        }
                        Some(trust_types::admissible_body::PrimitiveCallee::WrappingSub(w)) => {
                            (BinOp::Sub, w)
                        }
                        // `WrappingMul` is refused for the reason
                        // `clean_origin_wrapping_binop_postconditions` already records
                        // for its own Mul arm; this lane does not reopen it.
                        _ => return Err("call outside the fragment"),
                    };
                let [lhs, rhs] = args.as_slice() else {
                    return Err("wrapping primitive with other than two arguments");
                };
                // THE CROSS-CHECK. The callee says the operation is at `width`; the
                // destination local says what the result is stored as. If they disagree
                // the body is not the thing this clause would describe.
                let dest_ty = local_ty_with(self.func, dest.local, self.positional_locals)
                    .ok_or("undeclared destination")?;
                match dest_ty {
                    Ty::Int { width: dest_width, signed: false } if *dest_width == width => {}
                    _ => return Err("wrapping primitive width disagrees with its destination"),
                }
                let lhs_ty = operand_ty(self.func, lhs, self.positional_locals)
                    .ok_or("untyped wrapping operand")?;
                let rhs_ty = operand_ty(self.func, rhs, self.positional_locals)
                    .ok_or("untyped wrapping operand")?;
                if lhs_ty != dest_ty || rhs_ty != dest_ty {
                    return Err("wrapping primitive operand width disagrees with its result");
                }
                let lhs_f = self.read(&env, lhs, lhs_ty)?;
                let rhs_f = self.read(&env, rhs, rhs_ty)?;
                let value = super::assert_refutation::wrapping_binop_modular_ite(
                    op, &lhs_f, &rhs_f, width, false,
                )
                .ok_or("wrapping primitive outside the modelled width range")?;
                let mut env = env;
                *env.get_mut(dest.local).ok_or("local index out of range")? = Some(value);
                self.eval(*next, env)
            }
            Terminator::Return => {
                env.first().cloned().flatten().ok_or("return before `_0` is written")
            }
            Terminator::SwitchInt { discr, targets, otherwise, .. } => {
                let discr_ty = operand_ty(self.func, discr, self.positional_locals)
                    .ok_or("switch on a non-local")?;
                let d = self.read(&env, discr, discr_ty)?;
                let mut seen = (targets.len() > 8).then(FxHashSet::default);
                let mut arms = Vec::with_capacity(targets.len());
                for (idx, (value, target)) in targets.iter().enumerate() {
                    let dup = match &mut seen {
                        Some(set) => !set.insert(*value),
                        None => targets[..idx].iter().any(|(prev, _)| prev == value),
                    };
                    if dup {
                        return Err("duplicate switch label");
                    }
                    let cond = match discr_ty {
                        Ty::Bool => match value {
                            0 => Formula::Not(Box::new(d.clone())),
                            1 => d.clone(),
                            _ => return Err("bool switch label outside {0, 1}"),
                        },
                        _ => Formula::Eq(
                            Box::new(d.clone()),
                            Box::new(
                                crate::switch_label_to_formula(discr_ty, *value)
                                    .ok_or("undecodable switch label")?,
                            ),
                        ),
                    };
                    arms.push((cond, *target));
                }
                if arms.is_empty() {
                    return self.eval(*otherwise, env);
                }
                let mut result = self.eval(*otherwise, env.clone())?;
                let mut iter = arms.into_iter().rev().peekable();
                while let Some((cond, target)) = iter.next() {
                    let branch_env =
                        if iter.peek().is_some() { env.clone() } else { std::mem::take(&mut env) };
                    let then = self.eval(target, branch_env)?;
                    result = Formula::Ite(Box::new(cond), Box::new(then), Box::new(result));
                }
                Ok(result)
            }
            _ => Err("terminator outside the fragment"),
        }
    }
}

#[cfg(test)]
fn node_count(formula: &Formula) -> usize {
    let mut nodes = 0usize;
    trust_types::visit_formula_nodes(formula, &mut |_| nodes += 1);
    nodes
}

fn node_count_exceeds(formula: &Formula, limit: usize) -> bool {
    let mut nodes = 0usize;
    trust_types::any_formula_node(formula, &mut |_| {
        nodes += 1;
        nodes > limit
    })
}

/// Whether the CFG reachable from `entry` is acyclic (iterative three-colour
/// DFS; a missing successor is reported by the evaluator, not here).
fn acyclic_from(func: &VerifiableFunction, entry: BlockId) -> bool {
    #[derive(Clone, Copy, PartialEq)]
    enum Colour {
        Grey,
        Black,
    }
    let blocks = &func.body.blocks;
    let positional_blocks = blocks.iter().enumerate().all(|(i, block)| block.id.0 == i);
    let nth_successor = |id: BlockId, idx: usize| -> Option<BlockId> {
        let block = if positional_blocks {
            blocks.get(id.0)?
        } else {
            blocks
                .get(id.0)
                .filter(|block| block.id == id)
                .or_else(|| blocks.iter().find(|block| block.id == id))?
        };
        match &block.terminator {
            Terminator::Goto(next) | Terminator::Call { target: Some(next), .. } => {
                (idx == 0).then_some(*next)
            }
            Terminator::SwitchInt { targets, otherwise, .. } => {
                if idx == 0 {
                    Some(*otherwise)
                } else {
                    targets.get(targets.len().checked_sub(idx)?).map(|(_, t)| *t)
                }
            }
            _ => None,
        }
    };
    if positional_blocks {
        if entry.0 >= blocks.len() {
            return true;
        }
        // 0 = unvisited, 1 = Grey, 2 = Black
        let mut colour = vec![0u8; blocks.len()];
        let mut stack: Vec<(BlockId, usize)> = Vec::with_capacity(blocks.len());
        colour[entry.0] = 1;
        stack.push((entry, 0));
        while let Some((node, next_idx)) = stack.last_mut() {
            let cur = *node;
            let idx = *next_idx;
            if let Some(next) = nth_successor(cur, idx) {
                *next_idx += 1;
                match colour.get(next.0).copied() {
                    Some(1) => return false,
                    Some(2) | None => {}
                    Some(_) => {
                        colour[next.0] = 1;
                        stack.push((next, 0));
                    }
                }
            } else {
                colour[cur.0] = 2;
                stack.pop();
            }
        }
        return true;
    }
    let mut colour: FxHashMap<BlockId, Colour> = FxHashMap::default();
    let mut stack: Vec<(BlockId, usize)> = vec![(entry, 0)];
    colour.insert(entry, Colour::Grey);
    while let Some((node, next_idx)) = stack.last_mut() {
        let cur = *node;
        let idx = *next_idx;
        if let Some(next) = nth_successor(cur, idx) {
            *next_idx += 1;
            match colour.get(&next) {
                Some(Colour::Grey) => return false,
                Some(Colour::Black) => {}
                None => {
                    colour.insert(next, Colour::Grey);
                    stack.push((next, 0));
                }
            }
        } else {
            colour.insert(cur, Colour::Black);
            stack.pop();
        }
    }
    true
}

/// Synthesize the candidate `_0 == E(params)` for `func`, or name the gate it
/// fails. See the module doc for the fragment. `Ok` is a CANDIDATE: it carries
/// no authority until every [`InferredReturn::check_vcs`] row is kernel-certified.
pub fn infer_return_candidate(func: &VerifiableFunction) -> Result<InferredReturn, &'static str> {
    // Cheap structural gates first: this runs over every body in the crate.
    if !func.contracts.is_empty() || !func.postconditions.is_empty() || !func.spec.is_empty() {
        return Err("authored contract present");
    }
    if (1..=func.body.arg_count)
        .any(|index| local_ty(func, index).is_some_and(crate::enum_entry::enum_shape))
    {
        return enum_return::infer(func);
    }
    let (param_names, postcondition) = scalar_return_equation(func)?;
    let arg_count = func.body.arg_count;
    let check_vcs = inferred_return_check_vcs(func, &postcondition)?;
    // Keep the existing candidate and original check rows byte-for-byte. The
    // extra private binding lets the shared call rule consume a scalar
    // candidate after its original rows have been independently checked.
    let entry_bindings = (fragment_scalar(&func.body.return_ty)
        && local_ty(func, 0) == Some(&func.body.return_ty)
        && (1..=arg_count).all(|local| local_ty(func, local).is_some_and(fragment_scalar)))
    .then(|| EntryBindings {
        return_ty: func.body.return_ty.clone(),
        parameters: param_names
            .iter()
            .enumerate()
            .map(|(index, name)| (name.clone(), func.body.locals[index + 1].ty.clone()))
            .collect(),
        accesses: Vec::new(),
        postcondition: postcondition.clone(),
        def_path: func.def_path.clone(),
    });
    Ok(InferredReturn {
        def_path: func.def_path.clone(),
        param_names,
        postcondition,
        check_vcs,
        entry_bindings,
    })
}

/// The existing bounded scalar evaluator, shared by candidate synthesis and
/// source-clause correspondence. Contracts are irrelevant to evaluation here:
/// callers retain and bind their original clauses separately. This returns
/// semantic data only; it neither generates nor certifies a new obligation.
pub(super) fn scalar_return_equation(
    func: &VerifiableFunction,
) -> Result<(Vec<String>, Formula), &'static str> {
    let arg_count = func.body.arg_count;
    if arg_count > MAX_PARAMS {
        return Err("too many parameters");
    }
    if func.body.blocks.is_empty() || func.body.blocks.len() > MAX_BLOCKS {
        return Err("block count outside the fragment");
    }
    // Only a PARAMETER may be a dataless struct. Every other local remains a
    // fragment scalar, and indices are exactly 0..n (so `Env` indexing is total
    // and unambiguous). No value-level rule is added for the struct: the existing
    // evaluator and the kernel check must still establish the scalar return.
    let n_locals = func.body.locals.len();
    let positional_locals = func.body.locals.iter().enumerate().all(|(i, decl)| decl.index == i);
    for index in 0..n_locals {
        let ty =
            local_ty_with(func, index, positional_locals).ok_or("non-positional local table")?;
        if !fragment_scalar(ty) {
            if !((1..=arg_count).contains(&index) && fragment_empty_parameter(ty)) {
                return Err("local of a non-scalar type");
            }
            if !empty_parameter_is_unused(func, index) {
                return Err("dataless parameter is used");
            }
        }
    }
    if arg_count >= n_locals {
        return Err("parameter count exceeds the local table");
    }
    // Exactly one `Return` block, and every terminator in the body (reachable or
    // not) inside the fragment.
    let mut returns = 0usize;
    for block in &func.body.blocks {
        match &block.terminator {
            Terminator::Return => returns += 1,
            Terminator::Goto(_) | Terminator::SwitchInt { .. } => {}
            call @ Terminator::Call { .. }
                if crate::inferred_return_call_for(func, call).is_some() => {}
            // Trust (W5 Stage 1): admitted in the shape scan only for the one primitive
            // the evaluator models; the evaluator re-classifies and refuses anything
            // else, so this is not the authority.
            Terminator::Call { func, target: Some(_), .. }
                if matches!(
                    trust_types::admissible_body::PrimitiveCallee::classify(func),
                    Some(
                        trust_types::admissible_body::PrimitiveCallee::WrappingAdd(_)
                            | trust_types::admissible_body::PrimitiveCallee::WrappingSub(_)
                    )
                ) => {}
            _ => return Err("terminator outside the fragment"),
        }
    }
    if returns != 1 {
        return Err("not exactly one Return block");
    }
    let _analysis = super::FuncAnalysisScope::enter_if_unbound(func);
    if super::body_contains_memory_image_for(func) {
        return Err("memory image");
    }
    crate::validate_function(func).map_err(|_| "malformed function")?;
    let entry = BlockId(0);
    if !func.body.blocks.iter().any(|block| block.id == entry) {
        return Err("no entry block");
    }
    if !acyclic_from(func, entry) {
        return Err("cyclic control flow");
    }

    // Parameter and result spellings, from the generator's own renderer.
    let render = |local: usize| operand_to_formula(func, &Operand::Copy(Place::local(local)));
    let result_var = render(0);
    if !matches!(&result_var, Formula::Var(name, _) if name == "_0") {
        return Err("return slot does not render as `_0`");
    }
    let mut env: Env = vec![None; n_locals];
    let mut param_names = Vec::with_capacity(arg_count);
    for local in 1..=arg_count {
        let var = render(local);
        let Formula::Var(name, _) = &var else {
            return Err("parameter does not render as a variable");
        };
        if name == "_0" || param_names.contains(name) {
            return Err("ambiguous parameter spelling");
        }
        param_names.push(name.clone());
        env[local] = Some(var);
    }

    let positional_blocks = func.body.blocks.iter().enumerate().all(|(i, block)| block.id.0 == i);
    let mut exec = SymExec { func, visits: 0, positional_locals, positional_blocks };
    let value = exec.eval(entry, env)?;
    if node_count_exceeds(&value, INFERRED_RETURN_MAX_NODES) {
        return Err("inferred expression too large");
    }
    if !trust_types::all_free_variable_names(&value, &mut |v| param_names.iter().any(|p| p == v)) {
        return Err("inferred expression mentions a non-parameter");
    }
    let postcondition = Formula::Eq(Box::new(result_var), Box::new(value));
    Ok((param_names, postcondition))
}

/// The body-aware postcondition VCs that establish `postcondition` against
/// `func`'s own body, generated by the ordinary pipeline over a clone with every
/// entry hypothesis cleared (so what they establish is unconditional).
///
/// Refuses unless the generation yields at least one row and EVERY row is a
/// `VcKind::Postcondition` (anything else — an `UnsupportedMir`, a safety row —
/// means the body is not the total fragment the caller assumes).
///
/// Public so a test can drive a deliberately WRONG `postcondition` through the
/// same check the compiler runs and see the kernel refuse it.
pub fn inferred_return_check_vcs(
    func: &VerifiableFunction,
    postcondition: &Formula,
) -> Result<Vec<VerificationCondition>, &'static str> {
    return_check_vcs(func, postcondition, false)
}

/// Original-body checks for a pure enum helper also retain the impossible
/// default edge of an exhaustive match. That edge is an OBLIGATION, never an
/// assumed fact: the compiler must kernel-certify it along with every return
/// row. The scalar/constructor entry above remains postcondition-only.
pub fn inferred_enum_return_check_vcs(
    func: &VerifiableFunction,
    postcondition: &Formula,
) -> Result<Vec<VerificationCondition>, &'static str> {
    if !(1..=func.body.arg_count).any(|index| {
        matches!(local_ty(func, index),
        Some(Ty::Adt { adt_kind: Some(trust_types::AdtKind::Enum), variants, .. })
        if !variants.is_empty())
    }) {
        return Err("no declared enum parameter");
    }
    return_check_vcs(func, postcondition, true)
}

fn return_check_vcs(
    func: &VerifiableFunction,
    postcondition: &Formula,
    retain_unreachable: bool,
) -> Result<Vec<VerificationCondition>, &'static str> {
    let mut probe = func.clone();
    probe.preconditions.clear();
    probe.postconditions = vec![postcondition.clone()];
    probe.contracts.clear();
    probe.spec = Default::default();
    // The cleared hypothesis is the question (unconditional), so the generator does not
    // restate the parameters' type ranges into it (`without_stated_param_ranges`).
    let vcs = super::without_stated_param_ranges(|| {
        if let Some(summaries) = calls::database(&probe) {
            // Trust: keep the scoped exact-call inputs while checking the
            // unchanged original body with the ordinary summary injector.
            super::entry::generate_vcs_impl(&probe, Some(&summaries), false, &FxHashSet::default())
        } else {
            super::generate_vcs(&probe)
        }
    });
    if vcs.is_empty() {
        return Err("no postcondition check row generated");
    }
    if vcs.len() > MAX_CHECK_VCS {
        return Err("too many check rows");
    }
    if !vcs.iter().all(|vc| {
        matches!(vc.kind, VcKind::Postcondition)
            || (retain_unreachable && matches!(vc.kind, VcKind::Unreachable))
    }) {
        return Err("check generation produced a non-postcondition row");
    }
    if !vcs.iter().any(|vc| matches!(vc.kind, VcKind::Postcondition)) {
        return Err("no postcondition check row generated");
    }
    Ok(vcs)
}

/// [`infer_return_candidate`] into the caller's context `rows` (T3 C07p, design D-VC-1):
/// a candidate's check rows are interned through the row oracle, and the candidate is
/// returned as synthesized. A declined body interns nothing.
///
/// # Errors
///
/// The gate the body fails, as [`infer_return_candidate`].
pub fn infer_return_candidate_rows(
    func: &VerifiableFunction,
    rows: &mut trust_types::vc_context::VcContext,
) -> Result<InferredReturn, &'static str> {
    let candidate = infer_return_candidate(func)?;
    super::intern_eager_rows(rows, candidate.check_vcs());
    Ok(candidate)
}

/// Compose previously kernel-checked callee candidates in a fresh owner-bound
/// context. Every ORIGINAL caller row must still independently kernel-check
/// before the compiler may reuse the resulting candidate.
pub fn infer_return_candidate_with_calls_rows(
    func: &VerifiableFunction,
    callees: &[InferredReturnCall],
    rows: &mut trust_types::vc_context::VcContext,
) -> Result<InferredReturn, &'static str> {
    with_inferred_return_calls(func, callees, || infer_return_candidate_rows(func, rows))?
}

/// Candidate context only. The caller remains responsible for checking every
/// original callee obligation before treating the generated rows as evidence.
pub(crate) fn with_inferred_return_calls<R>(
    func: &VerifiableFunction,
    callees: &[InferredReturnCall],
    f: impl FnOnce() -> R,
) -> Result<R, &'static str> {
    if callees.len() > 32 {
        return Err("too many inferred callees");
    }
    let mut names = FxHashSet::default();
    let mut calls = FxHashMap::default();
    for callee in callees {
        if !names.insert(callee.name()) || calls.insert(callee.identity(), callee.clone()).is_some()
        {
            return Err("ambiguous inferred callee");
        }
    }
    let summaries = crate::CalleeSummaryContext::default().with_inferred_return_calls(calls);
    let context =
        crate::VcgenContext::for_function(func.def_path.clone()).with_callee_summaries(summaries);
    Ok(crate::with_vcgen_context(&context, f))
}

#[cfg(test)]
#[path = "inferred_return_tests.rs"]
mod tests;
