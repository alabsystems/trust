// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Trust (Clean R80; Clean R151 consumer (1); `docs/DECISION_QUEUE.md`
//! R80-CONSUMERS-1): `@[implemented_by]` and `@[extern]` on the Clean-origin
//! call lane.
//!
//! Pinned Lean, and Clean's compiled lanes since R80, never run the kernel
//! value of a declaration that carries either attribute: `@[implemented_by f]`
//! runs `f` (`clean_compiler::constant_to_decl` substitutes the end of the
//! chain at every reference, and refuses every declaration of an environment
//! whose ORDER record is not empty: `attribute [implemented_by]` written after
//! code that reaches the declaration; `clean_compiler::implemented_by_order`),
//! and `@[extern "sym"]` calls the external symbol `sym` (Clean's native walk
//! refuses a reached source-registered one, `native-extern` /
//! `native-extern-body`, R80 item 5). clean-compiler's own predicate for
//! "compiled code never runs this constant's value" is the pair
//! (`implemented_by::has_compiler_attr`). This lane does neither. It plans from
//! KERNEL VALUES (the declaration's own, its named callees' through
//! `named_calls`, whatever the inductive-projection proof unfolds) and the gate
//! proves the emitted body equal to those values, so either attribute anywhere
//! in what the value reaches would make Rust compute the logical body where
//! Lean and Clean run something else: a wrong answer at exit 0. So the lane
//! refuses:
//!
//! * every declaration of an environment whose order record is not empty, with
//!   clean-compiler's own refusal text, naming the least recorded constant as
//!   `constant_to_decl` does ([`refuse_order`]);
//! * a declaration that carries either attribute, or whose value reaches a
//!   constant that does, transitively through the values of the constants it
//!   names ([`refuse_reached_binding`]); the named-call expansion refuses such
//!   a callee by itself as well ([`bound_callee`]), because the kernel-TV
//!   source side calls it without the planner.
//!
//! Over-refusal, stated: a binding reached only through a proof inside a value,
//! or one whose implementation agrees with the value, is refused too; and a
//! closure larger than the walk's bound is refused rather than assumed free.
//! Each is fail-closed. At Trust's Clean pin only source elaboration registers
//! either attribute (neither the builtin prelude nor `.olean` import does), so
//! an island that writes neither plans exactly as before. A Clean pin whose
//! import registers a module's own rows (Clean R149) makes imported runtime
//! primitives (`Nat.add`'s `@[extern "lean_nat_add"]`) bindings here too; that
//! pin move must narrow the check to what this lane does not emit as a
//! primitive, as Clean's walk skips `is_primitive_denylisted`, or this lane
//! refuses those callers (fail-closed until then).

use std::cell::{Cell, RefCell};
use std::collections::{HashSet, VecDeque};

use clean_kernel::{ConstantKind, Environment, Expr, ExprFolderOpt, ExprKind, Name};

use crate::emit::EmitRefusal;

/// The most constants the binding walk visits before it refuses.
const MAX_CONSTANTS: usize = 100_000;
/// The most expression nodes it enters, over all of them.
const MAX_NODES: usize = 4_000_000;

/// Why compiled code would not run the kernel value this lane plans from.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum NotRun {
    /// An `@[implemented_by]` binding, the order record, or a closure the walk
    /// could not finish.
    ImplementedBy(String),
    /// An `@[extern]` binding.
    Extern(String),
}

impl NotRun {
    /// The refusal of planned declaration `name`.
    pub(crate) fn refusal(self, name: &str) -> EmitRefusal {
        let name = name.to_owned();
        match self {
            Self::ImplementedBy(reason) => EmitRefusal::ImplementedBy { name, reason },
            Self::Extern(reason) => EmitRefusal::Extern { name, reason },
        }
    }

    /// The reason alone, for the named-call expansion's `String` errors.
    pub(crate) fn into_reason(self) -> String {
        match self {
            Self::ImplementedBy(reason) | Self::Extern(reason) => reason,
        }
    }
}

/// The order refusal, when `env`'s order record is not empty: the text of
/// `clean_compiler::CompilerError::ImplementedByOrder` for the least recorded
/// constant by name, which is what `constant_to_decl` returns for it.
pub(crate) fn refuse_order(env: &Environment) -> Result<(), String> {
    let Some(record) = clean_compiler::implemented_by_order(env) else {
        return Ok(());
    };
    match record.iter().min_by_key(|(referrer, _)| referrer.to_string()) {
        Some((referrer, why)) => Err(clean_compiler::CompilerError::ImplementedByOrder {
            referrer: referrer.clone(),
            rebound: why.rebound.clone(),
            via: why.via.clone(),
        }
        .to_string()),
        None => Ok(()),
    }
}

/// The refusal of a declaration that carries a binding itself.
fn bound_declaration(declaration: &Name, implementation: &Name) -> String {
    format!(
        "`{declaration}` is @[implemented_by {implementation}]: compiled code runs the \
         implementation, and this lane would emit the kernel value of `{declaration}` instead \
         (implemented-by). Options: call `{implementation}` from Rust, or remove the attribute."
    )
}

/// The refusal of a declaration whose value reaches `bound`, which `named_by`'s
/// value names.
fn reached_binding(bound: &Name, implementation: &Name, named_by: &Name) -> String {
    format!(
        "it reaches `{bound}` (named by `{named_by}`), which is @[implemented_by \
         {implementation}]: compiled code runs the implementation, and this lane would emit the \
         kernel value of `{bound}` instead (implemented-by). Options: call `{implementation}` in \
         place of `{bound}`, or remove the attribute."
    )
}

/// The refusal of a declaration that is `@[extern "symbol"]` itself.
fn extern_declaration(declaration: &Name, symbol: &str) -> String {
    format!(
        "`{declaration}` is @[extern \"{symbol}\"]: compiled code calls the external symbol \
         `{symbol}`, and this lane would emit the kernel value of `{declaration}` instead \
         (extern). Options: call the function behind `{symbol}` from Rust, or remove the \
         attribute."
    )
}

/// The refusal of a declaration whose value reaches `bound`, an
/// `@[extern "symbol"]` constant that `named_by`'s value names.
fn reached_extern(bound: &Name, symbol: &str, named_by: &Name) -> String {
    format!(
        "it reaches `{bound}` (named by `{named_by}`), which is @[extern \"{symbol}\"]: compiled \
         code calls the external symbol `{symbol}`, and this lane would emit the kernel value of \
         `{bound}` instead (extern). Options: call the function behind `{symbol}` in place of \
         `{bound}`, or remove the attribute."
    )
}

/// The refusal of `reached`, named by `named_by`'s value, when compiled code
/// never runs its kernel value (`clean_compiler`'s `has_compiler_attr`).
fn refuse_reached(env: &Environment, reached: &Name, named_by: &Name) -> Result<(), NotRun> {
    if let Some(implementation) = env.get_implemented_by(reached) {
        return Err(NotRun::ImplementedBy(reached_binding(reached, implementation, named_by)));
    }
    if let Some(symbol) = env.get_extern(reached) {
        return Err(NotRun::Extern(reached_extern(reached, symbol, named_by)));
    }
    Ok(())
}

/// The named-call expansion's refusal of `callee`, named by `caller`'s value.
pub(crate) fn bound_callee(env: &Environment, caller: &Name, callee: &Name) -> Result<(), NotRun> {
    refuse_reached(env, callee, caller)
}

/// The refusal of `declaration` when it carries either attribute.
pub(crate) fn refuse_own_binding(env: &Environment, declaration: &Name) -> Result<(), NotRun> {
    if let Some(implementation) = env.get_implemented_by(declaration) {
        return Err(NotRun::ImplementedBy(bound_declaration(declaration, implementation)));
    }
    if let Some(symbol) = env.get_extern(declaration) {
        return Err(NotRun::Extern(extern_declaration(declaration, symbol)));
    }
    Ok(())
}

/// Every constant a term names. The kernel owns child traversal, so no
/// expression variant is skipped; pointer keys only avoid re-entering a shared
/// node and are never compared as identity.
#[derive(Default)]
struct Named {
    names: RefCell<Vec<Name>>,
    seen: RefCell<HashSet<*const ExprKind>>,
    budget: Cell<usize>,
    exhausted: Cell<bool>,
}

impl ExprFolderOpt for Named {
    fn should_descend(&self, expr: &Expr) -> bool {
        if self.exhausted.get() || !self.seen.borrow_mut().insert(expr.kind() as *const ExprKind) {
            return false;
        }
        match self.budget.get().checked_sub(1) {
            Some(left) => self.budget.set(left),
            None => {
                self.exhausted.set(true);
                return false;
            }
        }
        if let ExprKind::Const(name, _) = expr.kind() {
            self.names.borrow_mut().push(name.clone());
        }
        true
    }
}

/// Refuse `declaration` when it carries either attribute, or when a constant
/// its value reaches does: breadth first over the values of `Definition` and
/// `Opaque` constants (a theorem's value is a proof, never run), so the
/// refusal names the nearest such constant and the constant whose value names
/// it.
pub(crate) fn refuse_reached_binding(env: &Environment, declaration: &Name) -> Result<(), NotRun> {
    refuse_own_binding(env, declaration)?;
    let Some(root_info) = env.get_const(declaration) else {
        return Ok(());
    };
    if !matches!(root_info.kind, ConstantKind::Definition | ConstantKind::Opaque)
        || root_info.value.is_none()
    {
        return Ok(());
    }
    let mut named = Named { budget: Cell::new(MAX_NODES), ..Named::default() };
    let mut visited: HashSet<Name> = HashSet::from([declaration.clone()]);
    let mut pending: VecDeque<Name> = VecDeque::from([declaration.clone()]);
    while let Some(current) = pending.pop_front() {
        let Some(info) = env.get_const(&current) else {
            continue;
        };
        if !matches!(info.kind, ConstantKind::Definition | ConstantKind::Opaque) {
            continue;
        }
        let Some(value) = info.value.as_ref() else {
            continue;
        };
        let unchanged = named.fold_expr_opt(value);
        debug_assert!(unchanged.is_none(), "the walk rewrites no term");
        if named.exhausted.get() {
            return Err(NotRun::ImplementedBy(walk_limit()));
        }
        let mut names = named.names.borrow_mut();
        for name in names.drain(..) {
            if visited.contains(&name) {
                continue;
            }
            refuse_reached(env, &name, &current)?;
            visited.insert(name.clone());
            if visited.len() > MAX_CONSTANTS {
                return Err(NotRun::ImplementedBy(walk_limit()));
            }
            pending.push_back(name);
        }
    }
    Ok(())
}

fn walk_limit() -> String {
    format!(
        "its value's dependency closure exceeds the {MAX_CONSTANTS}-constant, {MAX_NODES}-node \
         walk this lane takes to find @[implemented_by] and @[extern] bindings, so whether \
         compiled code runs its kernel value is not established (implemented-by)"
    )
}
