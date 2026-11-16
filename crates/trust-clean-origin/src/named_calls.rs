// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Source-side expansion of transparent Lean helper calls. This is a planning
//! heuristic, never evidence: the gate still reads the original declaration
//! from the environment and compares it with the independently reflected code.

use std::collections::HashSet;

use clean_kernel::name::NameInner;
use clean_kernel::{ConstantKind, DeclarationVerification, Environment, Expr, ExprKind, Name};
use trust_clean_carrier::carrier_signature_for;

use crate::emit::RustCalleeRef;
use crate::table::{KernelSelector, ROWS};

/// Shared with `emit::check_rust_call_chain`'s unfold rail: the reflected
/// side B of a `let`-bearing Rust-call chain inlines a shared temporary per
/// use, and that rendering is capped at the same node envelope this
/// expansion works under.
pub(crate) const MAX_NODES: usize = 4_096;
const MAX_DEPTH: usize = 128;
const MAX_EXPANSIONS: usize = 128;

/// The source declaration and its environment are never modified. Existing
/// recognized bodies do not call this function. All limits refuse explicitly;
/// no partial expansion may become a plan.
pub(crate) fn expand_named_calls(
    env: &Environment,
    declaration: &Name,
    body: &Expr,
    callees: &[RustCalleeRef],
) -> Result<Option<Expr>, String> {
    // Trust (Clean R80): the expansion inlines kernel values, so it refuses
    // what `clean_compiler::constant_to_decl` refuses (an ORDER record) and a
    // declaration compiled code does not run, `@[implemented_by]` or
    // `@[extern]` (`crate::implemented_by`). Each callee is checked as it is
    // reached, in `Expansion::application`.
    crate::implemented_by::refuse_order(env)?;
    crate::implemented_by::refuse_own_binding(env, declaration)
        .map_err(crate::implemented_by::NotRun::into_reason)?;
    bounded_nodes(body)?;
    let mut expansion = Expansion {
        env,
        rust_names: callees_set(callees),
        remaining: MAX_NODES,
        expanded: 0,
        active: vec![declaration.clone()],
    };
    let result = expansion.walk(body, 0)?;
    Ok((expansion.expanded != 0).then_some(result))
}

struct Expansion<'a> {
    env: &'a Environment,
    rust_names: HashSet<Name>,
    remaining: usize,
    expanded: usize,
    active: Vec<Name>,
}

fn callees_set(callees: &[RustCalleeRef]) -> HashSet<Name> {
    if callees.is_empty() {
        return HashSet::new();
    }
    callees.iter().map(|row| Name::from_string(&row.clean_name)).collect()
}

fn limit() -> String {
    format!(
        "named Lean call expansion exceeded its {MAX_NODES}-node, {MAX_DEPTH}-depth or \
         {MAX_EXPANSIONS}-definition work envelope; no partial body was admitted. \
         The compiler needs a direct linked-call realization for this body"
    )
}

/// Count before substitution, including binder types. Refuse unfamiliar kernel
/// extensions rather than letting an uncounted child enter a size estimate.
fn bounded_nodes(expr: &Expr) -> Result<usize, String> {
    let mut stack = vec![(expr, 0)];
    let mut nodes = 0;
    while let Some((expr, depth)) = stack.pop() {
        nodes += 1;
        if nodes > MAX_NODES || depth > MAX_DEPTH {
            return Err(limit());
        }
        let next = depth + 1;
        match expr.kind() {
            ExprKind::App(f, a) | ExprKind::Lam(_, f, a) | ExprKind::Pi(_, f, a) => {
                stack.extend([(f.as_ref(), next), (a.as_ref(), next)]);
            }
            ExprKind::Let(_, ty, val, body, _) => {
                stack.extend([(ty.as_ref(), next), (val.as_ref(), next), (body.as_ref(), next)]);
            }
            ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => {
                stack.push((inner.as_ref(), next));
            }
            ExprKind::BVar(_)
            | ExprKind::FVar(_)
            | ExprKind::Sort(_)
            | ExprKind::Const(_, _)
            | ExprKind::Lit(_) => {}
            _ => {
                return Err(
                    "named Lean call expansion cannot measure this kernel extension yet".into()
                );
            }
        }
    }
    Ok(nodes)
}

fn substitute(body: &Expr, arg: &Expr) -> Result<Expr, String> {
    // A conservative upper bound is checked before the allocating kernel
    // substitution. Repeated uses of an argument cannot produce a huge tree
    // and only then discover that the work envelope was exceeded.
    if bounded_nodes(body)?.saturating_mul(bounded_nodes(arg)?) > MAX_NODES {
        return Err(limit());
    }
    let result = body.instantiate(arg);
    bounded_nodes(&result)?;
    Ok(result)
}

fn strip_metadata(mut expr: &Expr) -> &Expr {
    while let ExprKind::MData(_, inner) = expr.kind() {
        expr = inner;
    }
    expr
}

/// A Rust callee is an opaque mathematical function in the existing kernel
/// model. Definitional equality can therefore erase or duplicate an argument
/// that calls Rust, although the native call can have effects or panic. Only
/// pure arguments (or the exact identity substitution) may be substituted by
/// this planner; a Rust call the body wants to name is carried by the
/// explicit value temporary of a TOP-LEVEL `let` instead
/// (`emit::walk_let_spine`, W5 increment 7), which the notes below point at.
pub(crate) fn check_substitution_effects_with_names(
    env: &Environment,
    body: &Expr,
    argument: &Expr,
    rust_names: &HashSet<Name>,
) -> Result<(), String> {
    if matches!(strip_metadata(body).kind(), ExprKind::BVar(0)) {
        return Ok(());
    }
    check_rust_call_free_with_names(env, argument, rust_names)
}

pub(crate) fn check_rust_call_free(
    env: &Environment,
    argument: &Expr,
    callees: &[RustCalleeRef],
) -> Result<(), String> {
    let rust_names = callees_set(callees);
    check_rust_call_free_with_names(env, argument, &rust_names)
}

fn check_rust_call_free_with_names<'a>(
    env: &'a Environment,
    argument: &'a Expr,
    rust_names: &HashSet<Name>,
) -> Result<(), String> {
    let mut visited = HashSet::new();
    let mut stack = vec![argument];
    let mut remaining = MAX_NODES;
    while let Some(expr) = stack.pop() {
        if remaining == 0 {
            return Err(limit());
        }
        remaining -= 1;
        match expr.kind() {
            ExprKind::Const(name, _) => {
                if rust_names.contains(name) {
                    return Err(format!(
                        "substituting an argument that calls Rust `{name}` could drop, duplicate \
                         or reorder that call; pure kernel equality does not preserve its \
                         effects or panic. options: `let`-bind the call at the TOP of the \
                         `def` body (`let y := f x; …`) and pass `y` straight to Rust callees, \
                         where the compiler evaluates it exactly once as a value temporary \
                         (hoist a `let` nested in an operand or in another `let`'s value up to \
                         that spine); or call Rust from Rust and pass the result into the Lean \
                         function"
                    ));
                }
                if visited.contains(name) {
                    continue;
                }
                visited.insert(name.clone());
                // A primitive-looking spelling can name a user definition.
                // Rust declarations are ordinary Opaque constants with a hidden
                // placeholder inhabitant, so that value is never purity evidence,
                // including when a caller supplied no or incomplete callee metadata.
                let info = env.get_const(name);
                if info.is_some_and(|info| info.kind == ConstantKind::Theorem) {
                    if env.declaration_verification(name)
                        != Some(DeclarationVerification::FullKernelCheck)
                    {
                        return Err(format!(
                            "unchecked theorem dependency `{name}` cannot be treated as erased \
                             proof; substitution needs an explicit value temporary or a full \
                             kernel check establishing its Prop type"
                        ));
                    }
                    continue;
                }
                if info.is_some_and(|info| info.kind == ConstantKind::Opaque) {
                    return Err(format!(
                        "substituting opaque dependency `{name}` could discard or change a Rust \
                         call whose effect metadata is absent; its hidden kernel inhabitant \
                         does not establish purity. options: call the registered Rust `fn` \
                         itself, `let`-bound at the TOP of the `def` body, where the compiler \
                         evaluates it exactly once as a value temporary; or call Rust from Rust \
                         and pass the result into the Lean function"
                    ));
                }
                if let Some(value) = info.and_then(|info| info.value.as_ref()) {
                    bounded_nodes(value)?;
                    stack.push(value);
                } else if env.get_inductive(name).is_none()
                    && env.get_constructor(name).is_none()
                    && env.get_recursor(name).is_none()
                {
                    return Err(format!(
                        "cannot establish evaluation behavior of dependency `{name}`; \
                         substitution needs an explicit value temporary or authenticated \
                         runtime dependency metadata"
                    ));
                }
            }
            ExprKind::App(f, a) | ExprKind::Lam(_, f, a) | ExprKind::Pi(_, f, a) => {
                stack.extend([f.as_ref(), a.as_ref()]);
            }
            ExprKind::Let(_, ty, value, body, _) => {
                stack.extend([ty.as_ref(), value.as_ref(), body.as_ref()]);
            }
            ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => stack.push(inner.as_ref()),
            ExprKind::BVar(_) | ExprKind::FVar(_) | ExprKind::Sort(_) | ExprKind::Lit(_) => {}
            _ => {
                return Err(
                    "cannot establish Rust-call-free substitution through this kernel extension"
                        .into(),
                );
            }
        }
    }
    Ok(())
}

/// Apply the same effect boundary to the earlier let-reduction path. Otherwise
/// a let could erase a Rust call before named-call expansion sees the argument.
pub(crate) fn check_let_substitutions(
    env: &Environment,
    expr: &Expr,
    callees: &[RustCalleeRef],
) -> Result<(), String> {
    bounded_nodes(expr)?;
    let rust_names = callees_set(callees);
    let mut stack = vec![expr];
    while let Some(expr) = stack.pop() {
        match expr.kind() {
            ExprKind::Let(_, ty, value, body, _) => {
                check_substitution_effects_with_names(env, body, value, &rust_names)?;
                stack.extend([ty.as_ref(), value.as_ref(), body.as_ref()]);
            }
            ExprKind::App(f, a) | ExprKind::Lam(_, f, a) | ExprKind::Pi(_, f, a) => {
                stack.extend([f.as_ref(), a.as_ref()])
            }
            ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => stack.push(inner.as_ref()),
            _ => {}
        }
    }
    Ok(())
}

impl Expansion<'_> {
    fn walk(&mut self, expr: &Expr, depth: usize) -> Result<Expr, String> {
        if self.remaining == 0 || depth > MAX_DEPTH {
            return Err(limit());
        }
        self.remaining -= 1;
        match expr.kind() {
            ExprKind::Lam(binder, ty, body) => {
                Ok(Expr::lam(binder.clone(), ty.as_ref().clone(), self.walk(body, depth + 1)?))
            }
            ExprKind::Let(_, _, value, body, _) => {
                let value = self.walk(value, depth + 1)?;
                check_substitution_effects_with_names(self.env, body, &value, &self.rust_names)?;
                self.walk(&substitute(body, &value)?, depth + 1)
            }
            ExprKind::MData(_, inner) => self.walk(inner, depth + 1),
            ExprKind::Proj(name, field, inner) => Ok(Expr::proj_arc(
                name.clone(),
                *field,
                std::sync::Arc::new(self.walk(inner, depth + 1)?),
            )),
            ExprKind::App(..) | ExprKind::Const(..) => self.application(expr, depth),
            // Binder types/propositions are retained, not evaluated as code.
            _ => Ok(expr.clone()),
        }
    }

    fn application(&mut self, expr: &Expr, depth: usize) -> Result<Expr, String> {
        let head = strip_metadata(expr.get_app_fn());
        let args = expr
            .get_app_args()
            .iter()
            .map(|arg| self.walk(arg, depth + 1))
            .collect::<Result<Vec<_>, _>>()?;

        if let ExprKind::Lam(..) = head.kind() {
            return self.apply(head.clone(), &args, depth + 1);
        }
        let ExprKind::Const(name, levels) = head.kind() else {
            return Ok(Expr::apps(head.clone(), args));
        };
        // Trust (Clean R80): compiled code runs a bound callee's implementation,
        // or calls an `@[extern]` callee's symbol, never the kernel value this
        // expansion would inline.
        let Some(caller) = self.active.last() else {
            return Err(limit());
        };
        crate::implemented_by::bound_callee(self.env, caller, name)
            .map_err(crate::implemented_by::NotRun::into_reason)?;
        // Preserve the established primitive spelling and opaque Rust callee
        // identity. In particular, a quoted display alias is never a match.
        if selection_head(name) || self.rust_names.contains(name) {
            return Ok(Expr::apps(head.clone(), args));
        }
        let Some(info) = self.env.get_const(name) else {
            return Ok(Expr::apps(head.clone(), args));
        };
        if info.kind != ConstantKind::Definition {
            return Ok(Expr::apps(head.clone(), args));
        }
        let Some(ref raw_body) = info.value else {
            return Ok(Expr::apps(head.clone(), args));
        };
        if info.level_params.len() != levels.len() {
            return Err(format!("named Lean callee `{name}` has mismatched universe arguments"));
        }
        // Do not unfold typeclass dictionaries, type aliases or proof values.
        // Instantiate EVERY actual argument in order, including implicit type
        // parameters; a polymorphic helper can then expose a concrete carrier.
        let mut ty = info.type_.instantiate_level_params_direct(&info.level_params, levels);
        bounded_nodes(&ty)?;
        for arg in &args {
            let ExprKind::Pi(_, _, body) = strip_metadata(&ty).kind() else {
                return Ok(Expr::apps(head.clone(), args));
            };
            ty = substitute(body, arg)?;
        }
        if carrier_signature_for(&ty).is_err() {
            return Ok(Expr::apps(head.clone(), args));
        }
        if self.env.declaration_verification(name) != Some(DeclarationVerification::FullKernelCheck)
        {
            return Err(format!("named Lean callee `{name}` has no full kernel check"));
        }
        if self.active.contains(name) {
            return Err(format!(
                "recursive named Lean callee `{name}` requires a linked-call realization; no expansion was admitted"
            ));
        }
        if self.expanded == MAX_EXPANSIONS {
            return Err(limit());
        }
        bounded_nodes(raw_body)?;
        let body = raw_body.instantiate_level_params_direct(&info.level_params, levels);
        bounded_nodes(&body)?;
        self.expanded += 1;
        self.active.push(name.clone());
        let result = self.apply(body, &args, depth + 1);
        self.active.pop();
        result
    }

    fn apply(&mut self, mut body: Expr, args: &[Expr], depth: usize) -> Result<Expr, String> {
        for arg in args {
            body = match strip_metadata(&body).kind() {
                ExprKind::Lam(_, _, inner) => {
                    check_substitution_effects_with_names(self.env, inner, arg, &self.rust_names)?;
                    substitute(inner, arg)?
                }
                _ => Expr::app(body, arg.clone()),
            };
        }
        self.walk(&body, depth + 1)
    }
}

#[inline]
fn name_eq_str2(name: &Name, first: &str, second: &str) -> bool {
    matches!(
        name.inner(),
        NameInner::Str(parent, s2)
            if s2.as_ref() == second
                && matches!(parent.inner(), NameInner::Str(root, s1) if root.is_anon() && s1.as_ref() == first)
    )
}

#[inline]
fn name_eq_dotted(name: &Name, text: &str) -> bool {
    if text.is_empty() {
        return name.is_anon();
    }
    let mut current = name;
    for part in text.rsplit('.') {
        let NameInner::Str(parent, s) = current.inner() else {
            return false;
        };
        if s.as_ref() != part {
            return false;
        }
        current = parent.as_ref();
    }
    current.is_anon()
}

/// Derive the primitive boundary from the same selection table the existing
/// readers use. These are structural name comparisons, never display matches.
fn selection_head(name: &Name) -> bool {
    let is = |text: &str| name_eq_dotted(name, text);
    let method = |suffix: &str| {
        matches!(
            name.inner(),
            NameInner::Str(parent, s2)
                if s2.as_ref() == suffix
                    && matches!(
                        parent.inner(),
                        NameInner::Str(root, s1)
                            if root.is_anon()
                                && matches!(
                                    s1.as_ref(),
                                    "UInt8" | "UInt16" | "UInt32" | "UInt64" | "UInt128" | "Nat" | "Int" | "BitVec"
                                )
                    )
        )
    };
    ROWS.iter().flat_map(|row| row.side_a).any(|selector| match selector {
        KernelSelector::CarrierMethod { suffix } => method(suffix),
        KernelSelector::SurfaceClass { class, projection } => name_eq_str2(name, class, projection),
        KernelSelector::CarrierNumeral | KernelSelector::CarrierNumeralBody => {
            name_eq_str2(name, "OfNat", "ofNat") || method("ofNat")
        }
        KernelSelector::IteAt(_) | KernelSelector::IteAtBoolDecisionEq => is("ite"),
        KernelSelector::DecideAt(_) => {
            ["decide", "Decidable.decide", "LT.lt", "LE.le", "Eq", "BEq.beq"]
                .iter()
                .any(|head| is(head))
        }
        KernelSelector::BoolValueHead(head) | KernelSelector::ConstantHead(head) => is(head),
        KernelSelector::BoundVariable
        | KernelSelector::InductiveProjectionProof
        | KernelSelector::NatLiteral
        | KernelSelector::RecursiveOccurrence
        | KernelSelector::RustCallee => false,
    })
}
