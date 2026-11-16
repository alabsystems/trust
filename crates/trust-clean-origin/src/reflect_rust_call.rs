// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **Side B for Rust-call chain emissions** (W5, Lean-calls-Rust; design of
//! record `docs/design/2026-09-13-lean-calls-rust-lane.md`, EMISSION) — the
//! reflection mint that turns a recognized
//! [`trust_types::admissible_body::RustCallChainBody`] (read out of the
//! EMITTED MIR by `recognize_rust_call_chain`) into the kernel term
//! [`crate::gate::check_faithful`] decides over.
//!
//! # FROZEN against the lane it feeds
//!
//! This module is a side-B producer, under the same standing prohibition as
//! `crates/trust-clean/src/reflect.rs`, [`crate::reflect_rec`] and
//! `recognize_rust_call_chain`: **if a Clean-origin body fails the gate, the
//! fix is NEVER an edit here.** Editing the reflection to make side B agree
//! with side A converts the gate into a round trip. Its output is a CLAIM —
//! re-decided against the kernel by `check_faithful`, which is the only place
//! a [`crate::gate::Faithful`] can come from.
//!
//! # A NEW side-B producer, and what that costs
//!
//! The non-recursive machine shapes reflect through `trust_spec_elab`'s
//! `admit_*` family — producers written years earlier for the OPPOSITE
//! direction (frozen-R's pedigree). No such producer can exist for an
//! application of a USER function: `trust_spec_elab` knows the marker-
//! authenticated `core::num` primitives and the bignum runtime, and nothing
//! else, by design. This module is therefore a Trust-authored producer and
//! gets its own `docs/TCB.md` row rather than borrowing frozen-R's pedigree
//! (`table.rs`'s `rust.call` row names it). What substitutes for the
//! pedigree is FAST-LANE-FIRST: every rendering below is pinned by
//! `tests/control_23_rust_call_emitter_mutation.rs`, which demands refusals
//! at both the structural and the kernel layer.
//!
//! # The rendering is DUMB, deliberately
//!
//! Every node spells what the MACHINE computes — an application of the
//! callee CONSTANT to the operands the bytes carry — never what side A wrote.
//! In particular:
//!
//! * the binder types and the result type come from the EMITTED body's own
//!   locals (`extracted.body.locals`, `return_ty`), never from the plan, so an
//!   emitter that typed a local wrongly is caught;
//! * a numeral is rendered at its ENCODED width (`UInt{w}.ofNat v`), never at
//!   the width the callee wants — if the two differ, the KERNEL's typing of
//!   the application refuses, which is where that fact belongs;
//! * the callee constant is looked up by the RENDERING side B read
//!   (`safe_def_path_str` of the emitted call), through the table the caller
//!   hands over. That table — rendering → Clean name — is the compiler-
//!   asserted identity "`inc` DENOTES `fn inc`", disclosed in `docs/TCB.md`;
//!   this module neither checks nor could check it, and says so.
//!
//! Every minted term is FULL-KERNEL-CHECKED as a `Definition` in a CLONE of
//! the caller's environment (the same scratch-clone discipline as
//! `emit::admit_lowering`'s reflection step), so checking a body can never
//! mutate the environment it is checked against, and an ill-typed
//! application — the wrong-width literal, a `Bool` where a `UInt64` is due —
//! never reaches `is_def_eq` untyped.

use std::collections::BTreeMap;

use clean_kernel::{BinderInfo, Declaration, Environment, Expr, Name};
use trust_types::admissible_body::{RustCallChainArg, RustCallChainBody, RustCallChainNode};
use trust_types::{Ty, VerifiableFunction};

/// The Clean type a Rust carrier local denotes, or `None` outside the closed
/// vocabulary this lane reflects.
///
/// Deliberately the SAME closed reading `trust_certify::clean_island::
/// declare_rust_callees` makes when it declares a callee (`uN` ↔ `UIntN`,
/// `bool` ↔ `Bool`), restated here so a local this lane cannot spell is a
/// refusal rather than a guess — and NO `usize`, for the reason
/// `emit::ty_to_domain` gives.
fn clean_type_of(ty: &Ty) -> Option<Expr> {
    let name = match ty {
        Ty::Bool => "Bool",
        Ty::Int { width: 8, signed: false } => "UInt8",
        Ty::Int { width: 16, signed: false } => "UInt16",
        Ty::Int { width: 32, signed: false } => "UInt32",
        Ty::Int { width: 64, signed: false } => "UInt64",
        _ => return None,
    };
    Some(Expr::const_(Name::interned(name), vec![]))
}

/// Reflect a recognized Rust-call chain into the kernel term
/// `fun (p0 : T0) … (p_{n-1} : T_{n-1}) => <root application>`, full-kernel-
/// checked in a scratch clone of `env`, and return that term.
///
/// `clean_name_of_path` maps the extractor's rendering of a callee to the
/// Clean constant the compiler declared for it — the compiler-asserted
/// identity (see the module docs). A rendering the map does not hold is a
/// refusal: the recognizer's allow-list should have excluded it, so reaching
/// it is a producer-chain disagreement.
///
/// # Errors
///
/// A message naming the position, when a local is outside the reflectable
/// vocabulary, a callee rendering is unmapped, a node reference is not an
/// earlier node, or the kernel refuses the minted definition.
pub fn reflect_rust_call_chain(
    env: &Environment,
    name: &str,
    body: &RustCallChainBody,
    extracted: &VerifiableFunction,
    clean_name_of_path: &BTreeMap<String, String>,
) -> Result<Expr, String> {
    let arity = extracted.body.arg_count;

    // ── 1. binder and result types, off the EMITTED body's own locals ──────
    let mut param_types = Vec::with_capacity(arity);
    for index in 1..=arity {
        let local = extracted.body.locals.iter().find(|local| local.index == index);
        let Some(clean) = local.and_then(|local| clean_type_of(&local.ty)) else {
            return Err(format!(
                "cannot reflect the Rust-call chain emitted for `{name}`: parameter local \
                 _{index} is absent or not a `bool`/`u8`/`u16`/`u32`/`u64` carrier \
                 ({:?}). This is a producer-chain defect, not a user error. Please report it.",
                local.map(|local| &local.ty)
            ));
        };
        param_types.push(clean);
    }
    let Some(result_type) = clean_type_of(&extracted.body.return_ty) else {
        return Err(format!(
            "cannot reflect the Rust-call chain emitted for `{name}`: the return type \
             {:?} is not a `bool`/`u8`/`u16`/`u32`/`u64` carrier. Please report it.",
            extracted.body.return_ty
        ));
    };

    // ── 2. the application tree, rendered from the RECOGNIZED dataflow ─────
    let Some(root) = body.nodes.len().checked_sub(1) else {
        return Err(format!(
            "cannot reflect the Rust-call chain emitted for `{name}`: it has no calls. \
             Please report it."
        ));
    };
    let mut rendered_nodes = vec![None; body.nodes.len()];
    let rendered =
        render_node(name, body, root, arity, clean_name_of_path, &mut rendered_nodes, 0)?;
    let value = param_types
        .iter()
        .rev()
        .fold(rendered, |acc, param| Expr::lam(BinderInfo::Default, param.clone(), acc));
    let type_ =
        param_types.iter().rev().fold(result_type, |acc, param| Expr::arrow(param.clone(), acc));

    // ── 3. FULL kernel check of the minted term, in a CLONE ────────────────
    //
    // The name uses the same non-namespace `_` suffix discipline as
    // `emit::reflection_name` and never enters the real environment.
    let mut scratch = env.clone();
    scratch
        .add_decl(Declaration::Definition {
            name: Name::from_string(&format!("{name}_trust_clean_origin_reflection")),
            level_params: vec![],
            type_,
            value: value.clone(),
            is_reducible: true,
        })
        .map_err(|refusal| {
            format!(
                "cannot reflect the Rust-call chain emitted for `{name}`: the kernel refused \
                 the reflected application: {refusal:?}. An operand the emitted call passes \
                 is not at the carrier the callee's declared type takes, or the chain is \
                 ill-formed; there is no degraded rendering — an unchecked term must never \
                 reach the gate, where it would be put to `is_def_eq` untyped. Please report \
                 it."
            )
        })?;

    Ok(value)
}

/// Render node `index` as an application of its callee constant to its
/// rendered operands.
///
/// # The chain is a DAG, and this renders it as one
///
/// A node may be read by SEVERAL later nodes (the explicit value temporary,
/// `emit::walk_let_spine`): `let y := f x; g y y` is one `f`
/// node read twice. Rendered naively, each read re-renders its whole subtree,
/// and the term's SIZE is then the chain's UNFOLDED weight — for a doubling
/// chain of `n` nodes that is `2^n - 1` applications, which no depth rail can
/// see (the depth is only `n`). So every node is rendered ONCE and kept in
/// `rendered`, keyed by node index; a later read clones the kept `Expr`, which
/// is shallow (children are `Arc`s), so the reflected term is a DAG in memory
/// with exactly one application per chain node. It is the SAME term the tree
/// rendering would produce — the kernel sees an application of the callee
/// constant at every read either way — so nothing about the gate changes;
/// only the cost of minting the term does, from exponential to linear.
///
/// This is defence in depth, not the bound. The bound is on the PLAN:
/// `emit::check_rust_call_chain`'s unfold rail refuses a chain whose unfolded
/// size exceeds the kernel envelope this lane is measured at
/// (`named_calls::MAX_NODES`) before anything is emitted, so a chain that
/// reaches here has a small unfolding whatever this function does.
/// The two are independent on purpose: a memo alone would leave the kernel's
/// `is_def_eq` to re-unfold the DAG, and a bound alone would leave the reflector
/// exponential inside its cap.
///
/// `depth` rails the DESCENT only — a defensive stack bound against a
/// malformed chain — and says nothing about the term's size; the order check
/// on `Node(k)` (an earlier node only) is what keeps the descent finite.
fn render_node(
    name: &str,
    body: &RustCallChainBody,
    index: usize,
    arity: usize,
    clean_name_of_path: &BTreeMap<String, String>,
    rendered: &mut [Option<Expr>],
    depth: usize,
) -> Result<Expr, String> {
    if let Some(Some(already)) = rendered.get(index) {
        return Ok(already.clone());
    }
    if depth > crate::emit::COMPOSED_MAX_OPS {
        return Err(format!(
            "cannot reflect the Rust-call chain emitted for `{name}`: it nests deeper than \
             {} calls. Please report it.",
            crate::emit::COMPOSED_MAX_OPS
        ));
    }
    let RustCallChainNode { callee, args } = &body.nodes[index];
    let Some(clean_name) = clean_name_of_path.get(callee) else {
        return Err(format!(
            "cannot reflect the Rust-call chain emitted for `{name}`: call {index} names \
             `{callee}`, which no registered Rust callee renders as. The recognizer's \
             allow-list and the reflection's identity table have drifted apart. Please \
             report it."
        ));
    };
    let mut operands = Vec::with_capacity(args.len());
    for (position, arg) in args.iter().enumerate() {
        let operand = match arg {
            RustCallChainArg::Param(i) => {
                if *i >= arity {
                    return Err(format!(
                        "cannot reflect the Rust-call chain emitted for `{name}`: call {index} \
                         argument {position} reads parameter {i} of {arity}. Please report it."
                    ));
                }
                // Under `n` binders, SOURCE parameter `i` is `BVar(n-1-i)`.
                Expr::bvar((arity - 1 - i) as u32)
            }
            RustCallChainArg::Node(k) => {
                if *k >= index {
                    return Err(format!(
                        "cannot reflect the Rust-call chain emitted for `{name}`: call {index} \
                         reads call {k}, which is not an earlier call. Please report it."
                    ));
                }
                render_node(name, body, *k, arity, clean_name_of_path, rendered, depth + 1)?
            }
            RustCallChainArg::UInt { value, width_bits } => {
                let of_nat_name = match width_bits {
                    8 => "UInt8.ofNat",
                    16 => "UInt16.ofNat",
                    32 => "UInt32.ofNat",
                    64 => "UInt64.ofNat",
                    _ => {
                        return Err(format!(
                            "cannot reflect the Rust-call chain emitted for `{name}`: call {index} \
                             argument {position} is a scalar at width {width_bits}, which has no \
                             `UInt` carrier. Please report it."
                        ));
                    }
                };
                // At the ENCODED width. The kernel decides whether the
                // callee accepts it there.
                Expr::app(
                    Expr::const_(Name::interned(of_nat_name), vec![]),
                    Expr::nat_lit_u128(*value),
                )
            }
            RustCallChainArg::Bool(value) => Expr::const_(
                Name::interned(if *value { "Bool.true" } else { "Bool.false" }),
                vec![],
            ),
        };
        operands.push(operand);
    }
    let application = Expr::apps(Expr::const_(Name::interned(clean_name), vec![]), operands);
    if let Some(slot) = rendered.get_mut(index) {
        *slot = Some(application.clone());
    }
    Ok(application)
}
