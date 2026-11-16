// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Trust (E9-ODT-FACE-SELF-CALL-1, the E9 goal builder): the contracted
//! function's own call, rebuilt over a NOMINAL ODT import through the face
//! constructor.
//!
//! The clause binds a by-value struct parameter as one row per field
//! (`c.degree`, `c.coeff`; E6/E9 widening increment 7), and
//! `ensures_goal_source` builds the substitute for `result` as a call over
//! those rows. TG11's ODT import takes the struct itself (TG11-ODT-E6: no
//! flattened signature is substituted for an ODT import). This module rebuilds
//! each struct argument through the face's own constructor,
//! `trust_import_f (TrustOdt.k….mk c.degree c.coeff)`, so the goal keeps the
//! clause's binders and the import keeps its nominal signature. Nothing is
//! minted here.
//!
//! WHAT IS CHECKED, exactly. The goal is `∀ rows, Q(rows, f (K.mk rows))`; the
//! VC is its instance at the argument's field values, and a one-constructor
//! structure IS `K.mk` of its fields. The kernel cannot see WHICH row fills
//! WHICH slot when two fields share a carrier (a swap still types, and a
//! theorem about one field would discharge a clause about the other), so:
//!
//! * FIELD slots are checked by REGISTERED NAME against the face: the kernel's
//!   structure-field side table, which ODT B1 binds to the Rust declaration
//!   (`trust_certify::odt::readmit_into`). The face is bound to the extracted
//!   parameter type by TG11's `agrees` (`crates/trust-certify/src/odt_e6.rs`,
//!   `admit`, line 246 at the time of writing). Each field slot also takes only
//!   a row at an ODT scalar domain whose kernel type is the slot's declared
//!   type.
//! * SCALAR slots are checked by carrier, at the same ODT scalar vocabulary.
//! * STRUCT ROOTS are checked for consistency (one root per group) and
//!   uniqueness (no root fills two parameters) ONLY — never against the
//!   import's parameter names, because the ODT admission records none.
//! * Every row is consumed exactly once, in order.
//!
//! WHAT IS NOT CHECKED. The position of each PARAMETER rests on MIR's argument
//! order being the signature order, the order the clause side walks too.
//! Recording the parameter names would need `.with_param_names(..)` on the
//! admission TG11 mints (`odt_e6.rs:294-295`, TG11's file) and a matching change
//! to the cross-check in `ensures_goal_source`. The flattened mint's
//! `Admission::param_names` binds each row to its parameter as well; this does
//! not restore that half.
//!
//! Applies to every call of the contracted function in its own clause, under the
//! exact self key `is_ambient_self_fn_key` matches — the synthesized substitute, and
//! an author-written call spelled with that key, which is held to the same
//! checks and denotes `f` applied to the constructed struct. A call of any OTHER
//! ODT-admitted function over flattened rows keeps the arity refusal.
//!
//! Only entry points that install the self key reach this rebuild. The
//! conditional (under-`requires`) rungs, `elaborate_ensures_under_requires_in`,
//! and the ∀-`result` fallback (`elaborate_goal_typed_in_mode` with no self
//! key) do not, so a citation on an ODT struct-parameter function that needs a
//! `requires` hypothesis, or reaches only that fallback, keeps the arity
//! refusal: fail-closed, and recorded in E9-ODT-FACE-SELF-CALL-1.

use std::collections::{BTreeMap, BTreeSet};

use clean_kernel::{Expr, Name};
use syn::Expr as SynExpr;

use super::{Admission, Carrier, Domain, MachineSIntWidth, atom_var_name, elab_term};

/// The applied self-call, built through the face constructor of every ODT
/// struct parameter.
///
/// `Ok(None)`: not this shape — no declared carriers, no registered-datatype
/// parameter, an argument that is not a row atom, or no dotted row. The caller's
/// path and its refusals are then unchanged. `Err`: it is this shape and a check
/// failed; nothing is guessed.
pub(super) fn face_self_call(
    callee: &str,
    admission: &Admission,
    c: &syn::ExprCall,
    vars: &[String],
    offset: u32,
    var_domains: &BTreeMap<String, Domain>,
) -> Result<Option<Expr>, String> {
    let Some(carriers) = admission.carriers.as_ref().filter(|k| k.params.len() == admission.arity)
    else {
        return Ok(None);
    };
    if !carriers.params.iter().any(|k| matches!(k, Carrier::RegisteredAdt(_))) {
        return Ok(None);
    }
    let args: Vec<&SynExpr> = c.args.iter().collect();
    let Some(rows) = args.iter().map(|a| atom_var_name(a)).collect::<Option<Vec<String>>>() else {
        return Ok(None);
    };
    if !rows.iter().any(|row| row.contains('.')) {
        return Ok(None);
    }
    let refuse = |why: String| -> Result<Option<Expr>, String> {
        Err(format!(
            "the E9 self-call of `{callee}` applies its nominal ODT import to the clause's \
             flattened rows {rows:?}, and they cannot be rebuilt into its declared parameters: \
             {why}; the discharge fails closed"
        ))
    };
    let mut next = 0usize;
    let mut roots: BTreeSet<String> = BTreeSet::new();
    let mut applied = Expr::const_(Name::from_string(&admission.kernel_const), vec![]);
    for (i, declared) in carriers.params.iter().enumerate() {
        let argument = if let Carrier::RegisteredAdt(adt) = declared {
            let Some((ctor, fields)) = adt.structure_fields() else {
                return refuse(format!(
                    "parameter {i} is a registered datatype but not a one-constructor structure \
                     with a registered field table"
                ));
            };
            let Some(group) = rows.get(next..next + fields.len()) else {
                return refuse(format!(
                    "parameter {i} needs {} field row(s) and {} remain",
                    fields.len(),
                    rows.len() - next
                ));
            };
            let mut root: Option<&str> = None;
            let mut built = Expr::const_(ctor, vec![]);
            for (j, (row, (field_name, field_ty))) in group.iter().zip(&fields).enumerate() {
                let Some(registered) = odt_member_rust_name(field_name) else {
                    return refuse(format!(
                        "field slot {j} of parameter {i} is registered as `{field_name}`, which \
                         is not an ODT member name"
                    ));
                };
                let Some((row_root, row_field)) = row.split_once('.') else {
                    return refuse(format!("`{row}` is not a field row of parameter {i}"));
                };
                if *root.get_or_insert(row_root) != row_root || row_field != registered {
                    return refuse(format!(
                        "`{row}` does not fill field slot {j} of parameter {i}, whose registered \
                         field is `{registered}`; the clause and the face must flatten the \
                         struct in the same declaration order"
                    ));
                }
                let Some(dom) = var_domains.get(row.as_str()) else {
                    return Err(format!("unbound variable `{row}`"));
                };
                if !is_odt_scalar_domain(dom) || dom.ty() != *field_ty {
                    return refuse(format!(
                        "`{row}` is bound at `{}`, but field slot {j} of parameter {i} is \
                         declared `{field_ty}`",
                        dom.rust_name()
                    ));
                }
                built =
                    Expr::app(built, elab_term(args[next + j], vars, offset, var_domains, dom)?);
            }
            // A zero-field structure has no row naming its root. ODT faces have
            // at least one field; any other zero-field family is one value.
            if let Some(root) = root {
                if !roots.insert(root.to_string()) {
                    return refuse(format!("`{root}` would fill two parameters"));
                }
            }
            next += fields.len();
            built
        } else {
            let Some(row) = rows.get(next) else {
                return refuse(format!("no row is left for parameter {i}"));
            };
            if row.contains('.') || !roots.insert(row.clone()) {
                return refuse(format!("`{row}` cannot stand for scalar parameter {i}"));
            }
            let Some(dom) = var_domains.get(row.as_str()) else {
                return Err(format!("unbound variable `{row}`"));
            };
            if !is_odt_scalar_domain(dom) || dom.carrier() != *declared {
                return refuse(format!(
                    "`{row}` is bound at `{}` (carrier `{}`), but parameter {i} is declared `{}`",
                    dom.rust_name(),
                    dom.carrier().clean_name(),
                    declared.clean_name()
                ));
            }
            let term = elab_term(args[next], vars, offset, var_domains, dom)?;
            next += 1;
            term
        };
        applied = Expr::app(applied, argument);
    }
    if next != rows.len() {
        return refuse(format!("{} row(s) are left over", rows.len() - next));
    }
    Ok(Some(applied))
}

/// The ODT scalar vocabulary (`trust_odt::Scalar`: `bool`, `u8`..`u64`,
/// `i8`..`i64`). On it the map from a domain to its kernel type is injective,
/// so comparing kernel types is comparing domains; `usize`/`isize`, `u128` and
/// `i128` share a `BitVec` with a member of it and are refused instead.
fn is_odt_scalar_domain(dom: &Domain) -> bool {
    matches!(
        dom,
        Domain::Bool
            | Domain::Machine(_)
            | Domain::Signed(
                MachineSIntWidth::I8
                    | MachineSIntWidth::I16
                    | MachineSIntWidth::I32
                    | MachineSIntWidth::I64
            )
    )
}

/// The Rust field name an ODT member name encodes (`trust_odt::member_name`:
/// `n` followed by the name's UTF-8 bytes in lowercase hex), or `None` when
/// `name` is not exactly such an encoding.
///
/// Decoded here rather than re-encoded through `trust_odt`, so this crate takes
/// no dependency edge for it. Drift in the encoding fails closed: an encoding
/// this does not decode is refused, never compared loosely. The registered
/// `Name` must also BE the one-component name the spelling builds, since equal
/// display strings do not make equal names.
fn odt_member_rust_name(name: &Name) -> Option<String> {
    let spelled = name.to_string();
    let hex = spelled.strip_prefix('n')?;
    if hex.len() % 2 != 0 || !hex.bytes().all(|b| matches!(b, b'0'..=b'9' | b'a'..=b'f')) {
        return None;
    }
    let bytes = (0..hex.len())
        .step_by(2)
        .map(|at| u8::from_str_radix(&hex[at..at + 2], 16).ok())
        .collect::<Option<Vec<u8>>>()?;
    let rust = String::from_utf8(bytes).ok()?;
    (Name::from_string(&spelled) == *name).then_some(rust)
}

#[cfg(test)]
mod tests;
