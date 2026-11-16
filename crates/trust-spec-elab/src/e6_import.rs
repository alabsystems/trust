// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Canonical E6 import of an actual emitted body into a Reflected kernel definition.
//!
//! This bridge and its carrier helpers moved from trust-certify without changing
//! their bodies, including the independently authored TG14 arithmetic bridge.
//! The independent trust-types reader and existing kernel-term producers remain
//! unchanged by the move. This entry does not establish facets, grant
//! Clean-origin emission permission, or mint Certified proof authority.

// Keep the producer vocabulary identical to the original bridge.
use clean_kernel::Environment;

use crate as trust_spec_elab;

/// The E6-ONLY reader's arm of `trust-certify`'s `admit_function_into` (E6 expansion I1′,
/// I3′, I4′): `None` when [`trust_types::e6_expr::read_e6_body`] does not read the
/// body, else the result of the producer for what it read. Reached only
/// after `recognize_admissible_body` and island forwarding both answered
/// `None`. The composed Boolean Clean-origin gate also calls this unchanged
/// reader/renderer on its actual emitted body, then independently checks that
/// defining value against the original Clean declaration. This import alone
/// grants no Clean-origin emission permission.
pub fn admit_e6_only_body(
    env: &mut Environment,
    func: &trust_types::VerifiableFunction,
    kernel_const: &str,
) -> Option<Result<trust_spec_elab::Admission, String>> {
    use trust_types::e6_expr::{BoolEqOp, BoolLeaf, E6Expr};
    let expr = trust_types::e6_expr::read_e6_body(func)?;
    let param_domains = param_domains_of(func)?;
    Some(match expr {
        // Trust (E6 expansion I3′, I4′): a `bool` connective tree or a value
        // decision tree, minted by the E6-only tree producer with each
        // parameter at its own carrier.
        E6Expr::Tree(term) => {
            let Some(ret) = ty_to_domain(&func.body.return_ty) else {
                return Some(Err("the return type has no scalar kernel carrier".to_owned()));
            };
            e6_tree_term(&term).and_then(|term| {
                trust_spec_elab::admit_e6_tree_function(
                    env,
                    kernel_const,
                    &param_domains,
                    &ret,
                    &term,
                )
            })
        }
        E6Expr::BoolCmp { op, left, right } => {
            let operand = |leaf: BoolLeaf| match leaf {
                BoolLeaf::Param(i) => i,
            };
            let cmp = match op {
                BoolEqOp::Eq => trust_spec_elab::BoolCmp::Eq,
                BoolEqOp::Ne => trust_spec_elab::BoolCmp::Ne,
            };
            trust_spec_elab::admit_bool_cmp_function(
                env,
                kernel_const,
                &param_domains,
                cmp,
                operand(left),
                operand(right),
            )
        }
    })
}

/// The E6-only tree reader's term in the producer's vocabulary: the same
/// tree, with each comparison's carrier mapped to its kernel [`Domain`]
/// through [`ty_to_domain`] — the map every E6 parameter carrier goes through
/// — or why a carrier has none.
///
/// [`Domain`]: trust_spec_elab::Domain
fn e6_tree_term(
    term: &trust_types::e6_expr::E6Term,
) -> Result<trust_spec_elab::E6TreeTerm, String> {
    use trust_spec_elab::{E6TreeCmp, E6TreeTerm};
    use trust_types::e6_expr::{E6Carrier, E6Cmp, E6Term};
    let boxed = |t: &E6Term| e6_tree_term(t).map(Box::new);
    Ok(match term {
        E6Term::Param(i) => E6TreeTerm::Param(*i),
        E6Term::Bool(b) => E6TreeTerm::Bool(*b),
        E6Term::Int(v) => E6TreeTerm::Int(*v),
        E6Term::Checked { .. } => {
            return Err("an Option value escaped the matched checked-arithmetic fragment".into());
        }
        E6Term::CheckedTag { overflow, .. } => E6TreeTerm::Ite {
            cond: boxed(overflow)?,
            then: Box::new(E6TreeTerm::Int(0)),
            els: Box::new(E6TreeTerm::Int(1)),
        },
        E6Term::Overflow { op, carrier, left, right } => {
            let ty = match carrier {
                E6Carrier::Unsigned(width) => trust_types::Ty::Int { width: *width, signed: false },
                E6Carrier::Signed(width) => trust_types::Ty::Int { width: *width, signed: true },
                _ => return Err("overflow on a non-integer".into()),
            };
            E6TreeTerm::Overflow {
                op: match op {
                    trust_types::BinOp::Add => trust_spec_elab::E6TreeArith::Add,
                    trust_types::BinOp::Sub => trust_spec_elab::E6TreeArith::Sub,
                    trust_types::BinOp::Mul => trust_spec_elab::E6TreeArith::Mul,
                    _ => return Err("unsupported overflow operator".into()),
                },
                domain: ty_to_domain(&ty).ok_or("overflow on an unsupported carrier")?,
                left: boxed(left)?,
                right: boxed(right)?,
            }
        }
        E6Term::Arith { op, left, right, .. } => E6TreeTerm::Arith {
            op: match op {
                trust_types::BinOp::Add => trust_spec_elab::E6TreeArith::Add,
                trust_types::BinOp::Sub => trust_spec_elab::E6TreeArith::Sub,
                trust_types::BinOp::Mul => trust_spec_elab::E6TreeArith::Mul,
                _ => return Err("unsupported E6 arithmetic operation".into()),
            },
            left: boxed(left)?,
            right: boxed(right)?,
        },
        E6Term::Not(x) => E6TreeTerm::Not(boxed(x)?),
        E6Term::And(x, y) => E6TreeTerm::And(boxed(x)?, boxed(y)?),
        E6Term::Or(x, y) => E6TreeTerm::Or(boxed(x)?, boxed(y)?),
        E6Term::Xor(x, y) => E6TreeTerm::Xor(boxed(x)?, boxed(y)?),
        E6Term::Cmp { op, carrier, left, right } => {
            let ty = match carrier {
                E6Carrier::Bool => trust_types::Ty::Bool,
                E6Carrier::Unsigned(width) => trust_types::Ty::Int { width: *width, signed: false },
                E6Carrier::Signed(width) => trust_types::Ty::Int { width: *width, signed: true },
            };
            let domain = ty_to_domain(&ty).ok_or_else(|| {
                format!(
                    "a comparison over `{}` has no kernel carrier",
                    trust_types::e6_expr::ty_spelling(&ty)
                )
            })?;
            E6TreeTerm::Cmp {
                op: match op {
                    E6Cmp::Eq => E6TreeCmp::Eq,
                    E6Cmp::Ne => E6TreeCmp::Ne,
                    E6Cmp::Lt => E6TreeCmp::Lt,
                    E6Cmp::Le => E6TreeCmp::Le,
                },
                domain,
                left: boxed(left)?,
                right: boxed(right)?,
            }
        }
        // Trust (E6 expansion I4′): a value decision.
        E6Term::Ite { cond, then, els } => {
            E6TreeTerm::Ite { cond: boxed(cond)?, then: boxed(then)?, els: boxed(els)? }
        }
    })
}

/// The machine-integer width for a bit count, or `None` outside the supported
/// widths (which fails the import closed).
pub fn machine_width(bits: u32) -> Option<trust_spec_elab::MachineUIntWidth> {
    use trust_spec_elab::MachineUIntWidth::{U8, U16, U32, U64};
    Some(match bits {
        8 => U8,
        16 => U16,
        32 => U32,
        64 => U64,
        _ => return None,
    })
}

/// The signed sibling of [`machine_width`]: `i8`–`i128`.
///
/// `i128` joined the table on 2026-08-24 (E6 widening increment 6). Nothing
/// below the table blocked it: `MachineSIntWidth::I128` and the `BitVec 128`
/// carrier have been in the clause elaborator all along, `Domain::bitvec_bits`
/// already answers `Some(128)`, `Domain::numeral`/`negative_numeral` already
/// range-check at `2^127`, and the sign-flip order key is the same
/// `Nat.xor (BitVec.toNat v) 2^(w-1)` shape at the wider `w`. The width table
/// was the only gate, and the cost of it being closed was that every
/// `i128`-typed function stayed unadmitted, so `result` in its postcondition
/// stayed universally quantified and the citation failed with a raw
/// `TermRejected` term dump instead of a discharge.
pub fn signed_machine_width(bits: u32) -> Option<trust_spec_elab::MachineSIntWidth> {
    use trust_spec_elab::MachineSIntWidth::{I8, I16, I32, I64, I128};
    Some(match bits {
        8 => I8,
        16 => I16,
        32 => I32,
        64 => I64,
        128 => I128,
        _ => return None,
    })
}

/// The E6 elaboration [`trust_spec_elab::Domain`] a Rust type carries, or `None`
/// for a type outside the supported fragment (floats, references, aggregates, …)
/// — which fails the import closed. Signed `i8`–`i64` map to
/// [`trust_spec_elab::Domain::Signed`] (E6 widening increment 4): the exact
/// two's-complement `BitVec` carrier whose comparisons the clause elaborator
/// already states over the sign-flip order keys.
///
/// `i128`/`u128` map to `Signed(I128)`/`U128` (E6 widening increment 6). Note
/// `u128` is NOT a `Machine` width: `MachineUIntWidth` tops out at 64 and its
/// carrier is `UInt64`, whereas `u128`'s carrier is the exact `BitVec 128`
/// [`trust_spec_elab::Domain::U128`] already provides. Routing it through
/// `machine_width` would have been the silent wrong answer.
///
/// POINTER-SIZED INTEGERS, exactly as the code has them. `Ty::PtrSizedInt` is
/// the FAITHFUL extractor's spelling of `usize`/`isize`
/// (`trust_mir_extract::extract_function_faithful`, v25 B1). The arm below
/// answers `Machine(U64)` for the unsigned case — the `64` is a HARD-CODED
/// constant, not the target's pointer width, because nothing reaches this
/// function that could supply one — and there is NO signed arm, so `isize`
/// falls through to `None` and fails the import closed.
///
/// That arm is DEAD on every path that reaches this function today. Verified by
/// source inspection on 2026-09-18 (an inspection, not a test run): the E6
/// intake accumulates bodies extracted by
/// `trust_mir_extract::extract_function_with_contract_bundle`, which does not
/// enable the extractor's `FaithfulScalarsGuard`, so a pointer-sized integer
/// arrives here already collapsed to `Int { width: <target pointer width>, .. }`
/// — where the width IS the target's — and `Ty::PtrSizedInt` is constructed
/// nowhere under `compiler/`; in this crate it occurs only as the pattern below.
/// While that holds, the carrier-agreement argument the forwarding gate in
/// `trust-certify`'s `admit_island_forwarding_into` rests on is sound at every width the
/// elaborator models: the domain it compares carries the target's own width, so
/// a target whose `usize` is not the declared carrier REFUSES the mint.
///
/// THROUGH THIS ARM it would hold only at 64 bits. Before routing a
/// faithful-extracted body into this lane, give the arm a target width or make
/// it fail closed: on a 32-bit target it otherwise hands a `usize` parameter the
/// `UInt64` carrier, and the forwarding gate would then accept a call forwarded
/// into a `UInt64` Clean slot that the target's 32-bit `usize` does not justify.
/// Fail-closing it costs nothing measurable today (the arm is unreachable, as
/// above); the day the faithful lane is wired in it would cost every
/// `usize`-typed function its kernel import, so `result` in such a function's
/// postcondition stays universally quantified and its citations fail closed —
/// the same cost the `i128` width gate carried before 2026-08-24.
pub fn ty_to_domain(ty: &trust_types::Ty) -> Option<trust_spec_elab::Domain> {
    use trust_spec_elab::{Domain, MachineUIntWidth};
    match ty {
        trust_types::Ty::Bool => Some(Domain::Bool),
        trust_types::Ty::Int { width: 128, signed: false } => Some(Domain::U128),
        trust_types::Ty::Int { width, signed: false } => machine_width(*width).map(Domain::Machine),
        trust_types::Ty::Int { width, signed: true } => {
            signed_machine_width(*width).map(Domain::Signed)
        }
        trust_types::Ty::PtrSizedInt { signed: false } => {
            Some(Domain::Machine(MachineUIntWidth::U64))
        }
        _ => None,
    }
}

/// The domains of every value parameter of `func`, in order, or `None` if any
/// parameter's type is outside the supported fragment. Parameters are locals
/// `1..=arg_count` (local `0` is the return place).
pub fn param_domains_of(
    func: &trust_types::VerifiableFunction,
) -> Option<Vec<trust_spec_elab::Domain>> {
    (1..=func.body.arg_count)
        .map(|i| func.body.locals.iter().find(|l| l.index == i).and_then(|l| ty_to_domain(&l.ty)))
        .collect()
}
