// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
//! An INDEPENDENT TrustIR -> Clean reflector, and the kernel agreements it earns.
//!
//! # Why a second reflector exists at all
//!
//! `trust-clean-ir` emits a `trust_ir::Function` from a sealed `CleanOriginPlan`.
//! Checking that emission by reflecting the IR back to a Clean term and asking the
//! kernel `is_def_eq` is only worth anything if the reflector does not share the
//! emitter's beliefs. A reflector written by reading the emitter can invert the
//! emitter's own mistake, the round trip cancels, and the kernel blesses a wrong
//! body while looking like it proved something.
//!
//! This file was therefore written WITHOUT reading `trust-clean-ir/src/**`, the
//! co-authored `tests/symbolic_reflection.rs`, or `trust-clean-origin/src/reflect.rs`.
//! Its inputs were, in full:
//!
//!   * `first-party/trust-ir/crates/trust-ir/src/**` — the IR spec (`Inst`, `BinOp`,
//!     `ICmpOp`, `Constant`, `Ty`, `Block`, `Function`), including
//!     `interpret.rs:5789-5795`, which fixes `Add`/`Sub`/`Mul` on an integer carrier
//!     as `wrapping_{add,sub,mul}` masked to the width, and `And`/`Or` as raw
//!     bitwise operations;
//!   * `first-party/clean/crates/clean-kernel/src/**` — `Expr`, `Name`, `Level`,
//!     `BinderData`, `TypeChecker`, and `env/data_types_uint.rs`, which is where the
//!     `UIntN` carrier and `UIntN.ofNat` come from;
//!   * direct measurement of the Clean environment itself (see
//!     `clean_primitives_have_the_semantics_this_reflector_assumes` below), which is
//!     evidence about Clean, not about the emitter.
//!
//! # The spelling, bottom-up
//!
//! Each `Inst` variant is given a Clean spelling in isolation, chosen to be the most
//! PRIMITIVE constant that denotes the IR operation, and justified against the
//! kernel's own prelude rather than against anything the emitter does:
//!
//! | TrustIR | Clean | why it denotes the same function |
//! |---|---|---|
//! | entry block param `i` of `n` | `BVar(n-1-i)` | one binder per param, leftmost outermost |
//! | `Const { ty: UN, Int(v) }` | `UIntN.ofNat v` | `UIntN.ofNat` is `n mod 2^N`; admitted only for `0 <= v < 2^N`, where that is `v` |
//! | `BinOp Add` | `UIntN.add` | `= ofNat (toNat a + toNat b)`, i.e. wrapping add |
//! | `BinOp Sub` | `UIntN.sub` | `= ofNat (toNat a + (2^N - toNat b))`, i.e. wrapping sub — measured, NOT `Nat` monus |
//! | `BinOp Mul` | `UIntN.mul` | `= ofNat (toNat a * toNat b)`, i.e. wrapping mul |
//! | `BinOp And`/`Or` | `UIntN.land`/`UIntN.lor` | bitwise, total, no edge cases to disagree about |
//! | `Copy` | the operand's term | a pure move |
//! | `ICmp Ult` | prop `UIntN.lt a b`, decision `UIntN.decLt a b` | `instLTUIntN = LT.mk _ UIntN.lt`, so the primitive is the class spelling after delta |
//! | `ICmp Ule` | prop `UIntN.le a b`, decision `UIntN.decLe a b` | as above via `instLEUIntN` |
//! | `ICmp Eq` | prop `@Eq.{1} UIntN a b`, decision `UIntN.decEq a b` | `UIntN` wraps a `BitVec N`, so propositional equality IS bit equality |
//! | `Select` | `@ite.{1} UIntN <prop> <decision> t e` | `ite` at `Sort 1`, since `UIntN : Type` |
//! | `Return [v]` | `v`'s term | the body under the binders |
//!
//! An `ICmp` does not produce a carrier term — it produces a Prop plus a `Decidable`
//! for it — so the value environment is a two-constructor `Reflected`, and a
//! `Select` whose condition is not a comparison is REFUSED rather than coerced.
//!
//! # What is refused, and why refusing beats guessing
//!
//! Everything not in the table above is refused BY NAME (see [`ReflectRefusal`]).
//! The refusals that are semantic rather than merely unimplemented:
//!
//!   * **`UDiv`/`URem`/`SDiv`/`SRem`** — `UIntN.div`/`.mod` in Clean are TOTAL
//!     (`x / 0 = 0`), while TrustIR's `UDiv` traps on a zero divisor
//!     (`interpret.rs`). Spelling one as the other would silently rename a
//!     different function.
//!   * **`Shl`/`LShr`/`AShr`** — TrustIR poisons on a shift amount at or above the
//!     width; `UIntN.shiftLeft`/`shiftRight` are total there. Same defect.
//!   * **`Xor`** — the prelude measured here has no `UInt8.xor`, and `a ^^^ b` does
//!     not even elaborate (`HXor UInt8 UInt8 UInt8` is unsynthesized). There is
//!     nothing to spell it as.
//!   * **signed carriers, `U128`, `Usize`, `Char`, `Bool`, floats, pointers** — no
//!     fixed-width `UIntN` in the Clean prelude denotes them. `Usize` in particular
//!     is target-width; guessing 64 would be a claim about the target that this
//!     function is in no position to make.
//!   * **`ICmp Ne/Ugt/Uge/S*`** — reflectable in principle, but only `Ult`/`Ule`/`Eq`
//!     were justified against measured prelude constants here, and an unjustified
//!     comparison in a `Select` condition is exactly the place a wrong reflection
//!     would be invisible.
//!
//! # Two things a defeq-judged round trip cannot decide (both measured here)
//!
//! 1. **`Select` does not record which `Decidable` witness the source used.**
//!    Clean's elaborator picks `instDecidableUIntNLt` for `if a < b` but
//!    `instDecidableNatLt` on the `Nat` projections for `if a < 10`, and the two are
//!    NOT definitionally equal under an open operand. TrustIR carries the
//!    proposition and nothing about the witness.
//!    `a_numeral_on_the_right_of_a_comparison_changes_the_decidable_witness_only`
//!    isolates this to the witness alone: the reflected PROPOSITION is accepted, and
//!    substituting the declaration's own witness into the otherwise-identical
//!    reflection makes the kernel accept. Consequence: a kernel REJECTION of a
//!    `Select` reflection is not by itself evidence of a wrong body. An ACCEPTANCE
//!    still is evidence of a right one, since definitional equality implies equal
//!    values — which is why the numeral-comparison shape is deliberately left out of
//!    the must-agree battery rather than papered over.
//!
//! 2. **The emission is not injective on `Select` conditions.** `if a = b` and
//!    `if a == b` produce byte-identical TrustIR while their declarations are
//!    definitionally distinct (`@Eq UInt8 a b` versus `(a == b) = true`). No single
//!    spelling can be def-eq to both. This reflector picks `@Eq`, the one the IR's
//!    `ICmp Eq` names directly, and
//!    `two_definitionally_distinct_clean_bodies_emit_identical_ir` records the
//!    rejection of the other so that nobody later teaches the reflector to guess
//!    which surface syntax was written — that guess is unrecoverable from the IR,
//!    and a reflector that appears to make it is reading something other than the IR.
//!
//! # What a green here does and does not mean
//!
//! A passing `is_def_eq` says: the emitted TrustIR function, read by a reader who
//! does not know how it was produced, denotes the same mathematical function as the
//! Clean declaration's own value — as judged by the CIC kernel. It says nothing
//! about shapes this file refuses, and it is not itself proof authority: the gate on
//! a Clean-origin body remains `trust-clean-origin`'s.

use std::collections::HashMap;

use clean_kernel::env::Environment;
use clean_kernel::expr::{BinderInfo, Expr};
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::tc::TypeChecker;
use trust_certify::clean_island::CleanIslandSession;
use trust_ir::{BinOp, Block, Constant, FuncId, FuncTyId, ICmpOp, Inst, Ty, ValueId};

// ════════════════════════════════════════════════════════════════════════════
// The carrier
// ════════════════════════════════════════════════════════════════════════════

/// One unsigned machine carrier, with the Clean type that denotes it.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct Carrier {
    /// `UInt8` / `UInt16` / `UInt32` / `UInt64`.
    clean: &'static str,
    bits: u32,
}

impl Carrier {
    fn of(ty: &Ty) -> Option<Self> {
        Some(match ty {
            Ty::U8 => Carrier { clean: "UInt8", bits: 8 },
            Ty::U16 => Carrier { clean: "UInt16", bits: 16 },
            Ty::U32 => Carrier { clean: "UInt32", bits: 32 },
            Ty::U64 => Carrier { clean: "UInt64", bits: 64 },
            _ => return None,
        })
    }

    /// The Clean type constant, e.g. `UInt8`.
    fn ty_expr(self) -> Expr {
        konst(self.clean)
    }

    /// A member constant of the carrier's namespace, e.g. `UInt8.add`.
    fn member(self, suffix: &str) -> Expr {
        konst(&format!("{}.{suffix}", self.clean))
    }

    /// `2^bits`, as a `u128` (exact for every width this reflector admits).
    fn modulus(self) -> u128 {
        1u128 << self.bits
    }
}

fn konst(n: &str) -> Expr {
    Expr::const_(Name::from_string(n), vec![])
}

// ════════════════════════════════════════════════════════════════════════════
// Refusals
// ════════════════════════════════════════════════════════════════════════════

/// Why this reflector declined. Every variant names the construct it could not
/// spell — a refusal is a fact about this reflector's vocabulary, never a verdict
/// about the body.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReflectRefusal {
    /// More (or fewer) than one basic block: this reflector is straight-line only.
    NotStraightLine { blocks: usize },
    /// `Function::entry` names no block in `Function::blocks`.
    EntryBlockMissing,
    /// A type appeared that no `UIntN` in the Clean prelude denotes.
    UnsupportedCarrier { ty: String },
    /// Two different unsigned widths in one body; the lambda has one carrier.
    MixedCarriers { first: &'static str, then: &'static str },
    /// An `Inst` variant with no spelling here.
    UnsupportedInst { inst: &'static str },
    /// A `BinOp` with no spelling here (see the module docs for which are
    /// semantic refusals rather than gaps).
    UnsupportedBinOp { op: &'static str },
    /// An `ICmp` with no spelling here.
    UnsupportedICmp { op: &'static str },
    /// A `Constant` variant that is not an in-range unsigned integer.
    UnsupportedConstant { detail: String },
    /// An integer constant outside `0 ..< 2^bits` of its own carrier.
    ConstantOutOfCarrier { value: i128, carrier: &'static str },
    /// A value was used before any instruction or parameter defined it.
    UndefinedValue { value: ValueId },
    /// One `ValueId` defined twice: not SSA, so no single denotation.
    RedefinedValue { value: ValueId },
    /// A carrier term was required but the value is a comparison (a Prop plus a
    /// `Decidable`), or vice versa.
    WrongValueSort { value: ValueId, wanted: &'static str },
    /// An instruction produced a number of results this reflector cannot place.
    UnexpectedResultArity { inst: &'static str, results: usize },
    /// The block does not end in `Return`, or has code after it.
    MalformedTerminator { detail: String },
    /// `Return` with a value count other than one.
    UnsupportedReturnArity { values: usize },
    /// No parameter and no instruction fixed a carrier, so there is no binder
    /// type and no result type to speak of.
    NoCarrier,
}

impl std::fmt::Display for ReflectRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Values
// ════════════════════════════════════════════════════════════════════════════

/// What an SSA value denotes in Clean.
///
/// Deliberately two-sorted. A `ValueId` produced by `ICmp` is `Ty::Bool` in the IR,
/// but in CIC the natural denotation is a `Prop` together with the `Decidable`
/// instance `ite` needs. Collapsing the two sorts is how a reflector ends up
/// coercing a condition it did not actually understand.
#[derive(Clone, Debug)]
enum Reflected {
    /// A term of the carrier type.
    Term(Expr),
    /// A decidable comparison: the proposition and a `Decidable` for it.
    Decision { prop: Expr, decidable: Expr },
}

// ════════════════════════════════════════════════════════════════════════════
// The reflector
// ════════════════════════════════════════════════════════════════════════════

/// Rebuild a single-basic-block `trust_ir::Function` over one unsigned machine
/// carrier as a closed `clean_kernel::Expr` — a lambda with one binder per entry
/// block parameter, de Bruijn indexed, leftmost parameter outermost.
///
/// # Errors
///
/// [`ReflectRefusal`], by name, for every construct outside the table in the module
/// docs. A refusal is always preferred to a spelling this reflector cannot justify.
pub fn reflect_straight_line_function(
    func: &trust_ir::Function,
) -> Result<Expr, ReflectRefusal> {
    if func.blocks.len() != 1 {
        return Err(ReflectRefusal::NotStraightLine { blocks: func.blocks.len() });
    }
    let block: &Block = func
        .blocks
        .iter()
        .find(|b| b.id == func.entry)
        .ok_or(ReflectRefusal::EntryBlockMissing)?;

    let mut r = Reflector { carrier: None, values: HashMap::new() };

    // ── binders ────────────────────────────────────────────────────────────
    // Parameter `i` of `n` is bound by the `i`-th binder from the outside, so under
    // all `n` binders it is `BVar(n - 1 - i)`.
    let n = block.params.len();
    let mut binder_tys = Vec::with_capacity(n);
    for (i, (id, ty)) in block.params.iter().enumerate() {
        let carrier = r.unify(ty)?;
        binder_tys.push(carrier.ty_expr());
        let idx = u32::try_from(n - 1 - i).expect("parameter count fits u32");
        r.define(*id, Reflected::Term(Expr::bvar(idx)))?;
    }

    // ── body ───────────────────────────────────────────────────────────────
    let mut result: Option<Expr> = None;
    for (pos, node) in block.body.iter().enumerate() {
        if result.is_some() {
            return Err(ReflectRefusal::MalformedTerminator {
                detail: format!("instruction {pos} follows the `Return`"),
            });
        }
        if let Inst::Return { values } = &node.inst {
            let [only] = values.as_slice() else {
                return Err(ReflectRefusal::UnsupportedReturnArity { values: values.len() });
            };
            result = Some(r.term(*only)?);
            continue;
        }
        let value = r.reflect_inst(&node.inst)?;
        let [out] = node.results.as_slice() else {
            return Err(ReflectRefusal::UnexpectedResultArity {
                inst: inst_name(&node.inst),
                results: node.results.len(),
            });
        };
        r.define(*out, value)?;
    }

    let mut body = result.ok_or_else(|| ReflectRefusal::MalformedTerminator {
        detail: "the block has no `Return`".to_owned(),
    })?;
    if r.carrier.is_none() {
        return Err(ReflectRefusal::NoCarrier);
    }

    // ── close ──────────────────────────────────────────────────────────────
    for ty in binder_tys.into_iter().rev() {
        body = Expr::lam(BinderInfo::Default, ty, body);
    }
    Ok(body)
}

struct Reflector {
    carrier: Option<Carrier>,
    values: HashMap<ValueId, Reflected>,
}

impl Reflector {
    /// Fold `ty` into the single carrier this body is allowed to have.
    fn unify(&mut self, ty: &Ty) -> Result<Carrier, ReflectRefusal> {
        let c = Carrier::of(ty)
            .ok_or_else(|| ReflectRefusal::UnsupportedCarrier { ty: format!("{ty:?}") })?;
        match self.carrier {
            None => {
                self.carrier = Some(c);
                Ok(c)
            }
            Some(prev) if prev == c => Ok(c),
            Some(prev) => Err(ReflectRefusal::MixedCarriers { first: prev.clean, then: c.clean }),
        }
    }

    fn define(&mut self, id: ValueId, v: Reflected) -> Result<(), ReflectRefusal> {
        if self.values.insert(id, v).is_some() {
            return Err(ReflectRefusal::RedefinedValue { value: id });
        }
        Ok(())
    }

    fn get(&self, id: ValueId) -> Result<&Reflected, ReflectRefusal> {
        self.values.get(&id).ok_or(ReflectRefusal::UndefinedValue { value: id })
    }

    /// The carrier term denoted by `id`, or a refusal if it denotes a comparison.
    fn term(&self, id: ValueId) -> Result<Expr, ReflectRefusal> {
        match self.get(id)? {
            Reflected::Term(e) => Ok(e.clone()),
            Reflected::Decision { .. } => {
                Err(ReflectRefusal::WrongValueSort { value: id, wanted: "a carrier term" })
            }
        }
    }

    /// The decidable comparison denoted by `id`, or a refusal.
    fn decision(&self, id: ValueId) -> Result<(Expr, Expr), ReflectRefusal> {
        match self.get(id)? {
            Reflected::Decision { prop, decidable } => Ok((prop.clone(), decidable.clone())),
            Reflected::Term(_) => Err(ReflectRefusal::WrongValueSort {
                value: id,
                wanted: "a decidable comparison",
            }),
        }
    }

    fn reflect_inst(&mut self, inst: &Inst) -> Result<Reflected, ReflectRefusal> {
        match inst {
            // ── constants ──────────────────────────────────────────────────
            Inst::Const { ty, value } => {
                let c = self.unify(ty)?;
                let Constant::Int(v) = value else {
                    return Err(ReflectRefusal::UnsupportedConstant {
                        detail: constant_name(value).to_owned(),
                    });
                };
                // `UIntN.ofNat` is `n mod 2^N`. It denotes exactly `v` only when `v`
                // is already in the carrier, so anything else is refused rather than
                // silently reduced.
                if *v < 0 || (*v as u128) >= c.modulus() {
                    return Err(ReflectRefusal::ConstantOutOfCarrier {
                        value: *v,
                        carrier: c.clean,
                    });
                }
                let n = u64::try_from(*v).expect("checked to be in 0 ..< 2^64");
                Ok(Reflected::Term(Expr::app(c.member("ofNat"), Expr::nat_lit(n))))
            }

            // ── arithmetic ────────────────────────────────────────────────
            Inst::BinOp { op, ty, lhs, rhs } => {
                let c = self.unify(ty)?;
                let suffix = match op {
                    BinOp::Add => "add",
                    BinOp::Sub => "sub",
                    BinOp::Mul => "mul",
                    BinOp::And => "land",
                    BinOp::Or => "lor",
                    other => return Err(ReflectRefusal::UnsupportedBinOp { op: binop_name(*other) }),
                };
                let (a, b) = (self.term(*lhs)?, self.term(*rhs)?);
                Ok(Reflected::Term(Expr::apps(c.member(suffix), [a, b])))
            }

            // ── comparisons ───────────────────────────────────────────────
            Inst::ICmp { op, ty, lhs, rhs } => {
                let c = self.unify(ty)?;
                let (a, b) = (self.term(*lhs)?, self.term(*rhs)?);
                let (prop, decidable) = match op {
                    ICmpOp::Ult => (
                        Expr::apps(c.member("lt"), [a.clone(), b.clone()]),
                        Expr::apps(c.member("decLt"), [a, b]),
                    ),
                    ICmpOp::Ule => (
                        Expr::apps(c.member("le"), [a.clone(), b.clone()]),
                        Expr::apps(c.member("decLe"), [a, b]),
                    ),
                    // `@Eq.{1} UIntN a b`: `UIntN` wraps a `BitVec N`, so two
                    // carrier values are propositionally equal exactly when their
                    // bit patterns are, which is what TrustIR's `ICmp Eq` compares.
                    ICmpOp::Eq => (
                        Expr::apps(
                            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                            [c.ty_expr(), a.clone(), b.clone()],
                        ),
                        Expr::apps(c.member("decEq"), [a, b]),
                    ),
                    other => {
                        return Err(ReflectRefusal::UnsupportedICmp { op: icmp_name(*other) });
                    }
                };
                Ok(Reflected::Decision { prop, decidable })
            }

            // ── choice ────────────────────────────────────────────────────
            Inst::Select { ty, cond, then_val, else_val } => {
                let c = self.unify(ty)?;
                let (prop, decidable) = self.decision(*cond)?;
                let then_e = self.term(*then_val)?;
                let else_e = self.term(*else_val)?;
                // `@ite.{u} (α : Sort u) (c : Prop) [Decidable c] (t e : α) : α`.
                // `UIntN : Type = Sort 1`, so `u = 1`.
                let ite = Expr::const_(
                    Name::from_string("ite"),
                    vec![Level::succ(Level::zero())],
                );
                Ok(Reflected::Term(Expr::apps(
                    ite,
                    [c.ty_expr(), prop, decidable, then_e, else_e],
                )))
            }

            // ── moves ─────────────────────────────────────────────────────
            Inst::Copy { ty, operand } => {
                self.unify(ty)?;
                Ok(Reflected::Term(self.term(*operand)?))
            }

            other => Err(ReflectRefusal::UnsupportedInst { inst: inst_name(other) }),
        }
    }
}

// ── names, for refusals that must be readable ─────────────────────────────

fn binop_name(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => "Add",
        BinOp::Sub => "Sub",
        BinOp::Mul => "Mul",
        BinOp::UDiv => "UDiv",
        BinOp::SDiv => "SDiv",
        BinOp::URem => "URem",
        BinOp::SRem => "SRem",
        BinOp::FAdd => "FAdd",
        BinOp::FSub => "FSub",
        BinOp::FMul => "FMul",
        BinOp::FDiv => "FDiv",
        BinOp::FRem => "FRem",
        BinOp::FMin => "FMin",
        BinOp::FMax => "FMax",
        BinOp::And => "And",
        BinOp::Or => "Or",
        BinOp::Xor => "Xor",
        BinOp::Shl => "Shl",
        BinOp::LShr => "LShr",
        BinOp::AShr => "AShr",
        BinOp::BAnd => "BAnd",
        BinOp::BOr => "BOr",
        BinOp::BXor => "BXor",
    }
}

fn icmp_name(op: ICmpOp) -> &'static str {
    match op {
        ICmpOp::Eq => "Eq",
        ICmpOp::Ne => "Ne",
        ICmpOp::Ult => "Ult",
        ICmpOp::Ule => "Ule",
        ICmpOp::Ugt => "Ugt",
        ICmpOp::Uge => "Uge",
        ICmpOp::Slt => "Slt",
        ICmpOp::Sle => "Sle",
        ICmpOp::Sgt => "Sgt",
        ICmpOp::Sge => "Sge",
    }
}

fn constant_name(c: &Constant) -> &'static str {
    match c {
        Constant::Int(_) => "Int",
        Constant::U128(_) => "U128",
        Constant::Bytes { .. } => "Bytes",
        Constant::Float(_) => "Float",
        Constant::Bool(_) => "Bool",
        Constant::Aggregate(_) => "Aggregate",
        Constant::Array(_) => "Array",
        Constant::Vector(_) => "Vector",
        Constant::Sequence(_) => "Sequence",
        Constant::Set(_) => "Set",
        _ => "(other Constant)",
    }
}

fn inst_name(i: &Inst) -> &'static str {
    match i {
        Inst::BinOp { .. } => "BinOp",
        Inst::UnOp { .. } => "UnOp",
        Inst::Overflow { .. } => "Overflow",
        Inst::ICmp { .. } => "ICmp",
        Inst::FCmp { .. } => "FCmp",
        Inst::Cast { .. } => "Cast",
        Inst::Load { .. } => "Load",
        Inst::Store { .. } => "Store",
        Inst::Alloca { .. } => "Alloca",
        Inst::HeapAlloc { .. } => "HeapAlloc",
        Inst::GEP { .. } => "GEP",
        Inst::Br { .. } => "Br",
        Inst::CondBr { .. } => "CondBr",
        Inst::Switch { .. } => "Switch",
        Inst::Call { .. } => "Call",
        Inst::CallIndirect { .. } => "CallIndirect",
        Inst::Return { .. } => "Return",
        Inst::ExtractField { .. } => "ExtractField",
        Inst::InsertField { .. } => "InsertField",
        Inst::ExtractElement { .. } => "ExtractElement",
        Inst::InsertElement { .. } => "InsertElement",
        Inst::Const { .. } => "Const",
        Inst::NullPtr => "NullPtr",
        Inst::GlobalAddr { .. } => "GlobalAddr",
        Inst::Undef { .. } => "Undef",
        Inst::Assume { .. } => "Assume",
        Inst::Assert { .. } => "Assert",
        Inst::Unreachable => "Unreachable",
        Inst::Copy { .. } => "Copy",
        Inst::Select { .. } => "Select",
        _ => "(other Inst)",
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Harness
// ════════════════════════════════════════════════════════════════════════════

/// Every Clean declaration the batteries below drive, as `(name, source)`.
const PROGRAM: &[(&str, &str)] = &[
    // parameter projection
    ("p_first", "def p_first (a : UInt8) (b : UInt8) : UInt8 := a"),
    ("p_second", "def p_second (a : UInt8) (b : UInt8) : UInt8 := b"),
    ("p_third", "def p_third (a : UInt8) (b : UInt8) (c : UInt8) : UInt8 := c"),
    // integer constants
    ("k_zero", "def k_zero : UInt8 := 0"),
    ("k_seven", "def k_seven : UInt8 := 7"),
    ("k_max8", "def k_max8 : UInt8 := 255"),
    ("k_big64", "def k_big64 : UInt64 := 1000000"),
    // Add / Sub / Mul, at every admitted width
    ("a8", "def a8 (a : UInt8) (b : UInt8) : UInt8 := a + b"),
    ("s8", "def s8 (a : UInt8) (b : UInt8) : UInt8 := a - b"),
    ("m8", "def m8 (a : UInt8) (b : UInt8) : UInt8 := a * b"),
    ("a16", "def a16 (a : UInt16) (b : UInt16) : UInt16 := a + b"),
    ("s16", "def s16 (a : UInt16) (b : UInt16) : UInt16 := a - b"),
    ("m16", "def m16 (a : UInt16) (b : UInt16) : UInt16 := a * b"),
    ("a32", "def a32 (a : UInt32) (b : UInt32) : UInt32 := a + b"),
    ("s32", "def s32 (a : UInt32) (b : UInt32) : UInt32 := a - b"),
    ("m32", "def m32 (a : UInt32) (b : UInt32) : UInt32 := a * b"),
    ("a64", "def a64 (a : UInt64) (b : UInt64) : UInt64 := a + b"),
    ("s64", "def s64 (a : UInt64) (b : UInt64) : UInt64 := a - b"),
    ("m64", "def m64 (a : UInt64) (b : UInt64) : UInt64 := a * b"),
    // constants mixed into arithmetic
    ("lit_add", "def lit_add (a : UInt8) : UInt8 := a + 7"),
    ("lit_sub", "def lit_sub (a : UInt8) : UInt8 := a - 1"),
    ("lit_mul64", "def lit_mul64 (a : UInt64) : UInt64 := a * 1000000"),
    // nesting — the operand order that a commutative-only battery cannot see
    ("nest_mul_add", "def nest_mul_add (a : UInt8) (b : UInt8) (c : UInt8) : UInt8 := (a + b) * c"),
    ("nest_sub_sub", "def nest_sub_sub (a : UInt8) (b : UInt8) (c : UInt8) : UInt8 := (a - b) - c"),
    ("nest_deep", "def nest_deep (a : UInt32) (b : UInt32) (c : UInt32) : UInt32 := (a * b) - (a + c)"),
    // Select over `<` and `<=`
    ("min8", "def min8 (a : UInt8) (b : UInt8) : UInt8 := if a < b then a else b"),
    ("max8", "def max8 (a : UInt8) (b : UInt8) : UInt8 := if a < b then b else a"),
    ("min16", "def min16 (a : UInt16) (b : UInt16) : UInt16 := if a < b then a else b"),
    ("min32", "def min32 (a : UInt32) (b : UInt32) : UInt32 := if a < b then a else b"),
    ("min64", "def min64 (a : UInt64) (b : UInt64) : UInt64 := if a < b then a else b"),
    ("le8", "def le8 (a : UInt8) (b : UInt8) : UInt8 := if a <= b then a else b"),
    ("eq8", "def eq8 (a : UInt8) (b : UInt8) : UInt8 := if a = b then a else b"),
    ("eq32", "def eq32 (a : UInt32) (b : UInt32) : UInt32 := if a = b then a else b"),
    // bitwise
    ("and8", "def and8 (a : UInt8) (b : UInt8) : UInt8 := a &&& b"),
    ("or8", "def or8 (a : UInt8) (b : UInt8) : UInt8 := a ||| b"),
];

/// Elaborate and kernel-check every declaration in [`PROGRAM`], returning the
/// resulting Clean environment.
fn program_environment() -> Environment {
    let mut session = CleanIslandSession::new();
    for (name, src) in PROGRAM {
        let outcome = session.check(src);
        assert!(!outcome.is_rejected(), "island `{name}` was rejected: {:?}", outcome.errors);
    }
    session.environment().expect("a clean session has an environment").clone()
}

/// Drive the emitter to obtain the `trust_ir::Function` for `name`.
///
/// This is the only place the emitter is used — as a SOURCE of input, never as a
/// reference for how to reflect it.
fn emitted(env: &Environment, name: &str) -> trust_ir::Function {
    let plan = trust_clean_origin::plan_clean_origin_body(env, name)
        .unwrap_or_else(|e| panic!("`{name}` did not plan: {e:?}"));
    trust_clean_ir::emit_clean_origin_function(&plan, FuncId::new(0), FuncTyId::new(0))
        .unwrap_or_else(|e| panic!("`{name}` did not emit: {e:?}"))
}

fn declared_value(env: &Environment, name: &str) -> Expr {
    env.get_const(&Name::from_string(name))
        .unwrap_or_else(|| panic!("`{name}` is not in the environment"))
        .value
        .clone()
        .unwrap_or_else(|| panic!("`{name}` has no value"))
}

// ════════════════════════════════════════════════════════════════════════════
// The agreements
// ════════════════════════════════════════════════════════════════════════════

/// The main event: for every shape in [`PROGRAM`], emit, reflect independently,
/// and let the CIC kernel decide.
#[test]
fn kernel_accepts_the_independent_reflection_of_every_covered_shape() {
    let env = program_environment();
    let tc = TypeChecker::new(&env);
    let mut agreed = 0usize;
    for (name, _) in PROGRAM {
        let func = emitted(&env, name);
        let reflected = reflect_straight_line_function(&func)
            .unwrap_or_else(|e| panic!("`{name}` was refused by the reflector: {e}"));
        let declared = declared_value(&env, name);
        assert!(
            tc.is_def_eq(&reflected, &declared),
            "kernel REJECTED the independent reflection of `{name}`\n  reflected = {reflected:?}\n  declared  = {declared:?}",
        );
        agreed += 1;
    }
    assert_eq!(agreed, PROGRAM.len());
    println!("kernel agreements: {agreed}");
}

/// Coverage bookkeeping, asserted rather than asserted-in-prose: every admitted
/// width really is exercised, and so is every `Inst` variant this file spells.
#[test]
fn the_battery_actually_exercises_every_covered_construct() {
    let env = program_environment();
    let mut widths: Vec<u32> = Vec::new();
    let (mut binops, mut icmps) = (Vec::<&str>::new(), Vec::<&str>::new());
    let (mut consts, mut selects, mut params) = (0usize, 0usize, 0usize);
    for (name, _) in PROGRAM {
        let func = emitted(&env, name);
        let block = &func.blocks[0];
        params += block.params.len();
        for (_, ty) in &block.params {
            if let Some(c) = Carrier::of(ty) {
                if !widths.contains(&c.bits) {
                    widths.push(c.bits);
                }
            }
        }
        for node in &block.body {
            match &node.inst {
                Inst::BinOp { op, .. } => {
                    let n = binop_name(*op);
                    if !binops.contains(&n) {
                        binops.push(n);
                    }
                }
                Inst::ICmp { op, .. } => {
                    let n = icmp_name(*op);
                    if !icmps.contains(&n) {
                        icmps.push(n);
                    }
                }
                Inst::Const { .. } => consts += 1,
                Inst::Select { .. } => selects += 1,
                _ => {}
            }
        }
    }
    widths.sort_unstable();
    binops.sort_unstable();
    icmps.sort_unstable();
    assert_eq!(widths, vec![8, 16, 32, 64], "every admitted carrier width must be exercised");
    assert_eq!(binops, vec!["Add", "And", "Mul", "Or", "Sub"]);
    assert_eq!(icmps, vec!["Eq", "Ule", "Ult"]);
    assert!(consts >= 7, "integer constants exercised: {consts}");
    assert!(selects >= 7, "selects exercised: {selects}");
    assert!(params >= 2, "parameter projections exercised: {params}");
}

// ════════════════════════════════════════════════════════════════════════════
// Non-vacuity — a reflector that returned the declaration would pass everything
// above, so each mutation below must be REJECTED by the kernel
// ════════════════════════════════════════════════════════════════════════════

/// Rewrite the first `BinOp` in the entry block to a different operator.
fn mutate_binop(func: &trust_ir::Function, to: BinOp) -> trust_ir::Function {
    let mut f = func.clone();
    for node in &mut f.blocks[0].body {
        if let Inst::BinOp { op, .. } = &mut node.inst {
            *op = to;
            return f;
        }
    }
    panic!("no BinOp to mutate");
}

/// Swap the operands of the first `BinOp` in the entry block.
fn swap_binop_operands(func: &trust_ir::Function) -> trust_ir::Function {
    let mut f = func.clone();
    for node in &mut f.blocks[0].body {
        if let Inst::BinOp { lhs, rhs, .. } = &mut node.inst {
            std::mem::swap(lhs, rhs);
            return f;
        }
    }
    panic!("no BinOp to mutate");
}

/// Swap the arms of the first `Select` in the entry block.
fn swap_select_arms(func: &trust_ir::Function) -> trust_ir::Function {
    let mut f = func.clone();
    for node in &mut f.blocks[0].body {
        if let Inst::Select { then_val, else_val, .. } = &mut node.inst {
            std::mem::swap(then_val, else_val);
            return f;
        }
    }
    panic!("no Select to mutate");
}

/// Swap the operands of the first `ICmp` in the entry block.
fn swap_icmp_operands(func: &trust_ir::Function) -> trust_ir::Function {
    let mut f = func.clone();
    for node in &mut f.blocks[0].body {
        if let Inst::ICmp { lhs, rhs, .. } = &mut node.inst {
            std::mem::swap(lhs, rhs);
            return f;
        }
    }
    panic!("no ICmp to mutate");
}

/// Change the first integer constant in the entry block.
fn mutate_constant(func: &trust_ir::Function, to: i128) -> trust_ir::Function {
    let mut f = func.clone();
    for node in &mut f.blocks[0].body {
        if let Inst::Const { value, .. } = &mut node.inst {
            *value = Constant::Int(to);
            return f;
        }
    }
    panic!("no Const to mutate");
}

/// Return a different SSA value than the body computes.
fn mutate_return(func: &trust_ir::Function, to: ValueId) -> trust_ir::Function {
    let mut f = func.clone();
    for node in &mut f.blocks[0].body {
        if let Inst::Return { values } = &mut node.inst {
            *values = vec![to];
            return f;
        }
    }
    panic!("no Return to mutate");
}

#[test]
fn kernel_rejects_a_deliberately_wrong_reflection() {
    let env = program_environment();
    let tc = TypeChecker::new(&env);

    // Each row: (declaration under test, a WRONG function, what was broken).
    let cases: Vec<(&str, trust_ir::Function, &str)> = vec![
        ("a8", mutate_binop(&emitted(&env, "a8"), BinOp::Sub), "a + b reflected as a - b"),
        ("a8", mutate_binop(&emitted(&env, "a8"), BinOp::Mul), "a + b reflected as a * b"),
        ("s8", mutate_binop(&emitted(&env, "s8"), BinOp::Add), "a - b reflected as a + b"),
        ("s8", swap_binop_operands(&emitted(&env, "s8")), "a - b reflected as b - a"),
        ("s64", swap_binop_operands(&emitted(&env, "s64")), "a - b reflected as b - a at 64 bits"),
        ("m8", mutate_binop(&emitted(&env, "m8"), BinOp::And), "a * b reflected as a &&& b"),
        ("and8", mutate_binop(&emitted(&env, "and8"), BinOp::Or), "a &&& b reflected as a ||| b"),
        ("k_seven", mutate_constant(&emitted(&env, "k_seven"), 8), "7 reflected as 8"),
        ("lit_add", mutate_constant(&emitted(&env, "lit_add"), 6), "a + 7 reflected as a + 6"),
        ("min8", swap_select_arms(&emitted(&env, "min8")), "min reflected as max"),
        ("min8", swap_icmp_operands(&emitted(&env, "min8")), "a < b reflected as b < a"),
        ("min32", swap_select_arms(&emitted(&env, "min32")), "min reflected as max at 32 bits"),
        ("le8", swap_select_arms(&emitted(&env, "le8")), "<=-min reflected as <=-max"),
        ("p_first", mutate_return(&emitted(&env, "p_first"), ValueId::new(1)), "a reflected as b"),
        (
            "nest_sub_sub",
            swap_binop_operands(&emitted(&env, "nest_sub_sub")),
            "(a - b) - c reflected as (b - a) - c",
        ),
    ];

    for (declaration, wrong, what) in cases {
        let reflected = reflect_straight_line_function(&wrong)
            .unwrap_or_else(|e| panic!("the wrong function for `{declaration}` did not even reflect: {e}"));
        let declared = declared_value(&env, declaration);
        assert!(
            !tc.is_def_eq(&reflected, &declared),
            "kernel ACCEPTED a wrong reflection of `{declaration}` ({what}) — the round trip is vacuous",
        );
    }
}

/// Cross-product control: the reflection of one declaration must not satisfy a
/// different declaration. Catches a reflector that quietly returns something
/// canonical instead of the body it was given.
#[test]
fn distinct_declarations_do_not_collapse_onto_one_another() {
    let env = program_environment();
    let tc = TypeChecker::new(&env);
    // Pairwise-distinct functions of two UInt8 arguments.
    let distinct = ["a8", "s8", "m8", "min8", "max8", "and8", "or8", "p_first", "p_second"];
    for a in distinct {
        let reflected = reflect_straight_line_function(&emitted(&env, a)).expect("reflects");
        for b in distinct {
            let declared = declared_value(&env, b);
            let eq = tc.is_def_eq(&reflected, &declared);
            assert_eq!(
                eq,
                a == b,
                "`{a}` reflected vs `{b}` declared: kernel said {eq}, expected {}",
                a == b
            );
        }
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Two places where the IR does not determine the Clean term up to DEFINITIONAL
// equality. Neither is a defect in the emitted body — both are limits on what a
// defeq-judged round trip can conclude, and both are measured rather than argued.
// ════════════════════════════════════════════════════════════════════════════

/// Wrap `body` in `n` `UIntN` binders, so an open subterm can be compared as a
/// closed one.
fn under_binders(carrier: Carrier, n: usize, body: Expr) -> Expr {
    let mut e = body;
    for _ in 0..n {
        e = Expr::lam(BinderInfo::Default, carrier.ty_expr(), e);
    }
    e
}

/// Take `ite.{1} α c h t e` apart, if that is what `e` is.
fn split_ite(e: &Expr) -> Option<[Expr; 5]> {
    use clean_kernel::expr::ExprKind;
    match e.get_app_fn().kind() {
        ExprKind::Const(n, _) if n.to_string() == "ite" => {}
        _ => return None,
    }
    // `get_app_args_iter` yields innermost-first, so reverse into source order.
    let mut args: Vec<Expr> = e.get_app_args_iter().map(Clone::clone).collect();
    args.reverse();
    let [alpha, cond, dec, then_e, else_e] = args.as_slice() else { return None };
    Some([alpha.clone(), cond.clone(), dec.clone(), then_e.clone(), else_e.clone()])
}

/// Strip `n` leading lambdas.
fn strip_lams(e: &Expr, n: usize) -> Expr {
    use clean_kernel::expr::ExprKind;
    let mut cur = e.clone();
    for _ in 0..n {
        let ExprKind::Lam(_, _, body) = cur.kind() else { panic!("expected a lambda") };
        let next = body.as_ref().clone();
        cur = next;
    }
    cur
}

/// **Finding 1.** When the right operand of a `<` is a numeral, Clean's elaborator
/// synthesizes a DIFFERENT `Decidable` witness (`instDecidableNatLt` on the
/// `Nat` projections) than the carrier's registered one (`instDecidableUIntNLt`,
/// i.e. `UIntN.decLt`) — and the two are not definitionally equal under an open
/// operand. TrustIR's `ICmp` + `Select` records the PROPOSITION and nothing about
/// the witness, so no reflector can recover which one the source used.
///
/// This test pins the gap precisely: the proposition this reflector emits IS
/// definitionally the declaration's, and substituting the declaration's own
/// witness into this reflector's term makes the kernel accept. So the only
/// difference is the decision procedure, which does not change the function's
/// value — `Decidable` instances of one proposition are propositionally unique.
///
/// Consequence to carry: a kernel REJECTION of a `Select` reflection is not by
/// itself evidence of a wrong body. An ACCEPTANCE still is evidence of a right
/// one, since definitional equality implies equal values.
#[test]
fn a_numeral_on_the_right_of_a_comparison_changes_the_decidable_witness_only() {
    let mut session = CleanIslandSession::new();
    let src = "def lt_lit (a : UInt8) (b : UInt8) : UInt8 := if a < 10 then a else b";
    assert!(!session.check(src).is_rejected());
    let env = session.environment().expect("env").clone();
    let tc = TypeChecker::new(&env);
    let u8 = Carrier { clean: "UInt8", bits: 8 };

    let func = emitted(&env, "lt_lit");
    let mine = reflect_straight_line_function(&func).expect("reflects");
    let declared = declared_value(&env, "lt_lit");

    // 1. The kernel rejects the reflection outright.
    assert!(
        !tc.is_def_eq(&mine, &declared),
        "expected the numeral-comparison shape to be a measured defeq gap"
    );

    // 2. But the PROPOSITIONS agree.
    let [_, my_prop, my_dec, ..] = split_ite(&strip_lams(&mine, 2)).expect("an ite");
    let [_, their_prop, their_dec, ..] = split_ite(&strip_lams(&declared, 2)).expect("an ite");
    assert!(
        tc.is_def_eq(
            &under_binders(u8, 2, my_prop.clone()),
            &under_binders(u8, 2, their_prop.clone())
        ),
        "the reflected comparison must be the declaration's own proposition"
    );

    // 3. And the WITNESSES do not.
    assert!(
        !tc.is_def_eq(
            &under_binders(u8, 2, my_dec.clone()),
            &under_binders(u8, 2, their_dec.clone())
        ),
        "the two Decidable witnesses were expected to be definitionally distinct"
    );

    // 4. Swap in the declaration's witness and the kernel accepts — so the
    //    witness is the whole of the difference.
    let patched = under_binders(
        u8,
        2,
        Expr::apps(
            Expr::const_(Name::from_string("ite"), vec![Level::succ(Level::zero())]),
            [u8.ty_expr(), my_prop, their_dec, Expr::bvar(1), Expr::bvar(0)],
        ),
    );
    assert!(
        tc.is_def_eq(&patched, &declared),
        "with the declaration's own Decidable witness the reflection must be accepted"
    );
}

/// **Finding 2.** The emission is NOT injective on `Select` conditions. `if a = b`
/// and `if a == b` produce byte-identical TrustIR — one `ICmp Eq` feeding one
/// `Select` — while their Clean declarations are definitionally distinct
/// (`@Eq UInt8 a b` versus `(a == b) = true`). They denote the same function, but
/// only propositionally.
///
/// So a reflector must pick one of the two, and will be rejected on the other.
/// This reflector picks `@Eq`, which is the one the IR's `ICmp Eq` names directly.
/// The rejection of the `==` spelling is recorded here so nobody later "fixes" it
/// by teaching the reflector to guess which surface syntax was used — that guess
/// is unrecoverable from the IR, and a reflector that appears to make it is
/// reading something other than the IR.
#[test]
fn two_definitionally_distinct_clean_bodies_emit_identical_ir() {
    let mut session = CleanIslandSession::new();
    for src in [
        "def eq_prop (a : UInt8) (b : UInt8) : UInt8 := if a = b then a else b",
        "def eq_beq (a : UInt8) (b : UInt8) : UInt8 := if a == b then a else b",
    ] {
        assert!(!session.check(src).is_rejected());
    }
    let env = session.environment().expect("env").clone();
    let tc = TypeChecker::new(&env);

    let by_prop = emitted(&env, "eq_prop");
    let by_beq = emitted(&env, "eq_beq");

    // Identical IR bodies.
    assert_eq!(
        format!("{:?}", by_prop.blocks[0].body),
        format!("{:?}", by_beq.blocks[0].body),
        "`a = b` and `a == b` were expected to emit identical TrustIR"
    );

    // Definitionally distinct declarations.
    let d_prop = declared_value(&env, "eq_prop");
    let d_beq = declared_value(&env, "eq_beq");
    assert!(
        !tc.is_def_eq(&d_prop, &d_beq),
        "the two declarations were expected to be definitionally distinct"
    );

    // One reflection; accepted against one, rejected against the other.
    let mine = reflect_straight_line_function(&by_prop).expect("reflects");
    assert!(tc.is_def_eq(&mine, &d_prop), "the `Eq` spelling must satisfy `a = b`");
    assert!(
        !tc.is_def_eq(&mine, &d_beq),
        "no single spelling can satisfy both, and this one must not silently satisfy `==`"
    );
}

// ════════════════════════════════════════════════════════════════════════════
// The measurements this reflector's spellings rest on
// ════════════════════════════════════════════════════════════════════════════

/// Every semantic claim in the module docs, re-checked against the kernel rather
/// than trusted. If Clean's `UIntN.sub` were `Nat` monus lifted through `ofNat`
/// (`1 - 2 = 0`) instead of wrapping (`1 - 2 = 255`), spelling TrustIR's
/// `wrapping_sub` as `UIntN.sub` would be WRONG — and every `is_def_eq` above
/// would still pass, because the declaration uses the same constant. That is
/// exactly the class of error a round trip cannot see, so it is measured here.
#[test]
fn clean_primitives_have_the_semantics_this_reflector_assumes() {
    let env = program_environment();
    let tc = TypeChecker::new(&env);

    for c in [
        Carrier { clean: "UInt8", bits: 8 },
        Carrier { clean: "UInt16", bits: 16 },
        Carrier { clean: "UInt32", bits: 32 },
        Carrier { clean: "UInt64", bits: 64 },
    ] {
        let lit = |v: u64| Expr::app(c.member("ofNat"), Expr::nat_lit(v));
        let max = u64::try_from(c.modulus() - 1).expect("width <= 64");

        // ofNat is the identity on the carrier's own range.
        assert!(tc.is_def_eq(&lit(0), &lit(0)));
        assert!(!tc.is_def_eq(&lit(0), &lit(1)), "{}: ofNat 0 must differ from ofNat 1", c.clean);

        // add wraps: max + 1 = 0.
        let wrap_add = Expr::apps(c.member("add"), [lit(max), lit(1)]);
        assert!(
            tc.is_def_eq(&wrap_add, &lit(0)),
            "{}.add must be WRAPPING addition (max + 1 = 0)",
            c.clean
        );

        // sub wraps rather than saturating at zero: 0 - 1 = max.
        let wrap_sub = Expr::apps(c.member("sub"), [lit(0), lit(1)]);
        assert!(
            tc.is_def_eq(&wrap_sub, &lit(max)),
            "{}.sub must be WRAPPING subtraction (0 - 1 = max), not Nat monus",
            c.clean
        );
        assert!(
            !tc.is_def_eq(&wrap_sub, &lit(0)),
            "{}.sub must NOT be Nat monus (0 - 1 = 0)",
            c.clean
        );

        // mul wraps: max * 2 = max - 1.
        let wrap_mul = Expr::apps(c.member("mul"), [lit(max), lit(2)]);
        assert!(
            tc.is_def_eq(&wrap_mul, &lit(max - 1)),
            "{}.mul must be WRAPPING multiplication",
            c.clean
        );

        // land / lor are bitwise.
        assert!(
            tc.is_def_eq(&Expr::apps(c.member("land"), [lit(0b1100), lit(0b1010)]), &lit(0b1000)),
            "{}.land must be bitwise AND",
            c.clean
        );
        assert!(
            tc.is_def_eq(&Expr::apps(c.member("lor"), [lit(0b1100), lit(0b1010)]), &lit(0b1110)),
            "{}.lor must be bitwise OR",
            c.clean
        );

        // The primitive relation/decision constants this reflector emits are the
        // class-spelled ones after delta, so `ite` sees the same condition either way.
        let class_lt = Expr::apps(
            Expr::const_(Name::from_string("LT.lt"), vec![Level::zero()]),
            [c.ty_expr(), konst(&format!("instLT{}", c.clean)), lit(1), lit(2)],
        );
        assert!(
            tc.is_def_eq(&Expr::apps(c.member("lt"), [lit(1), lit(2)]), &class_lt),
            "{}.lt must be the LT.lt class spelling",
            c.clean
        );
        let class_le = Expr::apps(
            Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            [c.ty_expr(), konst(&format!("instLE{}", c.clean)), lit(1), lit(2)],
        );
        assert!(
            tc.is_def_eq(&Expr::apps(c.member("le"), [lit(1), lit(2)]), &class_le),
            "{}.le must be the LE.le class spelling",
            c.clean
        );
        assert!(
            tc.is_def_eq(
                &Expr::apps(c.member("decLt"), [lit(1), lit(2)]),
                &Expr::apps(konst(&format!("instDecidable{}Lt", c.clean)), [lit(1), lit(2)]),
            ),
            "{}.decLt must be the registered Decidable instance",
            c.clean
        );
        assert!(
            tc.is_def_eq(
                &Expr::apps(c.member("decLe"), [lit(1), lit(2)]),
                &Expr::apps(konst(&format!("instDecidable{}Le", c.clean)), [lit(1), lit(2)]),
            ),
            "{}.decLe must be the registered Decidable instance",
            c.clean
        );
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Refusals — each one named, each one proved to actually fire
// ════════════════════════════════════════════════════════════════════════════

/// Build a one-block function: `params`, then `body`, then `Return [ret]`.
fn hand_built(
    params: &[Ty],
    body: Vec<Inst>,
    ret: ValueId,
) -> trust_ir::Function {
    let mut f = trust_ir::Function::new(FuncId::new(0), "hand", FuncTyId::new(0), trust_ir::BlockId::new(0));
    let mut block = Block::new(trust_ir::BlockId::new(0));
    for (i, ty) in params.iter().enumerate() {
        block.params.push((ValueId::new(i as u32), ty.clone()));
    }
    let mut next = params.len() as u32;
    for inst in body {
        block.body.push(trust_ir::InstrNode::new(inst).with_result(ValueId::new(next)));
        next += 1;
    }
    block.body.push(trust_ir::InstrNode::new(Inst::Return { values: vec![ret] }));
    f.blocks.push(block);
    f
}

#[test]
fn every_shape_outside_the_vocabulary_is_refused_by_name() {
    use ReflectRefusal as R;

    // Signed carrier — no fixed-width `IntN` spelling was justified.
    let signed = hand_built(
        &[Ty::I32, Ty::I32],
        vec![Inst::BinOp { op: BinOp::Add, ty: Ty::I32, lhs: ValueId::new(0), rhs: ValueId::new(1) }],
        ValueId::new(2),
    );
    assert_eq!(
        reflect_straight_line_function(&signed),
        Err(R::UnsupportedCarrier { ty: "I32".to_owned() })
    );

    // `Usize` is target-width; guessing 64 would be a claim about the target.
    let usize_fn = hand_built(&[Ty::Usize], vec![], ValueId::new(0));
    assert_eq!(
        reflect_straight_line_function(&usize_fn),
        Err(R::UnsupportedCarrier { ty: "Usize".to_owned() })
    );

    // `U128` has no `UInt128` in the Clean prelude.
    let u128_fn = hand_built(&[Ty::U128], vec![], ValueId::new(0));
    assert_eq!(
        reflect_straight_line_function(&u128_fn),
        Err(R::UnsupportedCarrier { ty: "U128".to_owned() })
    );

    // Division: Clean's `.div` is total (`x / 0 = 0`), TrustIR's `UDiv` traps.
    let udiv = hand_built(
        &[Ty::U8, Ty::U8],
        vec![Inst::BinOp { op: BinOp::UDiv, ty: Ty::U8, lhs: ValueId::new(0), rhs: ValueId::new(1) }],
        ValueId::new(2),
    );
    assert_eq!(reflect_straight_line_function(&udiv), Err(R::UnsupportedBinOp { op: "UDiv" }));

    let urem = hand_built(
        &[Ty::U8, Ty::U8],
        vec![Inst::BinOp { op: BinOp::URem, ty: Ty::U8, lhs: ValueId::new(0), rhs: ValueId::new(1) }],
        ValueId::new(2),
    );
    assert_eq!(reflect_straight_line_function(&urem), Err(R::UnsupportedBinOp { op: "URem" }));

    // Shifts: TrustIR poisons at shift >= width, Clean's shifts are total there.
    for (op, name) in [(BinOp::Shl, "Shl"), (BinOp::LShr, "LShr"), (BinOp::AShr, "AShr")] {
        let f = hand_built(
            &[Ty::U8, Ty::U8],
            vec![Inst::BinOp { op, ty: Ty::U8, lhs: ValueId::new(0), rhs: ValueId::new(1) }],
            ValueId::new(2),
        );
        assert_eq!(reflect_straight_line_function(&f), Err(R::UnsupportedBinOp { op: name }));
    }

    // `Xor`: the measured prelude has no `UInt8.xor` at all.
    let xor = hand_built(
        &[Ty::U8, Ty::U8],
        vec![Inst::BinOp { op: BinOp::Xor, ty: Ty::U8, lhs: ValueId::new(0), rhs: ValueId::new(1) }],
        ValueId::new(2),
    );
    assert_eq!(reflect_straight_line_function(&xor), Err(R::UnsupportedBinOp { op: "Xor" }));

    // Comparisons outside `Ult`/`Ule`/`Eq`.
    for (op, name) in [
        (ICmpOp::Ne, "Ne"),
        (ICmpOp::Ugt, "Ugt"),
        (ICmpOp::Uge, "Uge"),
        (ICmpOp::Slt, "Slt"),
        (ICmpOp::Sle, "Sle"),
        (ICmpOp::Sgt, "Sgt"),
        (ICmpOp::Sge, "Sge"),
    ] {
        let f = hand_built(
            &[Ty::U8, Ty::U8],
            vec![
                Inst::ICmp { op, ty: Ty::U8, lhs: ValueId::new(0), rhs: ValueId::new(1) },
                Inst::Select {
                    ty: Ty::U8,
                    cond: ValueId::new(2),
                    then_val: ValueId::new(0),
                    else_val: ValueId::new(1),
                },
            ],
            ValueId::new(3),
        );
        assert_eq!(reflect_straight_line_function(&f), Err(R::UnsupportedICmp { op: name }));
    }

    // A `Select` whose condition is not a comparison is refused, never coerced.
    let bad_cond = hand_built(
        &[Ty::U8, Ty::U8],
        vec![Inst::Select {
            ty: Ty::U8,
            cond: ValueId::new(0),
            then_val: ValueId::new(0),
            else_val: ValueId::new(1),
        }],
        ValueId::new(2),
    );
    assert_eq!(
        reflect_straight_line_function(&bad_cond),
        Err(R::WrongValueSort { value: ValueId::new(0), wanted: "a decidable comparison" })
    );

    // A comparison used where a carrier term is required.
    let cmp_as_term = hand_built(
        &[Ty::U8, Ty::U8],
        vec![Inst::ICmp { op: ICmpOp::Ult, ty: Ty::U8, lhs: ValueId::new(0), rhs: ValueId::new(1) }],
        ValueId::new(2),
    );
    assert_eq!(
        reflect_straight_line_function(&cmp_as_term),
        Err(R::WrongValueSort { value: ValueId::new(2), wanted: "a carrier term" })
    );

    // Constants outside the carrier, and non-integer constants.
    let oob = hand_built(&[], vec![Inst::Const { ty: Ty::U8, value: Constant::Int(256) }], ValueId::new(0));
    assert_eq!(
        reflect_straight_line_function(&oob),
        Err(R::ConstantOutOfCarrier { value: 256, carrier: "UInt8" })
    );
    let neg = hand_built(&[], vec![Inst::Const { ty: Ty::U8, value: Constant::Int(-1) }], ValueId::new(0));
    assert_eq!(
        reflect_straight_line_function(&neg),
        Err(R::ConstantOutOfCarrier { value: -1, carrier: "UInt8" })
    );
    let boolean =
        hand_built(&[], vec![Inst::Const { ty: Ty::U8, value: Constant::Bool(true) }], ValueId::new(0));
    assert_eq!(
        reflect_straight_line_function(&boolean),
        Err(R::UnsupportedConstant { detail: "Bool".to_owned() })
    );

    // Mixed widths in one body.
    let mixed = hand_built(
        &[Ty::U8, Ty::U16],
        vec![Inst::Copy { ty: Ty::U8, operand: ValueId::new(0) }],
        ValueId::new(2),
    );
    assert_eq!(
        reflect_straight_line_function(&mixed),
        Err(R::MixedCarriers { first: "UInt8", then: "UInt16" })
    );

    // Instructions with no spelling here.
    let loadf = hand_built(
        &[Ty::U8],
        vec![Inst::Load { ty: Ty::U8, ptr: ValueId::new(0), volatile: false, align: None }],
        ValueId::new(1),
    );
    assert_eq!(reflect_straight_line_function(&loadf), Err(R::UnsupportedInst { inst: "Load" }));

    let cast = hand_built(
        &[Ty::U8],
        vec![Inst::Cast {
            op: trust_ir::CastOp::Trunc,
            src_ty: Ty::U16,
            dst_ty: Ty::U8,
            operand: ValueId::new(0),
        }],
        ValueId::new(1),
    );
    assert_eq!(reflect_straight_line_function(&cast), Err(R::UnsupportedInst { inst: "Cast" }));

    // Multiple blocks: straight-line only.
    let mut two = hand_built(&[Ty::U8], vec![], ValueId::new(0));
    two.blocks.push(Block::new(trust_ir::BlockId::new(1)));
    assert_eq!(reflect_straight_line_function(&two), Err(R::NotStraightLine { blocks: 2 }));

    // No `Return`.
    let mut no_ret = hand_built(&[Ty::U8], vec![], ValueId::new(0));
    no_ret.blocks[0].body.clear();
    assert!(matches!(
        reflect_straight_line_function(&no_ret),
        Err(R::MalformedTerminator { .. })
    ));

    // A dangling reference.
    let dangling = hand_built(&[Ty::U8], vec![], ValueId::new(9));
    assert_eq!(
        reflect_straight_line_function(&dangling),
        Err(R::UndefinedValue { value: ValueId::new(9) })
    );

    // A `Return` of no value at all.
    let mut unit = hand_built(&[Ty::U8], vec![], ValueId::new(0));
    unit.blocks[0].body = vec![trust_ir::InstrNode::new(Inst::Return { values: vec![] })];
    assert_eq!(
        reflect_straight_line_function(&unit),
        Err(R::UnsupportedReturnArity { values: 0 })
    );
}

/// A refusal must be a refusal, not a silent success — the `Copy` spelling is the
/// one place a "pure move" could quietly drop a carrier check, so it is pinned.
#[test]
fn copy_is_a_move_and_still_carries_its_type() {
    let f = hand_built(
        &[Ty::U8],
        vec![Inst::Copy { ty: Ty::U8, operand: ValueId::new(0) }],
        ValueId::new(1),
    );
    let e = reflect_straight_line_function(&f).expect("Copy reflects");
    // `fun (a : UInt8) => a`
    let expected = Expr::lam(BinderInfo::Default, konst("UInt8"), Expr::bvar(0));
    assert_eq!(format!("{e:?}"), format!("{expected:?}"));

    let bad = hand_built(
        &[Ty::U8],
        vec![Inst::Copy { ty: Ty::U16, operand: ValueId::new(0) }],
        ValueId::new(1),
    );
    assert_eq!(
        reflect_straight_line_function(&bad),
        Err(ReflectRefusal::MixedCarriers { first: "UInt8", then: "UInt16" })
    );
}

// ════════════════════════════════════════════════════════════════════════════
// MUTATION BATTERY — is the round trip LOAD-BEARING?
//
// Everything above this line is an agreement: emit, reflect, kernel says yes. A
// reflector that ignored its argument and returned the declaration would pass all
// of it. The only way to know an agreement is worth anything is to CORRUPT the
// emitted `trust_ir::Function` and watch the agreement break.
//
// Two disciplines make these tests mean something:
//
//   1. **Every trial asserts the PRISTINE body is accepted first.** A rejection of
//      a corrupted body proves nothing if the untouched body was rejected too —
//      that would be the reflector failing on the shape, not on the corruption.
//      `mutation_trial` refuses to report an outcome without passing that gate.
//   2. **Every trial asserts the corruption actually changed the IR.** A mutator
//      that silently found nothing to mutate would report a clean sweep.
//
// A refusal by the reflector counts as a catch: nothing reached the kernel, so
// nothing could be blessed. Only a kernel ACCEPTANCE of a corrupted body is a
// survivor, and a survivor is the finding — it means the round trip would sign off
// on a body that is not the one the declaration names.
//
// The honest bookkeeping: some corruptions do not change the FUNCTION the body
// denotes (`if a = b then a else b` with its arms swapped is still the same
// function; `a + b` with its operands swapped is still the same function). Those
// rows are marked `[denotation preserved]` and are NOT held to must-catch — a
// kernel acceptance there would not be a false verify. Only rows that genuinely
// change the denoted function are asserted.
// ════════════════════════════════════════════════════════════════════════════

/// Declarations the mutation battery needs that [`PROGRAM`] does not carry.
///
/// `lt_pick`/`le_pick` exist because widening `Ult -> Ule` is INVISIBLE on the
/// `min`/`max` shapes: `if a < b then a else b` and `if a <= b then a else b` both
/// denote `min`, so a kernel rejection there is definitional bookkeeping rather
/// than a caught defect. `lt_pick` returns a THIRD value on the false arm, so the
/// two comparisons disagree exactly at `a = b` and the widening is a real change of
/// function.
///
/// The rest (`k_eight`, `lit_add8`, `s8_flip`) are the declarations each mutant is
/// supposed to have BECOME, used by
/// [`each_mutant_denotes_exactly_the_declaration_it_was_corrupted_into`].
const MUTATION_EXTRAS: &[(&str, &str)] = &[
    ("lt_pick", "def lt_pick (a : UInt8) (b : UInt8) (c : UInt8) : UInt8 := if a < b then a else c"),
    ("le_pick", "def le_pick (a : UInt8) (b : UInt8) (c : UInt8) : UInt8 := if a <= b then a else c"),
    ("k_eight", "def k_eight : UInt8 := 8"),
    ("lit_add8", "def lit_add8 (a : UInt8) : UInt8 := a + 8"),
    ("s8_flip", "def s8_flip (a : UInt8) (b : UInt8) : UInt8 := b - a"),
];

/// [`PROGRAM`] plus [`MUTATION_EXTRAS`], elaborated and kernel-checked.
fn mutation_environment() -> Environment {
    let mut session = CleanIslandSession::new();
    for (name, src) in PROGRAM.iter().chain(MUTATION_EXTRAS.iter()) {
        let outcome = session.check(src);
        assert!(!outcome.is_rejected(), "island `{name}` was rejected: {:?}", outcome.errors);
    }
    session.environment().expect("a clean session has an environment").clone()
}

// ── mutators ───────────────────────────────────────────────────────────────
//
// Each targets the FIRST instruction MATCHING A STATED OPERATOR rather than the
// first instruction of its class, so which sub-expression gets corrupted does not
// depend on the order the emitter happens to lay instructions out.

/// Rewrite the first `BinOp` whose operator is `from` into `to`.
fn retarget_first_binop(func: &trust_ir::Function, from: BinOp, to: BinOp) -> trust_ir::Function {
    let mut f = func.clone();
    for node in &mut f.blocks[0].body {
        if let Inst::BinOp { op, .. } = &mut node.inst
            && *op == from
        {
            *op = to;
            return f;
        }
    }
    panic!("no `{}` BinOp to mutate", binop_name(from));
}

/// Swap the operands of the first `BinOp` whose operator is `which`.
fn swap_operands_of_first_binop(func: &trust_ir::Function, which: BinOp) -> trust_ir::Function {
    let mut f = func.clone();
    for node in &mut f.blocks[0].body {
        if let Inst::BinOp { op, lhs, rhs, .. } = &mut node.inst
            && *op == which
        {
            std::mem::swap(lhs, rhs);
            return f;
        }
    }
    panic!("no `{}` BinOp to mutate", binop_name(which));
}

/// Rewrite the first `ICmp` whose operator is `from` into `to`.
fn retarget_first_icmp(func: &trust_ir::Function, from: ICmpOp, to: ICmpOp) -> trust_ir::Function {
    let mut f = func.clone();
    for node in &mut f.blocks[0].body {
        if let Inst::ICmp { op, .. } = &mut node.inst
            && *op == from
        {
            *op = to;
            return f;
        }
    }
    panic!("no `{}` ICmp to mutate", icmp_name(from));
}

/// Move the first integer `Const` in the entry block by `by`.
fn shift_first_constant(func: &trust_ir::Function, by: i128) -> trust_ir::Function {
    let mut f = func.clone();
    for node in &mut f.blocks[0].body {
        if let Inst::Const { value, .. } = &mut node.inst {
            let cur = match value {
                Constant::Int(v) => *v,
                other => panic!("the first Const is not an integer: {}", constant_name(other)),
            };
            *value = Constant::Int(cur + by);
            return f;
        }
    }
    panic!("no Const to mutate");
}

// ── the trial ──────────────────────────────────────────────────────────────

/// What became of one corrupted body.
#[derive(Debug)]
enum MutationOutcome {
    /// The reflector declined the corrupted body by name. A catch: nothing reached
    /// the kernel, so nothing could be blessed.
    Refused(ReflectRefusal),
    /// The reflector produced a term and the CIC kernel refused to identify it with
    /// the pristine declaration. The catch this file is built to earn.
    KernelRejected,
    /// The reflector produced a term and the kernel ACCEPTED it against the pristine
    /// declaration. The corruption SURVIVED.
    Survived,
}

impl MutationOutcome {
    fn survived(&self) -> bool {
        matches!(self, MutationOutcome::Survived)
    }

    fn label(&self) -> String {
        match self {
            MutationOutcome::Refused(e) => format!("CAUGHT   (reflector refused: {e})"),
            MutationOutcome::KernelRejected => "CAUGHT   (kernel rejected)".to_owned(),
            MutationOutcome::Survived => "*** SURVIVED ***".to_owned(),
        }
    }
}

/// Corrupt one declaration's emitted body and report what the kernel made of it.
///
/// # Panics
///
/// Before any mutation, if the PRISTINE body is refused by the reflector or
/// rejected by the kernel — in that state the mutation below would prove nothing,
/// so reporting a "catch" would be a lie. Also if the mutation left the body
/// unchanged.
fn mutation_trial(
    env: &Environment,
    decl: &str,
    mutate: &dyn Fn(&trust_ir::Function) -> trust_ir::Function,
) -> MutationOutcome {
    let tc = TypeChecker::new(env);
    let declared = declared_value(env, decl);

    // ── the pristine gate — not optional ───────────────────────────────────
    let pristine = emitted(env, decl);
    let pristine_term = reflect_straight_line_function(&pristine).unwrap_or_else(|e| {
        panic!(
            "PRISTINE `{decl}` was REFUSED by the reflector ({e}) — \
             a rejection of the mutant would prove nothing"
        )
    });
    assert!(
        tc.is_def_eq(&pristine_term, &declared),
        "PRISTINE `{decl}` was REJECTED by the kernel — \
         a rejection of the mutant would prove nothing",
    );

    // ── the corruption ─────────────────────────────────────────────────────
    let mutated = mutate(&pristine);
    assert_ne!(
        format!("{:?}", mutated.blocks),
        format!("{:?}", pristine.blocks),
        "the mutation left `{decl}` byte-identical — it corrupts nothing",
    );

    match reflect_straight_line_function(&mutated) {
        Err(e) => MutationOutcome::Refused(e),
        Ok(term) if tc.is_def_eq(&term, &declared) => MutationOutcome::Survived,
        Ok(_) => MutationOutcome::KernelRejected,
    }
}

/// One row of a battery.
struct Trial<'a> {
    /// The declaration whose emitted body is corrupted.
    decl: &'a str,
    /// Human-readable statement of the corruption.
    what: &'a str,
    /// Does the corruption change the FUNCTION the body denotes?
    ///
    /// `false` rows are kept and reported but not held to must-catch: a kernel
    /// acceptance there would not be a false verify, because the mutant denotes the
    /// same function as the declaration. Marking them honestly is the difference
    /// between a mutation score and a mutation theatre.
    changes_the_function: bool,
    mutate: Box<dyn Fn(&trust_ir::Function) -> trust_ir::Function>,
}

fn trial<'a>(
    decl: &'a str,
    what: &'a str,
    changes_the_function: bool,
    mutate: impl Fn(&trust_ir::Function) -> trust_ir::Function + 'static,
) -> Trial<'a> {
    Trial { decl, what, changes_the_function, mutate: Box::new(mutate) }
}

/// Run every row, print the score, and fail on any survivor that changed the
/// denoted function.
fn run_battery(title: &str, trials: Vec<Trial<'_>>) {
    let env = mutation_environment();
    let mut survivors: Vec<String> = Vec::new();
    let mut caught = 0usize;
    println!("\n── mutation battery: {title} ──");
    for t in &trials {
        let outcome = mutation_trial(&env, t.decl, t.mutate.as_ref());
        println!(
            "  {:<10} {:<50} {}{}",
            t.decl,
            t.what,
            outcome.label(),
            if t.changes_the_function { "" } else { "   [denotation preserved]" },
        );
        if outcome.survived() {
            if t.changes_the_function {
                survivors.push(format!("`{}`  {}", t.decl, t.what));
            }
        } else {
            caught += 1;
        }
    }
    println!("  -> {caught}/{} caught", trials.len());
    assert!(
        survivors.is_empty(),
        "MUTATION SURVIVED — the round trip is VACUOUS for these shapes: the kernel \
         accepted a corrupted body against the pristine declaration, so an agreement \
         on these shapes is not evidence the emitted body is the declared one:\n  {}",
        survivors.join("\n  "),
    );
}

// ── the five required mutation classes ─────────────────────────────────────

/// **Mutation 1 — swap the two arms of a `Select`.**
///
/// `min` becomes `max`. If this survived, an emitter that put the arms in the wrong
/// order would round-trip clean.
#[test]
fn mutation_select_arms_swapped() {
    let swap = || |f: &trust_ir::Function| swap_select_arms(f);
    run_battery(
        "Select: swap the two arms",
        vec![
            trial("min8", "if a<b then a else b -> then b else a", true, swap()),
            trial("min16", "if a<b then a else b -> then b else a", true, swap()),
            trial("min32", "if a<b then a else b -> then b else a", true, swap()),
            trial("min64", "if a<b then a else b -> then b else a", true, swap()),
            trial("max8", "if a<b then b else a -> then a else b", true, swap()),
            trial("le8", "if a<=b then a else b -> then b else a", true, swap()),
            trial("lt_pick", "if a<b then a else c -> then c else a", true, swap()),
            // `a` and `b` are equal on the true arm, so swapping is a no-op on the
            // denotation. Reported, not required.
            trial("eq8", "if a=b then a else b -> then b else a", false, swap()),
            trial("eq32", "if a=b then a else b -> then b else a", false, swap()),
        ],
    );
}

/// **Mutation 2 — `BinOp::Add` becomes `BinOp::Sub`.**
///
/// The single most basic thing a reflector must be sensitive to: which operator the
/// IR names.
#[test]
fn mutation_add_becomes_sub() {
    let f = || |f: &trust_ir::Function| retarget_first_binop(f, BinOp::Add, BinOp::Sub);
    run_battery(
        "BinOp: Add -> Sub",
        vec![
            trial("a8", "a + b -> a - b", true, f()),
            trial("a16", "a + b -> a - b", true, f()),
            trial("a32", "a + b -> a - b", true, f()),
            trial("a64", "a + b -> a - b", true, f()),
            trial("lit_add", "a + 7 -> a - 7", true, f()),
            trial("nest_mul_add", "(a + b) * c -> (a - b) * c", true, f()),
            trial("nest_deep", "(a*b) - (a + c) -> (a*b) - (a - c)", true, f()),
        ],
    );
}

/// **Mutation 3 — swap the operands of a non-commutative `Sub`.**
///
/// Operand ORDER is the thing a battery of commutative shapes cannot see at all.
/// The `[denotation preserved]` rows at the bottom are the commutative controls:
/// they record that this reflector is stricter than semantics there, because
/// commutativity of `UIntN.add` is a propositional theorem and not a definitional
/// equality — the kernel rejects `b + a` against `a + b` under open binders.
#[test]
fn mutation_sub_operands_swapped() {
    let sub = || |f: &trust_ir::Function| swap_operands_of_first_binop(f, BinOp::Sub);
    let add = || |f: &trust_ir::Function| swap_operands_of_first_binop(f, BinOp::Add);
    let mul = || |f: &trust_ir::Function| swap_operands_of_first_binop(f, BinOp::Mul);
    run_battery(
        "BinOp: swap lhs/rhs of a non-commutative Sub",
        vec![
            trial("s8", "a - b -> b - a", true, sub()),
            trial("s16", "a - b -> b - a", true, sub()),
            trial("s32", "a - b -> b - a", true, sub()),
            trial("s64", "a - b -> b - a", true, sub()),
            trial("lit_sub", "a - 1 -> 1 - a", true, sub()),
            trial("nest_sub_sub", "(a - b) - c -> (b - a) - c", true, sub()),
            trial("nest_deep", "(a*b) - (a+c) -> (a+c) - (a*b)", true, sub()),
            // Commutative controls: the mutant denotes the same function.
            trial("a8", "a + b -> b + a", false, add()),
            trial("m8", "a * b -> b * a", false, mul()),
        ],
    );
}

/// **Mutation 4 — move an integer `Constant` by one.**
///
/// An off-by-one in a literal is the corruption most likely to slip through a
/// structural comparison, because the SHAPE of the body is untouched.
#[test]
fn mutation_constant_shifted_by_one() {
    let up = || |f: &trust_ir::Function| shift_first_constant(f, 1);
    let down = || |f: &trust_ir::Function| shift_first_constant(f, -1);
    run_battery(
        "Const: shift the integer by 1",
        vec![
            trial("k_zero", "0 -> 1", true, up()),
            trial("k_seven", "7 -> 8", true, up()),
            trial("k_seven", "7 -> 6", true, down()),
            trial("k_max8", "255 -> 254", true, down()),
            // 256 leaves the carrier: expected to be REFUSED rather than
            // kernel-rejected, which is also a catch.
            trial("k_max8", "255 -> 256 (out of UInt8)", true, up()),
            trial("k_big64", "1000000 -> 1000001", true, up()),
            trial("lit_add", "a + 7 -> a + 8", true, up()),
            trial("lit_sub", "a - 1 -> a - 2", true, up()),
            trial("lit_mul64", "a * 1000000 -> a * 1000001", true, up()),
        ],
    );
}

/// **Mutation 5 — widen `ICmpOp::Ult` to `ICmpOp::Ule`.**
///
/// A boundary-only corruption: the two comparisons disagree on exactly one input
/// pair, `a = b`. On `min`/`max` shapes that disagreement is invisible in the
/// DENOTATION (both spellings still compute `min`), which is why `lt_pick` — whose
/// false arm returns a third parameter — carries the must-catch weight here.
#[test]
fn mutation_ult_widened_to_ule() {
    let widen = || |f: &trust_ir::Function| retarget_first_icmp(f, ICmpOp::Ult, ICmpOp::Ule);
    run_battery(
        "ICmp: Ult -> Ule",
        vec![
            trial("lt_pick", "if a<b then a else c -> if a<=b ...", true, widen()),
            // Both spellings still denote `min`; reported, not required.
            trial("min8", "if a<b then a else b -> if a<=b ...", false, widen()),
            trial("min32", "if a<b then a else b -> if a<=b ...", false, widen()),
            trial("min64", "if a<b then a else b -> if a<=b ...", false, widen()),
        ],
    );
}

/// The strongest form of the non-vacuity claim: a mutant is not merely rejected, it
/// is ACCEPTED against the declaration it was corrupted INTO.
///
/// A reflector that returned garbage on any perturbation would pass every battery
/// above while proving nothing — "rejected" is cheap. This test shows the reflection
/// tracks the corrupted IR faithfully and lands exactly on the other function, so
/// the kernel's rejection of the original is a real discrimination between two
/// well-formed bodies rather than a reaction to nonsense.
#[test]
fn each_mutant_denotes_exactly_the_declaration_it_was_corrupted_into() {
    let env = mutation_environment();
    let tc = TypeChecker::new(&env);

    #[allow(clippy::type_complexity)]
    let cases: Vec<(&str, Box<dyn Fn(&trust_ir::Function) -> trust_ir::Function>, &str)> = vec![
        ("a8", Box::new(|f| retarget_first_binop(f, BinOp::Add, BinOp::Sub)), "s8"),
        ("s8", Box::new(|f| retarget_first_binop(f, BinOp::Sub, BinOp::Add)), "a8"),
        ("s8", Box::new(|f| swap_operands_of_first_binop(f, BinOp::Sub)), "s8_flip"),
        ("min8", Box::new(swap_select_arms), "max8"),
        ("max8", Box::new(swap_select_arms), "min8"),
        ("lt_pick", Box::new(|f| retarget_first_icmp(f, ICmpOp::Ult, ICmpOp::Ule)), "le_pick"),
        ("k_seven", Box::new(|f| shift_first_constant(f, 1)), "k_eight"),
        ("lit_add", Box::new(|f| shift_first_constant(f, 1)), "lit_add8"),
    ];

    for (from, mutate, into) in cases {
        // The pristine gate, again: the mutation means nothing without it.
        let pristine = emitted(&env, from);
        let pristine_term = reflect_straight_line_function(&pristine)
            .unwrap_or_else(|e| panic!("PRISTINE `{from}` was refused: {e}"));
        assert!(
            tc.is_def_eq(&pristine_term, &declared_value(&env, from)),
            "PRISTINE `{from}` was rejected by the kernel",
        );

        let mutant = reflect_straight_line_function(&mutate(&pristine))
            .unwrap_or_else(|e| panic!("the `{from}` mutant did not reflect: {e}"));
        assert!(
            !tc.is_def_eq(&mutant, &declared_value(&env, from)),
            "the `{from}` mutant was still accepted against `{from}` — mutation SURVIVED",
        );
        assert!(
            tc.is_def_eq(&mutant, &declared_value(&env, into)),
            "the `{from}` mutant should denote `{into}`, and the kernel says it does not — \
             the reflection is not tracking the corrupted IR",
        );
        println!("  `{from}` mutant denotes `{into}`, and no longer `{from}`");
    }
}

/// Insert a `Copy` whose result nobody reads, immediately before the `Return`.
///
/// This changes the IR and does NOT change the denotation, so it is the one
/// corruption whose correct outcome is `Survived`.
fn insert_dead_copy(func: &trust_ir::Function) -> trust_ir::Function {
    let mut f = func.clone();
    let block = &mut f.blocks[0];
    let (source, ty) = block.params[0].clone();
    // A `ValueId` far outside anything the emitter allocates, so it collides with
    // nothing and is read by nothing.
    let node = trust_ir::InstrNode::new(Inst::Copy { ty, operand: source })
        .with_result(ValueId::new(9_999));
    let before_the_return = block.body.len() - 1;
    block.body.insert(before_the_return, node);
    f
}

/// **The meta-test.** A clean mutation sweep is worthless if `Survived` is a state
/// the harness can never reach — a `mutation_trial` that returned `KernelRejected`
/// unconditionally would produce every green above.
///
/// So: mutate a body in a way that genuinely does NOT change what it denotes, and
/// require the harness to say so. A dead `Copy` is exactly that — the reflector
/// binds its result and nothing ever reads it, so the term under the binders is
/// unchanged and the kernel accepts. If this test ever starts failing with
/// "CAUGHT", the batteries above stopped being evidence.
///
/// It doubles as a recorded limit: **the round trip cannot see a dead instruction.**
/// That is not a soundness hole — a dead `Copy` denotes nothing, and every dead
/// instruction whose semantics could matter (`Store`, `Call`, …) is refused by name
/// — but it does mean an emitter could add unread instructions and this file would
/// not notice.
#[test]
fn the_mutation_harness_can_actually_report_a_survivor() {
    let env = mutation_environment();
    let outcome = mutation_trial(&env, "min8", &insert_dead_copy);
    assert!(
        outcome.survived(),
        "a dead `Copy` does not change the denotation, so the harness must report it as \
         SURVIVED; it said {outcome:?}. If the harness cannot reach `Survived`, every \
         clean sweep in this file is vacuous.",
    );
    println!("harness self-test: `Survived` is reachable (dead `Copy` in `min8`)");
}
