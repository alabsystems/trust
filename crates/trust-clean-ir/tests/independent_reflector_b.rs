// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// ============================================================================
// AN INDEPENDENT TrustIR -> Clean REFLECTOR (author B)
// ============================================================================
//
// WHY THIS FILE EXISTS. `trust-clean-ir` turns a sealed `CleanOriginPlan` into
// a `trust_ir::Function`. If the reflector that checks that emission is written
// by someone who knows how the emitter thinks, the round trip can CANCEL: a
// reflector that inverts the emitter's own mistake makes a wrong body come back
// looking right, and the kernel then blesses it. This reflector was therefore
// written WITHOUT reading `trust-clean-ir/src/**`, without reading the existing
// `tests/symbolic_reflection.rs`, and without reading
// `trust-clean-origin/src/reflect.rs`.
//
// WHAT IT IS. `reflect_uint_straight_line` implements a DENOTATIONAL SEMANTICS
// OF TrustIR, taken from the IR's own specification
// (`first-party/trust-ir/crates/trust-ir/src/{inst,ty,constant,interpret}.rs`),
// as Clean CIC terms. Its ONLY input is a `&trust_ir::Function`. It never sees
// the kernel `Environment`, never sees the `CleanOriginPlan`, never sees the
// declaration it will be compared against, and never sees a name other than the
// ones it mints itself from the IR's types and opcodes. A reflector that could
// return "the declaration, verbatim" is structurally impossible here, because
// the declaration is not in scope.
//
// THE SPELLING, AND WHY IT IS THE TYPECLASS-MEDIATED ONE. Working top-down from
// what the kernel must accept: Clean elaborates `a + b` at `UInt8` to
//
//     @HAdd.hAdd.{0,0,0} UInt8 UInt8 UInt8 instHAddUInt8 a b
//
// so that is what a TrustIR `BinOp { op: Add, ty: U8 }` is reflected to. This is
// a deliberate choice over the equally-def_eq `UInt8.add a b`: the heterogeneous
// form is the spelling the SURFACE LANGUAGE means, so the obligation the kernel
// discharges is "the IR computes what the Clean source says", not "the IR
// computes what one particular unfolding of the Clean source says". `is_def_eq`
// would accept either; the typeclass form needs no unfolding argument at all.
// It is uniform in the width (`instHAddUInt{8,16,32,64}`), so nothing about the
// mapping is special-cased per width.
//
// THE THREE SEMANTIC FACTS THE MAPPING RESTS ON, each MEASURED here rather than
// assumed (see `carrier_semantics_are_anchored`, and the differential leg
// described below):
//
//   1. TrustIR `BinOp::{Add,Sub,Mul}` on an unsigned `Ty` is WRAPPING modular
//      arithmetic — `interpret.rs` evaluates them as `wrapping_{add,sub,mul}`
//      on the raw payload masked to the type's bit width. Clean's `UInt8` (etc.)
//      arithmetic is `Fin (2^n)` arithmetic, also modular. The dangerous case is
//      Sub, because a `Nat`-style truncated subtraction would agree with
//      wrapping on every input EXCEPT underflow: `carrier_semantics_are_anchored`
//      pins `(0 : UInt8) - 1 = 255` AT THE KERNEL, so the agreement is a
//      measurement, not a hope.
//   2. TrustIR `ICmpOp::Ult` is unsigned less-than, and Clean's `instLTUInt{N}`
//      orders `UIntN` by its underlying `Nat`, i.e. unsigned. Pinned at the
//      kernel for the wrap-sensitive pair `200 < 100 = false`, which a SIGNED
//      reading would decide the other way.
//   3. TrustIR `Select` is a non-short-circuiting choice on a `Bool` condition.
//      Clean's `ite` chooses on a `Decidable` proposition. These agree exactly
//      when the IR `Bool` is the decision of that proposition — which is why
//      this reflector only accepts a `Select` whose condition is an `ICmp`
//      IN THE SAME BLOCK. A `Select` on any other Bool is REFUSED BY NAME: the
//      reflector does not know which proposition that Bool decides, and
//      inventing one would be exactly the kind of "helpful" guess that turns a
//      kernel PASS into a false verdict.
//
// THE THREE LEGS OF THE TEST.
//
//   A. KERNEL AGREEMENT (the assignment): for each covered shape, drive real
//      Clean source through a real island session, plan it, emit TrustIR with
//      `trust_clean_ir::emit_clean_origin_function`, reflect the RESULT with
//      this file's reflector, and require
//      `TypeChecker::is_def_eq(reflected, env.get_const(name).value)`.
//
//   B. DIFFERENTIAL ANCHOR (independence): leg A can only ever say "my spelling
//      and the declaration's spelling agree". It CANNOT catch a mapping that is
//      wrong in the same direction on both sides — if TrustIR `Sub` did not
//      mean Clean's `-`, leg A would still pass, because the reflector would
//      simply have written down the declaration's own operator. So every
//      covered function is ALSO executed on concrete inputs by TrustIR's own
//      reference `Interpreter`, and the reflected term is applied to the same
//      inputs and kernel-compared against the interpreter's answer. That leg
//      compares MY term against the IR's OPERATIONAL semantics, with the
//      declaration nowhere in the loop.
//
//      The two legs are complementary IN BOTH DIRECTIONS, measured by mutation:
//      swapping `Ule` to `Ult`, or swapping the operands of `Eq`, is invisible
//      to leg B — `min` at `a = b` returns the same value under `<` and `<=`,
//      and `a = b` is symmetric — and only leg A catches those. Mapping `Add`
//      to `Sub`, or `And` to `Or`, is caught by both. Keep both.
//
//   C. NON-VACUITY: reflections of the WRONG body must be REJECTED — `a - b`
//      against a declaration of `a + b`, swapped operands, a swapped `ite`
//      pair, and a wrong literal. Without leg C a reflector that returned a
//      constant would score 100%.
//
//   D. MUTATION (part 3, added after A-C were green): leg C hand-builds wrong
//      TERMS. That shows the KERNEL COMPARISON discriminates, but it never puts
//      a wrong `trust_ir::Function` through the real pipeline, so it cannot
//      answer the question the whole file exists for: **if the emitter were
//      wrong, would this check say so?** Leg D takes the function the emitter
//      actually produced, corrupts it at ONE instruction, and requires the
//      check to fail — either by refusal or by kernel rejection. A mutant that
//      survives is a hole in the check and is reported as such.

use std::collections::BTreeMap;

use clean_kernel::{BinderInfo, Environment, Expr, Level, LevelVec, Name, TypeChecker};
use trust_certify::clean_island::CleanIslandSession;
use trust_ir::interpret::{InterpretValue, Interpreter};
use trust_ir::value::{FuncId, FuncTyId, ValueId};
use trust_ir::{BinOp, Constant, Function, ICmpOp, Inst, Ty};

// ===========================================================================
// PART 1 — the reflector
// ===========================================================================

/// Why a `trust_ir::Function` could not be honestly reflected.
///
/// Every variant names the construct it declined, because "unsupported" with no
/// next step is a defect (DESIGN_PHILOSOPHY principle 10 / spec-surface v7/D3),
/// and because a refusal is the only correct answer when the alternative is a
/// guess the kernel would then rubber-stamp.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReflectRefusal {
    /// The function has no body, or more than one block: this reflector covers
    /// exactly the straight-line single-block fragment.
    NotSingleBlock { blocks: usize },
    /// The single block is not the declared entry block.
    BlockIsNotEntry,
    /// A block parameter, an instruction, or the result carries a type outside
    /// the unsigned machine carriers `U8`/`U16`/`U32`/`U64`.
    UnsupportedCarrier { ty: String, position: &'static str },
    /// An instruction this reflector has no denotation for. `inst` is the
    /// TrustIR variant name; nothing is invented for it.
    UnsupportedInst { inst: &'static str },
    /// A `BinOp` opcode this reflector has no denotation for.
    UnsupportedBinOp { op: String },
    /// An `ICmp` opcode this reflector has no denotation for.
    UnsupportedICmp { op: String },
    /// A `Select` whose condition is not an `ICmp` produced in the same block.
    /// The reflector cannot name the proposition that `Bool` decides.
    SelectConditionIsNotAComparison { cond: usize },
    /// A comparison result used somewhere other than a `Select` condition
    /// (e.g. returned, or fed to arithmetic). The `Prop`/`Decidable` pair a
    /// comparison denotes is not a `UIntN` value.
    ComparisonUsedAsValue { value: usize },
    /// An operand with no denotation in scope (not a block parameter and not a
    /// previously-defined result).
    UndefinedOperand { value: usize },
    /// An instruction produced a number of results this reflector does not
    /// model.
    UnexpectedResultArity { inst: &'static str, results: usize },
    /// The block does not end in `Return` with exactly one value.
    NotSingleValueReturn,
    /// A `Const` payload outside the carrier's range, or in a shape (bytes,
    /// float, aggregate, …) with no `UIntN` denotation.
    UnsupportedConstant { detail: String },
    /// A `ValueId` was defined twice. TrustIR is SSA; a redefinition means the
    /// input is not the artifact this reflector reasons about.
    DuplicateDefinition { value: usize },
    /// An instruction appeared after the terminator.
    InstructionAfterTerminator { inst: &'static str },
    // There was an `OrderComparisonAgainstNumeral` refusal here, for an order
    // comparison with a numeral operand. It existed only because Clean elaborated
    // `a < 10` to a `Nat`-reduced `Decidable` instance the kernel did not equate
    // with the uniform `instDecidableUInt8Lt a (UInt8.ofNat 10)`. Clean
    // `c91fa93f5` made the two kernel-equal, so it was deleted — see
    // `order_comparison_against_a_numeral_is_no_longer_a_limit`, which fails first,
    // naming the refusal to restore, if a Clean pin ever separates them again.
}

/// What a TrustIR SSA value denotes.
///
/// Two sorts, deliberately kept apart. Comparisons do NOT denote a `Bool` term
/// here: they denote the PROPOSITION they decide together with the `Decidable`
/// instance that decides it, which is the only form `ite` can consume. Keeping
/// them in a separate variant is what makes "a comparison used as a number" a
/// refusal instead of a silently wrong coercion.
#[derive(Debug, Clone)]
enum Den {
    /// A `UIntN`-valued Clean term.
    Value { width: u32, expr: Expr },
    /// A comparison: the `Prop` it decides, plus the `Decidable` instance.
    Cmp { prop: Expr, decidable: Expr },
}

/// A `UIntN` operand: its term.
struct Operand {
    expr: Expr,
}

/// The unsigned machine carriers this reflector can spell, and their widths.
///
/// `U128` is absent because the Clean prelude has no `UInt128`; `Usize`/`Isize`
/// are absent because their width is target-dependent and a reflection may not
/// depend on a fact the IR does not carry. Both are refusals, by name.
fn uint_width(ty: &Ty) -> Option<u32> {
    match ty {
        Ty::U8 => Some(8),
        Ty::U16 => Some(16),
        Ty::U32 => Some(32),
        Ty::U64 => Some(64),
        _ => None,
    }
}

fn carrier(width: u32) -> Expr {
    Expr::const_str(&format!("UInt{width}"))
}

fn levels(ls: Vec<Level>) -> LevelVec {
    LevelVec::from_vec(ls)
}

/// `@UIntN.ofNat n` — the elaboration of a numeral at a `UIntN`.
fn uint_lit(width: u32, n: u64) -> Expr {
    Expr::app(Expr::const_str(&format!("UInt{width}.ofNat")), Expr::nat_lit(n))
}

/// `@H<Op>.h<op>.{0,0,0} UIntN UIntN UIntN instH<Op>UIntN lhs rhs`.
///
/// The heterogeneous typeclass spelling, at the homogeneous instantiation the
/// surface `a + b` elaborates to.
fn hetero_binop(class: &str, method: &str, inst: &str, width: u32, lhs: Expr, rhs: Expr) -> Expr {
    let head = Expr::const_(
        Name::from_string(&format!("{class}.{method}")),
        levels(vec![Level::zero(), Level::zero(), Level::zero()]),
    );
    Expr::apps(
        head,
        [
            carrier(width),
            carrier(width),
            carrier(width),
            Expr::const_str(&format!("{inst}UInt{width}")),
            lhs,
            rhs,
        ],
    )
}

/// `@LT.lt.{0} UIntN instLTUIntN lhs rhs` — the PROPOSITION `lhs < rhs`.
fn lt_prop(width: u32, lhs: Expr, rhs: Expr) -> Expr {
    order_prop("LT.lt", "instLTUInt", width, lhs, rhs)
}

/// `instDecidableUIntNLt lhs rhs` — the instance deciding `lhs < rhs`.
fn lt_decidable(width: u32, lhs: Expr, rhs: Expr) -> Expr {
    decidable_inst(&format!("instDecidableUInt{width}Lt"), lhs, rhs)
}

/// `@<Class>.{0} UIntN inst<Class>UIntN lhs rhs` — an ORDER proposition
/// (`LT.lt` / `LE.le`). Level `0` because the class is indexed by the carrier,
/// which lives in `Type 0`.
fn order_prop(head: &str, inst_prefix: &str, width: u32, lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string(head), levels(vec![Level::zero()])),
        [carrier(width), Expr::const_str(&format!("{inst_prefix}{width}")), lhs, rhs],
    )
}

/// `@Eq.{1} UIntN lhs rhs` — propositional equality at the carrier. Unlike the
/// order relations this takes NO instance argument, and its level is `1`
/// (`Eq : {α : Sort u} → α → α → Prop`, with `UIntN : Type 0 = Sort 1`).
fn eq_prop(width: u32, lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), levels(vec![Level::succ(Level::zero())])),
        [carrier(width), lhs, rhs],
    )
}

/// `<inst> lhs rhs` — a `Decidable` instance applied to the two operands.
fn decidable_inst(name: &str, lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(Expr::const_str(name), [lhs, rhs])
}

/// `@ite.{1} UIntN prop dec then else`.
///
/// Level `1` because the result lives in `Type 0 = Sort 1`.
fn ite(width: u32, prop: Expr, dec: Expr, then_: Expr, else_: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("ite"), levels(vec![Level::succ(Level::zero())])),
        [carrier(width), prop, dec, then_, else_],
    )
}

/// Reflect a single-block, straight-line `trust_ir::Function` over the unsigned
/// machine carriers into the Clean term denoting the same mathematical function.
///
/// The result is a closed lambda with one binder per entry-block parameter, in
/// declaration order, de Bruijn indexed (parameter `i` of `n` is `BVar(n-1-i)`).
///
/// # Errors
///
/// Every shape outside the covered fragment is refused BY NAME — see
/// [`ReflectRefusal`]. Nothing is approximated: a refusal costs a failed check,
/// while a guess the kernel accepts costs a wrong binary.
pub fn reflect_uint_straight_line(func: &Function) -> Result<Expr, ReflectRefusal> {
    if func.blocks.len() != 1 {
        return Err(ReflectRefusal::NotSingleBlock { blocks: func.blocks.len() });
    }
    let block = &func.blocks[0];
    if block.id != func.entry {
        return Err(ReflectRefusal::BlockIsNotEntry);
    }

    // ---- binders -------------------------------------------------------
    // One binder per block parameter, in order. The whole body sits under all
    // of them and this fragment introduces no further binders, so a parameter's
    // de Bruijn index is CONSTANT throughout the body: parameter `i` of `n` is
    // `BVar(n - 1 - i)`.
    let arity = block.params.len();
    let mut env: BTreeMap<ValueId, Den> = BTreeMap::new();
    let mut binder_tys: Vec<u32> = Vec::with_capacity(arity);
    for (i, (value, ty)) in block.params.iter().enumerate() {
        let width = uint_width(ty).ok_or_else(|| ReflectRefusal::UnsupportedCarrier {
            ty: format!("{ty:?}"),
            position: "block parameter",
        })?;
        binder_tys.push(width);
        let idx = u32::try_from(arity - 1 - i).expect("arity fits in u32");
        if env.insert(*value, Den::Value { width, expr: Expr::bvar(idx) }).is_some() {
            return Err(ReflectRefusal::DuplicateDefinition { value: value.as_usize() });
        }
    }

    // ---- body ----------------------------------------------------------
    let mut body: Option<Expr> = None;
    for node in &block.body {
        if body.is_some() {
            return Err(ReflectRefusal::InstructionAfterTerminator { inst: inst_name(&node.inst) });
        }
        match &node.inst {
            Inst::Const { ty, value } => {
                let width = uint_width(ty).ok_or_else(|| ReflectRefusal::UnsupportedCarrier {
                    ty: format!("{ty:?}"),
                    position: "const",
                })?;
                let n = constant_as_uint(value, width)?;
                define(&mut env, node, "Const", Den::Value { width, expr: uint_lit(width, n) })?;
            }

            Inst::Copy { ty, operand } => {
                // Identity. Honest, and free: the denotation of a copy is the
                // denotation of its operand.
                let width = uint_width(ty).ok_or_else(|| ReflectRefusal::UnsupportedCarrier {
                    ty: format!("{ty:?}"),
                    position: "copy",
                })?;
                let den = value_den(&env, *operand, width)?;
                define(&mut env, node, "Copy", Den::Value { width, expr: den.expr })?;
            }

            Inst::BinOp { op, ty, lhs, rhs } => {
                let width = uint_width(ty).ok_or_else(|| ReflectRefusal::UnsupportedCarrier {
                    ty: format!("{ty:?}"),
                    position: "binop",
                })?;
                // The three modular ring operations plus the two bitwise
                // lattice operations. `interpret.rs` evaluates these five as
                // `wrapping_{add,sub,mul}` and `&`/`|` on the raw payload
                // masked to the width; Clean's `UIntN` counterparts are the
                // `Fin (2^n)` / `BitVec` operations of the same name.
                //
                // `UDiv`/`URem` are refused DELIBERATELY, and not for want of
                // effort: Clean's `UIntN.div`/`.mod` are TOTAL — the kernel
                // reduces `x / 0` to `0` — where TrustIR's are UB at a zero
                // divisor. A reflection would therefore be right on every input
                // except the one a proof exists to rule out. `Xor` and the
                // shifts are refused for want of a MEASURED Clean counterpart:
                // this reflector spells only what it has seen the prelude
                // elaborate, never what it expects the prelude to contain.
                // (The prelude has elaborated `^^^`/`<<<`/`>>>` at `UIntN`
                // since Clean `bf31976f48`; this file has not measured them,
                // and `trust-clean-ir` emits none of them to reflect.)
                let (class, method, inst) = match op {
                    BinOp::Add => ("HAdd", "hAdd", "instHAdd"),
                    BinOp::Sub => ("HSub", "hSub", "instHSub"),
                    BinOp::Mul => ("HMul", "hMul", "instHMul"),
                    BinOp::And => ("HAnd", "hAnd", "instHAnd"),
                    BinOp::Or => ("HOr", "hOr", "instHOr"),
                    other => {
                        return Err(ReflectRefusal::UnsupportedBinOp { op: format!("{other:?}") });
                    }
                };
                let l = value_den(&env, *lhs, width)?;
                let r = value_den(&env, *rhs, width)?;
                define(
                    &mut env,
                    node,
                    "BinOp",
                    Den::Value {
                        width,
                        expr: hetero_binop(class, method, inst, width, l.expr, r.expr),
                    },
                )?;
            }

            Inst::ICmp { op, ty, lhs, rhs } => {
                let width = uint_width(ty).ok_or_else(|| ReflectRefusal::UnsupportedCarrier {
                    ty: format!("{ty:?}"),
                    position: "icmp",
                })?;
                let l = value_den(&env, *lhs, width)?;
                let r = value_den(&env, *rhs, width)?;
                // The three UNSIGNED relations whose Clean counterpart has been
                // measured. The SIGNED opcodes are refused because they read
                // the same bits under a different order and there is no signed
                // Clean carrier in play; `Ne`/`Ugt`/`Uge` are refused because
                // spelling them would mean inventing a negation or an argument
                // swap that the elaborated declaration never writes — a
                // rearrangement is exactly the sort of "obviously equivalent"
                // step that turns a reflector into a second, unreviewed
                // compiler.
                // A numeral operand takes the SAME uniform instance as any other
                // operand, at every relation. The ORDER relations used to refuse
                // one (`OrderComparisonAgainstNumeral`), because Clean elaborated
                // `a < 10` through a `Nat`-reduced instance the kernel did not
                // equate with the uniform one; Clean `c91fa93f5` made the two
                // kernel-equal, and
                // `order_comparison_against_a_numeral_is_no_longer_a_limit`
                // measures it. Equality never needed the refusal: `a = 10`
                // elaborates through the same `instDecidableEqUIntN` as `a = b`.
                let (prop, decidable) = match op {
                    ICmpOp::Ult => (
                        lt_prop(width, l.expr.clone(), r.expr.clone()),
                        lt_decidable(width, l.expr, r.expr),
                    ),
                    ICmpOp::Ule => (
                        order_prop("LE.le", "instLEUInt", width, l.expr.clone(), r.expr.clone()),
                        decidable_inst(&format!("instDecidableUInt{width}Le"), l.expr, r.expr),
                    ),
                    ICmpOp::Eq => (
                        eq_prop(width, l.expr.clone(), r.expr.clone()),
                        decidable_inst(&format!("instDecidableEqUInt{width}"), l.expr, r.expr),
                    ),
                    other => {
                        return Err(ReflectRefusal::UnsupportedICmp { op: format!("{other:?}") });
                    }
                };
                define(&mut env, node, "ICmp", Den::Cmp { prop, decidable })?;
            }

            Inst::Select { ty, cond, then_val, else_val } => {
                let width = uint_width(ty).ok_or_else(|| ReflectRefusal::UnsupportedCarrier {
                    ty: format!("{ty:?}"),
                    position: "select",
                })?;
                let Some(Den::Cmp { prop, decidable }) = env.get(cond) else {
                    return Err(ReflectRefusal::SelectConditionIsNotAComparison {
                        cond: cond.as_usize(),
                    });
                };
                let (prop, decidable) = (prop.clone(), decidable.clone());
                let t = value_den(&env, *then_val, width)?;
                let e = value_den(&env, *else_val, width)?;
                define(
                    &mut env,
                    node,
                    "Select",
                    Den::Value { width, expr: ite(width, prop, decidable, t.expr, e.expr) },
                )?;
            }

            Inst::Return { values } => {
                let [only] = values.as_slice() else {
                    return Err(ReflectRefusal::NotSingleValueReturn);
                };
                let width = match env.get(only) {
                    Some(Den::Value { width, .. }) => *width,
                    Some(Den::Cmp { .. }) => {
                        return Err(ReflectRefusal::ComparisonUsedAsValue {
                            value: only.as_usize(),
                        });
                    }
                    None => {
                        return Err(ReflectRefusal::UndefinedOperand { value: only.as_usize() });
                    }
                };
                body = Some(value_den(&env, *only, width)?.expr);
            }

            other => {
                return Err(ReflectRefusal::UnsupportedInst { inst: inst_name(other) });
            }
        }
    }

    let Some(mut term) = body else {
        return Err(ReflectRefusal::NotSingleValueReturn);
    };

    // ---- close under the binders, innermost-last ------------------------
    for width in binder_tys.iter().rev() {
        term = Expr::lam(BinderInfo::Default, carrier(*width), term);
    }
    Ok(term)
}

/// Record a node's single result, refusing a redefinition or an arity this
/// reflector does not model.
fn define(
    env: &mut BTreeMap<ValueId, Den>,
    node: &trust_ir::InstrNode,
    inst: &'static str,
    den: Den,
) -> Result<(), ReflectRefusal> {
    let [result] = node.results.as_slice() else {
        return Err(ReflectRefusal::UnexpectedResultArity { inst, results: node.results.len() });
    };
    if env.insert(*result, den).is_some() {
        return Err(ReflectRefusal::DuplicateDefinition { value: result.as_usize() });
    }
    Ok(())
}

/// The `UIntN` denotation of an operand, refusing a comparison used as a value,
/// an unknown value, and a width mismatch between the operand and its use.
fn value_den(
    env: &BTreeMap<ValueId, Den>,
    value: ValueId,
    expect_width: u32,
) -> Result<Operand, ReflectRefusal> {
    match env.get(&value) {
        Some(Den::Value { width, expr }) if *width == expect_width => {
            Ok(Operand { expr: expr.clone() })
        }
        Some(Den::Value { width, .. }) => Err(ReflectRefusal::UnsupportedCarrier {
            ty: format!("UInt{width} used where UInt{expect_width} was expected"),
            position: "operand",
        }),
        Some(Den::Cmp { .. }) => {
            Err(ReflectRefusal::ComparisonUsedAsValue { value: value.as_usize() })
        }
        None => Err(ReflectRefusal::UndefinedOperand { value: value.as_usize() }),
    }
}

/// A TrustIR integer constant as the `Nat` numeral a `UIntN.ofNat` takes.
///
/// Refuses anything not literally in `0 .. 2^width`. In particular a NEGATIVE
/// payload is refused rather than reinterpreted as its two's-complement image:
/// the reflector would then be asserting a bit-pattern convention that this
/// artifact does not state, and a proof built on a convention nobody wrote down
/// is exactly the failure this file exists to avoid.
fn constant_as_uint(value: &Constant, width: u32) -> Result<u64, ReflectRefusal> {
    let raw = match value {
        Constant::Int(v) => *v,
        other => {
            return Err(ReflectRefusal::UnsupportedConstant { detail: format!("{other:?}") });
        }
    };
    if raw < 0 {
        return Err(ReflectRefusal::UnsupportedConstant {
            detail: format!("negative payload {raw} at an unsigned UInt{width} carrier"),
        });
    }
    let limit: i128 = 1i128 << width;
    if raw >= limit {
        return Err(ReflectRefusal::UnsupportedConstant {
            detail: format!("{raw} does not fit UInt{width}"),
        });
    }
    Ok(u64::try_from(raw).expect("checked against 2^64"))
}

/// The TrustIR variant name of an instruction, for refusal messages.
fn inst_name(inst: &Inst) -> &'static str {
    match inst {
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
        Inst::Const { .. } => "Const",
        Inst::Undef { .. } => "Undef",
        Inst::Assume { .. } => "Assume",
        Inst::Assert { .. } => "Assert",
        Inst::Unreachable => "Unreachable",
        Inst::Copy { .. } => "Copy",
        Inst::Select { .. } => "Select",
        _ => "<other TrustIR instruction>",
    }
}

// ===========================================================================
// PART 2 — the harness
// ===========================================================================

/// A checked island session plus the environment it produced.
struct Island {
    session: CleanIslandSession,
}

impl Island {
    fn check(source: &str) -> Self {
        let mut session = CleanIslandSession::new();
        let outcome = session.check(source);
        assert!(
            outcome.errors.is_empty(),
            "the Clean island must check before anything downstream is meaningful: {:?}",
            outcome.errors
        );
        Self { session }
    }

    fn env(&self) -> &Environment {
        self.session.environment().expect("an untainted session exposes its environment")
    }

    /// Plan + emit: this is the ARTIFACT UNDER TEST. Calling the emitter is
    /// fine — reading it is what would invalidate this file.
    fn emit(&self, name: &str) -> Function {
        let plan = trust_clean_origin::plan_clean_origin_body(self.env(), name)
            .unwrap_or_else(|e| panic!("plan {name}: {e:?}"));
        trust_clean_ir::emit_clean_origin_function(&plan, FuncId::new(0), FuncTyId::new(0))
            .unwrap_or_else(|e| panic!("emit {name}: {e:?}"))
    }

    fn declared(&self, name: &str) -> Expr {
        self.env()
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} is not registered"))
            .value
            .clone()
            .unwrap_or_else(|| panic!("{name} has no value"))
    }
}

/// `is_def_eq(reflected, declared)` — the kernel's verdict, and the only one
/// that counts.
fn kernel_accepts(env: &Environment, a: &Expr, b: &Expr) -> bool {
    TypeChecker::new(env).is_def_eq(a, b)
}

/// One covered shape: Clean source name, and the concrete inputs the
/// differential leg exercises.
struct Shape {
    name: &'static str,
    width: u32,
    points: &'static [&'static [u64]],
}

/// Leg B — the independence anchor.
///
/// Runs TrustIR's own reference interpreter on the emitted function, then
/// applies the REFLECTED term to the same inputs and asks the kernel whether it
/// equals the interpreter's answer. The declaration takes no part in this, so
/// it catches an opcode mapping that is wrong in a way leg A cannot see.
fn differential_leg(env: &Environment, shape: &Shape, func: &Function, reflected: &Expr) {
    let interpreter = Interpreter::new();
    let arg_ty = match shape.width {
        8 => Ty::U8,
        16 => Ty::U16,
        32 => Ty::U32,
        64 => Ty::U64,
        w => panic!("unexpected width {w}"),
    };
    for point in shape.points {
        let args: Vec<InterpretValue> = point
            .iter()
            .map(|v| {
                InterpretValue::int(arg_ty.clone(), i128::from(*v)).expect("in-range argument")
            })
            .collect();
        let outcome = interpreter
            .execute_function(func, args)
            .unwrap_or_else(|e| panic!("interpret {}: {e:?}", shape.name));
        let [ret] = outcome.returns.as_slice() else {
            panic!("{} returned {} values", shape.name, outcome.returns.len());
        };
        let expected = ret
            .as_int()
            .unwrap_or_else(|| panic!("{} did not return an integer", shape.name))
            .as_unsigned();
        let expected = u64::try_from(expected).expect("fits a u64 carrier");

        let applied =
            Expr::apps(reflected.clone(), point.iter().map(|v| uint_lit(shape.width, *v)));
        let target = uint_lit(shape.width, expected);
        assert!(
            kernel_accepts(env, &applied, &target),
            "DIFFERENTIAL MISMATCH for `{}` at {point:?}: the TrustIR interpreter says \
             {expected}, but the kernel does not agree that the reflected term reduces \
             to it. The opcode mapping in this reflector is wrong.",
            shape.name
        );
    }
}

const SOURCE: &str = r"
def projA (a : UInt8) (b : UInt8) : UInt8 := a
def projB (a : UInt8) (b : UInt8) : UInt8 := b
def addU8 (a : UInt8) (b : UInt8) : UInt8 := a + b
def subU8 (a : UInt8) (b : UInt8) : UInt8 := a - b
def mulU8 (a : UInt8) (b : UInt8) : UInt8 := a * b
def litU8 (a : UInt8) : UInt8 := a + 7
def litOnlyU8 : UInt8 := 200
def nestU8 (a : UInt8) (b : UInt8) : UInt8 := (a + b) * (a - b)
def deepU8 (a : UInt8) (b : UInt8) : UInt8 := ((a + b) * (a + 3)) - (b * b)
def triU8 (a : UInt8) (b : UInt8) (c : UInt8) : UInt8 := (a + b) * c
def andU8 (a : UInt8) (b : UInt8) : UInt8 := a &&& b
def orU8 (a : UInt8) (b : UInt8) : UInt8 := a ||| b
def minU8 (a : UInt8) (b : UInt8) : UInt8 := if a < b then a else b
def maxU8 (a : UInt8) (b : UInt8) : UInt8 := if a < b then b else a
def leU8 (a : UInt8) (b : UInt8) : UInt8 := if a <= b then a else b
def eqU8 (a : UInt8) (b : UInt8) : UInt8 := if a = b then a else b
def clampU8 (a : UInt8) (b : UInt8) : UInt8 := if a < 10 then a else b
def leLitU8 (a : UInt8) (b : UInt8) : UInt8 := if a <= 10 then a else b
def eqLitU8 (a : UInt8) (b : UInt8) : UInt8 := if a = 10 then a else b
def flagU8 (a : UInt8) (b : UInt8) : UInt8 := if a < b then 1 else 0
def addU16 (a : UInt16) (b : UInt16) : UInt16 := a + b
def nestU16 (a : UInt16) (b : UInt16) : UInt16 := (a - b) * (b + 9)
def minU16 (a : UInt16) (b : UInt16) : UInt16 := if a < b then a else b
def addU32 (a : UInt32) (b : UInt32) : UInt32 := a + b
def nestU32 (a : UInt32) (b : UInt32) : UInt32 := (a * b) + (a - b)
def minU32 (a : UInt32) (b : UInt32) : UInt32 := if a < b then a else b
def addU64 (a : UInt64) (b : UInt64) : UInt64 := a + b
def nestU64 (a : UInt64) (b : UInt64) : UInt64 := (a + b) * (a - b)
def minU64 (a : UInt64) (b : UInt64) : UInt64 := if a < b then a else b
";

/// The covered fragment, one row per shape x width.
const SHAPES: &[Shape] = &[
    // parameter projection — both positions, so a de Bruijn off-by-one is
    // caught rather than cancelled by symmetry.
    Shape { name: "projA", width: 8, points: &[&[0, 0], &[7, 200], &[255, 1]] },
    Shape { name: "projB", width: 8, points: &[&[0, 0], &[7, 200], &[255, 1]] },
    // arithmetic, including the wrap-sensitive points.
    Shape { name: "addU8", width: 8, points: &[&[3, 5], &[200, 100], &[255, 1]] },
    Shape { name: "subU8", width: 8, points: &[&[5, 3], &[0, 1], &[100, 200]] },
    Shape { name: "mulU8", width: 8, points: &[&[3, 5], &[16, 16], &[255, 255]] },
    // integer constants.
    Shape { name: "litU8", width: 8, points: &[&[0], &[1], &[250]] },
    Shape { name: "litOnlyU8", width: 8, points: &[&[]] },
    // nesting, and an arity the two-parameter shapes cannot exercise.
    Shape { name: "nestU8", width: 8, points: &[&[7, 3], &[0, 1], &[200, 99]] },
    Shape { name: "deepU8", width: 8, points: &[&[7, 3], &[0, 1], &[200, 99]] },
    Shape { name: "triU8", width: 8, points: &[&[1, 2, 3], &[200, 99, 7], &[0, 0, 255]] },
    // bitwise.
    Shape { name: "andU8", width: 8, points: &[&[0b1100, 0b1010], &[255, 0], &[255, 255]] },
    Shape { name: "orU8", width: 8, points: &[&[0b1100, 0b1010], &[255, 0], &[0, 0]] },
    // Select — both arm orders, and all three relations. `[4, 4]` is the point
    // that separates `<` from `<=` and both from `=`, so a mapping that
    // confused them could not pass.
    Shape { name: "minU8", width: 8, points: &[&[3, 5], &[5, 3], &[4, 4], &[200, 100]] },
    Shape { name: "maxU8", width: 8, points: &[&[3, 5], &[5, 3], &[4, 4], &[200, 100]] },
    Shape { name: "leU8", width: 8, points: &[&[3, 5], &[5, 3], &[4, 4], &[200, 100]] },
    Shape { name: "eqU8", width: 8, points: &[&[4, 4], &[3, 5], &[0, 0], &[255, 254]] },
    // Literal comparison RHS for the two relations added beside the existing
    // less-than clamp probe. Boundary-adjacent points distinguish the opcodes.
    Shape { name: "leLitU8", width: 8, points: &[&[9, 5], &[10, 5], &[11, 5], &[255, 1]] },
    Shape { name: "eqLitU8", width: 8, points: &[&[9, 5], &[10, 5], &[11, 5], &[255, 1]] },
    // Literal ARMS, as opposed to a literal comparison operand (`clampU8`, pinned
    // by `order_comparison_against_a_numeral_is_no_longer_a_limit`): no instance
    // is involved.
    Shape { name: "flagU8", width: 8, points: &[&[3, 5], &[5, 3], &[4, 4]] },
    // the other three carriers.
    Shape { name: "addU16", width: 16, points: &[&[3, 5], &[65535, 1]] },
    Shape { name: "nestU16", width: 16, points: &[&[3, 5], &[0, 1]] },
    Shape { name: "minU16", width: 16, points: &[&[3, 5], &[40000, 100]] },
    Shape { name: "addU32", width: 32, points: &[&[3, 5], &[4294967295, 1]] },
    Shape { name: "nestU32", width: 32, points: &[&[3, 5], &[0, 1]] },
    Shape { name: "minU32", width: 32, points: &[&[3, 5], &[3000000000, 100]] },
    Shape { name: "addU64", width: 64, points: &[&[3, 5], &[18446744073709551615, 1]] },
    Shape { name: "nestU64", width: 64, points: &[&[3, 5], &[0, 1]] },
    Shape { name: "minU64", width: 64, points: &[&[3, 5], &[18446744073709551615, 100]] },
];

// ---------------------------------------------------------------------------
// LEG A — the kernel decides
// ---------------------------------------------------------------------------

#[test]
fn kernel_accepts_every_covered_shape() {
    let island = Island::check(SOURCE);
    let env = island.env();
    let mut agreed = 0usize;
    for shape in SHAPES {
        let func = island.emit(shape.name);
        let reflected = reflect_uint_straight_line(&func)
            .unwrap_or_else(|r| panic!("REFUSED to reflect `{}`: {r:?}", shape.name));
        let declared = island.declared(shape.name);
        assert!(
            kernel_accepts(env, &reflected, &declared),
            "the kernel REJECTED the reflection of `{}`.\n  reflected: {reflected:?}\n  declared:  {declared:?}",
            shape.name
        );
        agreed += 1;
    }
    assert_eq!(agreed, SHAPES.len());
    eprintln!("kernel is_def_eq acceptances: {agreed}");
}

// ---------------------------------------------------------------------------
// LEG B — the independence anchor
// ---------------------------------------------------------------------------

#[test]
fn reflection_agrees_with_the_trust_ir_interpreter() {
    let island = Island::check(SOURCE);
    let env = island.env();
    for shape in SHAPES {
        let func = island.emit(shape.name);
        let reflected = reflect_uint_straight_line(&func)
            .unwrap_or_else(|r| panic!("REFUSED to reflect `{}`: {r:?}", shape.name));
        differential_leg(env, shape, &func, &reflected);
    }
}

/// Why leg B is not decoration: it catches the ONE failure kernel agreement is
/// structurally blind to.
///
/// Staged here deliberately — an emitter that emits `Sub` where the Clean source
/// says `+`, checked by a reflector that reads `Sub` back as `+`. The two
/// mistakes CANCEL, and the kernel, asked only "does the reflection match the
/// declaration", says yes about a body that computes something else entirely.
/// This is precisely the reason this file was written without reading the
/// emitter; the differential leg is the belt to that suspenders, because it
/// EXECUTES the IR instead of re-spelling it.
#[test]
fn a_cancelling_round_trip_is_caught_only_by_execution() {
    let island = Island::check(SOURCE);
    let env = island.env();

    // Stands in for a mis-emitted `a + b`: the IR really contains `Sub`.
    let wrong_ir = island.emit("subU8");
    // Stands in for a reflector that reads `Sub` as `+`.
    let cancelling = Expr::lam(
        BinderInfo::Default,
        carrier(8),
        Expr::lam(
            BinderInfo::Default,
            carrier(8),
            hetero_binop("HAdd", "hAdd", "instHAdd", 8, Expr::bvar(1), Expr::bvar(0)),
        ),
    );

    // LEG A IS FOOLED. It has to be, or this test demonstrates nothing.
    assert!(
        kernel_accepts(env, &cancelling, &island.declared("addU8")),
        "the staged cancellation must actually fool kernel agreement"
    );

    // LEG B IS NOT. Execute the IR: at (3, 5) it wraps to 254, not 8.
    let outcome = Interpreter::new()
        .execute_function(
            &wrong_ir,
            [
                InterpretValue::int(Ty::U8, 3).expect("in range"),
                InterpretValue::int(Ty::U8, 5).expect("in range"),
            ],
        )
        .expect("interprets");
    let actual = u64::try_from(outcome.returns[0].as_int().expect("integer result").as_unsigned())
        .expect("fits u64");
    assert_eq!(actual, 254, "wrapping 3 - 5 at UInt8");
    let applied = Expr::apps(cancelling, [uint_lit(8, 3), uint_lit(8, 5)]);
    assert!(
        !kernel_accepts(env, &applied, &uint_lit(8, actual)),
        "the differential leg must reject a cancellation that kernel agreement accepts"
    );
}

/// THE SHAPE THIS REFLECTOR USED TO REFUSE, and the measurement that retired the
/// refusal.
///
/// `if a < 10 then a else b` plans, emits, and interprets fine. Until the Clean
/// pin carried `c91fa93f5` it was refused here by name
/// (`ReflectRefusal::OrderComparisonAgainstNumeral`), because kernel agreement
/// for it could not be a function of the IR:
///
///   1. Clean elaborated `a < b` at `UInt8` to `instDecidableUInt8Lt a b`, but
///      `a < 10` to `instDecidableNatLt a.toBitVec.toFin.val 10` — a `Nat`-level
///      instance of the *same* proposition.
///   2. Those two `Decidable` terms were NOT definitionally equal (`Decidable` is
///      data, not a `Prop`, so there is no proof irrelevance to collapse the
///      diamond).
///   3. TrustIR records that the right operand has the VALUE 10, not that the
///      Clean source WROTE a numeral there.
///
/// Clean `c91fa93f5` ("kernel(uint): the BitVec-carrier decLe/decLt ARE
/// Nat.decLe/decLt, so `decide (d < 21)` is the carrier's decision") removed
/// premise 2: the uniform and `Nat`-reduced instances are now KERNEL-EQUAL, so
/// the uniform spelling earns agreement whichever instance the elaborator picks,
/// and premise 3 stops mattering — no rule about the elaborator is needed when
/// every instance it can pick is one term. Measured with `clean check` at the
/// superproject pin `dca882b5f`: the elaborator now picks the carrier instance
/// over the unfolded numeral (`instDecidableUInt8Lt a (UInt8.ofBitVec
/// (BitVec.ofFin 8 (Fin.ofNat 255 10)))`) for a numeral on the right, still the
/// `Nat`-reduced `instDecidableNatLt 10 a.toBitVec.toFin.val` for a numeral on
/// the LEFT, and the uniform reflection is accepted against both, at `<` and
/// `<=` and at all four widths. On the previous pin (`faf434b73`) every one of
/// those is rejected.
///
/// So the refusal is gone, as its own assertion message asked. Dropping it
/// cannot admit a wrong body: a reflection is evidence only when the kernel
/// accepts it, and the refusal only ever withheld evidence. What is pinned
/// instead, so that the new acceptance is not taken on faith:
///
///   * leg A — `clampU8` reflects AND the kernel accepts it (`Subject::new`,
///     the same control the mutation legs rest on);
///   * leg B — the reflected term computes the interpreter's answer on either
///     side of the numeral and AT it (`[10, 5]`, where `<` and `<=` part);
///   * leg D — every mutation operator that applies to this shape is caught BY
///     THE KERNEL, so the check still discriminates here and is not accepting
///     anything with an `ite` in it;
///   * the measurement itself — uniform and `Nat`-reduced instances are
///     kernel-equal, with the numeral on either side. If a Clean pin ever makes
///     them distinct again this fails first, and the refusal must come back.
///
/// `=` stays the CONTROL: a numeral on an equality keeps the uniform
/// `instDecidableEqUInt8` on every pin measured, so it never needed a refusal.
#[test]
fn order_comparison_against_a_numeral_is_no_longer_a_limit() {
    const CLAMP_POINTS: &[&[u64]] = &[&[3, 5], &[9, 5], &[10, 5], &[11, 5], &[255, 1], &[0, 200]];
    const CLAMP: Shape = Shape { name: "clampU8", width: 8, points: CLAMP_POINTS };

    let island = Island::check(SOURCE);
    let env = island.env();

    // Leg A: the emitted body reflects and the kernel accepts it — the
    // constructor panics otherwise.
    let subject = Subject::new(&island, "clampU8");
    let reflected = reflect_uint_straight_line(&subject.pristine).expect("clampU8 reflects");

    // Leg B: the reflected term agrees with the TrustIR interpreter.
    differential_leg(env, &CLAMP, &subject.pristine, &reflected);

    // Leg D: each operator that applies here is caught, and by the kernel — the
    // refusal that used to catch the operand swap is gone.
    for name in [
        "select-arms-swapped",
        "constant-shifted-by-one",
        "ult-widened-to-ule",
        "icmp-operands-swapped",
    ] {
        assert_eq!(
            subject.must_catch(mutation(name)),
            MutationVerdict::CaughtByKernel,
            "`{name}` on clampU8 must be a kernel rejection of a fully spelled term"
        );
    }

    // The newly exposed literal <= and propositional-equality single selects
    // take the same independent route. Pin their comparison identity rather
    // than relying only on boundary execution.
    for (name, expected, wrong) in
        [("leLitU8", ICmpOp::Ule, ICmpOp::Ult), ("eqLitU8", ICmpOp::Eq, ICmpOp::Ult)]
    {
        let subject = Subject::new(&island, name);
        for mutation_name in ["select-arms-swapped", "constant-shifted-by-one"] {
            assert!(
                subject.must_catch(mutation(mutation_name)).caught(),
                "{mutation_name} must be caught for {name}"
            );
        }
        let mut corrupt = subject.pristine.clone();
        let node = corrupt.blocks[0]
            .body
            .iter_mut()
            .find(|node| matches!(&node.inst, Inst::ICmp { .. }))
            .expect("literal select has one emitted comparison");
        let Inst::ICmp { op, .. } = &mut node.inst else { unreachable!() };
        assert_eq!(*op, expected);
        *op = wrong;
        assert_eq!(
            subject.verdict_of(&corrupt),
            MutationVerdict::CaughtByKernel,
            "wrong comparison on {name} must be a kernel rejection"
        );
    }

    // The measurement the refusal rested on, now asserted the other way: the
    // uniform instance and the `Nat`-reduced one every pre-`c91fa93f5` pin
    // elaborated are kernel-equal under two open binders.
    let a = Expr::bvar(1);
    let to_nat = |e: Expr| proj("Fin", 0, proj("BitVec", 0, proj("UInt8", 0, e)));
    let under_two_binders = |e: Expr| {
        Expr::lam(BinderInfo::Default, carrier(8), Expr::lam(BinderInfo::Default, carrier(8), e))
    };
    let uniform = decidable_inst("instDecidableUInt8Lt", a.clone(), uint_lit(8, 10));
    let nat_reduced =
        Expr::apps(Expr::const_str("instDecidableNatLt"), [to_nat(a.clone()), Expr::nat_lit(10)]);
    assert!(
        kernel_accepts(env, &under_two_binders(uniform), &under_two_binders(nat_reduced)),
        "the uniform and Nat-reduced Decidable instances of `a < 10` are no longer \
         def_eq: this Clean pin predates c91fa93f5 or reverted it. Restore the \
         OrderComparisonAgainstNumeral refusal — it existed only because they were not"
    );
    // The same with the numeral on the LEFT, where the elaborator still mints
    // the `Nat`-reduced instance, and against a real declaration: the uniform
    // reflection is accepted there too.
    let flipped = decidable_inst("instDecidableUInt8Lt", uint_lit(8, 10), a.clone());
    let flipped_nat =
        Expr::apps(Expr::const_str("instDecidableNatLt"), [Expr::nat_lit(10), to_nat(a)]);
    assert!(
        kernel_accepts(env, &under_two_binders(flipped.clone()), &under_two_binders(flipped_nat)),
        "the uniform and Nat-reduced Decidable instances of `10 < a` must be def_eq"
    );
    let left =
        Island::check("def ltLitLeftU8 (a : UInt8) (b : UInt8) : UInt8 := if 10 < a then a else b");
    let uniform_left_body =
        ite(8, lt_prop(8, uint_lit(8, 10), Expr::bvar(1)), flipped, Expr::bvar(1), Expr::bvar(0));
    assert!(
        kernel_accepts(
            left.env(),
            &under_two_binders(uniform_left_body),
            &left.declared("ltLitLeftU8")
        ),
        "a numeral on the left of `<` must reflect uniformly too"
    );

    // CONTROL: for `a = 10` the elaborator keeps the uniform
    // `instDecidableEqUInt8`, so the uniform spelling this reflector emits is
    // accepted — on every pin, which is why the old reflector refusal was
    // only ever keyed on ORDER relations. The emitter now exposes this exact
    // term too; `eqLitU8`'s SHAPES row exercises that route independently.
    let uniform_eq_body = ite(
        8,
        eq_prop(8, Expr::bvar(1), uint_lit(8, 10)),
        decidable_inst("instDecidableEqUInt8", Expr::bvar(1), uint_lit(8, 10)),
        Expr::bvar(1),
        Expr::bvar(0),
    );
    assert!(
        kernel_accepts(env, &under_two_binders(uniform_eq_body), &island.declared("eqLitU8")),
        "a numeral on `=` keeps the uniform instance, so nothing needs refusing there"
    );
}

/// `Expr::proj` with owned children, for readability above.
fn proj(structure: &str, idx: u32, of: Expr) -> Expr {
    Expr::proj_arc(Name::from_string(structure), idx, std::sync::Arc::new(of))
}

/// The two carrier facts the whole opcode mapping rests on, pinned AT THE
/// KERNEL rather than assumed from Lean folklore.
///
/// Both probes are chosen so that the WRONG reading gives a different answer:
/// truncated `Nat` subtraction would make `0 - 1 = 0`, and a signed comparison
/// would make `200 < 100` true at `UInt8`.
#[test]
fn carrier_semantics_are_anchored() {
    let island = Island::check(
        r"
def wrapProbe : UInt8 := (0 : UInt8) - (1 : UInt8)
def ordProbe (a : UInt8) (b : UInt8) : UInt8 := if a < b then 1 else 0
",
    );
    let env = island.env();

    // 1. `UInt8` subtraction WRAPS, matching TrustIR's `wrapping_sub`.
    let wrap = island.declared("wrapProbe");
    assert!(
        kernel_accepts(env, &wrap, &uint_lit(8, 255)),
        "UInt8 subtraction must wrap; TrustIR BinOp::Sub is wrapping_sub"
    );
    assert!(
        !kernel_accepts(env, &wrap, &uint_lit(8, 0)),
        "a truncated-Nat subtraction would break the Sub mapping"
    );

    // 2. `<` at `UInt8` is UNSIGNED, matching TrustIR's `ICmpOp::Ult`.
    let ord = island.declared("ordProbe");
    let at = |a: u64, b: u64| Expr::apps(ord.clone(), [uint_lit(8, a), uint_lit(8, b)]);
    assert!(kernel_accepts(env, &at(100, 200), &uint_lit(8, 1)), "100 < 200");
    assert!(
        kernel_accepts(env, &at(200, 100), &uint_lit(8, 0)),
        "200 < 100 must be FALSE at UInt8; a signed reading would say true"
    );
}

// ---------------------------------------------------------------------------
// LEG C — non-vacuity
// ---------------------------------------------------------------------------

/// A reflector that ignored its input and returned the declaration would pass
/// leg A perfectly. These are the cases that must FAIL.
#[test]
fn kernel_rejects_wrong_reflections() {
    let island = Island::check(SOURCE);
    let env = island.env();

    // 1. The reflection of a DIFFERENT body. `a - b` is not `a + b`.
    let sub_ir = island.emit("subU8");
    let sub_reflected = reflect_uint_straight_line(&sub_ir).expect("reflects");
    assert!(
        !kernel_accepts(env, &sub_reflected, &island.declared("addU8")),
        "NON-VACUITY BROKEN: the kernel accepted `a - b` as `a + b`"
    );
    assert!(
        kernel_accepts(env, &sub_reflected, &island.declared("subU8")),
        "control: the same term must still be accepted against its own declaration"
    );

    // 2. A term built with THIS FILE's own spelling helpers, deliberately
    //    wrong: `b + a` reversed is harmless for `+`, so use `-`, where operand
    //    order is observable.
    let b_minus_a = Expr::lam(
        BinderInfo::Default,
        carrier(8),
        Expr::lam(
            BinderInfo::Default,
            carrier(8),
            hetero_binop("HSub", "hSub", "instHSub", 8, Expr::bvar(0), Expr::bvar(1)),
        ),
    );
    assert!(
        !kernel_accepts(env, &b_minus_a, &island.declared("subU8")),
        "NON-VACUITY BROKEN: the kernel accepted `b - a` as `a - b`"
    );

    // 3. A swapped `ite` pair: `min` reflected as `max`.
    let swapped = Expr::lam(
        BinderInfo::Default,
        carrier(8),
        Expr::lam(
            BinderInfo::Default,
            carrier(8),
            ite(
                8,
                lt_prop(8, Expr::bvar(1), Expr::bvar(0)),
                lt_decidable(8, Expr::bvar(1), Expr::bvar(0)),
                Expr::bvar(0),
                Expr::bvar(1),
            ),
        ),
    );
    assert!(
        !kernel_accepts(env, &swapped, &island.declared("minU8")),
        "NON-VACUITY BROKEN: the kernel accepted `max` as `min`"
    );
    assert!(
        kernel_accepts(env, &swapped, &island.declared("maxU8")),
        "control: the swapped term IS `max`"
    );

    // 4. A wrong literal: `a + 8` is not `a + 7`.
    let off_by_one = Expr::lam(
        BinderInfo::Default,
        carrier(8),
        hetero_binop("HAdd", "hAdd", "instHAdd", 8, Expr::bvar(0), uint_lit(8, 8)),
    );
    assert!(
        !kernel_accepts(env, &off_by_one, &island.declared("litU8")),
        "NON-VACUITY BROKEN: the kernel accepted `a + 8` as `a + 7`"
    );

    // 5. A wrong PROJECTION: `projA` reflected as `projB` and back. This is the
    //    de Bruijn off-by-one that a symmetric operator would hide.
    let proj_a = reflect_uint_straight_line(&island.emit("projA")).expect("reflects");
    assert!(
        !kernel_accepts(env, &proj_a, &island.declared("projB")),
        "NON-VACUITY BROKEN: the kernel accepted the first projection as the second"
    );

    // 6. A wrong CARRIER: the UInt16 sum is not the UInt8 sum.
    let add16 = reflect_uint_straight_line(&island.emit("addU16")).expect("reflects");
    assert!(
        !kernel_accepts(env, &add16, &island.declared("addU8")),
        "NON-VACUITY BROKEN: the kernel accepted a UInt16 body as a UInt8 body"
    );
}

// ---------------------------------------------------------------------------
// The refusals, exercised
// ---------------------------------------------------------------------------

/// A refusal is a first-class answer, so it gets tests. Each case is a shape
/// this reflector will not spell, and the point is that it says so by NAME
/// instead of producing a term the kernel might accept.
#[test]
fn unsupported_shapes_are_refused_by_name() {
    use trust_ir::value::BlockId;
    use trust_ir::{Block, InstrNode};

    let mk = |params: Vec<(ValueId, Ty)>, body: Vec<InstrNode>| {
        let mut f = Function::new(FuncId::new(0), "probe", FuncTyId::new(0), BlockId::new(0));
        let mut b = Block::new(BlockId::new(0));
        b.params = params;
        b.body = body;
        f.blocks.push(b);
        f
    };

    // Signed carrier.
    let f = mk(
        vec![(ValueId::new(0), Ty::I32)],
        vec![InstrNode::new(Inst::Return { values: vec![ValueId::new(0)] })],
    );
    assert!(matches!(
        reflect_uint_straight_line(&f),
        Err(ReflectRefusal::UnsupportedCarrier { .. })
    ));

    // Target-dependent width.
    let f = mk(
        vec![(ValueId::new(0), Ty::Usize)],
        vec![InstrNode::new(Inst::Return { values: vec![ValueId::new(0)] })],
    );
    assert!(matches!(
        reflect_uint_straight_line(&f),
        Err(ReflectRefusal::UnsupportedCarrier { .. })
    ));

    // Division: Clean's `UInt8.div` is total, TrustIR's `UDiv` is not.
    let f = mk(
        vec![(ValueId::new(0), Ty::U8), (ValueId::new(1), Ty::U8)],
        vec![
            InstrNode::new(Inst::BinOp {
                op: BinOp::UDiv,
                ty: Ty::U8,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return { values: vec![ValueId::new(2)] }),
        ],
    );
    assert_eq!(
        reflect_uint_straight_line(&f),
        Err(ReflectRefusal::UnsupportedBinOp { op: "UDiv".to_string() })
    );

    // Signed comparison.
    let f = mk(
        vec![(ValueId::new(0), Ty::U8), (ValueId::new(1), Ty::U8)],
        vec![
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Slt,
                ty: Ty::U8,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Select {
                ty: Ty::U8,
                cond: ValueId::new(2),
                then_val: ValueId::new(0),
                else_val: ValueId::new(1),
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::Return { values: vec![ValueId::new(3)] }),
        ],
    );
    assert_eq!(
        reflect_uint_straight_line(&f),
        Err(ReflectRefusal::UnsupportedICmp { op: "Slt".to_string() })
    );

    // A `Select` on a Bool this reflector cannot name a proposition for. THIS
    // is the case that would be a false verdict if it were guessed at.
    let f = mk(
        vec![(ValueId::new(0), Ty::U8), (ValueId::new(1), Ty::U8)],
        vec![
            InstrNode::new(Inst::Const { ty: Ty::Bool, value: Constant::Bool(true) })
                .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Select {
                ty: Ty::U8,
                cond: ValueId::new(2),
                then_val: ValueId::new(0),
                else_val: ValueId::new(1),
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::Return { values: vec![ValueId::new(3)] }),
        ],
    );
    assert!(matches!(
        reflect_uint_straight_line(&f),
        // The Bool const is refused first, at the carrier; either way nothing
        // is invented for it.
        Err(ReflectRefusal::UnsupportedCarrier { .. })
            | Err(ReflectRefusal::SelectConditionIsNotAComparison { .. })
    ));

    // A comparison returned as if it were a number.
    let f = mk(
        vec![(ValueId::new(0), Ty::U8), (ValueId::new(1), Ty::U8)],
        vec![
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Ult,
                ty: Ty::U8,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return { values: vec![ValueId::new(2)] }),
        ],
    );
    assert_eq!(
        reflect_uint_straight_line(&f),
        Err(ReflectRefusal::ComparisonUsedAsValue { value: 2 })
    );

    // A negative constant payload at an unsigned carrier is NOT reinterpreted.
    let f = mk(
        vec![],
        vec![
            InstrNode::new(Inst::Const { ty: Ty::U8, value: Constant::Int(-1) })
                .with_result(ValueId::new(0)),
            InstrNode::new(Inst::Return { values: vec![ValueId::new(0)] }),
        ],
    );
    assert!(matches!(
        reflect_uint_straight_line(&f),
        Err(ReflectRefusal::UnsupportedConstant { .. })
    ));

    // Multi-block: outside the straight-line fragment.
    let mut f =
        mk(vec![], vec![InstrNode::new(Inst::Br { target: BlockId::new(1), args: vec![] })]);
    f.blocks.push(Block::new(BlockId::new(1)));
    assert_eq!(reflect_uint_straight_line(&f), Err(ReflectRefusal::NotSingleBlock { blocks: 2 }));

    // Memory: not a mathematical function of the block parameters at all.
    let f = mk(
        vec![(ValueId::new(0), Ty::Ptr)],
        vec![
            InstrNode::new(Inst::Load {
                ty: Ty::U8,
                ptr: ValueId::new(0),
                volatile: false,
                align: None,
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Return { values: vec![ValueId::new(1)] }),
        ],
    );
    assert!(matches!(
        reflect_uint_straight_line(&f),
        Err(ReflectRefusal::UnsupportedCarrier { .. })
    ));
}

// ===========================================================================
// PART 3 — LEG D: MUTATION. Proving legs A-C are not vacuous.
// ===========================================================================
//
// WHAT LEG C CANNOT DO. Leg C hand-writes wrong Clean terms and shows the
// kernel rejects them. That establishes the COMPARISON discriminates. It says
// nothing about the PIPELINE, because no wrong `trust_ir::Function` ever enters
// it: every function leg C reflects is one the emitter produced correctly.
// A check that is green on the pristine artifact and would ALSO be green on a
// corrupted one has measured nothing.
//
// WHAT LEG D DOES. Take the `trust_ir::Function` the emitter actually emitted,
// corrupt it at exactly ONE instruction, and put the corpse through the SAME
// check the pristine body passes. Two outcomes count as caught:
//
//   * the reflector REFUSES to spell the mutant (a refusal is a first-class
//     answer here, and a refused body never reaches a verdict), or
//   * the reflector spells it and `is_def_eq` against the DECLARATION says no.
//
// Anything else is a SURVIVING MUTANT: a `trust_ir::Function` that does not
// implement the Clean declaration, blessed by the kernel anyway. That is the
// single most valuable thing this file can find, so `mutation_sweep` collects
// every survivor before it fails, and names them all.
//
// THE CONTROL IS NOT OPTIONAL. Every mutation below runs through [`Subject`],
// whose constructor first asserts the PRISTINE body reflects AND is accepted by
// the kernel. Without that, "the check failed on the mutant" could equally mean
// the check was already failing for that shape, and the mutation would have
// proved nothing.
//
// MINIMALITY. Each operator corrupts the FIRST matching instruction only, not
// every match. A one-point corruption is the hardest mutant to catch — a
// wholesale rewrite would be caught by almost any check — so it is the one
// worth measuring. `mutate_first` additionally asserts the mutant is `!=` the
// pristine `Function`, so an operator that reports a change it did not make
// cannot silently score a free "caught".

/// What happened when a mutant went through the check the pristine body passes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MutationVerdict {
    /// The reflector declined to spell the corrupted body at all.
    CaughtByRefusal,
    /// The reflector spelled it, and the kernel rejected it against the
    /// declaration.
    CaughtByKernel,
    /// THE BAD ONE. The corrupted body reflected, and the kernel accepted it
    /// against a declaration it does not implement.
    Survived,
    /// The operator found nothing of its kind in this shape. NOT a pass — a
    /// mutation that never applied is not evidence about anything.
    NotApplicable,
}

impl MutationVerdict {
    fn caught(self) -> bool {
        matches!(self, Self::CaughtByRefusal | Self::CaughtByKernel)
    }

    fn tag(self) -> &'static str {
        match self {
            Self::CaughtByRefusal => "caught(refusal)",
            Self::CaughtByKernel => "caught(kernel)",
            Self::Survived => "SURVIVED",
            Self::NotApplicable => "n/a",
        }
    }
}

/// A single-instruction corruption of an emitted function.
struct Mutation {
    name: &'static str,
    /// Corrupt `inst` in place; return `true` iff it actually changed it.
    /// Applied to the FIRST matching instruction only — see MINIMALITY above.
    apply: fn(&mut Inst) -> bool,
}

/// Swap the two arms of a `Select`. Turns `min` into `max`.
fn mut_swap_select_arms(inst: &mut Inst) -> bool {
    if let Inst::Select { then_val, else_val, .. } = inst {
        if then_val == else_val {
            return false;
        }
        std::mem::swap(then_val, else_val);
        return true;
    }
    false
}

/// `BinOp::Add` -> `BinOp::Sub`. The classic wrong-opcode emission.
fn mut_add_to_sub(inst: &mut Inst) -> bool {
    if let Inst::BinOp { op, .. } = inst {
        if *op == BinOp::Add {
            *op = BinOp::Sub;
            return true;
        }
    }
    false
}

/// Swap the operands of a `Sub`. Chosen because `-` is NON-COMMUTATIVE, so the
/// mutant is a genuinely different function — an operand swap on `+` would be
/// a mutant nothing SHOULD catch semantically.
fn mut_swap_sub_operands(inst: &mut Inst) -> bool {
    if let Inst::BinOp { op: BinOp::Sub, lhs, rhs, .. } = inst {
        if lhs == rhs {
            return false;
        }
        std::mem::swap(lhs, rhs);
        return true;
    }
    false
}

/// Shift an integer `Constant` by one. The off-by-one an emitter makes when it
/// mis-reads a numeral.
fn mut_shift_constant(inst: &mut Inst) -> bool {
    if let Inst::Const { value: Constant::Int(v), .. } = inst {
        *v += 1;
        return true;
    }
    false
}

/// Widen a strict order to a non-strict one: `ICmpOp::Ult` -> `ICmpOp::Ule`.
///
/// The subtlest of the five. `min` under `<` and `min` under `<=` are the SAME
/// FUNCTION — they differ only at `a = b`, where both arms hold the same value —
/// so this mutant is invisible to any purely extensional check on `min`, and in
/// particular to leg B. Only leg A, comparing against the DECLARATION the source
/// actually wrote, can see it. It is a real defect: the same widening in
/// `flagU8` (`if a < b then 1 else 0`) changes the answer at `a = b` outright.
fn mut_widen_ult_to_ule(inst: &mut Inst) -> bool {
    if let Inst::ICmp { op, .. } = inst {
        if *op == ICmpOp::Ult {
            *op = ICmpOp::Ule;
            return true;
        }
    }
    false
}

/// `BinOp::And` -> `BinOp::Or`. The bitwise counterpart of Add->Sub.
fn mut_and_to_or(inst: &mut Inst) -> bool {
    if let Inst::BinOp { op, .. } = inst {
        if *op == BinOp::And {
            *op = BinOp::Or;
            return true;
        }
    }
    false
}

/// Swap the operands of an `ICmp`. `a < b` becomes `b < a`, which flips a `min`
/// into a `max` WITHOUT touching the `Select` — a different route to the same
/// wrong answer, and one the arm-swap operator would miss.
fn mut_swap_icmp_operands(inst: &mut Inst) -> bool {
    if let Inst::ICmp { lhs, rhs, .. } = inst {
        if lhs == rhs {
            return false;
        }
        std::mem::swap(lhs, rhs);
        return true;
    }
    false
}

/// The five the assignment names, plus two cheap neighbours that probe the same
/// machinery from a different side.
const MUTATIONS: &[Mutation] = &[
    Mutation { name: "select-arms-swapped", apply: mut_swap_select_arms },
    Mutation { name: "add-becomes-sub", apply: mut_add_to_sub },
    Mutation { name: "sub-operands-swapped", apply: mut_swap_sub_operands },
    Mutation { name: "constant-shifted-by-one", apply: mut_shift_constant },
    Mutation { name: "ult-widened-to-ule", apply: mut_widen_ult_to_ule },
    Mutation { name: "and-becomes-or", apply: mut_and_to_or },
    Mutation { name: "icmp-operands-swapped", apply: mut_swap_icmp_operands },
];

/// Clone `func` and apply `m` to its FIRST matching instruction.
///
/// `None` means the operator found nothing of its kind. A reported change that
/// leaves the `Function` equal to the original is an ASSERTION FAILURE, not a
/// quiet `None`: that is how a mutation operator silently degrades into a no-op
/// and starts handing out free "caught" verdicts.
fn mutate_first(func: &Function, m: &Mutation) -> Option<Function> {
    let mut out = func.clone();
    let mut applied = false;
    'search: for block in &mut out.blocks {
        for node in &mut block.body {
            if (m.apply)(&mut node.inst) {
                applied = true;
                break 'search;
            }
        }
    }
    if !applied {
        return None;
    }
    assert_ne!(
        out, *func,
        "mutation operator `{}` reported a change but produced an IDENTICAL \
         Function. A no-op mutant scores a free `caught` and proves nothing.",
        m.name
    );
    Some(out)
}

/// One shape, emitted once, with its pristine acceptance already established.
///
/// The constructor IS the control: it panics unless the pristine body both
/// reflects and is accepted by the kernel against its declaration. Every
/// verdict this type returns is therefore a statement about the MUTATION and
/// not about a check that was already broken.
struct Subject<'a> {
    name: &'static str,
    env: &'a Environment,
    declared: Expr,
    pristine: Function,
}

impl<'a> Subject<'a> {
    fn new(island: &'a Island, name: &'static str) -> Self {
        let env = island.env();
        let declared = island.declared(name);
        let pristine = island.emit(name);

        let term = reflect_uint_straight_line(&pristine).unwrap_or_else(|r| {
            panic!(
                "CONTROL FAILED for `{name}`: the PRISTINE emitted body was REFUSED \
                 ({r:?}). Every mutation verdict for this shape would be meaningless."
            )
        });
        assert!(
            kernel_accepts(env, &term, &declared),
            "CONTROL FAILED for `{name}`: the kernel does not accept the PRISTINE \
             reflection. A mutation cannot prove anything under a check that is \
             already red."
        );

        Self { name, env, declared, pristine }
    }

    /// Put an already-corrupted `Function` through exactly the check the
    /// pristine body passed.
    ///
    /// Factored out of [`Subject::verdict`] so that
    /// `the_mutation_harness_can_actually_report_a_survivor` can drive the SAME
    /// decision code with a mutant built by hand. A self-test that reimplemented
    /// this logic would prove nothing about the logic the sweep runs.
    fn verdict_of(&self, corrupt: &Function) -> MutationVerdict {
        assert_ne!(
            *corrupt, self.pristine,
            "`{}`: a mutant equal to the pristine function is not a mutant",
            self.name
        );
        match reflect_uint_straight_line(corrupt) {
            Err(_) => MutationVerdict::CaughtByRefusal,
            Ok(term) => {
                if kernel_accepts(self.env, &term, &self.declared) {
                    MutationVerdict::Survived
                } else {
                    MutationVerdict::CaughtByKernel
                }
            }
        }
    }

    /// Corrupt, re-check, and report.
    fn verdict(&self, m: &Mutation) -> MutationVerdict {
        let Some(corrupt) = mutate_first(&self.pristine, m) else {
            return MutationVerdict::NotApplicable;
        };
        self.verdict_of(&corrupt)
    }

    /// The assertion the dedicated tests make: this mutation must APPLY, and
    /// must then be CAUGHT.
    fn must_catch(&self, m: &Mutation) -> MutationVerdict {
        let v = self.verdict(m);
        assert_ne!(
            v,
            MutationVerdict::NotApplicable,
            "mutation `{}` found nothing to corrupt in `{}` — this test is \
             pointed at the wrong shape and is measuring nothing",
            m.name,
            self.name
        );
        assert!(
            v.caught(),
            "SURVIVING MUTANT — `{}` applied to `{}`.\n  \
             The emitted TrustIR was corrupted at ONE instruction, so it no longer \
             implements the Clean declaration `{}`, and the check passed it anyway.\n  \
             This is a HOLE IN THE EMITTER CHECK. Do not relax the assertion; report it.",
            m.name,
            self.name,
            self.name
        );
        eprintln!("  {:24} {:22} {}", self.name, m.name, v.tag());
        v
    }
}

fn mutation(name: &str) -> &'static Mutation {
    MUTATIONS
        .iter()
        .find(|m| m.name == name)
        .unwrap_or_else(|| panic!("no mutation operator named `{name}`"))
}

// ---------------------------------------------------------------------------
// The five named mutations, one test each
// ---------------------------------------------------------------------------

/// Swapping the arms of a `Select` turns `min` into `max` and `max` into `min`,
/// and turns `if a < b then 1 else 0` into its negation.
#[test]
fn mutation_swapping_select_arms_is_caught() {
    let island = Island::check(SOURCE);
    eprintln!("select-arms-swapped:");
    for shape in [
        "minU8", "maxU8", "leU8", "eqU8", "leLitU8", "eqLitU8", "flagU8", "minU16", "minU32",
        "minU64",
    ] {
        Subject::new(&island, shape).must_catch(mutation("select-arms-swapped"));
    }
}

/// `BinOp::Add` emitted where the source says `+` is the canonical wrong-opcode
/// bug, and the one the cancelling round trip in leg B is staged against.
#[test]
fn mutation_add_to_sub_is_caught() {
    let island = Island::check(SOURCE);
    eprintln!("add-becomes-sub:");
    for shape in ["addU8", "litU8", "nestU8", "deepU8", "triU8", "addU16", "addU32", "addU64"] {
        Subject::new(&island, shape).must_catch(mutation("add-becomes-sub"));
    }
}

/// Operand order on a NON-COMMUTATIVE opcode. `b - a` is not `a - b`, and this
/// is the mutant a reflector with a de Bruijn off-by-one would let through.
#[test]
fn mutation_swapping_sub_operands_is_caught() {
    let island = Island::check(SOURCE);
    eprintln!("sub-operands-swapped:");
    for shape in ["subU8", "nestU8", "deepU8", "nestU16", "nestU32", "nestU64"] {
        Subject::new(&island, shape).must_catch(mutation("sub-operands-swapped"));
    }
}

/// An integer literal off by one — `a + 8` where the source says `a + 7`, and
/// `201` where the source says `200`.
#[test]
fn mutation_shifting_a_constant_is_caught() {
    let island = Island::check(SOURCE);
    eprintln!("constant-shifted-by-one:");
    for shape in ["litU8", "litOnlyU8", "deepU8", "leLitU8", "eqLitU8", "flagU8", "nestU16"] {
        Subject::new(&island, shape).must_catch(mutation("constant-shifted-by-one"));
    }
}

/// Widening `<` to `<=`.
///
/// The one worth reading the comment for. On `min`/`max` this mutant is
/// EXTENSIONALLY INVISIBLE — `if a < b then a else b` and `if a <= b then a
/// else b` are the same function, differing only at `a = b` where both arms
/// coincide — so no amount of executing the IR can catch it, and leg B by
/// construction cannot. It is caught here only because leg A compares against
/// the DECLARATION, which records which relation the source wrote. On `flagU8`
/// the same widening changes the answer at `a = b`, so it is a real defect and
/// not a notational quibble.
#[test]
fn mutation_widening_ult_to_ule_is_caught() {
    let island = Island::check(SOURCE);
    eprintln!("ult-widened-to-ule:");
    for shape in ["minU8", "maxU8", "flagU8", "minU16", "minU32", "minU64"] {
        Subject::new(&island, shape).must_catch(mutation("ult-widened-to-ule"));
    }

    // The measurement behind the paragraph above: on `min` this mutant is
    // extensionally invisible, so leg A is carrying it alone.
    let subject = Subject::new(&island, "minU8");
    let corrupt = mutate_first(&subject.pristine, mutation("ult-widened-to-ule"))
        .expect("minU8 contains an Ult");
    let interpreter = Interpreter::new();
    for (a, b) in [(3u64, 5u64), (5, 3), (4, 4), (200, 100), (0, 255)] {
        let run = |f: &Function| {
            let out = interpreter
                .execute_function(
                    f,
                    [
                        InterpretValue::int(Ty::U8, i128::from(a)).expect("in range"),
                        InterpretValue::int(Ty::U8, i128::from(b)).expect("in range"),
                    ],
                )
                .expect("interprets");
            out.returns[0].as_int().expect("int").as_unsigned()
        };
        assert_eq!(
            run(&subject.pristine),
            run(&corrupt),
            "if `min` under `<` and under `<=` EVER disagree at ({a}, {b}), this \
             comment is wrong and leg B could have caught the widening too"
        );
    }
}

// ---------------------------------------------------------------------------
// The full matrix, and the survivor report
// ---------------------------------------------------------------------------

/// Every operator against every covered shape.
///
/// The per-mutation tests above are pointed at shapes chosen to make each
/// operator bite. This one is pointed at everything, because the survivor this
/// file is looking for is by definition in the cell nobody thought to check.
/// It collects the WHOLE matrix before asserting, so one survivor does not
/// hide the next.
#[test]
fn mutation_sweep_over_every_covered_shape() {
    let island = Island::check(SOURCE);

    let mut rows: Vec<(&'static str, &'static str, MutationVerdict)> = Vec::new();
    for shape in SHAPES {
        let subject = Subject::new(&island, shape.name);
        for m in MUTATIONS {
            rows.push((shape.name, m.name, subject.verdict(m)));
        }
    }

    let applied: Vec<_> =
        rows.iter().filter(|(_, _, v)| *v != MutationVerdict::NotApplicable).collect();
    let survivors: Vec<_> =
        rows.iter().filter(|(_, _, v)| *v == MutationVerdict::Survived).collect();

    eprintln!("\n=== MUTATION SWEEP ===");
    eprintln!(
        "{} shapes x {} operators = {} cells; {} applied, {} n/a",
        SHAPES.len(),
        MUTATIONS.len(),
        rows.len(),
        applied.len(),
        rows.len() - applied.len()
    );
    // Per operator: how many cells it reached, and — the distinction that
    // matters when reading this — how it was caught. A KERNEL rejection is the
    // strong outcome: the mutant was fully spelled as a Clean term and the
    // kernel said it is not the declaration. A REFUSAL is weaker evidence: the
    // reflector declined, which is a correct answer but could in principle be
    // for a reason incidental to the corruption. Both are printed so nobody has
    // to take the aggregate on faith.
    for m in MUTATIONS {
        let cells: Vec<_> = rows.iter().filter(|(_, n, _)| *n == m.name).collect();
        let count = |want: MutationVerdict| cells.iter().filter(|(_, _, v)| *v == want).count();
        let applied_here =
            cells.iter().filter(|(_, _, v)| *v != MutationVerdict::NotApplicable).count();
        eprintln!(
            "  {:24} applied {:3}  by-kernel {:3}  by-refusal {:3}  SURVIVED {}",
            m.name,
            applied_here,
            count(MutationVerdict::CaughtByKernel),
            count(MutationVerdict::CaughtByRefusal),
            count(MutationVerdict::Survived),
        );
    }

    // NON-VACUITY OF THE SWEEP ITSELF. The floor that matters is per-operator,
    // not aggregate: an operator that reached ZERO cells contributed no
    // evidence, and an aggregate count would hide it behind the operators that
    // did fire. (`and-becomes-or` reaches exactly one cell, because `andU8` is
    // the only covered shape with a `BinOp::And` — that is a fact about the
    // corpus, and the assertion below is what will notice if it ever silently
    // becomes zero.)
    for m in MUTATIONS {
        let applied_here = rows
            .iter()
            .filter(|(_, n, v)| *n == m.name && *v != MutationVerdict::NotApplicable)
            .count();
        assert!(
            applied_here > 0,
            "mutation operator `{}` reached NO covered shape. It contributed no \
             evidence, and a sweep that reports it as `0 survived` is lying by \
             omission — point it at a shape it can corrupt, or delete it.",
            m.name
        );
    }
    assert!(
        applied.len() >= 40,
        "the sweep applied only {} mutations across {} shapes — too few to be \
         evidence of anything",
        applied.len(),
        SHAPES.len()
    );

    if !survivors.is_empty() {
        let list = survivors
            .iter()
            .map(|(s, m, _)| format!("    {m} @ {s}"))
            .collect::<Vec<_>>()
            .join("\n");
        panic!(
            "SURVIVING MUTANTS ({} of {} applied) — the check is VACUOUS for these \
             cells. Each line names a one-instruction corruption of the emitted \
             TrustIR that the kernel accepted against a declaration it does not \
             implement:\n{list}",
            survivors.len(),
            applied.len()
        );
    }
    eprintln!("no survivors\n");
}

/// THE POSITIVE CONTROL FOR THE SWEEP ITSELF.
///
/// `mutation_sweep_over_every_covered_shape` reports "no survivors". That claim
/// is worth exactly as much as the harness's ability to say the opposite — a
/// `verdict_of` that returned `CaughtByKernel` unconditionally would print the
/// same clean sweep, and every mutation test in this section would pass. So the
/// `Survived` branch is REACHED here on purpose, through the same code path.
///
/// The mutant chosen is a genuine NO-OP: bind the returned value through an
/// identity `Inst::Copy` and return the copy. The `Function` is structurally
/// different (an extra instruction, a different returned `ValueId`), the
/// reflector denotes a `Copy` by its operand, so the term is unchanged and the
/// kernel accepts it.
///
/// THIS IS NOT A FINDING. A no-op mutant SHOULD survive — an emitter that binds
/// a value through a copy has emitted a correct body, and a check that rejected
/// it would be rejecting correct code. What it establishes is narrower and is
/// the only thing being claimed: `MutationVerdict::Survived` is reachable, so
/// the 45 `caught` verdicts are decisions and not a constant.
#[test]
fn the_mutation_harness_can_actually_report_a_survivor() {
    use trust_ir::InstrNode;

    let island = Island::check(SOURCE);
    let subject = Subject::new(&island, "addU8");

    // Read the returned value and pick a fresh SSA name, before taking a
    // mutable borrow.
    let (returned, fresh) = {
        let block = &subject.pristine.blocks[0];
        let Some(Inst::Return { values }) = block.body.last().map(|n| &n.inst) else {
            panic!("addU8's entry block must end in Return");
        };
        let [only] = values.as_slice() else {
            panic!("addU8 must return exactly one value");
        };
        let next = block
            .params
            .iter()
            .map(|(v, _)| v.index())
            .chain(block.body.iter().flat_map(|n| n.results.iter().map(|v| v.index())))
            .max()
            .expect("addU8 defines at least one value")
            + 1;
        (*only, ValueId::new(next))
    };

    let mut benign = subject.pristine.clone();
    let block = &mut benign.blocks[0];
    block.body.pop().expect("the terminator just read back");
    block
        .body
        .push(InstrNode::new(Inst::Copy { ty: Ty::U8, operand: returned }).with_result(fresh));
    block.body.push(InstrNode::new(Inst::Return { values: vec![fresh] }));

    assert_eq!(
        subject.verdict_of(&benign),
        MutationVerdict::Survived,
        "THE SWEEP IS UNFALSIFIABLE. A no-op mutant — the returned value bound \
         through an identity `Inst::Copy` — was not reported as surviving, which \
         means `verdict_of` cannot produce that verdict and the sweep's \
         `no survivors` line is not a measurement."
    );
}

/// THE LIMIT OF LEG B, measured rather than asserted.
///
/// It is tempting to read the differential leg as a second, independent check on
/// the EMITTER. It is not, and this is the measurement that says so: mutating the
/// IR moves the interpreter's answer and the reflected term TOGETHER, because
/// both are functions of the same corrupted `Function`. Leg B therefore stays
/// green on a mutant that computes something else entirely.
///
/// Leg B anchors the REFLECTOR'S OPCODE MAPPING against the IR's operational
/// semantics — that is a real job, and the staged cancellation test above shows
/// it doing it. But every emitter mutation in this section is caught by leg A
/// alone. Do not delete leg A on the grounds that leg B "also executes the code".
#[test]
fn the_differential_leg_is_blind_to_an_emitter_mutation() {
    const MUTANT_POINTS: &[&[u64]] = &[&[3, 5], &[200, 100], &[255, 1]];
    const MUTANT_SHAPE: Shape =
        Shape { name: "addU8 with Add mutated to Sub", width: 8, points: MUTANT_POINTS };

    let island = Island::check(SOURCE);
    let subject = Subject::new(&island, "addU8");
    let corrupt = mutate_first(&subject.pristine, mutation("add-becomes-sub"))
        .expect("addU8 contains an Add");
    let term = reflect_uint_straight_line(&corrupt).expect("the mutant still reflects");

    // LEG A CATCHES IT.
    assert!(
        !kernel_accepts(subject.env, &term, &subject.declared),
        "leg A must reject an emitted body that computes `a - b` for a \
         declaration of `a + b`"
    );

    // LEG B DOES NOT. It cannot: both sides of its comparison were mutated.
    // If this ever starts panicking, leg B became stronger than documented and
    // the doc comment above needs rewriting — it is not a regression.
    differential_leg(subject.env, &MUTANT_SHAPE, &corrupt, &term);
}
