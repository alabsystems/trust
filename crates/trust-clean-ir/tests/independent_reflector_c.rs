// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// AN INDEPENDENT TrustIR -> Clean REFLECTOR.
//
// WHY THIS FILE EXISTS, AND WHY IT WAS WRITTEN BLIND.
// `trust-clean-ir` turns a sealed `CleanOriginPlan` into a `trust_ir::Function`.
// The question this file answers is the converse one: *does that Function still
// denote the declaration it came from?* The check is a round trip -- reflect the
// IR back into a Clean term and ask the CIC kernel whether the result is
// definitionally equal to the declaration's own value.
//
// A round trip is only evidence if the two directions are independent. If the
// reflector is written by someone who knows how the emitter spells things, an
// emitter bug and a matching reflector bug cancel: the kernel is handed two
// wrong terms that agree, says yes, and blesses a body that computes something
// else. So this reflector was authored WITHOUT reading:
//
//   * `crates/trust-clean-ir/src/**`                       (the emitter)
//   * `crates/trust-clean-ir/tests/symbolic_reflection.rs`  (a co-authored reflector)
//   * `crates/trust-clean-origin/src/reflect.rs`            (the MIR-side reflector)
//
// What it WAS written from: the TrustIR data types
// (`first-party/trust-ir/crates/trust-ir/src/{inst,ty,constant,value}.rs`), the
// Clean kernel's `Expr`/`Level`/`TypeChecker` API, and direct measurement of what
// Clean's own elaborator produces for the surface programs under test. The
// emitter was used only as a black box: `plan_clean_origin_body` +
// `emit_clean_origin_function` supply the `Function`; its source was never read.
//
// THE METHOD: A DENOTATIONAL SEMANTICS, THEN ITS CLEAN IMAGE.
// Rather than pattern-matching IR shapes onto Clean shapes, the reflector gives
// the IR subset a semantics and then writes that semantics down as a Clean term.
//
//   Domain.  For an unsigned machine carrier of width w, the semantic domain is
//            the Clean type `UIntw` -- the total, wrapping w-bit carrier. There
//            is no bottom and no partiality in the domain, which is exactly why
//            the partial operations (`udiv`, `urem`, `load`, `call`) are refused
//            rather than approximated: they would need one.
//
//   States.  A straight-line block is a chain of pure definitions, so an
//            environment `rho : ValueId -> Denotation` suffices; no store, no
//            continuation, no fixpoint.
//
//   Values.  `Denotation` has two constructors because the IR has two kinds of
//            SSA value here:
//              Value(t)              -- t : UIntw, the meaning of a carrier value
//              Decision { prop, inst } -- the meaning of a comparison result: a
//                                       PROPOSITION together with a proof that
//                                       it is decidable.
//            A comparison is NOT given a `Bool` meaning. `ICmp` only ever feeds
//            `Select` in this fragment, and `Select`'s meaning is a mathematical
//            conditional; carrying the proposition (rather than `decide P`) is
//            both the more faithful reading and the one the kernel can compare
//            against Clean's `ite`, whose eliminator is the `Decidable` instance.
//            A `Decision` that reaches a value position, or a `Value` that
//            reaches a condition position, is a refusal -- never a coercion.
//
//   Clauses. Written out at each `sem_*` function below. `sem_binop` is where
//            wrapping arithmetic is pinned to `UIntw.add/sub/mul/land/lor`;
//            `sem_icmp` to `LT.lt`/`LE.le`/`Eq` at the carrier's own order;
//            `sem_select` to `ite`.
//
//   Sharing. An SSA value used twice is SUBSTITUTED, not let-bound. That step is
//            valid only because every accepted opcode is pure AND total: no
//            division, no memory, no calls, no traps. It is listed here as a
//            proof obligation of the design, not as an implementation detail --
//            admitting any partial opcode later would invalidate it.
//
// THE SPELLING IS DELIBERATELY NOT THE ELABORATOR'S.
// Clean elaborates `a + b` to `HAdd.hAdd [0,0,0] T T T instHAddT a b`. This
// reflector emits `UIntw.add a b`. `is_def_eq` closes the gap by unfolding the
// instance, and the difference is the point: a reflector that reproduced the
// elaborator's exact spine would be a pretty-printer for the declaration, and
// would pass even if it never looked at the IR. `test_non_vacuity_*` below make
// that failure mode impossible to hide.
//
// WHAT IS COVERED, AND WHY EXACTLY THAT SET.
// The acceptance rule is: an opcode is accepted only if it is DEMONSTRATED,
// end-to-end in this file, to round-trip against a real kernel declaration.
// There is no opcode this reflector will accept that is not exercised by a test
// here. Everything else is refused BY NAME with the reason. See
// `Refusal` and the `test_refuses_*` battery.

#![allow(clippy::items_after_test_module)]

use clean_kernel::expr::BinderInfo;
use clean_kernel::{Environment, Expr, Level, Name};
use trust_ir::{BinOp, Constant, Function, ICmpOp, Inst, Ty, ValueId};

// ═══════════════════════════════════════════════════════════════════════════
// 1. THE CARRIER
// ═══════════════════════════════════════════════════════════════════════════

/// The four unsigned machine carriers this reflector gives a semantics to.
///
/// Deliberately NOT `Ty`: making the carrier a separate, closed type is what
/// forces every entry point to go through [`Carrier::of_ty`], so a signed,
/// floating, boolean, pointer or aggregate type cannot reach the semantic
/// clauses at all.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Carrier {
    U8,
    U16,
    U32,
    U64,
}

impl Carrier {
    fn of_ty(ty: &Ty) -> Result<Self, Refusal> {
        match ty {
            Ty::U8 => Ok(Carrier::U8),
            Ty::U16 => Ok(Carrier::U16),
            Ty::U32 => Ok(Carrier::U32),
            Ty::U64 => Ok(Carrier::U64),
            other => Err(Refusal::NotAnUnsignedMachineCarrier { ty: format!("{other:?}") }),
        }
    }

    /// The Clean type this carrier denotes.
    fn clean_type(self) -> Expr {
        Expr::const_str(self.prefix())
    }

    fn prefix(self) -> &'static str {
        match self {
            Carrier::U8 => "UInt8",
            Carrier::U16 => "UInt16",
            Carrier::U32 => "UInt32",
            Carrier::U64 => "UInt64",
        }
    }

    fn width(self) -> u32 {
        match self {
            Carrier::U8 => 8,
            Carrier::U16 => 16,
            Carrier::U32 => 32,
            Carrier::U64 => 64,
        }
    }

    /// The half-open upper bound of the carrier's value set, as `i128`.
    /// `i128` holds `2^64` exactly, so this is lossless for every carrier here.
    fn modulus(self) -> i128 {
        1i128 << self.width()
    }

    /// `UInt8.add`, `UInt16.land`, ... — a member function of the carrier's
    /// own namespace.
    fn member(self, f: &str) -> Expr {
        Expr::const_str(&format!("{}.{f}", self.prefix()))
    }

    /// `instLTUInt8`, `instLEUInt32`, ...
    fn order_instance(self, rel: OrderRel) -> Expr {
        let tag = match rel {
            OrderRel::Lt => "LT",
            OrderRel::Le => "LE",
        };
        Expr::const_str(&format!("inst{tag}{}", self.prefix()))
    }

    /// `instDecidableUInt8Lt`, `instDecidableUInt32Le`, ...
    fn order_decidable(self, rel: OrderRel) -> Expr {
        let tag = match rel {
            OrderRel::Lt => "Lt",
            OrderRel::Le => "Le",
        };
        Expr::const_str(&format!("instDecidable{}{tag}", self.prefix()))
    }

    /// `instDecidableEqUInt8`, ...
    fn eq_decidable(self) -> Expr {
        Expr::const_str(&format!("instDecidableEq{}", self.prefix()))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum OrderRel {
    Lt,
    Le,
}

// ═══════════════════════════════════════════════════════════════════════════
// 2. REFUSALS — the complete list of what this reflector will not spell
// ═══════════════════════════════════════════════════════════════════════════

/// Every way this reflector declines, each naming the construct and the reason.
///
/// A refusal is the SAFE outcome. The unsafe outcome is a term the kernel
/// accepts that does not denote what the IR says, so anything whose Clean image
/// this author could not justify from the IR alone is listed here rather than
/// guessed at.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Refusal {
    // -- shape of the function ------------------------------------------------
    /// More (or fewer) than one basic block. Multi-block control flow needs a
    /// fixpoint or a join semantics; the domain here has neither.
    NotSingleBlock { blocks: usize },
    /// `entry` does not name the only block.
    EntryIsNotTheOnlyBlock,
    /// The block does not end in `Return`.
    BlockDoesNotEndInReturn { last: String },
    /// A terminator appears before the end of the block.
    TerminatorBeforeEndOfBlock { opcode: &'static str, at: usize },
    /// `Return` with other than exactly one value: a Clean `def` denotes one
    /// value, and a multi-value return would need a tuple type this fragment
    /// does not fix.
    ReturnArity { values: usize },
    /// An instruction produced a number of results the semantics does not
    /// expect.
    ResultArity { opcode: &'static str, got: usize },
    /// The same `ValueId` is defined twice. SSA is assumed, and shadowing would
    /// silently change which definition a later use denotes.
    ValueDefinedTwice { value: u32 },
    /// A use with no definition in this block (or a use before its definition).
    UndefinedValue { value: u32 },

    // -- types ----------------------------------------------------------------
    /// A parameter or operand type outside `{U8,U16,U32,U64}`. Covers signed
    /// integers, `Usize`/`Isize` (target-dependent width — not a fixed carrier),
    /// `Char`, floats, `Bool`, pointers, references, and every aggregate.
    NotAnUnsignedMachineCarrier { ty: String },
    /// Two different carriers in one body. Reflecting a mixed-width body needs a
    /// semantics for the casts between them, which this fragment does not give.
    MixedCarrierWidths { first: Carrier, then_: Carrier },

    // -- values ---------------------------------------------------------------
    /// A comparison result reached a position that needs a carrier value.
    ComparisonUsedAsValue { value: u32 },
    /// A carrier value reached the condition position of a `Select`. The IR type
    /// would be `Bool`, which is not a carrier, and a `Bool` condition would need
    /// `cond`/`bif` rather than `ite` — a different Clean head with a different
    /// eliminator. Refused rather than coerced.
    ValueUsedAsCondition { value: u32 },
    /// An integer constant outside the carrier's value set. The IR gives no
    /// wrapping rule for a literal, and `UIntw.ofNat` would silently reduce it
    /// mod 2^w — inventing a value the IR did not state.
    ConstantOutOfCarrierRange { value: i128, carrier: Carrier },
    /// A non-integer constant (bytes, float, bool, aggregate, ...).
    NonIntegerConstant { kind: &'static str },

    // -- opcodes --------------------------------------------------------------
    /// A `BinOp` this reflector does not spell. See [`Refusal::why_binop`].
    UnsupportedBinOp { op: &'static str, why: &'static str },
    /// An `ICmp` this reflector does not spell.
    UnsupportedICmp { op: &'static str, why: &'static str },
    /// An instruction outside the accepted set.
    UnsupportedInst { opcode: &'static str, why: &'static str },
}

impl Refusal {
    /// The reason text for each refused `BinOp`, kept next to the refusal so a
    /// reader can audit the list without reading the matcher.
    fn why_binop(op: BinOp) -> Option<(&'static str, &'static str)> {
        Some(match op {
            BinOp::UDiv | BinOp::URem => (
                "udiv/urem",
                "TrustIR integer division is UNDEFINED on a zero divisor, while Clean's \
                 `UIntw.div`/`UIntw.mod` are total (`x / 0 = 0`). Reflecting the IR op as the \
                 total Clean function would supply a meaning at a point where the IR states \
                 none, so a kernel `yes` would be about a stronger claim than the body makes. \
                 Admitting this needs an IR-visible non-zero-divisor witness AND the sharing \
                 argument in this file's header re-done for a partial op.",
            ),
            BinOp::SDiv | BinOp::SRem => (
                "sdiv/srem",
                "signed division at an unsigned carrier: the operand type says the values are \
                 unsigned, so a signed op is either a producer bug or a bit-pattern \
                 reinterpretation this reflector has no Clean image for.",
            ),
            BinOp::Xor => (
                "xor",
                "spellable in principle as `UIntw.xor`, but no surface program in the emitter's \
                 fragment produces it, so the path could not be demonstrated end to end. This \
                 file accepts only what it exercises.",
            ),
            BinOp::Shl | BinOp::LShr | BinOp::AShr => (
                "shl/lshr/ashr",
                "shift amounts >= the carrier width have a target-defined meaning in the IR and \
                 a total (masking or saturating) meaning in Clean; the two do not agree, and the \
                 IR carries no in-range witness.",
            ),
            BinOp::BAnd | BinOp::BOr | BinOp::BXor => (
                "band/bor/bxor",
                "the boolean 0/1-carrier connectives. Their operands are not machine carriers, \
                 so they are outside this reflector's domain.",
            ),
            BinOp::FAdd
            | BinOp::FSub
            | BinOp::FMul
            | BinOp::FDiv
            | BinOp::FRem
            | BinOp::FMin
            | BinOp::FMax => (
                "floating-point arithmetic",
                "IEEE-754 semantics (rounding mode, NaN payloads, signed zero) is not in this \
                 reflector's domain.",
            ),
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::And | BinOp::Or => return None,
        })
    }

    /// The reason text for each refused `ICmp`.
    fn why_icmp(op: ICmpOp) -> Option<(&'static str, &'static str)> {
        Some(match op {
            ICmpOp::Ne => (
                "ne",
                "the negation of an equality. `Ne` is `Not (a = b)`; deciding it needs an \
                 instance this reflector would have to synthesize, and no surface program in the \
                 fragment produces it, so it could not be demonstrated.",
            ),
            ICmpOp::Ugt | ICmpOp::Uge => (
                "ugt/uge",
                "mathematically just `Ult`/`Ule` with the operands swapped, but the emitter's \
                 fragment never produces them (`>` and `>=` are refused upstream), so the swap \
                 could not be demonstrated end to end. Accepting an unexercised path is exactly \
                 the risk this file exists to avoid.",
            ),
            ICmpOp::Slt | ICmpOp::Sle | ICmpOp::Sgt | ICmpOp::Sge => (
                "signed comparison at an unsigned carrier",
                "a signed compare reads the same bits under a different order. `LT.le`/`LT.lt` at \
                 `UIntw` is the UNSIGNED order, so emitting it would state the wrong proposition \
                 for exactly the operands where the two orders disagree (the high half).",
            ),
            ICmpOp::Eq | ICmpOp::Ult | ICmpOp::Ule => return None,
        })
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// 3. THE SEMANTIC DOMAIN
// ═══════════════════════════════════════════════════════════════════════════

/// The meaning of one SSA value.
///
/// The two constructors are the two kinds of thing a value in this fragment can
/// be. Keeping them apart in the TYPE is what makes "a comparison silently used
/// as a number" a refusal instead of a mis-typed term the kernel then has to
/// catch.
#[derive(Debug, Clone)]
enum Denotation {
    /// A term of the carrier type.
    Value(Expr),
    /// A decidable proposition: the proposition itself, plus the `Decidable`
    /// instance that eliminates it.
    Decision { prop: Expr, inst: Expr },
}

impl Denotation {
    fn expect_value(&self, id: ValueId) -> Result<Expr, Refusal> {
        match self {
            Denotation::Value(e) => Ok(e.clone()),
            Denotation::Decision { .. } => {
                Err(Refusal::ComparisonUsedAsValue { value: id.index() })
            }
        }
    }

    fn expect_decision(&self, id: ValueId) -> Result<(Expr, Expr), Refusal> {
        match self {
            Denotation::Decision { prop, inst } => Ok((prop.clone(), inst.clone())),
            Denotation::Value(_) => Err(Refusal::ValueUsedAsCondition { value: id.index() }),
        }
    }
}

/// `rho`: the environment mapping already-defined SSA values to their meanings.
#[derive(Default)]
struct Rho {
    slots: Vec<(ValueId, Denotation)>,
}

impl Rho {
    fn define(&mut self, id: ValueId, d: Denotation) -> Result<(), Refusal> {
        if self.slots.iter().any(|(v, _)| *v == id) {
            return Err(Refusal::ValueDefinedTwice { value: id.index() });
        }
        self.slots.push((id, d));
        Ok(())
    }

    fn lookup(&self, id: ValueId) -> Result<&Denotation, Refusal> {
        self.slots
            .iter()
            .find(|(v, _)| *v == id)
            .map(|(_, d)| d)
            .ok_or(Refusal::UndefinedValue { value: id.index() })
    }

    fn value(&self, id: ValueId) -> Result<Expr, Refusal> {
        self.lookup(id)?.expect_value(id)
    }
}

/// Accumulates the single carrier the whole body must be at.
struct WidthWitness(Option<Carrier>);

impl WidthWitness {
    fn observe(&mut self, ty: &Ty) -> Result<Carrier, Refusal> {
        let c = Carrier::of_ty(ty)?;
        match self.0 {
            None => {
                self.0 = Some(c);
                Ok(c)
            }
            Some(first) if first == c => Ok(c),
            Some(first) => Err(Refusal::MixedCarrierWidths { first, then_: c }),
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// 4. THE SEMANTIC CLAUSES
// ═══════════════════════════════════════════════════════════════════════════

/// `Sort 1` — the universe of `UIntw`, and therefore `ite`'s level argument.
fn type0() -> Vec<Level> {
    vec![Level::succ(Level::Zero)]
}

/// ⟦ Const { ty = T, value = k } ⟧ = the element of `T` whose value is `k`.
///
/// Spelled `T.ofNat k`. `k` is required to be in `0 .. 2^w` FIRST: `ofNat`
/// reduces mod `2^w`, so an out-of-range literal would quietly denote a
/// different number than the IR wrote.
fn sem_const(carrier: Carrier, value: &Constant) -> Result<Expr, Refusal> {
    let k = match value {
        Constant::Int(k) => *k,
        Constant::U128(_) => {
            return Err(Refusal::ConstantOutOfCarrierRange { value: i128::MAX, carrier });
        }
        Constant::Bool(_) => return Err(Refusal::NonIntegerConstant { kind: "bool" }),
        Constant::Float(_) => return Err(Refusal::NonIntegerConstant { kind: "float" }),
        Constant::Bytes { .. } => return Err(Refusal::NonIntegerConstant { kind: "bytes" }),
        other => {
            return Err(Refusal::NonIntegerConstant { kind: constant_kind_name(other) });
        }
    };
    if k < 0 || k >= carrier.modulus() {
        return Err(Refusal::ConstantOutOfCarrierRange { value: k, carrier });
    }
    // `k` is now provably in `0 .. 2^w` with `w <= 64`, so the cast is exact.
    let n = u64::try_from(k).expect("range-checked above");
    Ok(Expr::app(carrier.member("ofNat"), Expr::nat_lit(n)))
}

fn constant_kind_name(c: &Constant) -> &'static str {
    match c {
        Constant::Int(_) => "int",
        Constant::U128(_) => "u128",
        Constant::Bytes { .. } => "bytes",
        Constant::Float(_) => "float",
        Constant::Bool(_) => "bool",
        Constant::Aggregate(_) => "aggregate",
        Constant::Array(_) => "array",
        Constant::Vector(_) => "vector",
        Constant::Sequence(_) => "sequence",
        Constant::Set(_) => "set",
        _ => "other-constant",
    }
}

/// ⟦ BinOp { op, ty = T, lhs, rhs } ⟧ = `T.<f> ⟦lhs⟧ ⟦rhs⟧`.
///
/// The five accepted operations are exactly the ones that are TOTAL functions
/// `T -> T -> T` in both languages, with the same graph:
///
///   Add -> `T.add`   wrapping addition mod 2^w
///   Sub -> `T.sub`   wrapping subtraction mod 2^w
///   Mul -> `T.mul`   wrapping multiplication mod 2^w
///   And -> `T.land`  bitwise conjunction  (the IR's `And` at an INTEGER carrier
///                    is the bitwise reading; its boolean reading is `BAnd`,
///                    which is refused)
///   Or  -> `T.lor`   bitwise disjunction
fn sem_binop(carrier: Carrier, op: BinOp, lhs: Expr, rhs: Expr) -> Result<Expr, Refusal> {
    if let Some((op_name, why)) = Refusal::why_binop(op) {
        return Err(Refusal::UnsupportedBinOp { op: op_name, why });
    }
    let f = match op {
        BinOp::Add => "add",
        BinOp::Sub => "sub",
        BinOp::Mul => "mul",
        BinOp::And => "land",
        BinOp::Or => "lor",
        // Unreachable: `why_binop` returns `None` for exactly the five above.
        _ => unreachable!("why_binop admits exactly add/sub/mul/and/or"),
    };
    Ok(Expr::apps(carrier.member(f), [lhs, rhs]))
}

/// ⟦ ICmp { op, ty = T, lhs, rhs } ⟧ = a decidable PROPOSITION about `T`.
///
///   Ult -> `@LT.lt T instLT ⟦lhs⟧ ⟦rhs⟧`, decided by `instDecidableTLt`
///   Ule -> `@LE.le T instLE ⟦lhs⟧ ⟦rhs⟧`, decided by `instDecidableTLe`
///   Eq  -> `@Eq T ⟦lhs⟧ ⟦rhs⟧`,           decided by `instDecidableEqT`
///
/// `<` and `<=` at `UIntw` ARE the unsigned orders, which is why the unsigned
/// IR comparisons map onto them directly and the signed ones are refused.
///
/// KNOWN INFORMATION LOSS AT `Eq`, measured and demonstrated in
/// `test_finding_icmp_eq_is_not_injective_into_clean`. Clean's `if a = b`
/// elaborates to `ite (@Eq T a b) ..` while `if a == b` elaborates to
/// `ite (BEq.beq a b = true) ..`. The two propositions are provably equivalent
/// but NOT definitionally equal, and the emitter maps both to the same
/// `ICmp Eq`. No IR-only reflector can therefore be `is_def_eq` to both. This
/// one emits the canonical `@Eq T a b`; a `==`-spelled declaration is a FALSE
/// NEGATIVE (the kernel says no, nothing is blessed), never a false accept.
fn sem_icmp(carrier: Carrier, op: ICmpOp, lhs: Expr, rhs: Expr) -> Result<Denotation, Refusal> {
    if let Some((op_name, why)) = Refusal::why_icmp(op) {
        return Err(Refusal::UnsupportedICmp { op: op_name, why });
    }
    let ty = carrier.clean_type();
    Ok(match op {
        ICmpOp::Ult | ICmpOp::Ule => {
            let (rel, head) =
                if op == ICmpOp::Ult { (OrderRel::Lt, "LT.lt") } else { (OrderRel::Le, "LE.le") };
            Denotation::Decision {
                prop: Expr::apps(
                    Expr::const_str_levels(head, vec![Level::Zero]),
                    [ty, carrier.order_instance(rel), lhs.clone(), rhs.clone()],
                ),
                inst: Expr::apps(carrier.order_decidable(rel), [lhs, rhs]),
            }
        }
        ICmpOp::Eq => Denotation::Decision {
            prop: Expr::apps(Expr::const_str_levels("Eq", type0()), [ty, lhs.clone(), rhs.clone()]),
            inst: Expr::apps(carrier.eq_decidable(), [lhs, rhs]),
        },
        // Unreachable: `why_icmp` returns `None` for exactly the three above.
        _ => unreachable!("why_icmp admits exactly ult/ule/eq"),
    })
}

/// ⟦ Select { ty = T, cond, then_val, else_val } ⟧ = the mathematical
/// conditional `if P then ⟦then⟧ else ⟦else⟧`, spelled `@ite T P inst t e`.
///
/// `cond` MUST already denote a `Decision`. It is not `decide`d down to a `Bool`
/// and then eliminated with `cond`/`bif`: for a symbolic argument the instance
/// does not reduce to a constructor, so `bif (decide P) t e` and `ite P t e` are
/// not definitionally equal, and the kernel would reject a correct reflection.
/// Carrying the proposition all the way to the conditional avoids the detour.
fn sem_select(carrier: Carrier, prop: Expr, inst: Expr, t: Expr, e: Expr) -> Expr {
    Expr::apps(Expr::const_str_levels("ite", type0()), [carrier.clean_type(), prop, inst, t, e])
}

// ═══════════════════════════════════════════════════════════════════════════
// 5. THE REFLECTOR
// ═══════════════════════════════════════════════════════════════════════════

/// Rebuild `f` as a closed Clean term: one `Lam` binder per block parameter, in
/// declaration order, over the meaning of the block's returned value.
///
/// de Bruijn: the last parameter is the innermost binder, so parameter `i` of
/// `n` is `BVar(n - 1 - i)`. No clause below introduces a binder, so no index in
/// a sub-term is ever shifted — the whole body is built under exactly the `n`
/// binders the parameters supply.
fn reflect_straight_line_uint_function(f: &Function) -> Result<Expr, Refusal> {
    // ---- shape -------------------------------------------------------------
    if f.blocks.len() != 1 {
        return Err(Refusal::NotSingleBlock { blocks: f.blocks.len() });
    }
    let block = &f.blocks[0];
    if f.entry != block.id {
        return Err(Refusal::EntryIsNotTheOnlyBlock);
    }

    let mut width = WidthWitness(None);
    let mut rho = Rho::default();

    // ---- parameters --------------------------------------------------------
    let n = block.params.len();
    let mut binder_types = Vec::with_capacity(n);
    for (i, (id, ty)) in block.params.iter().enumerate() {
        let carrier = width.observe(ty)?;
        binder_types.push(carrier.clean_type());
        let index = u32::try_from(n - 1 - i).expect("parameter count fits in u32");
        rho.define(*id, Denotation::Value(Expr::bvar(index)))?;
    }

    // ---- the straight line -------------------------------------------------
    let Some((terminator, straight)) = block.body.split_last() else {
        return Err(Refusal::BlockDoesNotEndInReturn { last: "<empty block>".to_owned() });
    };

    for (at, node) in straight.iter().enumerate() {
        if let Some(opcode) = terminator_opcode(&node.inst) {
            return Err(Refusal::TerminatorBeforeEndOfBlock { opcode, at });
        }
        let (id, denot) = sem_instruction(&node.inst, &node.results, &rho, &mut width)?;
        rho.define(id, denot)?;
    }

    // ---- the returned value ------------------------------------------------
    let Inst::Return { values } = &terminator.inst else {
        return Err(Refusal::BlockDoesNotEndInReturn {
            last: opcode_name(&terminator.inst).to_owned(),
        });
    };
    if values.len() != 1 {
        return Err(Refusal::ReturnArity { values: values.len() });
    }
    let body = rho.value(values[0])?;

    // ---- close over the parameters ----------------------------------------
    let mut term = body;
    for ty in binder_types.into_iter().rev() {
        term = Expr::lam(BinderInfo::Default, ty, term);
    }
    Ok(term)
}

/// One non-terminator instruction: its result id and its meaning.
fn sem_instruction(
    inst: &Inst,
    results: &[ValueId],
    rho: &Rho,
    width: &mut WidthWitness,
) -> Result<(ValueId, Denotation), Refusal> {
    let one_result = |opcode: &'static str| -> Result<ValueId, Refusal> {
        match results {
            [id] => Ok(*id),
            other => Err(Refusal::ResultArity { opcode, got: other.len() }),
        }
    };

    match inst {
        Inst::Const { ty, value } => {
            let carrier = width.observe(ty)?;
            let id = one_result("const")?;
            Ok((id, Denotation::Value(sem_const(carrier, value)?)))
        }
        Inst::BinOp { op, ty, lhs, rhs } => {
            let carrier = width.observe(ty)?;
            let id = one_result("binop")?;
            let l = rho.value(*lhs)?;
            let r = rho.value(*rhs)?;
            Ok((id, Denotation::Value(sem_binop(carrier, *op, l, r)?)))
        }
        Inst::ICmp { op, ty, lhs, rhs } => {
            let carrier = width.observe(ty)?;
            let id = one_result("icmp")?;
            let l = rho.value(*lhs)?;
            let r = rho.value(*rhs)?;
            Ok((id, sem_icmp(carrier, *op, l, r)?))
        }
        Inst::Select { ty, cond, then_val, else_val } => {
            let carrier = width.observe(ty)?;
            let id = one_result("select")?;
            let (prop, inst_expr) = rho.lookup(*cond)?.expect_decision(*cond)?;
            let t = rho.value(*then_val)?;
            let e = rho.value(*else_val)?;
            Ok((id, Denotation::Value(sem_select(carrier, prop, inst_expr, t, e))))
        }
        other => Err(Refusal::UnsupportedInst {
            opcode: opcode_name(other),
            why: unsupported_inst_reason(other),
        }),
    }
}

fn terminator_opcode(inst: &Inst) -> Option<&'static str> {
    match inst {
        Inst::Return { .. } => Some("return"),
        Inst::Br { .. } => Some("br"),
        Inst::CondBr { .. } => Some("condbr"),
        Inst::Switch { .. } => Some("switch"),
        Inst::Unreachable => Some("unreachable"),
        _ => None,
    }
}

fn opcode_name(inst: &Inst) -> &'static str {
    match inst {
        Inst::BinOp { .. } => "binop",
        Inst::UnOp { .. } => "unop",
        Inst::Overflow { .. } => "overflow",
        Inst::ICmp { .. } => "icmp",
        Inst::FCmp { .. } => "fcmp",
        Inst::Cast { .. } => "cast",
        Inst::Load { .. } => "load",
        Inst::Store { .. } => "store",
        Inst::Alloca { .. } => "alloca",
        Inst::HeapAlloc { .. } => "heapalloc",
        Inst::GEP { .. } => "gep",
        Inst::Call { .. } => "call",
        Inst::CallIndirect { .. } => "callindirect",
        Inst::Return { .. } => "return",
        Inst::Br { .. } => "br",
        Inst::CondBr { .. } => "condbr",
        Inst::Switch { .. } => "switch",
        Inst::Const { .. } => "const",
        Inst::Select { .. } => "select",
        Inst::Copy { .. } => "copy",
        Inst::Undef { .. } => "undef",
        Inst::Assume { .. } => "assume",
        Inst::Assert { .. } => "assert",
        Inst::Unreachable => "unreachable",
        Inst::ExtractField { .. } => "extractfield",
        Inst::InsertField { .. } => "insertfield",
        Inst::ExtractElement { .. } => "extractelement",
        Inst::InsertElement { .. } => "insertelement",
        _ => "other-instruction",
    }
}

fn unsupported_inst_reason(inst: &Inst) -> &'static str {
    match inst {
        Inst::Copy { .. } => {
            "the identity on the denotation, and therefore trivially spellable — but no surface \
             program in the emitter's fragment produces it, so this file does not accept an \
             unexercised path."
        }
        Inst::Cast { .. } => {
            "a cast changes the carrier, and this fragment fixes ONE carrier for the whole body. \
             Truncation and zero/sign extension each need their own Clean image and their own \
             agreement argument."
        }
        Inst::Overflow { .. } => {
            "produces a (value, overflow-flag) pair. Its meaning is a tuple, which is outside \
             this reflector's domain, and collapsing it to the value alone would drop the flag."
        }
        Inst::UnOp { .. } => {
            "`Neg`/`Not`/`CtPop` at an unsigned carrier each have a Clean image, but none is \
             produced by the emitter's fragment, so none could be demonstrated."
        }
        Inst::Load { .. } | Inst::Store { .. } | Inst::Alloca { .. } | Inst::GEP { .. } => {
            "memory. The domain here is a pure environment with no store; a memory operation \
             would need a heap semantics AND would invalidate the substitution-for-sharing \
             argument in this file's header."
        }
        Inst::Call { .. } | Inst::CallIndirect { .. } => {
            "an interprocedural edge. The callee's meaning is not in this `Function`, and a \
             certified callee is NOT known to be pure (see CLAUDE.md), so its result cannot be \
             substituted."
        }
        Inst::Undef { .. } => {
            "`undef` has no value in the domain. Any term this reflector emitted for it would be \
             a value the IR does not commit to."
        }
        Inst::Assume { .. } | Inst::Assert { .. } => {
            "proof-directive instructions. They constrain the surrounding verification, not the \
             denoted function, and silently dropping them would change what the body claims."
        }
        _ => {
            "outside the accepted set: this reflector accepts only `const`, `binop` \
             (add/sub/mul/and/or), `icmp` (ult/ule/eq), `select`, and a final `return`."
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// 6. THE KERNEL HARNESS
// ═══════════════════════════════════════════════════════════════════════════

/// One Clean source line, its expected TrustIR-visible shape, and the verdict.
struct RoundTrip {
    name: String,
    /// The reflected term, as this file spelled it.
    reflected: Expr,
    /// The declaration's own value, as Clean's elaborator produced it.
    declared: Expr,
}

fn session_with(sources: &[&str]) -> trust_certify::clean_island::CleanIslandSession {
    let mut session = trust_certify::clean_island::CleanIslandSession::new();
    for src in sources {
        let outcome = session.check(src);
        assert!(
            !outcome.is_rejected(),
            "Clean rejected the fixture `{src}`:\n{:?}",
            outcome.errors
        );
    }
    session
}

/// Drive the emitter as a BLACK BOX to obtain a `Function`, then reflect it.
fn emit_and_reflect(env: &Environment, name: &str) -> (Function, Result<Expr, Refusal>) {
    let plan = trust_clean_origin::plan_clean_origin_body(env, name)
        .unwrap_or_else(|e| panic!("planning `{name}` failed: {e:?}"));
    let function = trust_clean_ir::emit_clean_origin_function(
        &plan,
        trust_ir::FuncId::new(0),
        trust_ir::FuncTyId::new(0),
    )
    .unwrap_or_else(|e| panic!("emitting `{name}` failed: {e:?}"));
    let reflected = reflect_straight_line_uint_function(&function);
    (function, reflected)
}

fn round_trip(env: &Environment, name: &str) -> RoundTrip {
    let (_, reflected) = emit_and_reflect(env, name);
    let reflected = reflected.unwrap_or_else(|r| panic!("reflection of `{name}` refused: {r:#?}"));
    let declared = env
        .get_const(&Name::from_string(name))
        .unwrap_or_else(|| panic!("`{name}` is not in the environment"))
        .value
        .clone()
        .unwrap_or_else(|| panic!("`{name}` has no value"));
    RoundTrip { name: name.to_owned(), reflected, declared }
}

/// The kernel verdict, with a well-typedness gate in front of it.
///
/// `is_def_eq` documents `REQUIRES: well-typed input`, so an ill-typed
/// reflection must never be handed to it — otherwise a "yes" would be outside
/// the contract that makes it mean anything. Inferring the reflected term's type
/// first and checking it against the declaration's own type closes that hole and
/// makes a "yes" a statement about two terms of the same type.
fn kernel_accepts(env: &Environment, rt: &RoundTrip) -> bool {
    let tc = clean_kernel::tc::TypeChecker::new(env);
    let declared_ty =
        env.get_const(&Name::from_string(&rt.name)).expect("declaration present").type_.clone();
    let Ok(inferred) = tc.infer_type_full(&rt.reflected) else {
        return false;
    };
    if !tc.is_def_eq(&inferred, &declared_ty) {
        return false;
    }
    tc.is_def_eq(&rt.reflected, &rt.declared)
}

/// Assert the kernel accepts the round trip, with the two terms printed on
/// failure so a mismatch is debuggable without re-running.
fn assert_kernel_agrees(env: &Environment, name: &str) {
    let rt = round_trip(env, name);
    assert!(
        kernel_accepts(env, &rt),
        "kernel REJECTED the independent reflection of `{name}`\n\
         reflected: {:?}\n\
         declared:  {:?}",
        rt.reflected,
        rt.declared
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// 7. COVERAGE TESTS — every accepted opcode, demonstrated end to end
// ═══════════════════════════════════════════════════════════════════════════

/// Every constant name this reflector can emit must actually exist in a plain
/// Clean prelude. A typo in a name would otherwise surface only as a mysterious
/// `is_def_eq = false`, which reads like a semantic disagreement.
#[test]
fn test_every_constant_this_reflector_names_exists() {
    let env = Environment::with_prelude();
    let mut named: Vec<String> = vec!["ite".into(), "Eq".into(), "LT.lt".into(), "LE.le".into()];
    for carrier in [Carrier::U8, Carrier::U16, Carrier::U32, Carrier::U64] {
        let p = carrier.prefix();
        named.push(p.to_owned());
        for f in ["ofNat", "add", "sub", "mul", "land", "lor"] {
            named.push(format!("{p}.{f}"));
        }
        named.push(format!("instLT{p}"));
        named.push(format!("instLE{p}"));
        named.push(format!("instDecidable{p}Lt"));
        named.push(format!("instDecidable{p}Le"));
        named.push(format!("instDecidableEq{p}"));
    }
    let missing: Vec<&String> =
        named.iter().filter(|n| env.get_const(&Name::from_string(n)).is_none()).collect();
    assert!(missing.is_empty(), "reflector names absent constants: {missing:?}");
}

#[test]
fn test_parameter_projection() {
    // The identity: a body that is a bare parameter. Reflection must produce
    // `fun a b => a`, i.e. the OUTER de Bruijn index, not the innermost one.
    let session = session_with(&[
        "def fst (a : UInt8) (b : UInt8) : UInt8 := a",
        "def snd (a : UInt8) (b : UInt8) : UInt8 := b",
        "def only (a : UInt32) : UInt32 := a",
    ]);
    let env = session.environment().expect("untainted session");
    for name in ["fst", "snd", "only"] {
        assert_kernel_agrees(env, name);
    }

    // De Bruijn discipline is load-bearing: `fst`'s reflection must NOT be
    // accepted against `snd`'s declaration.
    let fst = round_trip(env, "fst");
    let snd_decl = env.get_const(&Name::from_string("snd")).unwrap().value.clone().unwrap();
    let tc = clean_kernel::tc::TypeChecker::new(env);
    assert!(
        !tc.is_def_eq(&fst.reflected, &snd_decl),
        "`fst` and `snd` must not be definitionally equal — the binder index would be untested"
    );
}

#[test]
fn test_integer_constants() {
    let session = session_with(&[
        "def seven : UInt8 := 7",
        "def zero8 : UInt8 := 0",
        "def top8 : UInt8 := 255",
        "def bump (a : UInt8) : UInt8 := a + 7",
        "def big : UInt64 := 1000000",
    ]);
    let env = session.environment().expect("untainted session");
    for name in ["seven", "zero8", "top8", "bump", "big"] {
        assert_kernel_agrees(env, name);
    }
}

#[test]
fn test_add_sub_mul_and_nesting() {
    let session = session_with(&[
        "def sum (a : UInt8) (b : UInt8) : UInt8 := a + b",
        "def dif (a : UInt8) (b : UInt8) : UInt8 := a - b",
        "def prd (a : UInt8) (b : UInt8) : UInt8 := a * b",
        // Nesting, mixed operators, an operand used twice (exercises the
        // substitution-for-sharing step), and a literal inside the tree.
        "def poly (a : UInt8) (b : UInt8) : UInt8 := a * b + a - b",
        "def deep (a : UInt8) (b : UInt8) : UInt8 := (a + b) * (a - b) + (a * a) - 3",
    ]);
    let env = session.environment().expect("untainted session");
    for name in ["sum", "dif", "prd", "poly", "deep"] {
        assert_kernel_agrees(env, name);
    }
}

#[test]
fn test_bitwise_and_or() {
    let session = session_with(&[
        "def andf (a : UInt8) (b : UInt8) : UInt8 := a &&& b",
        "def orf (a : UInt8) (b : UInt8) : UInt8 := a ||| b",
        "def and16 (a : UInt16) (b : UInt16) : UInt16 := a &&& b",
        "def or64 (a : UInt64) (b : UInt64) : UInt64 := a ||| b",
    ]);
    let env = session.environment().expect("untainted session");
    for name in ["andf", "orf", "and16", "or64"] {
        assert_kernel_agrees(env, name);
    }
}

#[test]
fn test_all_four_widths() {
    let session = session_with(&[
        "def a8 (a : UInt8) (b : UInt8) : UInt8 := a * b + a - b",
        "def a16 (a : UInt16) (b : UInt16) : UInt16 := a * b + a - b",
        "def a32 (a : UInt32) (b : UInt32) : UInt32 := a * b + a - b",
        "def a64 (a : UInt64) (b : UInt64) : UInt64 := a * b + a - b",
    ]);
    let env = session.environment().expect("untainted session");
    for name in ["a8", "a16", "a32", "a64"] {
        assert_kernel_agrees(env, name);
    }
}

#[test]
fn test_select_over_lt_and_le() {
    let session = session_with(&[
        "def mn (a : UInt8) (b : UInt8) : UInt8 := if a < b then a else b",
        "def le0 (a : UInt8) (b : UInt8) : UInt8 := if a <= b then a else b",
        "def mn32 (a : UInt32) (b : UInt32) : UInt32 := if a < b then a else b",
        "def mn64 (a : UInt64) (b : UInt64) : UInt64 := if a <= b then a else b",
        "def mn16 (a : UInt16) (b : UInt16) : UInt16 := if a < b then a else b",
    ]);
    let env = session.environment().expect("untainted session");
    for name in ["mn", "le0", "mn32", "mn64", "mn16"] {
        assert_kernel_agrees(env, name);
    }

    // The arms are not symmetric: `mn`'s reflection must not satisfy the
    // declaration with the arms swapped.
    let session2 = session_with(&[
        "def mn (a : UInt8) (b : UInt8) : UInt8 := if a < b then a else b",
        "def mnflip (a : UInt8) (b : UInt8) : UInt8 := if a < b then b else a",
    ]);
    let env2 = session2.environment().unwrap();
    let mn = round_trip(env2, "mn");
    let flip = env2.get_const(&Name::from_string("mnflip")).unwrap().value.clone().unwrap();
    let tc = clean_kernel::tc::TypeChecker::new(env2);
    assert!(!tc.is_def_eq(&mn.reflected, &flip), "swapping the `ite` arms must change the term");
}

#[test]
fn test_select_over_eq() {
    let session =
        session_with(&["def eqp (a : UInt8) (b : UInt8) : UInt8 := if a = b then a else b"]);
    let env = session.environment().expect("untainted session");
    assert_kernel_agrees(env, "eqp");
}

// ═══════════════════════════════════════════════════════════════════════════
// 8. NON-VACUITY — the reflection must be a function of the IR, not of the
//    declaration. A reflector that returned the declaration verbatim, or that
//    ignored its input, must fail every test below.
// ═══════════════════════════════════════════════════════════════════════════

/// Reflect `a - b`'s IR against `a + b`'s declaration. If the kernel accepts
/// this, nothing else in this file means anything.
#[test]
fn test_non_vacuity_wrong_operator() {
    let session = session_with(&[
        "def sum (a : UInt8) (b : UInt8) : UInt8 := a + b",
        "def dif (a : UInt8) (b : UInt8) : UInt8 := a - b",
    ]);
    let env = session.environment().expect("untainted session");
    let dif = round_trip(env, "dif");
    let sum_decl = env.get_const(&Name::from_string("sum")).unwrap().value.clone().unwrap();
    let tc = clean_kernel::tc::TypeChecker::new(env);
    assert!(
        !tc.is_def_eq(&dif.reflected, &sum_decl),
        "the kernel accepted `a - b` as `a + b` — the round trip is vacuous"
    );
}

/// Reflect `a - b`'s IR against `b - a`'s declaration: operand ORDER must
/// survive the trip. (`+` would not detect this; `-` is not commutative.)
#[test]
fn test_non_vacuity_wrong_operand_order() {
    let session = session_with(&[
        "def dif (a : UInt8) (b : UInt8) : UInt8 := a - b",
        "def fid (a : UInt8) (b : UInt8) : UInt8 := b - a",
    ]);
    let env = session.environment().expect("untainted session");
    let dif = round_trip(env, "dif");
    let fid_decl = env.get_const(&Name::from_string("fid")).unwrap().value.clone().unwrap();
    let tc = clean_kernel::tc::TypeChecker::new(env);
    assert!(!tc.is_def_eq(&dif.reflected, &fid_decl), "the kernel accepted `a - b` as `b - a`");
}

/// A wrong literal must be caught.
#[test]
fn test_non_vacuity_wrong_literal() {
    let session = session_with(&[
        "def bump7 (a : UInt8) : UInt8 := a + 7",
        "def bump8 (a : UInt8) : UInt8 := a + 8",
    ]);
    let env = session.environment().expect("untainted session");
    let seven = round_trip(env, "bump7");
    let eight = env.get_const(&Name::from_string("bump8")).unwrap().value.clone().unwrap();
    let tc = clean_kernel::tc::TypeChecker::new(env);
    assert!(!tc.is_def_eq(&seven.reflected, &eight), "the kernel accepted `a + 7` as `a + 8`");
}

/// THE STRONGEST NON-VACUITY: mutate the IR the emitter produced — one opcode,
/// nothing else — reflect the MUTATED function, and require the kernel to reject
/// it against the UNMUTATED declaration.
///
/// This is the property that matters. It proves the reflected term is computed
/// from the IR's content: change the IR, and the verdict changes. A reflector
/// that re-printed the declaration, cached it, or consulted the environment
/// would pass every coverage test above and fail here.
#[test]
fn test_non_vacuity_ir_mutation_flips_the_verdict() {
    let session = session_with(&[
        "def sum (a : UInt8) (b : UInt8) : UInt8 := a + b",
        "def poly (a : UInt8) (b : UInt8) : UInt8 := a * b + a - b",
        "def mn (a : UInt8) (b : UInt8) : UInt8 := if a < b then a else b",
    ]);
    let env = session.environment().expect("untainted session");
    let tc = clean_kernel::tc::TypeChecker::new(env);

    // Mutation 1: Add -> Mul in `sum`.
    let (mut f, _) = emit_and_reflect(env, "sum");
    let unmutated = reflect_straight_line_uint_function(&f).expect("baseline reflects");
    let decl = env.get_const(&Name::from_string("sum")).unwrap().value.clone().unwrap();
    assert!(tc.is_def_eq(&unmutated, &decl), "baseline must be accepted");
    let mut mutated_any = false;
    for node in &mut f.blocks[0].body {
        if let Inst::BinOp { op, .. } = &mut node.inst {
            assert_eq!(*op, BinOp::Add, "fixture shape changed");
            *op = BinOp::Mul;
            mutated_any = true;
        }
    }
    assert!(mutated_any, "no BinOp found to mutate");
    let mutated = reflect_straight_line_uint_function(&f).expect("mutated IR still reflects");
    assert!(
        !tc.is_def_eq(&mutated, &decl),
        "mutating `add` to `mul` in the IR did not change the reflection — \
         the reflector is not reading its input"
    );

    // Mutation 2: swap the two operands of the outermost BinOp in `poly`.
    let (mut f, _) = emit_and_reflect(env, "poly");
    let decl = env.get_const(&Name::from_string("poly")).unwrap().value.clone().unwrap();
    assert!(
        tc.is_def_eq(&reflect_straight_line_uint_function(&f).expect("baseline reflects"), &decl),
        "baseline must be accepted"
    );
    let last_binop = f.blocks[0]
        .body
        .iter()
        .rposition(|n| matches!(n.inst, Inst::BinOp { .. }))
        .expect("a binop exists");
    if let Inst::BinOp { lhs, rhs, .. } = &mut f.blocks[0].body[last_binop].inst {
        std::mem::swap(lhs, rhs);
    }
    let mutated = reflect_straight_line_uint_function(&f).expect("mutated IR still reflects");
    assert!(
        !tc.is_def_eq(&mutated, &decl),
        "swapping the operands of the final `sub` did not change the reflection"
    );

    // Mutation 3: Ult -> Ule in `mn`. `if a < b then a else b` and
    // `if a <= b then a else b` are extensionally the same MIN function, but the
    // two `ite`s are not definitionally equal — so this catches a reflector that
    // ignores the comparison operator.
    let (mut f, _) = emit_and_reflect(env, "mn");
    let decl = env.get_const(&Name::from_string("mn")).unwrap().value.clone().unwrap();
    for node in &mut f.blocks[0].body {
        if let Inst::ICmp { op, .. } = &mut node.inst {
            assert_eq!(*op, ICmpOp::Ult, "fixture shape changed");
            *op = ICmpOp::Ule;
        }
    }
    let mutated = reflect_straight_line_uint_function(&f).expect("mutated IR still reflects");
    assert!(
        !tc.is_def_eq(&mutated, &decl),
        "mutating `ult` to `ule` in the IR did not change the reflection"
    );
}

/// A reflection at the wrong width must not be accepted, and — because the
/// harness type-checks first — must not even type-check against the other
/// declaration's type.
#[test]
fn test_non_vacuity_wrong_width() {
    let session = session_with(&[
        "def s8 (a : UInt8) (b : UInt8) : UInt8 := a + b",
        "def s16 (a : UInt16) (b : UInt16) : UInt16 := a + b",
    ]);
    let env = session.environment().expect("untainted session");
    let s8 = round_trip(env, "s8");
    let s16_decl = env.get_const(&Name::from_string("s16")).unwrap().value.clone().unwrap();
    let tc = clean_kernel::tc::TypeChecker::new(env);
    assert!(
        !tc.is_def_eq(&s8.reflected, &s16_decl),
        "a UInt8 reflection was accepted against a UInt16 declaration"
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// 9. REFUSALS — proved, not asserted
// ═══════════════════════════════════════════════════════════════════════════

fn u8_block(body: Vec<Inst>, params: usize) -> Function {
    let mut block = trust_ir::Block::new(trust_ir::BlockId::new(0));
    for i in 0..params {
        block = block.with_param(ValueId::new(u32::try_from(i).unwrap()), Ty::U8);
    }
    let mut next = u32::try_from(params).unwrap();
    for inst in body {
        let mut node = trust_ir::InstrNode::new(inst);
        if !matches!(node.inst, Inst::Return { .. }) {
            node.results = vec![ValueId::new(next)];
            next += 1;
        }
        block.body.push(node);
    }
    let mut f = Function::new(
        trust_ir::FuncId::new(0),
        "probe".to_owned(),
        trust_ir::FuncTyId::new(0),
        block.id,
    );
    f.entry = block.id;
    f.blocks = vec![block];
    f
}

/// One refusal probe: what it is, the hand-built function that triggers it, and
/// the refusal that must come back.
type RefusalCase = (&'static str, Function, fn(&Refusal) -> bool);

/// Each refusal below is exercised on a hand-built `Function` — the emitter
/// cannot produce these shapes, which is precisely why they must be refused
/// rather than left to the emitter's discretion.
#[test]
fn test_refuses_partial_and_out_of_domain_opcodes() {
    let v = ValueId::new;

    let cases: Vec<RefusalCase> = vec![
        (
            "udiv (UB on a zero divisor in the IR, total in Clean)",
            u8_block(
                vec![
                    Inst::BinOp { op: BinOp::UDiv, ty: Ty::U8, lhs: v(0), rhs: v(1) },
                    Inst::Return { values: vec![v(2)] },
                ],
                2,
            ),
            |r| matches!(r, Refusal::UnsupportedBinOp { op: "udiv/urem", .. }),
        ),
        (
            "urem",
            u8_block(
                vec![
                    Inst::BinOp { op: BinOp::URem, ty: Ty::U8, lhs: v(0), rhs: v(1) },
                    Inst::Return { values: vec![v(2)] },
                ],
                2,
            ),
            |r| matches!(r, Refusal::UnsupportedBinOp { op: "udiv/urem", .. }),
        ),
        (
            "shl (out-of-range shift amount)",
            u8_block(
                vec![
                    Inst::BinOp { op: BinOp::Shl, ty: Ty::U8, lhs: v(0), rhs: v(1) },
                    Inst::Return { values: vec![v(2)] },
                ],
                2,
            ),
            |r| matches!(r, Refusal::UnsupportedBinOp { op: "shl/lshr/ashr", .. }),
        ),
        (
            "xor (spellable, but never exercised)",
            u8_block(
                vec![
                    Inst::BinOp { op: BinOp::Xor, ty: Ty::U8, lhs: v(0), rhs: v(1) },
                    Inst::Return { values: vec![v(2)] },
                ],
                2,
            ),
            |r| matches!(r, Refusal::UnsupportedBinOp { op: "xor", .. }),
        ),
        (
            "slt (the SIGNED order at an unsigned carrier)",
            u8_block(
                vec![
                    Inst::ICmp { op: ICmpOp::Slt, ty: Ty::U8, lhs: v(0), rhs: v(1) },
                    Inst::Select { ty: Ty::U8, cond: v(2), then_val: v(0), else_val: v(1) },
                    Inst::Return { values: vec![v(3)] },
                ],
                2,
            ),
            |r| {
                matches!(
                    r,
                    Refusal::UnsupportedICmp { op: "signed comparison at an unsigned carrier", .. }
                )
            },
        ),
        (
            "ugt (operand-swap of ult, but never exercised)",
            u8_block(
                vec![
                    Inst::ICmp { op: ICmpOp::Ugt, ty: Ty::U8, lhs: v(0), rhs: v(1) },
                    Inst::Select { ty: Ty::U8, cond: v(2), then_val: v(0), else_val: v(1) },
                    Inst::Return { values: vec![v(3)] },
                ],
                2,
            ),
            |r| matches!(r, Refusal::UnsupportedICmp { op: "ugt/uge", .. }),
        ),
        (
            "ne",
            u8_block(
                vec![
                    Inst::ICmp { op: ICmpOp::Ne, ty: Ty::U8, lhs: v(0), rhs: v(1) },
                    Inst::Select { ty: Ty::U8, cond: v(2), then_val: v(0), else_val: v(1) },
                    Inst::Return { values: vec![v(3)] },
                ],
                2,
            ),
            |r| matches!(r, Refusal::UnsupportedICmp { op: "ne", .. }),
        ),
        (
            "load (memory)",
            u8_block(
                vec![
                    Inst::Load { ty: Ty::U8, ptr: v(0), volatile: false, align: None },
                    Inst::Return { values: vec![v(2)] },
                ],
                2,
            ),
            |r| matches!(r, Refusal::UnsupportedInst { opcode: "load", .. }),
        ),
        (
            "call (interprocedural; a certified callee is not known to be pure)",
            u8_block(
                vec![
                    Inst::Call { callee: trust_ir::FuncId::new(1), args: vec![v(0)] },
                    Inst::Return { values: vec![v(2)] },
                ],
                2,
            ),
            |r| matches!(r, Refusal::UnsupportedInst { opcode: "call", .. }),
        ),
        (
            "copy (identity, but never exercised)",
            u8_block(
                vec![Inst::Copy { ty: Ty::U8, operand: v(0) }, Inst::Return { values: vec![v(2)] }],
                2,
            ),
            |r| matches!(r, Refusal::UnsupportedInst { opcode: "copy", .. }),
        ),
        (
            "undef (no value in the domain)",
            u8_block(vec![Inst::Undef { ty: Ty::U8 }, Inst::Return { values: vec![v(2)] }], 2),
            |r| matches!(r, Refusal::UnsupportedInst { opcode: "undef", .. }),
        ),
        (
            "cast (changes the carrier)",
            u8_block(
                vec![
                    Inst::Cast {
                        op: trust_ir::CastOp::ZExt,
                        src_ty: Ty::U8,
                        dst_ty: Ty::U16,
                        operand: v(0),
                    },
                    Inst::Return { values: vec![v(2)] },
                ],
                2,
            ),
            |r| matches!(r, Refusal::UnsupportedInst { opcode: "cast", .. }),
        ),
        (
            "a comparison used where a carrier value is needed",
            u8_block(
                vec![
                    Inst::ICmp { op: ICmpOp::Ult, ty: Ty::U8, lhs: v(0), rhs: v(1) },
                    Inst::Return { values: vec![v(2)] },
                ],
                2,
            ),
            |r| matches!(r, Refusal::ComparisonUsedAsValue { .. }),
        ),
        (
            "a carrier value used as an `ite` condition",
            u8_block(
                vec![
                    Inst::Select { ty: Ty::U8, cond: v(0), then_val: v(0), else_val: v(1) },
                    Inst::Return { values: vec![v(2)] },
                ],
                2,
            ),
            |r| matches!(r, Refusal::ValueUsedAsCondition { .. }),
        ),
        (
            "an out-of-range literal for the carrier",
            u8_block(
                vec![
                    Inst::Const { ty: Ty::U8, value: Constant::Int(300) },
                    Inst::Return { values: vec![v(2)] },
                ],
                2,
            ),
            |r| matches!(r, Refusal::ConstantOutOfCarrierRange { value: 300, .. }),
        ),
        (
            "a negative literal",
            u8_block(
                vec![
                    Inst::Const { ty: Ty::U8, value: Constant::Int(-1) },
                    Inst::Return { values: vec![v(2)] },
                ],
                2,
            ),
            |r| matches!(r, Refusal::ConstantOutOfCarrierRange { value: -1, .. }),
        ),
        (
            "a block that does not end in `return`",
            u8_block(vec![Inst::BinOp { op: BinOp::Add, ty: Ty::U8, lhs: v(0), rhs: v(1) }], 2),
            |r| matches!(r, Refusal::BlockDoesNotEndInReturn { .. }),
        ),
        (
            "a multi-value return",
            u8_block(vec![Inst::Return { values: vec![v(0), v(1)] }], 2),
            |r| matches!(r, Refusal::ReturnArity { values: 2 }),
        ),
        (
            "a use of an undefined value",
            u8_block(vec![Inst::Return { values: vec![v(9)] }], 2),
            |r| matches!(r, Refusal::UndefinedValue { value: 9 }),
        ),
    ];

    for (label, f, predicate) in cases {
        let got = reflect_straight_line_uint_function(&f);
        match got {
            Ok(term) => panic!("REFLECTED {label} instead of refusing it: {term:?}"),
            Err(r) => {
                assert!(predicate(&r), "{label}: refused, but with the wrong refusal: {r:#?}")
            }
        }
    }
}

#[test]
fn test_refuses_non_carrier_types_and_mixed_widths() {
    let v = ValueId::new;

    // A signed carrier is not in the domain at all.
    let mut block = trust_ir::Block::new(trust_ir::BlockId::new(0));
    block = block.with_param(v(0), Ty::I32);
    let mut node = trust_ir::InstrNode::new(Inst::Return { values: vec![v(0)] });
    node.results = vec![];
    block.body.push(node);
    let mut f = Function::new(
        trust_ir::FuncId::new(0),
        "signed".to_owned(),
        trust_ir::FuncTyId::new(0),
        block.id,
    );
    f.entry = block.id;
    f.blocks = vec![block];
    assert!(matches!(
        reflect_straight_line_uint_function(&f),
        Err(Refusal::NotAnUnsignedMachineCarrier { .. })
    ));

    // `Usize` is target-dependent, not a fixed carrier.
    let mut block = trust_ir::Block::new(trust_ir::BlockId::new(0));
    block = block.with_param(v(0), Ty::Usize);
    let mut node = trust_ir::InstrNode::new(Inst::Return { values: vec![v(0)] });
    node.results = vec![];
    block.body.push(node);
    let mut f = Function::new(
        trust_ir::FuncId::new(0),
        "usize".to_owned(),
        trust_ir::FuncTyId::new(0),
        block.id,
    );
    f.entry = block.id;
    f.blocks = vec![block];
    assert!(matches!(
        reflect_straight_line_uint_function(&f),
        Err(Refusal::NotAnUnsignedMachineCarrier { .. })
    ));

    // Two carriers in one body.
    let mut block = trust_ir::Block::new(trust_ir::BlockId::new(0));
    block = block.with_param(v(0), Ty::U8).with_param(v(1), Ty::U16);
    let mut n1 =
        trust_ir::InstrNode::new(Inst::BinOp { op: BinOp::Add, ty: Ty::U16, lhs: v(0), rhs: v(1) });
    n1.results = vec![v(2)];
    block.body.push(n1);
    block.body.push(trust_ir::InstrNode::new(Inst::Return { values: vec![v(2)] }));
    let mut f = Function::new(
        trust_ir::FuncId::new(0),
        "mixed".to_owned(),
        trust_ir::FuncTyId::new(0),
        block.id,
    );
    f.entry = block.id;
    f.blocks = vec![block];
    assert!(matches!(
        reflect_straight_line_uint_function(&f),
        Err(Refusal::MixedCarrierWidths { first: Carrier::U8, then_: Carrier::U16 })
    ));
}

#[test]
fn test_refuses_multi_block_control_flow() {
    let mut b0 = trust_ir::Block::new(trust_ir::BlockId::new(0));
    b0 = b0.with_param(ValueId::new(0), Ty::U8);
    b0.body.push(trust_ir::InstrNode::new(Inst::Br {
        target: trust_ir::BlockId::new(1),
        args: vec![ValueId::new(0)],
    }));
    let mut b1 = trust_ir::Block::new(trust_ir::BlockId::new(1));
    b1 = b1.with_param(ValueId::new(1), Ty::U8);
    b1.body.push(trust_ir::InstrNode::new(Inst::Return { values: vec![ValueId::new(1)] }));
    let mut f = Function::new(
        trust_ir::FuncId::new(0),
        "twoblocks".to_owned(),
        trust_ir::FuncTyId::new(0),
        b0.id,
    );
    f.entry = b0.id;
    f.blocks = vec![b0, b1];
    assert!(matches!(
        reflect_straight_line_uint_function(&f),
        Err(Refusal::NotSingleBlock { blocks: 2 })
    ));
}

// ═══════════════════════════════════════════════════════════════════════════
// 10. FINDINGS, RECORDED AS TESTS
//
// Two things this reflector could not honestly spell, both discovered by
// building the semantics first and then measuring what the kernel said. Neither
// is a false accept — both are the kernel refusing a correct reflection, which
// is the safe direction. They are written down as executable tests so that a
// later reader who is tempted to "fix" the reflector by making it guess at
// source syntax has to argue with a measurement rather than with a comment.
// ═══════════════════════════════════════════════════════════════════════════

/// Strip `n` leading lambdas.
fn strip_lams(e: &Expr, n: usize) -> Expr {
    let mut cur = e.clone();
    for _ in 0..n {
        let next = match &*cur {
            clean_kernel::ExprKind::Lam(_, _, body) => (**body).clone(),
            other => panic!("expected a lambda, found {other:?}"),
        };
        cur = next;
    }
    cur
}

/// Split an application into its head and its arguments, in application order.
fn app_spine(e: &Expr) -> (Expr, Vec<Expr>) {
    // `get_app_args_iter` walks the spine outside-in, so it yields the LAST
    // argument first; reversing puts them back in application order.
    let mut args: Vec<Expr> = e.get_app_args_iter().cloned().collect();
    args.reverse();
    (e.get_app_fn().clone(), args)
}

/// Re-close a sub-term of a two-parameter body under its two binders, so it can
/// be handed to `is_def_eq` without loose de Bruijn indices.
fn reclose2(carrier: Carrier, body: Expr) -> Expr {
    Expr::lam(
        BinderInfo::Default,
        carrier.clean_type(),
        Expr::lam(BinderInfo::Default, carrier.clean_type(), body),
    )
}

/// The `Decidable` instance an `ite` eliminates is NOT recorded in the IR, and
/// Clean's elaborator does not always choose the carrier's own instance.
///
/// For `if a < b then a else b` it picks `instDecidableUInt8Lt a b`, which this
/// reflector reconstructs exactly. For `if a < 10 then a else b` — the same
/// relation, with a numeral on the right — it instead picks
/// `instDecidableNatLt a.toBitVec.toFin.val 10`, comparing at `Nat` after
/// projecting out of the carrier.
///
/// The IR is identical in structure for both (`ICmp Ult` on a value and a
/// constant), so an IR-only reflector has nothing to choose on. This test pins
/// down exactly where the two terms diverge: the propositions and both arms
/// agree definitionally, and ONLY the instance does not — and since `ite`'s
/// value is computed by eliminating that instance, the whole term is rejected.
///
/// This is a false NEGATIVE of the round trip, not a soundness gap: the kernel
/// declines to certify a body it in fact agrees with. Closing it would need
/// either a canonical-instance normalization on the Clean side, or an IR that
/// carries the instance — not a reflector that guesses.
#[test]
fn test_finding_the_decidable_instance_is_not_recorded_in_the_ir() {
    let session = session_with(&[
        "def mn (a : UInt8) (b : UInt8) : UInt8 := if a < b then a else b",
        "def clampish (a : UInt8) (b : UInt8) : UInt8 := if a < 10 then a else b",
    ]);
    let env = session.environment().expect("untainted session");
    let tc = clean_kernel::tc::TypeChecker::new(env);

    // The variable-on-the-right form round-trips.
    assert_kernel_agrees(env, "mn");

    // The numeral-on-the-right form does not.
    let (function, reflected) = emit_and_reflect(env, "clampish");
    let reflected = reflected.expect("`clampish` reflects");
    let declared = env.get_const(&Name::from_string("clampish")).unwrap().value.clone().unwrap();

    // Its IR is the ordinary compare-then-select shape — nothing about it says
    // "a numeral was involved" in a way an instance could be chosen from.
    assert!(
        function.blocks[0]
            .body
            .iter()
            .any(|n| matches!(n.inst, Inst::ICmp { op: ICmpOp::Ult, .. })),
        "fixture shape changed"
    );

    let (mine_head, mine_args) = app_spine(&strip_lams(&reflected, 2));
    let (decl_head, decl_args) = app_spine(&strip_lams(&declared, 2));
    assert_eq!(
        format!("{mine_head:?}"),
        format!("{decl_head:?}"),
        "both sides must be an `ite` application"
    );
    assert_eq!(mine_args.len(), 5, "ite takes ty, prop, inst, then, else");
    assert_eq!(decl_args.len(), 5);

    let close = |e: &Expr| reclose2(Carrier::U8, e.clone());
    // Result type, proposition, and both arms agree.
    for (i, what) in [(0, "result type"), (1, "proposition"), (3, "then"), (4, "else")] {
        assert!(
            tc.is_def_eq(&close(&mine_args[i]), &close(&decl_args[i])),
            "the {what} argument of `ite` should agree, but does not:\n\
             mine: {:?}\ndecl: {:?}",
            mine_args[i],
            decl_args[i]
        );
    }
    // The `Decidable` instance does not.
    assert!(
        !tc.is_def_eq(&close(&mine_args[2]), &close(&decl_args[2])),
        "if the two `Decidable` instances now reconcile, this finding has been \
         resolved upstream and `clampish` should move into the coverage tests"
    );
    assert!(!tc.is_def_eq(&reflected, &declared), "whole-term verdict must follow the instance");
}

/// `ICmp Eq` at an unsigned carrier does NOT determine the Clean proposition
/// the source wrote, and this is measurable from outside the emitter.
///
/// `if a = b then ..` elaborates to `ite (@Eq UInt8 a b) (instDecidableEqUInt8 a b) ..`;
/// `if a == b then ..` elaborates to `ite (BEq.beq a b = true) (instDecidableEqBool ..) ..`.
/// The two propositions are provably equivalent but not DEFINITIONALLY equal —
/// and the emitter maps both surface forms to a byte-identical `ICmp Eq`.
///
/// Consequence, stated plainly: no reflector that reads only the IR can be
/// `is_def_eq` to both declarations. This one emits `@Eq`, so the `==` form is a
/// false NEGATIVE. That is the safe direction (the kernel refuses; nothing is
/// blessed), and it is recorded here so a later reader does not "fix" it by
/// making the reflector guess at source syntax it cannot see.
#[test]
fn test_finding_icmp_eq_is_not_injective_into_clean() {
    let session = session_with(&[
        "def eqp (a : UInt8) (b : UInt8) : UInt8 := if a = b then a else b",
        "def eqb (a : UInt8) (b : UInt8) : UInt8 := if a == b then a else b",
    ]);
    let env = session.environment().expect("untainted session");

    let (fp, rp) = emit_and_reflect(env, "eqp");
    let (fb, rb) = emit_and_reflect(env, "eqb");

    // Same IR, to the instruction.
    let shape = |f: &Function| {
        f.blocks[0]
            .body
            .iter()
            .map(|n| format!("{:?} -> {:?}", n.inst, n.results))
            .collect::<Vec<_>>()
    };
    assert_eq!(
        shape(&fp),
        shape(&fb),
        "the fixture assumes `=` and `==` produce the same IR; they no longer do"
    );

    // Same reflection, therefore.
    let rp = rp.expect("`=` form reflects");
    let rb = rb.expect("`==` form reflects");
    assert_eq!(
        format!("{rp:?}"),
        format!("{rb:?}"),
        "identical IR must give an identical reflection"
    );

    // But only one declaration accepts it.
    let tc = clean_kernel::tc::TypeChecker::new(env);
    let decl = |n: &str| env.get_const(&Name::from_string(n)).unwrap().value.clone().unwrap();
    assert!(tc.is_def_eq(&rp, &decl("eqp")), "the `=` form must be accepted");
    assert!(
        !tc.is_def_eq(&rb, &decl("eqb")),
        "if the kernel now accepts the `==` form too, this finding has been \
         resolved upstream and this test should be revisited"
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// 11. THE MUTATION BATTERY — the round trip's own non-vacuity, proved
//
// EVERYTHING IN SECTIONS 7-10 IS CONDITIONAL ON THIS SECTION.
//
// Section 7 shows that the kernel says YES to the reflection of a correctly
// emitted body. On its own that is worth nothing: a reflector that ignored its
// input and re-printed the declaration would produce exactly the same eighteen
// greens. The round trip is evidence only if the verdict is a FUNCTION OF THE
// IR's CONTENT — i.e. if corrupting the IR flips the verdict to NO.
//
// So this section takes the `trust_ir::Function` the emitter ACTUALLY PRODUCED,
// changes exactly one thing in it, and demands that the corruption be caught.
// Two outcomes count as caught, and they are not equally informative:
//
//   Refused        the reflector declined to spell the mutated body at all. The
//                  corruption never reached the kernel. Safe, but it is THIS
//                  FILE catching it, not the kernel.
//   KernelRejected the reflector produced a well-typed Clean term and the CIC
//                  kernel said the term is not the declaration. This is the
//                  outcome that actually exercises the round trip, so each test
//                  below records WHICH it got rather than accepting either
//                  silently.
//
// And one outcome is a defect:
//
//   KernelAccepted the kernel blessed the reflection of a CORRUPTED body against
//                  the pristine declaration. That is a surviving mutation: a
//                  class of wrong body this round trip cannot see, and therefore
//                  a class of wrong body that could be certified.
//
// THE PRECONDITION THAT MAKES A MUTATION MEAN ANYTHING. Every test here asserts
// the PRISTINE body is accepted BEFORE mutating it. Without that assertion a
// mutation test is self-fulfilling — if the fixture were rejected for an
// unrelated reason (a renamed instance, a changed elaboration) then every
// mutation of it would also be rejected, the test would stay green, and it would
// be measuring nothing. `assert_mutation_is_caught` refuses to run a mutation
// whose baseline was not first accepted.
//
// AND THE SECOND PRECONDITION: the mutation must actually change the IR.
// `mutate_first` panics if no instruction accepted the mutation, and
// `assert_mutation_is_caught` panics if the post-mutation body is equal to the
// pristine one. A mutator that silently matched nothing would otherwise pass
// forever, and would do so most convincingly right after a fixture's shape
// changed underneath it.
// ═══════════════════════════════════════════════════════════════════════════

/// What happened when a (possibly corrupted) `Function` was put through the
/// round trip against a fixed declaration.
#[derive(Debug)]
enum MutationVerdict {
    /// This reflector declined to spell the body. The kernel never saw it.
    Refused(Refusal),
    /// A well-typed Clean term was produced and the kernel said it is not the
    /// declaration.
    KernelRejected,
    /// The kernel accepted it. For a pristine body this is required; for a
    /// mutated body it is a SURVIVING MUTATION.
    KernelAccepted,
}

impl MutationVerdict {
    fn is_accepted(&self) -> bool {
        matches!(self, MutationVerdict::KernelAccepted)
    }

    /// A short tag for the per-test measurement lines, so a reader of the test
    /// output can see whether the KERNEL caught a mutation or whether this file
    /// refused it before the kernel was consulted.
    fn tag(&self) -> &'static str {
        match self {
            MutationVerdict::Refused(_) => "REFUSED (by the reflector)",
            MutationVerdict::KernelRejected => "REJECTED (by the kernel)",
            MutationVerdict::KernelAccepted => "ACCEPTED — SURVIVING MUTATION",
        }
    }
}

fn declared_value(env: &Environment, name: &str) -> Expr {
    env.get_const(&Name::from_string(name))
        .unwrap_or_else(|| panic!("`{name}` is not in the environment"))
        .value
        .clone()
        .unwrap_or_else(|| panic!("`{name}` has no value"))
}

/// The emitter's output for `name`, as a black box.
fn emitted(env: &Environment, name: &str) -> Function {
    emit_and_reflect(env, name).0
}

/// Put `f` — pristine or corrupted — through the round trip against `name`'s
/// declaration, using EXACTLY the acceptance predicate section 7 uses. Judging
/// the mutant by a different (stricter) rule than the baseline would be how a
/// mutation battery lies to itself, so `kernel_accepts` is reused verbatim.
fn verdict_for(env: &Environment, name: &str, f: &Function) -> MutationVerdict {
    let reflected = match reflect_straight_line_uint_function(f) {
        Ok(e) => e,
        Err(r) => return MutationVerdict::Refused(r),
    };
    let rt = RoundTrip { name: name.to_owned(), reflected, declared: declared_value(env, name) };
    if kernel_accepts(env, &rt) {
        MutationVerdict::KernelAccepted
    } else {
        MutationVerdict::KernelRejected
    }
}

/// A corruption of one instruction. Returns whether it applied.
type Mutator = fn(&mut Inst) -> bool;

/// Apply `mutate` to the FIRST instruction that accepts it.
///
/// Panics when nothing accepts it: a mutator that quietly matched nothing is the
/// one failure mode that makes a mutation test green and worthless.
fn mutate_first(f: &mut Function, what: &str, mutate: Mutator) {
    let applied = f.blocks[0].body.iter_mut().any(|n| mutate(&mut n.inst));
    assert!(
        applied,
        "no instruction accepted the mutation `{what}` — the fixture's IR shape changed, and \
         this test would otherwise pass while corrupting nothing"
    );
}

/// The two assertions that give a mutation its teeth: the corruption must be
/// real, and it must not be accepted.
///
/// Factored out of [`assert_mutation_is_caught`] on purpose, so that
/// `test_the_battery_can_actually_see_a_survivor` can drive a KNOWN survivor
/// through this exact code and prove the panic fires. An unfireable assertion is
/// the way a mutation battery lies.
fn check_mutant(
    env: &Environment,
    name: &str,
    what: &str,
    pristine: &Function,
    mutant: &Function,
) -> MutationVerdict {
    assert_ne!(
        pristine.blocks[0].body, mutant.blocks[0].body,
        "`{what}` left the IR unchanged — nothing was corrupted, so nothing is being tested"
    );

    let verdict = verdict_for(env, name, mutant);
    assert!(
        !verdict.is_accepted(),
        "\n\
         ════════════════════════════════════════════════════════════════════\n\
         MUTATION SURVIVED: `{what}` on `{name}`\n\
         ════════════════════════════════════════════════════════════════════\n\
         The CIC kernel accepted the reflection of a CORRUPTED body against the\n\
         PRISTINE declaration. The round trip cannot see this class of error,\n\
         so a body wrong in this way would certify.\n\
         pristine IR: {:#?}\n\
         mutated  IR: {:#?}\n",
        pristine.blocks[0].body,
        mutant.blocks[0].body
    );
    eprintln!("  mutation `{what}` on `{name}`: {}", verdict.tag());
    verdict
}

/// The whole discipline in one function: baseline accepted, IR really changed,
/// corruption caught. Returns the mutant's verdict so a caller can additionally
/// assert WHICH way it was caught.
fn assert_mutation_is_caught(
    env: &Environment,
    name: &str,
    what: &str,
    mutate: Mutator,
) -> MutationVerdict {
    // PRECONDITION 1 — the pristine body must round-trip. Otherwise the mutation
    // below is being compared against a baseline that was already failing, and a
    // green here would mean nothing at all.
    let pristine = emitted(env, name);
    let baseline = verdict_for(env, name, &pristine);
    assert!(
        baseline.is_accepted(),
        "the PRISTINE body of `{name}` was NOT accepted ({}), so the `{what}` mutation would \
         prove nothing: every mutation of an already-rejected baseline is trivially 'caught'.\n\
         {baseline:#?}",
        baseline.tag()
    );

    // PRECONDITION 2 — the corruption must be real, and it must be caught.
    let mut mutant = pristine.clone();
    mutate_first(&mut mutant, what, mutate);
    check_mutant(env, name, what, &pristine, &mutant)
}

// ---- the mutators -----------------------------------------------------------

/// Swap a `Select`'s two arms: `if P then t else e` becomes `if P then e else t`.
fn mut_swap_select_arms(inst: &mut Inst) -> bool {
    match inst {
        Inst::Select { then_val, else_val, .. } if then_val != else_val => {
            std::mem::swap(then_val, else_val);
            true
        }
        _ => false,
    }
}

/// `BinOp::Add` -> `BinOp::Sub`.
fn mut_add_to_sub(inst: &mut Inst) -> bool {
    match inst {
        Inst::BinOp { op, .. } if *op == BinOp::Add => {
            *op = BinOp::Sub;
            true
        }
        _ => false,
    }
}

/// `BinOp::Sub` -> `BinOp::Add` (the same corruption from the other side).
fn mut_sub_to_add(inst: &mut Inst) -> bool {
    match inst {
        Inst::BinOp { op, .. } if *op == BinOp::Sub => {
            *op = BinOp::Add;
            true
        }
        _ => false,
    }
}

/// `BinOp::Mul` -> `BinOp::Add`.
fn mut_mul_to_add(inst: &mut Inst) -> bool {
    match inst {
        Inst::BinOp { op, .. } if *op == BinOp::Mul => {
            *op = BinOp::Add;
            true
        }
        _ => false,
    }
}

/// `BinOp::And` -> `BinOp::Or` (bitwise, at the integer carrier).
fn mut_and_to_or(inst: &mut Inst) -> bool {
    match inst {
        Inst::BinOp { op, .. } if *op == BinOp::And => {
            *op = BinOp::Or;
            true
        }
        _ => false,
    }
}

/// `BinOp::Or` -> `BinOp::And`.
fn mut_or_to_and(inst: &mut Inst) -> bool {
    match inst {
        Inst::BinOp { op, .. } if *op == BinOp::Or => {
            *op = BinOp::And;
            true
        }
        _ => false,
    }
}

/// Swap the operands of a NON-COMMUTATIVE `Sub`. Restricted to `Sub` on purpose:
/// see `test_mutation_operand_swap_at_a_commutative_op` for why the commutative
/// ops are measured separately rather than folded in here.
fn mut_swap_sub_operands(inst: &mut Inst) -> bool {
    match inst {
        Inst::BinOp { op: BinOp::Sub, lhs, rhs, .. } if lhs != rhs => {
            std::mem::swap(lhs, rhs);
            true
        }
        _ => false,
    }
}

/// Swap the operands of ANY binop with distinct operands.
fn mut_swap_any_binop_operands(inst: &mut Inst) -> bool {
    match inst {
        Inst::BinOp { lhs, rhs, .. } if lhs != rhs => {
            std::mem::swap(lhs, rhs);
            true
        }
        _ => false,
    }
}

/// Shift an integer constant up by one. `k` becomes `k + 1` — the smallest
/// possible corruption of a literal.
fn mut_const_plus_one(inst: &mut Inst) -> bool {
    match inst {
        Inst::Const { value: Constant::Int(k), .. } => {
            *k += 1;
            true
        }
        _ => false,
    }
}

/// Shift an integer constant down by one.
fn mut_const_minus_one(inst: &mut Inst) -> bool {
    match inst {
        Inst::Const { value: Constant::Int(k), .. } => {
            *k -= 1;
            true
        }
        _ => false,
    }
}

/// WIDEN a strict comparison: `Ult` -> `Ule`. The dangerous direction, because
/// for `min` the two are EXTENSIONALLY the same function — only the terms differ.
fn mut_ult_to_ule(inst: &mut Inst) -> bool {
    match inst {
        Inst::ICmp { op, .. } if *op == ICmpOp::Ult => {
            *op = ICmpOp::Ule;
            true
        }
        _ => false,
    }
}

/// NARROW a comparison: `Ule` -> `Ult`.
fn mut_ule_to_ult(inst: &mut Inst) -> bool {
    match inst {
        Inst::ICmp { op, .. } if *op == ICmpOp::Ule => {
            *op = ICmpOp::Ult;
            true
        }
        _ => false,
    }
}

/// Replace an equality test with a strict order test.
fn mut_eq_to_ult(inst: &mut Inst) -> bool {
    match inst {
        Inst::ICmp { op, .. } if *op == ICmpOp::Eq => {
            *op = ICmpOp::Ult;
            true
        }
        _ => false,
    }
}

/// Swap the operands of a comparison.
fn mut_swap_icmp_operands(inst: &mut Inst) -> bool {
    match inst {
        Inst::ICmp { lhs, rhs, .. } if lhs != rhs => {
            std::mem::swap(lhs, rhs);
            true
        }
        _ => false,
    }
}

// ---- the five mandated mutations, one test each ------------------------------

/// MUTATION 1 — swap the two arms of a `Select`.
///
/// `min` becomes `max`. If this survived, a certified `min` could be a `max`.
#[test]
fn test_mutation_select_arms_swapped() {
    let session = session_with(&[
        "def mn (a : UInt8) (b : UInt8) : UInt8 := if a < b then a else b",
        "def mnle (a : UInt8) (b : UInt8) : UInt8 := if a <= b then a else b",
        "def mn32 (a : UInt32) (b : UInt32) : UInt32 := if a < b then a else b",
        "def eqp (a : UInt8) (b : UInt8) : UInt8 := if a = b then a else b",
        // Three parameters, and the two arms are NON-ADJACENT binders (indices 2
        // and 0). Swapping them is a bigger de Bruijn move than the two-parameter
        // fixtures can express, and the arms are not the compared operands.
        "def pick (a : UInt8) (b : UInt8) (c : UInt8) : UInt8 := if a < b then a else c",
    ]);
    let env = session.environment().expect("untainted session");
    for name in ["mn", "mnle", "mn32", "eqp", "pick"] {
        assert_mutation_is_caught(env, name, "select: arms swapped", mut_swap_select_arms);
    }
}

/// MUTATION 2 — `BinOp::Add` becomes `BinOp::Sub`.
#[test]
fn test_mutation_add_becomes_sub() {
    let session = session_with(&[
        "def sum (a : UInt8) (b : UInt8) : UInt8 := a + b",
        "def bump (a : UInt8) : UInt8 := a + 7",
        "def poly (a : UInt8) (b : UInt8) : UInt8 := a * b + a - b",
        "def sum64 (a : UInt64) (b : UInt64) : UInt64 := a + b",
    ]);
    let env = session.environment().expect("untainted session");
    for name in ["sum", "bump", "poly", "sum64"] {
        assert_mutation_is_caught(env, name, "binop: add -> sub", mut_add_to_sub);
    }

    // ... and the same corruption from the other side, so neither direction is
    // being caught by an accident of which opcode happens to be first.
    let session = session_with(&[
        "def dif (a : UInt8) (b : UInt8) : UInt8 := a - b",
        "def poly (a : UInt8) (b : UInt8) : UInt8 := a * b + a - b",
    ]);
    let env = session.environment().expect("untainted session");
    for name in ["dif", "poly"] {
        assert_mutation_is_caught(env, name, "binop: sub -> add", mut_sub_to_add);
    }
}

/// MUTATION 3 — swap `lhs`/`rhs` of a non-commutative `Sub`.
///
/// `a - b` becomes `b - a`. Operand ORDER is the part of the IR a reflector that
/// merely counted opcodes would lose.
#[test]
fn test_mutation_sub_operands_swapped() {
    let session = session_with(&[
        "def dif (a : UInt8) (b : UInt8) : UInt8 := a - b",
        "def poly (a : UInt8) (b : UInt8) : UInt8 := a * b + a - b",
        "def deep (a : UInt8) (b : UInt8) : UInt8 := (a + b) * (a - b) + (a * a) - 3",
        "def dif32 (a : UInt32) (b : UInt32) : UInt32 := a - b",
    ]);
    let env = session.environment().expect("untainted session");
    for name in ["dif", "poly", "deep", "dif32"] {
        assert_mutation_is_caught(env, name, "binop: sub operands swapped", mut_swap_sub_operands);
    }
}

/// MUTATION 4 — shift an integer `Constant` by one.
///
/// The smallest possible corruption of a literal, at three interesting places:
/// an ordinary literal, `0` (where `-1` leaves the carrier's value set entirely),
/// and the carrier maximum (where `+1` does the same). The last two are expected
/// to be caught by a REFUSAL rather than by the kernel, and the test records
/// which, because "the reflector refused" and "the kernel disagreed" are
/// different amounts of evidence.
#[test]
fn test_mutation_integer_constant_shifted_by_one() {
    let session = session_with(&[
        "def bump (a : UInt8) : UInt8 := a + 7",
        "def seven : UInt8 := 7",
        "def zero8 : UInt8 := 0",
        "def top8 : UInt8 := 255",
        "def big : UInt64 := 1000000",
        "def deep (a : UInt8) (b : UInt8) : UInt8 := (a + b) * (a - b) + (a * a) - 3",
    ]);
    let env = session.environment().expect("untainted session");

    // `k` -> `k + 1`, everywhere it stays inside the carrier.
    for name in ["bump", "seven", "zero8", "big", "deep"] {
        let v = assert_mutation_is_caught(env, name, "const: k -> k+1", mut_const_plus_one);
        assert!(
            matches!(v, MutationVerdict::KernelRejected),
            "`{name}` +1 stays inside the carrier, so the KERNEL should be the one to catch it, \
             not a range refusal: {v:#?}"
        );
    }
    // `k` -> `k - 1`.
    for name in ["bump", "seven", "top8", "big", "deep"] {
        let v = assert_mutation_is_caught(env, name, "const: k -> k-1", mut_const_minus_one);
        assert!(
            matches!(v, MutationVerdict::KernelRejected),
            "`{name}` -1 stays inside the carrier, so the KERNEL should catch it: {v:#?}"
        );
    }

    // The two boundary shifts leave the carrier's value set. Caught, but by the
    // reflector's range check rather than by the kernel — recorded as such so
    // nobody later reads these as kernel evidence.
    let over =
        assert_mutation_is_caught(env, "top8", "const: 255 -> 256 (over)", mut_const_plus_one);
    assert!(
        matches!(over, MutationVerdict::Refused(Refusal::ConstantOutOfCarrierRange { .. })),
        "255 + 1 must be refused as out of the UInt8 carrier, NOT silently wrapped to 0: {over:#?}"
    );
    let under =
        assert_mutation_is_caught(env, "zero8", "const: 0 -> -1 (under)", mut_const_minus_one);
    assert!(
        matches!(under, MutationVerdict::Refused(Refusal::ConstantOutOfCarrierRange { .. })),
        "0 - 1 must be refused, NOT wrapped to 255: {under:#?}"
    );
}

/// MUTATION 5 — WIDEN `ICmpOp::Ult` to `ICmpOp::Ule`.
///
/// The most interesting of the five. For `if a < b then a else b` versus
/// `if a <= b then a else b` the two functions are EXTENSIONALLY EQUAL — both
/// are `min` — so nothing about the function's input/output behaviour
/// distinguishes them. Only the terms differ. A round trip that normalized "hard
/// enough", or that reasoned about behaviour rather than denotation, would
/// accept the mutant. The kernel must reject it on the term.
#[test]
fn test_mutation_ult_widened_to_ule() {
    let session = session_with(&[
        "def mn (a : UInt8) (b : UInt8) : UInt8 := if a < b then a else b",
        "def mn32 (a : UInt32) (b : UInt32) : UInt32 := if a < b then a else b",
        "def mn64 (a : UInt64) (b : UInt64) : UInt64 := if a < b then a else b",
    ]);
    let env = session.environment().expect("untainted session");
    for name in ["mn", "mn32", "mn64"] {
        let v = assert_mutation_is_caught(env, name, "icmp: ult -> ule (widened)", mut_ult_to_ule);
        assert!(
            matches!(v, MutationVerdict::KernelRejected),
            "`ule` is a fully supported opcode, so this must be the KERNEL rejecting a term, \
             never this file refusing an opcode: {v:#?}"
        );
    }

    // And the narrowing direction.
    let session = session_with(&[
        "def mnle (a : UInt8) (b : UInt8) : UInt8 := if a <= b then a else b",
        "def mnle64 (a : UInt64) (b : UInt64) : UInt64 := if a <= b then a else b",
    ]);
    let env = session.environment().expect("untainted session");
    for name in ["mnle", "mnle64"] {
        let v = assert_mutation_is_caught(env, name, "icmp: ule -> ult (narrowed)", mut_ule_to_ult);
        assert!(
            matches!(v, MutationVerdict::KernelRejected),
            "expected a kernel rejection: {v:#?}"
        );
    }
}

// ---- adjacent mutations, measured rather than assumed -------------------------

/// Bitwise `And` <-> `Or` at the integer carrier.
#[test]
fn test_mutation_bitwise_and_becomes_or() {
    let session = session_with(&[
        "def andf (a : UInt8) (b : UInt8) : UInt8 := a &&& b",
        "def and16 (a : UInt16) (b : UInt16) : UInt16 := a &&& b",
    ]);
    let env = session.environment().expect("untainted session");
    for name in ["andf", "and16"] {
        assert_mutation_is_caught(env, name, "binop: and -> or", mut_and_to_or);
    }
}

/// Swapping the operands of a COMMUTATIVE op.
///
/// Recorded separately because a survival here would NOT be a soundness defect:
/// `a + b` and `b + a` denote the same function, so accepting the mutant would
/// bless a body that is in fact correct. What the test measures is whether the
/// round trip is DEFINITIONAL (term-level) or EXTENSIONAL (behaviour-level).
/// Commutativity of `UIntw.add` is a propositional theorem, not a reduction
/// rule, so a definitional round trip must still reject it — and if that ever
/// stops being true, the round trip has acquired a normalization step powerful
/// enough that mutation 5 (`ult`/`ule`, also extensionally invisible) deserves
/// re-measuring.
#[test]
fn test_mutation_operand_swap_at_a_commutative_op() {
    let session = session_with(&[
        "def sum (a : UInt8) (b : UInt8) : UInt8 := a + b",
        "def prd (a : UInt8) (b : UInt8) : UInt8 := a * b",
        "def andf (a : UInt8) (b : UInt8) : UInt8 := a &&& b",
    ]);
    let env = session.environment().expect("untainted session");
    for name in ["sum", "prd", "andf"] {
        assert_mutation_is_caught(
            env,
            name,
            "binop: operands swapped at a COMMUTATIVE op",
            mut_swap_any_binop_operands,
        );
    }
}

/// Swapping the operands of a comparison, and replacing `Eq` with `Ult`.
#[test]
fn test_mutation_comparison_corrupted() {
    let session = session_with(&[
        "def mn (a : UInt8) (b : UInt8) : UInt8 := if a < b then a else b",
        "def mnle (a : UInt8) (b : UInt8) : UInt8 := if a <= b then a else b",
        "def eqp (a : UInt8) (b : UInt8) : UInt8 := if a = b then a else b",
    ]);
    let env = session.environment().expect("untainted session");
    for name in ["mn", "mnle", "eqp"] {
        assert_mutation_is_caught(env, name, "icmp: operands swapped", mut_swap_icmp_operands);
    }
    assert_mutation_is_caught(env, "eqp", "icmp: eq -> ult", mut_eq_to_ult);
}

/// `Mul` -> `Add`.
#[test]
fn test_mutation_mul_becomes_add() {
    let session = session_with(&[
        "def prd (a : UInt8) (b : UInt8) : UInt8 := a * b",
        "def poly (a : UInt8) (b : UInt8) : UInt8 := a * b + a - b",
        "def deep (a : UInt8) (b : UInt8) : UInt8 := (a + b) * (a - b) + (a * a) - 3",
    ]);
    let env = session.environment().expect("untainted session");
    for name in ["prd", "poly", "deep"] {
        assert_mutation_is_caught(env, name, "binop: mul -> add", mut_mul_to_add);
    }
}

// ---- the exhaustive sweep -----------------------------------------------------

/// EVERY mutator, at EVERY instruction, of EVERY coverage fixture.
///
/// The single-mutation tests above corrupt the FIRST matching instruction. That
/// leaves a real gap: a body with four binops is only tested at one of them, and
/// a reflector that read (say) only the last instruction's opcode and inferred
/// the rest would pass every test above. This sweep closes it by mutating each
/// instruction INDEX independently and requiring that no mutant anywhere in the
/// corpus is accepted.
///
/// It also guards its own non-vacuity three ways: it asserts each fixture's
/// PRISTINE body round-trips before mutating it, it discards any "mutant" equal
/// to the pristine body, and it fails if the distinct-mutant count collapses —
/// which is exactly what a fixture-shape change would look like, and which would
/// otherwise report a triumphant "0 survivors out of 0 mutants".
///
/// COST: ~110s (measured 2026-08-26, debug build). Nearly all of it is the
/// kernel: 72 mutants, each type-inferred and then `is_def_eq`-compared. That is
/// the price of asking the CIC kernel rather than a structural comparison, and
/// asking anything cheaper would be measuring something weaker.
#[test]
fn test_mutation_sweep_over_the_whole_corpus() {
    const CORPUS: &[(&str, &str)] = &[
        ("fst", "def fst (a : UInt8) (b : UInt8) : UInt8 := a"),
        ("snd", "def snd (a : UInt8) (b : UInt8) : UInt8 := b"),
        ("seven", "def seven : UInt8 := 7"),
        ("zero8", "def zero8 : UInt8 := 0"),
        ("top8", "def top8 : UInt8 := 255"),
        ("bump", "def bump (a : UInt8) : UInt8 := a + 7"),
        ("big", "def big : UInt64 := 1000000"),
        ("sum", "def sum (a : UInt8) (b : UInt8) : UInt8 := a + b"),
        ("dif", "def dif (a : UInt8) (b : UInt8) : UInt8 := a - b"),
        ("prd", "def prd (a : UInt8) (b : UInt8) : UInt8 := a * b"),
        ("poly", "def poly (a : UInt8) (b : UInt8) : UInt8 := a * b + a - b"),
        ("deep", "def deep (a : UInt8) (b : UInt8) : UInt8 := (a + b) * (a - b) + (a * a) - 3"),
        ("andf", "def andf (a : UInt8) (b : UInt8) : UInt8 := a &&& b"),
        ("orf", "def orf (a : UInt8) (b : UInt8) : UInt8 := a ||| b"),
        ("and16", "def and16 (a : UInt16) (b : UInt16) : UInt16 := a &&& b"),
        ("or64", "def or64 (a : UInt64) (b : UInt64) : UInt64 := a ||| b"),
        ("a32", "def a32 (a : UInt32) (b : UInt32) : UInt32 := a * b + a - b"),
        ("a64", "def a64 (a : UInt64) (b : UInt64) : UInt64 := a * b + a - b"),
        ("mn", "def mn (a : UInt8) (b : UInt8) : UInt8 := if a < b then a else b"),
        ("mnle", "def mnle (a : UInt8) (b : UInt8) : UInt8 := if a <= b then a else b"),
        ("mn32", "def mn32 (a : UInt32) (b : UInt32) : UInt32 := if a < b then a else b"),
        ("eqp", "def eqp (a : UInt8) (b : UInt8) : UInt8 := if a = b then a else b"),
        ("pick", "def pick (a : UInt8) (b : UInt8) (c : UInt8) : UInt8 := if a < b then a else c"),
    ];

    const MUTATORS: &[(&str, Mutator)] = &[
        ("select: arms swapped", mut_swap_select_arms),
        ("binop: add -> sub", mut_add_to_sub),
        ("binop: sub -> add", mut_sub_to_add),
        ("binop: mul -> add", mut_mul_to_add),
        ("binop: and -> or", mut_and_to_or),
        ("binop: or -> and", mut_or_to_and),
        ("binop: sub operands swapped", mut_swap_sub_operands),
        ("binop: operands swapped", mut_swap_any_binop_operands),
        ("const: k -> k+1", mut_const_plus_one),
        ("const: k -> k-1", mut_const_minus_one),
        ("icmp: ult -> ule", mut_ult_to_ule),
        ("icmp: ule -> ult", mut_ule_to_ult),
        ("icmp: eq -> ult", mut_eq_to_ult),
        ("icmp: operands swapped", mut_swap_icmp_operands),
    ];

    let sources: Vec<&str> = CORPUS.iter().map(|(_, src)| *src).collect();
    let session = session_with(&sources);
    let env = session.environment().expect("untainted session");

    let mut built = 0usize;
    let mut refused = 0usize;
    let mut rejected = 0usize;
    let mut survivors: Vec<String> = Vec::new();
    // Two mutators deliberately overlap (`sub operands swapped` is a special
    // case of `operands swapped`), and a third can coincide with them on a
    // particular instruction. Judging the same mutant twice would inflate the
    // count this test's own non-vacuity floor is read off, so distinct mutants
    // are counted once.
    let mut seen: std::collections::HashSet<String> = std::collections::HashSet::new();

    for (name, _) in CORPUS {
        let pristine = emitted(env, name);
        // The precondition, per fixture: no mutant of a body the kernel already
        // rejects is evidence of anything.
        let baseline = verdict_for(env, name, &pristine);
        assert!(
            baseline.is_accepted(),
            "`{name}` does NOT round-trip pristine ({}), so every mutation of it below would be \
             trivially 'caught'. Fix the baseline before reading this sweep as evidence.\n{baseline:#?}",
            baseline.tag()
        );

        for (label, mutate) in MUTATORS {
            for index in 0..pristine.blocks[0].body.len() {
                let mut mutant = pristine.clone();
                if !mutate(&mut mutant.blocks[0].body[index].inst) {
                    continue; // this mutator does not apply to this instruction
                }
                if mutant.blocks[0].body == pristine.blocks[0].body {
                    continue; // a no-op corruption tests nothing
                }
                if !seen.insert(format!("{name}|{:?}", mutant.blocks[0].body)) {
                    continue; // an identical mutant was already judged
                }
                built += 1;
                match verdict_for(env, name, &mutant) {
                    MutationVerdict::Refused(_) => refused += 1,
                    MutationVerdict::KernelRejected => rejected += 1,
                    MutationVerdict::KernelAccepted => {
                        survivors.push(format!("  {name} @ inst {index}: {label}"));
                    }
                }
            }
        }
    }

    eprintln!(
        "mutation sweep: {built} mutants — {rejected} rejected by the kernel, \
         {refused} refused by the reflector, {} SURVIVED",
        survivors.len()
    );

    // Non-vacuity of the sweep itself. If a fixture-shape change silently
    // stopped every mutator from applying, `built` would collapse and this
    // sweep would report a triumphant zero survivors out of zero mutants.
    // MEASURED 2026-08-26: 72 distinct mutants — 70 rejected by the kernel, 2
    // refused by the reflector (the two out-of-carrier constant shifts), 0
    // survived. The floor is set below that with margin, so a benign emitter
    // change that costs a mutation site does not fail the build, while a
    // collapse — a fixture shape change that stops the mutators applying, which
    // would otherwise report a triumphant "0 survivors out of 0" — does.
    assert!(
        built >= 60,
        "the sweep built only {built} distinct mutants; 72 were measured on 2026-08-26. Either \
         the corpus or the emitter's IR shape changed, and this sweep is no longer measuring what \
         it claims. Do NOT lower this floor to make the build green — re-measure and say so."
    );
    // The kernel, not this file's refusal list, must be doing most of the work.
    assert!(
        rejected >= built / 2,
        "only {rejected} of {built} mutants reached the kernel and were rejected there; the rest \
         were refused before the kernel saw them. The sweep is measuring this file's refusal \
         list more than it is measuring the round trip."
    );

    assert!(
        survivors.is_empty(),
        "\n\
         ════════════════════════════════════════════════════════════════════\n\
         {} MUTATION(S) SURVIVED out of {built}\n\
         ════════════════════════════════════════════════════════════════════\n\
         The kernel accepted the reflection of these CORRUPTED bodies against\n\
         their pristine declarations:\n{}\n",
        survivors.len(),
        survivors.join("\n")
    );
}

/// The sweep above would be worthless if `verdict_for` could never return
/// `KernelAccepted` at all — e.g. if a harness change made every reflection
/// fail to type-check. This asserts the positive direction is reachable through
/// the very same function the sweep judges mutants with.
#[test]
fn test_the_mutation_harness_can_still_say_yes() {
    let session = session_with(&[
        "def sum (a : UInt8) (b : UInt8) : UInt8 := a + b",
        "def mn (a : UInt8) (b : UInt8) : UInt8 := if a < b then a else b",
        "def deep (a : UInt8) (b : UInt8) : UInt8 := (a + b) * (a - b) + (a * a) - 3",
    ]);
    let env = session.environment().expect("untainted session");
    for name in ["sum", "mn", "deep"] {
        let v = verdict_for(env, name, &emitted(env, name));
        assert!(v.is_accepted(), "`{name}` must be accepted by the mutation harness: {v:#?}");
    }
}

/// THE MUTATION PROOF OF THE MUTATION BATTERY.
///
/// Twenty-nine green tests reporting "0 survivors" is exactly what a battery
/// whose survivor assertion CANNOT FIRE would also report. Every test above is
/// therefore conditional on this one: it drives a mutant that IS accepted
/// through `check_mutant` — the same function every other mutation test uses —
/// and requires the panic.
///
/// The known survivor is a REORDERING of two independent pure instructions. That
/// is a semantics-preserving change: the reflector substitutes definitions into
/// uses, so as long as every definition still precedes its uses, the order of
/// two instructions that do not depend on each other cannot affect the denoted
/// term. The kernel accepting it is CORRECT, not a defect — which is precisely
/// what makes it a safe positive control. It is a real accepted mutant, obtained
/// without weakening anything.
///
/// Recorded consequence, stated plainly so it is not mistaken for a gap later:
/// **instruction ORDER among mutually independent pure instructions is not
/// observable through this round trip.** It is not supposed to be. A reordering
/// is not a wrong body; it is the same body written down differently.
#[test]
fn test_the_battery_can_actually_see_a_survivor() {
    let session = session_with(&[
        "def deep (a : UInt8) (b : UInt8) : UInt8 := (a + b) * (a - b) + (a * a) - 3",
    ]);
    let env = session.environment().expect("untainted session");
    let pristine = emitted(env, "deep");
    assert!(
        verdict_for(env, "deep", &pristine).is_accepted(),
        "the pristine baseline must be accepted before a survivor means anything"
    );

    // Search for an adjacent swap that is semantics-preserving. Searching rather
    // than hardcoding an index means an emitter change that renumbers the body
    // makes this test look for a different pair instead of silently testing a
    // use-before-def refusal.
    let n = pristine.blocks[0].body.len();
    let mut survivor: Option<(usize, Function)> = None;
    for i in 0..n.saturating_sub(1) {
        let mut candidate = pristine.clone();
        candidate.blocks[0].body.swap(i, i + 1);
        if verdict_for(env, "deep", &candidate).is_accepted() {
            survivor = Some((i, candidate));
            break;
        }
    }
    let (at, survivor) = survivor.expect(
        "no semantics-preserving instruction reordering was found in `deep`, so this test cannot \
         supply a known survivor and the battery above is UNPROVEN. Do not delete this test to \
         make the suite green — find another accepted mutant.",
    );
    eprintln!("  positive control: reordering instructions {at}/{} of `deep` IS accepted", at + 1);

    // Now the point: `check_mutant` must PANIC on it.
    eprintln!("  (the panic printed below is EXPECTED — it is what this test asserts)");
    let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        check_mutant(env, "deep", "reordered two independent instructions", &pristine, &survivor)
    }));
    let payload = outcome.err().expect(
        "check_mutant ACCEPTED a mutant the kernel accepted, instead of panicking. The survivor \
         assertion in `check_mutant` cannot fire, so every '0 survivors' result in this file is \
         meaningless.",
    );
    let message = payload
        .downcast_ref::<String>()
        .cloned()
        .or_else(|| payload.downcast_ref::<&str>().map(|s| (*s).to_owned()))
        .unwrap_or_default();
    assert!(
        message.contains("MUTATION SURVIVED"),
        "check_mutant panicked, but not with the survivor diagnostic — so it may have failed for \
         an unrelated reason and the survivor path is still unproven. Message was: {message}"
    );
}
