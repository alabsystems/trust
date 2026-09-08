//! Recognition of the simplest E6 kernel-import body SHAPES from an extracted
//! [`VerifiableFunction`] — the soundness-critical trust boundary of the
//! compiler-side minting hook.
//!
//! Once a function is certified `Pure ∧ Total ∧ Deterministic ∧ NoPanic`, the
//! kernel-import step must turn its BODY into a defining equation the kernel
//! re-checks (see `trust_spec_elab::admit_constant_function` /
//! `admit_projection_function` and `docs/design-notes/2026-07-15-e6-kernel-import-spec.md`).
//! The correspondence between the minted definition and the function's actual
//! computation rests entirely on this recognition being FAITHFUL: a body that is
//! reported `ConstantUint { value }` must genuinely return exactly that constant.
//! So the recognizer is deliberately CONSERVATIVE — it matches only the two
//! simplest, unambiguous shapes and returns `None` (fail closed → no admission →
//! the call keeps failing closed) for anything else. Widening it (arithmetic,
//! select, `SwitchInt`) is future work, each shape added only when its
//! recognition is provably exact.
//!
//! A pure IR analysis with no `rustc` dependency, unit-testable in isolation.

use crate::{
    BasicBlock, BinOp, BlockId, ConstValue, Operand, Projection, Rvalue, Statement, Terminator, Ty,
    VerifiableFunction,
};

/// A body shape the kernel-import elaborator can turn into a defining equation.
/// Deliberately minimal; see the module docs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AdmissibleBody {
    /// The body returns exactly a machine-integer literal — `fn f() -> uN { V }`.
    ConstantUint {
        /// The returned value.
        value: u128,
        /// The width of the machine integer, in bits.
        width_bits: u32,
    },
    /// The body returns exactly a SIGNED machine-integer literal —
    /// `fn zero() -> i64 { 0 }`, `fn lo() -> i32 { -7 }`, `fn min() -> i64
    /// { i64::MIN }`. The signed sibling of [`AdmissibleBody::ConstantUint`]
    /// (signed-constant increment, 2026-08-26): measured at `-O`, such a body
    /// is the same one-block / one-statement `_0 = const V; return` shape, but
    /// the literal arrives as `ConstValue::Int` rather than `ConstValue::Uint`,
    /// which is the whole reason the four `CoeffDomain`/`Exact` `zero`/`one`
    /// impls of the veripb client were `admissible = true, recognize = None`.
    ///
    /// A SEPARATE variant rather than a widened `ConstantUint`, for two
    /// reasons that are not cosmetic:
    ///   * the two mint DIFFERENT kernel terms — `<Carrier>.ofNat n` at an
    ///     unsigned `UIntN` carrier versus `BitVec.ofNat N …` at the exact
    ///     two's-complement `BitVec N` carrier, with a negative literal going
    ///     through `Domain::negative_numeral`;
    ///   * a shared `value: u128` field would make `-1` and `u128::MAX` the
    ///     SAME body — exactly the collision [`CmpOperand::NegConst`] already
    ///     exists to avoid. The value is therefore carried as the `i128` it is.
    ///
    /// FAITHFULNESS. `Rvalue::Use` of a constant IS that constant, so a body
    /// that is exactly `_0 = const V` returns exactly `V`. The one thing a
    /// signed literal does NOT carry is its WIDTH (`ConstValue::Int(i128)` is
    /// width-less by construction — trust-mir-extract sign-extends the scalar
    /// to `i128` and drops the carrier), so the width is taken from the
    /// function's DECLARED return type, which the recognizer requires to be a
    /// signed carrier AND to agree with the return place `_0`'s own declared
    /// type. The value is then range-checked at that width, so a body whose
    /// literal does not fit the carrier it claims can never be reported here.
    /// Every deviation fails closed: an unsigned carrier, a `bool`/aggregate
    /// return, a projected place, a constant that is not the whole body, a
    /// non-`Return` terminator, and a malformed local table.
    ConstantInt {
        /// The returned value, as the SIGNED integer it is.
        value: i128,
        /// The width of the signed carrier, in bits — taken from the DECLARED
        /// return type, never from the constant.
        width_bits: u32,
    },
    /// The body returns one of its parameters verbatim — `fn f(.., x, ..) { x }`.
    /// `param` is the 0-based source parameter index.
    Projection {
        /// 0-based index of the returned parameter.
        param: usize,
    },
    /// The body reads ONE SCALAR FIELD of a by-value aggregate parameter and
    /// returns it — `fn degree_of(c: Cst) -> u64 { c.degree }` (E6/E9 widening
    /// increment 7). Both indices are 0-based: `param` is the source parameter,
    /// `field` its declared field position.
    ///
    /// FAITHFULNESS. `Rvalue::Use` of a place IS that place's value, so a body
    /// that is exactly `_0 = copy (_p.f)` returns exactly field `f` of
    /// parameter `p`. The recognizer additionally requires:
    ///   * the projection to be EXACTLY `[Field(f)]` — a `Deref` is refused, so
    ///     a `&Cst`/`&mut Cst` parameter never reaches this shape (its pointee
    ///     is not provably unchanged between entry and exit, and the clause
    ///     lane has no two-state reading for it);
    ///   * the local to be a source PARAMETER (`1..=arg_count`), never a
    ///     temporary, so the projected value is an input the clause can bind;
    ///   * the parameter's type to be a STRUCT (`variants` empty) — an enum's
    ///     field is variant-relative and would need a `Downcast`;
    ///   * the field's declared type to be exactly the function's return type,
    ///     so a same-shaped body at a different width cannot be admitted.
    ///
    /// The MINT is over the FLATTENED scalar parameter list (one binder per
    /// scalar field of every parameter): see
    /// `trust_spec_elab::admit_field_projection_function`. No aggregate ever
    /// reaches the kernel.
    FieldProjection {
        /// 0-based index of the aggregate source parameter.
        param: usize,
        /// 0-based declared field position within that parameter's struct.
        field: usize,
    },
    /// The body is a single WRAPPING binary arithmetic operation over two
    /// operands, each a parameter or a literal — `fn winc(x) { x.wrapping_add(1) }`,
    /// `fn wsum(x, y) { x.wrapping_add(y) }`. `wrapping_add`/`wrapping_sub`/
    /// `wrapping_mul` are recognized: the Machine-domain elaboration resolves
    /// `+`/`-`/`*` to the fixed-width WRAPPING carrier ops (`<Carrier>.add`/
    /// `.sub`/`.mul` — the `UInt64.sub` wrap is kernel-oracle-tested in
    /// trust-spec-elab), exactly the primitives' unsigned semantics. (An
    /// earlier note here claimed a truncating `-` under an
    /// `ofNat(Nat.op(toNat..))` encoding; that described a superseded
    /// encoding — corrected 2026-07-22 with the evidence cited above.)
    Arithmetic {
        /// The operation.
        op: ArithBinOp,
        /// Left operand.
        left: ArithOperand,
        /// Right operand.
        right: ArithOperand,
    },
    /// The body is a LINEAR CHAIN of wrapping-primitive calls composing one
    /// arithmetic expression over parameters and literals (E6 widening
    /// increment 3) — `fn f(x) { x.wrapping_add(1).wrapping_mul(2) }` as MIR
    /// lowers it: strictly consecutive call blocks, each feeding a fresh
    /// temporary, the last writing the return place. The composed tree is
    /// elaborated fully parenthesized over the SAME Machine-domain wrapping
    /// ops as [`AdmissibleBody::Arithmetic`], so faithfulness composes
    /// node-for-node from the single-op case.
    Composed {
        /// The composed expression tree.
        expr: ArithExpr,
    },
    /// The body compares two parameters and returns one of them — the
    /// `if <cmp> { p_then } else { p_else }` shape, of which `min`/`max` are
    /// canonical (`fn min2(a, b) { if a < b { a } else { b } }`). All indices are
    /// 0-based source parameters.
    Select {
        /// The comparison the branch tests.
        cmp: SelectCmp,
        /// Left operand parameter of the comparison.
        cmp_left: usize,
        /// Right operand parameter of the comparison.
        cmp_right: usize,
        /// Parameter returned when the comparison holds.
        then_param: usize,
        /// Parameter returned otherwise.
        else_param: usize,
    },
    /// The body compares a parameter against a machine-integer LITERAL and
    /// returns one of its parameters — the param-vs-const compare
    /// `if p_cmp <cmp> LIT { p_then } else { p_else }` (R2/C9), of which the
    /// threshold select `fn min10(a, b) { if a < 10 { a } else { b } }` and
    /// gcd's guard `if b == 0 { … }` are canonical.
    ///
    /// The literal is STRICTLY the comparison's RIGHT operand — a literal on
    /// the left (`if 10 < a`) has no arm and fails closed, the same
    /// unrepresentable-by-vocabulary rule the elaborator's
    /// `admit_select_literal_function` applies. Its encoded width must be
    /// exactly the function's unsigned return width, the same single-width
    /// anchor [`arith_operand`] uses, so a width-skewed constant can never
    /// recognize. The ARMS remain parameters only: constant arms stay outside
    /// the fragment (e6 probe f03's boundary is untouched).
    SelectLiteral {
        /// The comparison the branch tests.
        cmp: SelectCmp,
        /// Left operand parameter of the comparison.
        cmp_param: usize,
        /// The literal the parameter is compared against — the comparison's
        /// right operand, in range for the function's carrier width.
        literal: u128,
        /// Parameter returned when the comparison holds.
        then_param: usize,
        /// Parameter returned otherwise.
        else_param: usize,
    },


    /// The body compares two operands and returns the comparison ITSELF as
    /// `bool` — `fn le(a, b) -> bool { a <= b }` (E6 widening increment 5),
    /// `fn nonneg(x) -> bool { x >= 0 }` (increment 6). The shape guard-layer
    /// decision functions take: the whole computation is one MIR
    /// `BinaryOp(Lt|Le|Eq|Gt|Ge, operand, operand)` assigned to the return
    /// place, each operand a bare parameter or an integer literal
    /// ([`CmpOperand`]), and the recognizer additionally pins the declared
    /// return type to `bool`, so a same-shaped body at any other type fails
    /// closed.
    ComparisonBool {
        /// The comparison computed, after `>`/`>=` are normalized to `<`/`<=`
        /// by OPERAND SWAP (see [`comparison_cmp`]).
        cmp: SelectCmp,
        /// Left operand.
        left: CmpOperand,
        /// Right operand.
        right: CmpOperand,
    },
    /// The body is a boolean CONJUNCTION (`&&`) or DISJUNCTION (`||`) of two
    /// comparison LEAVES, each of which is individually an admissible
    /// [`AdmissibleBody::ComparisonBool`] shape returned as `bool` — the
    /// range-guard idiom `fn f(x) -> bool { LO <= x && x <= HI }` (E6 widening
    /// increment 7). Rust's `&&`/`||` never lower to a bitwise op in MIR; they
    /// lower to a SHORT-CIRCUIT DIAMOND, and the trust citation lane verifies
    /// the FULLY OPTIMIZED MIR (`TrustVerify` runs last, after
    /// `MatchBranchSimplification`, which only fuses two CONSTANT-bool arms —
    /// never a `false`/comparison pair). So this shape recognizes exactly that
    /// diamond:
    /// - entry: `_d = <cmpA>(..); switchInt(_d) -> [0: bb_zero, otherwise: bb_other]`
    /// - `&&`: `bb_zero` assigns `const false`, `bb_other` assigns `<cmpB>(..)`;
    ///   the result is `A && B`.
    /// - `||`: `bb_other` assigns `const true`, `bb_zero` assigns `<cmpB>(..)`;
    ///   the result is `A || B`.
    /// - both arms write the SAME place (the return place `_0` directly, or a
    ///   shared temp copied to `_0` in the join) and jump to the SAME `return`
    ///   join block.
    ///
    /// FAITHFULNESS: both operand subexpressions are PURE, PANIC-FREE
    /// comparisons already admissible as leaves, so `A && B` = `Bool.and A B`
    /// and `A || B` = `Bool.or A B` on every input (short-circuit is
    /// observationally identical to the strict connective when the right
    /// operand has no effect). The discriminant leaf is always `A` (the LHS,
    /// evaluated first); each leaf carries the SAME operand-swap normalization
    /// as [`AdmissibleBody::ComparisonBool`] and requires ≥1 parameter operand.
    /// Every deviation — a non-`bool` return, a projected operand or place, a
    /// non-comparison arm rvalue, a const arm that is not the connective's
    /// short-circuit constant, mismatched arm places/joins, an effectful
    /// sibling — fails closed.
    BoolBinary {
        /// The boolean connective: `&&` (`And`) or `||` (`Or`).
        op: BoolBinOp,
        /// The LEFT (first-evaluated, discriminant) comparison leaf `A`.
        left: ComparisonLeaf,
        /// The RIGHT (second-evaluated) comparison leaf `B`.
        right: ComparisonLeaf,
    },
    /// The body is a single overflow-CHECKED SIGNED arithmetic operation
    /// returning the std `Option<iN>` — `fn cadd(a: i64, b: i64) -> Option<i64>
    /// { a.checked_add(b) }` (checked-arithmetic admission increment). Two MIR
    /// spellings are recognized, both measured against the live `-O` pipeline
    /// (2026-08-25) and both fail-closed against every deviation
    /// ([`recognize_checked_arithmetic`]):
    ///
    /// **Shape A** — the un-inlined call: a two-block body whose entry `Call`s
    /// a compiler-marked [`crate::RustcCheckedPrimitiveMethod`] into the bare
    /// return place.
    ///
    /// **Shape B** — the inlined overflow-flag diamond, THE `-O` shape:
    /// ```text
    /// bb0: _t = CheckedBinaryOp(op, a, b)        // (iN, bool)
    ///      _r = (_t.0: iN)  _f = (_t.1: bool)
    ///      switchInt(_f) -> [0: bb_some, otherwise: bb_cold|bb_none]
    /// bb_cold: cold_path() -> bb_none            // optional hint block
    /// bb_none: _0 = Option::<iN>::None           // Aggregate variant 0, []
    /// bb_some: _0 = Option::<iN>::Some(_r)       // Aggregate variant 1, [_r]
    /// bb_join: return
    /// ```
    /// The discriminator against UNCHECKED `a + b` is the ABSENCE of any
    /// `Assert` terminator: unchecked arithmetic lowers to the same
    /// `CheckedBinaryOp` followed by `Assert(!flag)`, and any body containing
    /// an `Assert` is refused outright.
    ///
    /// FAITHFULNESS. `CheckedBinaryOp(op, a, b)` computes the `(wrapped
    /// result, overflow flag)` pair; the flag is true IFF the exact signed
    /// result does not fit `iN`. The recognized diamond returns `Some(wrapped
    /// result)` exactly on flag-false and `None` exactly on flag-true — which
    /// is exactly the total kernel model `checkedOpN` (exact `Int` arithmetic
    /// + a `fits` guard + wrapping re-embed). The `Some` payload is pinned to
    /// be EXACTLY the CheckedBinaryOp's result field (no aliasing), the
    /// variant indices are pinned to the Direct-tag std Option shape
    /// (`facet_inference::ty_is_std_option_of_signed` — every niche layout is
    /// refused), and the `0` switch edge is pinned to the `Some` arm.
    CheckedArithmetic {
        /// The checked operation.
        op: CheckedArithOp,
        /// The signed carrier width in bits (8/16/32/64/128).
        width_bits: u32,
        /// Left operand (the receiver of `a.checked_op(b)`).
        left: ArithOperand,
        /// Right operand.
        right: ArithOperand,
    },
    /// The body is a WIDTH-GUARDED NARROWING of one wide signed parameter into
    /// the std `Option<iN>` — `fn narrow(x: i128) -> Option<i64> { if x >=
    /// i64::MIN as i128 && x <= i64::MAX as i128 { Some(x as i64) } else
    /// { None } }` (the guarded-narrow / Option-consumer increment). This is
    /// the exact body of `veripb_core_proved::guard::narrow`, the width-guard
    /// choke point every soundness-path narrowing site routes through.
    ///
    /// MONOMORPHIC BY DESIGN this increment: `(from_bits, to_bits)` is
    /// `(128, 64)` and the bounds are the pinned `i64::MIN`/`i64::MAX`
    /// literals. Other widths and other bound pairs PARK — they are refused
    /// until a probe measures their MIR, exactly as the standing
    /// accept-only-measured-spellings discipline requires.
    ///
    /// Measured `-O` CFG (probe `c2`, 5 blocks; probe `c10` — the call-inlined
    /// `if fits_i64(x)` form that the real client body has — is the SAME
    /// diamond with the block order permuted and ONE bookkeeping `goto`
    /// trampoline on a false edge, so the recognizer chases EDGES and never
    /// block indices):
    /// ```text
    /// G1: _a = Ge(param, const -2^63 : i128)   switchInt(_a) [0 -> N*, otherwise -> G2]
    /// G2: _b = Le(param, const 2^63-1 : i128)  switchInt(_b) [0 -> N*, otherwise -> S]
    /// S : _t = param as i64 (IntToInt); _0 = Option::<i64>::Some(move _t); goto J
    /// N : _0 = const Option::<i64>::None;                                  goto J
    /// J : return
    /// ```
    /// (`N*` = possibly reached through a value-neutral `goto` trampoline.)
    ///
    /// FAITHFULNESS, and why the mint models TRUNCATION rather than identity.
    /// rustc's `IntToInt` i128→i64 cast is two's-complement TRUNCATION (the
    /// low 64 bits), which is `BitVec.ofNat 64 (BitVec.toNat x)` — and that is
    /// what the mint emits, UNCONDITIONALLY. Under the guard the truncation
    /// happens to be value-preserving, but no soundness is allowed to rest on
    /// that: the minted defining equation is exact on EVERY input, including
    /// the ones the guard rejects, so even a guard bug cannot make the model
    /// lie about the payload. The `Some`/`None` split is likewise exact:
    /// `Some` is produced on exactly the conjunction-true path, which the
    /// recognizer pins to be the `otherwise` edge of BOTH comparisons, while
    /// BOTH `0` edges must reach the SAME `None` block — so an arms-swapped
    /// body (`None` on the guard-true edge, the unsound shape) is structurally
    /// unrepresentable here, not merely unmatched. Every deviation listed on
    /// [`recognize_guarded_narrow`] fails closed.
    GuardedNarrow {
        /// The SOURCE signed width in bits — `128` only, this increment.
        from_bits: u32,
        /// The TARGET signed width in bits, i.e. the `Option<iN>` payload
        /// width — `64` only, this increment.
        to_bits: u32,
        /// 0-based index of the guarded-and-narrowed source parameter. Both
        /// comparison bounds and the cast source are pinned to be exactly this
        /// one parameter, so a multi-argument twin can never smuggle a
        /// guard-on-`x` / cast-of-`y` body past the recognizer.
        param: usize,
    },
    /// The body compares a WIDENED narrow parameter against a wide parameter
    /// and returns the comparison as `bool` — `fn eq_ok(machine: i64, truth:
    /// i128) -> bool { Wide::from(machine) == truth }` (the widening-cast
    /// comparison increment). This is the exact body of
    /// `veripb_core_proved::guard::eq_ok`, the checked-equality choke point
    /// every machine-computed degree passes through before the proved core
    /// will accept it.
    ///
    /// It is the ONE shape [`AdmissibleBody::ComparisonBool`] structurally
    /// cannot reach: its [`CmpOperand`]s are a parameter or a literal at ONE
    /// carrier, whereas here the two sides live at DIFFERENT widths
    /// (`BitVec 64` vs `BitVec 128`) and one of them is produced by a cast.
    ///
    /// MONOMORPHIC BY DESIGN this increment: `(from_bits, to_bits)` is
    /// `(64, 128)`, both SIGNED, the operation is `==` only, and both operands
    /// are bare parameters. Every other width pair, signedness pair,
    /// comparison, and operand shape PARKS — refused until a probe measures
    /// its MIR, exactly as the standing accept-only-measured-spellings
    /// discipline requires.
    ///
    /// Measured `-O` MIR (2026-08-26), ONE basic block, TWO value statements:
    /// ```text
    /// bb0: StorageLive(_3);
    ///      _3 = copy _1 as i128 (IntToInt);   // the sign-extending cast
    ///      _0 = Eq(move _3, copy _2);         // the mixed-width comparison
    ///      StorageDead(_3);
    ///      return;
    /// ```
    /// (`i128::from(machine)` and `machine as i128` measure IDENTICALLY at
    /// `-O`; the `From` impl is inlined to the same cast, leaving only a
    /// `scope` annotation the extractor drops.)
    ///
    /// FAITHFULNESS, and why the mint models SIGN EXTENSION. The extracted
    /// `Rvalue::Cast` does not carry rustc's `CastKind`, so the KIND is pinned
    /// by TYPES, exactly as [`recognize_guarded_narrow`] pins its truncation:
    /// an integer SOURCE (a declared `i64` PARAMETER local) and an integer
    /// TARGET (`i128`). The only rustc cast kind with an `iW → iN` signature
    /// is `IntToInt`, and `IntToInt` from a SIGNED source to a STRICTLY WIDER
    /// target is two's-complement SIGN EXTENSION — the value is preserved
    /// exactly, on every input, negatives included. That is what the mint
    /// emits, and it is why the source's signedness is pinned: a `u64` source
    /// at the identical MIR spelling would be ZERO extension, a different
    /// function on exactly the negative half of the domain, so it is refused
    /// rather than modeled. Likewise `from_bits < to_bits` is required: the
    /// reverse direction is truncation and belongs to the guarded-narrow lane.
    ///
    /// The comparison itself is the SAME `Eq` the
    /// [`AdmissibleBody::ComparisonBool`] lane already admits, evaluated at
    /// the WIDE carrier where both sides now live, so nothing new is claimed
    /// about equality — only about the cast. Every deviation listed on
    /// [`recognize_widened_eq`] fails closed.
    WidenedEq {
        /// The NARROW signed source width in bits — `64` only, this increment.
        from_bits: u32,
        /// The WIDE signed target width in bits — `128` only, this increment.
        to_bits: u32,
        /// 0-based index of the narrow parameter that is sign-extended.
        narrow_param: usize,
        /// 0-based index of the wide parameter it is compared against. Pinned
        /// distinct from `narrow_param`, and pinned to the target carrier.
        wide_param: usize,
        /// Whether the SIGN-EXTENDED side is the LEFT operand of the MIR `Eq`
        /// (`Wide::from(m) == t`) rather than the right (`t == Wide::from(m)`).
        /// Carried rather than normalized away: the minted `Eq` is spelled
        /// over `BitVec.toNat` of each side and is therefore not syntactically
        /// symmetric, so the mint must reproduce the source's operand order.
        cast_on_left: bool,
    },
    /// The body CONSTRUCTS A STRUCT and returns it, with each field built by a
    /// shape this recognizer already knows — `fn sat_term(degree, coeff, lit)
    /// -> Term { coeff: cap_coeff(degree, coeff), lit }`, which is the per-term
    /// step of every mapping rule (SATURATE, MULTIPLY, DIVIDE) once the leaf
    /// call is inlined at `-O`.
    ///
    /// The fields are carried INDIVIDUALLY, in declaration order, and no term
    /// is minted for the aggregate as a whole. That is the point: a clause on
    /// an aggregate return names `result.<i>`, never `result`, so what the
    /// discharge lane needs is field `i`'s defining expression — not a Clean
    /// structure for the client's ADT, which would require mapping every client
    /// type into the kernel.
    ///
    /// FAITHFULNESS. `Rvalue::Aggregate` of a struct writes exactly its
    /// operands into its fields, positionally, so field `i` of the returned
    /// value IS operand `i`. Each operand is then resolved to its own shape and
    /// carries that shape's own faithfulness argument. `fields.len()` equals the
    /// aggregate's operand count by construction, so index `i` here is field `i`
    /// there. Fail-closed on: an enum or union aggregate (a field is
    /// variant-relative, or aliases its siblings), a projected destination, any
    /// operand whose shape is not recognized, a non-`Return` terminator, and any
    /// effectful statement in the return block other than the aggregate store.
    AggregateFields {
        /// The shape of each field, in declaration order. `None` is a field
        /// this walk cannot shape -- a literal operand, or anything else it
        /// declines -- and it is carried rather than refusing the whole
        /// aggregate, because a SIBLING field may still be mintable. `pos(var)
        /// -> Lit { var, negated: false }` is the motivating case: `var` is a
        /// projection worth minting, `negated` is a constant this walk does not
        /// shape, and refusing both left `Lit::pos` uncontractable.
        fields: Vec<Option<AdmissibleBody>>,
    },
}

/// The operation of an [`AdmissibleBody::CheckedArithmetic`].
///
/// Deliberately its own enum rather than a reuse of [`ArithBinOp`]: the two
/// vocabularies mint DIFFERENT kernel semantics (wrapping vs checked-Option),
/// and a shared type would let one be passed where the other is meant without
/// a compile error. `Div`/`Rem`/`Shl`/`Shr`/`Neg` are deliberately absent
/// (no overflow-flag form / a different model — spec §2).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CheckedArithOp {
    /// `checked_add`
    Add,
    /// `checked_sub`
    Sub,
    /// `checked_mul`
    Mul,
}

/// The boolean connective of an [`AdmissibleBody::BoolBinary`].
///
/// `!=` and bitwise `&`/`|` are deliberately absent: this variant is reached
/// only from a short-circuit `&&`/`||` diamond, never from a bitwise op (which
/// would be a different source construct with its own recognition burden).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BoolBinOp {
    /// `&&`
    And,
    /// `||`
    Or,
}

/// One comparison LEAF of an [`AdmissibleBody::BoolBinary`] — structurally the
/// same as an [`AdmissibleBody::ComparisonBool`] body, reused as a sub-term.
/// `>`/`>=` are already normalized to `<`/`<=` by operand swap (see
/// [`comparison_cmp`]); at least one operand is a [`CmpOperand::Param`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ComparisonLeaf {
    /// The comparison, after `>`/`>=` normalization.
    pub cmp: SelectCmp,
    /// Left operand.
    pub left: CmpOperand,
    /// Right operand.
    pub right: CmpOperand,
}

/// An operand of an [`AdmissibleBody::ComparisonBool`].
///
/// A guard-layer decision is almost never two parameters: it is a parameter
/// against a BOUND (`x <= HI`, `LO <= x`, `x >= 0`), and rustc lowers a `const`
/// item to a plain constant operand rather than an `Rvalue::Cast`, so the bound
/// arrives here as a literal. At least one operand must still be a
/// [`Self::Param`]: two constants make the comparison constant-valued AND leave
/// no declared parameter type to fix the literals' carrier width, so that case
/// fails closed (mirroring `operands_have_same_comparable_ty`'s `(None, None)`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CmpOperand {
    /// A 0-based source parameter.
    Param(usize),
    /// A non-negative integer literal.
    Const(u128),
    /// A NEGATIVE integer literal, carried by MAGNITUDE.
    ///
    /// Signed literals extract as `ConstValue::Int(i128)` with no width
    /// (trust-mir-extract), so the magnitude is what survives; the mint routes
    /// it through `Domain::negative_numeral`, which range-checks it against the
    /// carrier and emits the two's-complement bit pattern. Carrying it as a
    /// wrapped `u128` instead would make `-1` and `u128::MAX` the same operand.
    NegConst(u128),
}

/// The comparison a [`AdmissibleBody::Select`] branch tests, and the one an
/// [`AdmissibleBody::ComparisonBool`] body computes.
///
/// Only the comparisons the elaborator's `decidable_comparison` supports. `!=`
/// is not among them and is not recognized in either shape. `>`/`>=` ARE
/// recognized in the comparison-to-bool shape, normalized to `<`/`<=` by
/// [`comparison_cmp`]'s operand swap — but deliberately NOT in the select
/// shape, whose branch arms are keyed to the `switchInt` edges and would have
/// to swap with them.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SelectCmp {
    /// `<`
    Lt,
    /// `<=`
    Le,
    /// `==`
    Eq,
}

/// A wrapping binary arithmetic operation in an [`AdmissibleBody::Arithmetic`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ArithBinOp {
    /// `wrapping_add`
    Add,
    /// `wrapping_sub` — admitted 2026-07-22 (E6 widening increment 1): the
    /// Machine-domain `-` elaboration is the fixed-width wrapping carrier
    /// sub, matching this primitive's unsigned semantics exactly.
    Sub,
    /// `wrapping_mul`
    Mul,
}

/// An operand of an [`AdmissibleBody::Arithmetic`] body.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ArithOperand {
    /// A 0-based source parameter.
    Param(usize),
    /// A machine-integer literal.
    Const(u128),
}

/// **THE ONE authenticated identity of a callee this lane may emit or read.**
///
/// # Why this exists, and why it is ONE thing rather than two fields
///
/// Landing 1 of §6f's general reflector expresses the emittable ladder as rows
/// in an instruction-selection table. The adversarial review of that design
/// recorded a specific way such a table manufactures a wrong binary: if a row
/// carries an `emit:` field naming what the emitter calls and a separate
/// `side_b:` field naming what the reader must find, then **one edit** can make
/// them disagree — the emitter emits `wrapping_sub`, the reader is told to look
/// for `wrapping_add`, the structural comparison agrees with itself, and the
/// kernel is handed a term about a call that was never emitted. Two adjacent
/// independently-authored fields are not two authorships; they are one edit.
///
/// So a selection row carries exactly ONE of these, and both directions DERIVE
/// from it:
///
/// * the EMITTER resolves a `DefId` from it (`resolve_core_wrapping_method` /
///   `resolve_bignum_method` in `clean_origin_mir.rs`, both keyed on this
///   value, never on a second spelling);
/// * the READER authenticates the extracted callee string through
///   [`PrimitiveCallee::classify`], which is the sole classifier
///   [`arith_method`] and [`bignum_callee`] are now expressed in terms of.
///
/// An emit/read callee disagreement is therefore unrepresentable rather than
/// merely discouraged.
///
/// # What this is NOT
///
/// It is **not** a table, and the reader does not consume the selection table.
/// The reader's DATAFLOW reading — which local holds what, which block is which
/// arm, which operand is which — stays entirely inside this crate, authored
/// independently of side A, exactly as it is today. That separation is the
/// double fault `docs/TCB.md` rests on ("a rendering bug alone is caught
/// structurally, a recognition bug alone is caught by the kernel") and this
/// type does not touch it: it fixes the NAME of a primitive, never the reading
/// of a body.
///
/// # Trust accounting, unchanged
///
/// The wrapping rows ride the closed compiler-authenticated marker
/// ([`crate::RustcTotalPrimitiveMethod`]); the bignum rows ride the exact
/// def-path strings plus carrier-typed locals, whose accounting is stated at
/// [`is_nat_carrier_ty`] — the name is not what makes admission sound, the
/// kernel gate is. Nothing about either accounting changes here; the strings
/// and the marker are the same ones, in one place instead of two.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PrimitiveCallee {
    /// `u{w}::wrapping_add`, marker-authenticated.
    WrappingAdd(u32),
    /// `u{w}::wrapping_sub`, marker-authenticated.
    WrappingSub(u32),
    /// `u{w}::wrapping_mul`, marker-authenticated.
    WrappingMul(u32),
    /// `trust_bignum::Nat::is_zero` — the emitted constructor split.
    NatIsZero,
    /// `trust_bignum::Nat::from_u64` — a `Nat` numeral.
    NatFromU64,
    /// `trust_bignum::Nat::sub` (or its `saturating_sub` alias) — Lean's
    /// truncated `Nat.sub`, the emitted predecessor at subtrahend 1.
    NatSub,
    /// `trust_bignum::Nat::add`.
    NatAdd,
    /// `trust_bignum::Nat::mul`. The `*` twin of [`Self::NatAdd`], added
    /// 2026-08-25 for the R2 factorial fragment. Its `impl` block is the same
    /// `mod arith` that declares `add`/`sub`, so it renders module-qualified
    /// for exactly the reason those two do — see [`bignum_callee`]'s note.
    NatMul,
    /// `trust_bignum::Nat::rem` — Lean's TOTAL `Nat.mod`, with `n % 0 = n`.
    /// Added 2026-08-28 by §R8; it is what makes the TEXTBOOK MODULO `gcd`
    /// (`if h : 0 < b then gcd b (a % b) else a`) reachable.
    ///
    /// **Its `impl` block is `mod divmod`, NOT `mod arith`** — so the
    /// module-qualified spelling is `trust_bignum::divmod::<impl
    /// trust_bignum::Nat>::rem`, and copying `arith` from the `add`/`sub`/`mul`
    /// rows would silently fail to classify every real extracted body. See
    /// [`bignum_callee`]'s note for why the module, not the method, decides the
    /// spelling.
    ///
    /// # Why this row does NOT carry a panic-freedom claim
    ///
    /// Rust's `%` panics at a zero divisor; `Nat.mod` is total. On the machine-
    /// width lane that divergence is REAL and the faithfulness gate is blind to
    /// it — `fa788aab89`, re-measured live in `r8_nat_mod_probes::q6` — which is
    /// why `recognise_raw_binop_expr` still refuses a symbolic divisor at
    /// `UInt{N}` and why widening it would be unsound.
    ///
    /// This identity is a different lane, and the difference is not the gate's
    /// power: **there is no emitted panic path here at all.** The realization is
    /// `Call(Fixed(NatRem))`, `TemplateTerminator` has no `Assert` variant, and
    /// `Nat::rem` is `checked_div_rem(..)`-with-fallback-to-the-dividend by
    /// construction. What replaces panic-freedom is TOTALITY AGREEMENT of the
    /// carrier, and it is NOT carried by a `Faithful` token — the kernel cannot
    /// even state it at an open dividend (`∀ a, a % 0 = a` by `rfl` is REFUSED,
    /// `r8_nat_mod_probes::q2`). It is carried by
    /// `trust-bignum/tests/kernel_differential.rs`'s
    /// `the_division_by_zero_lane_is_measured_not_assumed`, which reduces
    /// `Nat.mod` in the REAL Clean `TypeChecker` at a zero divisor and asserts
    /// the runtime agrees, plus this type's authenticated-callee TCB row. The
    /// `nat.mod` selection row says so in its `tcb_row`, and `docs/TCB.md`
    /// carries it. **This is no NEW kind of trust:** [`Self::NatSub`] already
    /// rests on exactly it (`Nat::sub` is `checked_sub().unwrap_or(ZERO)`, which
    /// truncates where Rust's `-` would underflow-panic).
    ///
    /// The obligation the compiler DOES discharge on this lane is the DECREASE
    /// — `a % b < b` needs `0 < b`, the textbook `dite` puts it in scope, and
    /// `Nat.mod_lt … h` is visibly in the elaborated term (`q4`). A guard on the
    /// wrong value, or one that does not dominate the division, is REFUSED
    /// (`q5`). That is the real obligation with a real undischarged case.
    NatRem,
}

impl PrimitiveCallee {
    /// The identity a callee def path denotes, or `None` (fail closed).
    ///
    /// The ONLY classifier. [`arith_method`] and [`bignum_callee`] are views of
    /// it, so a widening here is a widening of both and cannot be a widening of
    /// one.
    #[must_use]
    pub fn classify(callee: &str) -> Option<Self> {
        if let Some(marked) = crate::RustcTotalPrimitiveMethod::classify(callee) {
            return Some(match marked {
                crate::RustcTotalPrimitiveMethod::WrappingAdd(width) => Self::WrappingAdd(width),
                crate::RustcTotalPrimitiveMethod::WrappingSub(width) => Self::WrappingSub(width),
                crate::RustcTotalPrimitiveMethod::WrappingMul(width) => Self::WrappingMul(width),
            });
        }
        match callee {
            // Root-module impl, co-located with `Nat` — one spelling, and it is
            // the one measured. See [`bignum_callee`]'s note for why no
            // module-qualified row is invented for these two.
            "trust_bignum::Nat::is_zero" => Some(Self::NatIsZero),
            "trust_bignum::Nat::from_u64" => Some(Self::NatFromU64),
            // `saturating_sub` is a doc-level alias of `sub` in trust-bignum;
            // both spell Lean's truncated `Nat.sub`.
            "trust_bignum::Nat::sub"
            | "trust_bignum::Nat::saturating_sub"
            | "trust_bignum::arith::<impl trust_bignum::Nat>::sub"
            | "trust_bignum::arith::<impl trust_bignum::Nat>::saturating_sub" => Some(Self::NatSub),
            "trust_bignum::Nat::add" | "trust_bignum::arith::<impl trust_bignum::Nat>::add" => {
                Some(Self::NatAdd)
            }
            "trust_bignum::Nat::mul" | "trust_bignum::arith::<impl trust_bignum::Nat>::mul" => {
                Some(Self::NatMul)
            }
            // `divmod`, NOT `arith` — `rem`'s `impl` block is the one in
            // `trust_bignum/src/divmod.rs`. `Nat::div` is deliberately absent:
            // nothing in the emittable fragment names `/`, and an unreachable
            // accepted callee is surface the gate would have to defend for no
            // capability.
            "trust_bignum::Nat::rem" | "trust_bignum::divmod::<impl trust_bignum::Nat>::rem" => {
                Some(Self::NatRem)
            }
            _ => None,
        }
    }

    /// The Rust METHOD NAME this identity resolves to at the emitter.
    ///
    /// This is the emitter's half of the one identity: `clean_origin_mir.rs`
    /// resolves a `DefId` by looking this name up on the primitive's or the
    /// carrier's inherent impls and then AUTHENTICATING the candidate, never by
    /// matching a path string. The distinction matters and is recorded at
    /// `resolve_bignum_method`: side A must not mirror side B's table, because
    /// "side A asserting what side B will accept is exactly the independence
    /// the gate exists to have". A method NAME is not a path — the extractor
    /// re-renders the path from `TyCtxt` facts at read-back, independently, and
    /// side B classifies THAT.
    #[must_use]
    pub fn rust_method_name(self) -> &'static str {
        match self {
            Self::WrappingAdd(_) => "wrapping_add",
            Self::WrappingSub(_) => "wrapping_sub",
            Self::WrappingMul(_) => "wrapping_mul",
            Self::NatIsZero => "is_zero",
            Self::NatFromU64 => "from_u64",
            Self::NatSub => "sub",
            Self::NatAdd => "add",
            Self::NatMul => "mul",
            Self::NatRem => "rem",
        }
    }

    /// The unsigned machine width this identity is at, for the marker-
    /// authenticated core primitives. `None` for the bignum carrier, which is
    /// width-free by construction — that is what makes it exact.
    #[must_use]
    pub fn machine_width(self) -> Option<u32> {
        match self {
            Self::WrappingAdd(width) | Self::WrappingSub(width) | Self::WrappingMul(width) => {
                Some(width)
            }
            Self::NatIsZero
            | Self::NatFromU64
            | Self::NatSub
            | Self::NatAdd
            | Self::NatMul
            | Self::NatRem => None,
        }
    }

    /// One path spelling that [`Self::classify`] maps back to `self`.
    ///
    /// Exists for the round-trip control (`classify(canonical_path(r)) == r`
    /// for every row), which is what makes "one identity" a checked statement
    /// rather than a comment. It is NOT the only accepted spelling — the
    /// bignum ops render module-qualified when their `impl` block does — and it
    /// is never used to decide admission.
    #[must_use]
    pub fn canonical_path(self) -> String {
        let prefix = crate::TRUST_RUSTC_TOTAL_PRIMITIVE_METHOD_PATH_PREFIX;
        match self {
            Self::WrappingAdd(width) => {
                format!("{prefix}core::num::<impl u{width}>::wrapping_add")
            }
            Self::WrappingSub(width) => {
                format!("{prefix}core::num::<impl u{width}>::wrapping_sub")
            }
            Self::WrappingMul(width) => {
                format!("{prefix}core::num::<impl u{width}>::wrapping_mul")
            }
            Self::NatIsZero => "trust_bignum::Nat::is_zero".to_owned(),
            Self::NatFromU64 => "trust_bignum::Nat::from_u64".to_owned(),
            Self::NatSub => "trust_bignum::Nat::sub".to_owned(),
            Self::NatAdd => "trust_bignum::Nat::add".to_owned(),
            Self::NatMul => "trust_bignum::Nat::mul".to_owned(),
            Self::NatRem => "trust_bignum::Nat::rem".to_owned(),
        }
    }
}

/// Whether a statement has NO effect on any value — pure bookkeeping the
/// recognizer may skip. Anything NOT on this whitelist is treated as effectful,
/// so a body carrying it fails to match (fail closed); the list only ever grows
/// with statements that are provably value-neutral.
/// The `(0-based source parameter, 0-based declared field)` a place denotes,
/// when it is exactly ONE named-struct field read of a by-value parameter whose
/// declared field type is the function's return type — and `None` for every
/// other place.
///
/// Fail-closed on: any projection other than a single `Field` (notably `Deref`,
/// which is how a `&Cst` parameter would arrive — its pointee is not provably
/// unchanged across the call, so it stays outside this increment); a non-
/// parameter local; a non-`Adt` or ENUM-typed parameter (an enum field is
/// variant-relative and reached through a `Downcast`); an out-of-range field
/// index; and a field whose declared type differs from the return type.
fn param_struct_field(func: &VerifiableFunction, place: &crate::Place) -> Option<(usize, usize)> {
    let [Projection::Field(field)] = place.projections.as_slice() else {
        return None;
    };
    if place.local < 1 || place.local > func.body.arg_count {
        return None;
    }
    let local = func.body.locals.iter().find(|l| l.index == place.local)?;
    let Ty::Adt { fields, variants, .. } = &local.ty else {
        return None;
    };
    if !variants.is_empty() {
        return None;
    }
    let (_, field_ty) = fields.get(*field)?;
    if *field_ty != func.body.return_ty {
        return None;
    }
    Some((place.local - 1, *field))
}

fn is_value_neutral(stmt: &Statement) -> bool {
    matches!(
        stmt,
        Statement::StorageLive(_)
            | Statement::StorageDead(_)
            | Statement::PlaceMention(_)
            | Statement::Retag { .. }
            | Statement::Coverage
            | Statement::ConstEvalCounter
            | Statement::Nop
    )
}

/// Recognize a [`VerifiableFunction`] whose body is one of the [`AdmissibleBody`]
/// shapes, or `None` (fail closed). CONSERVATIVE: requires a single basic block
/// that `Return`s after exactly one value-carrying statement — an assignment of
/// a constant or a bare parameter to the return place (`_0`). See the module
/// docs for why faithfulness here is soundness-critical.
#[must_use]
pub fn recognize_admissible_body(func: &VerifiableFunction) -> Option<AdmissibleBody> {
    // Keep the soundness-critical admission boundary total over the explicit
    // TailCall variant.  Its successful-return semantics are exactly an
    // ordinary call writing `_0` followed by Return; presenting that canonical
    // view prevents both wildcard omission and a second, divergent recognizer.
    let expanded = func.with_tail_calls_expanded();
    let func = expanded.as_ref();

    recognize_single_block(func)
        .or_else(|| recognize_arithmetic(func))
        .or_else(|| recognize_select(func))
        .or_else(|| recognize_bool_binary(func))
        .or_else(|| recognize_use_chain(func))
        .or_else(|| recognize_call_chain(func))
        .or_else(|| recognize_checked_arithmetic(func))
        .or_else(|| recognize_guarded_narrow(func))
        .or_else(|| recognize_widened_eq(func))
        .or_else(|| recognize_aggregate_fields(func))
}

/// Linear wrapping-call chain (E6 widening increment 3, 2026-07-22): N ≥ 2
/// consecutive call blocks — each a `core::num` wrapping primitive whose
/// operands are literals, parameters, or PRIOR chain temporaries, whose
/// destination is a fresh bare temporary (never rewritten), and whose target
/// is exactly the next block — with the LAST call writing the bare return
/// place and targeting a bookkeeping-only `Return` block.
///
/// FAITHFULNESS: each node is the recognized primitive (the same
/// [`arith_method`] gate as the single-call shape), operands resolve to the
/// values the temporaries carry by construction (single assignment, linear
/// control flow, value-neutral statements only), so the composed tree IS the
/// body's dataflow; the elaborator renders it fully parenthesized over the
/// same Machine-domain wrapping ops. Fail-closed on: any non-primitive
/// callee, any branching/diverging/reordered target, any projected place,
/// any temporary rewrite, any read of an unresolved local, and fewer than
/// two calls (the single-call shape stays with [`recognize_arithmetic`]).
fn recognize_call_chain(func: &VerifiableFunction) -> Option<AdmissibleBody> {
    let blocks = &func.body.blocks;
    if blocks.len() < 3 {
        return None;
    }
    let (ret_blk, call_blks) = blocks.split_last()?;
    if !matches!(ret_blk.terminator, Terminator::Return)
        || ret_blk.stmts.iter().any(|s| !is_value_neutral(s))
    {
        return None;
    }
    if call_blks.len() < 2 {
        return None;
    }
    let mut env: std::collections::BTreeMap<usize, ArithExpr> = (1..=func.body.arg_count)
        .map(|i| (i, ArithExpr::Operand(ArithOperand::Param(i - 1))))
        .collect();
    let mut result: Option<ArithExpr> = None;
    let mut chain_width: Option<u32> = None;
    for (index, blk) in call_blks.iter().enumerate() {
        if blk.stmts.iter().any(|s| !is_value_neutral(s)) {
            return None;
        }
        let Terminator::Call { func: callee, args, dest, target, .. } = &blk.terminator else {
            return None;
        };
        let next = blocks.get(index + 1)?;
        if *target != Some(next.id) || !dest.projections.is_empty() {
            return None;
        }
        let (op, width) = arith_method(callee)?;
        if chain_width.is_some_and(|prior| prior != width)
            || !function_returns_unsigned_width(func, width)
            || !bare_local_has_unsigned_width(func, dest.local, width)
        {
            return None;
        }
        chain_width = Some(width);
        let resolve = |operand: &Operand| -> Option<ArithExpr> {
            match operand {
                Operand::Constant(ConstValue::Uint(value, encoded_width))
                    if *encoded_width == width && uint_fits_width(*value, width) =>
                {
                    u128::try_from(*value).ok().map(|v| ArithExpr::Operand(ArithOperand::Const(v)))
                }
                Operand::Copy(p) | Operand::Move(p) => {
                    if !p.projections.is_empty()
                        || !bare_local_has_unsigned_width(func, p.local, width)
                    {
                        return None;
                    }
                    env.get(&p.local).cloned()
                }
                _ => None,
            }
        };
        let [a, b] = &args[..] else {
            return None;
        };
        let node = ArithExpr::Bin { op, left: Box::new(resolve(a)?), right: Box::new(resolve(b)?) };
        let is_last = index == call_blks.len() - 1;
        if dest.local == 0 {
            if !is_last {
                return None; // the return place is written only by the LAST call
            }
            result = Some(node);
        } else {
            if is_last {
                return None; // the last call must produce the return value
            }
            if env.insert(dest.local, node).is_some() {
                return None; // temporary rewrite — single assignment only
            }
        }
    }
    Some(AdmissibleBody::Composed { expr: result? })
}

/// Multi-statement straight-line `Use`-chain (E6 widening increment 2,
/// 2026-07-22): a single returning block whose every value statement assigns
/// a constant or an already-resolved bare local (`Copy`/`Move`) to a bare
/// local — value-identity copies through temporaries, resolved by
/// substitution to the SAME `ConstantUint`/`Projection` shapes the
/// single-statement recognizer emits (no new admission vocabulary, no
/// elaborator change).
///
/// FAITHFULNESS: `Rvalue::Use` is value identity, so `_0`'s final value is
/// exactly the resolution of its LAST write through the chain, and every
/// non-bookkeeping statement is such a copy — no other effect exists to
/// misrepresent. Fail-closed on: any projection (read or write side), any
/// non-`Use` rvalue, any read of a local without a resolved value (including
/// reads of `_0` itself — untracked by construction), and a body that never
/// writes `_0`. Requires at least TWO value statements so the
/// single-statement shape stays owned by [`recognize_single_block`] and
/// previously-admitted bodies keep their recognizer unchanged.
fn recognize_use_chain(func: &VerifiableFunction) -> Option<AdmissibleBody> {
    let [block] = &func.body.blocks[..] else {
        return None;
    };
    if !matches!(block.terminator, Terminator::Return) {
        return None;
    }
    #[derive(Clone, Copy)]
    enum Resolved {
        Const { value: u128, width_bits: u32 },
        Param(usize),
    }
    let mut env: std::collections::BTreeMap<usize, Resolved> =
        (1..=func.body.arg_count).map(|i| (i, Resolved::Param(i - 1))).collect();
    let mut ret: Option<Resolved> = None;
    let mut value_stmts = 0usize;
    for stmt in &block.stmts {
        if is_value_neutral(stmt) {
            continue;
        }
        value_stmts += 1;
        let Statement::Assign { place, rvalue, .. } = stmt else {
            return None;
        };
        if !place.projections.is_empty() {
            return None;
        }
        let value = match rvalue {
            Rvalue::Use(Operand::Constant(ConstValue::Uint(value, width_bits))) => {
                Resolved::Const { value: *value, width_bits: *width_bits }
            }
            Rvalue::Use(Operand::Copy(p)) | Rvalue::Use(Operand::Move(p)) => {
                if !p.projections.is_empty() {
                    return None;
                }
                *env.get(&p.local)?
            }
            _ => return None,
        };
        if place.local == 0 {
            ret = Some(value);
        } else {
            env.insert(place.local, value);
        }
    }
    if value_stmts < 2 {
        return None;
    }
    match ret? {
        Resolved::Const { value, width_bits } => {
            Some(AdmissibleBody::ConstantUint { value, width_bits })
        }
        Resolved::Param(param) => Some(AdmissibleBody::Projection { param }),
    }
}

/// The single wrapping-arithmetic shape: a two-block body whose entry is a
/// `Call` to a compiler-authenticated primitive
/// `wrapping_add`/`wrapping_sub`/`wrapping_mul` on two operands (each a
/// parameter or a literal), assigned to the return place, returning in the
/// next block. Fail-closed on anything else: unmarked or malformed paths,
/// excluded carriers, width/type disagreement, and user functions merely
/// named like a primitive.
fn recognize_arithmetic(func: &VerifiableFunction) -> Option<AdmissibleBody> {
    let [call_blk, ret_blk] = &func.body.blocks[..] else {
        return None;
    };
    if !matches!(ret_blk.terminator, Terminator::Return)
        || ret_blk.stmts.iter().any(|s| !is_value_neutral(s))
        || call_blk.stmts.iter().any(|s| !is_value_neutral(s))
    {
        return None;
    }
    let Terminator::Call { func: callee, args, dest, target, .. } = &call_blk.terminator else {
        return None;
    };
    if dest.local != 0 || !dest.projections.is_empty() || *target != Some(ret_blk.id) {
        return None;
    }
    let [op1, op2] = &args[..] else {
        return None;
    };
    let (op, width) = arith_method(callee)?;
    if !function_returns_unsigned_width(func, width)
        || !bare_local_has_unsigned_width(func, dest.local, width)
    {
        return None;
    }
    Some(AdmissibleBody::Arithmetic {
        op,
        left: arith_operand(op1, func, width)?,
        right: arith_operand(op2, func, width)?,
    })
}

/// The wrapping arithmetic operation and width a callee denotes, requiring the
/// closed compiler-authenticated primitive-method marker so a same-named user
/// function or serialized lookalike is not matched.
///
/// `wrapping_sub` ADMITTED (E6 widening increment 1, 2026-07-22): the former
/// exclusion note ("its encoding does not match the machine `-` elaboration")
/// predated trust-spec-elab's machine-subtraction landing. Today the Machine
/// domain elaborates `-` as the fixed-width WRAPPING carrier sub
/// (trust-spec-elab lib.rs "`-` denotes the DOMAIN's subtraction: … wrapping
/// `<Carrier>.sub` over a machine domain"), which is exactly
/// `u{8,16,32,64}::wrapping_sub`'s semantics — and `ty_to_domain` already
/// restricts admission to UNSIGNED carriers, so the signed case never
/// reaches this recognizer's consumers. Faithfulness pinned by
/// `widening_battery_census_targets_currently_refuse`'s flipped first pin.
///
/// A VIEW of [`PrimitiveCallee::classify`], never a second classifier — see
/// that type's docs for why the emitted and read spellings of a primitive must
/// be one thing.
fn arith_method(callee: &str) -> Option<(ArithBinOp, u32)> {
    match PrimitiveCallee::classify(callee)? {
        PrimitiveCallee::WrappingAdd(width) => Some((ArithBinOp::Add, width)),
        PrimitiveCallee::WrappingSub(width) => Some((ArithBinOp::Sub, width)),
        PrimitiveCallee::WrappingMul(width) => Some((ArithBinOp::Mul, width)),
        PrimitiveCallee::NatIsZero
        | PrimitiveCallee::NatFromU64
        | PrimitiveCallee::NatSub
        | PrimitiveCallee::NatAdd
        | PrimitiveCallee::NatMul
        | PrimitiveCallee::NatRem => None,
    }
}

/// A composed wrapping-arithmetic expression tree (see
/// [`AdmissibleBody::Composed`]).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ArithExpr {
    /// A leaf operand.
    Operand(ArithOperand),
    /// A wrapping binary node.
    Bin {
        /// The operation.
        op: ArithBinOp,
        /// Left subtree.
        left: Box<ArithExpr>,
        /// Right subtree.
        right: Box<ArithExpr>,
    },
}

/// An arithmetic operand: a bare parameter (`1..=arg_count`) or a machine-integer
/// literal.
fn bare_local_has_unsigned_width(func: &VerifiableFunction, local: usize, width: u32) -> bool {
    func.body
        .locals
        .get(local)
        .is_some_and(|decl| decl.index == local && decl.ty == Ty::Int { width, signed: false })
}

fn function_returns_unsigned_width(func: &VerifiableFunction, width: u32) -> bool {
    func.body.return_ty == Ty::Int { width, signed: false }
        && bare_local_has_unsigned_width(func, 0, width)
}

fn uint_fits_width(value: u128, width: u32) -> bool {
    width == 128 || value < (1_u128 << width)
}

/// The SIGNED carrier width this function returns, or `None` (fail closed).
///
/// Requires BOTH the declared return type and the return place `_0`'s own
/// declared type to be the same signed `Ty::Int` — an unsigned carrier, a
/// `bool`, an aggregate, or a local table that disagrees with the signature
/// all answer `None`. This is the sole source of width for a
/// [`AdmissibleBody::ConstantInt`], whose literal carries none.
fn function_returns_signed_width(func: &VerifiableFunction) -> Option<u32> {
    let Ty::Int { width, signed: true } = func.body.return_ty else {
        return None;
    };
    bare_local_has_signed_width(func, 0, width).then_some(width)
}

/// Whether `value` is representable in a two's-complement `iN`, i.e. lies in
/// `[-2^(N-1), 2^(N-1) - 1]`. Widths outside `1..=128` answer `false` rather
/// than shifting out of range.
fn int_fits_signed_width(value: i128, width: u32) -> bool {
    if width == 128 {
        return true;
    }
    if width == 0 || width > 128 {
        return false;
    }
    let bound = 1_i128 << (width - 1);
    value >= -bound && value < bound
}

fn arith_operand(op: &Operand, func: &VerifiableFunction, width: u32) -> Option<ArithOperand> {
    match op {
        Operand::Copy(p) | Operand::Move(p)
            if p.projections.is_empty()
                && p.local >= 1
                && p.local <= func.body.arg_count
                && bare_local_has_unsigned_width(func, p.local, width) =>
        {
            Some(ArithOperand::Param(p.local - 1))
        }
        Operand::Constant(ConstValue::Uint(v, encoded_width))
            if *encoded_width == width && uint_fits_width(*v, width) =>
        {
            Some(ArithOperand::Const(*v))
        }
        _ => None,
    }
}

/// The single-block shapes: a constant return, a bare-parameter projection,
/// or a comparison of two parameters returned as `bool`.
fn recognize_single_block(func: &VerifiableFunction) -> Option<AdmissibleBody> {
    // Exactly one basic block, returning.
    let [block] = &func.body.blocks[..] else {
        return None;
    };
    if !matches!(block.terminator, Terminator::Return) {
        return None;
    }
    // Exactly one non-bookkeeping statement.
    let mut effectful = block.stmts.iter().filter(|s| !is_value_neutral(s));
    let assign = effectful.next()?;
    if effectful.next().is_some() {
        return None;
    }
    // …an assignment to the return place `_0` (a bare local, no projections).
    let Statement::Assign { place, rvalue, .. } = assign else {
        return None;
    };
    if place.local != 0 || !place.projections.is_empty() {
        return None;
    }
    match rvalue {
        // `_0 = const V` — a machine-integer literal return.
        Rvalue::Use(Operand::Constant(ConstValue::Uint(value, width_bits))) => {
            Some(AdmissibleBody::ConstantUint { value: *value, width_bits: *width_bits })
        }
        // `_0 = const V_iN` — a SIGNED machine-integer literal return (the
        // signed-constant increment). See [`AdmissibleBody::ConstantInt`]: the
        // literal is width-LESS, so the carrier comes from the declared return
        // type (pinned signed, and pinned to agree with `_0`'s own declared
        // type), and the value is range-checked against it.
        Rvalue::Use(Operand::Constant(ConstValue::Int(value))) => {
            let width_bits = function_returns_signed_width(func)?;
            if !int_fits_signed_width(*value, width_bits) {
                return None;
            }
            Some(AdmissibleBody::ConstantInt { value: *value, width_bits })
        }
        // `_0 = _i` (copy/move a bare parameter local) — a projection. Parameters
        // are locals `1..=arg_count` (local `0` is the return place), so a
        // returned local `i` in that range is 0-based source parameter `i-1`.
        Rvalue::Use(Operand::Copy(p)) | Rvalue::Use(Operand::Move(p)) => {
            if p.projections.is_empty() && p.local >= 1 && p.local <= func.body.arg_count {
                Some(AdmissibleBody::Projection { param: p.local - 1 })
            } else {
                // `_0 = _p.f` — the field-projection shape. See
                // [`AdmissibleBody::FieldProjection`] for what each gate buys.
                param_struct_field(func, p)
                    .map(|(param, field)| AdmissibleBody::FieldProjection { param, field })
            }
        }
        // `_0 = Lt|Le|Eq|Gt|Ge(operand, operand)` at declared return type
        // `bool` — the comparison-to-bool shape (E6 widening increment 5).
        // FAITHFULNESS: a MIR comparison `BinaryOp` IS the returned value (no
        // branch, no temp), each operand is a bare parameter local or an
        // integer literal, the declared return type is pinned to `bool` so a
        // lookalike at another type — or through a projected place — fails
        // closed, and `>`/`>=` are normalized by OPERAND SWAP, never by
        // negation (`a > b` ≡ `b < a` holds at a total order; a negated
        // reading would additionally have to know the order is total AND would
        // mint a different term from the one the clause lane emits for the
        // same source). `!=` stays unrecognized: it has no `SelectCmp`, and
        // guessing `Bool.not (decide (Eq ..))` here would be a mint the
        // recognizer's name does not describe.
        Rvalue::BinaryOp(binop, opl, opr) => {
            if func.body.return_ty != Ty::Bool {
                return None;
            }
            // Shared leaf recognition (operand swap + ≥1-parameter rule) with
            // the bool-binary shape, so a standalone comparison and one arm of
            // an `&&`/`||` are admitted by identical rules — see
            // [`comparison_leaf`].
            let ComparisonLeaf { cmp, left, right } =
                comparison_leaf(binop, opl, opr, func.body.arg_count)?;
            Some(AdmissibleBody::ComparisonBool { cmp, left, right })
        }
        _ => None,
    }
}

/// The select shape — `if <cmp> { p_then } else { p_else }`, the comparison
/// over two parameters ([`AdmissibleBody::Select`]) or a parameter and a
/// machine-integer literal on the right ([`AdmissibleBody::SelectLiteral`],
/// R2/C9; a literal on the LEFT fails closed) — as rustc lowers it: a
/// four-block diamond
/// - entry: `_c = <cmp>(param, param); switchInt(_c) -> [0: bb_false, otherwise: bb_true]`
/// - true / false: `_t = <param>; goto bb_join`  (the SAME temp `_t`, the SAME join)
/// - join: `_0 = _t; return`
///
/// Every deviation fails closed. The `switchInt` sends `0` (the comparison being
/// FALSE) to the false branch and everything else (TRUE) to `otherwise`, so the
/// `otherwise` branch is `then` and the `0` branch is `else`.
///
/// A third, ARM-COALESCED `-O` spelling is also recognized (2026-08-13, the
/// `e9_release_mode_discharge` debug/release divergence): DestinationPropagation
/// may merge the select temp into the very PARAMETER local one arm selects,
/// leaving that arm empty — `min2` under `-O` becomes
/// `bb_true: goto bb_join`, `bb_false: _1 = copy _2`, `bb_join: _0 = copy _1`.
/// The empty arm's value is the temp local's untouched entry value, so it is
/// admissible only when the temp IS a parameter and the entry comparison only
/// COPY-reads its operands (so no path consumed that parameter before the arm);
/// the empty arm then selects exactly that parameter. See `select_arm`.
///
/// # §6f landing 3 — this is a NARROWING of one reader, not a second reader
///
/// The diamond is read ONCE, by [`select_diamond`], whose arms are OPERANDS
/// (parameter or numeral). This function is the projection of that reading
/// into the vocabulary [`AdmissibleBody`] has: a general reading whose arms
/// are not both parameters has no `AdmissibleBody` value and fails closed
/// here. Two readers of one MIR contract can only drift — the reason
/// `recognize_wf_nat_rec` delegates to `recognize_structural_rec` — so the
/// widened capability is reached through the SEPARATE entry point
/// [`recognize_select_general`], never through a second descent.
fn recognize_select(func: &VerifiableFunction) -> Option<AdmissibleBody> {
    let general = select_diamond(func)?;
    // The E6 vocabulary: both arms are bare parameters. A constant arm is
    // recognized by `select_diamond` and DISCARDED here, which is what keeps
    // `recognize_admissible_body`'s reach — and therefore the gate-free E6
    // kernel-import direction's reach — exactly what it was.
    let (ArithOperand::Param(then_param), ArithOperand::Param(else_param)) =
        (general.then_arm, general.else_arm)
    else {
        return None;
    };
    Some(match general.cmp_right {
        ArithOperand::Param(cmp_right) => AdmissibleBody::Select {
            cmp: general.cmp,
            cmp_left: general.cmp_left,
            cmp_right,
            then_param,
            else_param,
        },
        ArithOperand::Const(literal) => AdmissibleBody::SelectLiteral {
            cmp: general.cmp,
            cmp_param: general.cmp_left,
            literal,
            then_param,
            else_param,
        },
    })
}

/// **§6f landing 3 — the GENERAL select reading, as a SEPARATE entry point.**
///
/// The `if <cmp> { <arm> } else { <arm> }` diamond with each arm a source
/// parameter **or an in-range machine numeral** — `if a < b { a } else { 0 }`,
/// `if a < b { 1 } else { 0 }`, `if a < 10 { a } else { 0 }`.
///
/// # Why a separate entry point rather than an `AdmissibleBody` variant
///
/// Exactly [`recognize_structural_rec`]'s reason, and this landing measured
/// that it is MECHANICAL rather than a matter of taste:
/// `trust_certify::clean_island::admit_function_into` matches
/// `recognize_admissible_body(func)?` **exhaustively, with no wildcard arm**.
/// A new [`AdmissibleBody`] variant therefore cannot widen the CALL direction
/// alone — it forces an arm in the E6 kernel-import direction, where a
/// recognized body becomes a defining equation with NO side A and NO kernel
/// gate. Adding the capability HERE leaves that direction's vocabulary
/// untouched by construction: the constant-arm diamond still reads back as
/// `None` from [`recognize_admissible_body`]
/// (`landing3_selection_probes::l3_p2`), so E6 imports exactly what it
/// imported before this landing.
///
/// The sole intended consumer is `trust-clean-origin`'s `admit_lowering`,
/// where the reading is reflected through `trust_spec_elab`'s general select
/// producer and put to the faithfulness gate — a side A, and a kernel verdict.
///
/// The comparison's LEFT operand is a parameter, and that is a MEASURED
/// boundary rather than a cautious one: `if 10 < a then …` does not elaborate
/// in the real Clean island at all (`landing3_selection_probes::l3_p6`).
#[must_use]
pub fn recognize_select_general(func: &VerifiableFunction) -> Option<GeneralSelectBody> {
    // The same canonical view `recognize_admissible_body` takes before its
    // chain runs — a `TailCall` returning the selected value is an ordinary
    // call writing `_0` — so this entry point cannot disagree with the chain
    // about what the body IS.
    let expanded = func.with_tail_calls_expanded();
    select_diamond(expanded.as_ref())
}

/// The ONE reading of the select diamond. Both [`recognize_select`] (narrow,
/// in the E6 chain) and [`recognize_select_general`] (wide, outside it) are
/// views of this function's result; there is no second descent over these
/// blocks.
fn select_diamond(func: &VerifiableFunction) -> Option<GeneralSelectBody> {
    let blocks = &func.body.blocks;
    if blocks.len() != 4 {
        return None;
    }
    let n = func.body.arg_count;
    let by_id = |id: BlockId| blocks.iter().find(|b| b.id == id);

    // Entry: one comparison of two parameters, then a two-way switch on it.
    let entry = &blocks[0];
    let cmp_stmt = sole_effectful(&entry.stmts)?;
    let Statement::Assign { place: cmp_place, rvalue: Rvalue::BinaryOp(binop, opl, opr), .. } =
        cmp_stmt
    else {
        return None;
    };
    if !cmp_place.projections.is_empty() {
        return None;
    }
    let cmp = select_cmp(binop)?;
    let cmp_left = param_of_operand(opl, n)?;
    // R2/C9: the comparison's RIGHT operand is a parameter (the original
    // param-vs-param select, unchanged) or a width-anchored machine-integer
    // literal (the param-vs-const compare). A literal on the LEFT has no arm
    // — `param_of_operand(opl, ..)` above already failed the body closed.
    let cmp_rhs = match param_of_operand(opr, n) {
        Some(param) => SelectRhs::Param(param),
        None => SelectRhs::Literal(select_literal_of_operand(opr, cmp_left, func)?),
    };
    let Terminator::SwitchInt { discr, targets, otherwise, .. } = &entry.terminator else {
        return None;
    };
    if bare_local(discr)? != cmp_place.local {
        return None;
    }
    if targets.len() != 1 || targets[0].0 != 0 {
        return None;
    }
    let false_blk = by_id(targets[0].1)?;
    let true_blk = by_id(*otherwise)?;

    // The arms and the join, read by the ONE function both diamond shapes read
    // them with. The arm-coalesced `-O` spelling is admissible here exactly
    // when the entry comparison only COPY-reads its operands — see
    // [`select_arms_and_join`], which is this code, extracted verbatim.
    let (then_arm, else_arm) = select_arms_and_join(
        func,
        true_blk,
        false_blk,
        matches!(opl, Operand::Copy(_)) && matches!(opr, Operand::Copy(_)),
    )?;

    Some(GeneralSelectBody {
        cmp,
        cmp_left,
        cmp_right: match cmp_rhs {
            SelectRhs::Param(cmp_right) => ArithOperand::Param(cmp_right),
            SelectRhs::Literal(literal) => ArithOperand::Const(literal),
        },
        then_arm,
        else_arm,
    })
}

/// **The ARMS and the JOIN of a select diamond, read once for both shapes.**
///
/// Extracted from [`select_diamond`] in §6f landing 6 with no behavioural
/// change, so the one-step diamond (`_c = Eq(a, b); switchInt`) and the
/// two-step `==` diamond (`_d = Eq(a, b); _c = Eq(_d, true); switchInt`) share
/// their arm reading instead of acquiring two of them. The entry blocks
/// genuinely differ — that difference is the whole point of the two-step form
/// — but everything after the `SwitchInt` is one contract, and two readers of
/// one contract can only drift (the reason `recognize_wf_nat_rec` delegates to
/// `recognize_structural_rec`).
///
/// `coalesced_arm_admissible` is the caller's statement that an EMPTY arm may
/// be bound to the shared temp's untouched entry value: it holds only when the
/// entry block's comparison COPY-reads its operands, so no path consumed the
/// parameter before the arm. The two-step lane passes `false` — the emitter
/// never produces the coalesced spelling and no pass ever runs on a
/// Clean-origin body to create it, so admitting it there would be untested
/// capability.
fn select_arms_and_join(
    func: &VerifiableFunction,
    true_blk: &BasicBlock,
    false_blk: &BasicBlock,
    coalesced_arm_admissible: bool,
) -> Option<(ArithOperand, ArithOperand)> {
    let n = func.body.arg_count;
    let by_id = |id: BlockId| func.body.blocks.iter().find(|b| b.id == id);

    // Each branch either assigns one temp from a parameter OR AN IN-RANGE
    // NUMERAL (§6f landing 3) and jumps to the join, or (arm-coalesced -O
    // spelling) is empty except for that jump.
    let (then_assign, then_join) = select_arm(true_blk, n, func)?;
    let (else_assign, else_join) = select_arm(false_blk, n, func)?;
    if then_join != else_join {
        return None;
    }
    let (then_arm, else_arm, then_temp) = match (then_assign, else_assign) {
        (Some((then_arm, then_temp)), Some((else_arm, else_temp))) => {
            if then_temp != else_temp {
                return None;
            }
            (then_arm, else_arm, then_temp)
        }
        // Two empty arms select nothing nameable; fail closed.
        (None, None) => return None,
        // Exactly one arm is empty: its value is the shared temp's UNTOUCHED
        // entry value, so the temp must itself be a parameter (`1..=n`; this
        // also excludes the return place `_0`, which has no entry value), and
        // the entry comparison must only COPY-read its operands so that
        // parameter still holds its entry value on every path into the arm.
        // The entry block's sole effectful statement is the comparison
        // (checked above), and the assigning arm runs only on the OTHER path,
        // so the empty arm returns exactly that parameter.
        //
        // An empty arm can therefore only ever be a PARAMETER, whatever the
        // other arm is: the numeral vocabulary widens what an arm may ASSIGN,
        // never what an untouched local may hold.
        (empty_or_then, empty_or_else) => {
            if !coalesced_arm_admissible {
                return None;
            }
            match (empty_or_then, empty_or_else) {
                (None, Some((else_arm, temp))) if (1..=n).contains(&temp) => {
                    (ArithOperand::Param(temp - 1), else_arm, temp)
                }
                (Some((then_arm, temp)), None) if (1..=n).contains(&temp) => {
                    (then_arm, ArithOperand::Param(temp - 1), temp)
                }
                _ => return None,
            }
        }
    };

    // Join: return the selected value. Two equivalent spellings:
    //  - O0: the branches assigned a TEMP and the join copies it to the return
    //    place (`_0 = _temp; return`);
    //  - -O: the branches assigned the RETURN PLACE `_0` directly and the join
    //    is a bare `return` (only value-neutral bookkeeping).
    let join = by_id(then_join)?;
    if !matches!(join.terminator, Terminator::Return) {
        return None;
    }
    if then_temp == 0 {
        // Direct-to-return form: the join must carry NO effectful statement.
        if join.stmts.iter().any(|s| !is_value_neutral(s)) {
            return None;
        }
    } else {
        let Statement::Assign { place: ret_place, rvalue: Rvalue::Use(ret_op), .. } =
            sole_effectful(&join.stmts)?
        else {
            return None;
        };
        if ret_place.local != 0
            || !ret_place.projections.is_empty()
            || bare_local(ret_op)? != then_temp
        {
            return None;
        }
    }
    Some((then_arm, else_arm))
}

/// **§6f landing 6 — the `==` (`BEq.beq … = true`) select reading, as a
/// SEPARATE ENTRY POINT.**
///
/// The TWO-STEP diamond the Clean-origin emitter builds for a branch condition
/// written `a == b`:
///
/// ```text
/// bb0: _d = Eq(copy _l, <rhs>)        // the bool DECISION
///      _c = Eq(copy _d, const true)   // the LIFT to a proposition
///      switchInt(copy _c) -> [0: bb_false, otherwise: bb_true]
/// bb1/bb2: _t = <arm>; goto bb_join
/// bb3: _0 = copy _t; return
/// ```
///
/// # Why the MIR has a second comparison at all
///
/// Because the KERNEL distinguishes the two spellings and side B must be able
/// to as well. `a == b` elaborates to
/// `ite {C} (Eq Bool (BEq.beq {C} … l r) Bool.true) (instDecidableEqBool …) t e`
/// while `a = b` elaborates to `ite {C} (Eq {C} l r) (instDecidableEq{C} …) t e`,
/// and §6f landing 5 measured that those two `ite`s are **not definitionally
/// equal** — the Clean island rejects even `theorem … := rfl` between them.
/// Until landing 6 both realized ONE MIR, so side B — which reads only the
/// emitted body — could not tell them apart while the kernel could, and the
/// gate refused a correct body. The fix direction the discipline takes is that
/// the EMITTER moves to meet the reader: the emitted body now transcribes the
/// `Bool` decision and its `= Bool.true` lift as two comparisons, so what this
/// function reads back IS the tree it reflects.
///
/// # Why a separate entry point rather than an [`AdmissibleBody`] variant
///
/// Exactly [`recognize_select_general`]'s reason, and it is mechanical:
/// `trust_certify::clean_island::admit_function_into` matches
/// `recognize_admissible_body(func)?` **exhaustively, with no wildcard**, so a
/// new variant cannot widen the CALL direction alone — it forces an arm in the
/// gate-free E6 kernel-import direction, where a recognized body becomes a
/// defining equation with NO side A and NO kernel gate. The two-step diamond
/// therefore still reads back as `None` from [`recognize_admissible_body`] and
/// from [`recognize_select_general`], which
/// `landing6_selection_probes::l6_p3` pins.
///
/// The sole intended consumer is `trust-clean-origin`'s `admit_lowering`,
/// where the reading is reflected through
/// `trust_spec_elab::admit_select_beq_function` and put to the faithfulness
/// gate — a side A, and a kernel verdict.
///
/// **There is no `cmp` field**, and that is a statement rather than an
/// omission: this shape exists for ONE surface operator. `!=` elaborates to
/// the same tree with a `Bool.not` around the decision, has no `Ne` anywhere
/// in this module's comparison vocabulary, and is a separate measured demand.
/// A body whose decision is not `BinOp::Eq` fails closed here.
#[must_use]
pub fn recognize_select_beq(func: &VerifiableFunction) -> Option<BeqSelectBody> {
    // The same canonical view the other entry points take, so this reading
    // cannot disagree with them about what the body IS.
    let expanded = func.with_tail_calls_expanded();
    beq_diamond(expanded.as_ref())
}

/// **§6f LANDING 7 — the RAW-BINOP operator vocabulary.**
///
/// The four unsigned machine operators whose realization is a bare
/// `Rvalue::BinaryOp` rather than a call to a marker-authenticated
/// `core::num` primitive. They are a separate enum from [`ArithBinOp`] on
/// purpose, and the purpose is not taste:
///
/// * `ArithBinOp` is the operand of `AdmissibleBody::Arithmetic`, which feeds
///   the **gate-free E6 kernel-import direction**. A variant added there
///   widens what can be imported as a defining equation with no side A and no
///   kernel gate — see [`recognize_raw_binop`] for the mechanical statement.
/// * every `ArithBinOp` maps to a [`PrimitiveCallee::Wrapping*`] identity
///   (the emit lane's callee selector is a closed match over exactly those
///   three, at a width). `&`/`|` live on the `BitAnd`/`BitOr` trait
///   impls and `/`/`%` on `Div`/`Rem`, none of them in `core::num`, so a
///   fourth variant there would demand a callee that does not exist —
///   a widening of the authenticated marker set in `library/core`, which is a
///   different change with a different review.
///
/// **There is no `BitXor`, `Shl` or `Shr`, and that is measured rather than
/// cautious**: `a ^^^ b`, `a <<< 3` and `a >>> 3` do not ELABORATE at a
/// `UInt{N}` carrier — the Clean prelude has no `HXor`/`HShiftLeft`/
/// `HShiftRight` instance at those widths, so instance synthesis fails before
/// a term exists (`landing7_selection_probes::l7_p7`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RawBinOpKind {
    /// `&` — the bitwise conjunction. `MirShape` realization
    /// `Rvalue::BinaryOp(BinOp::BitAnd, …)`.
    BitAnd,
    /// `|` — the bitwise disjunction.
    BitOr,
    /// `/` — TRUNCATED unsigned division. **Total only at a nonzero divisor**;
    /// see [`RawBinOpBody`] for the total-vs-panicking boundary that constrains
    /// where this may be emitted.
    Div,
    /// `%` — the unsigned remainder. Same divisor boundary as [`Self::Div`].
    Rem,
}

impl RawBinOpKind {
    /// The MIR binary operator this kind realizes.
    ///
    /// The ONE mapping, in the same spirit as [`PrimitiveCallee`] being the
    /// one callee identity. It is stated HERE, in the crate that owns the MIR
    /// vocabulary, so that whatever emits a raw binop and whatever reads one
    /// back agree by construction rather than by two tables that can drift.
    /// This crate names nobody: it publishes the mapping and the emit lane
    /// consumes it, which is the direction the dependency edge already runs.
    #[must_use]
    pub fn mir_binop(self) -> BinOp {
        match self {
            Self::BitAnd => BinOp::BitAnd,
            Self::BitOr => BinOp::BitOr,
            Self::Div => BinOp::Div,
            Self::Rem => BinOp::Rem,
        }
    }

    /// The kind a MIR binary operator denotes, or `None` (fail closed).
    ///
    /// Deliberately the inverse of [`Self::mir_binop`] and deliberately
    /// PARTIAL: `Add`/`Sub`/`Mul` are NOT read here even though MIR spells
    /// them, because their emitted realization is the marker-authenticated
    /// call and admitting the raw spelling for them would flip the third pin
    /// of `binop_provenance_pins_never_admit` — a soundness incident, not a
    /// widening.
    #[must_use]
    pub fn from_mir_binop(op: BinOp) -> Option<Self> {
        match op {
            BinOp::BitAnd => Some(Self::BitAnd),
            BinOp::BitOr => Some(Self::BitOr),
            BinOp::Div => Some(Self::Div),
            BinOp::Rem => Some(Self::Rem),
            _ => None,
        }
    }

    /// Whether this operator's Rust semantics PANIC at a zero right operand
    /// while the Clean declaration it reflects is TOTAL there.
    ///
    /// The asymmetry is the whole reason this landing has a divisor rule:
    /// Clean's `UInt{N}.div`/`.mod` are total (`x / 0 = 0`, `x % 0 = x`,
    /// measured at the kernel by `landing7_selection_probes::l7_p6`) and
    /// Rust's `/`/`%` are not. A raw `BinaryOp(Div)` whose divisor can be zero
    /// computes a DIFFERENT function from the declaration it was emitted for,
    /// on exactly the input where the difference is invisible to a value-level
    /// test that never divides by zero.
    #[must_use]
    pub fn panics_at_zero_right_operand(self) -> bool {
        matches!(self, Self::Div | Self::Rem)
    }
}

/// **§6f LANDING 7 — the raw-binop reading.**
///
/// One `_0 = <op>(<operand>, <operand>); return` body at ONE unsigned machine
/// width, with both operands an [`ArithOperand`] — a source parameter or an
/// in-range numeral.
///
/// # Why a separate entry point rather than an [`AdmissibleBody`] variant
///
/// Exactly [`recognize_select_general`]'s and [`recognize_select_beq`]'s
/// reason, and it is mechanical: `trust_certify::clean_island::
/// admit_function_into` matches `recognize_admissible_body(func)?`
/// **exhaustively, with no wildcard**, so a new variant cannot widen the CALL
/// direction alone — it forces an arm in the gate-free E6 kernel-import
/// direction, where a recognized body becomes a defining equation with NO side
/// A and NO kernel gate.
///
/// It matters more here than for either select shape, because this reading is
/// of the RAW BINOP SPELLING, whose exclusion from `recognize_admissible_body`
/// is a pinned provenance boundary
/// (`binop_provenance_pins_never_admit`: *"the raw-binop spelling is outside
/// the recognized fragment today"*). That pin is UNCHANGED — a raw
/// `BinaryOp(Add)` still reads back as `None` from the chain, and so does a
/// raw `BinaryOp(BitAnd)` — and `landing7_selection_probes::l7_p5` measures
/// both.
///
/// # THE DIVISOR BOUNDARY IS NOT ENFORCED HERE, DELIBERATELY
///
/// This reading is a faithful statement of what the emitted bytes COMPUTE, and
/// `Div(a, b)` at an open `b` genuinely computes a panicking division. Saying
/// so is this function's job. REFUSING it is two other programs' job, and both
/// refuse independently:
///
/// * side A's planner, which will not produce a `Div`/`Rem` plan whose right
///   operand is anything but a strictly positive numeral, and
/// * `trust_spec_elab::admit_expr_function` — the FROZEN producer, written
///   years earlier for the opposite direction — which refuses to mint
///   `p0 / p1` or `p0 / 0` at all: *"division/remainder in a spec requires a
///   positive integer literal divisor (a variable or zero divisor needs a
///   nonzero side-condition, not yet wired)"*.
///
/// A reader that silently declined the shape would put the boundary in a THIRD
/// place and, worse, would report the panicking body as *unrecognized* rather
/// than as *the panicking body it is*.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RawBinOpBody {
    /// The operator the single statement applies.
    pub op: RawBinOpKind,
    /// The left operand: a source parameter or an in-range numeral.
    pub left: ArithOperand,
    /// The right operand: a source parameter or an in-range numeral.
    pub right: ArithOperand,
}

/// **§6f LANDING 7 — read a single raw-binop body back out of emitted MIR.**
///
/// The shape, and nothing wider:
///
/// ```text
/// bb0: _0 = <BitAnd|BitOr|Div|Rem>(<operand>, <operand>)
///      return
/// ```
///
/// Fail-closed on: any other block count, any other terminator, more than one
/// effectful statement, a projected or non-return destination, an rvalue that
/// is not `Rvalue::BinaryOp` (in particular `UncheckedBinaryOp` and
/// `CheckedBinaryOp`, whose provenance differs — the first is UB on overflow,
/// the second returns a pair), an operator outside
/// [`RawBinOpKind::from_mir_binop`], and any operand outside the single-width
/// [`ArithOperand`] anchor.
///
/// The sole intended consumer is `trust-clean-origin`'s `admit_lowering`,
/// where the reading is reflected through the FROZEN
/// `trust_spec_elab::admit_expr_function` and put to the faithfulness gate.
#[must_use]
pub fn recognize_raw_binop(func: &VerifiableFunction) -> Option<RawBinOpBody> {
    // The same canonical view every other entry point takes, so this reading
    // cannot disagree with them about what the body IS.
    let expanded = func.with_tail_calls_expanded();
    raw_binop_body(expanded.as_ref())
}

/// The reading behind [`recognize_raw_binop`]. Every deviation fails closed.
fn raw_binop_body(func: &VerifiableFunction) -> Option<RawBinOpBody> {
    let [block] = &func.body.blocks[..] else {
        return None;
    };
    if !matches!(block.terminator, Terminator::Return) {
        return None;
    }
    let mut effectful = block.stmts.iter().filter(|s| !is_value_neutral(s));
    let assign = effectful.next()?;
    if effectful.next().is_some() {
        return None;
    }
    let Statement::Assign { place, rvalue, .. } = assign else {
        return None;
    };
    if place.local != 0 || !place.projections.is_empty() {
        return None;
    }
    // `Rvalue::BinaryOp` EXACTLY. The two lookalikes stay unreadable here for
    // the reason `binop_provenance_pins_never_admit` states: an
    // `UncheckedBinaryOp` is UB on overflow and a `CheckedBinaryOp` returns a
    // pair, so neither denotes the total function a Clean declaration does.
    let Rvalue::BinaryOp(op, left, right) = rvalue else {
        return None;
    };
    let op = RawBinOpKind::from_mir_binop(*op)?;
    // The single-width anchor, identical to every other machine reading: the
    // function returns an unsigned machine width and the return place is
    // declared at it, so a width-skewed body cannot recognize.
    let Ty::Int { width, signed: false } = func.body.return_ty else {
        return None;
    };
    if !matches!(width, 8 | 16 | 32 | 64)
        || !function_returns_unsigned_width(func, width)
        || !bare_local_has_unsigned_width(func, 0, width)
    {
        return None;
    }
    Some(RawBinOpBody {
        op,
        left: arith_operand(left, func, width)?,
        right: arith_operand(right, func, width)?,
    })
}

/// The reading behind [`recognize_select_beq`]. Every deviation fails closed.
fn beq_diamond(func: &VerifiableFunction) -> Option<BeqSelectBody> {
    let blocks = &func.body.blocks;
    if blocks.len() != 4 {
        return None;
    }
    let n = func.body.arg_count;
    let by_id = |id: BlockId| blocks.iter().find(|b| b.id == id);

    // The entry block carries EXACTLY TWO effectful statements, in this order.
    // Requiring the count is what makes a body with a third statement — an
    // extra write to either bool, say — fail closed rather than be skipped
    // over.
    let entry = &blocks[0];
    let mut effectful = entry.stmts.iter().filter(|s| !is_value_neutral(s));
    let decision_stmt = effectful.next()?;
    let lift_stmt = effectful.next()?;
    if effectful.next().is_some() {
        return None;
    }

    // 1. THE DECISION: `_d = Eq(copy _l, <param | numeral>)`, at `bool`.
    let Statement::Assign {
        place: decision_place,
        rvalue: Rvalue::BinaryOp(BinOp::Eq, opl, opr),
        ..
    } = decision_stmt
    else {
        return None;
    };
    if !decision_place.projections.is_empty() || !bare_local_is_bool(func, decision_place.local) {
        return None;
    }
    // A parameter or the return place cannot be the decision temp: the value
    // it holds is read again by the lift, and a body that wrote over a
    // parameter would not be this shape.
    if decision_place.local <= n {
        return None;
    }
    let cmp_left = param_of_operand(opl, n)?;
    let cmp_right = match param_of_operand(opr, n) {
        Some(param) => ArithOperand::Param(param),
        None => ArithOperand::Const(select_literal_of_operand(opr, cmp_left, func)?),
    };

    // 2. THE LIFT: `_c = Eq(copy _d, const true)`, at `bool`. `const false`
    // here is the complementary function with every arm, index and width still
    // right — the mutation `control_13`'s own half injects — so the constant is
    // matched exactly and nothing else is admitted in its position.
    let Statement::Assign {
        place: lift_place,
        rvalue: Rvalue::BinaryOp(BinOp::Eq, lift_left, lift_right),
        ..
    } = lift_stmt
    else {
        return None;
    };
    if !lift_place.projections.is_empty()
        || !bare_local_is_bool(func, lift_place.local)
        || lift_place.local <= n
        || lift_place.local == decision_place.local
    {
        return None;
    }
    if bare_local(lift_left)? != decision_place.local
        || !matches!(lift_right, Operand::Constant(ConstValue::Bool(true)))
    {
        return None;
    }

    // 3. THE BRANCH, on the LIFTED bool and not on the decision. Reading the
    // decision here would be the one-step body wearing an extra statement.
    let Terminator::SwitchInt { discr, targets, otherwise, .. } = &entry.terminator else {
        return None;
    };
    if bare_local(discr)? != lift_place.local {
        return None;
    }
    if targets.len() != 1 || targets[0].0 != 0 {
        return None;
    }
    let false_blk = by_id(targets[0].1)?;
    let true_blk = by_id(*otherwise)?;

    // 4. The arms and the join — the SAME reading the one-step diamond uses.
    let (then_arm, else_arm) = select_arms_and_join(func, true_blk, false_blk, false)?;
    Some(BeqSelectBody { cmp_left, cmp_right, then_arm, else_arm })
}

/// Whether a bare local is declared at `bool`. The two temporaries of the
/// two-step diamond are the only `bool`-typed locals it has, and typing them is
/// what makes `Eq(_d, const true)` a comparison of two booleans rather than of
/// something the reflection would state at the carrier.
fn bare_local_is_bool(func: &VerifiableFunction, local: usize) -> bool {
    func.body.locals.get(local).is_some_and(|decl| decl.index == local && decl.ty == Ty::Bool)
}

/// **§6f LANDING 8 — one operand of a `Bool`-decision select.**
///
/// The vocabulary of [`recognize_select_beq_general`]'s two decision positions:
/// the two leaves every select position has carried since landing 3, plus a
/// RAW-BINOP node computed into a temporary before the decision reads it.
///
/// # Why the computed variant is not an [`ArithExpr`]
///
/// `ArithExpr` is a TREE over `+`/`-`/`*`, and its emitted realization is a
/// CALL CHAIN — one `Call` terminator per node, which splits a basic block.
/// A `RawBin` node's realization is a single `Rvalue::BinaryOp` STATEMENT, so
/// it composes into the two-step diamond's entry block without adding a block
/// at all. That difference is why this variant carries exactly one raw-binop
/// node over two [`ArithOperand`] leaves and not a tree: a nested tree and a
/// wrapping operand both elaborate and both kernel-check (measured,
/// `landing8_selection_probes::l8_p1`), and both are refused here because
/// their realizations are a deeper statement chain and a fifth skeleton
/// respectively — separate measured demands, not a fall-through.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BeqOperand {
    /// A 0-based source parameter.
    Param(usize),
    /// A width-anchored machine literal.
    Const(u128),
    /// A raw binary operator over two leaves, computed into a temporary in the
    /// entry block before the decision reads it.
    ///
    /// **The divisor boundary is NOT enforced here, deliberately** — exactly
    /// [`RawBinOpBody`]'s accounting. This reading is a faithful statement of
    /// what the emitted bytes COMPUTE, and `Div(a, b)` at an open `b` genuinely
    /// computes a panicking division. Refusing it is two other programs' job:
    /// `trust-clean-origin`'s planner, and the FROZEN `trust_spec_elab`
    /// producer, which will not elaborate `p0 / p1` or `p0 / 0` at all.
    RawBin {
        /// The operator.
        op: RawBinOpKind,
        /// The left leaf.
        left: ArithOperand,
        /// The right leaf.
        right: ArithOperand,
    },
}

/// **§6f LANDING 8 — the GENERAL `Bool`-decision select reading.**
///
/// The two-step diamond of landing 6, with the two coordinates that landing
/// fixed now READ OUT OF THE BYTES:
///
/// ```text
/// bb0: [_t = <&|/%>(<leaf>, <leaf>)]{0,2}   // the computed decision operands
///      _d  = Eq(<operand>, <operand>)       // the bool DECISION
///      _c  = Eq(copy _d, const <true|false>)// the LIFT, at EITHER polarity
///      switchInt(copy _c) -> [0: bb_false, otherwise: bb_true]
/// bb1/bb2: _t = <arm>; goto bb_join
/// bb3: _0 = copy _t; return
/// ```
///
/// # The two widenings, and why each is read rather than assumed
///
/// * **[`Self::scrutinee`]** — landing 6 required the lift's constant to be
///   `true` and reflected `Bool.true`. A user who writes `(a == b) = false`
///   elaborates to the SAME tree with the scrutinee `false` (measured,
///   `landing8_selection_probes::l8_p2`), which is a different kernel term:
///   the island refuses `rfl` between them, and refuses it even against the
///   `==` body with SWAPPED ARMS — the complementary function. So the polarity
///   is a fact about the declaration, it is transcribed into the emitted
///   constant, and side B reads it back rather than being told.
/// * **[`Self::cmp_left`] / [`Self::cmp_right`]** — a computed operand.
///
/// # DISJOINT FROM [`recognize_select_beq`] BY CONSTRUCTION
///
/// This function returns `None` for a body landing 6's reader accepts: a
/// `true` scrutinee with both operands leaves. So no emitted body has two
/// readings, and every pin landing 6 and `control_13` put on the narrow shape
/// is untouched — that reader is not modified by this landing at all.
///
/// # Why a separate entry point rather than an [`AdmissibleBody`] variant
///
/// Exactly [`recognize_select_beq`]'s reason, and it is mechanical:
/// `trust_certify::clean_island::admit_function_into` matches
/// `recognize_admissible_body(func)?` **exhaustively, with no wildcard**, so a
/// new variant cannot widen the CALL direction alone — it forces an arm in the
/// gate-free E6 kernel-import direction, where a recognized body becomes a
/// defining equation with NO side A and NO kernel gate. It matters twice over
/// here, because the computed operand carries the RAW-BINOP spelling whose
/// exclusion from `recognize_admissible_body` is a pinned provenance boundary
/// (`binop_provenance_pins_never_admit`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GeneralBeqSelectBody {
    /// The constant the `Bool` decision is lifted against — `true` for the
    /// `==` spelling, `false` for `(a == b) = false`.
    ///
    /// **A polarity, read from the emitted constant.** Landing 6 refused in
    /// advance the alternative of flipping the `SwitchInt` targets instead:
    /// side B would then read a `==` tree off a body denoting its complement.
    /// Here the DECLARATION itself says `= false`, the emitted constant says
    /// `false`, and the term this reading reflects says `Bool.false` — so
    /// nothing is complemented anywhere and the kernel still decides.
    pub scrutinee: bool,
    /// The decision's LEFT operand.
    pub cmp_left: BeqOperand,
    /// The decision's RIGHT operand.
    pub cmp_right: BeqOperand,
    /// The value when the lifted proposition holds.
    pub then_arm: ArithOperand,
    /// The value otherwise.
    pub else_arm: ArithOperand,
}

/// **§6f LANDING 8 — read a general two-step diamond back out of emitted MIR.**
///
/// See [`GeneralBeqSelectBody`] for the shape and for the disjointness rule
/// against [`recognize_select_beq`]. Every deviation fails closed.
///
/// The sole intended consumer is `trust-clean-origin`'s `admit_lowering`, where
/// the reading is reflected through
/// `trust_spec_elab::admit_select_beq_operands_function` and put to the
/// faithfulness gate — a side A, and a kernel verdict.
#[must_use]
pub fn recognize_select_beq_general(func: &VerifiableFunction) -> Option<GeneralBeqSelectBody> {
    // The same canonical view every other entry point takes, so this reading
    // cannot disagree with them about what the body IS.
    let expanded = func.with_tail_calls_expanded();
    general_beq_diamond(expanded.as_ref())
}

/// The reading behind [`recognize_select_beq_general`]. Every deviation fails
/// closed.
fn general_beq_diamond(func: &VerifiableFunction) -> Option<GeneralBeqSelectBody> {
    let blocks = &func.body.blocks;
    if blocks.len() != 4 {
        return None;
    }
    let n = func.body.arg_count;
    let by_id = |id: BlockId| blocks.iter().find(|b| b.id == id);

    // The single-width anchor, taken before anything else so a width-skewed
    // body cannot recognize: identical to every other machine reading.
    let Ty::Int { width, signed: false } = func.body.return_ty else {
        return None;
    };
    if !matches!(width, 8 | 16 | 32 | 64) || !function_returns_unsigned_width(func, width) {
        return None;
    }

    // The entry block carries the DECISION and the LIFT last, in that order,
    // preceded by AT MOST TWO computed-operand statements. Requiring the exact
    // count is what makes a body with one statement too many fail closed rather
    // than be skipped over.
    let entry = &blocks[0];
    let effectful: Vec<&Statement> = entry.stmts.iter().filter(|s| !is_value_neutral(s)).collect();
    if effectful.len() < 2 || effectful.len() > 4 {
        return None;
    }
    let lift_stmt = effectful[effectful.len() - 1];
    let decision_stmt = effectful[effectful.len() - 2];
    let prefix = &effectful[..effectful.len() - 2];

    // 1. THE LIFT: `_c = Eq(copy _d, const <bool>)`, at `bool`. Read first
    //    because its `bool` constant is the polarity, and reading it rather
    //    than demanding one value is the whole of this landing's second half.
    let Statement::Assign {
        place: lift_place,
        rvalue: Rvalue::BinaryOp(BinOp::Eq, lift_left, lift_right),
        ..
    } = lift_stmt
    else {
        return None;
    };
    if !lift_place.projections.is_empty()
        || !bare_local_is_bool(func, lift_place.local)
        || lift_place.local <= n
    {
        return None;
    }
    let Operand::Constant(ConstValue::Bool(scrutinee)) = lift_right else {
        return None;
    };
    let scrutinee = *scrutinee;

    // 2. THE DECISION: `_d = Eq(<operand>, <operand>)`, at `bool`, and it must
    //    be what the lift reads.
    let Statement::Assign {
        place: decision_place,
        rvalue: Rvalue::BinaryOp(BinOp::Eq, opl, opr),
        ..
    } = decision_stmt
    else {
        return None;
    };
    if !decision_place.projections.is_empty()
        || !bare_local_is_bool(func, decision_place.local)
        || decision_place.local <= n
        || decision_place.local == lift_place.local
    {
        return None;
    }
    if bare_local(lift_left)? != decision_place.local {
        return None;
    }

    // 3. THE COMPUTED OPERANDS. Each prefix statement writes a FRESH temporary
    //    at the result carrier and is consumed EXACTLY ONCE by the decision;
    //    a dead prefix statement, a repeated temp, or a temp the decision never
    //    reads all fail closed, because a statement whose value nothing uses is
    //    not part of the term this body denotes.
    let mut computed: Vec<(usize, BeqOperand)> = Vec::with_capacity(prefix.len());
    for stmt in prefix {
        let Statement::Assign { place, rvalue: Rvalue::BinaryOp(op, left, right), .. } = stmt
        else {
            return None;
        };
        if !place.projections.is_empty()
            || place.local <= n
            || place.local == decision_place.local
            || place.local == lift_place.local
            || computed.iter().any(|(temp, _)| *temp == place.local)
            || !bare_local_has_unsigned_width(func, place.local, width)
        {
            return None;
        }
        let op = RawBinOpKind::from_mir_binop(*op)?;
        computed.push((
            place.local,
            BeqOperand::RawBin {
                op,
                left: arith_operand(left, func, width)?,
                right: arith_operand(right, func, width)?,
            },
        ));
    }
    let resolve = |operand: &Operand| -> Option<BeqOperand> {
        if let Some(local) = bare_local(operand) {
            if let Some((_, computed)) = computed.iter().find(|(temp, _)| *temp == local) {
                return Some(*computed);
            }
        }
        match arith_operand(operand, func, width)? {
            ArithOperand::Param(index) => Some(BeqOperand::Param(index)),
            ArithOperand::Const(value) => Some(BeqOperand::Const(value)),
        }
    };
    let cmp_left = resolve(opl)?;
    let cmp_right = resolve(opr)?;
    // Every computed temp must be consumed, and each exactly once: two reads of
    // one temp would be one statement standing for two operands, which is not
    // the shape the emitter builds.
    let consumed: Vec<usize> = [opl, opr].iter().filter_map(|op| bare_local(op)).collect();
    for (temp, _) in &computed {
        if consumed.iter().filter(|local| *local == temp).count() != 1 {
            return None;
        }
    }

    // 4. DISJOINTNESS from `recognize_select_beq`. A `true` scrutinee with two
    //    leaf operands is landing 6's body and is read by landing 6's reader;
    //    admitting it here too would give one emitted body two readings.
    let has_computed = matches!(cmp_left, BeqOperand::RawBin { .. })
        || matches!(cmp_right, BeqOperand::RawBin { .. });
    if scrutinee && !has_computed {
        return None;
    }

    // 5. THE BRANCH, on the LIFTED bool and not on the decision.
    let Terminator::SwitchInt { discr, targets, otherwise, .. } = &entry.terminator else {
        return None;
    };
    if bare_local(discr)? != lift_place.local {
        return None;
    }
    if targets.len() != 1 || targets[0].0 != 0 {
        return None;
    }
    let false_blk = by_id(targets[0].1)?;
    let true_blk = by_id(*otherwise)?;

    // 6. The arms and the join — the SAME reading both diamond shapes use,
    //    unmodified. The coalesced spelling stays inadmissible here for landing
    //    6's reason: the emitter never produces it and no MIR pass ever runs on
    //    a Clean-origin body to create it.
    let (then_arm, else_arm) = select_arms_and_join(func, true_blk, false_blk, false)?;
    Some(GeneralBeqSelectBody { scrutinee, cmp_left, cmp_right, then_arm, else_arm })
}

/// **§6f landing 6 — the `==` select reading.**
///
/// One `if a == <rhs> { <arm> } else { <arm> }` body at ONE unsigned machine
/// width, with every non-comparison position an [`ArithOperand`].
///
/// Deliberately NOT an [`AdmissibleBody`] variant — see
/// [`recognize_select_beq`] for the mechanical reason — and deliberately
/// carrying no comparison: the shape is the `Bool`-decision spelling of
/// EQUALITY and nothing else.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BeqSelectBody {
    /// The decision's LEFT operand — always a 0-based source parameter, for
    /// the reason `landing3_selection_probes::l3_p6` measured for every select
    /// shape: a numeral on the left does not elaborate at all.
    pub cmp_left: usize,
    /// The decision's RIGHT operand: a parameter, or a width-anchored machine
    /// literal.
    pub cmp_right: ArithOperand,
    /// The value when the decision holds.
    pub then_arm: ArithOperand,
    /// The value otherwise.
    pub else_arm: ArithOperand,
}

/// **§6f landing 3 — the general select reading.**
///
/// One `if <cmp> { <arm> } else { <arm> }` body at ONE unsigned machine width,
/// with every non-comparison position an [`ArithOperand`] — a source parameter
/// or an in-range numeral.
///
/// The operand vocabulary is REUSED from the arithmetic shapes rather than
/// redefined, the same "vocabulary reuse, not a producer edit" the
/// `CleanOriginShape` arms already rest on: the values here come from the
/// EMITTED MIR, the plan's come from the Clean term, and the structural
/// comparison in `admit_lowering` is then direct equality.
///
/// **This type is deliberately NOT an [`AdmissibleBody`] variant.** See
/// [`recognize_select_general`] for the mechanical reason: `AdmissibleBody` is
/// the vocabulary of the gate-free E6 kernel-import direction, whose dispatch
/// matches it exhaustively, so a variant there is a widening of what can be
/// imported as a defining equation with no side A and no kernel gate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GeneralSelectBody {
    /// The comparison the branch tests.
    pub cmp: SelectCmp,
    /// The comparison's LEFT operand — always a 0-based source parameter.
    pub cmp_left: usize,
    /// The comparison's RIGHT operand: a parameter, or a width-anchored
    /// machine literal (R2/C9's `SelectLiteral`, in operand form).
    pub cmp_right: ArithOperand,
    /// The value when the comparison holds.
    pub then_arm: ArithOperand,
    /// The value otherwise.
    pub else_arm: ArithOperand,
}

/// The recognized RIGHT operand of a select comparison: a source parameter
/// (the original param-vs-param select) or a machine-integer literal (R2/C9).
enum SelectRhs {
    Param(usize),
    Literal(u128),
}

/// The machine-integer literal a select comparison's RIGHT operand names, or
/// `None` (fail closed). Admissible only under the single-width anchor
/// [`arith_operand`] uses: the function must return an unsigned machine width,
/// the comparison's LEFT parameter local must be declared at exactly that
/// width, and the constant's encoded width and value must both agree with it —
/// so a width-skewed or out-of-range constant can never recognize.
fn select_literal_of_operand(
    op: &Operand,
    cmp_left: usize,
    func: &VerifiableFunction,
) -> Option<u128> {
    let Ty::Int { width, signed: false } = func.body.return_ty else {
        return None;
    };
    if !matches!(width, 8 | 16 | 32 | 64) {
        return None;
    }
    if !function_returns_unsigned_width(func, width)
        || !bare_local_has_unsigned_width(func, cmp_left + 1, width)
    {
        return None;
    }
    match op {
        Operand::Constant(ConstValue::Uint(v, encoded_width))
            if *encoded_width == width && uint_fits_width(*v, width) =>
        {
            Some(*v)
        }
        _ => None,
    }
}

/// What one arm of a [`recognize_bool_binary`] diamond computes: a constant
/// `bool` (the short-circuit value), or a comparison leaf (the second-evaluated
/// operand).
enum ArmValue {
    /// `_place = const <bool>`.
    ConstBool(bool),
    /// `_place = <cmp>(op, op)`.
    Cmp(ComparisonLeaf),
}

/// The bool-binary shape — `A && B` / `A || B` over two comparison leaves — as
/// rustc lowers a SHORT-CIRCUIT `&&`/`||` and leaves it through the full
/// optimization pipeline (see [`AdmissibleBody::BoolBinary`]): a four-block
/// diamond whose entry computes the LHS comparison `A` into a bare local and
/// two-way `switchInt`es on it, whose two arms assign the SAME place — one the
/// short-circuit constant, the other the RHS comparison `B` — and jump to a
/// shared `return` join.
///
/// `&&` and `||` differ only in which arm holds the constant and its value:
/// `&&` short-circuits to `false` on the `0` edge; `||` short-circuits to
/// `true` on the `otherwise` edge. Any other pairing (two constants, two
/// comparisons, the wrong constant on an edge) fails closed. Every leaf must be
/// an admissible comparison ([`comparison_leaf`]); the declared return type is
/// pinned to `bool` so a diamond at any other type fails closed.
fn recognize_bool_binary(func: &VerifiableFunction) -> Option<AdmissibleBody> {
    if func.body.return_ty != Ty::Bool {
        return None;
    }
    let blocks = &func.body.blocks;
    if blocks.len() != 4 {
        return None;
    }
    let n = func.body.arg_count;
    let by_id = |id: BlockId| blocks.iter().find(|b| b.id == id);

    // Entry: one comparison of admissible operands into a bare local, then a
    // two-way switch on exactly that local.
    let entry = &blocks[0];
    let Statement::Assign { place: cmp_place, rvalue: Rvalue::BinaryOp(binop, opl, opr), .. } =
        sole_effectful(&entry.stmts)?
    else {
        return None;
    };
    if !cmp_place.projections.is_empty() {
        return None;
    }
    // The LHS comparison `A` — always the first-evaluated / discriminant leaf.
    let left = comparison_leaf(binop, opl, opr, n)?;
    let Terminator::SwitchInt { discr, targets, otherwise, .. } = &entry.terminator else {
        return None;
    };
    if bare_local(discr)? != cmp_place.local {
        return None;
    }
    if targets.len() != 1 || targets[0].0 != 0 {
        return None;
    }
    let zero_blk = by_id(targets[0].1)?; // the `0` (LHS-false) edge
    let other_blk = by_id(*otherwise)?; // the `otherwise` (LHS-true) edge

    // Each arm assigns the SAME place (the return place `_0` directly, or a
    // shared temp) and jumps to the SAME join.
    let (zero_value, zero_place, zero_join) = bool_binary_arm(zero_blk, n)?;
    let (other_value, other_place, other_join) = bool_binary_arm(other_blk, n)?;
    if zero_place != other_place || zero_join != other_join {
        return None;
    }

    // Join: return the selected value. Two equivalent spellings, exactly as the
    // select recognizer accepts — direct-to-`_0` (bare `return`) or via a temp
    // (`_0 = _temp; return`).
    let join = by_id(zero_join)?;
    if !matches!(join.terminator, Terminator::Return) {
        return None;
    }
    if zero_place == 0 {
        if join.stmts.iter().any(|s| !is_value_neutral(s)) {
            return None;
        }
    } else {
        let Statement::Assign { place: ret_place, rvalue: Rvalue::Use(ret_op), .. } =
            sole_effectful(&join.stmts)?
        else {
            return None;
        };
        if ret_place.local != 0
            || !ret_place.projections.is_empty()
            || bare_local(ret_op)? != zero_place
        {
            return None;
        }
    }

    // The connective is fixed by WHERE the short-circuit constant sits and its
    // value. `A && B` short-circuits to `false` on the `0` edge (RHS on
    // `otherwise`); `A || B` short-circuits to `true` on the `otherwise` edge
    // (RHS on the `0` edge). The discriminant leaf is `A` in both; `B` is the
    // comparison arm. Any other pairing fails closed.
    match (zero_value, other_value) {
        (ArmValue::ConstBool(false), ArmValue::Cmp(right)) => {
            Some(AdmissibleBody::BoolBinary { op: BoolBinOp::And, left, right })
        }
        (ArmValue::Cmp(right), ArmValue::ConstBool(true)) => {
            Some(AdmissibleBody::BoolBinary { op: BoolBinOp::Or, left, right })
        }
        _ => None,
    }
}

/// The two callee spellings a Shape-B cold-hint block may carry, EXACTLY.
///
/// `core::intrinsics::cold_path` is a nullary, unit-returning codegen HINT
/// with no semantics; the `-O` lowering of `checked_*` places one call to it
/// on the overflow edge (measured 2026-08-25). Both the compiler-marked
/// spelling (once extraction stamps `cold_path` as a modeled intrinsic) and
/// the current bare spelling are accepted; trust-ir-bridge's `EXACT_TOTAL`
/// table carries the same bare-path precedent. SOUNDNESS of accepting the
/// bare spelling: the recognizer additionally pins the call to ZERO
/// arguments and a `Unit`-typed destination local that is READ NOWHERE, so
/// the call cannot contribute a VALUE to the recognized dataflow; its only
/// residual leverage is effects/panic/divergence, which are exactly the
/// properties the facet gate (`facet_inference`) independently requires of
/// every callee before any admission — an unmarked callee is facet-usable
/// only if it is a same-unit function CERTIFIED pure/total/deterministic/
/// panic-free, and such a nullary unit function is observationally a no-op.
const COLD_PATH_CALLEES: [&str; 2] = [
    "core::intrinsics::cold_path",
    "@trust-rustc-intrinsic::core::intrinsics::cold_path",
];

/// The `(op, width)` a compiler-marked CHECKED signed primitive callee
/// denotes, through the closed [`crate::RustcCheckedPrimitiveMethod`]
/// classifier — never a name suffix.
fn checked_method(callee: &str) -> Option<(CheckedArithOp, u32)> {
    Some(match crate::RustcCheckedPrimitiveMethod::classify(callee)? {
        crate::RustcCheckedPrimitiveMethod::CheckedAdd(w) => (CheckedArithOp::Add, w),
        crate::RustcCheckedPrimitiveMethod::CheckedSub(w) => (CheckedArithOp::Sub, w),
        crate::RustcCheckedPrimitiveMethod::CheckedMul(w) => (CheckedArithOp::Mul, w),
    })
}

/// The [`CheckedArithOp`] a MIR [`BinOp`] inside a `CheckedBinaryOp` denotes.
/// Only Add/Sub/Mul — `Shl`/`Shr` also have `*WithOverflow` forms in rustc
/// but a DIFFERENT (shift-amount) flag semantics, and division has none.
fn checked_binop(op: &BinOp) -> Option<CheckedArithOp> {
    match op {
        BinOp::Add => Some(CheckedArithOp::Add),
        BinOp::Sub => Some(CheckedArithOp::Sub),
        BinOp::Mul => Some(CheckedArithOp::Mul),
        _ => None,
    }
}

fn bare_local_has_signed_width(func: &VerifiableFunction, local: usize, width: u32) -> bool {
    func.body
        .locals
        .get(local)
        .is_some_and(|decl| decl.index == local && decl.ty == Ty::Int { width, signed: true })
}

/// A checked-arithmetic operand: a bare SIGNED parameter of the exact width,
/// or a NON-NEGATIVE integer literal within `iN`'s positive range
/// (`0..=2^(N-1)-1`). A negative literal has no [`ArithOperand`] spelling and
/// PARKS (fail closed) rather than being guessed at.
fn checked_operand(op: &Operand, func: &VerifiableFunction, width: u32) -> Option<ArithOperand> {
    let positive_max = (1u128 << (width - 1)) - 1;
    match op {
        Operand::Copy(p) | Operand::Move(p)
            if p.projections.is_empty()
                && p.local >= 1
                && p.local <= func.body.arg_count
                && bare_local_has_signed_width(func, p.local, width) =>
        {
            Some(ArithOperand::Param(p.local - 1))
        }
        // A signed literal extracts as `ConstValue::Int(i128)` with no width
        // (see [`cmp_operand`]); only the non-negative in-range case has an
        // `ArithOperand` spelling.
        Operand::Constant(ConstValue::Int(v)) if *v >= 0 => {
            let v = v.unsigned_abs();
            (v <= positive_max).then_some(ArithOperand::Const(v))
        }
        _ => None,
    }
}

/// The expected monomorphized generic-args rendering of the std `Option<iN>`
/// aggregate (`AggregateKind::Adt::args`), pinned so a wrong-instantiation
/// reconstruction in serialized IR cannot slip past the `name` check alone.
fn option_args_rendering(width: u32) -> String {
    format!("core::option::Option<i{width}>")
}

/// Whether an `Aggregate` rvalue constructs EXACTLY the pinned std
/// `Option<iN>` variant `variant` with generic args `i<width>`. `None`-strict:
/// a missing `args` rendering (pre-C1 serialized IR) is refused rather than
/// assumed to be the right instantiation.
fn is_option_aggregate(kind: &crate::AggregateKind, expected_variant: usize, width: u32) -> bool {
    let crate::AggregateKind::Adt { name, variant, active_field, args } = kind else {
        return false;
    };
    name == "core::option::Option"
        && *variant == expected_variant
        && active_field.is_none()
        && args.as_deref() == Some(option_args_rendering(width).as_str())
}

/// Recognize the overflow-checked signed arithmetic shapes (see
/// [`AdmissibleBody::CheckedArithmetic`] for the shapes and the faithfulness
/// argument). CONSERVATIVE and fail-closed on (spec §2): any `Assert`
/// terminator ANYWHERE in the body (= unchecked arithmetic — reachability is
/// deliberately not consulted, stricter is safer); a return type that is not
/// the pinned Direct-tag std `Option<iN>`; a niche or indirect discriminant
/// encoding (refused inside `ty_is_std_option_of_signed`); a `Some` payload
/// that is not exactly the CheckedBinaryOp result field; mismatched variant
/// indices; an unsigned receiver (the classifier admits `iN` only); ops
/// outside Add/Sub/Mul; a mismatched width anywhere; and any third spelling,
/// which PARKS rather than being guessed at.
fn recognize_checked_arithmetic(func: &VerifiableFunction) -> Option<AdmissibleBody> {
    // ANY Assert in the body means unchecked arithmetic (or something else
    // entirely): refuse before looking at anything else.
    if func
        .body
        .blocks
        .iter()
        .any(|b| matches!(b.terminator, Terminator::Assert { .. }))
    {
        return None;
    }
    // The declared return type (and the return slot's declared type) must be
    // the pinned std Option-of-signed shape.
    let width = crate::facet_inference::ty_is_std_option_of_signed(&func.body.return_ty)?;
    let ret_local = func.body.locals.iter().find(|l| l.index == 0)?;
    if ret_local.ty != func.body.return_ty {
        return None;
    }
    recognize_checked_call(func, width).or_else(|| recognize_checked_diamond(func, width))
}

/// Shape A — the un-inlined marked call:
/// `bb0: _0 = <marked iN::checked_op>(a, b) -> bb1; bb1: return`.
fn recognize_checked_call(func: &VerifiableFunction, width: u32) -> Option<AdmissibleBody> {
    let [call_blk, ret_blk] = &func.body.blocks[..] else {
        return None;
    };
    if !matches!(ret_blk.terminator, Terminator::Return)
        || ret_blk.stmts.iter().any(|s| !is_value_neutral(s))
        || call_blk.stmts.iter().any(|s| !is_value_neutral(s))
    {
        return None;
    }
    let Terminator::Call {
        func: callee,
        callee_identity: _,
        args,
        dest,
        target,
        atomic,
        is_foreign,
        is_unsafe_sig,
        ..
    } = &call_blk.terminator
    else {
        return None;
    };
    if dest.local != 0
        || !dest.projections.is_empty()
        || *target != Some(ret_blk.id)
        || atomic.is_some()
        || *is_foreign
        || *is_unsafe_sig
    {
        return None;
    }
    let (op, callee_width) = checked_method(callee)?;
    if callee_width != width {
        return None;
    }
    let [a, b] = &args[..] else {
        return None;
    };
    Some(AdmissibleBody::CheckedArithmetic {
        op,
        width_bits: width,
        left: checked_operand(a, func, width)?,
        right: checked_operand(b, func, width)?,
    })
}

/// Shape B — the inlined overflow-flag diamond (the measured `-O` shape; see
/// [`AdmissibleBody::CheckedArithmetic`]), with or without the interposed
/// `cold_path` hint block on the overflow edge.
fn recognize_checked_diamond(func: &VerifiableFunction, width: u32) -> Option<AdmissibleBody> {
    let blocks = &func.body.blocks;
    // Exactly the diamond's blocks and nothing else: entry, some-arm,
    // none-arm, join, and optionally the cold-hint block.
    if blocks.len() != 4 && blocks.len() != 5 {
        return None;
    }
    let by_id = |id: BlockId| blocks.iter().find(|b| b.id == id);
    let n = func.body.arg_count;

    // ENTRY: exactly three value-carrying statements, in order — the checked
    // op into a fresh tuple temp, then the result-field and flag-field reads.
    let entry = blocks.first()?;
    let mut effectful = entry.stmts.iter().filter(|s| !is_value_neutral(s));
    let (s1, s2, s3) = (effectful.next()?, effectful.next()?, effectful.next()?);
    if effectful.next().is_some() {
        return None;
    }
    let Statement::Assign { place: t_place, rvalue: Rvalue::CheckedBinaryOp(binop, a, b), .. } = s1
    else {
        return None;
    };
    let op = checked_binop(binop)?;
    let left = checked_operand(a, func, width)?;
    let right = checked_operand(b, func, width)?;
    let t = bare_nonreturn_temp(func, t_place)?;
    // The tuple temp's declared type is the checked pair `(iN, bool)`.
    if declared_ty(func, t)? != &Ty::Tuple(vec![Ty::Int { width, signed: true }, Ty::Bool]) {
        return None;
    }
    let (r, r_src) = field_read_of(func, s2)?;
    let (f, f_src) = field_read_of(func, s3)?;
    // `_r = _t.0` (the wrapped result, at the signed width) and `_f = _t.1`
    // (the overflow flag, at bool) — both off the SAME tuple temp, with the
    // exact field indices; the three locals are pairwise distinct fresh
    // temporaries, so no operand can alias another's value.
    if r_src != (t, 0)
        || f_src != (t, 1)
        || !bare_local_has_signed_width(func, r, width)
        || declared_ty(func, f)? != &Ty::Bool
        || r == f
        || r == t
        || f == t
        || r <= n
        || f <= n
        || t <= n
    {
        return None;
    }

    // The switch on the overflow flag: `0` (no overflow) → the Some arm;
    // `otherwise` → the None arm, possibly through the cold-hint block.
    let Terminator::SwitchInt { discr, targets, otherwise, .. } = &entry.terminator else {
        return None;
    };
    if bare_local(discr)? != f || targets.len() != 1 || targets[0].0 != 0 {
        return None;
    }
    let some_blk = by_id(targets[0].1)?;
    let mut none_edge = by_id(*otherwise)?;

    // Optional cold-hint block on the overflow edge (present in the measured
    // 5-block `-O` shape): exactly one nullary call to the pinned callee
    // spelling, into a never-read Unit temp, falling through to the None arm.
    let mut used_cold = false;
    if let Terminator::Call {
        func: callee,
        callee_identity: _,
        args,
        dest,
        target,
        atomic,
        is_foreign,
        is_unsafe_sig,
        ..
    } = &none_edge.terminator
    {
        if !COLD_PATH_CALLEES.contains(&callee.as_str())
            || !args.is_empty()
            || !dest.projections.is_empty()
            || atomic.is_some()
            || *is_foreign
            || *is_unsafe_sig
            || none_edge.stmts.iter().any(|s| !is_value_neutral(s))
        {
            return None;
        }
        let u = dest.local;
        // The hint's destination: a fresh Unit temp, not the return place, not
        // a parameter, distinct from the dataflow temps, and READ NOWHERE
        // (its only occurrence in any value-carrying position is this dest).
        if u == 0
            || u <= n
            || u == t
            || u == r
            || u == f
            || declared_ty(func, u)? != &Ty::Unit
            || local_is_read_anywhere(func, u)
        {
            return None;
        }
        none_edge = by_id((*target)?)?;
        used_cold = true;
    }
    if blocks.len() == 5 && !used_cold {
        return None; // a fifth block that is not the cold hint is unrecognized
    }
    if blocks.len() == 4 && used_cold {
        return None; // the cold hint cannot also be an arm
    }
    let none_blk = none_edge;

    // The two arms: `_0 = Some(_r)` on the no-overflow edge, `_0 = None` on
    // the overflow edge, both `goto` the SAME join. Variant indices are pinned
    // (1 = `Some`, 0 = `None`) — trustworthy because the return-shape gate
    // required the Direct tag encoding.
    let some_agg = sole_effectful(&some_blk.stmts)?;
    let Statement::Assign { place: sp, rvalue: Rvalue::Aggregate(s_kind, s_ops), .. } = some_agg
    else {
        return None;
    };
    let Terminator::Goto(some_join) = &some_blk.terminator else {
        return None;
    };
    if sp.local != 0
        || !sp.projections.is_empty()
        || !is_option_aggregate(s_kind, 1, width)
        || s_ops.len() != 1
        || bare_local(&s_ops[0])? != r
    {
        return None;
    }
    let none_agg = sole_effectful(&none_blk.stmts)?;
    let Statement::Assign { place: np, rvalue: Rvalue::Aggregate(n_kind, n_ops), .. } = none_agg
    else {
        return None;
    };
    let Terminator::Goto(none_join) = &none_blk.terminator else {
        return None;
    };
    if np.local != 0
        || !np.projections.is_empty()
        || !is_option_aggregate(n_kind, 0, width)
        || !n_ops.is_empty()
        || some_join != none_join
    {
        return None;
    }

    // JOIN: bookkeeping only, then return.
    let join = by_id(*some_join)?;
    if !matches!(join.terminator, Terminator::Return)
        || join.stmts.iter().any(|s| !is_value_neutral(s))
    {
        return None;
    }
    // Every block is accounted for: entry, some, none, join (+ cold).
    let mut named: Vec<BlockId> = vec![entry.id, some_blk.id, none_blk.id, join.id];
    if used_cold {
        named.push(*otherwise);
    }
    named.sort_by_key(|b| b.0);
    named.dedup();
    if named.len() != blocks.len() {
        return None;
    }

    Some(AdmissibleBody::CheckedArithmetic { op, width_bits: width, left, right })
}

/// How many bookkeeping `goto` trampolines the guard's false-edge chaser walks
/// before failing CLOSED.
///
/// The measured call-inlined form (probe c10 — the real client body's shape)
/// interposes exactly ONE (`bb5: StorageDead(_4); goto bb2`) on the first
/// comparison's false edge. The bound is what makes the chase terminate on a
/// `goto` CYCLE, and it keeps the accepted CFG small enough that the block
/// census at the end of [`recognize_guarded_narrow`] can still account for
/// every block.
const NARROW_TRAMPOLINE_LIMIT: usize = 2;

/// Walk value-neutral `goto`-only blocks from `start` to the first block that
/// actually does something, recording each trampoline walked into `walked` (the
/// block census needs them). `None` — fail closed — when the chain is longer
/// than [`NARROW_TRAMPOLINE_LIMIT`] or leaves the block list.
///
/// A block STOPS the walk when it carries any value-carrying statement or ends
/// in anything other than a plain `goto`; such a block is the destination and
/// is returned unexamined, for the caller to parse as an arm.
fn chase_goto_trampolines<'a>(
    blocks: &'a [BasicBlock],
    start: BlockId,
    walked: &mut Vec<BlockId>,
) -> Option<&'a BasicBlock> {
    let mut id = start;
    for _ in 0..=NARROW_TRAMPOLINE_LIMIT {
        let blk = blocks.iter().find(|b| b.id == id)?;
        let Terminator::Goto(next) = &blk.terminator else {
            return Some(blk);
        };
        if blk.stmts.iter().any(|s| !is_value_neutral(s)) {
            return Some(blk);
        }
        walked.push(blk.id);
        id = *next;
    }
    None
}

/// One comparison block of the guarded-narrow conjunction diamond:
/// `_g = <cmp>(..); switchInt(_g) -> [0: <false edge>, otherwise: <true edge>]`.
/// Returns `(leaf, g_local, false_edge, true_edge)`.
///
/// The leaf goes through the SHARED [`comparison_leaf`] grammar (the same one
/// [`recognize_bool_binary`] uses), so the `>`/`>=` operand-swap normalization
/// and the ≥1-parameter requirement are identical, and there is no second copy
/// of the comparison rules to drift.
fn narrow_guard_block(
    block: &BasicBlock,
    arg_count: usize,
) -> Option<(ComparisonLeaf, usize, BlockId, BlockId)> {
    let Statement::Assign { place, rvalue: Rvalue::BinaryOp(binop, opl, opr), .. } =
        sole_effectful(&block.stmts)?
    else {
        return None;
    };
    if !place.projections.is_empty() {
        return None;
    }
    let leaf = comparison_leaf(binop, opl, opr, arg_count)?;
    let Terminator::SwitchInt { discr, targets, otherwise, .. } = &block.terminator else {
        return None;
    };
    if bare_local(discr)? != place.local || targets.len() != 1 || targets[0].0 != 0 {
        return None;
    }
    Some((leaf, place.local, targets[0].1, *otherwise))
}

/// The single parameter the two guard leaves bound, when they are EXACTLY the
/// measured `iN::MIN as iW <= x` / `x <= iN::MAX as iW` pair for the target
/// width `to_bits` — else `None` (fail closed).
///
/// [`comparison_leaf`] has already normalized the source `>=` by operand swap
/// (`Ge(x, MIN)` ↦ `Le(NegConst(2^(N-1)), Param p)`), so what is matched here is
/// literal-exact in the comparison SENSE, in each bound's MAGNITUDE and SIGN,
/// and in the ORDER the two bounds are evaluated (lower bound first — the
/// measured lowering of `x >= MIN && x <= MAX`, which is how the client body
/// spells it). A `Lt(x, 2^(N-1))` respelling, an off-by-one bound, a sense
/// flip, a `Const` where the `NegConst` belongs, or two DIFFERENT parameters
/// all fail closed. If rustc ever canonicalizes the guard differently the lane
/// stops discharging (a red build) rather than admitting an unmeasured guard.
fn narrow_guarded_param(lo: ComparisonLeaf, hi: ComparisonLeaf, to_bits: u32) -> Option<usize> {
    if !(1..=128).contains(&to_bits) {
        return None;
    }
    let pivot = 1u128 << (to_bits - 1); // 2^(N-1) = |iN::MIN| = iN::MAX + 1
    let (CmpOperand::NegConst(min_magnitude), CmpOperand::Param(p)) = (lo.left, lo.right) else {
        return None;
    };
    let (CmpOperand::Param(q), CmpOperand::Const(max)) = (hi.left, hi.right) else {
        return None;
    };
    (lo.cmp == SelectCmp::Le
        && hi.cmp == SelectCmp::Le
        && min_magnitude == pivot
        && max == pivot - 1
        && p == q)
        .then_some(p)
}

/// Recognize the WIDTH-GUARDED NARROWING shape — see
/// [`AdmissibleBody::GuardedNarrow`] for the measured CFG and the faithfulness
/// argument. CONSERVATIVE and fail-closed (`None`) on ALL of:
///
/// 1. any `Assert` terminator anywhere in the body, any `Call` (including a
///    `cold_path` hint — neither c2 nor c10 has one, so it is not accepted
///    until a probe measures it), any `Drop`/`Unreachable`/`Resume`;
/// 2. a return type that is not the pinned Direct-tag std `Option<iN>`
///    ([`crate::facet_inference::ty_is_std_option_of_signed`] — every niche
///    layout is refused there), or a return SLOT whose declared type disagrees
///    with it;
/// 3. any `(from, to)` pair other than `(i128, i64)`, and any unsigned
///    parameter or payload (both sides are pinned `signed: true`);
/// 4. bounds that are not EXACTLY the `i64::MIN`/`i64::MAX` literals in the
///    measured `Ge`-then-`Le` order and polarity ([`narrow_guarded_param`]);
/// 5. two false-edges that do not reach the SAME `None` block — which is what
///    makes an ARMS-SWAPPED body (`Some` reachable with either comparison
///    false) structurally impossible rather than merely unmatched;
/// 6. a `Some` arm that is not exactly `_t = <the guarded param> as iN
///    (IntToInt); _0 = Some(move _t)` — one cast into a fresh bare temp of the
///    exact payload type, then the aggregate of exactly that temp: no extra
///    statement, no projection, no rewritten place, no cast of a DIFFERENT
///    local (cross-parameter smuggling), no aliased payload;
/// 7. a `None` arm whose aggregate is not variant 0 with NO operands at the
///    pinned instantiation — a promoted `const Some(0)` sitting in that slot
///    arrives as variant 1 with one operand and is refused by VALUE, never
///    accepted by type alone;
/// 8. mismatched arm join blocks, a non-`Return` join, an effectful join, an
///    `||` guard (its arms are a bool constant and a comparison, neither of
///    which parses as an Option arm), a `switchInt` with a third successor or a
///    non-`0` case value, a projected/aliased guard temp, guard temps that are
///    not distinct fresh `bool` locals;
/// 9. ANY block that is neither one of the five named blocks nor a `goto`
///    trampoline the chaser actually walked (the final census) — so the c10
///    trampoline is handled while any other extra block fails closed. In
///    particular the UNGUARDED `Some(x as i64)` body (probe c11) is a single
///    block with no `switchInt` at all and can never reach this shape.
fn recognize_guarded_narrow(func: &VerifiableFunction) -> Option<AdmissibleBody> {
    // A body with an `Assert` is panicking (or is unchecked arithmetic): refuse
    // before reading anything else — the checked lane's discipline, unchanged.
    if func
        .body
        .blocks
        .iter()
        .any(|b| matches!(b.terminator, Terminator::Assert { .. }))
    {
        return None;
    }
    // The pinned std Option-of-signed return shape, agreeing with the return
    // slot's own declared type.
    let to_bits = crate::facet_inference::ty_is_std_option_of_signed(&func.body.return_ty)?;
    let ret_local = func.body.locals.iter().find(|l| l.index == 0)?;
    if ret_local.ty != func.body.return_ty {
        return None;
    }
    // MONOMORPHIC this increment: (i128 → Option<i64>) with the pinned
    // i64::MIN/i64::MAX bounds. Other widths and bound pairs PARK.
    if to_bits != 64 {
        return None;
    }
    let from_bits = 128u32;

    let blocks = &func.body.blocks;
    let n = func.body.arg_count;
    if n == 0 {
        return None;
    }
    let by_id = |id: BlockId| blocks.iter().find(|b| b.id == id);

    // ── the conjunction guard: two comparison blocks, reached by EDGE ────────
    let entry = blocks.first()?;
    let (lo_leaf, g_lo, lo_false, second_id) = narrow_guard_block(entry, n)?;
    let second = by_id(second_id)?;
    let (hi_leaf, g_hi, hi_false, some_id) = narrow_guard_block(second, n)?;
    // Two DISTINCT fresh `bool` temporaries: neither is a parameter or the
    // return place, so neither guard scrutinee can alias a value the arms use.
    if g_lo == g_hi
        || g_lo <= n
        || g_hi <= n
        || declared_ty(func, g_lo)? != &Ty::Bool
        || declared_ty(func, g_hi)? != &Ty::Bool
    {
        return None;
    }
    // The narrowed parameter — bounded by BOTH leaves, declared at the source
    // signed width.
    let param = narrow_guarded_param(lo_leaf, hi_leaf, to_bits)?;
    if !bare_local_has_signed_width(func, param + 1, from_bits) {
        return None;
    }

    // BOTH false edges must land on the SAME `None` block (possibly through a
    // measured bookkeeping trampoline). This is rule 5: it is what forbids the
    // arms-swapped body structurally.
    let mut trampolines: Vec<BlockId> = Vec::new();
    let none_blk = chase_goto_trampolines(blocks, lo_false, &mut trampolines)?;
    let none_from_hi = chase_goto_trampolines(blocks, hi_false, &mut trampolines)?;
    if none_blk.id != none_from_hi.id {
        return None;
    }

    // ── the Some arm: exactly the cast then the aggregate ────────────────────
    let some_blk = by_id(some_id)?;
    let mut effectful = some_blk.stmts.iter().filter(|s| !is_value_neutral(s));
    let (cast_stmt, agg_stmt) = (effectful.next()?, effectful.next()?);
    if effectful.next().is_some() {
        return None;
    }
    let Statement::Assign { place: t_place, rvalue: Rvalue::Cast(src, cast_ty), .. } = cast_stmt
    else {
        return None;
    };
    let payload_ty = Ty::Int { width: to_bits, signed: true };
    let t = bare_nonreturn_temp(func, t_place)?;
    // The extracted `Rvalue::Cast` does not carry rustc's `CastKind`, so the
    // KIND is pinned by TYPES instead: an integer SOURCE (this exact `i128`
    // parameter local, by declared type) and an integer TARGET of the payload
    // width. The only rustc cast kind with an `iW → iN` signature is
    // `IntToInt`: `FloatToInt`/`IntToFloat` need a float end, `PtrToPtr` a
    // pointer target, and the extractor's `Transmute` leg only ever yields a
    // POINTER-source or pointer/box-target `Cast`. So this IS the measured
    // two's-complement truncation, and the mint models it as such.
    if *cast_ty != payload_ty
        || declared_ty(func, t)? != &payload_ty
        || t <= n
        || t == g_lo
        || t == g_hi
        || param_of_operand(src, n)? != param
    {
        return None;
    }
    let Statement::Assign { place: sp, rvalue: Rvalue::Aggregate(s_kind, s_ops), .. } = agg_stmt
    else {
        return None;
    };
    if sp.local != 0
        || !sp.projections.is_empty()
        || !is_option_aggregate(s_kind, 1, to_bits)
        || s_ops.len() != 1
        || bare_local(&s_ops[0])? != t
    {
        return None;
    }
    let Terminator::Goto(some_join) = &some_blk.terminator else {
        return None;
    };

    // ── the None arm: the payload-less variant, by VALUE ─────────────────────
    let Statement::Assign { place: np, rvalue: Rvalue::Aggregate(n_kind, n_ops), .. } =
        sole_effectful(&none_blk.stmts)?
    else {
        return None;
    };
    let Terminator::Goto(none_join) = &none_blk.terminator else {
        return None;
    };
    if np.local != 0
        || !np.projections.is_empty()
        || !is_option_aggregate(n_kind, 0, to_bits)
        || !n_ops.is_empty()
        || some_join != none_join
    {
        return None;
    }

    // ── the join: bookkeeping only, then return ──────────────────────────────
    let join = by_id(*some_join)?;
    if !matches!(join.terminator, Terminator::Return)
        || join.stmts.iter().any(|s| !is_value_neutral(s))
    {
        return None;
    }

    // Census: every block is one of the five named ones or a trampoline the
    // chaser walked. Any other block — a second cast, a `cold_path` hint, an
    // unreached arm — fails the recognition closed.
    let mut named: Vec<BlockId> = vec![entry.id, second.id, some_blk.id, none_blk.id, join.id];
    named.extend(trampolines);
    named.sort_by_key(|b| b.0);
    named.dedup();
    if named.len() != blocks.len() {
        return None;
    }

    Some(AdmissibleBody::GuardedNarrow { from_bits, to_bits, param })
}

/// The WIDENING-CAST comparison shape (see [`AdmissibleBody::WidenedEq`]) —
/// `fn eq_ok(machine: i64, truth: i128) -> bool { Wide::from(machine) == truth }`
/// as `-O` lowers it: ONE basic block whose two value statements are the
/// sign-extending cast of a narrow parameter into a fresh temporary, then an
/// `Eq` of that temporary against a wide parameter, assigned to the return
/// place, then `Return`.
///
/// FAIL CLOSED on every deviation, each gate named where it is written:
///   * more than one block, or a terminator other than `Return`;
///   * a value-statement count other than exactly two, which is what refuses
///     `(a as i128) == (b as i128)` (BOTH sides cast — three statements) and
///     `(c.field as i128) == t` (a field read first — three statements);
///   * the two statements in the other order, or either one not an `Assign`;
///   * a projected place on either write, or a projected/aliased cast source;
///   * a cast destination that is not a FRESH non-parameter, non-return
///     temporary, or whose declared type disagrees with the cast target type;
///   * a cast source that is not a bare PARAMETER (so a cast of a call result
///     or of a struct field never reaches the mint);
///   * a non-SIGNED source or target carrier — a `u64` source at the identical
///     spelling is ZERO extension, and a `u128` target is a different carrier;
///   * a width pair other than the measured `(64, 128)`, which is what refuses
///     the TRUNCATING `(x as i64) == t` at `i128 → i64` and the unmeasured
///     `(a as i64) == b` at `i32 → i64`;
///   * any comparison other than `Eq` — `Ne`, `Lt`, `Le`, `Gt`, `Ge` all park;
///   * a non-parameter other operand (a literal bound needs a range check the
///     mint does not do here), or an other operand that is the SAME parameter
///     as the cast source, or one not declared at the wide carrier;
///   * a declared return type, or a return-place declared type, other than
///     `bool`.
fn recognize_widened_eq(func: &VerifiableFunction) -> Option<AdmissibleBody> {
    // MONOMORPHIC this increment: signed 64 → signed 128 only.
    let (from_bits, to_bits) = (64u32, 128u32);

    let [block] = &func.body.blocks[..] else {
        return None;
    };
    if !matches!(block.terminator, Terminator::Return) {
        return None;
    }
    // The decision is a `bool`, by the signature AND by the return place's own
    // declared type — a same-shaped body at any other type fails closed.
    if func.body.return_ty != Ty::Bool || declared_ty(func, 0)? != &Ty::Bool {
        return None;
    }
    let n = func.body.arg_count;

    // EXACTLY two value-carrying statements, in the measured order: the cast,
    // then the comparison. A third (a second cast, a field read) is refused.
    let mut effectful = block.stmts.iter().filter(|s| !is_value_neutral(s));
    let (cast_stmt, cmp_stmt) = (effectful.next()?, effectful.next()?);
    if effectful.next().is_some() {
        return None;
    }

    // ── the cast: `_t = <narrow param> as iTO (IntToInt)` ────────────────────
    let Statement::Assign { place: t_place, rvalue: Rvalue::Cast(src, cast_ty), .. } = cast_stmt
    else {
        return None;
    };
    let wide_ty = Ty::Int { width: to_bits, signed: true };
    let t = bare_nonreturn_temp(func, t_place)?;
    // A fresh TEMPORARY, never a parameter: a parameter destination would mean
    // the cast overwrote an input the comparison then reads under its old name.
    if t <= n || *cast_ty != wide_ty || declared_ty(func, t)? != &wide_ty {
        return None;
    }
    // The cast SOURCE is a bare parameter declared at the NARROW SIGNED
    // carrier. Signedness here is the whole faithfulness gate: the identical
    // MIR over a `u64` source is ZERO extension, not sign extension.
    let narrow_param = param_of_operand(src, n)?;
    if !bare_local_has_signed_width(func, narrow_param + 1, from_bits) {
        return None;
    }

    // ── the comparison: `_0 = Eq(_t, <wide param>)`, either operand order ────
    let Statement::Assign { place: r_place, rvalue: Rvalue::BinaryOp(binop, opl, opr), .. } =
        cmp_stmt
    else {
        return None;
    };
    if r_place.local != 0 || !r_place.projections.is_empty() {
        return None;
    }
    // `Eq` ONLY. `Ne` has no `SelectCmp` and the ORDERED comparisons at mixed
    // widths are unmeasured; both park rather than being guessed at.
    if !matches!(binop, BinOp::Eq) {
        return None;
    }
    // Exactly ONE side is the cast temporary; the other is a bare parameter.
    let cast_on_left = match (bare_local(opl), bare_local(opr)) {
        (Some(l), _) if l == t => true,
        (_, Some(r)) if r == t => false,
        _ => return None,
    };
    let other = if cast_on_left { opr } else { opl };
    let wide_param = param_of_operand(other, n)?;
    // Distinct from the narrow source (their carriers already differ, but the
    // index is pinned so a malformed local table cannot collapse them), and
    // declared at the WIDE signed carrier.
    if wide_param == narrow_param || !bare_local_has_signed_width(func, wide_param + 1, to_bits) {
        return None;
    }

    Some(AdmissibleBody::WidenedEq { from_bits, to_bits, narrow_param, wide_param, cast_on_left })
}

/// The bare non-return local a place names, else `None`.
fn bare_nonreturn_temp(func: &VerifiableFunction, place: &crate::Place) -> Option<usize> {
    if !place.projections.is_empty() || place.local == 0 || place.local >= func.body.locals.len() {
        return None;
    }
    Some(place.local)
}

/// The DECLARED type of local `l`, requiring the canonical `decl.index == l`
/// agreement (a malformed serialized identity fails closed rather than typing
/// through the wrong row).
fn declared_ty(func: &VerifiableFunction, l: usize) -> Option<&Ty> {
    func.body.locals.get(l).filter(|decl| decl.index == l).map(|decl| &decl.ty)
}

/// `Some((dest_local, (src_local, field)))` when `stmt` is exactly
/// `_dest = copy/move (_src.field)` with a bare destination, else `None`.
fn field_read_of(func: &VerifiableFunction, stmt: &Statement) -> Option<(usize, (usize, usize))> {
    let Statement::Assign { place, rvalue: Rvalue::Use(op), .. } = stmt else {
        return None;
    };
    let dest = bare_nonreturn_temp(func, place)?;
    let (Operand::Copy(src) | Operand::Move(src)) = op else {
        return None;
    };
    let [Projection::Field(field)] = src.projections.as_slice() else {
        return None;
    };
    Some((dest, (src.local, *field)))
}

/// Whether local `l` is READ anywhere in the body — as an operand of any
/// statement rvalue, a call/assert/switch operand, or the base of any read
/// place. Used to pin the cold-hint destination as value-inert.
fn local_is_read_anywhere(func: &VerifiableFunction, l: usize) -> bool {
    let place_reads = |p: &crate::Place| p.local == l;
    let op_reads = |op: &Operand| match op {
        Operand::Copy(p) | Operand::Move(p) => place_reads(p),
        _ => false,
    };
    let rvalue_reads = |rv: &Rvalue| match rv {
        Rvalue::Use(op) | Rvalue::UnaryOp(_, op) | Rvalue::Cast(op, _) | Rvalue::Repeat(op, _) => {
            op_reads(op)
        }
        Rvalue::BinaryOp(_, a, b)
        | Rvalue::CheckedBinaryOp(_, a, b)
        | Rvalue::UncheckedBinaryOp(_, a, b) => op_reads(a) || op_reads(b),
        Rvalue::Aggregate(_, ops) => ops.iter().any(op_reads),
        Rvalue::Ref { place, .. }
        | Rvalue::Discriminant(place)
        | Rvalue::Len(place)
        | Rvalue::AddressOf(_, place)
        | Rvalue::CopyForDeref(place) => place_reads(place),
        Rvalue::PtrOffset { ptr, count } => op_reads(ptr) || op_reads(count),
        Rvalue::Unsupported { operands, .. } => operands.iter().any(op_reads),
    };
    func.body.blocks.iter().any(|blk| {
        blk.stmts.iter().any(|s| match s {
            Statement::Assign { rvalue, .. } => rvalue_reads(rvalue),
            Statement::Intrinsic { args, .. } => args.iter().any(op_reads),
            Statement::CopyNonOverlapping { src, dst, count, .. } => {
                op_reads(src) || op_reads(dst) || op_reads(count)
            }
            Statement::Unsupported { operands, .. } => operands.iter().any(op_reads),
            _ => false,
        }) || match &blk.terminator {
            Terminator::Call { args, .. } => args.iter().any(op_reads),
            Terminator::SwitchInt { discr, .. } => op_reads(discr),
            Terminator::Assert { cond, .. } => op_reads(cond),
            _ => false,
        }
    })
}

/// One arm of a [`recognize_bool_binary`] diamond: `_place = <const bool | cmp>;
/// goto <join>`. Returns `(value, place_local, join_block)`, else `None`.
fn bool_binary_arm(block: &BasicBlock, arg_count: usize) -> Option<(ArmValue, usize, BlockId)> {
    let Terminator::Goto(join) = &block.terminator else {
        return None;
    };
    let Statement::Assign { place, rvalue, .. } = sole_effectful(&block.stmts)? else {
        return None;
    };
    if !place.projections.is_empty() {
        return None;
    }
    let value = match rvalue {
        Rvalue::Use(Operand::Constant(ConstValue::Bool(b))) => ArmValue::ConstBool(*b),
        Rvalue::BinaryOp(binop, opl, opr) => {
            ArmValue::Cmp(comparison_leaf(binop, opl, opr, arg_count)?)
        }
        _ => return None,
    };
    Some((value, place.local, *join))
}

/// The [`ComparisonLeaf`] a MIR comparison `BinaryOp(binop, opl, opr)` denotes:
/// the same recognition — and the same `>`/`>=`-by-operand-swap normalization
/// and ≥1-parameter requirement — as an [`AdmissibleBody::ComparisonBool`]
/// body. `None` (fail closed) for a non-comparison `binop`, a projected or
/// non-parameter/non-literal operand, or a two-constant leaf (no parameter to
/// fix the carrier).
fn comparison_leaf(
    binop: &BinOp,
    opl: &Operand,
    opr: &Operand,
    arg_count: usize,
) -> Option<ComparisonLeaf> {
    let (cmp, opl, opr) = comparison_cmp(binop, opl, opr)?;
    let left = cmp_operand(opl, arg_count)?;
    let right = cmp_operand(opr, arg_count)?;
    if !matches!(left, CmpOperand::Param(_)) && !matches!(right, CmpOperand::Param(_)) {
        return None;
    }
    Some(ComparisonLeaf { cmp, left, right })
}

/// The sole non-bookkeeping statement, or `None` if there is not exactly one.
fn sole_effectful(stmts: &[Statement]) -> Option<&Statement> {
    let mut it = stmts.iter().filter(|s| !is_value_neutral(s));
    let first = it.next()?;
    if it.next().is_some() {
        return None;
    }
    Some(first)
}

/// The bare local a `Copy`/`Move` operand names (no projections), else `None`.
fn bare_local(op: &Operand) -> Option<usize> {
    match op {
        Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => Some(p.local),
        _ => None,
    }
}

/// The 0-based source parameter a `Copy`/`Move` operand names — a bare local in
/// `1..=arg_count` (local 0 is the return place) — else `None`.
fn param_of_operand(op: &Operand, arg_count: usize) -> Option<usize> {
    let local = bare_local(op)?;
    (local >= 1 && local <= arg_count).then_some(local - 1)
}

/// The comparison an [`AdmissibleBody::ComparisonBool`] body computes, with the
/// operands in the order the minted term must apply them.
///
/// `>` and `>=` are normalized to `<` and `<=` by swapping the operands. This is
/// deliberately NOT done in [`select_cmp`]: a select's two branch arms are
/// keyed to the `switchInt` edges, so swapping the comparison there without
/// swapping the arms would silently mint `max` where the program wrote `min` —
/// and the E9 goal closes whenever the island happens to be reversed the same
/// way, so a positive fixture would not catch it. A comparison-to-bool body has
/// no arms, so the swap is complete on its own.
fn comparison_cmp<'a>(
    binop: &BinOp,
    opl: &'a Operand,
    opr: &'a Operand,
) -> Option<(SelectCmp, &'a Operand, &'a Operand)> {
    Some(match binop {
        BinOp::Lt => (SelectCmp::Lt, opl, opr),
        BinOp::Le => (SelectCmp::Le, opl, opr),
        BinOp::Eq => (SelectCmp::Eq, opl, opr),
        BinOp::Gt => (SelectCmp::Lt, opr, opl),
        BinOp::Ge => (SelectCmp::Le, opr, opl),
        _ => return None,
    })
}

/// The [`CmpOperand`] an operand of a comparison-to-bool body denotes: a bare
/// parameter local, or an integer literal.
///
/// `ConstValue::Int` is accepted alongside `Uint` because a SIGNED literal
/// extracts as `Int(i128)` with NO width — reading only `Uint` would leave every
/// `i64` bound (`x <= i64::MAX`, `x >= -1`) unrecognized. The literal's carrier
/// is fixed by the other operand's declared parameter type, and the mint
/// range-checks the value against it (`Domain::numeral` /
/// `Domain::negative_numeral`), so an out-of-carrier literal fails closed there
/// rather than wrapping.
fn cmp_operand(op: &Operand, arg_count: usize) -> Option<CmpOperand> {
    match op {
        Operand::Constant(ConstValue::Uint(value, _)) => Some(CmpOperand::Const(*value)),
        Operand::Constant(ConstValue::Int(value)) => Some(if *value < 0 {
            CmpOperand::NegConst(value.unsigned_abs())
        } else {
            CmpOperand::Const(value.unsigned_abs())
        }),
        _ => param_of_operand(op, arg_count).map(CmpOperand::Param),
    }
}

/// The select comparison a `BinOp` denotes, or `None` if unsupported.
fn select_cmp(binop: &BinOp) -> Option<SelectCmp> {
    Some(match binop {
        BinOp::Lt => SelectCmp::Lt,
        BinOp::Le => SelectCmp::Le,
        BinOp::Eq => SelectCmp::Eq,
        _ => return None,
    })
}


/// A select branch block: `_temp = <param>; goto <join>`. Returns
/// `(param_index, temp_local, join_block)`, else `None`.
/// The struct-construction shape — see [`AdmissibleBody::AggregateFields`].
///
/// Two block layouts, which are the two the client code actually produces:
///
///   * ONE BLOCK — `_0 = S { a, b }; return`, every field a parameter or a
///     literal (`pack_constraint`, `literal_axiom`);
///   * FOUR BLOCKS — the `-O` select diamond feeding one field, exactly as
///     [`recognize_select`] describes it, with the JOIN block storing the
///     aggregate instead of returning the selected value (`sat_term`).
///
/// Anything else fails closed.
fn recognize_aggregate_fields(func: &VerifiableFunction) -> Option<AdmissibleBody> {
    let blocks = &func.body.blocks;
    let n = func.body.arg_count;

    let returns: Vec<usize> = blocks
        .iter()
        .enumerate()
        .filter(|(_, b)| matches!(b.terminator, Terminator::Return))
        .map(|(i, _)| i)
        .collect();

    match returns.as_slice() {
        // ONE return: the aggregate is stored once, and a field may be fed by
        // the select diamond that joins into this block.
        [only] => {
            let ops = aggregate_store_after_pure(&blocks[*only], n)?.1;
            let select = ((blocks.len() == 4 && *only == 3)
                || (blocks.len() == 3 && *only == 2))
                .then(|| recognize_select_into_temp(func))
                .flatten();
            let select_dest = select.as_ref().map(|(local, _)| *local);

            // Every local the body writes, with how many times. `-O` REUSES
            // PARAMETER SLOTS, so "local k holds parameter k-1" is true only
            // while nothing writes k -- resolving an operand by index without
            // checking that is how an earlier version of this walk reported a
            // parameter for a slot that had been overwritten with the cap.
            let mut writes: Vec<(usize, usize)> = Vec::new();
            for (block_index, block) in blocks.iter().enumerate() {
                for st in &block.stmts {
                    if let Statement::Assign { place, .. } = st {
                        if !place.projections.is_empty() {
                            return None;
                        }
                        writes.push((block_index, place.local));
                    }
                }
            }
            let written_count = |local: usize| writes.iter().filter(|(_, w)| *w == local).count();

            // A PARAMETER slot may be written only if it is the select's own
            // destination, and then exactly twice -- once in each arm, which is
            // what `recognize_select_into_temp` already proved about it. Any
            // other write into a parameter slot leaves that parameter
            // unresolvable here, so the body is refused.
            for param_local in 1..=n {
                if written_count(param_local) > 0 && Some(param_local) != select_dest {
                    return None;
                }
            }
            // …and the select's destination may be written ONLY in the arms.
            // Not a COUNT: `-O` leaves the arm that keeps the value a local
            // ALREADY holds empty, so the destination is written once in that
            // asymmetric shape and twice in the symmetric one. What matters is
            // that no write to it happens anywhere else, which is what makes
            // `recognize_select_into_temp`'s reading of it the whole story.
            if let Some(dest) = select_dest {
                // The arm blocks are exactly the interior Goto blocks: [1, 2]
                // in the four-block diamond, [1] in the coalesced three-block
                // form. Deriving them keeps the check exact in both shapes.
                let arms: Vec<usize> = blocks
                    .iter()
                    .enumerate()
                    .filter(|(i, b)| *i != 0 && matches!(b.terminator, Terminator::Goto(_)))
                    .map(|(i, _)| i)
                    .collect();
                if writes.iter().any(|(block_index, w)| *w == dest && !arms.contains(block_index)) {
                    return None;
                }
            }

            let mut fields = Vec::with_capacity(ops.len());
            for op in ops {
                let shape = match bare_local(op) {
                    Some(local) if Some(local) == select_dest => {
                        // The select's result, in whichever slot it landed.
                        Some(select.as_ref()?.1.clone())
                    }
                    Some(local) if (1..=n).contains(&local) && written_count(local) == 0 => {
                        // An UNTOUCHED parameter slot still holds its parameter.
                        Some(AdmissibleBody::Projection { param: local - 1 })
                    }
                    // A TEMP assigned exactly once, from a FIELD of an
                    // untouched parameter: `-O` copies `self.var` into a temp
                    // before building the aggregate, so `Lit::negate`'s `var`
                    // field arrives as `_2` where `_2 = _1.0`. Resolving that
                    // one hop is what lets a constructor that forwards a field
                    // be shaped at all.
                    Some(local)
                        if written_count(local) == 1
                            && !(1..=n).contains(&local)
                            && Some(local) != select_dest =>
                    {
                        field_projection_of_param(func, blocks, local, n)
                    }
                    // A literal, or a local this walk cannot account for: no
                    // shape for THIS field, and none claimed for it.
                    _ => None,
                };
                fields.push(shape);
            }
            Some(AdmissibleBody::AggregateFields { fields })
        }
        // TWO returns: `-O` if-converted the select, so EACH ARM builds its own
        // aggregate and returns it. See `recognize_two_arm_aggregate`.
        [a, b] if blocks.len() == 3 => recognize_two_arm_aggregate(func, *a, *b),
        _ => None,
    }
}

/// The shape of a TEMP that is assigned exactly once from one FIELD of a
/// parameter — `_2 = _1.0` — as an [`AdmissibleBody::FieldProjection`].
///
/// `None` for anything else: a multi-step chain, a projection deeper than one
/// field, a source that is not a parameter, or a parameter the body rewrites
/// (whose slot no longer holds it). Following exactly one hop is deliberate;
/// a general dataflow walk is a different increment and would need its own
/// faithfulness argument.
fn field_projection_of_param(
    func: &VerifiableFunction,
    blocks: &[BasicBlock],
    temp: usize,
    arg_count: usize,
) -> Option<AdmissibleBody> {
    let mut found = None;
    for block in blocks {
        for st in &block.stmts {
            let Statement::Assign { place, rvalue: Rvalue::Use(op), .. } = st else { continue };
            if place.local != temp || !place.projections.is_empty() {
                continue;
            }
            let (Operand::Copy(src) | Operand::Move(src)) = op else { return None };
            let [Projection::Field(field)] = src.projections.as_slice() else { return None };
            if !(1..=arg_count).contains(&src.local) {
                return None;
            }
            // The source parameter must not be rewritten anywhere, or its slot
            // no longer holds the parameter this shape names.
            if blocks.iter().any(|b| {
                b.stmts.iter().any(|s| {
                    matches!(s, Statement::Assign { place: p, .. } if p.local == src.local)
                })
            }) {
                return None;
            }
            let _ = func;
            found = Some(AdmissibleBody::FieldProjection { param: src.local - 1, field: *field });
        }
    }
    found
}

/// The sole aggregate store of a block, as `(kind, operands)` — and only when
/// it writes the BARE return place, is a struct (variant 0, no active field),
/// and has at least one operand.
/// Is this statement a PURE PRECURSOR: a write to a bare temp, by an rvalue
/// that reads memory it does not change and cannot diverge?
///
/// The whitelist is deliberately short and states what it excludes. `Ref` and
/// `AddressOf` create aliases, after which a later write through the alias is
/// invisible to this walk. `Len`, `Discriminant` and `CopyForDeref` read
/// through a pointer whose provenance the walk does not track. `Repeat` and
/// `Aggregate` build a second value the caller is not expecting. Anything not
/// named here is refused, so a new `Rvalue` variant is excluded until someone
/// decides otherwise -- the fail-closed direction.
///
/// `CheckedBinaryOp` is admitted: it is total by construction, returning the
/// wrapped value beside an overflow flag rather than diverging.
fn is_pure_precursor(st: &Statement, arg_count: usize) -> bool {
    let Statement::Assign { place, rvalue, .. } = st else {
        return false;
    };
    // A bare temp only: never the return slot, never a parameter slot (whose
    // contents other operands are resolved against by index), never a
    // projection (a field write is a mutation of something else).
    if place.local == 0 || place.local <= arg_count || !place.projections.is_empty() {
        return false;
    }
    matches!(
        rvalue,
        Rvalue::Use(_)
            | Rvalue::UnaryOp(_, _)
            | Rvalue::BinaryOp(_, _, _)
            | Rvalue::CheckedBinaryOp(_, _, _)
            | Rvalue::Cast(_, _)
    )
}

/// The block's aggregate store, allowing PURE PRECURSOR statements before it.
///
/// `sole_effectful` alone was too strict for any constructor that computes
/// before it builds. `Lit::pos`/`neg` are a bare `bb0[_0=aggregate|ret]` and
/// pass it; `Lit::negate` computes `!self.negated` first, so its shape is
/// `bb0[_2=use,_4=use,_3=unop,_0=aggregate|ret]` and the whole function was
/// refused -- not for anything about the aggregate, but for the three
/// statements feeding it.
///
/// The aggregate must still be the LAST effectful statement and the only one
/// writing the return slot; everything before it must be a pure write to a
/// temp. So the block computes some values and then builds one struct, which
/// is the shape being recognized.
fn aggregate_store_after_pure(
    block: &BasicBlock,
    arg_count: usize,
) -> Option<(&crate::AggregateKind, &Vec<Operand>)> {
    let effectful: Vec<&Statement> =
        block.stmts.iter().filter(|s| !is_value_neutral(s)).collect();
    let (last, before) = effectful.split_last()?;
    if !before.iter().all(|st| is_pure_precursor(st, arg_count)) {
        return None;
    }
    let Statement::Assign { place, rvalue: Rvalue::Aggregate(kind, ops), .. } = last else {
        return None;
    };
    if place.local != 0 || !place.projections.is_empty() || ops.is_empty() {
        return None;
    }
    let crate::AggregateKind::Adt { variant: 0, active_field: None, .. } = kind else {
        return None;
    };
    Some((kind, ops))
}

/// The strict shape: the aggregate is the block's ONLY effectful statement.
fn aggregate_store(block: &BasicBlock) -> Option<(&crate::AggregateKind, &Vec<Operand>)> {
    let Statement::Assign { place, rvalue: Rvalue::Aggregate(kind, ops), .. } =
        sole_effectful(&block.stmts)?
    else {
        return None;
    };
    if place.local != 0 || !place.projections.is_empty() || ops.is_empty() {
        return None;
    }
    let crate::AggregateKind::Adt { variant: 0, active_field: None, .. } = kind else {
        return None;
    };
    Some((kind, ops))
}

/// The if-converted select: `bb0` compares and switches to two arms, each of
/// which builds the SAME struct and returns it.
fn recognize_two_arm_aggregate(
    func: &VerifiableFunction,
    arm_a: usize,
    arm_b: usize,
) -> Option<AdmissibleBody> {
    let blocks = &func.body.blocks;
    let n = func.body.arg_count;
    let by_id = |id: BlockId| blocks.iter().position(|b| b.id == id);

    let entry = &blocks[0];
    if arm_a == 0 || arm_b == 0 {
        return None;
    }
    let Statement::Assign { place: cmp_place, rvalue: Rvalue::BinaryOp(binop, opl, opr), .. } =
        sole_effectful(&entry.stmts)?
    else {
        return None;
    };
    if !cmp_place.projections.is_empty() {
        return None;
    }
    let cmp = select_cmp(binop)?;
    let cmp_left = param_of_operand(opl, n)?;
    let cmp_right = param_of_operand(opr, n)?;
    let Terminator::SwitchInt { discr, targets, otherwise, .. } = &entry.terminator else {
        return None;
    };
    if bare_local(discr)? != cmp_place.local || targets.len() != 1 || targets[0].0 != 0 {
        return None;
    }
    // `targets[0]` is the FALSE edge, `otherwise` the TRUE edge — the same
    // keying `recognize_select` uses, so `then_param` really is the value taken
    // when the comparison holds.
    let false_idx = by_id(targets[0].1)?;
    let true_idx = by_id(*otherwise)?;
    let mut got = [false_idx, true_idx];
    let mut want = [arm_a, arm_b];
    got.sort_unstable();
    want.sort_unstable();
    if got != want {
        return None;
    }
    let (true_kind, true_ops) = aggregate_store(&blocks[true_idx])?;
    let (false_kind, false_ops) = aggregate_store(&blocks[false_idx])?;
    // Both arms must build the SAME struct, positionally. `AggregateKind` is
    // compared by the parts that decide identity here — the ADT path and the
    // variant — because a differing name or variant means the two arms are not
    // two spellings of one construction at all.
    let same_adt = match (true_kind, false_kind) {
        (
            crate::AggregateKind::Adt { name: tn, variant: tv, .. },
            crate::AggregateKind::Adt { name: fnm, variant: fv, .. },
        ) => tn == fnm && tv == fv,
        _ => false,
    };
    if !same_adt || true_ops.len() != false_ops.len() {
        return None;
    }
    let mut fields = Vec::with_capacity(true_ops.len());
    for (t_op, f_op) in true_ops.iter().zip(false_ops.iter()) {
        let shape = match (param_of_operand(t_op, n), param_of_operand(f_op, n)) {
            (Some(then_param), Some(else_param)) if then_param == else_param => {
                Some(AdmissibleBody::Projection { param: then_param })
            }
            (Some(then_param), Some(else_param)) => {
                Some(AdmissibleBody::Select { cmp, cmp_left, cmp_right, then_param, else_param })
            }
            // Not both parameters: no shape for this field.
            _ => None,
        };
        fields.push(shape);
    }
    Some(AdmissibleBody::AggregateFields { fields })
}

/// [`recognize_select`]'s diamond, but ending in a JOIN that does not itself
/// return the selected value -- the arms decide a local which something else in
/// the join block consumes. Returns that local and the select shape.
fn recognize_select_into_temp(func: &VerifiableFunction) -> Option<(usize, AdmissibleBody)> {
    let blocks = &func.body.blocks;
    let n = func.body.arg_count;
    let by_id = |id: BlockId| blocks.iter().find(|b| b.id == id);

    let entry = &blocks[0];
    let Statement::Assign { place: cmp_place, rvalue: Rvalue::BinaryOp(binop, opl, opr), .. } =
        sole_effectful_ignoring_contract(func, entry)?
    else {
        return None;
    };
    if !cmp_place.projections.is_empty() {
        return None;
    }
    let cmp = select_cmp(binop)?;
    let cmp_left = param_of_operand(opl, n)?;
    let cmp_right = param_of_operand(opr, n)?;
    let Terminator::SwitchInt { discr, targets, otherwise, .. } = &entry.terminator else {
        return None;
    };
    if bare_local(discr)? != cmp_place.local || targets.len() != 1 || targets[0].0 != 0 {
        return None;
    }
    let false_blk = by_id(targets[0].1)?;
    let true_blk = by_id(*otherwise)?;

    // An arm is either a single `L = <param>` store or EMPTY. `-O` leaves the
    // arm that keeps the value the local ALREADY holds with nothing to do:
    // `sat_term`'s measured shape is `bb1[|goto3] bb2[_2=use|goto3]`, where the
    // `coeff <= degree` arm is empty because `_2` already holds `coeff`.
    let arm = |b: &BasicBlock| -> Option<(Option<(usize, usize)>, BlockId)> {
        let Terminator::Goto(join) = &b.terminator else { return None };
        match sole_effectful_ignoring_contract(func, b) {
            None => Some((None, *join)),
            Some(Statement::Assign { place, rvalue: Rvalue::Use(op), .. }) => {
                if !place.projections.is_empty() {
                    return None;
                }
                Some((Some((param_of_operand(op, n)?, place.local)), *join))
            }
            Some(_) => None,
        }
    };
    // The newer upstream's `-O` goes one step further than the EMPTY arm: it
    // deletes the empty block entirely and points the switch edge STRAIGHT at
    // the join -- measured on `sat_term`, whose shape shrank from
    // `bb1[|goto3] bb2[_2=use|goto3] bb3[aggregate]` to
    // `bb1[_2=use|goto2] bb2[aggregate]`. An edge that lands on the block the
    // OTHER arm joins to IS that empty arm, and it means exactly what the
    // empty block meant: the local keeps what it had. Everything else about
    // the reading -- including the parameter-slot requirement that gives the
    // kept value a name -- is unchanged and still fails closed.
    let (then_store, else_store, then_join, else_join) =
        match (arm(true_blk), arm(false_blk)) {
            (Some((ts, tj)), Some((es, ej))) => (ts, es, tj, ej),
            (None, Some((es, ej))) if true_blk.id == ej => (None, es, ej, ej),
            (Some((ts, tj)), None) if false_blk.id == tj => (ts, None, tj, tj),
            _ => return None,
        };
    if then_join != else_join {
        return None;
    }

    let (dest, then_param, else_param) = match (then_store, else_store) {
        // Both arms store: the classic diamond.
        (Some((tp, tl)), Some((ep, el))) if tl == el => (tl, tp, ep),
        // One arm EMPTY: the local keeps what it had, which has a name only if
        // the local is a PARAMETER slot -- a temp's incoming value is undefined
        // here, so that refuses. `l - 1` is the parameter it still holds.
        (None, Some((ep, el))) if (1..=n).contains(&el) => (el, el - 1, ep),
        (Some((tp, tl)), None) if (1..=n).contains(&tl) => (tl, tp, tl - 1),
        _ => return None,
    };
    if dest == 0 {
        return None;
    }
    Some((dest, AdmissibleBody::Select { cmp, cmp_left, cmp_right, then_param, else_param }))
}

/// A block's sole effectful statement, DISREGARDING the contract lowering's own
/// store.
///
/// A closure-form `ensures` builds its predicate into an `Option<{closure}>`
/// local, and `-O` places that construction in the ENTRY block beside the
/// body's own first statement -- measured: `bb0[_4=aggregate,_5=binop|...]`.
/// `sole_effectful` then sees two statements and refuses, so writing a contract
/// stopped the body being RECOGNIZABLE, the same way it used to stop the body
/// being ADMISSIBLE (`facet_inference::is_contract_injected_ty`).
fn sole_effectful_ignoring_contract<'a>(
    func: &'a VerifiableFunction,
    block: &'a BasicBlock,
) -> Option<&'a Statement> {
    let mut kept = block.stmts.iter().filter(|st| {
        if is_value_neutral(st) {
            return false;
        }
        match st {
            Statement::Assign { place, .. } => !func.body.locals.get(place.local).is_some_and(|l| {
                crate::facet_inference::is_contract_injected_ty(&l.ty, &func.def_path)
            }),
            _ => true,
        }
    });
    let first = kept.next()?;
    kept.next().is_none().then_some(first)
}


/// A select branch block. Two admissible forms:
/// - `_temp = <operand>; goto <join>` — returns `(Some((operand, temp_local)), join)`,
///   the operand a source parameter or (§6f landing 3) a width-anchored
///   machine numeral;
/// - NO effectful statement at all, `goto <join>` — returns `(None, join)`;
///   admissible only when the caller can bind the shared temp to a parameter
///   (the arm-coalesced `-O` spelling; see `select_diamond`).
///
/// Anything else fails closed.
///
/// **The numeral's width anchor is the function's own unsigned return width**,
/// the same single-width anchor [`arith_operand`] and
/// [`select_literal_of_operand`] use — so a width-skewed or out-of-range arm
/// constant can never recognize, and the reflection's domain (derived from
/// that same return type) can never be at a width the emitted scalar is not
/// at.
fn select_arm(
    block: &BasicBlock,
    arg_count: usize,
    func: &VerifiableFunction,
) -> Option<(Option<(ArithOperand, usize)>, BlockId)> {
    let Terminator::Goto(join) = &block.terminator else {
        return None;
    };
    let mut effectful = block.stmts.iter().filter(|s| !is_value_neutral(s));
    let Some(stmt) = effectful.next() else {
        return Some((None, *join));
    };
    if effectful.next().is_some() {
        return None;
    }
    let Statement::Assign { place, rvalue: Rvalue::Use(op), .. } = stmt else {
        return None;
    };
    if !place.projections.is_empty() {
        return None;
    }
    let operand = match param_of_operand(op, arg_count) {
        Some(param) => ArithOperand::Param(param),
        None => ArithOperand::Const(select_arm_literal(op, func)?),
    };
    Some((Some((operand, place.local)), *join))
}

/// The machine-integer literal a select ARM assigns, or `None` (fail closed).
/// §6f landing 3, and deliberately the SAME anchor
/// [`select_literal_of_operand`] applies to a comparison literal: the function
/// must return an unsigned machine width, and the constant's encoded width and
/// value must both agree with it.
fn select_arm_literal(op: &Operand, func: &VerifiableFunction) -> Option<u128> {
    let Ty::Int { width, signed: false } = func.body.return_ty else {
        return None;
    };
    if !matches!(width, 8 | 16 | 32 | 64) || !function_returns_unsigned_width(func, width) {
        return None;
    }
    match op {
        Operand::Constant(ConstValue::Uint(v, encoded_width))
            if *encoded_width == width && uint_fits_width(*v, width) =>
        {
            Some(*v)
        }
        _ => None,
    }
}

// ───────────────────────────────────────────────────────────────────────────
// Structural single-step Nat recursion (R1, §6e as amended + §6f)
// ───────────────────────────────────────────────────────────────────────────

/// One arm's value in a structural-recursion body over the SOLE `Nat`
/// parameter's case analysis. Closed vocabulary; every constructor's kernel
/// rendering is measured (`trust-clean-origin/tests/r1_equation_probes.rs`,
/// the s-series).
///
/// The vocabulary deliberately has NO `Pair`/`Fst`/`Snd` this slice: the pair
/// result carrier (`Prod Nat Nat`) does not exist in `trust-clean-carrier`
/// yet, so no plan can reach a pair-valued arm and an unreachable arm is
/// exactly the untested-capability shape §6e's fast-lane-first discipline
/// forbids. The fib `.cov` equations are measured green at the kernel
/// (probe e4); the vocabulary grows the pair nodes in the increment that
/// lands the carrier.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RecBodyExpr {
    /// The decreasing parameter itself — `n`. Denotes `Nat.succ k` in the
    /// succ case and `0` in the zero case.
    Decreasing,
    /// `pred(n)` — the case binder `k`, computed by the emitted body as
    /// `Nat::sub(&n, &1)` (Lean's truncated `Nat.sub`, which IS the
    /// predecessor for subtrahend 1 on ALL inputs, `Nat.pred 0 = 0`
    /// included). Succ arm only.
    Pred,
    /// The self-call's RESULT — the recursor's `ih`. Succ arm only, exactly
    /// once.
    Rec,
    /// A `Nat` literal materialised via `trust_bignum::Nat::from_u64`.
    NatConst(u64),
    /// `Nat` addition through the bignum runtime (`trust_bignum::Nat::add`).
    Add(Box<RecBodyExpr>, Box<RecBodyExpr>),
    /// `Nat` multiplication through the bignum runtime
    /// (`trust_bignum::Nat::mul`). Added 2026-08-25; it is what makes the
    /// FACTORIAL fragment (`if h : 0 < n then n * fact (n - 1) else 1`)
    /// reachable, and it is a strictly additive node — the emitted MIR is the
    /// `Add` chain with one callee changed, and the kernel identification it
    /// rests on (`a * b ≡ Nat.mul a b`, with `a * b ≢ Nat.add a b`) is
    /// measured in `trust-clean-origin/tests/r6_nat_mul_probes.rs` q7.
    Mul(Box<RecBodyExpr>, Box<RecBodyExpr>),
    /// GENERAL truncated `Nat` subtraction through the bignum runtime
    /// (`trust_bignum::Nat::sub`, whose `checked_sub(..).unwrap_or(ZERO)` IS
    /// Lean's `Nat.sub`). Added 2026-08-27 by R3b, and it is what makes
    /// SUBTRACTIVE EUCLID reachable — the fuelled step map
    /// `(a, b) ↦ ((a-b)+(b-a), a-(a-b))` is `|a-b|` and `min a b` written in
    /// truncated `-` and `+` alone.
    ///
    /// **[`Self::Pred`] is the SAME callee at one argument shape, and that is a
    /// hazard, not a redundancy.** `Sub(Decreasing, NatConst(1))` and `Pred`
    /// would denote one position in two spellings — the thing the `Param` /
    /// `Decreasing` note below is written against — so BOTH readers
    /// canonicalise that exact pattern to `Pred` in the succ arm and neither
    /// ever constructs it as a `Sub` (side A: `read_wf_value`; side B:
    /// `walk_structural_arm`). The zero arm keeps refusing it outright, since a
    /// predecessor there has no recursor-minor reading.
    ///
    /// The kernel identification it rests on is measured BEFORE this producer
    /// was written, in `trust-clean-origin/tests/gcd_route_probes.rs` m1:
    /// `a - b = Nat.sub a b` closes by `rfl`, and the wrong-op twin
    /// (`Nat.add`), the wrong-ORDER twin (`Nat.sub b a` — `Nat.sub` is not
    /// commutative, unlike `+` and `*`), a wrong value and a wrong truncation
    /// are all REFUSED. So subtraction's asymmetry is the kernel's decision.
    Sub(Box<RecBodyExpr>, Box<RecBodyExpr>),
    /// TOTAL `Nat` remainder through the bignum runtime
    /// (`trust_bignum::Nat::rem`, whose `checked_div_rem(..)`-else-the-dividend
    /// IS Lean's `Nat.mod`, `n % 0 = n` included). Added 2026-08-28 by §R8, and
    /// it is what makes the TEXTBOOK MODULO `gcd` reachable —
    /// `if h : 0 < b then gcd b (a % b) else a`, the Euclidean step written the
    /// way a textbook writes it rather than as R3b's subtractive fuel form.
    ///
    /// **Operand ORDER is load-bearing and is the kernel's decision, not this
    /// node's.** Like `-` and unlike `+`/`*`, `%` is not commutative; the
    /// identification and its refuting twins were measured BEFORE this node
    /// existed, in `trust-clean-origin/tests/r8_nat_mod_probes.rs` q1:
    /// `a % b = Nat.mod a b` closes by `rfl`, and the wrong-ORDER twin
    /// (`Nat.mod b a`), the SIBLING-OP twin (`Nat.div a b` — the other half of
    /// the same `checked_div_rem`, and the likeliest emitter mutation), the
    /// `Nat.sub`/`Nat.add`/`Nat.mul` twins and a wrong value are all REFUSED.
    ///
    /// **This node carries NO panic-freedom claim, because there is no panic on
    /// this lane to be free of.** See [`PrimitiveCallee::NatRem`] for the full
    /// accounting: the realization is a `Call`, not an `Rvalue::BinaryOp`, so
    /// no zero-divisor `Assert` is emitted; what stands in its place is the
    /// carrier's totality agreement, carried by trust-bignum's kernel-
    /// differential test rather than by any `Faithful` token. The obligation
    /// the compiler genuinely discharges here is the DECREASE (`a % b < b` from
    /// the guard's `0 < b`), and `q5` is its undischarged-case control.
    ///
    /// Unlike [`Self::Sub`] there is no canonicalisation hazard: no other
    /// `RecBodyExpr` spelling denotes `Nat.mod`, so `Rem` is the only tree for
    /// this position on BOTH readers.
    Rem(Box<RecBodyExpr>, Box<RecBodyExpr>),
    /// A NON-MEASURE parameter, by its 0-based SOURCE index — the nodes a
    /// multi-parameter recursion threads alongside the one it descends on.
    /// Added 2026-08-26 by R3a (the arity widening).
    ///
    /// **`Param(i)` and [`Self::Decreasing`] are disjoint by construction, and
    /// that disjointness is what makes the direct structural equality in
    /// `admit_lowering` meaningful.** `Decreasing` denotes the MEASURE
    /// parameter — the one the emitted zero test decides and the emitted
    /// `sub(&_, &1)` takes the predecessor of; every reader canonicalises that
    /// one position to `Decreasing` and never to `Param(measure_index)`. Two
    /// spellings for one position would let a side-A tree and a side-B tree
    /// denote the same thing and compare unequal (or worse, the reverse).
    ///
    /// The kernel identification it rests on is POSITIONAL and is measured in
    /// `trust-clean-origin/tests/r7_arity_widening_probes.rs` q3: `sel a b = b`
    /// closes by `rfl` and the same-shaped `sel a b = a` is REFUSED, so
    /// parameter order is the kernel's decision rather than this vocabulary's
    /// assumption.
    Param(usize),
}

impl RecBodyExpr {
    /// Whether `self` contains the node `probe` anywhere.
    #[must_use]
    pub fn contains(&self, probe: &RecBodyExpr) -> bool {
        if self == probe {
            return true;
        }
        match self {
            Self::Add(left, right) | Self::Mul(left, right) | Self::Sub(left, right) => {
                left.contains(probe) || right.contains(probe)
            }
            _ => false,
        }
    }

    /// The number of occurrences of the node `probe`.
    #[must_use]
    pub fn count(&self, probe: &RecBodyExpr) -> usize {
        let here = usize::from(self == probe);
        match self {
            Self::Add(left, right) | Self::Mul(left, right) | Self::Sub(left, right) => {
                here + left.count(probe) + right.count(probe)
            }
            _ => here,
        }
    }

    /// The number of ARITHMETIC nodes (`+`, `*` and the GENERAL `-`) — bounds
    /// recursion depth for consumers.
    ///
    /// Renamed from `add_nodes` when `Mul` landed: a bound that counted only
    /// `Add` would let a `Mul` tree of any depth through the very check that
    /// exists to bound emitter recursion, and a name that says `add` while
    /// counting both is the kind of drift this file is written against. R3b's
    /// `Sub` joined the same arm on the same reasoning, and on the day it
    /// landed — a node added to the vocabulary but not to this count is a hole
    /// in the only bound the emitter's recursion has. [`Self::Pred`] is NOT
    /// counted: it is a leaf, its operands are fixed, and it cannot nest.
    #[must_use]
    pub fn arith_nodes(&self) -> usize {
        match self {
            Self::Add(left, right) | Self::Mul(left, right) | Self::Sub(left, right) => {
                1 + left.arith_nodes() + right.arith_nodes()
            }
            _ => 0,
        }
    }

    /// Whether this tree names a NON-MEASURE parameter anywhere.
    ///
    /// The single-parameter lanes assert this is false rather than infer it
    /// from their arity gate: "a `Param` cannot occur at arity 1" is a property
    /// of the shared reader, and an entry point that is supposed to be provably
    /// unmoved must not rest on a property of code someone else may widen.
    #[must_use]
    pub fn mentions_other_parameter(&self) -> bool {
        match self {
            Self::Param(_) => true,
            Self::Add(left, right) | Self::Mul(left, right) | Self::Sub(left, right) => {
                left.mentions_other_parameter() || right.mentions_other_parameter()
            }
            _ => false,
        }
    }

    /// How many times this tree names the parameter at 0-based SOURCE index
    /// `index`, under a recursion whose measure sits at `measure_index`.
    ///
    /// One function rather than two `count` calls, because the caller must not
    /// have to remember the canonicalisation rule (the measure position is
    /// spelled [`Self::Decreasing`], never `Param(measure_index)`) at every
    /// site that bounds parameter use.
    #[must_use]
    pub fn parameter_uses(&self, index: usize, measure_index: usize) -> usize {
        if index == measure_index {
            self.count(&Self::Decreasing)
        } else {
            self.count(&Self::Param(index))
        }
    }
}

/// A recognized structural single-step recursion over the sole `Nat`
/// parameter: a bignum zero-test `SwitchInt`, a base arm, and a succ arm
/// containing exactly ONE self-call.
///
/// `rec_arg` is the self-call argument AS READ FROM DATAFLOW — recorded even
/// though recognition requires it to be [`RecBodyExpr::Pred`], so the kernel
/// layer re-decides it (`check_faithful_equations`, gate step 5 — the s4
/// divergence catch) rather than trusting this recognizer's requirement.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructuralRecBody {
    /// The zero-arm value. Never contains `Rec` or `Pred`.
    pub base: RecBodyExpr,
    /// The succ-arm value. Contains exactly one `Rec`.
    pub step: RecBodyExpr,
    /// The self-call argument, from dataflow.
    pub rec_arg: RecBodyExpr,
}

/// Whether a local type is the `Nat` bignum carrier, in either spelling this
/// boundary meets: the carrier decision's own [`Ty::BignumNat`], or the
/// EXTRACTED body's `Adt` naming the runtime type (`trust-mir-extract`
/// renders an ADT by path and knows nothing of the carrier variant).
///
/// SOUNDNESS NOTE (same accounting as `trust-clean-origin`'s `ty_to_domain`):
/// the name match is NOT what makes admission sound — nothing authenticates
/// the ADT here. It is sound because the recognized tree is put to the kernel
/// gate against side A; a wrong or impostor `Nat` yields a term the kernel
/// refuses to identify. The runtime-semantics claim (`is_zero`/`sub`/`add`/
/// `from_u64` realise `Nat`'s constructor analysis and arithmetic) is the
/// `trust_bignum` TCB row, never a kernel statement.
fn is_nat_carrier_ty(ty: &Ty) -> bool {
    match ty {
        Ty::BignumNat => true,
        Ty::Adt { name, .. } => name == "trust_bignum::Nat",
        _ => false,
    }
}

/// The bignum runtime operations the structural-recursion contract admits,
/// authenticated by exact def-path string plus local-type checks at every
/// use site (see [`is_nat_carrier_ty`] for the trust accounting).
#[derive(Clone, Copy, PartialEq, Eq)]
enum BignumOp {
    IsZero,
    FromU64,
    Sub,
    Add,
    Mul,
    Rem,
}

/// The [`BignumOp`] a callee def path names, or `None` (fail closed).
///
/// THE SPELLING OF A PATH IS DECIDED BY WHERE THE `impl` BLOCK WAS TYPED, not
/// by the method. rustc's inherent-impl path printer renders `Type::method`
/// when the `impl` sits in the module the type is declared in, and
/// `module::<impl Type>::method` when it does not. In trust-bignum, `Nat`,
/// `is_zero` and `from_u64` are all declared in the crate root, so those two
/// render co-located and have ONE row each; `add`, `sub` and `saturating_sub`
/// are declared in `mod arith`, so they render module-qualified and carry the
/// co-located row plus that one. Nothing about the operations differs.
///
/// MEASURED 2026-08-21, not assumed: an ordinary Rust
/// `n.sub(&Nat::from_u64(1))` extracted with `-Ztrust-dump=mir-only:<dir>`
/// carries `trust_bignum::Nat::from_u64` and
/// `trust_bignum::arith::<impl trust_bignum::Nat>::sub` in one body.
///
/// REVIEWED EXCEPTION to the standing side-B prohibition (recorded here
/// because a table of accepted callee strings is exactly the sort of thing
/// that must never grow to fit an emitter): the module-qualified rows were
/// added because the co-located rows for `add`/`sub`/`saturating_sub` name
/// paths that **no compilation can produce**, which made
/// [`BignumOp::Sub`], [`BignumOp::Add`], the whole [`RecBodyExpr::Add`]
/// vocabulary and this recognizer's own documented succ-arm contract
/// (`exactly ONE sub(&_1, &one)`) unreachable — a contract that cannot be
/// satisfied is not a strict reader, it is a dead one. The emitter was not
/// widened to and cannot reach these strings: it emits
/// `Operand::function_handle` for the DefId that `tcx.inherent_impls` returns
/// for the NAME `sub`, and the def path is then rendered by the extractor
/// from `TyCtxt` facts alone. No admitted SHAPE changed: same operations,
/// same arity, same operand discipline, same arm confinement, same kernel
/// gate downstream. The co-located rows are retained because they are the
/// rendering these same methods take the moment their `impl` block moves next
/// to `Nat` — as `is_zero`'s and `from_u64`'s already do.
///
/// A near-miss is still refused: a foreign crate's `sub`, and every SIBLING
/// of `sub` in the very same impl block (`mul`, `div`, `checked_sub`, …),
/// which share the whole `<impl …>` prefix. The trust accounting is unchanged
/// — the name is not what makes admission sound (see [`is_nat_carrier_ty`]);
/// the per-defining-equation kernel gate is.
///
/// SINCE LANDING 1 (§6f) this is a VIEW of [`PrimitiveCallee::classify`], which
/// holds the accepted spellings above verbatim and is the SOLE classifier the
/// emitter's callee resolution is also keyed on. The reviewed exception, the
/// near-miss discipline and the trust accounting are unchanged — the strings
/// moved, nothing about which strings are accepted did.
fn bignum_callee(callee: &str) -> Option<BignumOp> {
    match PrimitiveCallee::classify(callee)? {
        PrimitiveCallee::NatIsZero => Some(BignumOp::IsZero),
        PrimitiveCallee::NatFromU64 => Some(BignumOp::FromU64),
        PrimitiveCallee::NatSub => Some(BignumOp::Sub),
        PrimitiveCallee::NatAdd => Some(BignumOp::Add),
        PrimitiveCallee::NatMul => Some(BignumOp::Mul),
        PrimitiveCallee::NatRem => Some(BignumOp::Rem),
        PrimitiveCallee::WrappingAdd(_)
        | PrimitiveCallee::WrappingSub(_)
        | PrimitiveCallee::WrappingMul(_) => None,
    }
}

/// The declared type of a bare local, requiring the index to be in range and
/// self-consistent (the same discipline as [`bare_local_has_unsigned_width`]).
fn bare_local_ty<'f>(func: &'f VerifiableFunction, local: usize) -> Option<&'f Ty> {
    let decl = func.body.locals.get(local)?;
    (decl.index == local).then_some(&decl.ty)
}

/// Recognize a structural single-step `Nat` recursion from an extracted
/// body, or `None` (fail closed). **A SEPARATE entry point, deliberately NOT
/// an [`AdmissibleBody`] variant and NOT in [`recognize_admissible_body`]'s
/// chain**: every existing consumer of that chain — in particular the E6
/// kernel-import direction (`trust_certify::clean_island::admit_function_into`),
/// where a recognized body becomes a defining equation with NO side A and NO
/// kernel gate — must keep failing closed on recursive bodies until trust-mc's
/// `Termination` facet is Certified for them (§6e corollary). Keeping the
/// chain unchanged makes that fail-closed BY CONSTRUCTION: the import
/// direction cannot even see this shape. The sole intended consumer is
/// `trust-clean-origin`'s `admit_lowering`, where the recognized tree is put
/// to the per-defining-equation kernel gate (§6e as amended).
///
/// The exact MIR contract (everything else fails closed to `None`):
///
/// ```text
/// _0, _1 : Nat carrier  (arity exactly 1)
/// bb0:      _r = &_1
///           Call(trust_bignum::Nat::is_zero, [move _r]) -> _b: bool, bb1
/// bb1:      switchInt(_b) [(0, succ_start)] otherwise zero_start
/// zero…:    linear chain — from_u64 / add / value-identity copies — last
///           writes _0, into the Return block; NO sub, NO self-call
/// succ…:    same vocabulary plus exactly ONE `sub(&_1, &one)` predecessor
///           (one == from_u64(1)) and exactly ONE call whose callee string
///           equals `func.def_path`, whose argument's dataflow value is
///           REQUIRED to be that predecessor (belt at this layer; the kernel
///           re-decides it, braces at that layer)
/// ret:      Return (bookkeeping only), shared by both arms
/// ```
///
/// Every block of the body must be accounted for by exactly one of the four
/// regions — an unreachable or shared block fails closed.
#[must_use]
pub fn recognize_structural_rec(func: &VerifiableFunction) -> Option<StructuralRecBody> {
    // R1's OWN entry point stays pinned at arity 1, so R1's reading is
    // provably unmoved by R3a's widening (2026-08-26). The bytes are read by
    // ONE reader — two readers of one contract can only drift — but this
    // wrapper admits nothing R1 did not admit before: at arity 1 there is no
    // non-measure parameter, so `measure_index` is forced to 0 and
    // `RecBodyExpr::Param` is unconstructible. The last two conditions are
    // therefore redundant with the arity gate; they are asserted anyway,
    // because "unconstructible" is a claim about the shared reader and this
    // entry point must not rest on it.
    let ZeroTestRec { base, step, rec_args, measure_index } =
        recognize_zero_test_rec(func, GuardedArgument::Predecessor)?;
    if rec_args.len() != 1 || measure_index != 0 {
        return None;
    }
    let rec_arg = rec_args.into_iter().next()?;
    if base.mentions_other_parameter()
        || step.mentions_other_parameter()
        || rec_arg.mentions_other_parameter()
    {
        return None;
    }
    Some(StructuralRecBody { base, step, rec_arg })
}

/// The shared reading of the zero-test recursion MIR contract, at ANY arity.
///
/// One reader for the bytes both lanes emit; the DENOTATION is the caller's
/// (see [`recognize_wf_nat_rec`]'s note on why the delegation is the
/// measurement rather than a shortcut).
struct ZeroTestRec {
    base: RecBodyExpr,
    step: RecBodyExpr,
    /// Indexed by 0-based source parameter position; length = arity.
    rec_args: Vec<RecBodyExpr>,
    measure_index: usize,
}

fn recognize_zero_test_rec(
    func: &VerifiableFunction,
    guarded: GuardedArgument,
) -> Option<ZeroTestRec> {
    let expanded = func.with_tail_calls_expanded();
    let func = expanded.as_ref();
    let blocks = &func.body.blocks;

    let arity = func.body.arg_count;
    if arity == 0 {
        return None;
    }
    if !is_nat_carrier_ty(&func.body.return_ty) || !is_nat_carrier_ty(bare_local_ty(func, 0)?) {
        return None;
    }
    for index in 1..=arity {
        if !is_nat_carrier_ty(bare_local_ty(func, index)?) {
            return None;
        }
    }
    // Minimum: entry, switch, one block per arm, return.
    if blocks.len() < 5 {
        return None;
    }

    // Exactly one Return block, bookkeeping-only.
    let mut returns = blocks.iter().filter(|b| matches!(b.terminator, Terminator::Return));
    let ret_blk = returns.next()?;
    if returns.next().is_some() || ret_blk.stmts.iter().any(|s| !is_value_neutral(s)) {
        return None;
    }
    let ret_id = ret_blk.id;

    // ── entry: `_r = &_1; is_zero(move _r) -> _b` ───────────────────────────
    let entry = &blocks[0];
    let Statement::Assign {
        place: ref_place,
        rvalue: Rvalue::Ref { mutable: false, place: referent },
        ..
    } = sole_effectful(&entry.stmts)?
    else {
        return None;
    };
    // THE MEASURE IS READ FROM THE MIR, never assumed: it is the parameter the
    // entry block's zero test decides, and (below) the one the succ arm takes
    // the predecessor of. A body that tests one parameter and decreases another
    // fails the `Sub` arm's `Decreasing` requirement and reads back as `None`.
    if !ref_place.projections.is_empty()
        || !referent.projections.is_empty()
        || referent.local == 0
        || referent.local > arity
    {
        return None;
    }
    let measure_index = referent.local - 1;
    if !matches!(
        bare_local_ty(func, ref_place.local)?,
        Ty::Ref { mutable: false, inner } if is_nat_carrier_ty(inner.as_ref())
    ) {
        return None;
    }
    let Terminator::Call { func: callee, args, dest, target, .. } = &entry.terminator else {
        return None;
    };
    if bignum_callee(callee) != Some(BignumOp::IsZero) {
        return None;
    }
    let [arg] = &args[..] else {
        return None;
    };
    if bare_local(arg)? != ref_place.local {
        return None;
    }
    if !dest.projections.is_empty() || bare_local_ty(func, dest.local)? != &Ty::Bool {
        return None;
    }
    let switch_blk = blocks.iter().find(|b| Some(b.id) == *target)?;

    // ── the case split: `switchInt(_b) [(0, succ)] otherwise zero` ─────────
    if switch_blk.stmts.iter().any(|s| !is_value_neutral(s)) {
        return None;
    }
    let Terminator::SwitchInt { discr, targets, otherwise, .. } = &switch_blk.terminator else {
        return None;
    };
    if bare_local(discr)? != dest.local || targets.len() != 1 || targets[0].0 != 0 {
        return None;
    }
    // `is_zero` FALSE (0) means a nonzero `n`: the succ arm. TRUE (`otherwise`)
    // is the zero arm. This polarity is the contract; a swapped emission puts
    // the self-call in the zero arm and fails the arm walk below.
    let succ_start = targets[0].1;
    let zero_start = *otherwise;

    let layout = ArmLayout { arity, measure_index };
    let (base, zero_rec_args, zero_visited) =
        walk_structural_arm(func, zero_start, ret_id, Arm::Zero, layout)?;
    if zero_rec_args.is_some() {
        return None; // defensive: Arm::Zero already refuses self-calls
    }
    let (step, succ_rec_args, succ_visited) =
        walk_structural_arm(func, succ_start, ret_id, Arm::Succ, layout)?;
    let rec_args = succ_rec_args?;

    // Belt at the structural layer: the self-call's argument AT THE GUARDED
    // POSITION must be the predecessor — for the callers that ask for it. (The
    // kernel layer re-decides this from the recorded value — braces — so a
    // recognizer defect here alone cannot admit.) The other positions are
    // ordinary values and are deliberately NOT constrained here: they carry no
    // termination weight, and constraining them would be this recognizer
    // deciding a question the kernel decides.
    //
    // R3d made it a PARAMETER because phase 3's guarded position is an ordinary
    // value too — see `recognize_wf_sum_measure_rec`. Nothing else in this
    // reader moved.
    if rec_args.len() != arity {
        return None;
    }
    if guarded == GuardedArgument::Predecessor
        && rec_args.get(measure_index)? != &RecBodyExpr::Pred
    {
        return None;
    }
    // The base arm must be recursion-free in VALUE as well as in calls.
    if base.contains(&RecBodyExpr::Rec) || base.contains(&RecBodyExpr::Pred) {
        return None;
    }
    // Exactly one recursive result in the step value.
    if step.count(&RecBodyExpr::Rec) != 1 {
        return None;
    }

    // Coverage: every block is exactly one of entry, switch, ret, or a member
    // of exactly one arm region.
    let mut seen: Vec<BlockId> = vec![entry.id, switch_blk.id, ret_id];
    seen.extend(zero_visited.iter().copied());
    seen.extend(succ_visited.iter().copied());
    if seen.len() != blocks.len() {
        return None;
    }
    let mut deduped = seen.clone();
    deduped.sort_by_key(|id| id.0);
    deduped.dedup();
    if deduped.len() != seen.len() {
        return None;
    }

    Some(ZeroTestRec { base, step, rec_args, measure_index })
}

/// A recognized WELL-FOUNDED `Nat` recursion (R2, widened to any arity by R3a
/// with the measure still a SINGLE parameter), read out
/// of exactly the same emitted MIR contract as [`recognize_structural_rec`].
///
/// The FIELD NAMES are the R2 denotation and they are not R1's: a well-founded
/// functional has no case family and no case substitution, so the two arms are
/// named by the ZERO TEST that selects them rather than by a constructor. The
/// values themselves are the same MIR dataflow reading, in the same
/// [`RecBodyExpr`] vocabulary — a vocabulary reuse, not a producer edit (the
/// `WrappingBinOp`/`ArithBinOp` precedent).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WfRecBody {
    /// The value written when the parameter IS zero — side A's `dite` ELSE
    /// branch. Never contains `Rec` or `Pred`.
    pub zero_value: RecBodyExpr,
    /// The value written when the parameter is NONZERO — side A's `dite` THEN
    /// branch. Contains exactly one `Rec`.
    pub nonzero_value: RecBodyExpr,
    /// The self-call arguments, from dataflow, **indexed by 0-based SOURCE
    /// parameter position**. Length is always the body's arity.
    ///
    /// `rec_args[measure_index]` is the argument at the GUARDED position.
    /// [`recognize_wf_nat_rec`] requires it to be [`RecBodyExpr::Pred`] (that
    /// is phase 2's decreasing argument); [`recognize_wf_sum_measure_rec`] does
    /// not, because phase 3's decrease is stated about the MEASURE and proved
    /// by side A. The KERNEL re-decides it either way,
    /// because side B renders it into the functional's own `rec` slot where a
    /// non-decreasing argument cannot take side A's borrowed decrease proof
    /// (`trust-clean-origin/tests/r2_axiom_closure_probes.rs`, probe c6). The
    /// other positions are ordinary VALUE arguments and are decided the same
    /// way every other value in the functional is: by the type check of side B
    /// at side A's own functional type (gate step 7) and by the kernel defeq
    /// of the two functionals (gate step 8, argument-sensitive per w7/d3).
    pub rec_args: Vec<RecBodyExpr>,
    /// Which 0-based SOURCE parameter the emitted ZERO TEST decides — read
    /// from the MIR as the local the entry block's `is_zero` borrows (and, on
    /// the phase-2 door, the same local the succ arm's `sub(&_, &1)`
    /// predecessor is taken of).
    ///
    /// Carried rather than implied because side B's de Bruijn layout is
    /// indexed on it: the functional binds `x` (the measure) and `rec` before
    /// the remaining parameters, so a body whose measure sits at source
    /// position 1 renders its two parameters at different indices than one
    /// whose measure sits at position 0. R7 q1 measures both (`addAcc`,
    /// `addAcc2`).
    pub measure_index: usize,
}

/// Recognize a WELL-FOUNDED `Nat` recursion of ANY arity from an extracted
/// body (R2), or `None` (fail closed). **A SEPARATE entry point, for exactly
/// the reason [`recognize_structural_rec`] is one**: neither may join
/// [`recognize_admissible_body`]'s chain, because that chain also feeds the E6
/// kernel-import direction (`trust_certify::clean_island::admit_function_into`),
/// where a recognized body becomes a defining equation with NO side A and NO
/// kernel gate. Keeping the chain unchanged makes the import direction
/// fail-closed on recursive bodies BY CONSTRUCTION. The sole intended consumer
/// is `trust-clean-origin`'s `admit_lowering`, where the recognized tree is
/// reflected into a `WellFounded.fix` functional and put to the F-layer kernel
/// gate (`check_faithful_wf_functional`, §6e MEASUREMENT NOTE + ESCAPE CLOSED).
///
/// # It DELEGATES, and that is the measurement, not a shortcut
///
/// The MIR a well-founded `Nat` recursion emits is **the same contract** the
/// structural one emits — bignum zero test, linear arm regions, one
/// `sub(&n, &1)` predecessor, one self-call — because the emitted body is
/// built from the same runtime vocabulary at the same carrier and arity. There
/// is nothing for a second reader of those bytes to read differently, and two
/// readers of one contract can only drift. What differs between R1 and R2 is
/// the DENOTATION of the reading, and that lives entirely in the reflection:
/// R1 maps `Decreasing`/`Pred` through the recursor's case substitution
/// (`Nat.succ k` / `Nat.sub (Nat.succ k) 1`), R2 maps them to the functional's
/// own parameter binder (`x` / `Nat.sub x 1`).
///
/// **Consequence a widener must honour:** because this delegates, any widening
/// of the SHARED reader's contract widens R2's reading too. That is not
/// automatically wrong — both lanes end at a kernel gate — but it must be
/// re-measured against the R2 reflection in the same change, never assumed.
///
/// # R3a (2026-08-26): the shared reader is arity-parametric, R1's door is not
///
/// The widening moved the arity gate OUT of the shared reader and INTO the two
/// entry points, rather than duplicating the reader. R2's door (this one) takes
/// whatever arity the emitted body carries; R1's door
/// ([`recognize_structural_rec`]) still admits arity 1 alone, so its reading is
/// provably unmoved — at arity 1 there is no non-measure parameter,
/// `measure_index` can only be 0, and [`RecBodyExpr::Param`] is
/// unconstructible. `recognize_admissible_body`'s chain is untouched by both,
/// which is what keeps the E6 kernel-import direction
/// (`trust_certify::clean_island::admit_function_into`, no side A and no kernel
/// gate) fail-closed on recursive bodies BY CONSTRUCTION.
#[must_use]
pub fn recognize_wf_nat_rec(func: &VerifiableFunction) -> Option<WfRecBody> {
    let ZeroTestRec { base, step, rec_args, measure_index } =
        recognize_zero_test_rec(func, GuardedArgument::Predecessor)?;
    Some(WfRecBody { zero_value: base, nonzero_value: step, rec_args, measure_index })
}

/// Recognize a well-founded `Nat` recursion emitted for
/// `first-party/clean`'s **SUM-MEASURE lowering** (WF phase 3), or `None` (fail
/// closed). A THIRD entry point onto the SAME shared reader, for the same
/// reason the other two are separate: neither may join
/// [`recognize_admissible_body`]'s chain, which also feeds the E6 kernel-import
/// direction where a recognized body becomes a defining equation with no side A
/// and no kernel gate.
///
/// # It reads exactly the same MIR, and differs in exactly one belt
///
/// The emitted body is byte-identical to phase 2's: one bignum zero test on a
/// parameter, a `switchInt`, two linear arm regions, one self-call carrying one
/// operand per parameter. What this door drops is
/// [`GuardedArgument::Predecessor`] — the requirement that the self-call's
/// argument AT THE GUARDED POSITION be `Nat::sub(&n, &1)`.
///
/// **That belt is phase 2's TERMINATION contract, and it is not phase 3's.** At
/// `WfLowering::OnParameter` the fix runs on the guarded parameter itself, so
/// the only decrease side A can carry is by one and a body that decreased
/// otherwise would have no emission. At `WfLowering::OnMeasureValue` the fix
/// runs on the MEASURE'S VALUE: the self-call's arguments are ordinary values
/// with no termination weight, and what decreases is `m[a⃗] < m[p⃗]`, proved by
/// side A's own cascade in the slot the gate borrows. Requiring `Pred` here
/// would refuse a subtractive `gcd`'s `|a-b|` and `min a b` while establishing
/// nothing — the decrease it tests is not the one the recursion runs on.
///
/// Everything else this reader enforces is unchanged and still enforced: the
/// carriers, the block coverage, the zero-test polarity, a zero arm free of
/// `Rec`/`Pred`, and exactly one recursive result in the step value.
#[must_use]
pub fn recognize_wf_sum_measure_rec(func: &VerifiableFunction) -> Option<WfRecBody> {
    let ZeroTestRec { base, step, rec_args, measure_index } =
        recognize_zero_test_rec(func, GuardedArgument::Unconstrained)?;
    Some(WfRecBody {
        zero_value: base,
        nonzero_value: step,
        rec_args,
        measure_index,
    })
}

/// What the shared zero-test reader requires of the self-call's argument at the
/// GUARDED parameter's position.
///
/// A parameter rather than a constant because the two well-founded lowerings
/// disagree about it and nothing else — see
/// [`recognize_wf_sum_measure_rec`] for the measured reason.
#[derive(Clone, Copy, PartialEq, Eq)]
enum GuardedArgument {
    /// `Nat::sub(&n, &1)` — the emitted predecessor. R1's contract, and phase
    /// 2's.
    Predecessor,
    /// Any value the arm walk can read. Phase 3's: the decrease is stated about
    /// the measure, not about an argument, and side A carries its proof.
    Unconstrained,
}

/// The parameter layout one arm walk reads against: how many parameters there
/// are, and which of them the recursion descends on.
#[derive(Clone, Copy)]
struct ArmLayout {
    arity: usize,
    measure_index: usize,
}

impl ArmLayout {
    /// The value a parameter LOCAL seeds the dataflow with. The measure
    /// canonicalises to [`RecBodyExpr::Decreasing`] and never to
    /// `Param(measure_index)` — see that variant's note on why one position
    /// may not have two spellings.
    fn seed(self, source_index: usize) -> RecBodyExpr {
        if source_index == self.measure_index {
            RecBodyExpr::Decreasing
        } else {
            RecBodyExpr::Param(source_index)
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Arm {
    Zero,
    Succ,
}

/// Walk one linear arm region from `start` to the shared Return block,
/// resolving dataflow into a [`RecBodyExpr`]. Returns the arm's root value
/// (what it writes to `_0`), the recorded self-call argument (succ arm only),
/// and the visited block ids. Fail-closed on everything outside the contract.
fn walk_structural_arm(
    func: &VerifiableFunction,
    start: BlockId,
    ret_id: BlockId,
    arm: Arm,
    layout: ArmLayout,
) -> Option<(RecBodyExpr, Option<Vec<RecBodyExpr>>, Vec<BlockId>)> {
    use std::collections::BTreeMap;
    let blocks = &func.body.blocks;
    let by_id = |id: BlockId| blocks.iter().find(|b| b.id == id);

    // Dataflow: `vals` maps a Nat local to its value; `refs` maps a `&Nat`
    // local to the Nat local it borrows. EVERY parameter seeds the walk — the
    // measure as `Decreasing`, the rest by source index.
    let mut vals: BTreeMap<usize, RecBodyExpr> = BTreeMap::new();
    for source_index in 0..layout.arity {
        vals.insert(source_index + 1, layout.seed(source_index));
    }
    let mut refs: BTreeMap<usize, usize> = BTreeMap::new();
    let mut root: Option<RecBodyExpr> = None;
    let mut rec_arg: Option<Vec<RecBodyExpr>> = None;
    let mut visited: Vec<BlockId> = Vec::new();

    let mut cur = start;
    // The block count bounds the walk, so a cyclic region terminates refused.
    for _ in 0..=blocks.len() {
        if cur == ret_id {
            // Reached the shared Return: the arm is complete iff it wrote `_0`.
            return Some((root?, rec_arg, visited));
        }
        let blk = by_id(cur)?;
        if visited.contains(&cur) {
            return None;
        }
        visited.push(cur);

        for stmt in &blk.stmts {
            if is_value_neutral(stmt) {
                continue;
            }
            if root.is_some() {
                return None; // nothing effectful after the root write
            }
            let Statement::Assign { place, rvalue, .. } = stmt else {
                return None;
            };
            if !place.projections.is_empty() {
                return None;
            }
            match rvalue {
                // `_r = &_x` — borrow of a bare Nat local with a known value.
                Rvalue::Ref { mutable: false, place: referent } => {
                    if !referent.projections.is_empty()
                        || !vals.contains_key(&referent.local)
                        || !matches!(
                            bare_local_ty(func, place.local)?,
                            Ty::Ref { mutable: false, inner } if is_nat_carrier_ty(inner.as_ref())
                        )
                        || refs.insert(place.local, referent.local).is_some()
                    {
                        return None;
                    }
                }
                // Value identity through a bare Nat local (`_0 = move _t`).
                Rvalue::Use(Operand::Copy(p)) | Rvalue::Use(Operand::Move(p)) => {
                    if !p.projections.is_empty() {
                        return None;
                    }
                    let value = vals.get(&p.local)?.clone();
                    if place.local == 0 {
                        root = Some(value);
                    } else if !is_nat_carrier_ty(bare_local_ty(func, place.local)?)
                        || vals.insert(place.local, value).is_some()
                    {
                        return None;
                    }
                }
                _ => return None,
            }
        }

        match &blk.terminator {
            Terminator::Goto(target) => {
                // Only the post-root hop to the Return block.
                if *target != ret_id || root.is_none() {
                    return None;
                }
                cur = *target;
            }
            Terminator::Call { func: callee, args, dest, target, .. } => {
                if root.is_some() || !dest.projections.is_empty() {
                    return None;
                }
                let target = (*target)?;
                // Resolve a by-reference operand: a moved `&Nat` local.
                let deref = |operand: &Operand| -> Option<RecBodyExpr> {
                    let local = bare_local(operand)?;
                    vals.get(refs.get(&local)?).cloned()
                };
                let value = if let Some(op) = bignum_callee(callee) {
                    match op {
                        // The zero test belongs to the entry, never an arm.
                        BignumOp::IsZero => return None,
                        BignumOp::FromU64 => {
                            let [Operand::Constant(ConstValue::Uint(v, 64))] = &args[..] else {
                                return None;
                            };
                            RecBodyExpr::NatConst(u64::try_from(*v).ok()?)
                        }
                        // `-`, read as `+` and `*` are, with ONE extra step:
                        // the PREDECESSOR pattern is canonicalised away.
                        //
                        // R3b widened this from "the only admitted subtraction
                        // is `sub(&n, &1)`" to general truncated subtraction,
                        // which is what lets a step map like `a - (a - b)`
                        // (`min a b`) be read back. The canonicalisation is not
                        // cosmetic: `Pred` and `Sub(Decreasing, NatConst(1))`
                        // are the same emitted call, so leaving both readable
                        // would give one MIR position two side-B spellings and
                        // the gate's direct structural equality against side A
                        // (which canonicalises identically, `read_wf_value`)
                        // would compare unequal on a body that is correct.
                        //
                        // The ZERO-arm refusal of that one pattern is
                        // deliberately UNCHANGED — a predecessor there has no
                        // recursor-minor reading — while a general subtraction
                        // in the zero arm is ordinary arithmetic and is read.
                        BignumOp::Sub => {
                            let [lhs, rhs] = &args[..] else {
                                return None;
                            };
                            let (lhs, rhs) = (deref(lhs)?, deref(rhs)?);
                            if lhs == RecBodyExpr::Decreasing && rhs == RecBodyExpr::NatConst(1) {
                                if arm == Arm::Zero {
                                    return None;
                                }
                                RecBodyExpr::Pred
                            } else {
                                RecBodyExpr::Sub(Box::new(lhs), Box::new(rhs))
                            }
                        }
                        BignumOp::Add => {
                            let [lhs, rhs] = &args[..] else {
                                return None;
                            };
                            RecBodyExpr::Add(Box::new(deref(lhs)?), Box::new(deref(rhs)?))
                        }
                        // `*`, read exactly as `+` is — same by-reference
                        // operand discipline, same arm freedom, same
                        // fail-closed `deref`. The two are siblings in
                        // `trust_bignum`'s `mod arith` and siblings here.
                        BignumOp::Mul => {
                            let [lhs, rhs] = &args[..] else {
                                return None;
                            };
                            RecBodyExpr::Mul(Box::new(deref(lhs)?), Box::new(deref(rhs)?))
                        }
                        // `%`, read exactly as `+`/`*`/`-` are — same
                        // by-reference operand discipline, same arm freedom,
                        // same fail-closed `deref`. §R8.
                        //
                        // NO canonicalisation step, deliberately, and that is
                        // the difference from `Sub` above: no other
                        // `RecBodyExpr` spelling denotes `Nat.mod`, so there is
                        // no second tree for this position to collapse into and
                        // nothing for the two readers to disagree about.
                        //
                        // The operands are read POSITIONALLY and are never
                        // reordered or simplified — a DUMB reading, for
                        // `nat.sub`'s reason: `%` is not commutative, and
                        // deciding `a % b`'s operand order in Rust instead of at
                        // the kernel is authority this producer must not have.
                        BignumOp::Rem => {
                            let [lhs, rhs] = &args[..] else {
                                return None;
                            };
                            RecBodyExpr::Rem(Box::new(deref(lhs)?), Box::new(deref(rhs)?))
                        }
                    }
                } else if callee == &func.def_path {
                    // THE self-call. Succ arm only, at most once, by value, and
                    // at EXACTLY the body's own arity: a self-call the emitted
                    // signature could not accept is not this contract.
                    if arm == Arm::Zero || rec_arg.is_some() || args.len() != layout.arity {
                        return None;
                    }
                    let mut arguments = Vec::with_capacity(args.len());
                    for operand in args {
                        let local = bare_local(operand)?;
                        arguments.push(vals.get(&local).cloned()?);
                    }
                    rec_arg = Some(arguments);
                    RecBodyExpr::Rec
                } else {
                    return None;
                };

                if dest.local == 0 {
                    // The root write: the call must land directly on Return.
                    if target != ret_id {
                        return None;
                    }
                    root = Some(value);
                } else if !is_nat_carrier_ty(bare_local_ty(func, dest.local)?)
                    || vals.insert(dest.local, value).is_some()
                {
                    return None;
                }
                cur = target;
            }
            _ => return None,
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        BasicBlock, BlockId, LocalDecl, Place, Projection, SourceSpan, Ty, VerifiableBody,
        VerifiableFunction,
    };

    fn func(arg_count: usize, stmts: Vec<Statement>, term: Terminator) -> VerifiableFunction {
        VerifiableFunction {
            name: "f".into(),
            def_path: "crate::f".into(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: (0..8)
                    .map(|index| LocalDecl { index, ty: Ty::u64(), name: None })
                    .collect(),
                blocks: vec![BasicBlock { id: BlockId(0), stmts, terminator: term }],
                arg_count,
                return_ty: Ty::u64(),
                datatype_defs: Default::default(),
            },
            contracts: Vec::new(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            spec: Default::default(),
        }
    }

    fn assign(place: Place, rvalue: Rvalue) -> Statement {
        Statement::Assign { place, rvalue, span: SourceSpan::default() }
    }

    fn func_blocks(arg_count: usize, blocks: Vec<BasicBlock>) -> VerifiableFunction {
        let mut f = func(arg_count, Vec::new(), Terminator::Return);
        f.body.blocks = blocks;
        f
    }

    /// `Term { coeff: i64, lit: i64 }` — two scalar fields, one variant.
    fn term_adt() -> crate::AggregateKind {
        crate::AggregateKind::Adt {
            name: "veripb::Term".into(),
            variant: 0,
            active_field: None,
            args: None,
        }
    }

    /// The `-O` shape of SATURATE's per-term step with the cap inlined:
    ///
    /// ```text
    /// bb0: _5 = Le(_2, _1); switchInt(_5) [0 -> bb2, otherwise -> bb1]
    /// bb1: _4 = _2;         goto bb3
    /// bb2: _4 = _1;         goto bb3
    /// bb3: _0 = Term { _4, _3 }; return
    /// ```
    fn sat_term_shape(agg_ops: Vec<Operand>, kind: crate::AggregateKind) -> VerifiableFunction {
        func_blocks(
            3,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![assign(
                        Place::local(5),
                        Rvalue::BinaryOp(
                            crate::BinOp::Le,
                            Operand::Copy(Place::local(2)),
                            Operand::Copy(Place::local(1)),
                        ),
                    )],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Move(Place::local(5)),
                        targets: vec![(0, BlockId(2))],
                        otherwise: BlockId(1),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![assign(
                        Place::local(4),
                        Rvalue::Use(Operand::Copy(Place::local(2))),
                    )],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![assign(
                        Place::local(4),
                        Rvalue::Use(Operand::Copy(Place::local(1))),
                    )],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![assign(Place::local(0), Rvalue::Aggregate(kind, agg_ops))],
                    terminator: Terminator::Return,
                },
            ],
        )
    }

    /// The whole point of the shape: field 0 is the SELECT, field 1 is a
    /// parameter, and they are reported IN DECLARATION ORDER — a clause on
    /// `result.0` must not be able to bind to field 1's term.
    #[test]
    fn a_struct_build_is_recognized_field_by_field() {
        let f = sat_term_shape(
            vec![Operand::Move(Place::local(4)), Operand::Copy(Place::local(3))],
            term_adt(),
        );
        let Some(AdmissibleBody::AggregateFields { fields }) = recognize_admissible_body(&f) else {
            panic!("expected AggregateFields, got {:?}", recognize_admissible_body(&f));
        };
        assert_eq!(fields.len(), 2, "one shape per field: {fields:?}");
        assert!(
            matches!(
                fields[0],
                Some(AdmissibleBody::Select { cmp_left: 1, cmp_right: 0, then_param: 1, else_param: 0, .. })
            ),
            "field 0 is the select over (coeff, degree): {:?}",
            fields[0]
        );
        assert_eq!(
            fields[1],
            Some(AdmissibleBody::Projection { param: 2 }),
            "field 1 is the third parameter, verbatim"
        );
    }

    /// The `-O` IF-CONVERTED shape: the select is gone and EACH ARM builds its
    /// own aggregate and returns it.
    ///
    /// ```text
    /// bb0: _4 = Le(_2, _1); switchInt(_4) [0 -> bb2, otherwise -> bb1]
    /// bb1: _0 = Term { _2, _3 }; return      // coeff <= degree: keep coeff
    /// bb2: _0 = Term { _1, _3 }; return      // otherwise: the degree
    /// ```
    fn two_arm_shape(true_ops: Vec<Operand>, false_kind: crate::AggregateKind) -> VerifiableFunction {
        func_blocks(
            3,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![assign(
                        Place::local(4),
                        Rvalue::BinaryOp(
                            crate::BinOp::Le,
                            Operand::Copy(Place::local(2)),
                            Operand::Copy(Place::local(1)),
                        ),
                    )],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Move(Place::local(4)),
                        targets: vec![(0, BlockId(2))],
                        otherwise: BlockId(1),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![assign(Place::local(0), Rvalue::Aggregate(term_adt(), true_ops))],
                    terminator: Terminator::Return,
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![assign(
                        Place::local(0),
                        Rvalue::Aggregate(
                            false_kind,
                            vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(3))],
                        ),
                    )],
                    terminator: Terminator::Return,
                },
            ],
        )
    }

    /// REGRESSION. Reading only the first `Return` block reported
    /// `Projection { param: 1 }` for field 0 -- i.e. "the term keeps `coeff`"
    /// -- which is true on ONE arm and false on the other. Field 0 must be the
    /// SELECT, keyed to the switch edges, and field 1 (same parameter on both
    /// arms) must stay a projection.
    #[test]
    fn a_two_arm_aggregate_reports_the_select_not_one_arm() {
        let f = two_arm_shape(
            vec![Operand::Copy(Place::local(2)), Operand::Copy(Place::local(3))],
            term_adt(),
        );
        let Some(AdmissibleBody::AggregateFields { fields }) = recognize_admissible_body(&f) else {
            panic!("expected AggregateFields, got {:?}", recognize_admissible_body(&f));
        };
        assert_eq!(
            fields[0],
            Some(AdmissibleBody::Select {
                cmp: SelectCmp::Le,
                cmp_left: 1,
                cmp_right: 0,
                then_param: 1,
                else_param: 0,
            }),
            "field 0 is the cap, not either arm's operand"
        );
        assert_eq!(
            fields[1],
            Some(AdmissibleBody::Projection { param: 2 }),
            "field 1 is the same parameter on both arms"
        );
    }

    /// Two arms that build DIFFERENT structs are not two spellings of one
    /// construction, so the whole shape is refused.
    #[test]
    fn arms_building_different_structs_are_refused() {
        let other = crate::AggregateKind::Adt {
            name: "veripb::Other".into(),
            variant: 0,
            active_field: None,
            args: None,
        };
        let f = two_arm_shape(
            vec![Operand::Copy(Place::local(2)), Operand::Copy(Place::local(3))],
            other,
        );
        assert_eq!(recognize_admissible_body(&f), None, "differing ADTs must refuse");
    }

    /// `-O` reuses PARAMETER SLOTS for temporaries: the cap lands in `_2`,
    /// which is also `coeff`'s slot, and the aggregate reads `_2`.
    ///
    /// The property under test has never changed -- that operand must NOT be
    /// reported as `Projection { param: 1 }`, which would claim the term keeps
    /// `coeff` for a body that keeps the cap. What changed is the remedy: the
    /// walk used to refuse such a body outright, and now RESOLVES it, because
    /// the slot's writes are exactly the select's two arms.
    #[test]
    fn a_select_landing_in_a_parameter_slot_resolves_to_the_select() {
        let mut f = sat_term_shape(
            vec![Operand::Copy(Place::local(2)), Operand::Copy(Place::local(3))],
            term_adt(),
        );
        // Both arms write the PARAMETER slot `_2` instead of a fresh temp.
        f.body.blocks[1].stmts =
            vec![assign(Place::local(2), Rvalue::Use(Operand::Copy(Place::local(2))))];
        f.body.blocks[2].stmts =
            vec![assign(Place::local(2), Rvalue::Use(Operand::Copy(Place::local(1))))];
        let Some(AdmissibleBody::AggregateFields { fields }) = recognize_admissible_body(&f) else {
            panic!("expected AggregateFields, got {:?}", recognize_admissible_body(&f));
        };
        assert!(
            matches!(fields[0], Some(AdmissibleBody::Select { .. })),
            "the reused slot holds the SELECT, not `coeff`: {:?}",
            fields[0]
        );
        assert_eq!(
            fields[1],
            Some(AdmissibleBody::Projection { param: 2 }),
            "an untouched parameter slot still holds its parameter"
        );
    }

    /// A parameter slot written by something that is NOT the select is still
    /// unresolvable: nothing here says what it holds at the aggregate.
    #[test]
    fn a_parameter_slot_written_outside_the_select_refuses_the_body() {
        let mut f = sat_term_shape(
            vec![Operand::Copy(Place::local(4)), Operand::Copy(Place::local(3))],
            term_adt(),
        );
        // An extra write to `_3` -- `lit`'s slot -- in the entry block.
        f.body.blocks[0]
            .stmts
            .push(assign(Place::local(3), Rvalue::Use(Operand::Copy(Place::local(1)))));
        assert_eq!(
            recognize_admissible_body(&f),
            None,
            "a parameter slot clobbered outside the select cannot be resolved"
        );
    }

    /// THE MEASURED SHAPE of `sat_term` at `-O`, read off `TRUST_E6_DEBUG`:
    ///
    /// ```text
    /// bb0[_4=aggregate,_5=binop|switch[0->2]else1]
    /// bb1[|goto3]
    /// bb2[_2=use|goto3]
    /// bb3[_0=aggregate|ret]
    /// ```
    ///
    /// Two things this pins that no earlier fixture had. The arms are
    /// ASYMMETRIC -- the `coeff <= degree` arm is EMPTY, because `_2` already
    /// holds `coeff` and there is nothing to do -- and the entry block carries
    /// the CONTRACT closure's own construction (`_4=aggregate`) beside the
    /// comparison, which made `sole_effectful` refuse the block outright.
    #[test]
    fn the_measured_asymmetric_diamond_with_a_contract_store_is_recognized() {
        let lit = Ty::adt("crate::Lit", vec![("var".into(), Ty::u64()), ("neg".into(), Ty::Bool)]);
        let contract_ty = Ty::adt(
            "core::option::Option",
            vec![
                ("__tag".into(), Ty::Int { width: 64, signed: true }),
                (
                    "__v1_0".into(),
                    Ty::Closure {
                        name: "crate::sat::{closure#0}".into(),
                        upvars: vec![Ty::i64()],
                        call: None,
                    },
                ),
            ],
        );
        let mut f = func_blocks(
            3,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        // the contract closure, exactly where `-O` puts it
                        assign(
                            Place::local(4),
                            Rvalue::Aggregate(
                                crate::AggregateKind::Adt {
                                    name: "core::option::Option".into(),
                                    variant: 1,
                                    active_field: None,
                                    args: None,
                                },
                                vec![Operand::Copy(Place::local(1))],
                            ),
                        ),
                        assign(
                            Place::local(5),
                            Rvalue::BinaryOp(
                                crate::BinOp::Le,
                                Operand::Copy(Place::local(2)),
                                Operand::Copy(Place::local(1)),
                            ),
                        ),
                    ],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Move(Place::local(5)),
                        targets: vec![(0, BlockId(2))],
                        otherwise: BlockId(1),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                // EMPTY arm: `_2` already holds `coeff`.
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Goto(BlockId(3)) },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![assign(
                        Place::local(2),
                        Rvalue::Use(Operand::Copy(Place::local(1))),
                    )],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![assign(
                        Place::local(0),
                        Rvalue::Aggregate(
                            term_adt(),
                            vec![Operand::Copy(Place::local(2)), Operand::Copy(Place::local(3))],
                        ),
                    )],
                    terminator: Terminator::Return,
                },
            ],
        );
        f.def_path = "crate::sat".into();
        f.body.locals = vec![
            LocalDecl { index: 0, ty: Ty::u64(), name: None },
            LocalDecl { index: 1, ty: Ty::i64(), name: Some("degree".into()) },
            LocalDecl { index: 2, ty: Ty::i64(), name: Some("coeff".into()) },
            LocalDecl { index: 3, ty: lit, name: Some("lit".into()) },
            LocalDecl { index: 4, ty: contract_ty, name: None },
            LocalDecl { index: 5, ty: Ty::Bool, name: None },
        ];

        let Some(AdmissibleBody::AggregateFields { fields }) = recognize_admissible_body(&f) else {
            panic!("expected AggregateFields, got {:?}", recognize_admissible_body(&f));
        };
        assert_eq!(
            fields[0],
            Some(AdmissibleBody::Select {
                cmp: SelectCmp::Le,
                cmp_left: 1,
                cmp_right: 0,
                then_param: 1,
                else_param: 0,
            }),
            "the empty arm KEEPS `coeff`; only the other arm writes `degree`"
        );
        assert_eq!(fields[1], Some(AdmissibleBody::Projection { param: 2 }), "`lit`, untouched");
    }

    /// An ENUM construction is refused: a field there is variant-relative, so
    /// positional operands are not a write of the whole destination.
    #[test]
    fn an_enum_build_is_refused() {
        let enum_kind = crate::AggregateKind::Adt {
            name: "veripb::Maybe".into(),
            variant: 1,
            active_field: None,
            args: None,
        };
        let f = sat_term_shape(
            vec![Operand::Move(Place::local(4)), Operand::Copy(Place::local(3))],
            enum_kind,
        );
        assert_eq!(recognize_admissible_body(&f), None, "a non-zero variant must not recognize");
    }

    /// An operand that is neither a parameter nor the select's temp has no
    /// shape, so the whole aggregate fails closed rather than reporting a
    /// field it cannot account for.
    #[test]
    fn an_unresolved_field_operand_refuses_the_whole_aggregate() {
        let f = sat_term_shape(
            vec![Operand::Move(Place::local(4)), Operand::Copy(Place::local(9))],
            term_adt(),
        );
        // The SIBLING still shapes; only the unaccountable field is `None`, so
        // nothing is claimed for it and a clause naming it fails closed.
        let Some(AdmissibleBody::AggregateFields { fields }) = recognize_admissible_body(&f) else {
            panic!("expected AggregateFields, got {:?}", recognize_admissible_body(&f));
        };
        assert_eq!(fields[1], None, "local 9 is not a parameter or the temp");
    }

    fn two_block_call(callee: &str, args: Vec<Operand>, dest: Place) -> VerifiableFunction {
        func_blocks(
            2,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: Vec::new(),
                    terminator: Terminator::Call {
                        func: callee.into(),
                        args,
                        dest,
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_foreign: false,
                        is_unsafe_sig: false,
                        callee_identity: None,
                        unwind: crate::UnwindEdge::Unreachable,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: Vec::new(), terminator: Terminator::Return },
            ],
        )
    }

    /// R4 §1-executor FALSIFICATION BATTERY, part 1 (2026-07-22, written
    /// BEFORE any E6 recognizer widening): the census-motivated widening
    /// TARGETS, pinned refused at the current boundary. Each pin may flip
    /// only in a commit that lands that ONE shape with its faithfulness
    /// argument and elaborator arm — a widening that flips a pin as a side
    /// effect of something else is a red flag, not progress.
    #[test]
    fn widening_battery_census_targets_currently_refuse() {
        // (1) wrapping_sub: FLIPPED 2026-07-22 (E6 widening increment 1).
        // The historical exclusion predated trust-spec-elab's machine
        // subtraction; the Machine domain now elaborates `-` as the wrapping
        // carrier sub — exactly this primitive's unsigned semantics — and
        // admission is already restricted to unsigned carriers. The pin flips
        // POSITIVE with the shape it recognizes.
        let sub = two_block_call(
            "@trust-rustc-total-primitive-method::core::num::<impl u64>::wrapping_sub",
            vec![Operand::Copy(Place::local(1)), Operand::Constant(ConstValue::Uint(1, 64))],
            Place::local(0),
        );
        assert!(
            matches!(
                recognize_admissible_body(&sub),
                Some(AdmissibleBody::Arithmetic {
                    op: ArithBinOp::Sub,
                    left: ArithOperand::Param(0),
                    right: ArithOperand::Const(1),
                })
            ),
            "wrapping_sub now admits as machine wrapping subtraction"
        );

        // (2) FLIPPED 2026-07-22 (E6 widening increment 2): the two-write
        // straight-line body resolves by Use-chain substitution to its FINAL
        // dataflow — the last `_0` write wins, exactly the param projection.
        let two_writes = func(
            1,
            vec![
                assign(Place::local(0), Rvalue::Use(Operand::Constant(ConstValue::Uint(7, 64)))),
                assign(Place::local(0), Rvalue::Use(Operand::Copy(Place::local(1)))),
            ],
            Terminator::Return,
        );
        assert!(
            matches!(
                recognize_admissible_body(&two_writes),
                Some(AdmissibleBody::Projection { param: 0 })
            ),
            "the final dataflow, not the first write"
        );
        // Temp-chain form: `t = p0; _0 = t` resolves through the temporary.
        let via_temp = func(
            1,
            vec![
                assign(Place::local(2), Rvalue::Use(Operand::Copy(Place::local(1)))),
                assign(Place::local(0), Rvalue::Use(Operand::Move(Place::local(2)))),
            ],
            Terminator::Return,
        );
        assert!(matches!(
            recognize_admissible_body(&via_temp),
            Some(AdmissibleBody::Projection { param: 0 })
        ));
    }

    /// E6 widening increment 3 TARGET (written red, 2026-07-22): a linear
    /// multi-block chain of wrapping-primitive calls composing an arithmetic
    /// expression. Flips only in the commit landing the composed-expression
    /// vocabulary with its faithfulness argument.
    #[test]
    fn widening_battery_call_chain_target_currently_refuses() {
        // b0: _2 = wrapping_add(p0, 1) -> b1: _0 = wrapping_mul(_2, 2) -> b2: return
        let chain = func_blocks(
            1,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: Vec::new(),
                    terminator: Terminator::Call {
                        func: "@trust-rustc-total-primitive-method::core::num::<impl u64>::wrapping_add".into(),
                        args: vec![
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Uint(1, 64)),
                        ],
                        dest: Place::local(2),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_foreign: false,
                        is_unsafe_sig: false,
                        callee_identity: None,
                        unwind: crate::UnwindEdge::Unreachable,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: Vec::new(),
                    terminator: Terminator::Call {
                        func: "@trust-rustc-total-primitive-method::core::num::<impl u64>::wrapping_mul".into(),
                        args: vec![
                            Operand::Copy(Place::local(2)),
                            Operand::Constant(ConstValue::Uint(2, 64)),
                        ],
                        dest: Place::local(0),
                        target: Some(BlockId(2)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_foreign: false,
                        is_unsafe_sig: false,
                        callee_identity: None,
                        unwind: crate::UnwindEdge::Unreachable,
                    },
                },
                BasicBlock { id: BlockId(2), stmts: Vec::new(), terminator: Terminator::Return },
            ],
        );
        // FLIPPED 2026-07-22 (E6 widening increment 3): the chain composes to
        // the exact expression tree, node-for-node.
        assert_eq!(
            recognize_admissible_body(&chain),
            Some(AdmissibleBody::Composed {
                expr: ArithExpr::Bin {
                    op: ArithBinOp::Mul,
                    left: Box::new(ArithExpr::Bin {
                        op: ArithBinOp::Add,
                        left: Box::new(ArithExpr::Operand(ArithOperand::Param(0))),
                        right: Box::new(ArithExpr::Operand(ArithOperand::Const(1))),
                    }),
                    right: Box::new(ArithExpr::Operand(ArithOperand::Const(2))),
                },
            })
        );
    }

    /// E6 widening increment 3's forgery pins (pre-landed): call-chain shapes
    /// no composed-expression widening may ever admit.
    #[test]
    fn widening_battery_call_chain_forgeries_never_admit() {
        let prim_call = |callee: &str, args: Vec<Operand>, dest: Place, target: Option<BlockId>| {
            Terminator::Call {
                func: callee.into(),
                args,
                dest,
                target,
                span: SourceSpan::default(),
                atomic: None,
                is_foreign: false,
                is_unsafe_sig: false,
                callee_identity: None,
                unwind: crate::UnwindEdge::Unreachable,
            }
        };
        // (1) a NON-primitive call in the middle of the chain: arbitrary user
        // semantics must never compose into an admitted expression.
        let user_middle = func_blocks(
            1,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: Vec::new(),
                    terminator: prim_call(
                        "my_crate::helper",
                        vec![Operand::Copy(Place::local(1))],
                        Place::local(2),
                        Some(BlockId(1)),
                    ),
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: Vec::new(),
                    terminator: prim_call(
                        "@trust-rustc-total-primitive-method::core::num::<impl u64>::wrapping_add",
                        vec![
                            Operand::Copy(Place::local(2)),
                            Operand::Constant(ConstValue::Uint(1, 64)),
                        ],
                        Place::local(0),
                        Some(BlockId(2)),
                    ),
                },
                BasicBlock { id: BlockId(2), stmts: Vec::new(), terminator: Terminator::Return },
            ],
        );
        assert!(recognize_admissible_body(&user_middle).is_none(), "user call in chain");

        // (2) a BRANCHING chain (a call target that is not the next linear
        // block): control flow the composed expression would erase.
        let branching = func_blocks(
            1,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: Vec::new(),
                    terminator: prim_call(
                        "@trust-rustc-total-primitive-method::core::num::<impl u64>::wrapping_add",
                        vec![
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Uint(1, 64)),
                        ],
                        Place::local(0),
                        Some(BlockId(2)),
                    ),
                },
                BasicBlock { id: BlockId(1), stmts: Vec::new(), terminator: Terminator::Return },
                BasicBlock {
                    id: BlockId(2),
                    stmts: Vec::new(),
                    terminator: Terminator::Goto(BlockId(1)),
                },
            ],
        );
        assert!(recognize_admissible_body(&branching).is_none(), "non-linear chain");
    }

    /// E6 widening increment 2's OWN forgery pins: chain shapes the Use-chain
    /// recognizer must refuse forever.
    #[test]
    fn widening_battery_chain_forgeries_never_admit() {
        // (1) a chain containing a NON-Use rvalue (any computation) — the
        // chain's faithfulness argument is value identity only.
        let computes = func(
            1,
            vec![
                assign(
                    Place::local(2),
                    Rvalue::BinaryOp(
                        crate::BinOp::Add,
                        Operand::Copy(Place::local(1)),
                        Operand::Constant(ConstValue::Uint(1, 64)),
                    ),
                ),
                assign(Place::local(0), Rvalue::Use(Operand::Copy(Place::local(2)))),
            ],
            Terminator::Return,
        );
        assert!(recognize_admissible_body(&computes).is_none(), "computation in a Use-chain");

        // (2) a read of an UNRESOLVED local (uninitialized temp).
        let uninit = func(
            1,
            vec![
                assign(Place::local(0), Rvalue::Use(Operand::Copy(Place::local(3)))),
                assign(Place::local(2), Rvalue::Use(Operand::Copy(Place::local(1)))),
            ],
            Terminator::Return,
        );
        assert!(recognize_admissible_body(&uninit).is_none(), "uninitialized read");

        // (3) a projected WRITE mid-chain (partial state the resolution
        // would erase).
        let mut proj_place = Place::local(2);
        proj_place.projections.push(Projection::Field(0));
        let projected = func(
            1,
            vec![
                assign(proj_place, Rvalue::Use(Operand::Copy(Place::local(1)))),
                assign(Place::local(0), Rvalue::Use(Operand::Copy(Place::local(1)))),
            ],
            Terminator::Return,
        );
        assert!(recognize_admissible_body(&projected).is_none(), "projected write");
    }

    /// R4 §1-executor FALSIFICATION BATTERY, part 2: shapes NO widening may
    /// EVER admit. If any of these pins goes green, a false definitional
    /// import has been armed — treat as a soundness incident, not a test
    /// update.
    #[test]
    fn widening_battery_shapes_no_widening_may_ever_admit() {
        let operands =
            || vec![Operand::Copy(Place::local(1)), Operand::Constant(ConstValue::Uint(1, 64))];

        // (1) a USER function merely named wrapping_add, outside the
        // core::num primitive path: admitting it imports arbitrary user
        // semantics as the primitive.
        let user = two_block_call("my_crate::wrapping_add", operands(), Place::local(0));
        assert!(recognize_admissible_body(&user).is_none(), "user-named primitive forgery");

        // (2) the genuine primitive but the destination writes a PROJECTION
        // of the return place — a partial-return the imported constant would
        // misrepresent as the whole value.
        let mut projected_dest = Place::local(0);
        projected_dest.projections.push(Projection::Field(0));
        let partial = two_block_call(
            "@trust-rustc-total-primitive-method::core::num::<impl u64>::wrapping_add",
            operands(),
            projected_dest,
        );
        assert!(recognize_admissible_body(&partial).is_none(), "projected-return forgery");

        // (3) the genuine primitive with an EFFECTFUL statement beside the
        // recognized value flow — hidden state change the import would erase.
        let mut effectful = two_block_call(
            "@trust-rustc-total-primitive-method::core::num::<impl u64>::wrapping_add",
            operands(),
            Place::local(0),
        );
        effectful.body.blocks[0]
            .stmts
            .push(assign(Place::local(2), Rvalue::Use(Operand::Constant(ConstValue::Uint(9, 64)))));
        assert!(recognize_admissible_body(&effectful).is_none(), "effectful-sibling forgery");

        // (4) a DIVERGING call (no return target): there is no returned value
        // for a definitional import to be faithful to.
        let mut diverging = two_block_call(
            "@trust-rustc-total-primitive-method::core::num::<impl u64>::wrapping_add",
            operands(),
            Place::local(0),
        );
        if let Terminator::Call { target, .. } = &mut diverging.body.blocks[0].terminator {
            *target = None;
        }
        assert!(recognize_admissible_body(&diverging).is_none(), "diverging-call forgery");
    }

    #[test]
    fn recognizes_the_optimized_select_form() {
        use crate::BinOp;
        // The SAME min2 under -O: the branches write the RETURN PLACE `_0`
        // directly and the join is a bare `return` (only bookkeeping) — the
        // form compiletest's run-pass `-O` produces. Semantically identical
        // select; must recognize.
        let f = func_blocks(
            2,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![assign(
                        Place::local(3),
                        Rvalue::BinaryOp(
                            BinOp::Lt,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                    )],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(3)),
                        targets: vec![(0, BlockId(2))],
                        otherwise: BlockId(1),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![assign(
                        Place::local(0),
                        Rvalue::Use(Operand::Copy(Place::local(1))),
                    )],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![assign(
                        Place::local(0),
                        Rvalue::Use(Operand::Copy(Place::local(2))),
                    )],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
            ],
        );
        assert_eq!(
            recognize_admissible_body(&f),
            Some(AdmissibleBody::Select {
                cmp: SelectCmp::Lt,
                cmp_left: 0,
                cmp_right: 1,
                then_param: 0,
                else_param: 1,
            })
        );
        // An EFFECTFUL join statement in the direct-to-return form fails closed
        // (it could overwrite the selected value).
        let mut g = f.clone();
        g.body.blocks[3]
            .stmts
            .push(assign(Place::local(0), Rvalue::Use(Operand::Copy(Place::local(2)))));
        assert_eq!(recognize_admissible_body(&g), None);
    }

    #[test]
    fn recognizes_the_arm_coalesced_optimized_select_form() {
        use crate::BinOp;
        // The SAME min2 under -O after DestinationPropagation coalesced the
        // select temp into parameter `_1` (the exact stage2 `-Ztrust-dump=mir:`
        // shape behind the `e9_release_mode_discharge` debug/release
        // divergence, 2026-08-13): the TRUE arm is empty (its value stays in
        // `_1`), the FALSE arm overwrites `_1 = copy _2`, and the join returns
        // `_0 = copy _1`. Semantically identical select; must recognize.
        let f = func_blocks(
            2,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::StorageLive(3),
                        assign(
                            Place::local(3),
                            Rvalue::BinaryOp(
                                BinOp::Lt,
                                Operand::Copy(Place::local(1)),
                                Operand::Copy(Place::local(2)),
                            ),
                        ),
                    ],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Move(Place::local(3)),
                        targets: vec![(0, BlockId(2))],
                        otherwise: BlockId(1),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                // otherwise / true branch: a < b ⇒ the value is already in _1.
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                // 0 / false branch ⇒ overwrite the coalesced parameter with b.
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![assign(
                        Place::local(1),
                        Rvalue::Use(Operand::Copy(Place::local(2))),
                    )],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![
                        Statement::StorageDead(3),
                        assign(Place::local(0), Rvalue::Use(Operand::Copy(Place::local(1)))),
                    ],
                    terminator: Terminator::Return,
                },
            ],
        );
        assert_eq!(
            recognize_admissible_body(&f),
            Some(AdmissibleBody::Select {
                cmp: SelectCmp::Lt,
                cmp_left: 0,
                cmp_right: 1,
                then_param: 0, // a < b true ⇒ untouched _1 = a (param 0)
                else_param: 1, // else ⇒ _1 = copy _2 = b (param 1)
            })
        );

        // The mirrored coalescing (empty FALSE arm) resolves symmetrically.
        let mut g = f.clone();
        g.body.blocks[1].stmts =
            vec![assign(Place::local(1), Rvalue::Use(Operand::Copy(Place::local(2))))];
        g.body.blocks[2].stmts = vec![];
        assert_eq!(
            recognize_admissible_body(&g),
            Some(AdmissibleBody::Select {
                cmp: SelectCmp::Lt,
                cmp_left: 0,
                cmp_right: 1,
                then_param: 1,
                else_param: 0,
            })
        );

        // TWO empty arms select nothing nameable; fail closed.
        let mut bad = f.clone();
        bad.body.blocks[2].stmts = vec![];
        assert_eq!(recognize_admissible_body(&bad), None);

        // An empty arm whose sibling writes a NON-parameter temp has no entry
        // value to name; fail closed (this is the plain temp form with a
        // missing arm, not a coalescing).
        let mut bad = f.clone();
        bad.body.blocks[2].stmts =
            vec![assign(Place::local(5), Rvalue::Use(Operand::Copy(Place::local(2))))];
        assert_eq!(recognize_admissible_body(&bad), None);

        // A MOVE comparison operand may have consumed the coalesced parameter
        // before the empty arm reads it; fail closed.
        let mut bad = f.clone();
        bad.body.blocks[0].stmts = vec![
            Statement::StorageLive(3),
            assign(
                Place::local(3),
                Rvalue::BinaryOp(
                    BinOp::Lt,
                    Operand::Move(Place::local(1)),
                    Operand::Copy(Place::local(2)),
                ),
            ),
        ];
        assert_eq!(recognize_admissible_body(&bad), None);

        // The join must read the coalesced parameter, not something else.
        let mut bad = f;
        bad.body.blocks[3].stmts = vec![
            Statement::StorageDead(3),
            assign(Place::local(0), Rvalue::Use(Operand::Copy(Place::local(2)))),
        ];
        assert_eq!(recognize_admissible_body(&bad), None);
    }

    #[test]
    fn recognizes_a_select_min2() {
        use crate::BinOp;
        // fn min2(a, b) -> u64 { if a < b { a } else { b } } — the exact 4-block
        // rustc lowering: compare into _4, switch, each branch writes temp _3,
        // join returns _3.
        let f = func_blocks(
            2,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![assign(
                        Place::local(4),
                        Rvalue::BinaryOp(
                            BinOp::Lt,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                    )],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(4)),
                        targets: vec![(0, BlockId(2))],
                        otherwise: BlockId(1),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1), // otherwise / true branch: a < b ⇒ return a
                    stmts: vec![assign(
                        Place::local(3),
                        Rvalue::Use(Operand::Copy(Place::local(1))),
                    )],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(2), // 0 / false branch ⇒ return b
                    stmts: vec![assign(
                        Place::local(3),
                        Rvalue::Use(Operand::Copy(Place::local(2))),
                    )],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![assign(
                        Place::local(0),
                        Rvalue::Use(Operand::Copy(Place::local(3))),
                    )],
                    terminator: Terminator::Return,
                },
            ],
        );
        assert_eq!(
            recognize_admissible_body(&f),
            Some(AdmissibleBody::Select {
                cmp: SelectCmp::Lt,
                cmp_left: 0,
                cmp_right: 1,
                then_param: 0, // a < b true ⇒ a (param 0)
                else_param: 1, // else ⇒ b (param 1)
            })
        );

        // max2: same shape, branches swapped (then=b, else=a).
        let mut g = f.clone();
        g.body.blocks[1].stmts =
            vec![assign(Place::local(3), Rvalue::Use(Operand::Copy(Place::local(2))))];
        g.body.blocks[2].stmts =
            vec![assign(Place::local(3), Rvalue::Use(Operand::Copy(Place::local(1))))];
        assert_eq!(
            recognize_admissible_body(&g),
            Some(AdmissibleBody::Select {
                cmp: SelectCmp::Lt,
                cmp_left: 0,
                cmp_right: 1,
                then_param: 1,
                else_param: 0,
            })
        );

        // Fail closed if the two branches write DIFFERENT temps (not a clean
        // select diamond).
        let mut bad = f.clone();
        bad.body.blocks[2].stmts =
            vec![assign(Place::local(5), Rvalue::Use(Operand::Copy(Place::local(2))))];
        assert_eq!(recognize_admissible_body(&bad), None);
    }

    /// The R2/C9 param-vs-const compare diamond, with the literal-position
    /// knobs the forgery pins below turn.
    fn select_literal_diamond(cmp: BinOp, opl: Operand, opr: Operand) -> VerifiableFunction {
        func_blocks(
            2,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![assign(Place::local(4), Rvalue::BinaryOp(cmp, opl, opr))],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(4)),
                        targets: vec![(0, BlockId(2))],
                        otherwise: BlockId(1),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![assign(
                        Place::local(3),
                        Rvalue::Use(Operand::Copy(Place::local(1))),
                    )],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![assign(
                        Place::local(3),
                        Rvalue::Use(Operand::Copy(Place::local(2))),
                    )],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![assign(
                        Place::local(0),
                        Rvalue::Use(Operand::Copy(Place::local(3))),
                    )],
                    terminator: Terminator::Return,
                },
            ],
        )
    }

    /// R2/C9: `fn min10(a, b) -> u64 { if a < 10 { a } else { b } }` — the
    /// param-vs-const compare — recognizes as the EXACT `SelectLiteral`.
    #[test]
    fn recognizes_the_literal_compare_select() {
        use crate::BinOp;
        let f = select_literal_diamond(
            BinOp::Lt,
            Operand::Copy(Place::local(1)),
            Operand::Constant(ConstValue::Uint(10, 64)),
        );
        assert_eq!(
            recognize_admissible_body(&f),
            Some(AdmissibleBody::SelectLiteral {
                cmp: SelectCmp::Lt,
                cmp_param: 0,
                literal: 10,
                then_param: 0,
                else_param: 1,
            })
        );
        // gcd's guard shape: `if a == 0 { a } else { b }` at Eq.
        let g = select_literal_diamond(
            BinOp::Eq,
            Operand::Copy(Place::local(1)),
            Operand::Constant(ConstValue::Uint(0, 64)),
        );
        assert_eq!(
            recognize_admissible_body(&g),
            Some(AdmissibleBody::SelectLiteral {
                cmp: SelectCmp::Eq,
                cmp_param: 0,
                literal: 0,
                then_param: 0,
                else_param: 1,
            })
        );
    }

    /// R2/C9 FORGERY PINS (the standing amendment: a recognizer widening
    /// lands with its own adversarial pins). Each nearby-but-different body
    /// must stay `None`; a flip of any pin is a deliberate future widening
    /// with its own faithfulness argument, never a side effect.
    #[test]
    fn select_literal_forgery_pins_fail_closed() {
        use crate::BinOp;

        // (1) The literal on the LEFT of the compare (`if 10 < a`): outside
        // the fragment — the vocabulary places the literal strictly on the
        // right, mirroring `admit_select_literal_function`'s signature.
        let left = select_literal_diamond(
            BinOp::Lt,
            Operand::Constant(ConstValue::Uint(10, 64)),
            Operand::Copy(Place::local(1)),
        );
        assert_eq!(recognize_admissible_body(&left), None);

        // (2) BOTH operands literal: nothing parametric to select on.
        let both = select_literal_diamond(
            BinOp::Lt,
            Operand::Constant(ConstValue::Uint(1, 64)),
            Operand::Constant(ConstValue::Uint(10, 64)),
        );
        assert_eq!(recognize_admissible_body(&both), None);

        // (3) A literal ARM (`if a < 10 { 7 } else { b }`): constant arms
        // stay outside the fragment — e6 probe f03's boundary, untouched by
        // this widening.
        let mut const_arm = select_literal_diamond(
            BinOp::Lt,
            Operand::Copy(Place::local(1)),
            Operand::Constant(ConstValue::Uint(10, 64)),
        );
        const_arm.body.blocks[1].stmts =
            vec![assign(Place::local(3), Rvalue::Use(Operand::Constant(ConstValue::Uint(7, 64))))];
        assert_eq!(recognize_admissible_body(&const_arm), None);

        // (4) A width-skewed constant (u32-encoded literal in a u64 body):
        // the encoded width must be exactly the function's return width —
        // the same single-width anchor `arith_operand` enforces.
        let skewed = select_literal_diamond(
            BinOp::Lt,
            Operand::Copy(Place::local(1)),
            Operand::Constant(ConstValue::Uint(10, 32)),
        );
        assert_eq!(recognize_admissible_body(&skewed), None);

        // (5) A non-integer constant in the compare.
        let boolean = select_literal_diamond(
            BinOp::Eq,
            Operand::Copy(Place::local(1)),
            Operand::Constant(ConstValue::Bool(true)),
        );
        assert_eq!(recognize_admissible_body(&boolean), None);

        // (6) An unsupported comparison stays unsupported with a literal.
        let unsupported = select_literal_diamond(
            BinOp::Ne,
            Operand::Copy(Place::local(1)),
            Operand::Constant(ConstValue::Uint(10, 64)),
        );
        assert_eq!(recognize_admissible_body(&unsupported), None);

        // (7) A width-skewed COMPARISON PARAMETER: the compared local must be
        // declared at the function's width for the literal arm to recognize.
        let mut param_skew = select_literal_diamond(
            BinOp::Lt,
            Operand::Copy(Place::local(1)),
            Operand::Constant(ConstValue::Uint(10, 64)),
        );
        param_skew.body.locals[1].ty = Ty::Int { width: 32, signed: false };
        assert_eq!(recognize_admissible_body(&param_skew), None);

        // (8) The arm-coalesced `-O` spelling with a literal compare is NOT
        // recognized (the empty-arm rule requires both comparison operands
        // to be parameter COPIES; a literal there is unmeasured — refuse).
        let mut coalesced = select_literal_diamond(
            BinOp::Lt,
            Operand::Copy(Place::local(1)),
            Operand::Constant(ConstValue::Uint(10, 64)),
        );
        coalesced.body.blocks[1].stmts.clear();
        coalesced.body.blocks[2].stmts =
            vec![assign(Place::local(1), Rvalue::Use(Operand::Copy(Place::local(2))))];
        coalesced.body.blocks[3].stmts =
            vec![assign(Place::local(0), Rvalue::Use(Operand::Copy(Place::local(1))))];
        assert_eq!(recognize_admissible_body(&coalesced), None);
    }

    #[test]
    fn recognizes_wrapping_arithmetic() {
        // fn winc(x: u64) -> u64 { x.wrapping_add(1) } — the two-block Call shape.
        let call = |callee: &str, a: Operand, b: Operand| Terminator::Call {
            func: callee.into(),
            args: vec![a, b],
            dest: Place::local(0),
            target: Some(BlockId(1)),
            span: SourceSpan::default(),
            atomic: None,
            is_foreign: false,
            is_unsafe_sig: false,
            callee_identity: None,
            unwind: crate::UnwindEdge::Unreachable,
        };
        let winc = |t: Terminator, argc: usize| {
            func_blocks(
                argc,
                vec![
                    BasicBlock { id: BlockId(0), stmts: Vec::new(), terminator: t },
                    BasicBlock {
                        id: BlockId(1),
                        stmts: Vec::new(),
                        terminator: Terminator::Return,
                    },
                ],
            )
        };
        let f = winc(
            call(
                "@trust-rustc-total-primitive-method::core::num::<impl u64>::wrapping_add",
                Operand::Copy(Place::local(1)),
                Operand::Constant(ConstValue::Uint(1, 64)),
            ),
            1,
        );
        assert_eq!(
            recognize_admissible_body(&f),
            Some(AdmissibleBody::Arithmetic {
                op: ArithBinOp::Add,
                left: ArithOperand::Param(0),
                right: ArithOperand::Const(1),
            })
        );
        // wsum(x, y) = x.wrapping_add(y).
        let g = winc(
            call(
                "@trust-rustc-total-primitive-method::core::num::<impl u64>::wrapping_add",
                Operand::Copy(Place::local(1)),
                Operand::Copy(Place::local(2)),
            ),
            2,
        );
        assert_eq!(
            recognize_admissible_body(&g),
            Some(AdmissibleBody::Arithmetic {
                op: ArithBinOp::Add,
                left: ArithOperand::Param(0),
                right: ArithOperand::Param(1),
            })
        );
        // A user function merely NAMED wrapping_add fails closed.
        let bad = winc(
            call(
                "crate::wrapping_add",
                Operand::Copy(Place::local(1)),
                Operand::Copy(Place::local(1)),
            ),
            1,
        );
        assert_eq!(recognize_admissible_body(&bad), None);
        // wrapping_sub: recognized since the 2026-07-22 E6 widening
        // increment 1 (the Machine-domain `-` elaboration is the wrapping
        // carrier sub — see arith_method's doc; the widening battery carries the
        // authoritative pins).
        let sub = winc(
            call(
                "@trust-rustc-total-primitive-method::core::num::<impl u64>::wrapping_sub",
                Operand::Copy(Place::local(1)),
                Operand::Constant(ConstValue::Uint(1, 64)),
            ),
            1,
        );
        assert_eq!(
            recognize_admissible_body(&sub),
            Some(AdmissibleBody::Arithmetic {
                op: ArithBinOp::Sub,
                left: ArithOperand::Param(0),
                right: ArithOperand::Const(1),
            })
        );
    }

    #[test]
    fn tail_call_uses_the_same_admission_and_provenance_gates() {
        let tail = |callee: &str| {
            func(
                1,
                Vec::new(),
                Terminator::TailCall {
                    func: callee.to_string(),
                    args: vec![
                        Operand::Copy(Place::local(1)),
                        Operand::Constant(ConstValue::Uint(1, 64)),
                    ],
                    span: SourceSpan::default(),
                    atomic: None,
                    is_foreign: false,
                    is_unsafe_sig: false,
                    callee_identity: None,
                },
            )
        };

        assert_eq!(
            recognize_admissible_body(&tail(
                "@trust-rustc-total-primitive-method::core::num::<impl u64>::wrapping_add",
            )),
            Some(AdmissibleBody::Arithmetic {
                op: ArithBinOp::Add,
                left: ArithOperand::Param(0),
                right: ArithOperand::Const(1),
            })
        );
        assert_eq!(recognize_admissible_body(&tail("crate::wrapping_add")), None);
    }

    /// R2/C4 provenance pins: no recognizer arm reads the raw-binop spelling,
    /// and the two forms that LOOK like it must never be admitted as wrapping
    /// arithmetic by any future widening:
    ///
    /// * `Rvalue::UncheckedBinaryOp` is `unsafe { a.unchecked_add(b) }` under
    ///   `-O` — UB on overflow, its own variant since the R2/C4 extractor fix
    ///   (it used to extract indistinguishably from the wrapping op);
    /// * `Rvalue::CheckedBinaryOp` returns `(result, overflowed)`.
    ///
    /// The third pin holds TODAY's boundary: a bare `BinaryOp(Add)` sole
    /// statement is unrecognized (the C4 emitter emits the marker-
    /// authenticated call form; `control_5`'s natural-lowering trap pins the
    /// same fact from the emit lane). A widening that flips the third pin
    /// must carry the binop-form faithfulness argument (no name to forge;
    /// MIR `Add`/`Sub`/`Mul` wrapping-defined; provenance preserved at
    /// extraction) — and must NEVER flip the first two: if either admits, a
    /// false definitional import has been armed. Soundness incident, not a
    /// test update.
    #[test]
    fn binop_provenance_pins_never_admit() {
        let one_stmt =
            |rvalue: Rvalue| func(2, vec![assign(Place::local(0), rvalue)], Terminator::Return);
        let ops = || (Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2)));

        let (a, b) = ops();
        assert!(
            recognize_admissible_body(&one_stmt(Rvalue::UncheckedBinaryOp(BinOp::Add, a, b)))
                .is_none(),
            "UB-on-overflow provenance admitted as arithmetic"
        );
        let (a, b) = ops();
        assert!(
            recognize_admissible_body(&one_stmt(Rvalue::CheckedBinaryOp(BinOp::Add, a, b)))
                .is_none(),
            "pair-returning checked op admitted as arithmetic"
        );
        let (a, b) = ops();
        assert!(
            recognize_admissible_body(&one_stmt(Rvalue::BinaryOp(BinOp::Add, a, b))).is_none(),
            "the raw-binop spelling is outside the recognized fragment today"
        );
    }

    #[test]
    fn wrapping_arithmetic_marker_width_and_carrier_gate_fail_closed() {
        let marked_u64 = "@trust-rustc-total-primitive-method::core::num::<impl u64>::wrapping_add";
        let call = |callee: &str, rhs: ConstValue| {
            two_block_call(
                callee,
                vec![Operand::Copy(Place::local(1)), Operand::Constant(rhs)],
                Place::local(0),
            )
        };

        for bad in [
            call("core::num::<impl u64>::wrapping_add", ConstValue::Uint(1, 64)),
            call(
                "@trust-rustc-total-primitive-method::core::num::<impl u64>::wrapping_add::suffix",
                ConstValue::Uint(1, 64),
            ),
            call(
                "@trust-rustc-total-primitive-method::core::num::<impl u128>::wrapping_add",
                ConstValue::Uint(1, 128),
            ),
            call(
                "@trust-rustc-total-primitive-method::core::num::<impl usize>::wrapping_add",
                ConstValue::Uint(1, 64),
            ),
            call(
                "@trust-rustc-total-primitive-method::core::num::<impl i64>::wrapping_add",
                ConstValue::Uint(1, 64),
            ),
            call(
                "@trust-rustc-total-primitive-method::core::num::<impl u32>::wrapping_add",
                ConstValue::Uint(1, 32),
            ),
            call(marked_u64, ConstValue::Uint(1, 32)),
            call(marked_u64, ConstValue::Uint(u64::MAX as u128 + 1, 64)),
        ] {
            assert!(
                recognize_admissible_body(&bad).is_none(),
                "unmarked, malformed, excluded, or type-incoherent arithmetic must fail closed"
            );
        }

        let mut signed = call(marked_u64, ConstValue::Uint(1, 64));
        signed.body.locals[1].ty = Ty::Int { width: 64, signed: true };
        assert!(
            recognize_admissible_body(&signed).is_none(),
            "signed operand under an unsigned marker"
        );

        let mut return_mismatch = call(marked_u64, ConstValue::Uint(1, 64));
        return_mismatch.body.return_ty = Ty::u32();
        return_mismatch.body.locals[0].ty = Ty::u32();
        assert!(
            recognize_admissible_body(&return_mismatch).is_none(),
            "marker width must agree with the function return domain"
        );
    }

    #[test]
    fn composed_wrapping_chain_rejects_mixed_marker_widths() {
        let mut chain = func_blocks(
            1,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: Vec::new(),
                    terminator: Terminator::Call {
                        func: "@trust-rustc-total-primitive-method::core::num::<impl u64>::wrapping_add".into(),
                        args: vec![
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Uint(1, 64)),
                        ],
                        dest: Place::local(2),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_foreign: false,
                        is_unsafe_sig: false,
                        callee_identity: None,
                        unwind: crate::UnwindEdge::Unreachable,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: Vec::new(),
                    terminator: Terminator::Call {
                        func: "@trust-rustc-total-primitive-method::core::num::<impl u32>::wrapping_mul".into(),
                        args: vec![
                            Operand::Copy(Place::local(2)),
                            Operand::Constant(ConstValue::Uint(2, 32)),
                        ],
                        dest: Place::local(0),
                        target: Some(BlockId(2)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_foreign: false,
                        is_unsafe_sig: false,
                        callee_identity: None,
                        unwind: crate::UnwindEdge::Unreachable,
                    },
                },
                BasicBlock { id: BlockId(2), stmts: Vec::new(), terminator: Terminator::Return },
            ],
        );
        // Even if a hostile artifact rewrites the second temporary's type to
        // agree with its own marker, the cross-node width disagreement remains.
        chain.body.locals[2].ty = Ty::u32();
        assert!(
            recognize_admissible_body(&chain).is_none(),
            "S4 chains must use one exact machine domain throughout"
        );
    }

    #[test]
    fn recognizes_a_constant_return() {
        // `fn answer() -> u64 { 42 }` with bookkeeping around it.
        let f = func(
            0,
            vec![
                Statement::StorageLive(0),
                assign(Place::local(0), Rvalue::Use(Operand::Constant(ConstValue::Uint(42, 64)))),
                Statement::Nop,
            ],
            Terminator::Return,
        );
        assert_eq!(
            recognize_admissible_body(&f),
            Some(AdmissibleBody::ConstantUint { value: 42, width_bits: 64 })
        );
    }

    #[test]
    fn recognizes_a_projection() {
        // `fn fst(x, y) -> u64 { x }` — returns param 0 (local 1).
        let f = func(
            2,
            vec![assign(Place::local(0), Rvalue::Use(Operand::Copy(Place::local(1))))],
            Terminator::Return,
        );
        assert_eq!(recognize_admissible_body(&f), Some(AdmissibleBody::Projection { param: 0 }));
        // `{ y }` returns param 1 (local 2).
        let g = func(
            2,
            vec![assign(Place::local(0), Rvalue::Use(Operand::Move(Place::local(2))))],
            Terminator::Return,
        );
        assert_eq!(recognize_admissible_body(&g), Some(AdmissibleBody::Projection { param: 1 }));
    }

    #[test]
    fn fails_closed_outside_the_recognized_shapes() {
        // A non-Return terminator.
        assert_eq!(recognize_admissible_body(&func(0, Vec::new(), Terminator::Unreachable)), None);
        // Two value-carrying statements: recognized since the 2026-07-22
        // Use-chain widening (increment 2) — the FINAL dataflow wins, and
        // this body genuinely returns the constant. The chain's own forgery
        // pins live in widening_battery_chain_forgeries_never_admit.
        let two = func(
            1,
            vec![
                assign(Place::local(0), Rvalue::Use(Operand::Copy(Place::local(1)))),
                assign(Place::local(0), Rvalue::Use(Operand::Constant(ConstValue::Uint(1, 64)))),
            ],
            Terminator::Return,
        );
        assert_eq!(
            recognize_admissible_body(&two),
            Some(AdmissibleBody::ConstantUint { value: 1, width_bits: 64 })
        );
        // Assigning THROUGH a reference (a Deref projection), not the bare return.
        let deref = func(
            1,
            vec![assign(
                Place { local: 0, projections: vec![Projection::Deref] },
                Rvalue::Use(Operand::Constant(ConstValue::Uint(1, 64))),
            )],
            Terminator::Return,
        );
        assert_eq!(recognize_admissible_body(&deref), None);
        // Returning a NON-parameter local (out of `1..=arg_count`).
        let non_param = func(
            1,
            vec![assign(Place::local(0), Rvalue::Use(Operand::Copy(Place::local(7))))],
            Terminator::Return,
        );
        assert_eq!(recognize_admissible_body(&non_param), None);
        // Returning a projection of a parameter whose declared type is NOT a
        // struct: `Projection` is a whole-parameter shape, and the sibling
        // `FieldProjection` shape needs a struct to name a field of (see
        // `a_scalar_field_of_a_by_value_struct_parameter_is_recognized`).
        let field = func(
            1,
            vec![assign(
                Place::local(0),
                Rvalue::Use(Operand::Copy(Place {
                    local: 1,
                    projections: vec![Projection::Field(0)],
                })),
            )],
            Terminator::Return,
        );
        assert_eq!(recognize_admissible_body(&field), None);
        // Multiple blocks (not a straight-line return).
        assert_eq!(
            recognize_admissible_body(&VerifiableFunction {
                body: VerifiableBody {
                    blocks: vec![
                        BasicBlock {
                            id: BlockId(0),
                            stmts: Vec::new(),
                            terminator: Terminator::Goto(BlockId(1)),
                        },
                        BasicBlock {
                            id: BlockId(1),
                            stmts: Vec::new(),
                            terminator: Terminator::Return,
                        },
                    ],
                    ..func(0, Vec::new(), Terminator::Return).body
                },
                ..func(0, Vec::new(), Terminator::Return)
            }),
            None
        );
    }

    // ── structural single-step Nat recursion (R1, §6e as amended) ──────────

    /// The canonical contract body for `tozero` at the bignum carrier:
    ///
    /// ```text
    /// bb0: _2 = &_1;         is_zero(move _2) -> _3, bb1
    /// bb1: switchInt(_3)     [(0, bb3)] otherwise bb2
    /// bb2: from_u64(0) -> _0, bb6                        // zero arm
    /// bb3: from_u64(1) -> _4, bb4                        // succ arm…
    /// bb4: _5 = &_1; _6 = &_4; sub(move _5, move _6) -> _7, bb5
    /// bb5: self(move _7) -> _0, bb6
    /// bb6: return
    /// ```
    fn nat_local(index: usize) -> LocalDecl {
        LocalDecl { index, ty: Ty::BignumNat, name: None }
    }

    fn nat_ref_local(index: usize) -> LocalDecl {
        LocalDecl {
            index,
            ty: Ty::Ref { mutable: false, inner: Box::new(Ty::BignumNat) },
            name: None,
        }
    }

    fn nat_call(callee: &str, args: Vec<Operand>, dest: Place, target: BlockId) -> Terminator {
        Terminator::Call {
            func: callee.into(),
            args,
            dest,
            target: Some(target),
            span: SourceSpan::default(),
            atomic: None,
            is_foreign: false,
            is_unsafe_sig: false,
            callee_identity: None,
            unwind: crate::UnwindEdge::Unreachable,
        }
    }

    fn structural_tozero_contract() -> VerifiableFunction {
        let locals = vec![
            nat_local(0),
            nat_local(1),
            nat_ref_local(2),
            LocalDecl { index: 3, ty: Ty::Bool, name: None },
            nat_local(4),
            nat_ref_local(5),
            nat_ref_local(6),
            nat_local(7),
        ];
        let blocks = vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![assign(
                    Place::local(2),
                    Rvalue::Ref { mutable: false, place: Place::local(1) },
                )],
                terminator: nat_call(
                    "trust_bignum::Nat::is_zero",
                    vec![Operand::Move(Place::local(2))],
                    Place::local(3),
                    BlockId(1),
                ),
            },
            BasicBlock {
                id: BlockId(1),
                stmts: Vec::new(),
                terminator: Terminator::SwitchInt {
                    discr: Operand::Move(Place::local(3)),
                    targets: vec![(0, BlockId(3))],
                    otherwise: BlockId(2),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            BasicBlock {
                id: BlockId(2),
                stmts: Vec::new(),
                terminator: nat_call(
                    "trust_bignum::Nat::from_u64",
                    vec![Operand::Constant(ConstValue::Uint(0, 64))],
                    Place::local(0),
                    BlockId(6),
                ),
            },
            BasicBlock {
                id: BlockId(3),
                stmts: Vec::new(),
                terminator: nat_call(
                    "trust_bignum::Nat::from_u64",
                    vec![Operand::Constant(ConstValue::Uint(1, 64))],
                    Place::local(4),
                    BlockId(4),
                ),
            },
            BasicBlock {
                id: BlockId(4),
                stmts: vec![
                    assign(Place::local(5), Rvalue::Ref { mutable: false, place: Place::local(1) }),
                    assign(Place::local(6), Rvalue::Ref { mutable: false, place: Place::local(4) }),
                ],
                terminator: nat_call(
                    "trust_bignum::Nat::sub",
                    vec![Operand::Move(Place::local(5)), Operand::Move(Place::local(6))],
                    Place::local(7),
                    BlockId(5),
                ),
            },
            BasicBlock {
                id: BlockId(5),
                stmts: Vec::new(),
                terminator: nat_call(
                    "probe::tozero",
                    vec![Operand::Move(Place::local(7))],
                    Place::local(0),
                    BlockId(6),
                ),
            },
            BasicBlock { id: BlockId(6), stmts: Vec::new(), terminator: Terminator::Return },
        ];
        let mut f = func(1, Vec::new(), Terminator::Return);
        f.name = "tozero".into();
        f.def_path = "probe::tozero".into();
        f.body.locals = locals;
        f.body.blocks = blocks;
        f.body.return_ty = Ty::BignumNat;
        f
    }

    #[test]
    fn structural_rec_recognizes_the_contract_body() {
        let f = structural_tozero_contract();
        assert_eq!(
            recognize_structural_rec(&f),
            Some(StructuralRecBody {
                base: RecBodyExpr::NatConst(0),
                step: RecBodyExpr::Rec,
                rec_arg: RecBodyExpr::Pred,
            })
        );
        // THE SEPARATE-ENTRY-POINT DISCIPLINE: the E6 kernel-import chain must
        // NOT see this shape — `recognize_admissible_body` stays `None` on a
        // self-call body forever (probe r6's pin, unmoved), so
        // `trust_certify::clean_island::admit_function_into` fails closed on
        // recursion BY CONSTRUCTION rather than by an audit arm.
        assert_eq!(recognize_admissible_body(&f), None);
        // The Adt spelling of the carrier (what the real extractor renders)
        // recognizes identically.
        let mut g = f.clone();
        let nat_adt = || Ty::adt("trust_bignum::Nat", Vec::new());
        for decl in &mut g.body.locals {
            if decl.ty == Ty::BignumNat {
                decl.ty = nat_adt();
            } else if let Ty::Ref { mutable: false, inner } = &decl.ty {
                if **inner == Ty::BignumNat {
                    decl.ty = Ty::Ref { mutable: false, inner: Box::new(nat_adt()) };
                }
            }
        }
        g.body.return_ty = nat_adt();
        assert!(recognize_structural_rec(&g).is_some(), "Adt carrier spelling must recognize");
    }

    /// The predecessor's def path AS THE EXTRACTOR RENDERS IT (measured
    /// 2026-08-21 — `Nat::sub` is declared in `mod arith`, not in `Nat`'s own
    /// module, so rustc's inherent-impl printer qualifies it). Everything else
    /// about the body is the contract; only the callee string moves. See
    /// [`bignum_callee`]'s reviewed-exception note.
    #[test]
    fn structural_rec_recognizes_the_module_qualified_predecessor() {
        let mut f = structural_tozero_contract();
        if let Terminator::Call { func: callee, .. } = &mut f.body.blocks[4].terminator {
            *callee = "trust_bignum::arith::<impl trust_bignum::Nat>::sub".into();
        }
        assert_eq!(
            recognize_structural_rec(&f),
            Some(StructuralRecBody {
                base: RecBodyExpr::NatConst(0),
                step: RecBodyExpr::Rec,
                rec_arg: RecBodyExpr::Pred,
            }),
            "the module-qualified rendering of `Nat::sub` is the same method"
        );

        // …and the exception buys EXACTLY that method. A sibling declared in
        // the same impl block shares the entire `<impl …>` prefix, so this is
        // the mutation a prefix- or suffix-matching table would let through.
        for sibling in [
            "trust_bignum::arith::<impl trust_bignum::Nat>::mul",
            "trust_bignum::arith::<impl trust_bignum::Nat>::checked_sub",
            "trust_bignum::divmod::<impl trust_bignum::Nat>::div",
        ] {
            let mut wrong = structural_tozero_contract();
            if let Terminator::Call { func: callee, .. } = &mut wrong.body.blocks[4].terminator {
                *callee = sibling.into();
            }
            assert_eq!(recognize_structural_rec(&wrong), None, "{sibling} is not the predecessor");
        }

        // A foreign crate wearing the same shape of path is refused too.
        let mut foreign = structural_tozero_contract();
        if let Terminator::Call { func: callee, .. } = &mut foreign.body.blocks[4].terminator {
            *callee = "my_crate::arith::<impl my_crate::Nat>::sub".into();
        }
        assert_eq!(recognize_structural_rec(&foreign), None, "foreign module-qualified sub");
    }

    #[test]
    fn structural_rec_recognizes_an_add_step() {
        // step = Add(Rec, NatConst(2)): …; self(k) -> _8; from_u64(2) -> _9;
        // _10 = &_8; _11 = &_9; add(move _10, move _11) -> _0.
        let mut f = structural_tozero_contract();
        f.body.locals.extend([nat_local(8), nat_local(9), nat_ref_local(10), nat_ref_local(11)]);
        // Rewire: self-call now writes _8 and continues.
        f.body.blocks[5] = BasicBlock {
            id: BlockId(5),
            stmts: Vec::new(),
            terminator: nat_call(
                "probe::tozero",
                vec![Operand::Move(Place::local(7))],
                Place::local(8),
                BlockId(7),
            ),
        };
        // Zero arm still targets the (relocated) return block.
        let ret_id = BlockId(9);
        if let Terminator::Call { target, .. } = &mut f.body.blocks[2].terminator {
            *target = Some(ret_id);
        }
        f.body.blocks[6] = BasicBlock {
            id: BlockId(7),
            stmts: Vec::new(),
            terminator: nat_call(
                "trust_bignum::Nat::from_u64",
                vec![Operand::Constant(ConstValue::Uint(2, 64))],
                Place::local(9),
                BlockId(8),
            ),
        };
        f.body.blocks.push(BasicBlock {
            id: BlockId(8),
            stmts: vec![
                assign(Place::local(10), Rvalue::Ref { mutable: false, place: Place::local(8) }),
                assign(Place::local(11), Rvalue::Ref { mutable: false, place: Place::local(9) }),
            ],
            terminator: nat_call(
                "trust_bignum::Nat::add",
                vec![Operand::Move(Place::local(10)), Operand::Move(Place::local(11))],
                Place::local(0),
                ret_id,
            ),
        });
        f.body.blocks.push(BasicBlock {
            id: ret_id,
            stmts: Vec::new(),
            terminator: Terminator::Return,
        });
        assert_eq!(
            recognize_structural_rec(&f),
            Some(StructuralRecBody {
                base: RecBodyExpr::NatConst(0),
                step: RecBodyExpr::Add(
                    Box::new(RecBodyExpr::Rec),
                    Box::new(RecBodyExpr::NatConst(2)),
                ),
                rec_arg: RecBodyExpr::Pred,
            })
        );
    }

    /// The forgery battery: every mutation of the contract must fail closed.
    /// Each is the structural-layer half of a control whose kernel-layer half
    /// lives in `trust-clean-origin/tests/control_7_structural_rec_emitter_mutation.rs`.
    #[test]
    fn structural_rec_forgeries_never_recognize() {
        // (1) OFF-BY-ONE recursive argument: self(move _1) — the diverging
        // binary. The belt here is that the recorded dataflow value is
        // `Decreasing`, not `Pred`; the braces are the kernel identity check.
        let mut off_by_one = structural_tozero_contract();
        if let Terminator::Call { args, .. } = &mut off_by_one.body.blocks[5].terminator {
            *args = vec![Operand::Move(Place::local(1))];
        }
        assert_eq!(recognize_structural_rec(&off_by_one), None, "off-by-one rec arg");

        // (2) SWAPPED CASES: the switch polarity inverted puts the self-call
        // in the zero arm and the base value in the succ arm — both refused
        // (`Arm::Zero` admits no self-call; a succ arm with no self-call has
        // `rec_arg == None`).
        let mut swapped = structural_tozero_contract();
        if let Terminator::SwitchInt { targets, otherwise, .. } =
            &mut swapped.body.blocks[1].terminator
        {
            let old_zero = *otherwise;
            *otherwise = targets[0].1;
            targets[0].1 = old_zero;
        }
        assert_eq!(recognize_structural_rec(&swapped), None, "swapped cases");

        // (3) FOREIGN zero-test: a user function named like the runtime's.
        let mut foreign = structural_tozero_contract();
        if let Terminator::Call { func: callee, .. } = &mut foreign.body.blocks[0].terminator {
            *callee = "my_crate::Nat::is_zero".into();
        }
        assert_eq!(recognize_structural_rec(&foreign), None, "foreign is_zero");

        // (4) A call to a DIFFERENT function where the self-call belongs:
        // arbitrary semantics must never read as `Rec`.
        let mut other_callee = structural_tozero_contract();
        if let Terminator::Call { func: callee, .. } = &mut other_callee.body.blocks[5].terminator {
            *callee = "probe::other".into();
        }
        assert_eq!(recognize_structural_rec(&other_callee), None, "non-self callee");

        // (5) TWO self-calls: splice a second one between pred and the root.
        let mut two_calls = structural_tozero_contract();
        two_calls.body.locals.push(nat_local(8));
        two_calls.body.blocks[5] = BasicBlock {
            id: BlockId(5),
            stmts: Vec::new(),
            terminator: nat_call(
                "probe::tozero",
                vec![Operand::Move(Place::local(7))],
                Place::local(8),
                BlockId(7),
            ),
        };
        let ret = two_calls.body.blocks.pop().expect("ret block");
        two_calls.body.blocks.push(BasicBlock {
            id: BlockId(7),
            stmts: Vec::new(),
            terminator: nat_call(
                "probe::tozero",
                vec![Operand::Move(Place::local(8))],
                Place::local(0),
                BlockId(6),
            ),
        });
        two_calls.body.blocks.push(ret);
        assert_eq!(recognize_structural_rec(&two_calls), None, "two self-calls");

        // (6) WIDTH-SKEWED from_u64 literal: the encoded width must be 64.
        let mut skewed = structural_tozero_contract();
        if let Terminator::Call { args, .. } = &mut skewed.body.blocks[2].terminator {
            *args = vec![Operand::Constant(ConstValue::Uint(0, 32))];
        }
        assert_eq!(recognize_structural_rec(&skewed), None, "width-skewed literal");

        // (7) PREDECESSOR IN THE ZERO ARM: sub has no recursor-minor reading
        // there.
        let mut pred_in_zero = structural_tozero_contract();
        pred_in_zero.body.locals.extend([nat_ref_local(8), nat_ref_local(9), nat_local(10)]);
        pred_in_zero.body.blocks[2] = BasicBlock {
            id: BlockId(2),
            stmts: vec![
                assign(Place::local(8), Rvalue::Ref { mutable: false, place: Place::local(1) }),
                assign(Place::local(9), Rvalue::Ref { mutable: false, place: Place::local(4) }),
            ],
            terminator: nat_call(
                "trust_bignum::Nat::sub",
                vec![Operand::Move(Place::local(8)), Operand::Move(Place::local(9))],
                Place::local(0),
                BlockId(6),
            ),
        };
        assert_eq!(recognize_structural_rec(&pred_in_zero), None, "pred in zero arm");

        // (8) NON-NAT carrier anywhere in the value path.
        let mut wrong_ty = structural_tozero_contract();
        wrong_ty.body.locals[1] = LocalDecl { index: 1, ty: Ty::u64(), name: None };
        assert_eq!(recognize_structural_rec(&wrong_ty), None, "non-Nat parameter");

        // (9) ARITY 2: the contract is single-parameter.
        let mut two_params = structural_tozero_contract();
        two_params.body.arg_count = 2;
        assert_eq!(recognize_structural_rec(&two_params), None, "arity 2");

        // (10) The probes' minimal `spin(a) = spin(a)` and full gcd shapes
        // stay unrecognized here too (no zero-test, wrong carrier, Rem):
        // re-asserted in `trust-clean-origin`'s recursion_boundary_probes r6,
        // which owns those constructions.
    }

    /// E6 widening increments 5 and 6: the comparison-to-bool shape. The
    /// positive pins cover both a signed and an unsigned carrier (the
    /// recognizer is shape-only; domains gate later, in `ty_to_domain`), the
    /// `>`/`>=` operand swap, and both literal spellings (`Uint` with a width,
    /// signed `Int` without one, negative by magnitude). Every forgery
    /// direction the mint's faithfulness rests on fails closed: a non-`bool`
    /// return type, a projected operand, TWO constant operands, `!=`, a local
    /// outside `1..=arg_count`, and an effectful sibling statement.
    #[test]
    fn comparison_bool_recognizes_and_forgeries_fail_closed() {
        // fn le(a: i64, b: i64) -> bool { a <= b }
        let cmp_body = |binop: BinOp, opl: Operand, opr: Operand, param_ty: Ty, ret_ty: Ty| {
            let mut f = func(
                2,
                vec![assign(Place::local(0), Rvalue::BinaryOp(binop, opl, opr))],
                Terminator::Return,
            );
            for local in &mut f.body.locals {
                local.ty = if local.index == 0 { ret_ty.clone() } else { param_ty.clone() };
            }
            f.body.return_ty = ret_ty;
            f
        };
        let p = |i: usize| Operand::Copy(Place::local(i));

        // POSITIVE: signed i64 `<=`.
        assert_eq!(
            recognize_admissible_body(&cmp_body(BinOp::Le, p(1), p(2), Ty::i64(), Ty::Bool)),
            Some(AdmissibleBody::ComparisonBool {
                cmp: SelectCmp::Le,
                left: CmpOperand::Param(0),
                right: CmpOperand::Param(1),
            })
        );
        // POSITIVE: unsigned u64 `<`, operands reversed — indices FOLLOW the
        // operands (the reversed-operand forgery is a DIFFERENT recognition,
        // never a silent normalization).
        assert_eq!(
            recognize_admissible_body(&cmp_body(BinOp::Lt, p(2), p(1), Ty::u64(), Ty::Bool)),
            Some(AdmissibleBody::ComparisonBool {
                cmp: SelectCmp::Lt,
                left: CmpOperand::Param(1),
                right: CmpOperand::Param(0),
            })
        );
        // POSITIVE: `==`.
        assert_eq!(
            recognize_admissible_body(&cmp_body(BinOp::Eq, p(1), p(2), Ty::u64(), Ty::Bool)),
            Some(AdmissibleBody::ComparisonBool {
                cmp: SelectCmp::Eq,
                left: CmpOperand::Param(0),
                right: CmpOperand::Param(1),
            })
        );
        // POSITIVE: `>` / `>=` normalize by OPERAND SWAP onto `<` / `<=`
        // (E6 widening increment 6). `a > b` becomes `Lt(b, a)`, so the minted
        // term is the one the clause lane emits for the same source — and the
        // swap is visible in the recognition, not hidden inside the mint.
        assert_eq!(
            recognize_admissible_body(&cmp_body(BinOp::Gt, p(1), p(2), Ty::i64(), Ty::Bool)),
            Some(AdmissibleBody::ComparisonBool {
                cmp: SelectCmp::Lt,
                left: CmpOperand::Param(1),
                right: CmpOperand::Param(0),
            })
        );
        assert_eq!(
            recognize_admissible_body(&cmp_body(BinOp::Ge, p(1), p(2), Ty::i64(), Ty::Bool)),
            Some(AdmissibleBody::ComparisonBool {
                cmp: SelectCmp::Le,
                left: CmpOperand::Param(1),
                right: CmpOperand::Param(0),
            })
        );
        // POSITIVE: a LITERAL bound (E6 widening increment 6) — the shape every
        // width guard is written in. Unsigned literals arrive as `Uint`.
        assert_eq!(
            recognize_admissible_body(&cmp_body(
                BinOp::Le,
                p(1),
                Operand::Constant(ConstValue::Uint(7, 64)),
                Ty::u64(),
                Ty::Bool
            )),
            Some(AdmissibleBody::ComparisonBool {
                cmp: SelectCmp::Le,
                left: CmpOperand::Param(0),
                right: CmpOperand::Const(7),
            })
        );
        // POSITIVE: a SIGNED literal arrives as `ConstValue::Int` with NO
        // width, and a NEGATIVE one is carried by magnitude — never as a
        // wrapped bit pattern, or `-1` and `u128::MAX` would be one operand.
        assert_eq!(
            recognize_admissible_body(&cmp_body(
                BinOp::Ge,
                p(1),
                Operand::Constant(ConstValue::Int(-1)),
                Ty::i64(),
                Ty::Bool
            )),
            Some(AdmissibleBody::ComparisonBool {
                cmp: SelectCmp::Le,
                left: CmpOperand::NegConst(1),
                right: CmpOperand::Param(0),
            })
        );

        // NEG: non-bool declared return type fails closed even though the
        // rvalue shape matches.
        assert_eq!(
            recognize_admissible_body(&cmp_body(BinOp::Le, p(1), p(2), Ty::u64(), Ty::u64())),
            None
        );
        // NEG: `!=` is still not recognized. It has no `SelectCmp`, and there
        // is no swap that turns it into one.
        assert_eq!(
            recognize_admissible_body(&cmp_body(BinOp::Ne, p(1), p(2), Ty::i64(), Ty::Bool)),
            None
        );
        // NEG: a projected operand is not a bare parameter.
        assert_eq!(
            recognize_admissible_body(&cmp_body(
                BinOp::Le,
                Operand::Copy(Place { local: 1, projections: vec![Projection::Field(0)] }),
                p(2),
                Ty::i64(),
                Ty::Bool
            )),
            None
        );
        // NEG: TWO constant operands leave no parameter to fix the literals'
        // carrier width, and the decision is constant-valued. Fail closed.
        assert_eq!(
            recognize_admissible_body(&cmp_body(
                BinOp::Le,
                Operand::Constant(ConstValue::Uint(1, 64)),
                Operand::Constant(ConstValue::Uint(7, 64)),
                Ty::u64(),
                Ty::Bool
            )),
            None
        );
        // NEG: a non-parameter local operand (out of 1..=arg_count).
        assert_eq!(
            recognize_admissible_body(&cmp_body(BinOp::Le, p(1), p(5), Ty::i64(), Ty::Bool)),
            None
        );
        // NEG: an effectful sibling statement breaks the sole-assignment shape.
        let mut noisy = cmp_body(BinOp::Le, p(1), p(2), Ty::i64(), Ty::Bool);
        noisy.body.blocks[0]
            .stmts
            .insert(0, assign(Place::local(3), Rvalue::Use(Operand::Copy(Place::local(1)))));
        assert_eq!(recognize_admissible_body(&noisy), None);
    }

    /// `fn degree_of(c: Cst) -> RET { c.<field_index> }` with parameter local
    /// `1` declared at `param_ty`.
    fn field_read(
        param_ty: Ty,
        field_index: usize,
        return_ty: Ty,
        projections: Vec<Projection>,
    ) -> VerifiableFunction {
        let mut f = func(
            1,
            vec![assign(
                Place::local(0),
                Rvalue::Use(Operand::Copy(Place { local: 1, projections })),
            )],
            Terminator::Return,
        );
        let _ = field_index;
        f.body.locals[1] = LocalDecl { index: 1, ty: param_ty, name: Some("c".into()) };
        f.body.locals[0] = LocalDecl { index: 0, ty: return_ty.clone(), name: None };
        f.body.return_ty = return_ty;
        f
    }

    fn cst(fields: Vec<(String, Ty)>) -> Ty {
        Ty::adt("crate::Cst", fields)
    }

    fn scalar_cst() -> Ty {
        cst(vec![("degree".into(), Ty::u64()), ("coeff".into(), Ty::u64())])
    }

    #[test]
    fn a_scalar_field_of_a_by_value_struct_parameter_is_recognized() {
        assert_eq!(
            recognize_admissible_body(&field_read(
                scalar_cst(),
                0,
                Ty::u64(),
                vec![Projection::Field(0)]
            )),
            Some(AdmissibleBody::FieldProjection { param: 0, field: 0 })
        );
        // The SECOND field is a different shape value — the index is carried,
        // never assumed to be zero.
        assert_eq!(
            recognize_admissible_body(&field_read(
                scalar_cst(),
                1,
                Ty::u64(),
                vec![Projection::Field(1)]
            )),
            Some(AdmissibleBody::FieldProjection { param: 0, field: 1 })
        );
    }

    /// Every gate on the shape, each pinned on its own. A green line here is a
    /// definitional import that would name a value the program does not
    /// compute.
    #[test]
    fn field_projection_fails_closed_outside_its_exact_shape() {
        // A DEREF in the projection chain — how a `&Cst` parameter arrives.
        // Its pointee is not provably unchanged between entry and exit, so the
        // clause lane has no reading for it.
        assert_eq!(
            recognize_admissible_body(&field_read(
                scalar_cst(),
                0,
                Ty::u64(),
                vec![Projection::Deref, Projection::Field(0)]
            )),
            None
        );
        // A field of a field — the aggregate carrier this increment does not
        // build.
        assert_eq!(
            recognize_admissible_body(&field_read(
                scalar_cst(),
                0,
                Ty::u64(),
                vec![Projection::Field(0), Projection::Field(0)]
            )),
            None
        );
        // An out-of-range field index.
        assert_eq!(
            recognize_admissible_body(&field_read(
                scalar_cst(),
                9,
                Ty::u64(),
                vec![Projection::Field(9)]
            )),
            None
        );
        // The field's declared type is NOT the return type: a same-shaped body
        // at another width must not be admitted at this one.
        assert_eq!(
            recognize_admissible_body(&field_read(
                cst(vec![("degree".into(), Ty::u32())]),
                0,
                Ty::u64(),
                vec![Projection::Field(0)]
            )),
            None
        );
        // An ENUM: `fields` is the union view, so field 0 is variant-relative
        // and is reached through a `Downcast`, not a bare `Field`.
        let enum_ty = Ty::adt_enum(
            "crate::E",
            vec![crate::VariantDef {
                name: "A".into(),
                discriminant: 0,
                fields: vec![("degree".into(), Ty::u64())],
            }],
        );
        assert_eq!(
            recognize_admissible_body(&field_read(
                enum_ty,
                0,
                Ty::u64(),
                vec![Projection::Field(0)]
            )),
            None
        );
        // A NON-parameter local of struct type is not an input the clause can
        // bind, so its field is not a projection of anything nameable.
        let mut non_param =
            field_read(scalar_cst(), 0, Ty::u64(), vec![Projection::Field(0)]);
        non_param.body.locals[5] = LocalDecl { index: 5, ty: scalar_cst(), name: Some("t".into()) };
        non_param.body.blocks[0].stmts = vec![assign(
            Place::local(0),
            Rvalue::Use(Operand::Copy(Place { local: 5, projections: vec![Projection::Field(0)] })),
        )];
        assert_eq!(recognize_admissible_body(&non_param), None);
    }

    /// Build the FULLY-OPTIMIZED-MIR short-circuit diamond for a bool-binary
    /// body over one parameter — the shape `TrustVerify` sees post-optimization
    /// (`MatchBranchSimplification` leaves a `false`/comparison pair alone;
    /// `MultipleReturnTerminators`, which would collapse the join, is
    /// mir-opt-level ≥ 4 only, above the citation lane's `-O`).
    /// `switchInt(_2) -> [0: bb2, otherwise: bb1]`, bb1 = otherwise arm, bb2 =
    /// `0` arm, both writing `arm_place` and joining at bb3 (`return`); when
    /// `arm_place != 0` the join copies it to `_0`.
    fn bool_diamond(
        entry_cmp: (crate::BinOp, Operand, Operand),
        zero_arm: Rvalue,
        other_arm: Rvalue,
        ret_ty: Ty,
        arm_place: usize,
    ) -> VerifiableFunction {
        let (binop, opl, opr) = entry_cmp;
        let join_stmts = if arm_place == 0 {
            vec![]
        } else {
            vec![assign(Place::local(0), Rvalue::Use(Operand::Copy(Place::local(arm_place))))]
        };
        let mut f = func_blocks(
            1,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![assign(Place::local(2), Rvalue::BinaryOp(binop, opl, opr))],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(2)),
                        targets: vec![(0, BlockId(2))],
                        otherwise: BlockId(1),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1), // otherwise arm
                    stmts: vec![assign(Place::local(arm_place), other_arm)],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(2), // `0` arm
                    stmts: vec![assign(Place::local(arm_place), zero_arm)],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock { id: BlockId(3), stmts: join_stmts, terminator: Terminator::Return },
            ],
        );
        f.body.return_ty = ret_ty;
        f
    }

    /// E6 widening increment 7: the bool-binary (`&&` / `||`) shape. Positive
    /// pins cover the range-guard `&&`, the range-exclusion `||`, the task's
    /// i64-bounds example on an `i128` parameter (negative literal by
    /// magnitude), and the temp-copy join spelling. Every forgery the mint's
    /// faithfulness rests on fails closed: non-`bool` return, both-const /
    /// both-comparison arms, the wrong short-circuit constant (implication and
    /// `!A && B` shapes), a projected operand, a two-constant leaf, `!=`, a
    /// non-param local, mismatched arm places/joins, a discriminant that is not
    /// the entry comparison, an effectful sibling, and a non-4-block body.
    #[test]
    fn bool_binary_recognizes_and_forgeries_fail_closed() {
        use crate::BinOp;
        let c = |v: u128| Operand::Constant(ConstValue::Uint(v, 64));
        let x = || Operand::Copy(Place::local(1));
        let btrue = || Rvalue::Use(Operand::Constant(ConstValue::Bool(true)));
        let bfalse = || Rvalue::Use(Operand::Constant(ConstValue::Bool(false)));

        // POSITIVE `&&`: `x >= 5 && x <= 10`. The discriminant leaf `A` is the
        // LHS (`x >= 5`, normalized by swap to `5 <= x`); `B` is the otherwise
        // arm; the `0` arm short-circuits to `false`.
        let and = bool_diamond(
            (BinOp::Ge, x(), c(5)),
            bfalse(),
            Rvalue::BinaryOp(BinOp::Le, x(), c(10)),
            Ty::Bool,
            0,
        );
        assert_eq!(
            recognize_admissible_body(&and),
            Some(AdmissibleBody::BoolBinary {
                op: BoolBinOp::And,
                left: ComparisonLeaf {
                    cmp: SelectCmp::Le,
                    left: CmpOperand::Const(5),
                    right: CmpOperand::Param(0),
                },
                right: ComparisonLeaf {
                    cmp: SelectCmp::Le,
                    left: CmpOperand::Param(0),
                    right: CmpOperand::Const(10),
                },
            })
        );

        // POSITIVE `||`: `x < 5 || x > 10`. For `||` the constant `true` sits on
        // the `otherwise` arm and `B` (`x > 10`, normalized to `10 < x`) on the
        // `0` arm; the discriminant leaf `A` is still the LHS.
        let or = bool_diamond(
            (BinOp::Lt, x(), c(5)),
            Rvalue::BinaryOp(BinOp::Gt, x(), c(10)),
            btrue(),
            Ty::Bool,
            0,
        );
        assert_eq!(
            recognize_admissible_body(&or),
            Some(AdmissibleBody::BoolBinary {
                op: BoolBinOp::Or,
                left: ComparisonLeaf {
                    cmp: SelectCmp::Lt,
                    left: CmpOperand::Param(0),
                    right: CmpOperand::Const(5),
                },
                right: ComparisonLeaf {
                    cmp: SelectCmp::Lt,
                    left: CmpOperand::Const(10),
                    right: CmpOperand::Param(0),
                },
            })
        );

        // POSITIVE: the task's example `fn f(x: i128) -> bool { x >= i64::MIN &&
        // x <= i64::MAX }`. A signed literal arrives as `ConstValue::Int` with
        // no width; the negative bound is carried by magnitude.
        let i64_min = -9_223_372_036_854_775_808_i128;
        let i64_max = 9_223_372_036_854_775_807_i128;
        let bounds = bool_diamond(
            (BinOp::Ge, x(), Operand::Constant(ConstValue::Int(i64_min))),
            bfalse(),
            Rvalue::BinaryOp(BinOp::Le, x(), Operand::Constant(ConstValue::Int(i64_max))),
            Ty::Bool,
            0,
        );
        assert_eq!(
            recognize_admissible_body(&bounds),
            Some(AdmissibleBody::BoolBinary {
                op: BoolBinOp::And,
                left: ComparisonLeaf {
                    cmp: SelectCmp::Le,
                    left: CmpOperand::NegConst(9_223_372_036_854_775_808),
                    right: CmpOperand::Param(0),
                },
                right: ComparisonLeaf {
                    cmp: SelectCmp::Le,
                    left: CmpOperand::Param(0),
                    right: CmpOperand::Const(9_223_372_036_854_775_807),
                },
            })
        );

        // POSITIVE: the temp-copy join spelling recognizes to the same body.
        let via_temp = bool_diamond(
            (BinOp::Ge, x(), c(5)),
            bfalse(),
            Rvalue::BinaryOp(BinOp::Le, x(), c(10)),
            Ty::Bool,
            3,
        );
        assert_eq!(recognize_admissible_body(&via_temp), recognize_admissible_body(&and));

        // NEG: a non-`bool` declared return type fails closed even with the
        // right diamond shape.
        assert_eq!(
            recognize_admissible_body(&bool_diamond(
                (BinOp::Ge, x(), c(5)),
                bfalse(),
                Rvalue::BinaryOp(BinOp::Le, x(), c(10)),
                Ty::u64(),
                0,
            )),
            None
        );

        // NEG: BOTH arms constant — a plain conditional constant, not a
        // conjunction/disjunction of two comparisons.
        assert_eq!(
            recognize_admissible_body(&bool_diamond(
                (BinOp::Ge, x(), c(5)),
                bfalse(),
                btrue(),
                Ty::Bool,
                0,
            )),
            None
        );

        // NEG: BOTH arms comparisons — no short-circuit constant, so it is not a
        // recognized `&&`/`||` diamond.
        assert_eq!(
            recognize_admissible_body(&bool_diamond(
                (BinOp::Ge, x(), c(5)),
                Rvalue::BinaryOp(BinOp::Le, x(), c(10)),
                Rvalue::BinaryOp(BinOp::Le, x(), c(10)),
                Ty::Bool,
                0,
            )),
            None
        );

        // NEG: the WRONG short-circuit constant. `0`-arm `true` + otherwise-arm
        // comparison is `if A then B else true` = `A → B` (implication), never
        // `A && B`; fail closed.
        assert_eq!(
            recognize_admissible_body(&bool_diamond(
                (BinOp::Ge, x(), c(5)),
                btrue(),
                Rvalue::BinaryOp(BinOp::Le, x(), c(10)),
                Ty::Bool,
                0,
            )),
            None
        );
        // NEG: comparison on the `0` arm + otherwise-arm `false` is `!A && B`;
        // fail closed (neither And nor Or).
        assert_eq!(
            recognize_admissible_body(&bool_diamond(
                (BinOp::Ge, x(), c(5)),
                Rvalue::BinaryOp(BinOp::Le, x(), c(10)),
                bfalse(),
                Ty::Bool,
                0,
            )),
            None
        );

        // NEG: a projected operand in a leaf is not a bare parameter/literal.
        assert_eq!(
            recognize_admissible_body(&bool_diamond(
                (
                    BinOp::Ge,
                    Operand::Copy(Place { local: 1, projections: vec![Projection::Field(0)] }),
                    c(5),
                ),
                bfalse(),
                Rvalue::BinaryOp(BinOp::Le, x(), c(10)),
                Ty::Bool,
                0,
            )),
            None
        );

        // NEG: a two-constant leaf leaves no parameter fixing the carrier.
        assert_eq!(
            recognize_admissible_body(&bool_diamond(
                (BinOp::Ge, c(1), c(5)),
                bfalse(),
                Rvalue::BinaryOp(BinOp::Le, x(), c(10)),
                Ty::Bool,
                0,
            )),
            None
        );

        // NEG: `!=` has no `SelectCmp` — a leaf using it fails closed.
        assert_eq!(
            recognize_admissible_body(&bool_diamond(
                (BinOp::Ne, x(), c(5)),
                bfalse(),
                Rvalue::BinaryOp(BinOp::Le, x(), c(10)),
                Ty::Bool,
                0,
            )),
            None
        );

        // NEG: a non-parameter local operand (out of 1..=arg_count).
        assert_eq!(
            recognize_admissible_body(&bool_diamond(
                (BinOp::Ge, Operand::Copy(Place::local(5)), c(5)),
                bfalse(),
                Rvalue::BinaryOp(BinOp::Le, x(), c(10)),
                Ty::Bool,
                0,
            )),
            None
        );

        // NEG: the switch discriminant is not the entry comparison's place.
        let mut wrong_discr = and.clone();
        if let Terminator::SwitchInt { discr, .. } = &mut wrong_discr.body.blocks[0].terminator {
            *discr = Operand::Copy(Place::local(4));
        }
        assert_eq!(recognize_admissible_body(&wrong_discr), None);

        // NEG: the two arms write DIFFERENT places (not a clean diamond).
        let mut split_place = and.clone();
        split_place.body.blocks[1].stmts =
            vec![assign(Place::local(3), Rvalue::BinaryOp(BinOp::Le, x(), c(10)))];
        assert_eq!(recognize_admissible_body(&split_place), None);

        // NEG: the two arms jump to DIFFERENT joins.
        let mut split_join = and.clone();
        split_join.body.blocks[1].terminator = Terminator::Goto(BlockId(2));
        assert_eq!(recognize_admissible_body(&split_join), None);

        // NEG: an effectful sibling in the entry breaks the sole-comparison shape.
        let mut noisy = and.clone();
        noisy.body.blocks[0]
            .stmts
            .insert(0, assign(Place::local(4), Rvalue::Use(Operand::Copy(Place::local(1)))));
        assert_eq!(recognize_admissible_body(&noisy), None);

        // NEG: an effectful join statement in the direct-to-`_0` form could
        // overwrite the selected value.
        let mut noisy_join = and.clone();
        noisy_join.body.blocks[3].stmts.push(assign(Place::local(0), btrue()));
        assert_eq!(recognize_admissible_body(&noisy_join), None);

        // NEG: not a four-block body (a two-block truncation of the diamond).
        let mut three = and.clone();
        three.body.blocks.truncate(3);
        assert_eq!(recognize_admissible_body(&three), None);

        // NEG: `switchInt` value other than `0` on its single target.
        let mut bad_switch = and.clone();
        if let Terminator::SwitchInt { targets, .. } = &mut bad_switch.body.blocks[0].terminator {
            *targets = vec![(1, BlockId(2))];
        }
        assert_eq!(recognize_admissible_body(&bad_switch), None);
    }

    /// The pinned std `Option<iN>` return type exactly as the layout-aware
    /// extractor lowers it (Direct tag encoding ⇒ `disc_index_safe`).
    fn option_of_signed(width: u32) -> Ty {
        Ty::adt_enum_with_disc_safety(
            "core::option::Option",
            vec![
                crate::VariantDef { name: "None".into(), discriminant: 0, fields: vec![] },
                crate::VariantDef {
                    name: "Some".into(),
                    discriminant: 1,
                    fields: vec![("0".into(), Ty::Int { width, signed: true })],
                },
            ],
            true,
        )
    }

    fn option_agg(width: u32, variant: usize) -> crate::AggregateKind {
        crate::AggregateKind::Adt {
            name: "core::option::Option".into(),
            variant,
            active_field: None,
            args: Some(format!("core::option::Option<i{width}>")),
        }
    }

    /// The measured Shape-B body of `fn c(a: iN, b: iN) -> Option<iN>
    /// { a.checked_op(b) }` at `-O`: locals `_1`/`_2` params, `_3` result,
    /// `_4` flag, `_5` tuple, `_6` unit (cold dest); blocks
    /// entry/join/cold/none/some exactly as extraction numbered them.
    fn checked_diamond(op: BinOp, width: u32, with_cold: bool) -> VerifiableFunction {
        let int = Ty::Int { width, signed: true };
        let locals = vec![
            LocalDecl { index: 0, ty: option_of_signed(width), name: None },
            LocalDecl { index: 1, ty: int.clone(), name: Some("a".into()) },
            LocalDecl { index: 2, ty: int.clone(), name: Some("b".into()) },
            LocalDecl { index: 3, ty: int.clone(), name: None },
            LocalDecl { index: 4, ty: Ty::Bool, name: None },
            LocalDecl { index: 5, ty: Ty::Tuple(vec![int.clone(), Ty::Bool]), name: None },
            LocalDecl { index: 6, ty: Ty::Unit, name: None },
        ];
        let entry = BasicBlock {
            id: BlockId(0),
            stmts: vec![
                Statement::StorageLive(5),
                assign(
                    Place::local(5),
                    Rvalue::CheckedBinaryOp(
                        op,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                ),
                Statement::StorageLive(3),
                assign(Place::local(3), Rvalue::Use(Operand::Copy(Place::field(5, 0)))),
                Statement::StorageLive(4),
                assign(Place::local(4), Rvalue::Use(Operand::Copy(Place::field(5, 1)))),
                Statement::StorageDead(5),
            ],
            terminator: Terminator::SwitchInt {
                discr: Operand::Copy(Place::local(4)),
                targets: vec![(0, BlockId(4))],
                otherwise: BlockId(if with_cold { 2 } else { 3 }),
                exhaustive_enum_unreachable: false,
                span: SourceSpan::default(),
            },
        };
        let join = BasicBlock {
            id: BlockId(1),
            stmts: vec![Statement::StorageDead(4), Statement::StorageDead(3)],
            terminator: Terminator::Return,
        };
        let cold = BasicBlock {
            id: BlockId(2),
            stmts: vec![],
            terminator: Terminator::Call {
                func: "core::intrinsics::cold_path".into(),
                callee_identity: None,
                args: vec![],
                dest: Place::local(6),
                target: Some(BlockId(3)),
                span: SourceSpan::default(),
                atomic: None,
                is_foreign: false,
                is_unsafe_sig: false,
                unwind: crate::UnwindEdge::Unreachable,
            },
        };
        let none_arm = BasicBlock {
            id: BlockId(3),
            stmts: vec![assign(Place::local(0), Rvalue::Aggregate(option_agg(width, 0), vec![]))],
            terminator: Terminator::Goto(BlockId(1)),
        };
        let some_arm = BasicBlock {
            id: BlockId(4),
            stmts: vec![assign(
                Place::local(0),
                Rvalue::Aggregate(option_agg(width, 1), vec![Operand::Copy(Place::local(3))]),
            )],
            terminator: Terminator::Goto(BlockId(1)),
        };
        let blocks = if with_cold {
            vec![entry, join, cold, none_arm, some_arm]
        } else {
            // Renumber: entry, join, none(2), some(3) — keep ids canonical.
            let mut none_arm = none_arm;
            let mut some_arm = some_arm;
            none_arm.id = BlockId(2);
            some_arm.id = BlockId(3);
            let mut entry = entry;
            if let Terminator::SwitchInt { targets, otherwise, .. } = &mut entry.terminator {
                *targets = vec![(0, BlockId(3))];
                *otherwise = BlockId(2);
            }
            vec![entry, join, none_arm, some_arm]
        };
        let mut f = func(2, Vec::new(), Terminator::Return);
        f.body.locals = if with_cold { locals } else { locals[..6].to_vec() };
        f.body.blocks = blocks;
        f.body.return_ty = option_of_signed(width);
        f
    }

    /// Shape-A fixture: the un-inlined marked call.
    fn checked_call(method: &str, width: u32) -> VerifiableFunction {
        let int = Ty::Int { width, signed: true };
        let mut f = two_block_call(
            &format!(
                "@trust-rustc-checked-primitive-method::core::num::<impl i{width}>::{method}"
            ),
            vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
            Place::local(0),
        );
        f.body.locals = vec![
            LocalDecl { index: 0, ty: option_of_signed(width), name: None },
            LocalDecl { index: 1, ty: int.clone(), name: Some("a".into()) },
            LocalDecl { index: 2, ty: int, name: Some("b".into()) },
        ];
        f.body.return_ty = option_of_signed(width);
        f
    }

    /// POSITIVE matrix: 3 ops × the measured Shape B (with AND without the
    /// cold-hint block) × all five signed widths, plus Shape A.
    #[test]
    fn checked_arithmetic_positive_matrix() {
        for (binop, op) in [
            (BinOp::Add, CheckedArithOp::Add),
            (BinOp::Sub, CheckedArithOp::Sub),
            (BinOp::Mul, CheckedArithOp::Mul),
        ] {
            for width in [8u32, 16, 32, 64, 128] {
                for with_cold in [true, false] {
                    let f = checked_diamond(binop, width, with_cold);
                    assert_eq!(
                        recognize_admissible_body(&f),
                        Some(AdmissibleBody::CheckedArithmetic {
                            op,
                            width_bits: width,
                            left: ArithOperand::Param(0),
                            right: ArithOperand::Param(1),
                        }),
                        "shape B {binop:?} i{width} cold={with_cold}"
                    );
                }
            }
        }
        for (method, op) in [
            ("checked_add", CheckedArithOp::Add),
            ("checked_sub", CheckedArithOp::Sub),
            ("checked_mul", CheckedArithOp::Mul),
        ] {
            for width in [8u32, 64, 128] {
                let f = checked_call(method, width);
                assert_eq!(
                    recognize_admissible_body(&f),
                    Some(AdmissibleBody::CheckedArithmetic {
                        op,
                        width_bits: width,
                        left: ArithOperand::Param(0),
                        right: ArithOperand::Param(1),
                    }),
                    "shape A {method} i{width}"
                );
            }
        }
        // The marked cold_path spelling is accepted alongside the bare one.
        let mut marked = checked_diamond(BinOp::Add, 64, true);
        if let Terminator::Call { func: callee, .. } = &mut marked.body.blocks[2].terminator {
            *callee = "@trust-rustc-intrinsic::core::intrinsics::cold_path".into();
        }
        assert!(recognize_admissible_body(&marked).is_some(), "marked cold_path spelling");
    }

    /// The FULL fail-closed negative battery (spec §2). Every mutation of the
    /// positive fixture must refuse — parking, never guessing.
    #[test]
    fn checked_arithmetic_fail_closed_battery() {
        let base = || checked_diamond(BinOp::Add, 64, true);
        assert!(recognize_admissible_body(&base()).is_some(), "sanity: base recognizes");

        // (1) ANY Assert terminator = unchecked arithmetic. Even an Assert in
        // an arm the diamond does not use refuses the whole body.
        let mut asserted = base();
        asserted.body.blocks[2].terminator = Terminator::Assert {
            cond: Operand::Copy(Place::local(4)),
            expected: false,
            msg: crate::AssertMessage::Overflow(BinOp::Add),
            target: BlockId(3),
            span: SourceSpan::default(),
            unwind: crate::UnwindEdge::Unreachable,
        };
        assert_eq!(recognize_admissible_body(&asserted), None, "Assert present");

        // (2) The UNCHECKED `-O` lowering of `a + b` (plain BinaryOp into a
        // scalar return) is a different shape entirely — and even a
        // checked-looking body whose return is the SCALAR iN (not Option)
        // refuses.
        let mut scalar_ret = base();
        scalar_ret.body.return_ty = Ty::Int { width: 64, signed: true };
        scalar_ret.body.locals[0].ty = Ty::Int { width: 64, signed: true };
        assert_eq!(recognize_admissible_body(&scalar_ret), None, "non-Option return");

        // (3) NICHE / indirect discriminant encoding: disc_index_safe = false
        // (an `Option<NonZero>`-style layout) refuses even with identical
        // structure.
        let mut niche = base();
        let Ty::Adt { disc_index_safe, .. } = &mut niche.body.return_ty else { unreachable!() };
        *disc_index_safe = false;
        niche.body.locals[0].ty = niche.body.return_ty.clone();
        assert_eq!(recognize_admissible_body(&niche), None, "niche layout");

        // (4) UNSIGNED payload: Option<u64> is outside this increment.
        let mut unsigned = base();
        let make_unsigned = |ty: &mut Ty| {
            let Ty::Adt { variants, .. } = ty else { unreachable!() };
            variants[1].fields[0].1 = Ty::Int { width: 64, signed: false };
        };
        make_unsigned(&mut unsigned.body.return_ty);
        unsigned.body.locals[0].ty = unsigned.body.return_ty.clone();
        assert_eq!(recognize_admissible_body(&unsigned), None, "unsigned payload");

        // (5) NON-Option ADT with the same two-variant structure but a
        // different def-path name.
        let mut lookalike = base();
        let rename = |ty: &mut Ty| {
            let Ty::Adt { name, .. } = ty else { unreachable!() };
            *name = "my_crate::MyOption".into();
        };
        rename(&mut lookalike.body.return_ty);
        lookalike.body.locals[0].ty = lookalike.body.return_ty.clone();
        assert_eq!(recognize_admissible_body(&lookalike), None, "Option-lookalike ADT");

        // (6) SWAPPED variant indices in the arms: `Some` built on the
        // overflow edge / `None` on the fit edge must never admit (this is the
        // false-`Some` forgery).
        let mut swapped = base();
        swapped.body.blocks[3].stmts =
            vec![assign(
                Place::local(0),
                Rvalue::Aggregate(option_agg(64, 1), vec![Operand::Copy(Place::local(3))]),
            )];
        swapped.body.blocks[4].stmts =
            vec![assign(Place::local(0), Rvalue::Aggregate(option_agg(64, 0), vec![]))];
        assert_eq!(recognize_admissible_body(&swapped), None, "swapped Some/None arms");

        // (7) ALIASED payload: the `Some` operand is not the CheckedBinaryOp
        // result field but a raw parameter.
        let mut aliased = base();
        aliased.body.blocks[4].stmts = vec![assign(
            Place::local(0),
            Rvalue::Aggregate(option_agg(64, 1), vec![Operand::Copy(Place::local(1))]),
        )];
        assert_eq!(recognize_admissible_body(&aliased), None, "aliased Some payload");

        // (8) Ops outside Add/Sub/Mul: a Div-spelled CheckedBinaryOp (or any
        // other op) refuses.
        for bad in [BinOp::Div, BinOp::Shl, BinOp::Shr, BinOp::BitAnd] {
            let f = checked_diamond(bad, 64, true);
            assert_eq!(recognize_admissible_body(&f), None, "op {bad:?}");
        }

        // (9) A NON-cold_path call in the hint position: arbitrary user
        // semantics must never ride the overflow edge.
        let mut user_call = base();
        if let Terminator::Call { func: callee, .. } = &mut user_call.body.blocks[2].terminator {
            *callee = "my_crate::spooky".into();
        }
        assert_eq!(recognize_admissible_body(&user_call), None, "non-cold_path hint callee");

        // (10) A cold_path whose Unit destination IS read somewhere.
        let mut read_dest = base();
        read_dest.body.blocks[3]
            .stmts
            .insert(0, assign(Place::local(6), Rvalue::Use(Operand::Copy(Place::local(6)))));
        assert_eq!(recognize_admissible_body(&read_dest), None, "cold dest read");

        // (11) A cold_path with an argument, or writing the return place.
        let mut cold_arg = base();
        if let Terminator::Call { args, .. } = &mut cold_arg.body.blocks[2].terminator {
            args.push(Operand::Copy(Place::local(1)));
        }
        assert_eq!(recognize_admissible_body(&cold_arg), None, "cold_path with an arg");
        let mut cold_dest0 = base();
        if let Terminator::Call { dest, .. } = &mut cold_dest0.body.blocks[2].terminator {
            *dest = Place::local(0);
        }
        assert_eq!(recognize_admissible_body(&cold_dest0), None, "cold_path into _0");

        // (12) Split joins: the two arms must meet at one return block.
        let mut split = base();
        split.body.blocks.push(BasicBlock {
            id: BlockId(5),
            stmts: vec![],
            terminator: Terminator::Return,
        });
        split.body.blocks[4].terminator = Terminator::Goto(BlockId(5));
        assert_eq!(recognize_admissible_body(&split), None, "split join");

        // (13) Wrong tuple field indices (flag where the result should be).
        let mut flipped_fields = base();
        flipped_fields.body.blocks[0].stmts[3] =
            assign(Place::local(3), Rvalue::Use(Operand::Copy(Place::field(5, 1))));
        flipped_fields.body.blocks[0].stmts[5] =
            assign(Place::local(4), Rvalue::Use(Operand::Copy(Place::field(5, 0))));
        assert_eq!(recognize_admissible_body(&flipped_fields), None, "flipped tuple fields");

        // (14) The switch keyed on the RESULT local instead of the flag.
        let mut wrong_discr = base();
        if let Terminator::SwitchInt { discr, .. } = &mut wrong_discr.body.blocks[0].terminator {
            *discr = Operand::Copy(Place::local(3));
        }
        assert_eq!(recognize_admissible_body(&wrong_discr), None, "switch on the result");

        // (15) The `0` edge routed to the None arm (inverted branch sense).
        let mut inverted = base();
        if let Terminator::SwitchInt { targets, otherwise, .. } =
            &mut inverted.body.blocks[0].terminator
        {
            *targets = vec![(0, BlockId(2))];
            *otherwise = BlockId(4);
        }
        assert_eq!(recognize_admissible_body(&inverted), None, "inverted branch sense");

        // (16) A missing/foreign args rendering on the aggregate.
        let mut no_args = base();
        let Statement::Assign { rvalue: Rvalue::Aggregate(kind, _), .. } =
            &mut no_args.body.blocks[4].stmts[0]
        else {
            unreachable!()
        };
        let crate::AggregateKind::Adt { args, .. } = kind else { unreachable!() };
        *args = None;
        assert_eq!(recognize_admissible_body(&no_args), None, "aggregate args missing");

        // (17) Shape A with an UNMARKED (source-spellable) callee.
        let mut unmarked = checked_call("checked_add", 64);
        if let Terminator::Call { func: callee, .. } = &mut unmarked.body.blocks[0].terminator {
            *callee = "core::num::<impl i64>::checked_add".into();
        }
        assert_eq!(recognize_admissible_body(&unmarked), None, "unmarked Shape-A callee");

        // (18) Shape A at a width disagreeing with the return type.
        let mut wrong_width = checked_call("checked_add", 64);
        if let Terminator::Call { func: callee, .. } = &mut wrong_width.body.blocks[0].terminator {
            *callee =
                "@trust-rustc-checked-primitive-method::core::num::<impl i32>::checked_add".into();
        }
        assert_eq!(recognize_admissible_body(&wrong_width), None, "width mismatch");

        // (19) An extra unrecognized block (a 5-block body whose fifth block
        // is not the cold hint was covered by (12); a 6-block body parks).
        let mut extra = base();
        extra.body.blocks.push(BasicBlock {
            id: BlockId(5),
            stmts: vec![],
            terminator: Terminator::Unreachable,
        });
        assert_eq!(recognize_admissible_body(&extra), None, "extra block");

        // (20) A projected Some-payload operand (a field of a parameter).
        let mut projected = base();
        projected.body.blocks[4].stmts = vec![assign(
            Place::local(0),
            Rvalue::Aggregate(option_agg(64, 1), vec![Operand::Copy(Place::field(3, 0))]),
        )];
        assert_eq!(recognize_admissible_body(&projected), None, "projected payload");
    }

    fn i128_ty() -> Ty {
        Ty::Int { width: 128, signed: true }
    }

    fn i64_ty() -> Ty {
        Ty::Int { width: 64, signed: true }
    }

    /// Probe c2, statement for statement: locals `_0` = `Option<i64>`, `_1` =
    /// the `i128` parameter, `_2`/`_3` the two guard flags, `_4` the cast temp.
    const I64_MIN_AT_128: i128 = -9_223_372_036_854_775_808;
    const I64_MAX_AT_128: i128 = 9_223_372_036_854_775_807;

    fn narrow_diamond() -> VerifiableFunction {
        let locals = vec![
            LocalDecl { index: 0, ty: option_of_signed(64), name: None },
            LocalDecl { index: 1, ty: i128_ty(), name: Some("x".into()) },
            LocalDecl { index: 2, ty: Ty::Bool, name: None },
            LocalDecl { index: 3, ty: Ty::Bool, name: None },
            LocalDecl { index: 4, ty: i64_ty(), name: None },
        ];
        let blocks = vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::StorageLive(2),
                    assign(
                        Place::local(2),
                        Rvalue::BinaryOp(
                            BinOp::Ge,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Int(I64_MIN_AT_128)),
                        ),
                    ),
                ],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Move(Place::local(2)),
                    targets: vec![(0, BlockId(3))],
                    otherwise: BlockId(1),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![
                    Statement::StorageLive(3),
                    assign(
                        Place::local(3),
                        Rvalue::BinaryOp(
                            BinOp::Le,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Int(I64_MAX_AT_128)),
                        ),
                    ),
                ],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Move(Place::local(3)),
                    targets: vec![(0, BlockId(3))],
                    otherwise: BlockId(2),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            BasicBlock {
                id: BlockId(2),
                stmts: vec![
                    Statement::StorageLive(4),
                    assign(
                        Place::local(4),
                        Rvalue::Cast(Operand::Copy(Place::local(1)), i64_ty()),
                    ),
                    assign(
                        Place::local(0),
                        Rvalue::Aggregate(
                            option_agg(64, 1),
                            vec![Operand::Move(Place::local(4))],
                        ),
                    ),
                    Statement::StorageDead(4),
                ],
                terminator: Terminator::Goto(BlockId(4)),
            },
            BasicBlock {
                id: BlockId(3),
                stmts: vec![assign(
                    Place::local(0),
                    Rvalue::Aggregate(option_agg(64, 0), vec![]),
                )],
                terminator: Terminator::Goto(BlockId(4)),
            },
            BasicBlock {
                id: BlockId(4),
                stmts: vec![Statement::StorageDead(3), Statement::StorageDead(2)],
                terminator: Terminator::Return,
            },
        ];
        let mut f = func(1, Vec::new(), Terminator::Return);
        f.body.locals = locals;
        f.body.blocks = blocks;
        f.body.arg_count = 1;
        f.body.return_ty = option_of_signed(64);
        f
    }

    /// Probe c10, statement for statement: the SAME diamond reached through an
    /// inlined `fits_i64` call — block order permuted (`bb4` is the second
    /// comparison, `bb1`/`bb2` the arms) and `bb5` a value-neutral `goto`
    /// trampoline on the first comparison's false edge.
    fn narrow_diamond_trampoline() -> VerifiableFunction {
        let locals = vec![
            LocalDecl { index: 0, ty: option_of_signed(64), name: None },
            LocalDecl { index: 1, ty: i128_ty(), name: Some("x".into()) },
            LocalDecl { index: 2, ty: Ty::Bool, name: None },
            LocalDecl { index: 3, ty: i64_ty(), name: None },
            LocalDecl { index: 4, ty: Ty::Bool, name: None },
        ];
        let blocks = vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::StorageLive(2),
                    Statement::StorageLive(4),
                    assign(
                        Place::local(4),
                        Rvalue::BinaryOp(
                            BinOp::Ge,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Int(I64_MIN_AT_128)),
                        ),
                    ),
                ],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Move(Place::local(4)),
                    targets: vec![(0, BlockId(5))],
                    otherwise: BlockId(4),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![
                    Statement::StorageLive(3),
                    assign(
                        Place::local(3),
                        Rvalue::Cast(Operand::Copy(Place::local(1)), i64_ty()),
                    ),
                    assign(
                        Place::local(0),
                        Rvalue::Aggregate(
                            option_agg(64, 1),
                            vec![Operand::Move(Place::local(3))],
                        ),
                    ),
                    Statement::StorageDead(3),
                ],
                terminator: Terminator::Goto(BlockId(3)),
            },
            BasicBlock {
                id: BlockId(2),
                stmts: vec![assign(
                    Place::local(0),
                    Rvalue::Aggregate(option_agg(64, 0), vec![]),
                )],
                terminator: Terminator::Goto(BlockId(3)),
            },
            BasicBlock {
                id: BlockId(3),
                stmts: vec![Statement::StorageDead(2)],
                terminator: Terminator::Return,
            },
            BasicBlock {
                id: BlockId(4),
                stmts: vec![
                    assign(
                        Place::local(2),
                        Rvalue::BinaryOp(
                            BinOp::Le,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Int(I64_MAX_AT_128)),
                        ),
                    ),
                    Statement::StorageDead(4),
                ],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Move(Place::local(2)),
                    targets: vec![(0, BlockId(2))],
                    otherwise: BlockId(1),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            BasicBlock {
                id: BlockId(5),
                stmts: vec![Statement::StorageDead(4)],
                terminator: Terminator::Goto(BlockId(2)),
            },
        ];
        let mut f = func(1, Vec::new(), Terminator::Return);
        f.body.locals = locals;
        f.body.blocks = blocks;
        f.body.arg_count = 1;
        f.body.return_ty = option_of_signed(64);
        f
    }

    /// A TWO-parameter twin of [`narrow_diamond`] — `fn n2(x: i128, y: i128)`,
    /// guarded on and narrowing `x`. The `param` index must follow the guard,
    /// and the cross-parameter smuggling row below flips only the cast source.
    fn narrow_diamond_two_params() -> VerifiableFunction {
        let mut f = narrow_diamond();
        f.body.arg_count = 2;
        f.body.locals = vec![
            LocalDecl { index: 0, ty: option_of_signed(64), name: None },
            LocalDecl { index: 1, ty: i128_ty(), name: Some("x".into()) },
            LocalDecl { index: 2, ty: i128_ty(), name: Some("y".into()) },
            LocalDecl { index: 3, ty: Ty::Bool, name: None },
            LocalDecl { index: 4, ty: Ty::Bool, name: None },
            LocalDecl { index: 5, ty: i64_ty(), name: None },
        ];
        // Renumber the guard flags to `_3`/`_4` and the cast temp to `_5`.
        f.body.blocks[0].stmts = vec![assign(
            Place::local(3),
            Rvalue::BinaryOp(
                BinOp::Ge,
                Operand::Copy(Place::local(1)),
                Operand::Constant(ConstValue::Int(I64_MIN_AT_128)),
            ),
        )];
        if let Terminator::SwitchInt { discr, .. } = &mut f.body.blocks[0].terminator {
            *discr = Operand::Move(Place::local(3));
        }
        f.body.blocks[1].stmts = vec![assign(
            Place::local(4),
            Rvalue::BinaryOp(
                BinOp::Le,
                Operand::Copy(Place::local(1)),
                Operand::Constant(ConstValue::Int(I64_MAX_AT_128)),
            ),
        )];
        if let Terminator::SwitchInt { discr, .. } = &mut f.body.blocks[1].terminator {
            *discr = Operand::Move(Place::local(4));
        }
        f.body.blocks[2].stmts = vec![
            assign(Place::local(5), Rvalue::Cast(Operand::Copy(Place::local(1)), i64_ty())),
            assign(
                Place::local(0),
                Rvalue::Aggregate(option_agg(64, 1), vec![Operand::Move(Place::local(5))]),
            ),
        ];
        f.body.blocks[4].stmts = vec![];
        f
    }

    /// POSITIVE: both measured spellings recognize as the SAME shape, and a
    /// two-parameter twin indexes its guarded parameter correctly.
    #[test]
    fn guarded_narrow_positive_matrix() {
        let expected =
            Some(AdmissibleBody::GuardedNarrow { from_bits: 128, to_bits: 64, param: 0 });
        assert_eq!(
            recognize_admissible_body(&narrow_diamond()),
            expected,
            "c2: the inline-guard 5-block diamond"
        );
        assert_eq!(
            recognize_admissible_body(&narrow_diamond_trampoline()),
            expected,
            "c10: the call-inlined permuted diamond with a goto trampoline"
        );
        assert_eq!(
            recognize_admissible_body(&narrow_diamond_two_params()),
            expected,
            "a two-parameter twin guarded on and narrowing parameter 0"
        );
    }

    /// FAIL-CLOSED battery. Every row is a swap vector that would mint a WRONG
    /// contract if it were accepted; each must recognize as `None`. If any row
    /// ever starts admitting, that is a soundness incident, not a test update.
    #[test]
    fn guarded_narrow_fail_closed_battery() {
        // (1) The unsound UNGUARDED body — probe c11: one block, no switch,
        // `Some(x as i64)` with NO width check at all.
        let mut unguarded = narrow_diamond();
        unguarded.body.blocks = vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![
                assign(Place::local(4), Rvalue::Cast(Operand::Copy(Place::local(1)), i64_ty())),
                assign(
                    Place::local(0),
                    Rvalue::Aggregate(option_agg(64, 1), vec![Operand::Move(Place::local(4))]),
                ),
            ],
            terminator: Terminator::Return,
        }];
        assert_eq!(recognize_admissible_body(&unguarded), None, "unguarded truncation (c11)");

        // (2) ARMS SWAPPED — `None` on the guard-TRUE edge, `Some` on the
        // false edge. The unsound shape: a wide value admitted into storage.
        let mut swapped = narrow_diamond();
        let some_stmts = swapped.body.blocks[2].stmts.clone();
        let none_stmts = swapped.body.blocks[3].stmts.clone();
        swapped.body.blocks[2].stmts = none_stmts;
        swapped.body.blocks[3].stmts = some_stmts;
        assert_eq!(recognize_admissible_body(&swapped), None, "arms swapped");

        // (3) The `0` and `otherwise` edges of the SECOND switch swapped (the
        // same wrong-verdict class reached through the CFG instead of the
        // statements).
        let mut edges = narrow_diamond();
        if let Terminator::SwitchInt { targets, otherwise, .. } = &mut edges.body.blocks[1].terminator
        {
            *targets = vec![(0, BlockId(2))];
            *otherwise = BlockId(3);
        }
        assert_eq!(recognize_admissible_body(&edges), None, "second switch edges swapped");

        // (4) BOUND DRIFT: the upper bound off by one, and the lower bound at
        // the wrong magnitude, and a POSITIVE literal where the negative
        // lower bound belongs.
        for (name, lo, hi) in [
            ("upper bound off by one", I64_MIN_AT_128, I64_MAX_AT_128 + 1),
            ("lower bound off by one", I64_MIN_AT_128 + 1, I64_MAX_AT_128),
            ("i32 bounds", -2_147_483_648, 2_147_483_647),
            ("sign-flipped lower bound", -I64_MIN_AT_128, I64_MAX_AT_128),
        ] {
            let mut drift = narrow_diamond();
            drift.body.blocks[0].stmts = vec![assign(
                Place::local(2),
                Rvalue::BinaryOp(
                    BinOp::Ge,
                    Operand::Copy(Place::local(1)),
                    Operand::Constant(ConstValue::Int(lo)),
                ),
            )];
            drift.body.blocks[1].stmts = vec![assign(
                Place::local(3),
                Rvalue::BinaryOp(
                    BinOp::Le,
                    Operand::Copy(Place::local(1)),
                    Operand::Constant(ConstValue::Int(hi)),
                ),
            )];
            assert_eq!(recognize_admissible_body(&drift), None, "{name}");
        }

        // (5) COMPARISON SENSE FLIPS: `>` / `<` where `>=` / `<=` was
        // measured, and the two bounds in the other order.
        for (name, lo_op, hi_op) in [
            ("strict lower bound", BinOp::Gt, BinOp::Le),
            ("strict upper bound", BinOp::Ge, BinOp::Lt),
            ("equality guard", BinOp::Eq, BinOp::Le),
        ] {
            let mut flip = narrow_diamond();
            flip.body.blocks[0].stmts = vec![assign(
                Place::local(2),
                Rvalue::BinaryOp(
                    lo_op,
                    Operand::Copy(Place::local(1)),
                    Operand::Constant(ConstValue::Int(I64_MIN_AT_128)),
                ),
            )];
            flip.body.blocks[1].stmts = vec![assign(
                Place::local(3),
                Rvalue::BinaryOp(
                    hi_op,
                    Operand::Copy(Place::local(1)),
                    Operand::Constant(ConstValue::Int(I64_MAX_AT_128)),
                ),
            )];
            assert_eq!(recognize_admissible_body(&flip), None, "{name}");
        }
        let mut reordered = narrow_diamond();
        reordered.body.blocks[0].stmts = vec![assign(
            Place::local(2),
            Rvalue::BinaryOp(
                BinOp::Le,
                Operand::Copy(Place::local(1)),
                Operand::Constant(ConstValue::Int(I64_MAX_AT_128)),
            ),
        )];
        reordered.body.blocks[1].stmts = vec![assign(
            Place::local(3),
            Rvalue::BinaryOp(
                BinOp::Ge,
                Operand::Copy(Place::local(1)),
                Operand::Constant(ConstValue::Int(I64_MIN_AT_128)),
            ),
        )];
        assert_eq!(recognize_admissible_body(&reordered), None, "bounds in the other order");

        // (6) `||` INSTEAD OF `&&`: the first comparison's TRUE edge goes
        // straight to the `Some` arm, so the value is admitted when EITHER
        // bound holds.
        let mut disjunction = narrow_diamond();
        if let Terminator::SwitchInt { targets, otherwise, .. } =
            &mut disjunction.body.blocks[0].terminator
        {
            *targets = vec![(0, BlockId(1))];
            *otherwise = BlockId(2);
        }
        assert_eq!(recognize_admissible_body(&disjunction), None, "`||` guard");

        // (7) WRONG CAST WIDTH: the payload truncated to 32 bits and stored
        // into an `Option<i64>`.
        let mut narrow32 = narrow_diamond();
        narrow32.body.locals[4].ty = Ty::Int { width: 32, signed: true };
        narrow32.body.blocks[2].stmts[1] = assign(
            Place::local(4),
            Rvalue::Cast(Operand::Copy(Place::local(1)), Ty::Int { width: 32, signed: true }),
        );
        assert_eq!(recognize_admissible_body(&narrow32), None, "cast to the wrong width");

        // (8) The cast TARGET and the temp's declared type disagreeing.
        let mut mistyped = narrow_diamond();
        mistyped.body.locals[4].ty = Ty::Int { width: 32, signed: true };
        assert_eq!(recognize_admissible_body(&mistyped), None, "cast temp mistyped");

        // (9) An UNSIGNED cast target of the right width.
        let mut unsigned_cast = narrow_diamond();
        unsigned_cast.body.locals[4].ty = Ty::Int { width: 64, signed: false };
        unsigned_cast.body.blocks[2].stmts[1] = assign(
            Place::local(4),
            Rvalue::Cast(Operand::Copy(Place::local(1)), Ty::Int { width: 64, signed: false }),
        );
        assert_eq!(recognize_admissible_body(&unsigned_cast), None, "unsigned cast target");

        // (10) An UNSIGNED source parameter (`u128 -> Option<i64>`).
        let mut unsigned_src = narrow_diamond();
        unsigned_src.body.locals[1].ty = Ty::Int { width: 128, signed: false };
        assert_eq!(recognize_admissible_body(&unsigned_src), None, "unsigned source parameter");

        // (11) A SOURCE WIDTH other than 128 — the (from, to) pair parks.
        let mut from64 = narrow_diamond();
        from64.body.locals[1].ty = i64_ty();
        assert_eq!(recognize_admissible_body(&from64), None, "i64 source width parks");

        // (12) NON-OPTION return: the same diamond returning `i64`.
        let mut scalar_ret = narrow_diamond();
        scalar_ret.body.return_ty = i64_ty();
        scalar_ret.body.locals[0].ty = i64_ty();
        assert_eq!(recognize_admissible_body(&scalar_ret), None, "non-Option return");

        // (13) A NICHE-encoded Option (`disc_index_safe == false`): variant
        // indices no longer mean what they say, so the shape is refused.
        let mut niche = narrow_diamond();
        let niche_ty = Ty::adt_enum_with_disc_safety(
            "core::option::Option",
            vec![
                crate::VariantDef { name: "None".into(), discriminant: 0, fields: vec![] },
                crate::VariantDef {
                    name: "Some".into(),
                    discriminant: 1,
                    fields: vec![("0".into(), i64_ty())],
                },
            ],
            false,
        );
        niche.body.return_ty = niche_ty.clone();
        niche.body.locals[0].ty = niche_ty;
        assert_eq!(recognize_admissible_body(&niche), None, "niche-encoded Option");

        // (14) The return SLOT's declared type disagreeing with the signature.
        let mut slot_drift = narrow_diamond();
        slot_drift.body.locals[0].ty = option_of_signed(32);
        assert_eq!(recognize_admissible_body(&slot_drift), None, "return slot type drift");

        // (15) A PROMOTED `const Some(0)` sitting in the `None` slot: refused
        // by VALUE (variant + operand count), never accepted by type alone.
        let mut fake_none = narrow_diamond();
        fake_none.body.blocks[3].stmts = vec![assign(
            Place::local(0),
            Rvalue::Aggregate(
                option_agg(64, 1),
                vec![Operand::Constant(ConstValue::Int(0))],
            ),
        )];
        assert_eq!(recognize_admissible_body(&fake_none), None, "`Some(0)` in the None slot");

        // (16) A `None` aggregate at the WRONG instantiation (`Option<i32>`).
        let mut wrong_args = narrow_diamond();
        wrong_args.body.blocks[3].stmts = vec![assign(
            Place::local(0),
            Rvalue::Aggregate(option_agg(32, 0), vec![]),
        )];
        assert_eq!(recognize_admissible_body(&wrong_args), None, "None at the wrong Option arg");

        // (17) An EXTRA EFFECTFUL STATEMENT in the `Some` arm.
        let mut extra_stmt = narrow_diamond();
        extra_stmt.body.blocks[2].stmts.insert(
            1,
            assign(Place::local(3), Rvalue::Use(Operand::Constant(ConstValue::Bool(true)))),
        );
        assert_eq!(recognize_admissible_body(&extra_stmt), None, "extra statement in the Some arm");

        // (18) The `Some` payload ALIASED — the aggregate names a local other
        // than the cast temp.
        let mut aliased = narrow_diamond();
        aliased.body.blocks[2].stmts[2] = assign(
            Place::local(0),
            Rvalue::Aggregate(option_agg(64, 1), vec![Operand::Copy(Place::local(3))]),
        );
        assert_eq!(recognize_admissible_body(&aliased), None, "aliased Some payload");

        // (19) A PROJECTED guard operand and a PROJECTED cast source.
        let mut projected_guard = narrow_diamond();
        projected_guard.body.blocks[0].stmts = vec![assign(
            Place::local(2),
            Rvalue::BinaryOp(
                BinOp::Ge,
                Operand::Copy(Place::field(1, 0)),
                Operand::Constant(ConstValue::Int(I64_MIN_AT_128)),
            ),
        )];
        assert_eq!(recognize_admissible_body(&projected_guard), None, "projected guard operand");
        let mut projected_cast = narrow_diamond();
        projected_cast.body.blocks[2].stmts[1] =
            assign(Place::local(4), Rvalue::Cast(Operand::Copy(Place::field(1, 0)), i64_ty()));
        assert_eq!(recognize_admissible_body(&projected_cast), None, "projected cast source");

        // (20) ARMS WRITING DIFFERENT PLACES: the `None` arm writes a temp.
        let mut split_places = narrow_diamond();
        split_places.body.blocks[3].stmts = vec![assign(
            Place::local(4),
            Rvalue::Aggregate(option_agg(64, 0), vec![]),
        )];
        assert_eq!(recognize_admissible_body(&split_places), None, "arms write different places");

        // (21) MISMATCHED JOINS, and a NON-`Return` join.
        let mut split_join = narrow_diamond();
        split_join.body.blocks[3].terminator = Terminator::Goto(BlockId(0));
        assert_eq!(recognize_admissible_body(&split_join), None, "arms join different blocks");
        let mut bad_join = narrow_diamond();
        bad_join.body.blocks[4].terminator = Terminator::Unreachable;
        assert_eq!(recognize_admissible_body(&bad_join), None, "non-Return join");
        let mut busy_join = narrow_diamond();
        busy_join.body.blocks[4].stmts = vec![assign(
            Place::local(0),
            Rvalue::Aggregate(option_agg(64, 0), vec![]),
        )];
        assert_eq!(recognize_admissible_body(&busy_join), None, "effectful join");

        // (22) CROSS-PARAMETER SMUGGLING: guard on `x`, narrow `y`.
        let mut smuggle = narrow_diamond_two_params();
        smuggle.body.blocks[2].stmts[0] =
            assign(Place::local(5), Rvalue::Cast(Operand::Copy(Place::local(2)), i64_ty()));
        assert_eq!(recognize_admissible_body(&smuggle), None, "guard on x, narrow y");

        // (23) The two bounds guarding DIFFERENT parameters.
        let mut split_param = narrow_diamond_two_params();
        split_param.body.blocks[1].stmts = vec![assign(
            Place::local(4),
            Rvalue::BinaryOp(
                BinOp::Le,
                Operand::Copy(Place::local(2)),
                Operand::Constant(ConstValue::Int(I64_MAX_AT_128)),
            ),
        )];
        assert_eq!(recognize_admissible_body(&split_param), None, "bounds on different parameters");

        // (24) The two false edges reaching DIFFERENT `None` blocks: a body
        // whose second false edge lands on its own duplicate arm.
        let mut two_nones = narrow_diamond();
        two_nones.body.blocks.push(BasicBlock {
            id: BlockId(5),
            stmts: vec![assign(
                Place::local(0),
                Rvalue::Aggregate(option_agg(64, 0), vec![]),
            )],
            terminator: Terminator::Goto(BlockId(4)),
        });
        if let Terminator::SwitchInt { targets, .. } = &mut two_nones.body.blocks[1].terminator {
            *targets = vec![(0, BlockId(5))];
        }
        assert_eq!(recognize_admissible_body(&two_nones), None, "two distinct None blocks");

        // (25) A GUARD FLAG REUSED for both comparisons (the second switch
        // would then read a value the first already consumed).
        let mut shared_flag = narrow_diamond();
        shared_flag.body.blocks[1].stmts = vec![assign(
            Place::local(2),
            Rvalue::BinaryOp(
                BinOp::Le,
                Operand::Copy(Place::local(1)),
                Operand::Constant(ConstValue::Int(I64_MAX_AT_128)),
            ),
        )];
        if let Terminator::SwitchInt { discr, .. } = &mut shared_flag.body.blocks[1].terminator {
            *discr = Operand::Move(Place::local(2));
        }
        assert_eq!(recognize_admissible_body(&shared_flag), None, "one flag for both comparisons");

        // (26) A `switchInt` on something other than the comparison it just
        // computed, and one with a THIRD successor / a non-`0` case value.
        let mut wrong_discr = narrow_diamond();
        if let Terminator::SwitchInt { discr, .. } = &mut wrong_discr.body.blocks[0].terminator {
            *discr = Operand::Move(Place::local(3));
        }
        assert_eq!(recognize_admissible_body(&wrong_discr), None, "switch on the wrong local");
        let mut three_way = narrow_diamond();
        if let Terminator::SwitchInt { targets, .. } = &mut three_way.body.blocks[0].terminator {
            *targets = vec![(0, BlockId(3)), (1, BlockId(3))];
        }
        assert_eq!(recognize_admissible_body(&three_way), None, "three-way switch");
        let mut nonzero_case = narrow_diamond();
        if let Terminator::SwitchInt { targets, .. } = &mut nonzero_case.body.blocks[0].terminator {
            *targets = vec![(1, BlockId(3))];
        }
        assert_eq!(recognize_admissible_body(&nonzero_case), None, "non-zero switch case");

        // (27) An `Assert` ANYWHERE in the body.
        let mut asserted = narrow_diamond();
        asserted.body.blocks[4].terminator = Terminator::Assert {
            cond: Operand::Copy(Place::local(2)),
            expected: true,
            msg: crate::AssertMessage::Custom("boom".into()),
            target: BlockId(4),
            unwind: crate::UnwindEdge::Unreachable,
            span: SourceSpan::default(),
        };
        assert_eq!(recognize_admissible_body(&asserted), None, "an Assert anywhere");

        // (28) A CALL on the None edge — the checked lane's `cold_path` hint
        // is NOT accepted here (neither measured spelling has one).
        let mut cold = narrow_diamond();
        cold.body.locals.push(LocalDecl { index: 5, ty: Ty::Unit, name: None });
        cold.body.blocks.push(BasicBlock {
            id: BlockId(5),
            stmts: vec![],
            terminator: Terminator::Call {
                func: "core::intrinsics::cold_path".into(),
                callee_identity: None,
                args: vec![],
                dest: Place::local(5),
                target: Some(BlockId(3)),
                span: SourceSpan::default(),
                atomic: None,
                is_foreign: false,
                is_unsafe_sig: false,
                unwind: crate::UnwindEdge::Unreachable,
            },
        });
        if let Terminator::SwitchInt { targets, .. } = &mut cold.body.blocks[0].terminator {
            *targets = vec![(0, BlockId(5))];
        }
        assert_eq!(recognize_admissible_body(&cold), None, "a cold_path hint block");

        // (29) An EXTRA unreached block that is not a trampoline.
        let mut extra_block = narrow_diamond();
        extra_block.body.blocks.push(BasicBlock {
            id: BlockId(5),
            stmts: vec![],
            terminator: Terminator::Unreachable,
        });
        assert_eq!(recognize_admissible_body(&extra_block), None, "an extra unrecognized block");

        // (30) A TRAMPOLINE CHAIN longer than the measured one, and a `goto`
        // CYCLE, both fail closed rather than looping.
        let mut long_chain = narrow_diamond();
        for (id, next) in [(5u32, 6u32), (6, 7), (7, 3)] {
            long_chain.body.blocks.push(BasicBlock {
                id: BlockId(id as usize),
                stmts: vec![],
                terminator: Terminator::Goto(BlockId(next as usize)),
            });
        }
        if let Terminator::SwitchInt { targets, .. } = &mut long_chain.body.blocks[0].terminator {
            *targets = vec![(0, BlockId(5))];
        }
        assert_eq!(recognize_admissible_body(&long_chain), None, "trampoline chain too long");
        let mut cycle = narrow_diamond();
        cycle.body.blocks.push(BasicBlock {
            id: BlockId(5),
            stmts: vec![],
            terminator: Terminator::Goto(BlockId(5)),
        });
        if let Terminator::SwitchInt { targets, .. } = &mut cycle.body.blocks[0].terminator {
            *targets = vec![(0, BlockId(5))];
        }
        assert_eq!(recognize_admissible_body(&cycle), None, "a goto cycle");

        // (31) A NON-cast rvalue in the `Some` arm's first slot (a bare `Use`
        // of the parameter would be an UNTRUNCATED payload at the wrong type).
        let mut no_cast = narrow_diamond();
        no_cast.body.blocks[2].stmts[1] =
            assign(Place::local(4), Rvalue::Use(Operand::Copy(Place::local(1))));
        assert_eq!(recognize_admissible_body(&no_cast), None, "a Use where the cast belongs");

        // (32) The cast writing a PARAMETER or the RETURN place rather than a
        // fresh temp.
        let mut cast_to_param = narrow_diamond_two_params();
        cast_to_param.body.blocks[2].stmts[0] =
            assign(Place::local(2), Rvalue::Cast(Operand::Copy(Place::local(1)), i64_ty()));
        assert_eq!(recognize_admissible_body(&cast_to_param), None, "cast into a parameter");
        let mut cast_to_ret = narrow_diamond();
        cast_to_ret.body.blocks[2].stmts[1] =
            assign(Place::local(0), Rvalue::Cast(Operand::Copy(Place::local(1)), i64_ty()));
        assert_eq!(recognize_admissible_body(&cast_to_ret), None, "cast into the return place");

        // (33) A zero-parameter body: nothing to guard.
        let mut nullary = narrow_diamond();
        nullary.body.arg_count = 0;
        assert_eq!(recognize_admissible_body(&nullary), None, "no parameters");
    }

    /// `fn k() -> iN { V }` at the measured `-O` shape: one block, one
    /// statement, `_0 = const V_iN`, `return`. `ret` is the DECLARED return
    /// type and `ret_local_ty` local `_0`'s own declared type — separate
    /// parameters so the signature/local DISAGREEMENT gate is exercisable.
    fn signed_const_fn(value: i128, ret: Ty, ret_local_ty: Ty) -> VerifiableFunction {
        let mut f = func(
            0,
            vec![assign(
                Place::local(0),
                Rvalue::Use(Operand::Constant(ConstValue::Int(value))),
            )],
            Terminator::Return,
        );
        f.body.return_ty = ret;
        f.body.locals = vec![LocalDecl { index: 0, ty: ret_local_ty, name: None }];
        f
    }

    fn signed_const(value: i128, width: u32) -> VerifiableFunction {
        let ty = Ty::Int { width, signed: true };
        signed_const_fn(value, ty.clone(), ty)
    }

    /// The four real client bodies this increment unblocks, plus the sign and
    /// BOUNDARY values whose kernel spelling differs (`0` takes `Domain::zero`,
    /// a negative takes `negative_numeral`, `iN::MIN` is the extreme the
    /// magnitude encoding must survive).
    #[test]
    fn signed_constant_positive_matrix() {
        for (value, width) in [
            // `<i64 as CoeffDomain>::zero` / `::one`.
            (0i128, 64u32),
            (1, 64),
            // `<i128 as Exact>::zero` / `::one`.
            (0, 128),
            (1, 128),
            // Sign and boundary coverage at every admitted width.
            (-1, 64),
            (-7, 64),
            (i128::from(i64::MIN), 64),
            (i128::from(i64::MAX), 64),
            (i128::MIN, 128),
            (i128::MAX, 128),
            (i128::from(i8::MIN), 8),
            (i128::from(i8::MAX), 8),
            (i128::from(i32::MIN), 32),
            (i128::from(i32::MAX), 32),
        ] {
            assert_eq!(
                recognize_admissible_body(&signed_const(value, width)),
                Some(AdmissibleBody::ConstantInt { value, width_bits: width }),
                "a signed literal {value} at i{width} must be recognized"
            );
        }
    }

    /// Every way a signed-constant lookalike must FAIL CLOSED.
    #[test]
    fn signed_constant_fail_closed_battery() {
        // The literal does not fit the carrier the signature claims. A width
        // is never inferred from the value, so this can only be refused.
        for (value, width) in [
            (128i128, 8u32),
            (-129, 8),
            (i128::from(i32::MAX) + 1, 32),
            (i128::from(i32::MIN) - 1, 32),
            (i128::from(i64::MAX) + 1, 64),
            (i128::from(i64::MIN) - 1, 64),
        ] {
            assert_eq!(
                recognize_admissible_body(&signed_const(value, width)),
                None,
                "literal {value} does not fit i{width}"
            );
        }

        // An UNSIGNED carrier never takes the signed lane: `ConstValue::Int`
        // at a `uN` return has no `Domain::Signed` mint, and reading it as one
        // would give `-1` the value `u64::MAX`.
        for width in [8u32, 16, 32, 64, 128] {
            let ty = Ty::Int { width, signed: false };
            assert_eq!(
                recognize_admissible_body(&signed_const_fn(-1, ty.clone(), ty)),
                None,
                "a signed literal at a u{width} return must fail closed"
            );
        }
        // …and neither does a non-integer carrier.
        for ty in [Ty::Bool, Ty::PtrSizedInt { signed: true }] {
            assert_eq!(
                recognize_admissible_body(&signed_const_fn(1, ty.clone(), ty)),
                None,
                "a signed literal at a non-`Ty::Int` return must fail closed"
            );
        }

        // The signature and the return place's own declared type must AGREE:
        // a width taken from a signature the local contradicts is exactly the
        // wrong-width mint this gate exists to stop.
        assert_eq!(
            recognize_admissible_body(&signed_const_fn(
                1,
                Ty::Int { width: 64, signed: true },
                Ty::Int { width: 32, signed: true },
            )),
            None,
            "a return type the return LOCAL contradicts must fail closed"
        );
        assert_eq!(
            recognize_admissible_body(&signed_const_fn(
                1,
                Ty::Int { width: 64, signed: true },
                Ty::Int { width: 64, signed: false },
            )),
            None,
            "a signed signature over an unsigned return local must fail closed"
        );
        // A malformed local table (no row for `_0`) fails closed rather than
        // typing through a missing row.
        let mut no_ret_local = signed_const(1, 64);
        no_ret_local.body.locals.clear();
        assert_eq!(recognize_admissible_body(&no_ret_local), None, "no `_0` row");

        // The constant must be the WHOLE body, written to the BARE return
        // place, in a single RETURNING block.
        let mut projected = signed_const(1, 64);
        projected.body.blocks[0].stmts[0] = assign(
            Place::field(0, 0),
            Rvalue::Use(Operand::Constant(ConstValue::Int(1))),
        );
        assert_eq!(recognize_admissible_body(&projected), None, "a projected return place");

        let mut not_return_place = signed_const(1, 64);
        not_return_place.body.locals.push(LocalDecl {
            index: 1,
            ty: Ty::Int { width: 64, signed: true },
            name: None,
        });
        not_return_place.body.blocks[0].stmts[0] = assign(
            Place::local(1),
            Rvalue::Use(Operand::Constant(ConstValue::Int(1))),
        );
        assert_eq!(recognize_admissible_body(&not_return_place), None, "writes a temp, not `_0`");

        let mut extra_stmt = signed_const(1, 64);
        extra_stmt.body.locals.push(LocalDecl {
            index: 1,
            ty: Ty::Int { width: 64, signed: true },
            name: None,
        });
        extra_stmt.body.blocks[0].stmts.push(assign(
            Place::local(1),
            Rvalue::Use(Operand::Constant(ConstValue::Int(2))),
        ));
        assert_eq!(
            recognize_admissible_body(&extra_stmt),
            None,
            "a second value statement must fail closed"
        );

        let mut goto_term = signed_const(1, 64);
        goto_term.body.blocks[0].terminator = Terminator::Goto(BlockId(1));
        assert_eq!(recognize_admissible_body(&goto_term), None, "a non-`Return` terminator");

        // Bookkeeping statements around the constant stay value-neutral.
        let mut with_bookkeeping = signed_const(-3, 64);
        with_bookkeeping.body.blocks[0].stmts.insert(0, Statement::StorageLive(0));
        with_bookkeeping.body.blocks[0].stmts.push(Statement::StorageDead(0));
        assert_eq!(
            recognize_admissible_body(&with_bookkeeping),
            Some(AdmissibleBody::ConstantInt { value: -3, width_bits: 64 }),
            "StorageLive/Dead around the constant stay value-neutral"
        );
    }

    /// The measured `-O` body of `veripb_core_proved::guard::eq_ok`, statement
    /// for statement: locals `_0` = `bool`, `_1` = the narrow `i64` parameter,
    /// `_2` = the wide `i128` parameter, `_3` = the cast temp.
    fn widened_eq_fn() -> VerifiableFunction {
        let mut f = func(
            2,
            vec![
                Statement::StorageLive(3),
                assign(Place::local(3), Rvalue::Cast(Operand::Copy(Place::local(1)), i128_ty())),
                assign(
                    Place::local(0),
                    Rvalue::BinaryOp(
                        BinOp::Eq,
                        Operand::Move(Place::local(3)),
                        Operand::Copy(Place::local(2)),
                    ),
                ),
                Statement::StorageDead(3),
            ],
            Terminator::Return,
        );
        f.body.return_ty = Ty::Bool;
        f.body.locals = vec![
            LocalDecl { index: 0, ty: Ty::Bool, name: None },
            LocalDecl { index: 1, ty: i64_ty(), name: None },
            LocalDecl { index: 2, ty: i128_ty(), name: None },
            LocalDecl { index: 3, ty: i128_ty(), name: None },
        ];
        f
    }

    #[test]
    fn widened_eq_positive_matrix() {
        assert_eq!(
            recognize_admissible_body(&widened_eq_fn()),
            Some(AdmissibleBody::WidenedEq {
                from_bits: 64,
                to_bits: 128,
                narrow_param: 0,
                wide_param: 1,
                cast_on_left: true,
            }),
            "the measured `eq_ok` body must be recognized"
        );

        // `truth == Wide::from(machine)` — the same body with the operands
        // written the other way round (measured: `Eq(copy _2, move _3)`). The
        // side is RECORDED, not normalized away, because the minted `Eq` is
        // spelled over `BitVec.toNat` of each side and is not symmetric.
        let mut swapped = widened_eq_fn();
        swapped.body.blocks[0].stmts[2] = assign(
            Place::local(0),
            Rvalue::BinaryOp(
                BinOp::Eq,
                Operand::Copy(Place::local(2)),
                Operand::Move(Place::local(3)),
            ),
        );
        assert_eq!(
            recognize_admissible_body(&swapped),
            Some(AdmissibleBody::WidenedEq {
                from_bits: 64,
                to_bits: 128,
                narrow_param: 0,
                wide_param: 1,
                cast_on_left: false,
            }),
            "the reversed operand order must be recognized, and RECORDED"
        );

        // The parameters in the other declaration order, so neither index is
        // hard-wired.
        let mut reordered = widened_eq_fn();
        reordered.body.locals[1].ty = i128_ty();
        reordered.body.locals[2].ty = i64_ty();
        reordered.body.blocks[0].stmts[1] =
            assign(Place::local(3), Rvalue::Cast(Operand::Copy(Place::local(2)), i128_ty()));
        reordered.body.blocks[0].stmts[2] = assign(
            Place::local(0),
            Rvalue::BinaryOp(
                BinOp::Eq,
                Operand::Move(Place::local(3)),
                Operand::Copy(Place::local(1)),
            ),
        );
        assert_eq!(
            recognize_admissible_body(&reordered),
            Some(AdmissibleBody::WidenedEq {
                from_bits: 64,
                to_bits: 128,
                narrow_param: 1,
                wide_param: 0,
                cast_on_left: true,
            }),
            "the narrow parameter need not be `p0`"
        );
    }

    /// Every faithfulness hazard of the widening-cast lane, pinned REFUSED.
    /// Each of these is a body that would be a WRONG kernel model if it rode
    /// the sign-extension mint.
    #[test]
    fn widened_eq_fail_closed_battery() {
        // (1) A TRUNCATING cast — `(x as i64) == t` at i128 -> i64, the
        // measured `eq_ok_trunc` shape. Modeling it as sign extension would
        // claim a value-preserving widening for a wrapping narrowing.
        let mut truncating = widened_eq_fn();
        truncating.body.locals[1].ty = i128_ty();
        truncating.body.locals[2].ty = i64_ty();
        truncating.body.locals[3].ty = i64_ty();
        truncating.body.blocks[0].stmts[1] =
            assign(Place::local(3), Rvalue::Cast(Operand::Copy(Place::local(1)), i64_ty()));
        assert_eq!(
            recognize_admissible_body(&truncating),
            None,
            "a TRUNCATING cast must never be recognized as widening"
        );

        // (2) An UNSIGNED source — `(a: u64 as i128) == t`. rustc lowers this
        // to the IDENTICAL `IntToInt` spelling, but it is ZERO extension: it
        // disagrees with sign extension on exactly the negative half of the
        // 64-bit domain.
        let mut unsigned_src = widened_eq_fn();
        unsigned_src.body.locals[1].ty = Ty::Int { width: 64, signed: false };
        assert_eq!(
            recognize_admissible_body(&unsigned_src),
            None,
            "a ZERO-extending unsigned source must fail closed"
        );

        // (3) An UNSIGNED target, and a mismatched target: the cast type, the
        // temp's declared type and the wide parameter must all be the same
        // signed carrier.
        for (cast_ty, temp_ty, wide_ty) in [
            (Ty::Int { width: 128, signed: false }, Ty::Int { width: 128, signed: false }, Ty::Int { width: 128, signed: false }),
            (i128_ty(), Ty::Int { width: 128, signed: false }, i128_ty()),
            (i128_ty(), i128_ty(), Ty::Int { width: 128, signed: false }),
            (i64_ty(), i128_ty(), i128_ty()),
        ] {
            let mut f = widened_eq_fn();
            f.body.locals[2].ty = wide_ty;
            f.body.locals[3].ty = temp_ty;
            f.body.blocks[0].stmts[1] =
                assign(Place::local(3), Rvalue::Cast(Operand::Copy(Place::local(1)), cast_ty));
            assert_eq!(
                recognize_admissible_body(&f),
                None,
                "a target-carrier disagreement must fail closed"
            );
        }

        // (4) An unmeasured WIDTH PAIR — `(a: i32 as i64) == b`. It is a
        // genuine sign extension, but the lane is monomorphic by design and
        // an unmeasured spelling parks rather than being assumed.
        let mut i32_to_i64 = widened_eq_fn();
        i32_to_i64.body.locals[1].ty = Ty::Int { width: 32, signed: true };
        i32_to_i64.body.locals[2].ty = i64_ty();
        i32_to_i64.body.locals[3].ty = i64_ty();
        i32_to_i64.body.blocks[0].stmts[1] =
            assign(Place::local(3), Rvalue::Cast(Operand::Copy(Place::local(1)), i64_ty()));
        assert_eq!(recognize_admissible_body(&i32_to_i64), None, "(i32 -> i64) parks");

        // (5) BOTH sides cast — measured as THREE value statements, so the
        // exact-two gate refuses it.
        let mut both_cast = widened_eq_fn();
        both_cast.body.locals[2].ty = i64_ty();
        both_cast.body.locals.push(LocalDecl { index: 4, ty: i128_ty(), name: None });
        both_cast.body.blocks[0].stmts.insert(
            2,
            assign(Place::local(4), Rvalue::Cast(Operand::Copy(Place::local(2)), i128_ty())),
        );
        both_cast.body.blocks[0].stmts[3] = assign(
            Place::local(0),
            Rvalue::BinaryOp(
                BinOp::Eq,
                Operand::Move(Place::local(3)),
                Operand::Move(Place::local(4)),
            ),
        );
        assert_eq!(recognize_admissible_body(&both_cast), None, "both sides cast must fail closed");

        // (6) A cast of a NON-PARAMETER: a projected place (a struct field) and
        // a bare temporary. Neither is an input the mint can bind.
        for src in [Operand::Copy(Place::field(1, 0)), Operand::Copy(Place::local(3))] {
            let mut f = widened_eq_fn();
            f.body.blocks[0].stmts[1] = assign(Place::local(3), Rvalue::Cast(src, i128_ty()));
            assert_eq!(
                recognize_admissible_body(&f),
                None,
                "a cast of a non-parameter must fail closed"
            );
        }

        // (7) Any comparison other than `Eq`.
        for op in [BinOp::Ne, BinOp::Lt, BinOp::Le, BinOp::Gt, BinOp::Ge] {
            let mut f = widened_eq_fn();
            f.body.blocks[0].stmts[2] = assign(
                Place::local(0),
                Rvalue::BinaryOp(
                    op,
                    Operand::Move(Place::local(3)),
                    Operand::Copy(Place::local(2)),
                ),
            );
            assert_eq!(recognize_admissible_body(&f), None, "{op:?} must fail closed");
        }

        // (8) A LITERAL on the other side — measured (`cast_vs_lit`), and
        // parked: the mint does no range check for a bound here.
        let mut lit_other = widened_eq_fn();
        lit_other.body.blocks[0].stmts[2] = assign(
            Place::local(0),
            Rvalue::BinaryOp(
                BinOp::Eq,
                Operand::Move(Place::local(3)),
                Operand::Constant(ConstValue::Int(5)),
            ),
        );
        assert_eq!(recognize_admissible_body(&lit_other), None, "a literal other operand parks");

        // (9) A non-`bool` return, by the signature or by the return LOCAL.
        let mut int_return = widened_eq_fn();
        int_return.body.return_ty = i128_ty();
        int_return.body.locals[0].ty = i128_ty();
        assert_eq!(recognize_admissible_body(&int_return), None, "a non-`bool` return");
        let mut local_disagrees = widened_eq_fn();
        local_disagrees.body.locals[0].ty = i128_ty();
        assert_eq!(
            recognize_admissible_body(&local_disagrees),
            None,
            "a return local contradicting the `bool` signature"
        );

        // (10) A projected write of the result, and a cast destination that is
        // a PARAMETER rather than a fresh temporary.
        let mut projected_result = widened_eq_fn();
        projected_result.body.blocks[0].stmts[2] = assign(
            Place::field(0, 0),
            Rvalue::BinaryOp(
                BinOp::Eq,
                Operand::Move(Place::local(3)),
                Operand::Copy(Place::local(2)),
            ),
        );
        assert_eq!(recognize_admissible_body(&projected_result), None, "a projected result place");

        let mut param_dest = widened_eq_fn();
        param_dest.body.locals[2].ty = i128_ty();
        param_dest.body.blocks[0].stmts[1] =
            assign(Place::local(2), Rvalue::Cast(Operand::Copy(Place::local(1)), i128_ty()));
        param_dest.body.blocks[0].stmts[2] = assign(
            Place::local(0),
            Rvalue::BinaryOp(
                BinOp::Eq,
                Operand::Move(Place::local(2)),
                Operand::Copy(Place::local(2)),
            ),
        );
        assert_eq!(
            recognize_admissible_body(&param_dest),
            None,
            "a cast into a PARAMETER must fail closed"
        );

        // (11) The two statements in the other order — the comparison would
        // read an undefined temporary.
        let mut reordered = widened_eq_fn();
        reordered.body.blocks[0].stmts.swap(1, 2);
        assert_eq!(recognize_admissible_body(&reordered), None, "cast after the comparison");

        // (12) More than one block, and a non-`Return` terminator.
        let mut goto_term = widened_eq_fn();
        goto_term.body.blocks[0].terminator = Terminator::Goto(BlockId(1));
        assert_eq!(recognize_admissible_body(&goto_term), None, "a non-`Return` terminator");
        let mut two_blocks = widened_eq_fn();
        two_blocks.body.blocks.push(BasicBlock {
            id: BlockId(1),
            stmts: Vec::new(),
            terminator: Terminator::Return,
        });
        assert_eq!(recognize_admissible_body(&two_blocks), None, "a second block");
    }
}
