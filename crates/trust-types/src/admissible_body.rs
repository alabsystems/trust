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
    BasicBlock, BinOp, BlockId, ConstValue, Operand, Rvalue, Statement, Terminator, Ty,
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
    /// The body returns one of its parameters verbatim — `fn f(.., x, ..) { x }`.
    /// `param` is the 0-based source parameter index.
    Projection {
        /// 0-based index of the returned parameter.
        param: usize,
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
}

/// The comparison a [`AdmissibleBody::Select`] branch tests. Only the comparisons
/// the select elaborator supports; `!=`, `>` and `>=` are not recognized (fail
/// closed) — `>`/`>=` could be normalized to `<`/`<=` with swapped operands, a
/// future refinement.
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
        .or_else(|| recognize_use_chain(func))
        .or_else(|| recognize_call_chain(func))
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

/// The single-block shapes: a constant return or a bare-parameter projection.
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
        // `_0 = _i` (copy/move a bare parameter local) — a projection. Parameters
        // are locals `1..=arg_count` (local `0` is the return place), so a
        // returned local `i` in that range is 0-based source parameter `i-1`.
        Rvalue::Use(Operand::Copy(p)) | Rvalue::Use(Operand::Move(p)) => {
            if p.projections.is_empty() && p.local >= 1 && p.local <= func.body.arg_count {
                Some(AdmissibleBody::Projection { param: p.local - 1 })
            } else {
                None
            }
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

/// The select comparison a `BinOp` denotes, or `None` if unsupported.
fn select_cmp(binop: &BinOp) -> Option<SelectCmp> {
    Some(match binop {
        BinOp::Lt => SelectCmp::Lt,
        BinOp::Le => SelectCmp::Le,
        BinOp::Eq => SelectCmp::Eq,
        _ => return None,
    })
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
        // Returning a projection OF a parameter (`x.0`), not the parameter itself.
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
}
