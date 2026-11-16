//! Direct-lane typed L0 safety-formula MINT (Step 6, increment 1) — the single
//! source of truth for the formula a direct-THIR assert class denotes, built by
//! DELEGATING to this crate's own MIR-lane `reconstruct_*` builders over
//! synthesized `trust_types` inputs. Zero formula-shape recreation lives here:
//! if the bytes match the MIR lane, it is because both lanes executed the SAME
//! constructor over the same operand identities.
//!
//! Design of record: `docs/design/DIRECT-LANE-PROOF-AUTHORITY.md` STEP 6
//! (increment 1, adversarially reviewed 2026-08-31). Home (c): the minted
//! formula is SESSION STATE beside the `DirectObligationRecord` — no row, no
//! artifact byte, no wire format carries it; the non-frozen tier arm's
//! "carries a formula" violation remains the live gate.
//!
//! WHAT THE BYTE CLAIM REDUCES TO. The builders here are the very functions the
//! verdict-flip pins byte-equal against trust-vcgen (`reconstruct_overflow_body`
//! et al.). The mint feeds them operands synthesized from what the DIRECT lane
//! knows at emission — parameter names (`value_names` is params-only) and
//! literals — so the parity question this module's oracle measures is exactly
//! Step 6's: does THIR-held operand identity/width/signedness reproduce what
//! the bridge recovers by block search?
//!
//! FAIL-CLOSED DISCIPLINE:
//! * Every decline names its reason AND the fix (v7/D3): see [`FormulaDecline`].
//! * The post-mint sweep refuses any output containing a fallback-shaped
//!   (`_N`) variable — the mint NEVER fabricates a MIR local index, even when
//!   the guess would happen to be right (a parameter literally named `_1`
//!   declines rather than colliding with the MIR lane's fallback namespace).
//! * `overflow_neg` below signed-128 declines CLASS-WIDE
//!   ([`FormulaDecline::MirCoreIsTempCondVar`]): measured, the MIR lane's core
//!   is a bare bool `Var` over an unnamed MIR temp (`lower.rs` OverflowNeg
//!   arm) — there is no operand-level formula for the mint to independently
//!   derive, and minting one would grade equivalence, not parity.
//! * NO digest is minted here (the id/digest "never inferred or updated
//!   independently" rule): the formula bytes are self-comparable, and a digest
//!   would add exactly the recompute hazard the rule forbids.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{BinOp, ConstValue, Formula, LocalDecl, Operand, Place, Sort, Ty};

use crate::lower::{
    bounds_violation_from_parts, reconstruct_bv_mul_overflow_body,
    reconstruct_bv_signed_neg_overflow_body, reconstruct_divisor_is_zero,
    reconstruct_overflow_body, reconstruct_signed_div_overflow_body, safety_operand_to_formula,
    shift_violation_from_parts,
};

/// One operand as the DIRECT lane knows it at emission — the production
/// knowledge rule: parameter names (the `value_names` ledger is params-only)
/// and literals. Anything else is NOT representable here; the capture declines
/// with [`FormulaDecline::OpaqueOperand`] instead of guessing.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DirectFormulaOperand {
    /// A named source parameter (projection-free, unique by Rust's own
    /// no-duplicate-param-names rule within one signature).
    Named { name: String },
    /// An integer literal representable in `i128` (the `Constant::Int`
    /// carrier every direct-lane `Inst::Const` uses).
    Lit(i128),
    /// An unsigned literal above `i128::MAX` (`Constant::U128`).
    ULit(u128),
    /// Increment 3 (depth-2 widening, honest scope — casts EXCLUDED, measured
    /// 2026-09-01: the bridge renders a cast operand as a `Var` over the
    /// cast-result MIR temp, so cast byte-parity would require the pinned
    /// forbidden `_N` guess): the VALUE result of a CHECKED `Add`/`Sub`/`Mul`
    /// whose own operands are depth-1-resolvable. The checked trio is the
    /// exact envelope on BOTH carriers, structurally: the capture chases only
    /// `Inst::Overflow` (which exists only for checked add/sub/mul), and its
    /// MIR materialization is a `CheckedBinaryOp` tuple whose value is read
    /// through a `Field(0)` projection — a place the bridge's
    /// `safety_place_var_name` structurally refuses, so a minted nested row
    /// can never meet a bridge formula it silently mismatches. A PLAIN unnamed
    /// binop temp (div/rem/shift results, wrapping ops) is deliberately NOT
    /// admitted: the bridge spells those `Var("_N")`, the pinned
    /// vocabulary-divergence band (`unnamed-temp-operand`).
    ///
    /// `width`/`signed` are the checked operation's OWN integer type, checked
    /// against the outer operation's by the shared mint
    /// (`nested-operand-width-mismatch` on disagreement). Leaves are
    /// `Named`/`Lit`/`ULit` only — one nesting level; a `Nested` leaf declines
    /// at the mint (`nested-operand-depth-cap`).
    Nested {
        op: NestedBinOp,
        width: u32,
        signed: bool,
        lhs: Box<DirectFormulaOperand>,
        rhs: Box<DirectFormulaOperand>,
    },
}

/// The checked-trio discriminator for [`DirectFormulaOperand::Nested`] —
/// exactly the ops `Inst::Overflow` (capture carrier) and a MIR
/// `CheckedBinaryOp` (model carrier) can hold.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NestedBinOp {
    Add,
    Sub,
    Mul,
}

/// Which of the six direct assert classes the formula is about. Mirrors the
/// six `record_direct_assert` sites in `trust-thir-lower` one-to-one.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DirectFormulaClass {
    /// Site B, `Overflow(Add|Sub)`: the scalar out-of-range overflow core
    /// (BV sign-test arm auto-delegated for signed >= 128).
    OverflowAddSub { op: AddSubOp },
    /// Site B, `Overflow(Mul)`: the bare fixed-width BV mul overflow check.
    OverflowMul,
    /// Site C, `DivisionByZero`: `divisor == 0`.
    DivByZero,
    /// Site C, `RemainderByZero`: `divisor == 0` (same core, distinct class).
    RemByZero,
    /// Site D, `Overflow(Div|Rem)`: the signed `INT_MIN / -1` point condition.
    DivRemMinOverflow,
    /// Site E, `Overflow(Shl|Shr)`: shift-amount-in-range violation. The
    /// amount's OWN integer type drives the range conjunct; `value_bits` is
    /// the SHIFTED value's width (`amount >= value_bits` is the violation).
    ShiftInRange { amount_width: u32, amount_signed: bool, value_bits: u32 },
    /// Site F, `BoundsCheck`: dynamic index against a COMPILE-TIME array
    /// length (site F's only covered shape; the length is a `u64` constant).
    BoundsCheck { len: u64 },
    /// Site A, `OverflowNeg`: BV `x == INT_MIN` for signed >= 128 only;
    /// class-wide decline below (see module docs).
    OverflowNeg,
}

/// Add/Sub discriminator for [`DirectFormulaClass::OverflowAddSub`] — carried
/// because `Formula::Add` and `Formula::Sub` are distinct constructors.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AddSubOp {
    Add,
    Sub,
}

/// A successfully minted formula with its two derivatives, rendered ONCE at
/// mint (the same `serde_json::to_string` + `to_smtlib` calls
/// `safety_into_formula` makes) and never recomputed downstream.
#[derive(Debug, Clone, PartialEq)]
pub struct MintedDirectFormula {
    /// The L0 VIOLATION formula, vcgen polarity (SAT iff a violating input
    /// exists) — the flip's comparison object.
    pub formula: Formula,
    /// `serde_json::to_string(&formula)`, minted once.
    pub formula_json: String,
    /// `formula.to_smtlib()`, minted once.
    pub smtlib: String,
}

/// Why the mint declined. Every variant carries the fix, with options
/// (v7/D3: "a refusal must carry the fix").
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FormulaDecline {
    /// The operation's integer width is not a concrete `1..=128` — the
    /// generic-body tripwire (`Ty::Unit`-mapped params, width 0).
    NonConcreteWidth,
    /// `Ty::Char` is `is_int` for the direct lowering but has no measured
    /// MIR-lane formula counterpart; minting one would be unvalidated.
    UnsupportedCharWidth,
    /// An operand is neither a named parameter nor a literal — outside the
    /// production knowledge rule (`value_names` is params-only).
    OpaqueOperand,
    /// `overflow_neg` below signed-128: the MIR lane's core formula is a bare
    /// bool var over an unnamed MIR temp; no operand-level parity object
    /// exists (measured, `lower.rs` OverflowNeg arm).
    MirCoreIsTempCondVar,
    /// The minted output would contain a fallback-shaped (`_N`) variable —
    /// a MIR-local-index guess this lane must never make.
    FallbackShapedVarWouldGuessMirIndex,
    /// The minted output would contain a source name that collides with the
    /// generated-formula namespace (`source_contract_synthetic_name_collision`
    /// — `result`, `_N`-reserved, `__`-family, `old_*`). The MIR lane's
    /// `collision_safe_local_name` refuses exactly these names and falls back
    /// to `_<index>`, so minting one here would be a guaranteed vocabulary
    /// mismatch — and for a PARAM it was increment 1's latent hazard: the
    /// params-only ledger would have kept the name. Added to the post-mint
    /// sweep in increment 2, battery-pinned.
    SyntheticNameCollision,
    /// Increment 3: a nested (depth-2) operand's OWN integer type disagrees
    /// with the checked operation's. Unreachable from well-typed Rust (the
    /// only width-changing step between a checked intermediate and its
    /// consumer is a cast, and casts are outside the honest scope), but the
    /// guard is shared mint code for BOTH carriers, so a carrier desync or a
    /// hand-built operand fails closed here instead of minting a
    /// wrong-width formula. Mutation-pinned.
    NestedOperandWidthMismatch { outer: (u32, bool), inner: (u32, bool) },
    /// The delegated builder returned `None`: the synthesized operands are
    /// outside that builder's faithful envelope (e.g. all-literal operands,
    /// constant divisor, signed mul above 64 bits) — or, increment 3, a
    /// NESTED operand met a rendering stage that cannot carry a composed
    /// term (the BV builders' name-keyed fresh-var encoding, the depth cap,
    /// the placeholder-substitution machinery).
    OutsideBuilderEnvelope { builder: &'static str },
    /// The class/operand arity contract was violated by the caller.
    WrongOperandCount { expected: usize, got: usize },
    /// `serde_json` failed to render the formula (theoretical).
    RenderFailed,
}

impl FormulaDecline {
    /// Stable machine-readable reason code — the `&'static str` the
    /// session-state `Withheld { reason }` carries.
    #[must_use]
    pub const fn code(&self) -> &'static str {
        match self {
            Self::NonConcreteWidth => "non-concrete-width",
            Self::UnsupportedCharWidth => "unsupported-char-width",
            Self::OpaqueOperand => "opaque-operand",
            Self::MirCoreIsTempCondVar => "mir-core-is-temp-cond-var",
            Self::FallbackShapedVarWouldGuessMirIndex => {
                "fallback-shaped-var-would-guess-mir-index"
            }
            Self::SyntheticNameCollision => "synthetic-name-collision",
            Self::NestedOperandWidthMismatch { .. } => "nested-operand-width-mismatch",
            Self::OutsideBuilderEnvelope { .. } => "outside-builder-envelope",
            Self::WrongOperandCount { .. } => "wrong-operand-count",
            Self::RenderFailed => "render-failed",
        }
    }

    /// The fix, with options (v7/D3).
    #[must_use]
    pub const fn fix(&self) -> &'static str {
        match self {
            Self::NonConcreteWidth => {
                "instantiate the generic width (verify at a monomorphic call site), or keep \
                 this obligation on the MIR lane where concrete widths exist"
            }
            Self::UnsupportedCharWidth => {
                "model char's restricted scalar range first (safety_rust_type_range_constraint), \
                 or keep char arithmetic on the MIR lane"
            }
            Self::OpaqueOperand => {
                "extend the direct lane's value ledger beyond params (a reviewed widening of \
                 value_names), or accept the enumerated decline — the row itself still ships"
            }
            Self::MirCoreIsTempCondVar => {
                "give the MIR lane's negation VC an operand-level core first (a trust-vcgen \
                 change), or accept the class-wide decline; do NOT mint an equivalent-but-\
                 different formula here — that grades equivalence, not parity"
            }
            Self::FallbackShapedVarWouldGuessMirIndex => {
                "rename the source binding away from the `_<digits>` namespace, or accept the \
                 decline — the mint never fabricates a MIR local index"
            }
            Self::SyntheticNameCollision => {
                "rename the source binding out of the reserved formula namespace (`result`, \
                 `__`-containing, `old_*`), or accept the decline — the MIR lane demotes such \
                 names to `_<index>`, which this mint must never guess"
            }
            Self::NestedOperandWidthMismatch { .. } => {
                "bind the intermediate to its own `let` so both operations share one typed \
                 name, keep the width-changing step (a cast) out of the nested position, or \
                 accept the enumerated decline — the mint never adopts either width by guess"
            }
            Self::OutsideBuilderEnvelope { .. } => {
                "widen the named reconstruct_* builder's envelope in a reviewed change (it is \
                 the shared constructor for BOTH lanes), or accept the enumerated decline"
            }
            Self::WrongOperandCount { .. } => {
                "fix the caller: each DirectFormulaClass documents its operand arity"
            }
            Self::RenderFailed => "report a bug: serde_json failed on a Formula AST",
        }
    }
}

impl std::fmt::Display for FormulaDecline {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}: {}", self.code(), self.fix())
    }
}

/// Exhaustive `trust_ir::Ty -> (width, signed)` for the direct lowering's 13
/// `is_int` variants — NO wildcard over the integer family, so a 14th integer
/// variant fails the build here instead of silently declining. `Isize`/`Usize`
/// are pinned 64-bit (the producer's `map_ty` fails closed on non-64-bit
/// targets, so a captured usize IS 64 bits). `Char` declines: `is_int` admits
/// it at the emission sites, but no measured MIR-lane formula counterpart
/// exists ([`FormulaDecline::UnsupportedCharWidth`]).
pub fn direct_int_width(ty: &trust_ir::Ty) -> Result<(u32, bool), FormulaDecline> {
    use trust_ir::Ty as IrTy;
    match ty {
        IrTy::I8 => Ok((8, true)),
        IrTy::I16 => Ok((16, true)),
        IrTy::I32 => Ok((32, true)),
        IrTy::I64 => Ok((64, true)),
        IrTy::I128 => Ok((128, true)),
        IrTy::U8 => Ok((8, false)),
        IrTy::U16 => Ok((16, false)),
        IrTy::U32 => Ok((32, false)),
        IrTy::U64 => Ok((64, false)),
        IrTy::U128 => Ok((128, false)),
        IrTy::Isize => Ok((64, true)),
        IrTy::Usize => Ok((64, false)),
        IrTy::Char => Err(FormulaDecline::UnsupportedCharWidth),
        _ => Err(FormulaDecline::NonConcreteWidth),
    }
}

/// Increment 3: the reserved name prefix for the placeholder locals
/// [`synthesize_env`] mints for nested operands. Deliberately OUTSIDE every
/// namespace `collision_safe_local_name` demotes (no leading `_`, no `__`
/// family, not `result`/`old_*`), so the delegated builder renders the
/// placeholder verbatim and the substitution can find it; a USER name in this
/// prefix declines pre-mint when a nested operand is present
/// (`require_mintable_name`), and a placeholder that survives substitution is
/// a fail-closed decline, never an output.
///
/// `pub(crate)` since Step 7 vocabulary convergence increment 1: the bridge's
/// checked-pair chase (`lower.rs::resolve_checked_pair_operands`) synthesizes
/// its placeholder locals in the SAME namespace, so the two lanes' bytes match
/// by construction — one prefix, one substitution implementation.
pub(crate) const NESTED_OPERAND_PLACEHOLDER_PREFIX: &str = "trust_direct_nested_operand_";

/// Render one LEAF of a nested operand exactly as `safety_operand_to_formula`
/// renders the equivalent `trust_types` operand: named local -> `Var(name,
/// Int)`, `Lit` -> `Int`, `ULit` -> the same `Uint -> Int` narrowing. A
/// `Nested` leaf is the depth cap — one nesting level is the envelope, and
/// neither carrier's recognizer builds deeper, so this arm is a defensive
/// fail-closed decline for hand-built operands.
fn nested_leaf_formula(op: &DirectFormulaOperand) -> Result<Formula, FormulaDecline> {
    match op {
        DirectFormulaOperand::Named { name } => Ok(Formula::var(name, Sort::Int)),
        DirectFormulaOperand::Lit(n) => Ok(Formula::Int(*n)),
        DirectFormulaOperand::ULit(n) => Ok(match i128::try_from(*n) {
            Ok(n) => Formula::Int(n),
            Err(_) => Formula::UInt(*n),
        }),
        DirectFormulaOperand::Nested { .. } => {
            Err(FormulaDecline::OutsideBuilderEnvelope { builder: "nested-operand-depth-cap" })
        }
    }
}

/// The composed term a nested operand denotes: `op(lhs_leaf, rhs_leaf)` in
/// the scalar Int vocabulary — the checked op's VALUE on its own success
/// path (the intermediate's non-overflow is asserted by its own preceding
/// direct assert, so the Int reading is the machine value).
fn nested_operand_term(
    op: NestedBinOp,
    lhs: &DirectFormulaOperand,
    rhs: &DirectFormulaOperand,
) -> Result<Formula, FormulaDecline> {
    let lhs = Box::new(nested_leaf_formula(lhs)?);
    let rhs = Box::new(nested_leaf_formula(rhs)?);
    Ok(match op {
        NestedBinOp::Add => Formula::Add(lhs, rhs),
        NestedBinOp::Sub => Formula::Sub(lhs, rhs),
        NestedBinOp::Mul => Formula::Mul(lhs, rhs),
    })
}

/// Increment 3 width guard, SHARED mint code for both carriers: every nested
/// operand's own `(width, signed)` must equal the checked operation's (the
/// caller's `width`/`signed` — every caller passes the operand-carrier type).
/// Unreachable from well-typed Rust; mutation-pinned
/// (`nested_operand_mint_unit_pins`).
fn require_nested_widths(
    operands: &[DirectFormulaOperand],
    width: u32,
    signed: bool,
) -> Result<(), FormulaDecline> {
    for op in operands {
        if let DirectFormulaOperand::Nested { width: w, signed: s, .. } = op {
            if (*w, *s) != (width, signed) {
                return Err(FormulaDecline::NestedOperandWidthMismatch {
                    outer: (width, signed),
                    inner: (*w, *s),
                });
            }
        }
    }
    Ok(())
}

/// One recursion step of [`substitute_nested_operands`] over a binary node.
fn substitute_bin(
    ctor: fn(Box<Formula>, Box<Formula>) -> Formula,
    a: Box<Formula>,
    b: Box<Formula>,
    subs: &[(String, Formula)],
) -> Result<Formula, FormulaDecline> {
    Ok(ctor(Box::new(substitute_scalar(*a, subs)?), Box::new(substitute_scalar(*b, subs)?)))
}

/// Replace every placeholder `Var` with its composed nested term. The walk is
/// TOTAL over exactly the scalar vocabulary the Int-path builders emit
/// (Bool/Int/UInt/BitVec literals, Var/SymVar, Not/And/Or/Implies, the six
/// comparisons, Add/Sub/Mul/Div/Rem/Neg); ANY other variant fails closed —
/// if a delegated builder ever grows a new node kind, the nested lane
/// declines instead of silently passing an unsubstituted region through.
/// Shape discipline: this function never CREATES structure — the formula
/// stays the builder's own output with operand POSITIONS replaced, which is
/// what keeps the mint delegation, not recreation.
fn substitute_scalar(f: Formula, subs: &[(String, Formula)]) -> Result<Formula, FormulaDecline> {
    Ok(match f {
        Formula::Var(name, sort) => match subs.iter().find(|(p, _)| *p == name) {
            Some((_, term)) => term.clone(),
            None => Formula::Var(name, sort),
        },
        leaf @ (Formula::Bool(_)
        | Formula::Int(_)
        | Formula::UInt(_)
        | Formula::BitVec { .. }
        | Formula::SymVar(..)) => leaf,
        Formula::Not(inner) => Formula::Not(Box::new(substitute_scalar(*inner, subs)?)),
        Formula::Neg(inner) => Formula::Neg(Box::new(substitute_scalar(*inner, subs)?)),
        Formula::And(items) => Formula::And(
            items.into_iter().map(|i| substitute_scalar(i, subs)).collect::<Result<_, _>>()?,
        ),
        Formula::Or(items) => Formula::Or(
            items.into_iter().map(|i| substitute_scalar(i, subs)).collect::<Result<_, _>>()?,
        ),
        Formula::Implies(a, b) => substitute_bin(Formula::Implies, a, b, subs)?,
        Formula::Eq(a, b) => substitute_bin(Formula::Eq, a, b, subs)?,
        Formula::Lt(a, b) => substitute_bin(Formula::Lt, a, b, subs)?,
        Formula::Le(a, b) => substitute_bin(Formula::Le, a, b, subs)?,
        Formula::Gt(a, b) => substitute_bin(Formula::Gt, a, b, subs)?,
        Formula::Ge(a, b) => substitute_bin(Formula::Ge, a, b, subs)?,
        Formula::Add(a, b) => substitute_bin(Formula::Add, a, b, subs)?,
        Formula::Sub(a, b) => substitute_bin(Formula::Sub, a, b, subs)?,
        Formula::Mul(a, b) => substitute_bin(Formula::Mul, a, b, subs)?,
        Formula::Div(a, b) => substitute_bin(Formula::Div, a, b, subs)?,
        Formula::Rem(a, b) => substitute_bin(Formula::Rem, a, b, subs)?,
        _ => {
            return Err(FormulaDecline::OutsideBuilderEnvelope {
                builder: "nested_operand_substitution",
            });
        }
    })
}

/// Apply the nested-operand substitutions and enforce the fail-closed belt:
/// no placeholder survives into output (a builder path the walk missed, or a
/// name collision that made `collision_safe_local_name` demote the
/// placeholder, declines rather than ships).
///
/// `pub(crate)` since Step 7 vocabulary convergence increment 1: the bridge's
/// checked-pair chase applies THIS function to the builder output it composes
/// over placeholder locals — a single substitution implementation is what
/// makes the two lanes byte-equal by construction rather than by test.
pub(crate) fn substitute_nested_operands(
    formula: Formula,
    subs: &[(String, Formula)],
) -> Result<Formula, FormulaDecline> {
    if subs.is_empty() {
        return Ok(formula);
    }
    let out = substitute_scalar(formula, subs)?;
    let leftover = trust_types::any_formula_node(&out, &mut |node| {
        let name = match node {
            Formula::Var(name, _) => Some(name.as_str()),
            Formula::SymVar(sym, _) => Some(sym.as_str()),
            _ => None,
        };
        name.is_some_and(|n| n.starts_with(NESTED_OPERAND_PLACEHOLDER_PREFIX))
    });
    if leftover {
        return Err(FormulaDecline::OutsideBuilderEnvelope {
            builder: "nested_operand_substitution",
        });
    }
    Ok(out)
}

/// Synthesize the `trust_types` inputs the delegated builders consume: one
/// projection-free NAMED local per distinct parameter name (same name = same
/// local, exactly as one MIR local backs every use of one parameter), typed at
/// the given `(width, signed)`; literals as `ConstValue` constants; nested
/// operands (increment 3) as position-keyed PLACEHOLDER locals plus the
/// `(placeholder, composed term)` substitution the caller applies to the
/// builder's output via [`substitute_nested_operands`].
fn synthesize_env(
    operands: &[DirectFormulaOperand],
    width: u32,
    signed: bool,
) -> Result<(Vec<LocalDecl>, Vec<Operand>, Vec<(String, Formula)>), FormulaDecline> {
    let mut locals: Vec<LocalDecl> = Vec::new();
    let mut out = Vec::with_capacity(operands.len());
    let mut subs: Vec<(String, Formula)> = Vec::new();
    for (position, op) in operands.iter().enumerate() {
        match op {
            DirectFormulaOperand::Named { name } => {
                let index = match locals.iter().find(|d| d.name.as_deref() == Some(name)) {
                    Some(decl) => decl.index,
                    None => {
                        let index = locals.len();
                        locals.push(LocalDecl {
                            index,
                            ty: Ty::Int { width, signed },
                            name: Some(name.clone()),
                        });
                        index
                    }
                };
                out.push(Operand::Copy(Place::local(index)));
            }
            DirectFormulaOperand::Lit(n) => out.push(Operand::Constant(ConstValue::Int(*n))),
            DirectFormulaOperand::ULit(n) => {
                out.push(Operand::Constant(ConstValue::Uint(*n, width)));
            }
            DirectFormulaOperand::Nested { op, lhs, rhs, .. } => {
                // Position-keyed so two nested operands (the MIN/-1 pair over
                // `(a+b) / (a-b)`) get distinct placeholders. The width guard
                // (`require_nested_widths`) already ran, so the outer
                // `(width, signed)` IS the nested op's own type.
                let name = format!("{NESTED_OPERAND_PLACEHOLDER_PREFIX}{position}");
                let term = nested_operand_term(*op, lhs, rhs)?;
                let index = locals.len();
                locals.push(LocalDecl {
                    index,
                    ty: Ty::Int { width, signed },
                    name: Some(name.clone()),
                });
                out.push(Operand::Copy(Place::local(index)));
                subs.push((name, term));
            }
        }
    }
    Ok((locals, out, subs))
}

fn require_operands(
    operands: &[DirectFormulaOperand],
    expected: usize,
) -> Result<(), FormulaDecline> {
    if operands.len() == expected {
        Ok(())
    } else {
        Err(FormulaDecline::WrongOperandCount { expected, got: operands.len() })
    }
}

const fn require_concrete(width: u32) -> Result<(), FormulaDecline> {
    if width == 0 || width > 128 { Err(FormulaDecline::NonConcreteWidth) } else { Ok(()) }
}

/// Pre-mint operand-name guard (increment 2): a `Named` operand colliding
/// with the generated-formula namespace declines HERE, with the precise
/// reason and fix — the builders would otherwise demote it to a synthesized
/// `_<index>` (their `collision_safe_local_name` refuses such names), and the
/// post-mint sweep would then report the misleading fallback-shape reason.
/// Fallback-shaped names themselves (`_<digits>`, which the synthetic
/// vocabulary also reserves as `PositionalPlace`) are deliberately EXCLUDED:
/// they keep the sweep's pinned `fallback-shaped-var-would-guess-mir-index`
/// decline. This also closes increment 1's latent param hazard — a param
/// named `result`/`old_*`/`x__y` now declines instead of minting a formula
/// the MIR lane spells differently.
fn require_mintable_names(operands: &[DirectFormulaOperand]) -> Result<(), FormulaDecline> {
    // Increment 3: the placeholder-namespace guard applies only when a nested
    // operand is actually in play — without one, nothing is synthesized in
    // that prefix and a user name there stays mintable (increment-1 behavior
    // preserved, pinned by `nested_operand_mint_unit_pins`).
    let has_nested = operands.iter().any(|op| matches!(op, DirectFormulaOperand::Nested { .. }));
    for op in operands {
        require_mintable_name(op, has_nested)?;
    }
    Ok(())
}

/// One operand's name discipline, recursing into nested leaves (increment 3):
/// a synthetic-colliding name ANYWHERE in the composed term would make the
/// bridge's `collision_safe_local_name` demote it, so the same pre-mint
/// decline applies at every depth.
fn require_mintable_name(
    op: &DirectFormulaOperand,
    guard_placeholder_namespace: bool,
) -> Result<(), FormulaDecline> {
    match op {
        DirectFormulaOperand::Named { name } => {
            if !fallback_shaped(name)
                && trust_types::source_contract_synthetic_name_collision(name).is_some()
            {
                return Err(FormulaDecline::SyntheticNameCollision);
            }
            if guard_placeholder_namespace && name.starts_with(NESTED_OPERAND_PLACEHOLDER_PREFIX) {
                // A user name inside the reserved placeholder prefix would
                // alias a synthesized local (the builder would then demote
                // BOTH to `_<index>` and the substitution would miss) —
                // fail closed, never guess.
                return Err(FormulaDecline::OutsideBuilderEnvelope {
                    builder: "nested_operand_placeholder",
                });
            }
            Ok(())
        }
        DirectFormulaOperand::Nested { lhs, rhs, .. } => {
            require_mintable_name(lhs, guard_placeholder_namespace)?;
            require_mintable_name(rhs, guard_placeholder_namespace)
        }
        DirectFormulaOperand::Lit(_) | DirectFormulaOperand::ULit(_) => Ok(()),
    }
}

/// `_<digits>` — the MIR lane's collision fallback namespace. A var of this
/// shape in mint output would be a guessed MIR local index.
fn fallback_shaped(name: &str) -> bool {
    name.strip_prefix('_')
        .is_some_and(|digits| !digits.is_empty() && digits.bytes().all(|b| b.is_ascii_digit()))
}

/// Post-mint fail-closed sweep: refuse any output var that is fallback-shaped,
/// either bare (`_3`) or as the base of a fresh BV operand var
/// (`__trust_ovf_bv_lhs__3`) — and (increment 2) any BASE name colliding with
/// the generated-formula namespace (`source_contract_synthetic_name_collision`),
/// which the MIR lane's `collision_safe_local_name` demotes to `_<index>`.
/// Fallback shape takes precedence when a name trips both (a `_1` param is
/// pinned as the guessed-index decline). The synthetic check runs on the BASE
/// only: the BV fresh-var PREFIX itself lives in the `__` family by design.
fn sweep_no_guessed_mir_index(formula: &Formula) -> Result<(), FormulaDecline> {
    let mut guessed = false;
    let mut synthetic = false;
    let _ = trust_types::all_formula_nodes(formula, &mut |node| {
        let name = match node {
            Formula::Var(name, _) => Some(name.as_str()),
            Formula::SymVar(sym, _) => Some(sym.as_str()),
            _ => None,
        };
        if let Some(name) = name {
            let base = ["lhs", "rhs", "neg"].into_iter().find_map(|role| {
                name.strip_prefix("__trust_ovf_bv_")
                    .and_then(|rest| rest.strip_prefix(role))
                    .and_then(|rest| rest.strip_prefix('_'))
            });
            let base = base.unwrap_or(name);
            if fallback_shaped(base) {
                guessed = true;
                return false;
            }
            if !synthetic {
                synthetic = trust_types::source_contract_synthetic_name_collision(base).is_some();
            }
        }
        true
    });
    if guessed {
        Err(FormulaDecline::FallbackShapedVarWouldGuessMirIndex)
    } else if synthetic {
        Err(FormulaDecline::SyntheticNameCollision)
    } else {
        Ok(())
    }
}

/// Mint the typed L0 safety VIOLATION formula for one direct assert class.
///
/// `width`/`signed` are the checked operation's integer type (for
/// [`DirectFormulaClass::ShiftInRange`] the class carries the amount's own
/// type and `width`/`signed` are ignored in favour of it; for
/// [`DirectFormulaClass::BoundsCheck`] pass the index carrier `(64, false)`).
///
/// Minted ONCE per record at emission; the caller stores the outcome in
/// session state and NOTHING downstream recomputes it.
pub fn mint_direct_safety_formula(
    class: &DirectFormulaClass,
    width: u32,
    signed: bool,
    operands: &[DirectFormulaOperand],
) -> Result<MintedDirectFormula, FormulaDecline> {
    require_mintable_names(operands)?;
    // Increment 3: every caller passes the operand-carrier type as
    // `width`/`signed` (for ShiftInRange that is the AMOUNT's own type,
    // exactly what the class fields repeat), so one shared guard covers all
    // seven classes.
    require_nested_widths(operands, width, signed)?;
    let has_nested = operands.iter().any(|op| matches!(op, DirectFormulaOperand::Nested { .. }));
    let formula = match class {
        DirectFormulaClass::OverflowAddSub { op } => {
            require_operands(operands, 2)?;
            require_concrete(width)?;
            if has_nested && signed && width >= 128 {
                // The signed >= 128 arm auto-delegates to the BV builder,
                // whose operand encoding is a NAME-KEYED fresh var
                // (`__trust_ovf_bv_{role}_{base}`) — a composed term has no
                // base name, and fabricating one is the pinned guessed-index
                // hazard. Decline before the builder can render it.
                return Err(FormulaDecline::OutsideBuilderEnvelope {
                    builder: "reconstruct_bv_signed_addsub_overflow_body",
                });
            }
            let (locals, ops, subs) = synthesize_env(operands, width, signed)?;
            let bin = match op {
                AddSubOp::Add => BinOp::Add,
                AddSubOp::Sub => BinOp::Sub,
            };
            let built = reconstruct_overflow_body(&locals, bin, &ops[0], &ops[1]).ok_or(
                FormulaDecline::OutsideBuilderEnvelope { builder: "reconstruct_overflow_body" },
            )?;
            substitute_nested_operands(built, &subs)?
        }
        DirectFormulaClass::OverflowMul => {
            require_operands(operands, 2)?;
            require_concrete(width)?;
            if has_nested {
                // Mul is BV-encoded at every width — same name-keyed fresh-var
                // encoding, same structural decline as the signed >= 128 arm.
                return Err(FormulaDecline::OutsideBuilderEnvelope {
                    builder: "reconstruct_bv_mul_overflow_body",
                });
            }
            let (locals, ops, _subs) = synthesize_env(operands, width, signed)?;
            reconstruct_bv_mul_overflow_body(&locals, &ops[0], &ops[1]).ok_or(
                FormulaDecline::OutsideBuilderEnvelope {
                    builder: "reconstruct_bv_mul_overflow_body",
                },
            )?
        }
        DirectFormulaClass::DivByZero | DirectFormulaClass::RemByZero => {
            require_operands(operands, 1)?;
            require_concrete(width)?;
            let (locals, ops, subs) = synthesize_env(operands, width, signed)?;
            let built = reconstruct_divisor_is_zero(&locals, &ops[0]).ok_or(
                FormulaDecline::OutsideBuilderEnvelope { builder: "reconstruct_divisor_is_zero" },
            )?;
            substitute_nested_operands(built, &subs)?
        }
        DirectFormulaClass::DivRemMinOverflow => {
            require_operands(operands, 2)?;
            require_concrete(width)?;
            let (locals, ops, subs) = synthesize_env(operands, width, signed)?;
            let built = reconstruct_signed_div_overflow_body(&locals, &ops[0], &ops[1]).ok_or(
                FormulaDecline::OutsideBuilderEnvelope {
                    builder: "reconstruct_signed_div_overflow_body",
                },
            )?;
            substitute_nested_operands(built, &subs)?
        }
        DirectFormulaClass::ShiftInRange { amount_width, amount_signed, value_bits } => {
            require_operands(operands, 1)?;
            require_concrete(*amount_width)?;
            require_concrete(*value_bits)?;
            let (locals, ops, subs) = synthesize_env(operands, *amount_width, *amount_signed)?;
            let amount_f = safety_operand_to_formula(&locals, &ops[0]).ok_or(
                FormulaDecline::OutsideBuilderEnvelope { builder: "safety_operand_to_formula" },
            )?;
            substitute_nested_operands(
                shift_violation_from_parts(&amount_f, *amount_width, *amount_signed, *value_bits),
                &subs,
            )?
        }
        DirectFormulaClass::BoundsCheck { len } => {
            require_operands(operands, 1)?;
            require_concrete(width)?;
            let (locals, ops, subs) = synthesize_env(operands, width, signed)?;
            let idx_f = safety_operand_to_formula(&locals, &ops[0]).ok_or(
                FormulaDecline::OutsideBuilderEnvelope { builder: "safety_operand_to_formula" },
            )?;
            let len_f = match i128::try_from(*len) {
                Ok(n) => Formula::Int(n),
                Err(_) => return Err(FormulaDecline::NonConcreteWidth),
            };
            substitute_nested_operands(bounds_violation_from_parts(idx_f, len_f, signed), &subs)?
        }
        DirectFormulaClass::OverflowNeg => {
            require_operands(operands, 1)?;
            require_concrete(width)?;
            if !(signed && width >= 128) {
                // Class-wide decline below signed-128: see module docs.
                return Err(FormulaDecline::MirCoreIsTempCondVar);
            }
            if has_nested {
                // BV name-keyed operand encoding — same structural decline.
                return Err(FormulaDecline::OutsideBuilderEnvelope {
                    builder: "reconstruct_bv_signed_neg_overflow_body",
                });
            }
            let (locals, ops, _subs) = synthesize_env(operands, width, signed)?;
            reconstruct_bv_signed_neg_overflow_body(&locals, &ops[0], width).ok_or(
                FormulaDecline::OutsideBuilderEnvelope {
                    builder: "reconstruct_bv_signed_neg_overflow_body",
                },
            )?
        }
    };
    sweep_no_guessed_mir_index(&formula)?;
    let formula_json = serde_json::to_string(&formula).map_err(|_| FormulaDecline::RenderFailed)?;
    let smtlib = formula.to_smtlib();
    Ok(MintedDirectFormula { formula, formula_json, smtlib })
}

// ======================= the Step-6 parity oracle ===========================

/// The byte-or-decline parity oracle: for every `Terminator::Assert` in the
/// checked-in MIR corpus whose message is one of the six direct classes, run
/// BOTH lanes — the bridge's own `reconstruct_assert_safety_predicate` (the
/// MIR side, operands recovered by block search) and this module's mint over a
/// stated MODEL of the direct capture (params + literals, the production
/// knowledge rule) — and grade byte-equality of the violation `Formula` AST.
///
/// VALIDATION HONESTY (disclosed limit of this increment's number): the
/// direct-lane side here is a MODEL of `trust-thir-lower`'s capture, because
/// that crate is rustc_private and its units are not runnable in this
/// workflow. Closing the model-vs-real gap is the first deferred item
/// (the env-gated installer dump).
#[cfg(test)]
mod parity_oracle {
    use trust_types::{
        AssertMessage, BasicBlock, BinOp, BlockId, ConstValue, Formula, LocalDecl, Operand, Place,
        Projection, Rvalue, Sort, SourceSpan, Statement, Terminator, Ty, UnOp, UnwindEdge,
        VerifiableBody, VerifiableFunction,
    };

    use super::{
        AddSubOp, DirectFormulaClass, DirectFormulaOperand, FormulaDecline, NestedBinOp,
        mint_direct_safety_formula,
    };
    // Increment 2: the grading core is HOISTED to `direct_record_grading` so
    // the real-record grader and this model oracle share one vocabulary; the
    // 41/41 + per-class-floor pins passing unchanged was the refactor's gate.
    use crate::direct_record_grading::{
        AssertReport, DirectSide, Grade, class_label, grade_pair, load_corpus_dir, print_scorecard,
        tally,
    };
    use crate::lower::{
        SafetyPredicate, find_block_binary_operands, find_block_neg_statement,
        find_condition_binary_operands, find_divrem_on_assert_target_chain, neg_operand_int_ty,
        reconstruct_assert_safety_predicate, safety_int_op_type, safety_operand_int_ty,
        safety_operand_int_ty_or_const,
    };

    /// The model's answer for one assert: the case the direct capture would
    /// hold, or why no comparable case exists.
    enum ModelSide {
        Case {
            class: DirectFormulaClass,
            width: u32,
            signed: bool,
            operands: Vec<DirectFormulaOperand>,
            shadowed: bool,
        },
        /// An operand is outside the capture's knowledge rule — the capture
        /// mints `Withheld` under the carried enumerated reason (increment 2
        /// widened this from the single `opaque-operand` code).
        Withheld(&'static str),
        Excluded(&'static str),
    }

    /// All projection-free whole-local assignments to `local` across the
    /// body — the model's carrier for the one-level alias mirror.
    fn defs_of<'f>(func: &'f VerifiableFunction, local: usize) -> Vec<&'f Rvalue> {
        let mut out = Vec::new();
        for block in &func.body.blocks {
            for stmt in &block.stmts {
                if let Statement::Assign { place, rvalue, .. } = stmt {
                    if place.local == local && place.projections.is_empty() {
                        out.push(rvalue);
                    }
                }
            }
        }
        out
    }

    /// Model one MIR operand under the capture's knowledge rule.
    /// `Ok((operand, shadowed))` or `Err(reason)` with the SAME enumerated
    /// code the capture would withhold under.
    ///
    /// Increment 2 (named-value resolution — the widening's model mirror):
    /// * a NAMED PARAM keeps increment 1's fast path verbatim — the capture's
    ///   `value_names` ledger answers before the widened resolver, so a
    ///   shadowed param stays the pinned KnownMismatch class, never a
    ///   decline;
    /// * a NAMED NON-PARAM local resolves iff its name is unique among the
    ///   body's named locals (the census mirror; `collision_safe_local_name`
    ///   keeps the source name under exactly this condition) and the value is
    ///   not a one-level ALIAS of another binding (a single plain-copy def of
    ///   a named local: the capture's ledger then knows the value under TWO
    ///   names and cannot know which spelling MIR uses). Fallback-shaped and
    ///   synthetic-colliding names flow through to the SHARED mint
    ///   guard/sweep, same as the capture;
    /// * an UNNAMED local is the `_N` vocabulary-divergence band —
    ///   `unnamed-temp-operand`;
    /// * everything else (projections, symbolic, exotic constants) stays
    ///   `opaque-operand`.
    ///
    /// The two carriers cannot literally share code (trust_ir open-block/THIR
    /// vs trust_types MIR); this per-predicate mirror is documented against
    /// `direct_operand_widening.rs` side-by-side, and `grade_real_records`
    /// over the production dump is the EXECUTABLE equivalence check.
    fn convert_operand(
        func: &VerifiableFunction,
        op: &Operand,
    ) -> Result<(DirectFormulaOperand, bool), &'static str> {
        convert_operand_at(func, op, true)
    }

    /// The depth-carrying body of [`convert_operand`]. `allow_nested` is true
    /// at the top level only — nested leaves resolve depth-1 (the envelope is
    /// ONE nesting level, on both carriers).
    fn convert_operand_at(
        func: &VerifiableFunction,
        op: &Operand,
        allow_nested: bool,
    ) -> Result<(DirectFormulaOperand, bool), &'static str> {
        let locals = &func.body.locals;
        let arg_count = func.body.arg_count;
        match op {
            Operand::Constant(ConstValue::Int(n)) => Ok((DirectFormulaOperand::Lit(*n), false)),
            Operand::Constant(ConstValue::Uint(n, _)) => {
                Ok((DirectFormulaOperand::ULit(*n), false))
            }
            // Increment 3 (depth-2, checked trio only): the VALUE read of a
            // checked binop tuple — `_N.0` — mirrors the capture's chase of
            // the defining `Inst::Overflow`. Guarded to exactly the Field(0)
            // single-projection shape; every other projection stays outside
            // the knowledge rule below.
            Operand::Copy(place) | Operand::Move(place)
                if allow_nested && place.projections == [Projection::Field(0)] =>
            {
                convert_nested_checked(func, place.local)
            }
            Operand::Copy(place) | Operand::Move(place) if place.projections.is_empty() => {
                let decl =
                    locals.iter().find(|d| d.index == place.local).ok_or("opaque-operand")?;
                let is_param = (1..=arg_count).contains(&place.local);
                match (&decl.name, is_param) {
                    (Some(name), true) => {
                        let shadowed = locals
                            .iter()
                            .filter(|d| d.name.as_deref() == Some(name.as_str()))
                            .count()
                            > 1;
                        Ok((DirectFormulaOperand::Named { name: name.clone() }, shadowed))
                    }
                    (Some(name), false) => {
                        if locals
                            .iter()
                            .filter(|d| d.name.as_deref() == Some(name.as_str()))
                            .count()
                            > 1
                        {
                            return Err("shadowed-operand-name");
                        }
                        if let [Rvalue::Use(Operand::Copy(src) | Operand::Move(src))] =
                            defs_of(func, place.local).as_slice()
                        {
                            if src.projections.is_empty()
                                && locals.iter().any(|d| d.index == src.local && d.name.is_some())
                            {
                                return Err("ambiguous-operand-name");
                            }
                        }
                        Ok((DirectFormulaOperand::Named { name: name.clone() }, false))
                    }
                    (None, _) => Err("unnamed-temp-operand"),
                }
            }
            _ => Err("opaque-operand"),
        }
    }

    fn convert_pair(
        func: &VerifiableFunction,
        a: &Operand,
        b: &Operand,
    ) -> Result<(Vec<DirectFormulaOperand>, bool), &'static str> {
        let (ca, sa) = convert_operand(func, a)?;
        let (cb, sb) = convert_operand(func, b)?;
        Ok((vec![ca, cb], sa || sb))
    }

    /// Increment 3 model mirror of the capture's `nested_checked_operand`
    /// (`trust-thir-lower/src/direct_operand_widening.rs`): the local behind a
    /// `_N.0` read resolves to a [`DirectFormulaOperand::Nested`] iff its MIR
    /// type is the checked pair `(Int, bool)` (the capture reads the SAME type
    /// off `Inst::Overflow.ty`), its ONE whole-local def is a
    /// `CheckedBinaryOp` of the checked trio (the capture's `Inst::Overflow`
    /// exists only for exactly those), and both leaves resolve at depth 1.
    /// Every failure keeps the outer operand's own truth — it IS an unnamed
    /// temp — mirroring the capture's fallback reason verbatim.
    fn convert_nested_checked(
        func: &VerifiableFunction,
        local: usize,
    ) -> Result<(DirectFormulaOperand, bool), &'static str> {
        let decl =
            func.body.locals.iter().find(|d| d.index == local).ok_or("unnamed-temp-operand")?;
        let Ty::Tuple(elems) = &decl.ty else { return Err("unnamed-temp-operand") };
        let [value_ty, Ty::Bool] = elems.as_slice() else {
            return Err("unnamed-temp-operand");
        };
        let Some(width) = value_ty.int_width() else { return Err("unnamed-temp-operand") };
        let signed = value_ty.is_signed();
        let defs = defs_of(func, local);
        let [Rvalue::CheckedBinaryOp(op, a, b)] = defs.as_slice() else {
            return Err("unnamed-temp-operand");
        };
        let op = match op {
            BinOp::Add => NestedBinOp::Add,
            BinOp::Sub => NestedBinOp::Sub,
            BinOp::Mul => NestedBinOp::Mul,
            _ => return Err("unnamed-temp-operand"),
        };
        let (lhs, shadowed_l) =
            convert_operand_at(func, a, false).map_err(|_| "unnamed-temp-operand")?;
        let (rhs, shadowed_r) =
            convert_operand_at(func, b, false).map_err(|_| "unnamed-temp-operand")?;
        Ok((
            DirectFormulaOperand::Nested {
                op,
                width,
                signed,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            },
            shadowed_l || shadowed_r,
        ))
    }

    /// Increment 3: `(width, signed)` of an operand, seeing THROUGH the
    /// checked-pair `Field(0)` read (the model's mirror of the capture
    /// reading the op's own THIR type, which does not depend on operand
    /// shape). Falls back to the projection-free rule first, so every
    /// pre-existing row is untouched.
    fn deep_operand_int_ty(func: &VerifiableFunction, op: &Operand) -> Option<(u32, bool)> {
        if let Some(ws) = safety_operand_int_ty(&func.body.locals, op) {
            return Some(ws);
        }
        let place = match op {
            Operand::Copy(p) | Operand::Move(p) => p,
            _ => return None,
        };
        if place.projections != [Projection::Field(0)] {
            return None;
        }
        let decl = func.body.locals.iter().find(|d| d.index == place.local)?;
        let Ty::Tuple(elems) = &decl.ty else { return None };
        match elems.as_slice() {
            [value_ty, Ty::Bool] => Some((value_ty.int_width()?, value_ty.is_signed())),
            _ => None,
        }
    }

    /// Increment 3: `safety_int_op_type`'s agreement rule over the DEEP
    /// per-operand type — both operands must agree, or one is a literal that
    /// adopts the other's type. Used as the fallback when the projection-free
    /// rule declines, so pre-existing width recoveries are byte-untouched.
    fn deep_int_op_type(
        func: &VerifiableFunction,
        lhs: &Operand,
        rhs: &Operand,
    ) -> Option<(u32, bool)> {
        match (deep_operand_int_ty(func, lhs), deep_operand_int_ty(func, rhs)) {
            (Some(l), Some(r)) => (l == r).then_some(l),
            (Some(l), None) if matches!(rhs, Operand::Constant(_)) => Some(l),
            (None, Some(r)) if matches!(lhs, Operand::Constant(_)) => Some(r),
            _ => None,
        }
    }

    /// Build the model case for one assert. Returns `None` when the message
    /// is not one of the six direct classes (skipped entirely).
    fn model_direct_case(func: &VerifiableFunction, block: &BasicBlock) -> Option<ModelSide> {
        let Terminator::Assert { cond, msg, target, .. } = &block.terminator else {
            return None;
        };
        let body = &func.body;
        let locals = &body.locals;
        let block_by_id = |id: BlockId| body.blocks.iter().find(|b| b.id == id);
        let search = |op: BinOp| {
            find_block_binary_operands(block, op)
                .or_else(|| block_by_id(*target).and_then(|b| find_block_binary_operands(b, op)))
        };
        Some(match msg {
            AssertMessage::Overflow(op @ (BinOp::Add | BinOp::Sub | BinOp::Mul)) => {
                let Some((lhs, rhs)) = search(*op) else {
                    return Some(ModelSide::Excluded("no-binop-found"));
                };
                // Increment 3: fall back to the DEEP type read for nested
                // (checked-pair Field(0)) operands — the capture reads the
                // op's own THIR type, which no operand shape can hide.
                let (width, signed) = safety_int_op_type(locals, lhs, rhs)
                    .or_else(|| deep_int_op_type(func, lhs, rhs))
                    .unwrap_or((0, false));
                let (operands, shadowed) = match convert_pair(func, lhs, rhs) {
                    Ok(converted) => converted,
                    Err(reason) => return Some(ModelSide::Withheld(reason)),
                };
                let class = match op {
                    BinOp::Add => DirectFormulaClass::OverflowAddSub { op: AddSubOp::Add },
                    BinOp::Sub => DirectFormulaClass::OverflowAddSub { op: AddSubOp::Sub },
                    _ => DirectFormulaClass::OverflowMul,
                };
                ModelSide::Case { class, width, signed, operands, shadowed }
            }
            AssertMessage::Overflow(op @ (BinOp::Div | BinOp::Rem)) => {
                let Some((lhs, rhs)) = search(*op) else {
                    return Some(ModelSide::Excluded("no-binop-found"));
                };
                let (width, signed) = safety_int_op_type(locals, lhs, rhs)
                    .or_else(|| deep_int_op_type(func, lhs, rhs))
                    .unwrap_or((0, false));
                let (operands, shadowed) = match convert_pair(func, lhs, rhs) {
                    Ok(converted) => converted,
                    Err(reason) => return Some(ModelSide::Withheld(reason)),
                };
                ModelSide::Case {
                    class: DirectFormulaClass::DivRemMinOverflow,
                    width,
                    signed,
                    operands,
                    shadowed,
                }
            }
            AssertMessage::Overflow(op @ (BinOp::Shl | BinOp::Shr)) => {
                let Some((value, amount)) = search(*op) else {
                    return Some(ModelSide::Excluded("no-shift-op-found"));
                };
                let value_bits = safety_operand_int_ty(locals, value)
                    .or_else(|| deep_operand_int_ty(func, value))
                    .map_or(0, |(w, _)| w);
                let (amount_width, amount_signed) = safety_operand_int_ty_or_const(locals, amount)
                    .or_else(|| deep_operand_int_ty(func, amount))
                    .unwrap_or((0, false));
                let (converted, shadowed) =
                    match convert_operand(func, amount).map(|(c, s)| (vec![c], s)) {
                        Ok(converted) => converted,
                        Err(reason) => return Some(ModelSide::Withheld(reason)),
                    };
                ModelSide::Case {
                    class: DirectFormulaClass::ShiftInRange {
                        amount_width,
                        amount_signed,
                        value_bits,
                    },
                    width: amount_width,
                    signed: amount_signed,
                    operands: converted,
                    shadowed,
                }
            }
            AssertMessage::DivisionByZero | AssertMessage::RemainderByZero => {
                let want = if matches!(msg, AssertMessage::DivisionByZero) {
                    BinOp::Div
                } else {
                    BinOp::Rem
                };
                // The division runs on the success edge (target), mirroring
                // the bridge's target-then-source order — then BAND B (Step 7
                // convergence): THE SAME bounded target-chain walk the bridge
                // runs (`find_divrem_on_assert_target_chain`, one shared
                // helper, so search drift between model and bridge is
                // structurally impossible).
                let divisor = block_by_id(*target)
                    .and_then(|b| find_block_binary_operands(b, want))
                    .map(|(_, d)| d)
                    .or_else(|| find_block_binary_operands(block, want).map(|(_, d)| d))
                    .or_else(|| find_divrem_on_assert_target_chain(&body.blocks, *target, want));
                let Some(divisor) = divisor else {
                    return Some(ModelSide::Excluded("no-divrem-op-found"));
                };
                let (width, signed) = safety_operand_int_ty_or_const(locals, divisor)
                    .or_else(|| deep_operand_int_ty(func, divisor))
                    .unwrap_or((0, false));
                let (converted, shadowed) =
                    match convert_operand(func, divisor).map(|(c, s)| (vec![c], s)) {
                        Ok(converted) => converted,
                        Err(reason) => return Some(ModelSide::Withheld(reason)),
                    };
                let class = if matches!(msg, AssertMessage::DivisionByZero) {
                    DirectFormulaClass::DivByZero
                } else {
                    DirectFormulaClass::RemByZero
                };
                ModelSide::Case { class, width, signed, operands: converted, shadowed }
            }
            AssertMessage::OverflowNeg => {
                let Some((neg_dest, neg_op)) =
                    block_by_id(*target).and_then(find_block_neg_statement)
                else {
                    return Some(ModelSide::Excluded("no-neg-op-found"));
                };
                // The capture reads the negation's own THIR type; for a width-less
                // literal operand that is the Neg's destination type, never the
                // literal's value-derived width.
                let (width, signed) = if matches!(neg_op, Operand::Constant(ConstValue::Int(_))) {
                    neg_operand_int_ty(locals, neg_dest, neg_op)
                } else {
                    safety_operand_int_ty_or_const(locals, neg_op)
                        .or_else(|| deep_operand_int_ty(func, neg_op))
                }
                .unwrap_or((0, false));
                let (converted, shadowed) =
                    match convert_operand(func, neg_op).map(|(c, s)| (vec![c], s)) {
                        Ok(converted) => converted,
                        Err(reason) => return Some(ModelSide::Withheld(reason)),
                    };
                ModelSide::Case {
                    class: DirectFormulaClass::OverflowNeg,
                    width,
                    signed,
                    operands: converted,
                    shadowed,
                }
            }
            AssertMessage::BoundsCheck => {
                // Site F's envelope: direct-comparison shape, COMPILE-TIME
                // length, usize (unsigned) index. Anything else is a lane
                // exclusion, not a decline: the direct lane mints no row.
                let Some((op, idx, len)) = find_condition_binary_operands(block, cond) else {
                    return Some(ModelSide::Excluded("bounds-abstract-flag"));
                };
                if op != BinOp::Lt {
                    return Some(ModelSide::Excluded("bounds-non-lt-condition"));
                }
                let len = match len {
                    Operand::Constant(ConstValue::Int(n)) => u64::try_from(*n).ok(),
                    Operand::Constant(ConstValue::Uint(n, _)) => u64::try_from(*n).ok(),
                    _ => None,
                };
                let Some(len) = len else {
                    return Some(ModelSide::Excluded("bounds-non-constant-len"));
                };
                if let Some((_, true)) =
                    safety_operand_int_ty(locals, idx).or_else(|| deep_operand_int_ty(func, idx))
                {
                    return Some(ModelSide::Excluded("bounds-signed-index-outside-site-f"));
                }
                let (converted, shadowed) =
                    match convert_operand(func, idx).map(|(c, s)| (vec![c], s)) {
                        Ok(converted) => converted,
                        Err(reason) => return Some(ModelSide::Withheld(reason)),
                    };
                ModelSide::Case {
                    class: DirectFormulaClass::BoundsCheck { len },
                    width: 64,
                    signed: false,
                    operands: converted,
                    shadowed,
                }
            }
            _ => return None,
        })
    }

    /// Grade every six-class assert of one function — through the SHARED
    /// `grade_pair` core (the model side supplies `DirectSide::ModelMinted`).
    fn grade_function(fixture: &str, func: &VerifiableFunction) -> Vec<AssertReport> {
        let mut out = Vec::new();
        for block in &func.body.blocks {
            let Terminator::Assert { cond, msg, target, .. } = &block.terminator else {
                continue;
            };
            let Some(model) = model_direct_case(func, block) else {
                continue; // not one of the six classes
            };
            let bridge = reconstruct_assert_safety_predicate(
                &func.body.locals,
                &func.body.blocks,
                block.id,
                *target,
                cond,
                msg,
            );
            // Every six-class message has a Some() arm in the bridge.
            let bridge = bridge.expect("six-class assert must have a bridge disposition");
            let (grade, detail) = match model {
                ModelSide::Excluded(reason) => (Grade::Excluded(reason), String::new()),
                ModelSide::Withheld(reason) => {
                    grade_pair(&bridge, DirectSide::ModelMinted(Err(reason)), false)
                        .expect("a declined model side cannot be incoherent")
                }
                ModelSide::Case { class, width, signed, operands, shadowed } => {
                    let mint = mint_direct_safety_formula(&class, width, signed, &operands)
                        .map_err(|decline| decline.code());
                    grade_pair(&bridge, DirectSide::ModelMinted(mint), shadowed)
                        .expect("model minted derivatives must be the once-rendered pair")
                }
            };
            out.push(AssertReport {
                fixture: format!("{fixture}::{}", func.name),
                class_label: class_label(msg),
                grade,
                detail,
            });
        }
        out
    }

    fn corpus_dir() -> std::path::PathBuf {
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../trust-vcgen/tests/data")
    }

    fn load_corpus() -> Vec<(String, VerifiableFunction)> {
        load_corpus_dir(&corpus_dir())
    }

    // ---------------- adversarial in-test constructed bodies ----------------

    fn span() -> SourceSpan {
        SourceSpan {
            file: "adv.rs".to_string(),
            line_start: 1,
            col_start: 0,
            line_end: 1,
            col_end: 8,
        }
    }

    fn local(index: usize, width: u32, signed: bool, name: Option<&str>) -> LocalDecl {
        LocalDecl { index, ty: Ty::Int { width, signed }, name: name.map(str::to_string) }
    }

    /// The `(value, overflowed)` pair a MIR `CheckedBinaryOp` materializes —
    /// the increment-3 nested band's carrier (always unnamed in real MIR).
    fn checked_pair_local(index: usize, width: u32, signed: bool) -> LocalDecl {
        LocalDecl { index, ty: Ty::Tuple(vec![Ty::Int { width, signed }, Ty::Bool]), name: None }
    }

    fn assign(dest: usize, rvalue: Rvalue) -> Statement {
        Statement::Assign { place: Place::local(dest), rvalue, span: span() }
    }

    fn assert_block(
        id: usize,
        stmts: Vec<Statement>,
        cond_local: usize,
        msg: AssertMessage,
        target: usize,
    ) -> BasicBlock {
        BasicBlock {
            id: BlockId(id),
            stmts,
            terminator: Terminator::Assert {
                cond: Operand::Copy(Place::local(cond_local)),
                expected: true,
                msg,
                target: BlockId(target),
                span: span(),
                unwind: UnwindEdge::Unreachable,
            },
        }
    }

    fn return_block(id: usize, stmts: Vec<Statement>) -> BasicBlock {
        BasicBlock { id: BlockId(id), stmts, terminator: Terminator::Return }
    }

    fn mk_func(
        name: &str,
        locals: Vec<LocalDecl>,
        blocks: Vec<BasicBlock>,
        arg_count: usize,
    ) -> VerifiableFunction {
        VerifiableFunction {
            name: name.to_string(),
            def_path: format!("adv::{name}"),
            span: span(),
            body: VerifiableBody {
                locals,
                blocks,
                arg_count,
                return_ty: Ty::Unit,
                datatype_defs: Default::default(),
            },
            contracts: Vec::new(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            spec: Default::default(),
            tuple_layouts: Default::default(),
        }
    }

    fn copy(local_index: usize) -> Operand {
        Operand::Copy(Place::local(local_index))
    }

    /// The adversarial battery the design of record names, plus the in-test
    /// positive shapes that guarantee a ByteIdentical floor per class
    /// independent of corpus composition.
    fn adversarial_functions() -> Vec<(&'static str, VerifiableFunction)> {
        vec![
            // 1. shadowed-param body: param `x` shadowed by a same-named
            //    local; the MIR lane must fall back to `_1`, the direct lane
            //    keeps `x` -> pinned known-mismatch class.
            (
                "shadowed_param",
                mk_func(
                    "shadowed_param",
                    vec![
                        local(0, 32, false, None),
                        local(1, 32, false, Some("x")),
                        local(2, 32, false, Some("x")),
                        local(3, 32, false, None),
                    ],
                    vec![
                        assert_block(
                            0,
                            vec![assign(
                                3,
                                Rvalue::CheckedBinaryOp(
                                    BinOp::Add,
                                    copy(1),
                                    Operand::Constant(ConstValue::Uint(1, 32)),
                                ),
                            )],
                            3,
                            AssertMessage::Overflow(BinOp::Add),
                            1,
                        ),
                        return_block(1, vec![]),
                    ],
                    1,
                ),
            ),
            // 2. a param literally named `_1`: the mint's output would carry
            //    the fallback-shaped name -> the sweep declines rather than
            //    guessing a MIR index (even though the guess would be right).
            (
                "param_named_underscore_one",
                mk_func(
                    "param_named_underscore_one",
                    vec![
                        local(0, 32, false, None),
                        local(1, 32, false, Some("_1")),
                        local(2, 32, false, None),
                    ],
                    vec![
                        assert_block(
                            0,
                            vec![assign(
                                2,
                                Rvalue::CheckedBinaryOp(
                                    BinOp::Add,
                                    copy(1),
                                    Operand::Constant(ConstValue::Uint(1, 32)),
                                ),
                            )],
                            2,
                            AssertMessage::Overflow(BinOp::Add),
                            1,
                        ),
                        return_block(1, vec![]),
                    ],
                    1,
                ),
            ),
            // 3. i128 signed negation: the BV subset the mint DOES cover.
            (
                "neg_i128",
                mk_func(
                    "neg_i128",
                    vec![
                        local(0, 128, true, None),
                        local(1, 128, true, Some("x")),
                        local(2, 128, true, None),
                    ],
                    vec![
                        assert_block(0, vec![], 1, AssertMessage::OverflowNeg, 1),
                        return_block(1, vec![assign(2, Rvalue::UnaryOp(UnOp::Neg, copy(1)))]),
                    ],
                    1,
                ),
            ),
            // 4. sub-128 signed negation: class-wide mint decline
            //    (mir-core-is-temp-cond-var), bridge keeps its cond-var core.
            (
                "neg_i32",
                mk_func(
                    "neg_i32",
                    vec![
                        local(0, 32, true, None),
                        local(1, 32, true, Some("x")),
                        local(2, 32, true, None),
                    ],
                    vec![
                        assert_block(0, vec![], 1, AssertMessage::OverflowNeg, 1),
                        return_block(1, vec![assign(2, Rvalue::UnaryOp(UnOp::Neg, copy(1)))]),
                    ],
                    1,
                ),
            ),
            // 5. mixed-width operands: both lanes decline (no such THIR body
            //    exists; the MIR shape is synthetic).
            (
                "mixed_width",
                mk_func(
                    "mixed_width",
                    vec![
                        local(0, 32, false, None),
                        local(1, 32, false, Some("a")),
                        local(2, 64, false, Some("b")),
                        local(3, 32, false, None),
                    ],
                    vec![
                        assert_block(
                            0,
                            vec![assign(3, Rvalue::CheckedBinaryOp(BinOp::Add, copy(1), copy(2)))],
                            3,
                            AssertMessage::Overflow(BinOp::Add),
                            1,
                        ),
                        return_block(1, vec![]),
                    ],
                    2,
                ),
            ),
            // 6. distinct-name Sub over two params: scalar core, byte parity.
            (
                "sub_distinct_names",
                mk_func(
                    "sub_distinct_names",
                    vec![
                        local(0, 32, false, None),
                        local(1, 32, false, Some("a")),
                        local(2, 32, false, Some("b")),
                        local(3, 32, false, None),
                    ],
                    vec![
                        assert_block(
                            0,
                            vec![assign(3, Rvalue::CheckedBinaryOp(BinOp::Sub, copy(1), copy(2)))],
                            3,
                            AssertMessage::Overflow(BinOp::Sub),
                            1,
                        ),
                        return_block(1, vec![]),
                    ],
                    2,
                ),
            ),
            // 7. unsigned mul over two params: the bare BV envelope pin
            //    (the "mul M>0" pin is satisfiable by construction).
            (
                "mul_params_u32",
                mk_func(
                    "mul_params_u32",
                    vec![
                        local(0, 32, false, None),
                        local(1, 32, false, Some("a")),
                        local(2, 32, false, Some("b")),
                        local(3, 32, false, None),
                    ],
                    vec![
                        assert_block(
                            0,
                            vec![assign(3, Rvalue::CheckedBinaryOp(BinOp::Mul, copy(1), copy(2)))],
                            3,
                            AssertMessage::Overflow(BinOp::Mul),
                            1,
                        ),
                        return_block(1, vec![]),
                    ],
                    2,
                ),
            ),
            // 8. div by param divisor: div-zero core + signed MIN/-1 pair.
            (
                "div_i32_params",
                mk_func(
                    "div_i32_params",
                    vec![
                        local(0, 32, true, None),
                        local(1, 32, true, Some("a")),
                        local(2, 32, true, Some("b")),
                        local(3, 32, true, None),
                        local(4, 32, true, None),
                    ],
                    vec![
                        assert_block(0, vec![], 3, AssertMessage::DivisionByZero, 1),
                        assert_block(1, vec![], 4, AssertMessage::Overflow(BinOp::Div), 2),
                        return_block(
                            2,
                            vec![assign(3, Rvalue::BinaryOp(BinOp::Div, copy(1), copy(2)))],
                        ),
                    ],
                    2,
                ),
            ),
            // 8b. UNSIGNED div/rem by a param divisor: the single-assert MIR
            //     shape whose TARGET block holds the op — the shape the
            //     div/rem-zero recovery is built for. (The signed fixture
            //     above mirrors real signed MIR, where the div-zero assert's
            //     target holds the MIN/-1 assert instead of the Div — an
            //     enumerated exclusion there, as in the corpus.)
            (
                "udiv_params",
                mk_func(
                    "udiv_params",
                    vec![
                        local(0, 32, false, None),
                        local(1, 32, false, Some("a")),
                        local(2, 32, false, Some("b")),
                        local(3, 32, false, None),
                    ],
                    vec![
                        assert_block(0, vec![], 3, AssertMessage::DivisionByZero, 1),
                        return_block(
                            1,
                            vec![assign(3, Rvalue::BinaryOp(BinOp::Div, copy(1), copy(2)))],
                        ),
                    ],
                    2,
                ),
            ),
            (
                "urem_params",
                mk_func(
                    "urem_params",
                    vec![
                        local(0, 32, false, None),
                        local(1, 32, false, Some("a")),
                        local(2, 32, false, Some("b")),
                        local(3, 32, false, None),
                    ],
                    vec![
                        assert_block(0, vec![], 3, AssertMessage::RemainderByZero, 1),
                        return_block(
                            1,
                            vec![assign(3, Rvalue::BinaryOp(BinOp::Rem, copy(1), copy(2)))],
                        ),
                    ],
                    2,
                ),
            ),
            // 9. shift by param amount: the extracted shift tail, byte parity.
            (
                "shl_u32_params",
                mk_func(
                    "shl_u32_params",
                    vec![
                        local(0, 32, false, None),
                        local(1, 32, false, Some("x")),
                        local(2, 32, false, Some("s")),
                        local(3, 32, false, None),
                    ],
                    vec![
                        assert_block(
                            0,
                            vec![assign(3, Rvalue::CheckedBinaryOp(BinOp::Shl, copy(1), copy(2)))],
                            3,
                            AssertMessage::Overflow(BinOp::Shl),
                            1,
                        ),
                        return_block(1, vec![]),
                    ],
                    2,
                ),
            ),
            // ---- increment 2: the named-value-resolution widening battery ----
            // 11. nested named resolution: the checked op's operand is a
            //     NAMED-UNIQUE NON-PARAM local (a `let`-bound intermediate /
            //     loop counter — the corpus' countdown band). Both lanes
            //     render Var("i") -> byte parity.
            (
                "nested_named_resolution",
                mk_func(
                    "nested_named_resolution",
                    vec![
                        local(0, 32, false, None),
                        local(1, 32, false, Some("start")),
                        local(2, 32, false, Some("i")),
                        local(3, 32, false, None),
                    ],
                    vec![
                        assert_block(
                            0,
                            vec![assign(
                                3,
                                Rvalue::CheckedBinaryOp(
                                    BinOp::Sub,
                                    copy(2),
                                    Operand::Constant(ConstValue::Uint(1, 32)),
                                ),
                            )],
                            3,
                            AssertMessage::Overflow(BinOp::Sub),
                            1,
                        ),
                        return_block(1, vec![]),
                    ],
                    1,
                ),
            ),
            // 12. alias decline: `let y = x; y + 1` — the operand local's
            //     single def is a plain copy of a NAMED local, so the
            //     capture's ledger knows the value under TWO names and cannot
            //     know which spelling MIR uses.
            (
                "alias_of_param",
                mk_func(
                    "alias_of_param",
                    vec![
                        local(0, 32, false, None),
                        local(1, 32, false, Some("x")),
                        local(2, 32, false, Some("y")),
                        local(3, 32, false, None),
                    ],
                    vec![
                        assert_block(
                            0,
                            vec![
                                assign(2, Rvalue::Use(copy(1))),
                                assign(
                                    3,
                                    Rvalue::CheckedBinaryOp(
                                        BinOp::Add,
                                        copy(2),
                                        Operand::Constant(ConstValue::Uint(1, 32)),
                                    ),
                                ),
                            ],
                            3,
                            AssertMessage::Overflow(BinOp::Add),
                            1,
                        ),
                        return_block(1, vec![]),
                    ],
                    1,
                ),
            ),
            // 13. shadowed LOCAL decline: two non-param locals named `t` —
            //     the census count is 2, the bridge spells `_2`; the widened
            //     resolver declines instead of minting the name.
            (
                "shadowed_local",
                mk_func(
                    "shadowed_local",
                    vec![
                        local(0, 32, false, None),
                        local(1, 32, false, Some("a")),
                        local(2, 32, false, Some("t")),
                        local(3, 32, false, Some("t")),
                        local(4, 32, false, None),
                    ],
                    vec![
                        assert_block(
                            0,
                            vec![assign(
                                4,
                                Rvalue::CheckedBinaryOp(
                                    BinOp::Add,
                                    copy(2),
                                    Operand::Constant(ConstValue::Uint(1, 32)),
                                ),
                            )],
                            4,
                            AssertMessage::Overflow(BinOp::Add),
                            1,
                        ),
                        return_block(1, vec![]),
                    ],
                    1,
                ),
            ),
            // 14. unnamed temp decline: the operand local has NO source name
            //     — the `_N` vocabulary-divergence band, enumerated.
            (
                "unnamed_temp",
                mk_func(
                    "unnamed_temp",
                    vec![
                        local(0, 32, false, None),
                        local(1, 32, false, Some("a")),
                        local(2, 32, false, None),
                        local(3, 32, false, None),
                    ],
                    vec![
                        assert_block(
                            0,
                            vec![assign(
                                3,
                                Rvalue::CheckedBinaryOp(
                                    BinOp::Add,
                                    copy(2),
                                    Operand::Constant(ConstValue::Uint(1, 32)),
                                ),
                            )],
                            3,
                            AssertMessage::Overflow(BinOp::Add),
                            1,
                        ),
                        return_block(1, vec![]),
                    ],
                    1,
                ),
            ),
            // 15. synthetic-collision name decline: a unique local in the
            //     reserved `__` family — the bridge demotes it to `_2`, the
            //     mint's pre-guard declines with the precise reason (the
            //     latent increment-1 param hazard, closed).
            (
                "synthetic_collision_name",
                mk_func(
                    "synthetic_collision_name",
                    vec![
                        local(0, 32, false, None),
                        local(1, 32, false, Some("a")),
                        local(2, 32, false, Some("b__slice_len")),
                        local(3, 32, false, None),
                    ],
                    vec![
                        assert_block(
                            0,
                            vec![assign(
                                3,
                                Rvalue::CheckedBinaryOp(
                                    BinOp::Add,
                                    copy(2),
                                    Operand::Constant(ConstValue::Uint(1, 32)),
                                ),
                            )],
                            3,
                            AssertMessage::Overflow(BinOp::Add),
                            1,
                        ),
                        return_block(1, vec![]),
                    ],
                    1,
                ),
            ),
            // ---- increment 3: the depth-2 (checked-trio) widening battery ----
            // 16. nested checked VALUE operand — the p08::n2 shape
            //     `(a + b) - c`: the outer Sub's lhs is the Field(0) read of
            //     a CheckedAdd over two params. The mint composes
            //     `Sub(Add(a, b), c)` through the delegated scalar builder +
            //     substitution. Step 7 convergence increment 1 (Band A): the
            //     bridge now chases the SAME shape through the SAME builders
            //     and substitution, so this row is COMPARED and byte-identical
            //     — the oracle-checked byte-identity pin for a converted row.
            (
                "nested_checked_value_operand",
                mk_func(
                    "nested_checked_value_operand",
                    vec![
                        local(0, 32, false, None),
                        local(1, 32, false, Some("a")),
                        local(2, 32, false, Some("b")),
                        local(3, 32, false, Some("c")),
                        checked_pair_local(4, 32, false),
                        checked_pair_local(5, 32, false),
                    ],
                    vec![
                        assert_block(
                            0,
                            vec![
                                assign(4, Rvalue::CheckedBinaryOp(BinOp::Add, copy(1), copy(2))),
                                assign(
                                    5,
                                    Rvalue::CheckedBinaryOp(
                                        BinOp::Sub,
                                        Operand::Copy(Place::field(4, 0)),
                                        copy(3),
                                    ),
                                ),
                            ],
                            5,
                            AssertMessage::Overflow(BinOp::Sub),
                            1,
                        ),
                        return_block(1, vec![]),
                    ],
                    3,
                ),
            ),
            // 17. nested operand under an outer MUL — the p08::n1 shape
            //     `(a + b) * c`: Mul is BV-encoded at every width and the BV
            //     operand encoding is a name-keyed fresh var, so the mint
            //     pre-declines (outside-builder-envelope) and the bridge
            //     declines the projection — BothDeclined, enumerated.
            (
                "nested_bv_mul_operand",
                mk_func(
                    "nested_bv_mul_operand",
                    vec![
                        local(0, 32, false, None),
                        local(1, 32, false, Some("a")),
                        local(2, 32, false, Some("b")),
                        local(3, 32, false, Some("c")),
                        checked_pair_local(4, 32, false),
                        checked_pair_local(5, 32, false),
                    ],
                    vec![
                        assert_block(
                            0,
                            vec![
                                assign(4, Rvalue::CheckedBinaryOp(BinOp::Add, copy(1), copy(2))),
                                assign(
                                    5,
                                    Rvalue::CheckedBinaryOp(
                                        BinOp::Mul,
                                        Operand::Copy(Place::field(4, 0)),
                                        copy(3),
                                    ),
                                ),
                            ],
                            5,
                            AssertMessage::Overflow(BinOp::Mul),
                            1,
                        ),
                        return_block(1, vec![]),
                    ],
                    3,
                ),
            ),
            // 18. THE `_N` VOCABULARY WALL PIN: a PLAIN unnamed binop temp
            //     (`_4 = Sub(a, b)` — no checked pair, no projection) feeding
            //     a checked Add. The bridge reconstructs and spells the temp
            //     `Var("_4")`; the mint must keep declining
            //     `unnamed-temp-operand` — a chase widened onto plain temps
            //     would mint `Sub(a, b)` against the bridge's `Var("_4")` and
            //     surface here as an Unclassified mismatch (the mutation this
            //     fixture kills).
            (
                "plain_temp_binop_stays_unnamed",
                mk_func(
                    "plain_temp_binop_stays_unnamed",
                    vec![
                        local(0, 32, false, None),
                        local(1, 32, false, Some("a")),
                        local(2, 32, false, Some("b")),
                        local(3, 32, false, Some("c")),
                        local(4, 32, false, None),
                        checked_pair_local(5, 32, false),
                    ],
                    vec![
                        assert_block(
                            0,
                            vec![
                                assign(4, Rvalue::BinaryOp(BinOp::Sub, copy(1), copy(2))),
                                assign(5, Rvalue::CheckedBinaryOp(BinOp::Add, copy(4), copy(3))),
                            ],
                            5,
                            AssertMessage::Overflow(BinOp::Add),
                            1,
                        ),
                        return_block(1, vec![]),
                    ],
                    3,
                ),
            ),
            // ---- Step 7 convergence increment 1: the Band A/B refusal battery ----
            // 19. BAND A double-def refusal: TWO whole-local CheckedBinaryOp
            //     defs of the chased pair local — the `_N.0` read is
            //     path-dependent, so BOTH lanes must refuse (model `defs_of`
            //     != 1, bridge unique-def guard). A chase that picked either
            //     def would fabricate a formula about one path's value —
            //     the mutation this fixture kills (a last-def chase grades
            //     MintDeclined instead of the pinned BothDeclined).
            (
                "nested_double_def_refuses",
                mk_func(
                    "nested_double_def_refuses",
                    vec![
                        local(0, 32, false, None),
                        local(1, 32, false, Some("a")),
                        local(2, 32, false, Some("b")),
                        local(3, 32, false, Some("c")),
                        checked_pair_local(4, 32, false),
                        checked_pair_local(5, 32, false),
                    ],
                    vec![
                        assert_block(
                            0,
                            vec![
                                assign(4, Rvalue::CheckedBinaryOp(BinOp::Add, copy(1), copy(2))),
                                assign(4, Rvalue::CheckedBinaryOp(BinOp::Add, copy(1), copy(3))),
                                assign(
                                    5,
                                    Rvalue::CheckedBinaryOp(
                                        BinOp::Sub,
                                        Operand::Copy(Place::field(4, 0)),
                                        copy(3),
                                    ),
                                ),
                            ],
                            5,
                            AssertMessage::Overflow(BinOp::Sub),
                            1,
                        ),
                        return_block(1, vec![]),
                    ],
                    3,
                ),
            ),
            // 20. BAND B branching-edge refusal: the div-zero assert's TARGET
            //     terminator is a SwitchInt, and the Div sits beyond the
            //     branch — the op may not post-dominate the assert, so the
            //     walk must refuse on BOTH carriers (the model stays
            //     Excluded("no-divrem-op-found"), the bridge keeps its named
            //     decline). A walk that followed the branch would find the op
            //     and grade this row ByteIdentical — the mutation this pin
            //     kills.
            (
                "divzero_branching_chain_refuses",
                mk_func(
                    "divzero_branching_chain_refuses",
                    vec![
                        local(0, 32, true, None),
                        local(1, 32, true, Some("a")),
                        local(2, 32, true, Some("b")),
                        LocalDecl { index: 3, ty: Ty::Bool, name: None },
                        local(4, 32, true, None),
                    ],
                    vec![
                        assert_block(0, vec![], 3, AssertMessage::DivisionByZero, 1),
                        BasicBlock {
                            id: BlockId(1),
                            stmts: vec![],
                            terminator: Terminator::SwitchInt {
                                discr: copy(1),
                                targets: vec![(0, BlockId(2))],
                                otherwise: BlockId(3),
                                exhaustive_enum_unreachable: false,
                                span: span(),
                            },
                        },
                        return_block(
                            2,
                            vec![assign(4, Rvalue::BinaryOp(BinOp::Div, copy(1), copy(2)))],
                        ),
                        return_block(3, vec![]),
                    ],
                    2,
                ),
            ),
            // 21. BAND B staleness refusal: a write to the DIVISOR local on
            //     the walked chain between the assert and the op — the op's
            //     read denotes a different value than the one the assert
            //     guarded, so the walk must refuse (both carriers). Removing
            //     the staleness guard grades this row ByteIdentical over the
            //     WRONG value — the mutation this pin kills.
            (
                "divzero_stale_divisor_refuses",
                mk_func(
                    "divzero_stale_divisor_refuses",
                    vec![
                        local(0, 32, true, None),
                        local(1, 32, true, Some("a")),
                        local(2, 32, true, Some("b")),
                        LocalDecl { index: 3, ty: Ty::Bool, name: None },
                        LocalDecl { index: 4, ty: Ty::Bool, name: None },
                        local(5, 32, true, None),
                    ],
                    vec![
                        assert_block(0, vec![], 3, AssertMessage::DivisionByZero, 1),
                        assert_block(
                            1,
                            vec![assign(2, Rvalue::Use(copy(1)))],
                            4,
                            AssertMessage::Overflow(BinOp::Div),
                            2,
                        ),
                        return_block(
                            2,
                            vec![assign(5, Rvalue::BinaryOp(BinOp::Div, copy(1), copy(2)))],
                        ),
                    ],
                    2,
                ),
            ),
            // 10. array bounds against a compile-time length: site F's shape,
            //     the extracted bounds tail, byte parity.
            (
                "bounds_const_len",
                mk_func(
                    "bounds_const_len",
                    vec![
                        local(0, 32, false, None),
                        local(1, 64, false, Some("i")),
                        LocalDecl { index: 2, ty: Ty::Bool, name: None },
                    ],
                    vec![
                        assert_block(
                            0,
                            vec![assign(
                                2,
                                Rvalue::BinaryOp(
                                    BinOp::Lt,
                                    copy(1),
                                    Operand::Constant(ConstValue::Uint(5, 64)),
                                ),
                            )],
                            2,
                            AssertMessage::BoundsCheck,
                            1,
                        ),
                        return_block(1, vec![]),
                    ],
                    1,
                ),
            ),
        ]
    }

    // -------------------------------- oracle --------------------------------
    // Scorecard / tally / print_scorecard live in `direct_record_grading`
    // (hoisted, increment 2) — one core for the model oracle AND the
    // real-record grader.

    /// THE MEASURED NUMBER. Corpus = every checked-in vcgen MIR fixture
    /// (`crates/trust-vcgen/tests/data/*.json`) plus the in-test adversarial
    /// battery. Byte-or-decline: any unclassified mismatch fails.
    #[test]
    fn step6_parity_scorecard_byte_or_decline() {
        let mut reports = Vec::new();
        let mut total = 0usize;
        for (name, func) in load_corpus() {
            let graded = grade_function(&name, &func);
            total += graded.len();
            reports.extend(graded);
        }
        let corpus_card = tally(&reports);
        print_scorecard("checked-in vcgen MIR corpus", &corpus_card, total);

        let mut adv_reports = Vec::new();
        let mut adv_total = 0usize;
        for (name, func) in adversarial_functions() {
            let graded = grade_function(name, &func);
            adv_total += graded.len();
            adv_reports.extend(graded);
        }
        let adv_card = tally(&adv_reports);
        print_scorecard("in-test adversarial battery", &adv_card, adv_total);

        // PARITY IS THE PRODUCT: no unexplained mismatch, anywhere.
        assert_eq!(
            corpus_card.unclassified,
            Vec::<String>::new(),
            "corpus: every mismatch must be a pinned known class"
        );
        assert_eq!(
            adv_card.unclassified,
            Vec::<String>::new(),
            "adversarial battery: every mismatch must be a pinned known class"
        );
        // Version tokens exist on neither lane's builders — a nonzero count
        // means vocabulary drifted; investigate before relaxing.
        assert_eq!(corpus_card.version_stripped_only, 0);
        assert_eq!(adv_card.version_stripped_only, 0);
        // The byte claim is non-vacuous on BOTH corpora.
        assert!(corpus_card.byte_identical > 0, "corpus must yield byte-identical pairs");
        assert!(adv_card.byte_identical > 0);
        // The pinned known-mismatch class exists (count >= 1, adversarial 1).
        assert!(
            adv_card.known_mismatch_shadowed_param_name >= 1,
            "the shadowed-param-name structural mismatch must stay pinned"
        );
        // Per-class ByteIdentical floors from the constructed battery: the
        // scalar add/sub core, the bare BV mul envelope (the mul M>0 pin),
        // div-zero, the signed MIN/-1 pair, the shift tail, the bounds tail,
        // and the i128 BV negation subset.
        for class in [
            "overflow-add-sub",
            "overflow-mul",
            "div-by-zero",
            "rem-by-zero",
            "divrem-min-overflow",
            "shift-in-range",
            "bounds-check",
            "overflow-neg",
        ] {
            let (_, byte_identical) = adv_card.per_class.get(class).copied().unwrap_or((0, 0));
            assert!(
                byte_identical >= 1,
                "adversarial battery must pin a ByteIdentical floor for {class}"
            );
        }

        // ---- Increment 2 ratchets (named-value resolution widening) ----
        // The corpus compared count ROSE 41 -> 48 (increment 2's "48
        // expected" case), then 48 -> 79 (Step 7 vocabulary convergence
        // increment 1, measured 2026-09-01: +16 Band A checked-pair rows —
        // the whole increment-3 bridge-declined band gained a comparator —
        // and +15 Band B div/rem conversions out of the 19 walk recoveries;
        // the other 4 are 3 unnamed-temp divisors and 1 constant divisor,
        // each keeping its enumerated decline). Pin the rise and the
        // per-class byte-identical floors — a regression of any earlier
        // floor fails here too.
        assert!(
            corpus_card.compared() >= 79,
            "corpus compared must hold the converged floor (measured 79, was 48): {}",
            corpus_card.compared()
        );
        for (class, floor) in [
            ("overflow-add-sub", 28),
            ("overflow-mul", 1),
            ("div-by-zero", 20),
            ("rem-by-zero", 4),
            ("divrem-min-overflow", 14),
            ("shift-in-range", 8),
            ("bounds-check", 3),
            ("overflow-neg", 1),
        ] {
            let (_, byte_identical) = corpus_card.per_class.get(class).copied().unwrap_or((0, 0));
            assert!(
                byte_identical >= floor,
                "corpus {class}: byte-identical {byte_identical} fell below its floor {floor}"
            );
        }
        // Declines stay ENUMERATED, never vanished: the battery pins every
        // widening decline class, the corpus keeps its unnamed-temp residual
        // (the old opaque-operand 49's dominant component, measured 41), and
        // EVERY decline code on either card must be inside the ONE shared
        // vocabulary — a new class cannot appear without extending it in the
        // same reviewed change (fail-closed accounting).
        for code in [
            "ambiguous-operand-name",
            "shadowed-operand-name",
            "unnamed-temp-operand",
            "synthetic-name-collision",
            "fallback-shaped-var-would-guess-mir-index",
        ] {
            assert!(
                adv_card.mint_declined.get(code).copied().unwrap_or(0) >= 1,
                "battery must pin decline class {code}"
            );
        }
        assert!(
            corpus_card.mint_declined.get("unnamed-temp-operand").copied().unwrap_or(0) >= 1,
            "the corpus' unnamed-temp residual must stay enumerated"
        );
        for card in [&corpus_card, &adv_card] {
            for code in card.mint_declined.keys() {
                assert!(
                    crate::direct_formula_dump::ENUMERATED_WITHHELD_REASONS.contains(code),
                    "decline code {code} is outside the enumerated vocabulary"
                );
            }
        }
    }

    /// Item 1's differential proof (A): synthetic records generated by
    /// running the MODEL over the corpus + adversarial battery, rendered
    /// through the PRODUCTION writer, parsed by the fail-closed parser, and
    /// graded by `grade_real_records` — the scorecard must equal the in-situ
    /// oracle's field for field. The single documented mapping: a model
    /// EXCLUSION means the direct lane holds no record, so those asserts land
    /// in the real grader's `uncovered-by-direct-lane` bucket, whose count
    /// must equal the model's excluded total (and no other exclusion bucket
    /// may appear).
    #[test]
    fn real_record_grader_matches_the_model_oracle_field_for_field() {
        use std::collections::BTreeMap;

        use crate::direct_formula_dump::{
            DIRECT_FORMULA_DUMP_VERSION, DumpedDirectRecord, DumpedOutcome,
            parse_direct_formula_dump, write_direct_formula_dump,
        };
        use crate::direct_record_grading::{grade_real_records, slug_for_assert_message};

        let battery: Vec<(String, VerifiableFunction)> = adversarial_functions()
            .into_iter()
            .map(|(name, func)| (name.to_string(), func))
            .collect();
        for (label, corpus) in [("corpus", load_corpus()), ("battery", battery)] {
            // In-situ oracle card.
            let mut reports = Vec::new();
            for (name, func) in &corpus {
                reports.extend(grade_function(name, func));
            }
            let oracle_card = tally(&reports);

            // Synthesize records FROM THE MODEL, per crate (one production
            // dump file per crate, exactly the seam's own layout).
            let mut by_crate: BTreeMap<String, Vec<DumpedDirectRecord>> = BTreeMap::new();
            for (index, (_, func)) in corpus.iter().enumerate() {
                let Some((krate, def_path)) = func.def_path.split_once("::") else {
                    panic!("fixture def_path must be crate-qualified: {}", func.def_path);
                };
                let mut occ_counters: BTreeMap<(&'static str, u32, u32), u32> = BTreeMap::new();
                for block in &func.body.blocks {
                    let Terminator::Assert { msg, span, .. } = &block.terminator else {
                        continue;
                    };
                    let Some(slug) = slug_for_assert_message(msg) else { continue };
                    let key = (slug, span.line_start, span.col_start);
                    let counter = occ_counters.entry(key).or_insert(0);
                    let occ = *counter;
                    *counter += 1;
                    let model = model_direct_case(func, block)
                        .expect("slug set and model six-class set agree by construction");
                    let outcome = match model {
                        // The direct lane structurally holds no case: NO
                        // record — the real grader must enumerate the assert
                        // as uncovered.
                        ModelSide::Excluded(_) => continue,
                        ModelSide::Withheld(reason) => {
                            DumpedOutcome::Withheld { reason: reason.to_string() }
                        }
                        ModelSide::Case { class, width, signed, operands, .. } => {
                            match mint_direct_safety_formula(&class, width, signed, &operands) {
                                Ok(minted) => DumpedOutcome::minted_verbatim(
                                    &minted.formula_json,
                                    &minted.smtlib,
                                ),
                                Err(decline) => {
                                    DumpedOutcome::Withheld { reason: decline.code().to_string() }
                                }
                            }
                        }
                    };
                    by_crate.entry(krate.to_string()).or_default().push(DumpedDirectRecord {
                        v: DIRECT_FORMULA_DUMP_VERSION.to_string(),
                        krate: krate.to_string(),
                        def_path: def_path.to_string(),
                        def_index: u32::try_from(index).unwrap(),
                        slug: slug.to_string(),
                        line: span.line_start,
                        col: span.col_start,
                        occ,
                        assertion_id: format!(
                            "{krate}::{def_path}#L{}C{}#{slug}#o{occ}",
                            span.line_start, span.col_start
                        ),
                        block: u32::try_from(block.id.0).unwrap(),
                        inst_index: 0,
                        outcome,
                    });
                }
            }

            // Through the PRODUCTION writer and fail-closed parser.
            let dir = std::env::temp_dir()
                .join(format!("step6-differential-{}-{label}", std::process::id()));
            std::fs::create_dir_all(&dir).unwrap();
            let mut records = Vec::new();
            for (krate, rows) in &by_crate {
                let path = write_direct_formula_dump(&dir, krate, rows).expect("write");
                let text = std::fs::read_to_string(&path).unwrap();
                records.extend(
                    parse_direct_formula_dump(&text)
                        .unwrap_or_else(|errs| panic!("{label}/{krate}: {errs:#?}")),
                );
            }
            let real_card = grade_real_records(&records, &corpus)
                .unwrap_or_else(|errs| panic!("{label}: real grading refused: {errs:#?}"));

            assert_eq!(real_card.byte_identical, oracle_card.byte_identical, "{label}");
            assert_eq!(
                real_card.version_stripped_only, oracle_card.version_stripped_only,
                "{label}"
            );
            assert_eq!(real_card.mint_declined, oracle_card.mint_declined, "{label}");
            assert_eq!(real_card.bridge_declined, oracle_card.bridge_declined, "{label}");
            assert_eq!(real_card.both_declined, oracle_card.both_declined, "{label}");
            assert_eq!(
                real_card.known_mismatch_shadowed_param_name,
                oracle_card.known_mismatch_shadowed_param_name,
                "{label}"
            );
            assert_eq!(real_card.unclassified, oracle_card.unclassified, "{label}");
            assert_eq!(real_card.per_class, oracle_card.per_class, "{label}");
            let model_excluded_total: usize = oracle_card.excluded.values().sum();
            assert_eq!(
                real_card.excluded.get("uncovered-by-direct-lane").copied().unwrap_or(0),
                model_excluded_total,
                "{label}: every model exclusion must surface as an uncovered MIR assert"
            );
            assert_eq!(
                real_card.excluded.len(),
                usize::from(model_excluded_total > 0),
                "{label}: no exclusion bucket beyond uncovered-by-direct-lane: {:?}",
                real_card.excluded
            );
            let _ = std::fs::remove_dir_all(&dir);
        }
    }

    /// The `_1`-named param declines via the post-mint sweep — the mint never
    /// fabricates a MIR local index, even when the guess would be right.
    #[test]
    fn param_named_underscore_one_declines_not_guesses() {
        let (_, func) = adversarial_functions()
            .into_iter()
            .find(|(n, _)| *n == "param_named_underscore_one")
            .unwrap();
        let reports = grade_function("param_named_underscore_one", &func);
        assert_eq!(reports.len(), 1);
        assert_eq!(
            reports[0].grade,
            Grade::MintDeclined("fallback-shaped-var-would-guess-mir-index"),
            "the sweep must refuse the fallback-shaped name"
        );
    }

    /// Sub-128 negation: class-wide decline with the measured reason; the
    /// signed-128 BV subset mints byte-identically.
    #[test]
    fn overflow_neg_declines_below_128_and_mints_bv_at_128() {
        let funcs = adversarial_functions();
        let (_, sub128) = funcs.iter().find(|(n, _)| *n == "neg_i32").unwrap();
        let reports = grade_function("neg_i32", sub128);
        assert_eq!(reports.len(), 1);
        assert_eq!(reports[0].grade, Grade::MintDeclined("mir-core-is-temp-cond-var"));

        let (_, i128f) = funcs.iter().find(|(n, _)| *n == "neg_i128").unwrap();
        let reports = grade_function("neg_i128", i128f);
        assert_eq!(reports.len(), 1);
        assert_eq!(reports[0].grade, Grade::ByteIdentical);
    }

    /// Increment 2 widening pins — one per battery fixture, each naming the
    /// exact enumerated disposition. The positive case is byte parity; every
    /// negative case is a NAMED decline, never a vanished row and never a
    /// guessed spelling.
    #[test]
    fn widened_named_value_resolution_pins() {
        let funcs = adversarial_functions();
        let expect = [
            ("nested_named_resolution", Grade::ByteIdentical),
            ("alias_of_param", Grade::MintDeclined("ambiguous-operand-name")),
            ("shadowed_local", Grade::MintDeclined("shadowed-operand-name")),
            ("unnamed_temp", Grade::MintDeclined("unnamed-temp-operand")),
            ("synthetic_collision_name", Grade::MintDeclined("synthetic-name-collision")),
        ];
        for (name, want) in expect {
            let (_, func) = funcs.iter().find(|(n, _)| *n == name).unwrap();
            let reports = grade_function(name, func);
            assert_eq!(reports.len(), 1, "{name}");
            assert_eq!(reports[0].grade, want, "{name}: {}", reports[0].detail);
        }
        // The bridge side of each decline fixture still RECONSTRUCTS (the
        // decline is the direct lane's, not a both-declined coincidence) —
        // checked via the scorecard shape: every decline above tallies as
        // MintDeclined, which grade_pair only mints when the bridge built a
        // formula.
    }

    /// Increment 3 (depth-2 checked-trio widening) grade pins — one per
    /// battery fixture, each naming the exact enumerated disposition.
    /// UPDATED by Step 7 vocabulary convergence increment 1 (Band A):
    /// * the scalar nested shape now has a BRIDGE COMPARATOR — the
    ///   checked-pair chase (`resolve_checked_pair_operands`) renders the
    ///   SAME inline binop through the same builders over the same
    ///   placeholder namespace, so the row is COMPARED and must be
    ///   BYTE-IDENTICAL (this pin is the oracle-checked byte-identity proof
    ///   for a converted row; an operand-order swap in the chase turns it
    ///   red — mutation-proved);
    /// * the BV (mul) nested shape still declines on BOTH lanes (the chase is
    ///   deliberately NOT wired into the Mul arm — BV operand encoding is a
    ///   name-keyed fresh var);
    /// * a PLAIN unnamed binop temp stays `unnamed-temp-operand` — the `_N`
    ///   vocabulary wall. Widening the chase onto plain temps mints
    ///   `Sub(a, b)` against the bridge's reconstructed `Var("_4")` and this
    ///   pin (plus the master's 0-unclassified gate) goes red.
    #[test]
    fn nested_checked_binop_pins() {
        let funcs = adversarial_functions();
        let expect = [
            ("nested_checked_value_operand", Grade::ByteIdentical),
            ("nested_bv_mul_operand", Grade::BothDeclined),
            ("plain_temp_binop_stays_unnamed", Grade::MintDeclined("unnamed-temp-operand")),
        ];
        for (name, want) in expect {
            let (_, func) = funcs.iter().find(|(n, _)| *n == name).unwrap();
            let reports = grade_function(name, func);
            assert_eq!(reports.len(), 1, "{name}");
            assert_eq!(reports[0].grade, want, "{name}: {}", reports[0].detail);
        }
    }

    /// Step 7 vocabulary convergence increment 1 pins — the Band B walk's
    /// positive case and every stated refusal, each named:
    /// * `div_i32_params`' zero-check assert — previously the enumerated
    ///   `no-divrem-op-found` exclusion (the signed MIR shape interposes the
    ///   MIN/-1 assert) — now COMPARES byte-identically via the shared
    ///   bounded target-chain walk (hop 1);
    /// * a NON-unique checked-pair def refuses the Band A chase on BOTH
    ///   lanes;
    /// * a BRANCHING edge on the walk chain refuses Band B (both carriers);
    /// * an interposed WRITE to the divisor local refuses Band B (the assert
    ///   guarded a value the downstream op no longer reads).
    #[test]
    fn band_b_walk_and_band_a_refusal_pins() {
        let funcs = adversarial_functions();

        let (_, func) = funcs.iter().find(|(n, _)| *n == "div_i32_params").unwrap();
        let reports = grade_function("div_i32_params", func);
        assert_eq!(reports.len(), 2);
        assert_eq!(
            reports[0].grade,
            Grade::ByteIdentical,
            "the walk must recover the hop-1 divisor: {}",
            reports[0].detail
        );
        assert_eq!(reports[1].grade, Grade::ByteIdentical);

        let (_, func) = funcs.iter().find(|(n, _)| *n == "nested_double_def_refuses").unwrap();
        let reports = grade_function("nested_double_def_refuses", func);
        assert_eq!(reports.len(), 1);
        assert_eq!(
            reports[0].grade,
            Grade::BothDeclined,
            "a projection chased to a NON-unique def must refuse on both lanes: {}",
            reports[0].detail
        );

        for (fixture, expected_len) in
            [("divzero_branching_chain_refuses", 1), ("divzero_stale_divisor_refuses", 2)]
        {
            let (_, func) = funcs.iter().find(|(n, _)| *n == fixture).unwrap();
            let reports = grade_function(fixture, func);
            assert_eq!(reports.len(), expected_len, "{fixture}");
            assert_eq!(
                reports[0].grade,
                Grade::Excluded("no-divrem-op-found"),
                "{fixture}: the walk must refuse"
            );
            // The bridge's decline names the walk (v7/D3: the refusal carries
            // the fix text naming what was searched).
            let block = &func.body.blocks[0];
            let Terminator::Assert { cond, msg, target, .. } = &block.terminator else {
                panic!("fixture shape");
            };
            let bridge = reconstruct_assert_safety_predicate(
                &func.body.locals,
                &func.body.blocks,
                block.id,
                *target,
                cond,
                msg,
            )
            .expect("div-zero assert has a bridge disposition");
            let SafetyPredicate::NotReconstructed(reason) = bridge else {
                panic!("{fixture}: bridge must decline, got a formula");
            };
            assert!(
                reason.contains("bounded-walk"),
                "{fixture}: the decline must name the walk: {reason}"
            );
        }
        // The stale-divisor fixture's MIN/-1 assert still compares (the
        // existing target probe finds the op; staleness gates only the walk).
        let (_, func) = funcs.iter().find(|(n, _)| *n == "divzero_stale_divisor_refuses").unwrap();
        let reports = grade_function("divzero_stale_divisor_refuses", func);
        assert_eq!(reports[1].grade, Grade::ByteIdentical);
    }

    /// Increment 3 mint unit pins, all through the SHARED mint (the code path
    /// both carriers execute — the "same code" half of the equivalence
    /// obligation; the per-carrier recognizers are mirrored and pinned by the
    /// battery + the real-record driver).
    #[test]
    fn nested_operand_mint_unit_pins() {
        let nested = |op, width, signed, lhs: &str, rhs: DirectFormulaOperand| {
            DirectFormulaOperand::Nested {
                op,
                width,
                signed,
                lhs: Box::new(DirectFormulaOperand::Named { name: lhs.to_string() }),
                rhs: Box::new(rhs),
            }
        };
        let named = |name: &str| DirectFormulaOperand::Named { name: name.to_string() };

        // 1. Substitution byte pin (Operand-taking builder path): the composed
        //    div-zero core is EXACTLY the builder's own `Eq(divisor, 0)` shape
        //    with the divisor position holding the composed term.
        let minted = mint_direct_safety_formula(
            &DirectFormulaClass::DivByZero,
            32,
            true,
            &[nested(NestedBinOp::Sub, 32, true, "a", named("b"))],
        )
        .expect("nested divisor must mint through the scalar builder");
        assert_eq!(
            minted.formula,
            Formula::Eq(
                Box::new(Formula::Sub(
                    Box::new(Formula::var("a", Sort::Int)),
                    Box::new(Formula::var("b", Sort::Int)),
                )),
                Box::new(Formula::Int(0)),
            ),
            "substitution must inline the composed term at the operand position"
        );

        // 2. Substitution byte pin (from_parts path): bounds over `i + 1`.
        let minted = mint_direct_safety_formula(
            &DirectFormulaClass::BoundsCheck { len: 5 },
            64,
            false,
            &[nested(NestedBinOp::Add, 64, false, "i", DirectFormulaOperand::Lit(1))],
        )
        .expect("nested bounds index must mint through the extracted tail");
        assert_eq!(
            minted.formula,
            Formula::Ge(
                Box::new(Formula::Add(
                    Box::new(Formula::var("i", Sort::Int)),
                    Box::new(Formula::Int(1)),
                )),
                Box::new(Formula::Int(5)),
            ),
        );

        // 3. The scalar overflow core carries the composed term at EVERY
        //    operand position (ranges included) and NO placeholder survives.
        let minted = mint_direct_safety_formula(
            &DirectFormulaClass::OverflowAddSub { op: AddSubOp::Sub },
            32,
            false,
            &[nested(NestedBinOp::Add, 32, false, "a", named("b")), named("c")],
        )
        .expect("nested scalar sub must mint");
        let mut names = Vec::new();
        let mut saw_composed_result = false;
        minted.formula.visit(&mut |node| {
            if let Formula::Var(name, _) = node {
                names.push(name.clone());
            }
            saw_composed_result |= *node
                == Formula::Sub(
                    Box::new(Formula::Add(
                        Box::new(Formula::var("a", Sort::Int)),
                        Box::new(Formula::var("b", Sort::Int)),
                    )),
                    Box::new(Formula::var("c", Sort::Int)),
                );
        });
        names.sort();
        names.dedup();
        assert_eq!(names, vec!["a".to_string(), "b".to_string(), "c".to_string()]);
        assert!(saw_composed_result, "result term must be Sub(Add(a,b), c): {minted:?}");

        // 4. MUTATION-PINNED width guard: a nested operand whose own type
        //    disagrees with the checked op's declines, never adopts either.
        assert_eq!(
            mint_direct_safety_formula(
                &DirectFormulaClass::OverflowAddSub { op: AddSubOp::Add },
                32,
                false,
                &[
                    nested(NestedBinOp::Add, 64, false, "a", named("b")),
                    DirectFormulaOperand::Lit(1)
                ],
            ),
            Err(FormulaDecline::NestedOperandWidthMismatch {
                outer: (32, false),
                inner: (64, false),
            }),
        );
        // Signedness alone is a mismatch too.
        assert_eq!(
            mint_direct_safety_formula(
                &DirectFormulaClass::OverflowAddSub { op: AddSubOp::Add },
                32,
                false,
                &[
                    nested(NestedBinOp::Add, 32, true, "a", named("b")),
                    DirectFormulaOperand::Lit(1)
                ],
            ),
            Err(FormulaDecline::NestedOperandWidthMismatch {
                outer: (32, false),
                inner: (32, true),
            }),
        );

        // 5. Every BV-rendered class pre-declines a nested operand — the BV
        //    operand encoding is a NAME-KEYED fresh var; a composed term has
        //    no base name and fabricating one is the pinned guessed-index
        //    hazard.
        assert_eq!(
            mint_direct_safety_formula(
                &DirectFormulaClass::OverflowMul,
                32,
                false,
                &[nested(NestedBinOp::Add, 32, false, "a", named("b")), named("c")],
            ),
            Err(FormulaDecline::OutsideBuilderEnvelope {
                builder: "reconstruct_bv_mul_overflow_body"
            }),
        );
        assert_eq!(
            mint_direct_safety_formula(
                &DirectFormulaClass::OverflowAddSub { op: AddSubOp::Add },
                128,
                true,
                &[nested(NestedBinOp::Add, 128, true, "a", named("b")), named("c")],
            ),
            Err(FormulaDecline::OutsideBuilderEnvelope {
                builder: "reconstruct_bv_signed_addsub_overflow_body"
            }),
        );
        assert_eq!(
            mint_direct_safety_formula(
                &DirectFormulaClass::OverflowNeg,
                128,
                true,
                &[nested(NestedBinOp::Add, 128, true, "a", named("b"))],
            ),
            Err(FormulaDecline::OutsideBuilderEnvelope {
                builder: "reconstruct_bv_signed_neg_overflow_body"
            }),
        );

        // 6. Depth cap: one nesting level is the envelope; a Nested leaf is a
        //    fail-closed decline (neither carrier's recognizer builds it).
        assert_eq!(
            mint_direct_safety_formula(
                &DirectFormulaClass::DivByZero,
                32,
                true,
                &[DirectFormulaOperand::Nested {
                    op: NestedBinOp::Sub,
                    width: 32,
                    signed: true,
                    lhs: Box::new(nested(NestedBinOp::Add, 32, true, "a", named("b"))),
                    rhs: Box::new(named("c")),
                }],
            ),
            Err(FormulaDecline::OutsideBuilderEnvelope { builder: "nested-operand-depth-cap" }),
        );

        // 7. Placeholder-namespace discipline: with a nested operand present a
        //    user name in the reserved prefix declines (the builder would
        //    demote BOTH same-named locals and the substitution would miss)…
        assert_eq!(
            mint_direct_safety_formula(
                &DirectFormulaClass::OverflowAddSub { op: AddSubOp::Add },
                32,
                false,
                &[
                    nested(NestedBinOp::Add, 32, false, "a", named("b")),
                    named("trust_direct_nested_operand_0"),
                ],
            ),
            Err(FormulaDecline::OutsideBuilderEnvelope { builder: "nested_operand_placeholder" }),
        );
        // …and WITHOUT one, the same name still mints — increment-1 behavior
        // preserved (nothing is synthesized in the prefix).
        assert!(
            mint_direct_safety_formula(
                &DirectFormulaClass::OverflowAddSub { op: AddSubOp::Add },
                32,
                false,
                &[named("trust_direct_nested_operand_0"), DirectFormulaOperand::Lit(1)],
            )
            .is_ok(),
        );
    }

    /// Mixed-width operands: both lanes decline; nothing is guessed.
    #[test]
    fn mixed_width_declines_on_both_lanes() {
        let (_, func) =
            adversarial_functions().into_iter().find(|(n, _)| *n == "mixed_width").unwrap();
        let reports = grade_function("mixed_width", &func);
        assert_eq!(reports.len(), 1);
        assert_eq!(reports[0].grade, Grade::BothDeclined);
    }

    /// The shadowed-param fixture lands in the pinned known-mismatch class —
    /// and the bridge side indeed fell back to the `_N` namespace, so the
    /// mismatch is the measured structural one, not an accident.
    #[test]
    fn shadowed_param_name_is_the_pinned_known_mismatch() {
        let (_, func) =
            adversarial_functions().into_iter().find(|(n, _)| *n == "shadowed_param").unwrap();
        let reports = grade_function("shadowed_param", &func);
        assert_eq!(reports.len(), 1);
        assert_eq!(reports[0].grade, Grade::KnownMismatchShadowedParamName);

        // Independently confirm the bridge fell back to `_1` while the mint
        // kept the param name — the structural cause named by the design.
        let block = &func.body.blocks[0];
        let Terminator::Assert { cond, msg, target, .. } = &block.terminator else {
            panic!("fixture shape");
        };
        let bridge = reconstruct_assert_safety_predicate(
            &func.body.locals,
            &func.body.blocks,
            block.id,
            *target,
            cond,
            msg,
        )
        .unwrap();
        let SafetyPredicate::Reconstructed(bf) = bridge else { panic!("bridge must build") };
        let mut saw_fallback = false;
        bf.visit(&mut |node| {
            if let Formula::Var(name, _) = node {
                saw_fallback |= name == "_1";
            }
        });
        assert!(saw_fallback, "bridge side must carry the fallback var: {bf:?}");
    }

    /// Direct mint unit pin: same-param `x + x` synthesizes ONE local (one
    /// MIR local backs every use of one param), so both sides read one var.
    #[test]
    fn same_named_operand_synthesizes_one_local() {
        let minted = mint_direct_safety_formula(
            &DirectFormulaClass::OverflowAddSub { op: AddSubOp::Add },
            32,
            false,
            &[
                DirectFormulaOperand::Named { name: "x".to_string() },
                DirectFormulaOperand::Named { name: "x".to_string() },
            ],
        )
        .expect("same-name pair must mint");
        let mut names = Vec::new();
        minted.formula.visit(&mut |node| {
            if let Formula::Var(name, _) = node {
                names.push(name.clone());
            }
        });
        names.sort();
        names.dedup();
        assert_eq!(names, vec!["x".to_string()], "one param name, one var");
    }

    /// Arity and width guards fail closed with their named reasons.
    #[test]
    fn mint_guards_fail_closed_with_named_reasons() {
        assert_eq!(
            mint_direct_safety_formula(
                &DirectFormulaClass::DivByZero,
                0,
                false,
                &[DirectFormulaOperand::Named { name: "d".to_string() }],
            ),
            Err(FormulaDecline::NonConcreteWidth),
            "width 0 is the generic tripwire"
        );
        assert_eq!(
            mint_direct_safety_formula(
                &DirectFormulaClass::OverflowMul,
                32,
                false,
                &[DirectFormulaOperand::Lit(1)],
            ),
            Err(FormulaDecline::WrongOperandCount { expected: 2, got: 1 }),
        );
        // A constant divisor is outside reconstruct_divisor_is_zero's
        // envelope (vcgen gates the constant case separately).
        assert_eq!(
            mint_direct_safety_formula(
                &DirectFormulaClass::DivByZero,
                32,
                false,
                &[DirectFormulaOperand::Lit(3)],
            ),
            Err(FormulaDecline::OutsideBuilderEnvelope { builder: "reconstruct_divisor_is_zero" }),
        );
        // Char discipline lives in direct_int_width.
        assert_eq!(
            super::direct_int_width(&trust_ir::Ty::Char),
            Err(FormulaDecline::UnsupportedCharWidth)
        );
        assert_eq!(super::direct_int_width(&trust_ir::Ty::Usize), Ok((64, false)));
        assert_eq!(super::direct_int_width(&trust_ir::Ty::Isize), Ok((64, true)));
        assert_eq!(
            super::direct_int_width(&trust_ir::Ty::Unit),
            Err(FormulaDecline::NonConcreteWidth),
            "Ty::Unit (the generic placeholder) must trip the width tripwire"
        );
    }
}
