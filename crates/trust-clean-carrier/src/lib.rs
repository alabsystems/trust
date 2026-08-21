// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **Clean type → Rust carrier.** Increment I4 of
//! `docs/design/2026-08-04-two-language-compiler-architecture.md`.
//!
//! # Why this direction is different from every other gate in Trust
//!
//! Every other gate is refutation-shaped: it can only decline to prove
//! something, so a disagreement costs a failed build. This direction can
//! **produce a value**, so a disagreement is a **wrong binary**. That is the
//! entire reason this crate exists and the reason it lands before any `DefId`
//! is minted.
//!
//! # Kernel defeq does not subsume representation faithfulness
//!
//! `tests/control_b_defeq_insufficiency.rs` runs the real
//! `clean_kernel::TypeChecker` and establishes, as a kernel fact, that
//!
//! ```text
//! UInt64.toNat (UInt64.ofNat (2^64))   ≡   0
//! ```
//!
//! — the `Nat → UInt64` extraction composed with the `UInt64 → Nat` admission
//! is definitionally equal to the wrong answer. `UInt64.ofNat` is total and
//! reduces through `Fin.ofNat`, i.e. `mod 2^64`; it wraps, and defeq is happy.
//! So a gate whose whole test is "does the kernel accept this" admits a term
//! whose emitted value is wrong. The carrier obligation is therefore a
//! **separate** obligation, discharged **before** the kernel gate, and it is
//! stated at the **carrier** type — never at the Clean type, which would hand
//! the kernel a proposition that is already false.
//!
//! # The three properties this crate promises
//!
//! * **Partial.** It models a small set of Clean types and nothing else.
//! * **Total on its domain.** For a type it models, the carrier is exact for
//!   every inhabitant and every operation — no range assumption, no "in
//!   practice", no fast path.
//! * **Never approximating.** A Clean type with no faithful Rust
//!   representation gets **no carrier**. It does not get a lossy one, and it
//!   does not get a carrier plus a caveat.
//!
//! Fail-closed follows: unknown type ⇒ no carrier ⇒ no
//! [`CarrierEvidence::Total`] ⇒ no `Capability::Call`.
//!
//! # Function types
//!
//! A Clean `def` has a `Pi` for a type, so the base-type map alone cannot mint
//! a single Clean function: `def f (a : UInt64) : UInt64 := a` is typed
//! `UInt64 -> UInt64`. [`carrier_signature_for`] decomposes such a type into a
//! [`CarrierSignature`] — argument carriers, a result carrier, an arity.
//!
//! It is **built entirely out of [`carrier_for`]**, one call per position, and
//! that is the whole design: every property decided for a base type is
//! inherited positionally rather than re-derived. A signature is total in every
//! position or it does not exist — `Nat` in an argument refuses exactly as
//! `Nat` alone does, and there is no partial credit for the positions that were
//! fine. A genuinely dependent `Pi` is refused rather than flattened, because
//! erasing the dependency would type the Rust side at a weaker statement than
//! the Clean side proves.
//!
//! # The bignum carrier (I6)
//!
//! The Trust-owned bignum exists: `trust_bignum::Nat`
//! (crates/trust-bignum), a Rust value type with Lean `Nat` semantics exactly,
//! and it is the **default carrier for [`CleanType::Nat`]** — unbounded,
//! exact, spelled [`Ty::BignumNat`]. Two boundaries are unchanged by that:
//!
//! * **`Nat` at a fixed width stays refused.** `Nat → u64` is still
//!   [`CarrierRefused::Narrowing`], forever — the carrier grant is at the
//!   exact unbounded type only, never an approximation at a requested width.
//! * **`Int` still has no carrier.** A ℕ runtime is not a ℤ carrier; `Int`
//!   needs its own carrier decision, and pretending `Nat` covers it is how
//!   sign bugs ship. `trust-symbols` pins the exact `(clean_type,
//!   rust_carrier)` pairing independently, so an `Int → trust_bignum::Nat`
//!   obligation cannot discharge even if this table were edited to propose it.
//!
//! The runtime's agreement with kernel `Nat` is **trusted, not proved** —
//! [`trust_symbols::OperationAgreement::TrustedRuntimeAgreement`] says so by
//! name, and `docs/TCB.md` carries the row (evidence: trust-bignum's
//! hardware-referenced agreement tests, hand-transcribed Lean-semantics pins,
//! and the executed differential against clean-kernel's reduction lanes).

use clean_kernel::{BigNat, Expr, ExprKind, Literal};
use trust_symbols::{
    CarrierEvidence, CarrierExtent, CarrierWitness, ObligationNotDischarged, OperationAgreement,
    RepresentationObligation, SymbolHeader,
};
use trust_types::Ty;

// ---------------------------------------------------------------------------
// The modeled Clean types
// ---------------------------------------------------------------------------

/// A Clean type this crate models.
///
/// "Models" is stronger than "recognizes the name of": every variant here has a
/// decided answer about whether it has a faithful Rust carrier, including the
/// variants whose answer is **no**. A Clean type that is not a variant here is
/// not refused — it is *unmodeled*, which is also a refusal, but a different
/// and weaker one, and the two are kept apart on purpose.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
pub enum CleanType {
    /// `Bool`. Two inhabitants. Carrier: `bool`.
    Bool,
    /// `UInt8` / `UInt16` / `UInt32` / `UInt64` — genuine Lean v4.30 shape,
    /// `structure UIntN where ofBitVec :: (toBitVec : BitVec N)`. Arithmetic
    /// wraps at `2^N`, exactly as Rust's `uN` does in release mode.
    UInt(u32),
    /// `BitVec w`. Carrier: `uw` when `w` is a machine width.
    BitVec(u32),
    /// `Nat` — **unbounded**. No fixed-width carrier exists, at any width.
    Nat,
    /// `Int` — **unbounded** signed. Same verdict as [`Self::Nat`], and worth a
    /// variant of its own because `first-party`-adjacent probe fixtures pair
    /// Clean `Int` with Rust `i64`, which is not a carrier.
    Int,
    /// `USize` — bounded, but by `System.Platform.numBits`, which this crate
    /// has not resolved. Deliberately refused; see [`CarrierRefused::TargetDependentWidth`].
    USize,
    /// A `Sort` (`Prop`, `Type`). Not a type of values at all: a proposition is
    /// observed from a proof context, never produced.
    Sort,
}

impl CleanType {
    /// How many values it holds.
    #[must_use]
    pub fn extent(self) -> CarrierExtent {
        match self {
            // `Bool` is two inhabitants = 2^1, and Rust `bool` is the same two.
            Self::Bool => CarrierExtent::Bits(1),
            Self::UInt(w) | Self::BitVec(w) => CarrierExtent::Bits(w),
            Self::Nat | Self::Int => CarrierExtent::Unbounded,
            Self::USize => CarrierExtent::TargetDependent,
            Self::Sort => CarrierExtent::NotAValue,
        }
    }

    /// Its stable rendering, for diagnostics.
    #[must_use]
    pub fn name(self) -> String {
        match self {
            Self::Bool => "Bool".to_string(),
            Self::UInt(w) => format!("UInt{w}"),
            Self::BitVec(w) => format!("BitVec {w}"),
            Self::Nat => "Nat".to_string(),
            Self::Int => "Int".to_string(),
            Self::USize => "USize".to_string(),
            Self::Sort => "Sort".to_string(),
        }
    }

    /// The **one** Rust type that carries it faithfully, if there is one.
    ///
    /// Singular by design. A carrier map that offered a *set* of acceptable
    /// carriers would have to rank them, and the first time two are "both
    /// fine" is the first time a caller picks the wrong one.
    #[must_use]
    pub fn exact_carrier(self) -> Option<Ty> {
        match self {
            Self::Bool => Some(Ty::Bool),
            Self::UInt(w) | Self::BitVec(w) if is_machine_width(w) => {
                Some(Ty::Int { width: w, signed: false })
            }
            // I6: `Nat` is carried by the Trust-owned bignum runtime — exact
            // and unbounded. `Int` deliberately stays `None`: a ℕ runtime is
            // not a ℤ carrier.
            Self::Nat => Some(Ty::BignumNat),
            _ => None,
        }
    }
}

/// The widths Rust actually has an unsigned integer for.
fn is_machine_width(w: u32) -> bool {
    matches!(w, 8 | 16 | 32 | 64)
}

// ---------------------------------------------------------------------------
// Recognition
// ---------------------------------------------------------------------------

/// Recognize a Clean type expression, or `None` if this crate does not model it.
///
/// Matching is **syntactic and shallow on purpose**. It does not reduce, it
/// does not unfold, and it does not consult a kernel. Reduction is what turns
/// `UInt64.ofNat (2^64)` into `0`; a carrier map that reduces is a carrier map
/// that can be argued into the wrong answer by a clever definition.
/// `ExprKind::MData` is the one thing stripped, because metadata is annotation
/// and carries no semantics.
#[must_use]
pub fn recognize(ty: &Expr) -> Option<CleanType> {
    let ty = strip_mdata(ty);
    match ty.kind() {
        // A `Sort` is `Prop`/`Type`. Not a value.
        ExprKind::Sort(_) | ExprKind::SProp => Some(CleanType::Sort),
        ExprKind::Const(name, _) => match name.to_string().as_str() {
            "Bool" => Some(CleanType::Bool),
            "UInt8" => Some(CleanType::UInt(8)),
            "UInt16" => Some(CleanType::UInt(16)),
            "UInt32" => Some(CleanType::UInt(32)),
            "UInt64" => Some(CleanType::UInt(64)),
            "USize" => Some(CleanType::USize),
            "Nat" => Some(CleanType::Nat),
            "Int" => Some(CleanType::Int),
            // `Prop` spelled as a constant rather than `Sort 0`.
            "Prop" | "Type" => Some(CleanType::Sort),
            _ => None,
        },
        // `BitVec w`, with `w` a literal. A symbolic width is NOT recognized:
        // "some width" is not a width.
        ExprKind::App(head, arg) => {
            let ExprKind::Const(name, _) = strip_mdata(head).kind() else { return None };
            if name.to_string() != "BitVec" {
                return None;
            }
            let width = nat_literal(strip_mdata(arg))?.to_u64()?;
            Some(CleanType::BitVec(u32::try_from(width).ok()?))
        }
        _ => None,
    }
}

fn strip_mdata(e: &Expr) -> &Expr {
    let mut cur = e;
    while let ExprKind::MData(_, inner) = cur.kind() {
        cur = inner;
    }
    cur
}

fn nat_literal(e: &Expr) -> Option<&BigNat> {
    match e.kind() {
        ExprKind::Lit(Literal::Nat(n)) => Some(n),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// The Rust side
// ---------------------------------------------------------------------------

/// How many values a Rust type holds, as far as this crate models it.
///
/// This is the **storage** extent, and signedness is deliberately not part of
/// it: `i64` and `u64` both hold 2^64 values. Signedness is a difference in how
/// those bits are *read*, and it is caught by the exactness test
/// ([`CleanType::exact_carrier`] returns one type, not a family), which is
/// where it belongs — an extent that quietly folded in signedness would make
/// `UInt64 → i64` look like a *width* problem, and the user would fix the
/// wrong thing.
///
/// `PtrSizedInt` is [`CarrierExtent::TargetDependent`] rather than `Bits(64)`.
/// That is a deliberate divergence from `trust-certify`'s `clean_island.rs`,
/// which maps `PtrSizedInt { signed: false }` to a hardcoded `UInt64` with no
/// target consultation: on a 32-bit target that types a 32-bit value at 64
/// bits, a representation-faithfulness violation on exactly the path this crate
/// governs.
fn rust_extent(ty: &Ty) -> CarrierExtent {
    match ty {
        Ty::Bool => CarrierExtent::Bits(1),
        Ty::Int { width, .. } => CarrierExtent::Bits(*width),
        Ty::PtrSizedInt { .. } => CarrierExtent::TargetDependent,
        // I6: the trust-bignum runtime holds every natural — genuinely
        // unbounded, the honest extent that lets ONLY the trusted-runtime
        // discharge arm (never a width check) pair it with `Nat`.
        Ty::BignumNat => CarrierExtent::Unbounded,
        // Not a scalar this crate models as a value carrier at all.
        _ => CarrierExtent::NotAValue,
    }
}

/// The largest value an unsigned Rust carrier holds, in decimal, or `None`
/// when the type's signedness means `2^bits - 1` is not its maximum. A
/// diagnostic that states a bound must state the true one.
/// (`Ty::BignumNat` deliberately has no arm: an unbounded carrier has no
/// largest value, and the wildcard `None` is exactly that.)
fn unsigned_max_for(ty: &Ty) -> Option<String> {
    match ty {
        Ty::Bool => Some("1".to_string()),
        Ty::Int { width, signed: false } => Some(max_for_width(*width)),
        _ => None,
    }
}

/// Render a Rust type the way a user spells it.
fn rust_name(ty: &Ty) -> String {
    match ty {
        Ty::Bool => "bool".to_string(),
        // I6: this string is the witness/wire rendering of the bignum carrier;
        // trust-symbols' pinned pairing table matches it byte-for-byte.
        Ty::BignumNat => "trust_bignum::Nat".to_string(),
        Ty::Int { width, signed } => format!("{}{width}", if *signed { 'i' } else { 'u' }),
        Ty::PtrSizedInt { signed } => {
            if *signed { "isize".to_string() } else { "usize".to_string() }
        }
        Ty::Char => "char".to_string(),
        Ty::Float { width } => format!("f{width}"),
        other => format!("{other:?}"),
    }
}

// ---------------------------------------------------------------------------
// The granted carrier
// ---------------------------------------------------------------------------

/// A granted carrier: a Clean type, the Rust type that carries it, and the
/// discharged obligation that justifies the pairing.
///
/// This is the **only** type in the tree that holds a
/// [`trust_symbols::CarrierWitness`] derived from a Clean type, and
/// `CarrierWitness` is the only thing that mints
/// [`CarrierEvidence::Total`]. Those two facts together are what make the
/// `Nat → u64` miscompile unreachable **by construction** rather than by
/// policy: there is no code path from a `Nat` to a `Total`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Carrier {
    clean: CleanType,
    rust: Ty,
    witness: CarrierWitness,
}

impl Carrier {
    /// The Clean type.
    #[must_use]
    pub fn clean(&self) -> CleanType {
        self.clean
    }

    /// The Rust carrier.
    #[must_use]
    pub fn rust(&self) -> &Ty {
        &self.rust
    }

    /// The discharged representation-faithfulness obligation.
    #[must_use]
    pub fn witness(&self) -> &CarrierWitness {
        &self.witness
    }

    /// The carrier evidence this earns. Always [`CarrierEvidence::Total`] —
    /// a `Carrier` value cannot exist otherwise.
    #[must_use]
    pub fn evidence(&self) -> CarrierEvidence {
        CarrierEvidence::Total
    }

    /// Record this carrier on a symbol header — the seam into
    /// `SymbolHeader::grant_call`.
    #[must_use]
    pub fn record_on(&self, header: SymbolHeader) -> SymbolHeader {
        header.with_total_carrier(self.witness.clone())
    }
}

// ---------------------------------------------------------------------------
// Signatures
// ---------------------------------------------------------------------------

/// A position in a function signature, named so a refusal points at the thing
/// the user has to change (v7/D3).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SignaturePosition {
    /// The nth argument, 0-based, counting left to right.
    Argument(usize),
    /// The result.
    Result,
}

impl SignaturePosition {
    /// Its rendering inside a diagnostic sentence.
    #[must_use]
    pub fn describe(self) -> String {
        match self {
            Self::Argument(i) => format!("argument {i}"),
            Self::Result => "the result".to_string(),
        }
    }
}

impl core::fmt::Display for SignaturePosition {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(&self.describe())
    }
}

/// A granted **signature** carrier: a carrier per argument, a carrier for the
/// result, and therefore an arity.
///
/// # Why this cannot be a hole in the base-type discipline
///
/// The fields are private, there is no public constructor, and the only
/// producer is [`carrier_signature_for`], which obtains every component from
/// [`carrier_for`] — the same function that decides a base type, unchanged.
/// So:
///
/// * the components are `Carrier`, not `Option<Carrier>`. A partially-witnessed
///   signature is not a state this type can be in;
/// * every component therefore holds a [`CarrierWitness`], which exists only as
///   the `Ok` of `RepresentationObligation::discharge`;
/// * consequently [`CarrierEvidence::Total`] remains reachable only through a
///   discharged obligation — one per position, all of them.
///
/// "The interesting arguments are fine" is not expressible here, on purpose.
///
/// # The seal, as a compile-fail control
///
/// A signature cannot be assembled by hand out of whatever carriers happened to
/// be lying around, because the fields are private:
///
/// ```compile_fail,E0451
/// let sig = trust_clean_carrier::CarrierSignature { arguments: vec![], result: todo!() };
/// ```
///
/// The partner positive control — the same API, exercised so the block above
/// cannot "pass" because of a typo:
///
/// ```
/// use clean_kernel::{Expr, Name};
/// let f = |n: &str| Expr::const_(Name::from_string(n), vec![]);
/// let sig = trust_clean_carrier::carrier_signature_for(&Expr::arrow(f("UInt64"), f("Bool")))
///     .expect("UInt64 -> Bool is exact in both positions");
/// assert_eq!(sig.arity(), 1);
/// assert_eq!(sig.witnesses().count(), 2);
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CarrierSignature {
    arguments: Vec<Carrier>,
    result: Carrier,
}

impl CarrierSignature {
    /// The argument carriers, left to right.
    #[must_use]
    pub fn arguments(&self) -> &[Carrier] {
        &self.arguments
    }

    /// The result carrier.
    #[must_use]
    pub fn result(&self) -> &Carrier {
        &self.result
    }

    /// How many arguments. Zero for a bare (non-function) type.
    #[must_use]
    pub fn arity(&self) -> usize {
        self.arguments.len()
    }

    /// Every discharged witness, arguments first and the result last.
    ///
    /// Exactly `arity() + 1` of them, always — that count is the observable
    /// form of "total in every position".
    pub fn witnesses(&self) -> impl Iterator<Item = &CarrierWitness> + '_ {
        self.arguments.iter().chain(core::iter::once(&self.result)).map(Carrier::witness)
    }

    /// The carrier evidence this earns. Always [`CarrierEvidence::Total`] — a
    /// `CarrierSignature` value cannot exist otherwise.
    #[must_use]
    pub fn evidence(&self) -> CarrierEvidence {
        CarrierEvidence::Total
    }

    /// Record the **result** carrier on a symbol header.
    ///
    /// Named for what it does rather than called `record_on`, because a
    /// `SymbolHeader` carries one witness and a signature has several: the one
    /// recorded is the value a call *produces*. That is not a weakening — the
    /// existence of this `CarrierSignature` is already the statement that every
    /// argument is carried too, and a caller that wants those has
    /// [`Self::arguments`].
    #[must_use]
    pub fn record_result_on(&self, header: SymbolHeader) -> SymbolHeader {
        self.result.record_on(header)
    }
}

/// Decompose a Clean type into argument carriers and a result carrier.
///
/// A non-`Pi` type is a signature of arity 0 whose result is its base carrier,
/// so this is a strict generalization of [`carrier_for`] and agrees with it
/// exactly on base types.
///
/// # Errors
///
/// * [`CarrierRefused::SignatureComponent`] when any single position has no
///   carrier — naming the position and carrying that position's own base-type
///   refusal verbatim;
/// * [`CarrierRefused::DependentFunctionType`] when the `Pi` is genuinely
///   dependent.
pub fn carrier_signature_for(ty: &Expr) -> Result<CarrierSignature, CarrierRefused> {
    let mut arguments: Vec<Carrier> = Vec::new();
    let mut cursor = strip_mdata(ty);

    while let ExprKind::Pi(_, domain, body) = cursor.kind() {
        let index = arguments.len();

        // Dependency first, because a dependent `Pi` has no Rust signature at
        // ALL — not even a refusable one stated per position. `body` is the
        // whole remainder of the type, so a loose bound variable anywhere in it
        // means this binder (or an outer one) is used downstream; the check is
        // therefore not fooled by a dependency that surfaces several arrows
        // later. It over-approximates, which is the safe direction: the cost is
        // a refusal, never a grant.
        if body.has_loose_bvars_quick() {
            return Err(CarrierRefused::DependentFunctionType {
                binder_index: index,
                signature: render_signature(ty),
            });
        }

        // The ONE decision procedure, called positionally. Not a variant of it.
        let carrier = carrier_for(domain).map_err(|cause| CarrierRefused::SignatureComponent {
            position: SignaturePosition::Argument(index),
            arity: count_arrows(ty),
            signature: render_signature(ty),
            cause: Box::new(cause),
        })?;
        arguments.push(carrier);
        cursor = strip_mdata(body);
    }

    let result = carrier_for(cursor).map_err(|cause| CarrierRefused::SignatureComponent {
        position: SignaturePosition::Result,
        arity: arguments.len(),
        signature: render_signature(ty),
        cause: Box::new(cause),
    })?;

    Ok(CarrierSignature { arguments, result })
}

/// How many arrows the type has at the top level.
fn count_arrows(ty: &Expr) -> usize {
    let mut n = 0;
    let mut cursor = strip_mdata(ty);
    while let ExprKind::Pi(_, _, body) = cursor.kind() {
        n += 1;
        cursor = strip_mdata(body);
    }
    n
}

/// A whole signature, rendered `A -> B -> C`.
fn render_signature(ty: &Expr) -> String {
    let mut parts: Vec<String> = Vec::new();
    let mut cursor = strip_mdata(ty);
    while let ExprKind::Pi(_, domain, body) = cursor.kind() {
        parts.push(render_type(domain));
        cursor = strip_mdata(body);
    }
    parts.push(render_type(cursor));
    parts.join(" -> ")
}

/// A single position, rendered: its modeled name when this crate models it, and
/// otherwise as much of its head as can be read without guessing.
fn render_type(ty: &Expr) -> String {
    match recognize(ty) {
        Some(clean) => clean.name(),
        None if matches!(strip_mdata(ty).kind(), ExprKind::Pi(..)) => {
            format!("({})", render_signature(ty))
        }
        None => render_head(ty),
    }
}

// ---------------------------------------------------------------------------
// Refusals
// ---------------------------------------------------------------------------

/// Why no carrier was granted.
///
/// Every variant renders a message that names the fix **with options**
/// (standing ruling v7/D3): *"we state the rules but if somebody doesn't follow
/// the rules, then provide feedback via the compiler on how to fix the
/// situation (provide options)."* "Unsupported" with no next step is a defect.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum CarrierRefused {
    /// This crate does not model the Clean type at all. The fail-closed
    /// default for everything outside the modeled fragment.
    UnmodeledCleanType {
        /// The head of the type expression, as far as it could be read.
        rendered: String,
    },
    /// The Clean type is a `Sort`. A proposition is observed, never produced.
    NotAValue {
        /// The Clean type.
        clean: String,
    },
    /// The requested carrier holds strictly fewer values than the Clean type.
    ///
    /// This is the **one rule** that covers both `Nat → u64` (unbounded into
    /// 64 bits) and `UInt64 → u32` (64 bits into 32). They are the same defect
    /// at different scales, and a carrier map with a special case for `Nat`
    /// would catch the famous one and ship the other.
    Narrowing {
        /// The Clean type.
        clean: String,
        /// Its extent.
        clean_extent: CarrierExtent,
        /// The requested Rust carrier.
        requested: String,
        /// The requested carrier's width, in bits.
        requested_bits: u32,
        /// The largest value the requested carrier holds, in decimal — `None`
        /// when the carrier's signedness makes "largest" not simply
        /// `2^bits - 1`, because a diagnostic that states a bound must state
        /// the true one.
        requested_max: Option<String>,
        /// The out-of-range value, in decimal, when one is known.
        value: Option<String>,
    },
    /// The requested carrier holds strictly more values than the Clean type.
    ///
    /// Refused, and not out of excess caution. A widening preserves every
    /// value, so it is injective — but it changes the **wrap modulus**, and
    /// emitted arithmetic follows the modulus: `UInt8.add 200 100 = 44` while
    /// `200u64 + 100u64 = 300`. A carrier faithful on values can still be
    /// unfaithful on operations, and the binary follows the operations.
    Widening {
        /// The Clean type.
        clean: String,
        /// Its width, in bits.
        clean_bits: u32,
        /// The requested Rust carrier.
        requested: String,
        /// Its width, in bits.
        requested_bits: u32,
        /// The carrier that IS exact.
        exact: String,
    },
    /// Same storage width, different reading of it (`UInt64` at `i64`, `Bool`
    /// at `u8`).
    Interpretation {
        /// The Clean type.
        clean: String,
        /// The requested Rust carrier.
        requested: String,
        /// The carrier that IS exact.
        exact: String,
    },
    /// One of the two types is bounded, but by a width this compilation has not
    /// resolved: Clean `USize` is `System.Platform.numBits`, Rust
    /// `usize`/`isize` is the target pointer width.
    TargetDependentWidth {
        /// The Clean type.
        clean: String,
        /// The requested Rust carrier.
        requested: String,
        /// Which of the two has the unresolved width, named so the user fixes
        /// the right side.
        unresolved: String,
    },
    /// A concrete value does not fit a width.
    OutOfRange {
        /// The value, in decimal.
        value: String,
        /// The width, in bits.
        width: u32,
        /// The largest value that width holds, in decimal.
        max: String,
    },
    /// A **position** of a function signature has no carrier, so the signature
    /// has none.
    ///
    /// The whole signature is refused, never the offending position alone.
    /// There is no partial credit: a call that carries three of its four values
    /// faithfully still emits a wrong binary for the fourth, and the three good
    /// ones make the wrong one harder to find, not less wrong.
    ///
    /// `cause` is the **unmodified** base-type refusal for that position. It is
    /// carried rather than summarized so the positional lane can never state a
    /// softer reason than the base lane states for the same type — the property
    /// `a_known_value_never_turns_a_refusal_into_a_grant` is inherited, not
    /// re-derived.
    SignatureComponent {
        /// Which position — a numbered argument, or the result.
        position: SignaturePosition,
        /// How many arguments the signature has, when that is known.
        arity: usize,
        /// The whole signature, rendered.
        signature: String,
        /// The base-type refusal for that position, verbatim.
        cause: Box<CarrierRefused>,
    },
    /// The type is a **dependent** `Pi`: an argument's *value* appears in a
    /// later type.
    ///
    /// Refused rather than erased. `(a : UInt64) -> Vec a` flattened to
    /// `UInt64 -> Vec` is a Rust signature that says something strictly weaker
    /// than the Clean type does, and the gap is exactly where a wrong binary
    /// lives. A dependency this crate cannot express is a dependency this crate
    /// does not carry.
    DependentFunctionType {
        /// Which argument's binder is used downstream, 0-based.
        binder_index: usize,
        /// The whole signature, rendered.
        signature: String,
    },
    /// The carrier map proposed a pairing that `trust-symbols`' independent
    /// re-check declined.
    ///
    /// Unreachable if this crate's table and `RepresentationObligation`'s
    /// arithmetic agree — which is the point of keeping them in two crates.
    /// If it ever fires, the table is wrong, and refusing is the correct
    /// response to that.
    ObligationDeclined(ObligationNotDischarged),
}

impl core::fmt::Display for CarrierRefused {
    #[allow(clippy::too_many_lines)]
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::UnmodeledCleanType { rendered } => write!(
                f,
                "no Rust carrier is modeled for the Clean type `{rendered}`, so it cannot \
                 cross into Rust — a type this compiler cannot represent exactly is never \
                 represented approximately.\n\
                 options: (1) use one of the modeled value types — `Bool`, `UInt8`, \
                 `UInt16`, `UInt32`, `UInt64`, or `BitVec 8/16/32/64`; (2) keep the \
                 declaration PROOF-only and cite it from `requires`/`ensures`, where no \
                 carrier is needed; (3) if this type should be carried, extend the \
                 carrier map in `trust-clean-carrier` — extending capability extends \
                 the CHECK, never trust (v7/D2)"
            ),
            Self::NotAValue { clean } => write!(
                f,
                "`{clean}` is a sort, not a type of values, so it has no Rust carrier: a \
                 proposition is OBSERVED from a proof context and never PRODUCED.\n\
                 options: (1) keep the declaration PROOF-only — this is the normal and \
                 correct outcome for a `Prop`; (2) if a decision procedure is wanted in \
                 Rust, declare a `Bool`-valued Clean function and relate it to the \
                 proposition with a `Decidable` instance, then carry the `Bool`"
            ),
            Self::Narrowing {
                clean,
                clean_extent,
                requested,
                requested_bits,
                requested_max,
                value,
            } => {
                let extent = match clean_extent {
                    CarrierExtent::Bits(b) => format!("{b} bits"),
                    CarrierExtent::Unbounded => "unbounded".to_string(),
                    CarrierExtent::TargetDependent => "target-dependent".to_string(),
                    CarrierExtent::NotAValue => "not a value type".to_string(),
                };
                let witnessed = match (value, requested_max) {
                    (Some(v), Some(max)) => format!(
                        " The value {v} is already outside `{requested}`, whose largest \
                         value is {max}."
                    ),
                    (Some(v), None) => {
                        format!(" The value {v} does not fit {requested_bits} bits.")
                    }
                    (None, _) => String::new(),
                };
                // Option 4 is CONDITIONAL (I6): the bignum fix is real for
                // `Nat`, wrong for `Int` (a ℕ runtime is not a ℤ carrier), and
                // inapplicable to a fixed-width narrowing (`UInt64 -> u32`),
                // whose fixes are options 1-3. A refusal must carry THE fix,
                // not A fix (v7/D3).
                let option4 = match (clean_extent, clean.as_str()) {
                    (CarrierExtent::Unbounded, "Nat") => {
                        "; (4) drop the fixed-width request and take `Nat`'s default \
                         carrier `trust_bignum::Nat`, which carries it exactly and \
                         unboundedly — `carrier_for` grants it with no source change"
                    }
                    (CarrierExtent::Unbounded, _) => {
                        "; (4) the bignum carrier `trust_bignum::Nat` carries `Nat` \
                         only — a natural-number runtime is not a carrier for this \
                         type, so declaring the value `Nat` (when it is genuinely a \
                         natural) is what unlocks it"
                    }
                    _ => "",
                };
                write!(
                    f,
                    "`{clean}` is {extent} and `{requested}` is {requested_bits} bits, so \
                     carrying `{clean}` as `{requested}` would NARROW it.{witnessed} This \
                     is refused rather than truncated: the kernel cannot catch it, because \
                     a `{clean} -> {requested}` extraction composed with a \
                     `{requested} -> {clean}` admission is definitionally equal WHILE the \
                     emitted code wraps.\n\
                     options: (1) declare the value at a fixed-width Clean type and take \
                     its exact carrier — `UInt8`/`UInt16`/`UInt32`/`UInt64` carry \
                     `u8`/`u16`/`u32`/`u64`, and a {requested_bits}-bit unsigned value is \
                     granted; (2) keep the declaration PROOF-only, where an unbounded \
                     type is free and costs nothing; (3) prove the embedding — an \
                     explicit range obligation `n < 2^{requested_bits}`, discharged, is \
                     what a narrowing carrier would need, and \
                     `UInt{requested_bits}.ofNatLT` is the Clean-side constructor that \
                     demands exactly that proof{option4}"
                )
            }
            Self::Widening { clean, clean_bits, requested, requested_bits, exact } => write!(
                f,
                "`{clean}` is {clean_bits} bits and `{requested}` is {requested_bits} \
                 bits. Every `{clean}` value fits, so this is not a truncation — but it \
                 is still not a carrier: the wrap modulus changes, and emitted arithmetic \
                 follows the modulus (`{clean}` arithmetic wraps at 2^{clean_bits}, \
                 `{requested}` arithmetic wraps at 2^{requested_bits}).\n\
                 options: (1) use `{exact}`, which is the exact carrier for `{clean}` and \
                 is granted; (2) declare the value at `UInt{requested_bits}` on the Clean \
                 side, so both sides agree by construction; (3) keep it PROOF-only"
            ),
            Self::Interpretation { clean, requested, exact } => write!(
                f,
                "`{requested}` is not a carrier for `{clean}`: the two read the same bits \
                 differently, so the values agree only by accident and the operations do \
                 not agree at all.\n\
                 options: (1) use `{exact}`, the exact carrier for `{clean}`; (2) change \
                 the Clean type to the one `{requested}` actually carries; (3) keep it \
                 PROOF-only"
            ),
            Self::TargetDependentWidth { clean, requested, unresolved } => write!(
                f,
                "the width of {unresolved} is not resolved in this compilation, so \
                 `{requested}` cannot be shown to carry `{clean}`. A pointer-width \
                 carrier that assumes 64 bits types a 32-bit value at 64 bits on a \
                 32-bit target — a representation-faithfulness violation that no kernel \
                 check can see.\n\
                 options: (1) declare the value at a concrete Clean width (`UInt32`, \
                 `UInt64`) and carry the matching `u32`/`u64`; (2) keep it PROOF-only; \
                 (3) resolve the target pointer width and re-ask — the carrier map has \
                 no way to consult it today, and refuses rather than guessing"
            ),
            Self::OutOfRange { value, width, max } => write!(
                f,
                "the value {value} does not fit {width} bits: `u{width}` holds at most \
                 {max}. It is refused, not truncated and not wrapped — a wrapped constant \
                 is a wrong binary that every downstream proof still accepts.\n\
                 options: (1) widen the Rust type until the value fits, and declare the \
                 Clean side at the matching fixed width; (2) if the value is genuinely \
                 unbounded, keep the declaration PROOF-only; (3) if it is bounded by a \
                 fact the compiler does not have, state that fact as a Clean hypothesis \
                 and discharge it — `UInt{width}.ofNatLT` takes exactly that proof"
            ),
            Self::SignatureComponent { position, arity, signature, cause } => {
                let where_ = position.describe();
                let plural = if *arity == 1 { "argument" } else { "arguments" };
                write!(
                    f,
                    "the Clean signature `{signature}` ({arity} {plural}) has no Rust \
                     carrier, because {where_} has none. The WHOLE signature is refused, \
                     not just that position: a carrier for a signature is total in every \
                     position or it does not exist, since a call that carries the other \
                     values faithfully still emits a wrong value for this one.\n\
                     options: (1) change {where_} to a carried type — the refusal for \
                     that position, quoted below, lists the specific fixes; (2) keep the \
                     whole declaration PROOF-only, where no position needs a carrier at \
                     all; (3) split it — the carryable part becomes a `def` Rust calls, \
                     and the part that needs {where_} stays PROOF-only and is cited from \
                     `requires`/`ensures`\n\
                     the refusal at {where_} is:\n{cause}"
                )
            }
            Self::DependentFunctionType { binder_index, signature } => write!(
                f,
                "`{signature}` is a DEPENDENT function type: the VALUE of argument \
                 {binder_index} appears in the type of a later position, so no Rust \
                 signature says the same thing. It is refused rather than erased — \
                 flattening the dependency away would type the Rust side at a strictly \
                 weaker statement than the Clean side proves, and that gap is where a \
                 wrong binary lives.\n\
                 options: (1) make the type non-dependent — take the dependent index as \
                 an ordinary carried value and state the relationship in \
                 `requires`/`ensures`, where it costs nothing and is still proved; \
                 (2) keep the declaration PROOF-only and cite it from a contract, where \
                 dependency is free; (3) monomorphize at the Clean side — a `def` \
                 specialized to a concrete index has a non-dependent type and is carried \
                 by this map today; (4) if this shape should be carried, extend \
                 `trust-clean-carrier` — extending capability extends the CHECK, never \
                 trust (v7/D2)"
            ),
            Self::ObligationDeclined(inner) => write!(
                f,
                "the carrier map proposed a pairing that the independent \
                 representation-faithfulness re-check declined: {inner}"
            ),
        }
    }
}

impl std::error::Error for CarrierRefused {}

impl From<ObligationNotDischarged> for CarrierRefused {
    fn from(value: ObligationNotDischarged) -> Self {
        Self::ObligationDeclined(value)
    }
}

// ---------------------------------------------------------------------------
// The decision
// ---------------------------------------------------------------------------

/// The default carrier for a Clean type: the exact one, or a refusal.
///
/// # Errors
///
/// [`CarrierRefused`] whenever no exact carrier exists — which includes every
/// unbounded type, every sort, and everything outside the modeled fragment.
pub fn carrier_for(clean: &Expr) -> Result<Carrier, CarrierRefused> {
    let clean_ty = recognize(clean)
        .ok_or_else(|| CarrierRefused::UnmodeledCleanType { rendered: render_head(clean) })?;
    let exact = clean_ty.exact_carrier().ok_or_else(|| no_default_carrier(clean_ty))?;
    grant(clean_ty, exact)
}

/// The carrier for a Clean type **at a requested Rust type**.
///
/// # Errors
///
/// [`CarrierRefused`] unless `requested` is exactly the carrier of `clean`.
pub fn carrier_at(clean: &Expr, requested: &Ty) -> Result<Carrier, CarrierRefused> {
    carrier_at_value(clean, None, requested)
}

/// The carrier for a Clean type at a requested Rust type, with a known literal
/// value so the refusal can name it.
///
/// **Never more permissive than [`carrier_at`].** The value is used only to
/// make a refusal more specific; it can never turn a refusal into a grant.
/// That is the whole difference between this and "assume in range": a `Nat`
/// whose current value happens to be 3 is still a `Nat`, and its arithmetic is
/// still unbounded.
///
/// # Errors
///
/// [`CarrierRefused`] under exactly the conditions [`carrier_at`] refuses.
pub fn carrier_at_value(
    clean: &Expr,
    value: Option<&BigNat>,
    requested: &Ty,
) -> Result<Carrier, CarrierRefused> {
    let clean_ty = recognize(clean)
        .ok_or_else(|| CarrierRefused::UnmodeledCleanType { rendered: render_head(clean) })?;
    let clean_extent = clean_ty.extent();
    let requested_name = rust_name(requested);

    // A sort is not a value, whatever was requested.
    if clean_extent == CarrierExtent::NotAValue {
        return Err(CarrierRefused::NotAValue { clean: clean_ty.name() });
    }

    let requested_extent = rust_extent(requested);

    // An unresolved width on EITHER side is refused before anything else, and
    // the refusal names which side, so the user fixes the right one.
    if clean_extent == CarrierExtent::TargetDependent
        || requested_extent == CarrierExtent::TargetDependent
    {
        let unresolved = if clean_extent == CarrierExtent::TargetDependent {
            format!("Clean `{}` (`System.Platform.numBits`)", clean_ty.name())
        } else {
            format!("Rust `{requested_name}` (the target pointer width)")
        };
        return Err(CarrierRefused::TargetDependentWidth {
            clean: clean_ty.name(),
            requested: requested_name,
            unresolved,
        });
    }

    // An unbounded Clean type narrows into ANY fixed width. `Nat -> u8` and
    // `Nat -> u64` are one rule, not a special case each. The ONE unbounded
    // grant (I6) is the exact carrier requested exactly: `Nat` at
    // `Ty::BignumNat`. A `Bits` request never reaches it — an approximation
    // at a requested width is refused before an exact default is offered.
    if clean_extent == CarrierExtent::Unbounded {
        if let Some(exact) = clean_ty.exact_carrier() {
            if requested == &exact {
                return grant(clean_ty, exact);
            }
        }
        return Err(match requested_extent {
            CarrierExtent::Bits(bits) => CarrierRefused::Narrowing {
                clean: clean_ty.name(),
                clean_extent,
                requested: requested_name,
                requested_bits: bits,
                requested_max: unsigned_max_for(requested),
                value: value.map(to_decimal),
            },
            _ => CarrierRefused::Interpretation {
                clean: clean_ty.name(),
                requested: requested_name,
                // Name the exact carrier when one exists (`Nat` has one now);
                // `Int` keeps the honest "none exists" byte-identically.
                exact: clean_ty.exact_carrier().map_or_else(
                    || "no Rust type carries an unbounded Clean type".to_string(),
                    |exact| rust_name(&exact),
                ),
            },
        });
    }

    let Some(exact) = clean_ty.exact_carrier() else {
        return Err(no_default_carrier(clean_ty));
    };
    if requested == &exact {
        return grant(clean_ty, exact);
    }

    // Same family, wrong width; or the same width read differently.
    let exact_name = rust_name(&exact);
    match (clean_extent, requested_extent) {
        (CarrierExtent::Bits(clean_bits), CarrierExtent::Bits(requested_bits)) => {
            if requested_bits < clean_bits {
                Err(CarrierRefused::Narrowing {
                    clean: clean_ty.name(),
                    clean_extent,
                    requested: requested_name,
                    requested_bits,
                    requested_max: unsigned_max_for(requested),
                    value: value.map(to_decimal),
                })
            } else if requested_bits > clean_bits {
                Err(CarrierRefused::Widening {
                    clean: clean_ty.name(),
                    clean_bits,
                    requested: requested_name,
                    requested_bits,
                    exact: exact_name,
                })
            } else {
                // Same width, different type: `UInt64` at `i64`. The bits agree
                // and the reading of them does not.
                Err(CarrierRefused::Interpretation {
                    clean: clean_ty.name(),
                    requested: requested_name,
                    exact: exact_name,
                })
            }
        }
        _ => Err(CarrierRefused::Interpretation {
            clean: clean_ty.name(),
            requested: requested_name,
            exact: exact_name,
        }),
    }
}

/// The refusal for a modeled Clean type that has no exact carrier at all.
fn no_default_carrier(clean_ty: CleanType) -> CarrierRefused {
    match clean_ty.extent() {
        CarrierExtent::NotAValue => CarrierRefused::NotAValue { clean: clean_ty.name() },
        CarrierExtent::TargetDependent => CarrierRefused::TargetDependentWidth {
            clean: clean_ty.name(),
            requested: "usize".to_string(),
            unresolved: format!("Clean `{}` (`System.Platform.numBits`)", clean_ty.name()),
        },
        CarrierExtent::Unbounded => CarrierRefused::Narrowing {
            clean: clean_ty.name(),
            clean_extent: CarrierExtent::Unbounded,
            requested: "u64".to_string(),
            requested_bits: 64,
            requested_max: Some(max_for_width(64)),
            value: None,
        },
        // A modeled fixed-width type with no Rust integer of that width, e.g.
        // `BitVec 7`.
        CarrierExtent::Bits(bits) => CarrierRefused::Interpretation {
            clean: clean_ty.name(),
            requested: format!("u{bits}"),
            exact: "no Rust integer of that width exists".to_string(),
        },
    }
}

/// State the obligation and let `trust-symbols` re-check it independently.
///
/// The `?` here is not decoration. This crate decides the pairing; the crate
/// that owns `CarrierEvidence` decides whether the pairing's own statement
/// entails faithfulness. If they ever disagree, no carrier is granted.
fn grant(clean_ty: CleanType, rust: Ty) -> Result<Carrier, CarrierRefused> {
    // The agreement KIND follows the carrier's extent, and the re-check
    // refuses a mismatch in either direction (`WrongAgreementKind`):
    //
    // * fixed width — `ExactOnEveryOperation`, the checkable same-wrap-modulus
    //   fact;
    // * unbounded (I6, `Ty::BignumNat` only) — `TrustedRuntimeAgreement`, a
    //   TCB claim, not a proof: the trust-bignum runtime implements Lean `Nat`
    //   semantics, evidenced by its hardware-referenced agreement tests, its
    //   hand-transcribed Lean-semantics pins, and the executed differential
    //   against clean-kernel's reduction lanes
    //   (crates/trust-bignum/tests/{u64_agreement,multi_limb,lean_semantics,
    //   kernel_differential}.rs — code deliberately unshared with the kernel).
    //   Disclosed in docs/TCB.md ("Bignum carrier runtime"). trust-symbols
    //   additionally pins the exact pairing, so this arm cannot be repurposed
    //   for a pairing no shipped runtime carries.
    let operations = match rust_extent(&rust) {
        CarrierExtent::Bits(_) => OperationAgreement::ExactOnEveryOperation,
        CarrierExtent::Unbounded => OperationAgreement::TrustedRuntimeAgreement,
        // Unreachable through this crate's table (no exact carrier is
        // target-dependent or a non-value); if it ever fires, `Unestablished`
        // discharges nothing — fail-closed.
        _ => OperationAgreement::Unestablished,
    };
    let witness = RepresentationObligation::new(
        clean_ty.name(),
        rust_name(&rust),
        clean_ty.extent(),
        rust_extent(&rust),
        operations,
    )
    .discharge()?;
    Ok(Carrier { clean: clean_ty, rust, witness })
}

fn render_head(e: &Expr) -> String {
    match strip_mdata(e).kind() {
        ExprKind::Const(name, _) => name.to_string(),
        ExprKind::App(head, _) => format!("{} ..", render_head(head)),
        ExprKind::Pi(..) => "a function type".to_string(),
        ExprKind::Lam(..) => "a lambda".to_string(),
        ExprKind::FVar(_) => "a free variable".to_string(),
        ExprKind::BVar(_) => "a bound variable".to_string(),
        other => format!("{other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Value representability
// ---------------------------------------------------------------------------

/// Does this Clean natural fit in `width` bits?
///
/// The refusal **names the value and the width**, in decimal, at arbitrary
/// precision — a diagnostic that says "value out of range" without saying which
/// value or which range is a defect (v7/D3).
///
/// # Errors
///
/// [`CarrierRefused::OutOfRange`] when `value >= 2^width`.
pub fn representable_at(value: &BigNat, width: u32) -> Result<(), CarrierRefused> {
    if fits_in_bits(value, width) {
        return Ok(());
    }
    Err(CarrierRefused::OutOfRange {
        value: to_decimal(value),
        width,
        max: max_for_width(width),
    })
}

/// `value < 2^bits`, computed on the limbs so it is exact at any precision.
fn fits_in_bits(value: &BigNat, bits: u32) -> bool {
    if bits == 0 {
        return value.is_zero();
    }
    let limbs = value.limbs();
    let full = (bits / 64) as usize;
    let rest = bits % 64;
    for (i, &limb) in limbs.iter().enumerate() {
        if i < full {
            continue;
        }
        if i == full && rest != 0 {
            if limb >> rest != 0 {
                return false;
            }
            continue;
        }
        if limb != 0 {
            return false;
        }
    }
    true
}

/// `2^bits - 1`, in decimal.
fn max_for_width(bits: u32) -> String {
    if bits == 0 {
        return "0".to_string();
    }
    let mut limbs = vec![u64::MAX; (bits as usize).div_ceil(64)];
    let rest = bits % 64;
    if rest != 0 {
        let last = limbs.len() - 1;
        limbs[last] = (1u64 << rest) - 1;
    }
    decimal_of_limbs(&limbs)
}

/// A `BigNat` in decimal, exactly, at any precision.
///
/// `BigNat` itself offers only `to_u64() -> Option<u64>`, which cannot render
/// the values this crate must refuse — `2^64` is precisely the case where it
/// returns `None`. A refusal that cannot name the offending value is not a
/// refusal a user can act on.
fn to_decimal(value: &BigNat) -> String {
    decimal_of_limbs(value.limbs())
}

fn decimal_of_limbs(limbs: &[u64]) -> String {
    // Long division of the limb vector by 10^19, most significant limb first.
    const CHUNK: u128 = 10_000_000_000_000_000_000;

    let mut limbs = limbs.to_vec();
    while limbs.len() > 1 && limbs.last() == Some(&0) {
        limbs.pop();
    }
    if limbs.iter().all(|&l| l == 0) {
        return "0".to_string();
    }

    let mut chunks: Vec<u64> = Vec::new();
    loop {
        let mut rem: u128 = 0;
        for limb in limbs.iter_mut().rev() {
            let cur = (rem << 64) | u128::from(*limb);
            *limb = u64::try_from(cur / CHUNK).unwrap_or(u64::MAX);
            rem = cur % CHUNK;
        }
        chunks.push(u64::try_from(rem).unwrap_or(u64::MAX));
        while limbs.len() > 1 && limbs.last() == Some(&0) {
            limbs.pop();
        }
        if limbs.len() == 1 && limbs[0] == 0 {
            break;
        }
    }

    let mut out = chunks.pop().expect("at least one chunk").to_string();
    while let Some(chunk) = chunks.pop() {
        out.push_str(&format!("{chunk:019}"));
    }
    out
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::Name;

    fn c(name: &str) -> Expr {
        Expr::const_(Name::from_string(name), vec![])
    }

    fn bitvec(w: u64) -> Expr {
        Expr::app(c("BitVec"), Expr::nat_lit(w))
    }

    // -- Recognition ------------------------------------------------------

    #[test]
    fn the_modeled_fragment_is_exactly_what_it_says() {
        assert_eq!(recognize(&c("Bool")), Some(CleanType::Bool));
        assert_eq!(recognize(&c("UInt8")), Some(CleanType::UInt(8)));
        assert_eq!(recognize(&c("UInt64")), Some(CleanType::UInt(64)));
        assert_eq!(recognize(&c("Nat")), Some(CleanType::Nat));
        assert_eq!(recognize(&c("Int")), Some(CleanType::Int));
        assert_eq!(recognize(&c("USize")), Some(CleanType::USize));
        assert_eq!(recognize(&bitvec(32)), Some(CleanType::BitVec(32)));
    }

    #[test]
    fn an_unmodeled_type_is_not_recognized_rather_than_guessed() {
        for name in ["Float", "String", "List", "Fin", "Option", "Int8", "UInt128", "Rat"] {
            assert_eq!(recognize(&c(name)), None, "`{name}` must not be recognized");
        }
        // A `BitVec` with a symbolic width is "some width", which is not a
        // width.
        assert_eq!(recognize(&Expr::app(c("BitVec"), c("w"))), None);
    }

    #[test]
    fn metadata_is_transparent_but_nothing_else_is() {
        let plain = c("UInt64");
        assert_eq!(recognize(&plain), Some(CleanType::UInt(64)));
        // A definition that REDUCES to UInt64 is not recognized: this map does
        // not reduce, on purpose.
        assert_eq!(recognize(&c("MyAlias")), None);
    }

    // -- The domain, decided ----------------------------------------------

    #[test]
    fn every_modeled_type_has_a_decided_extent() {
        assert_eq!(CleanType::Bool.extent(), CarrierExtent::Bits(1));
        assert_eq!(CleanType::UInt(16).extent(), CarrierExtent::Bits(16));
        assert_eq!(CleanType::Nat.extent(), CarrierExtent::Unbounded);
        assert_eq!(CleanType::Int.extent(), CarrierExtent::Unbounded);
        assert_eq!(CleanType::USize.extent(), CarrierExtent::TargetDependent);
        assert_eq!(CleanType::Sort.extent(), CarrierExtent::NotAValue);
    }

    #[test]
    fn a_prop_gets_no_carrier_because_it_is_not_a_value() {
        let err = carrier_at(&c("Prop"), &Ty::Bool).expect_err("a Prop has no carrier");
        assert!(matches!(err, CarrierRefused::NotAValue { .. }));
        assert!(err.to_string().contains("OBSERVED"), "{err}");
        assert!(carrier_for(&c("Prop")).is_err());
    }

    #[test]
    fn clean_int_at_rust_i64_is_refused() {
        // The pairing that sits in `tests/e6-fragment-probe/probes/f13_signed_i64.rs`
        // today, inert only because the clause lane refuses first: Clean `Int`
        // is unbounded, Rust `i64` is not.
        let err = carrier_at(&c("Int"), &Ty::Int { width: 64, signed: true })
            .expect_err("Clean `Int` is unbounded");
        assert!(matches!(err, CarrierRefused::TargetDependentWidth { .. } | CarrierRefused::Narrowing { .. }));
    }

    #[test]
    fn usize_is_refused_rather_than_assumed_to_be_64_bits() {
        let err = carrier_at(&c("USize"), &Ty::PtrSizedInt { signed: false })
            .expect_err("USize's width is not resolved here");
        assert!(matches!(err, CarrierRefused::TargetDependentWidth { .. }));
        let text = err.to_string();
        assert!(text.contains("32-bit target"), "the refusal must say why: {text}");
        assert!(text.contains("options:"), "{text}");

        // And the hazard in the other direction: a resolved Clean width must
        // not be carried by a pointer-width Rust type either.
        assert!(carrier_at(&c("UInt64"), &Ty::PtrSizedInt { signed: false }).is_err());
    }

    #[test]
    fn a_signed_carrier_is_refused_for_an_unsigned_clean_type() {
        let err = carrier_at(&c("UInt64"), &Ty::Int { width: 64, signed: true })
            .expect_err("i64 reads the top bit as a sign");
        assert!(matches!(err, CarrierRefused::Interpretation { .. }), "{err:?}");
        assert!(err.to_string().contains("u64"), "must name the exact carrier: {err}");
    }

    #[test]
    fn bool_at_a_byte_is_refused() {
        let err = carrier_at(&c("Bool"), &Ty::Int { width: 8, signed: false })
            .expect_err("bool is one bit of information, not eight");
        assert!(matches!(err, CarrierRefused::Widening { .. }), "{err:?}");
    }

    #[test]
    fn a_bitvec_of_a_non_machine_width_gets_no_carrier() {
        for w in [1_u64, 7, 24, 63, 65] {
            assert!(
                carrier_for(&bitvec(w)).is_err(),
                "BitVec {w} has no exact Rust carrier and must not get an approximate one"
            );
        }
        assert!(carrier_for(&bitvec(32)).is_ok());
    }

    // -- The value lane ---------------------------------------------------

    #[test]
    fn a_known_value_never_turns_a_refusal_into_a_grant() {
        // A `Nat` whose current value is 3 is still a `Nat`: its arithmetic is
        // unbounded, so the carrier is refused exactly as it is without a
        // value. This is the "assume in range" trap, refused.
        let three = BigNat::from_u64(3);
        let u64_ty = Ty::Int { width: 64, signed: false };
        assert!(carrier_at(&c("Nat"), &u64_ty).is_err());
        assert!(carrier_at_value(&c("Nat"), Some(&three), &u64_ty).is_err());
        // ... and the refusal is the same KIND, not a softer one.
        assert!(matches!(
            carrier_at_value(&c("Nat"), Some(&three), &u64_ty),
            Err(CarrierRefused::Narrowing { .. })
        ));
    }

    #[test]
    fn a_known_out_of_range_value_is_named_in_the_refusal() {
        let two_64 = BigNat::from_limbs(vec![0, 1]);
        let err =
            carrier_at_value(&c("Nat"), Some(&two_64), &Ty::Int { width: 64, signed: false })
                .expect_err("Nat -> u64 is refused");
        let text = err.to_string();
        assert!(text.contains("18446744073709551616"), "names the value: {text}");
        assert!(text.contains("18446744073709551615"), "names the width's max: {text}");
    }

    #[test]
    fn representability_is_exact_at_the_boundary() {
        for width in [8_u32, 16, 32, 64] {
            let max = BigNat::from_limbs(max_limbs(width));
            assert!(representable_at(&max, width).is_ok(), "2^{width}-1 fits {width} bits");
            let over = BigNat::from_limbs(over_limbs(width));
            assert!(representable_at(&over, width).is_err(), "2^{width} does not fit");
        }
        assert!(representable_at(&BigNat::from_u64(0), 0).is_ok());
        assert!(representable_at(&BigNat::from_u64(1), 0).is_err());
    }

    fn max_limbs(width: u32) -> Vec<u64> {
        let mut limbs = vec![u64::MAX; (width as usize).div_ceil(64)];
        let rest = width % 64;
        if rest != 0 {
            let last = limbs.len() - 1;
            limbs[last] = (1u64 << rest) - 1;
        }
        limbs
    }

    fn over_limbs(width: u32) -> Vec<u64> {
        let mut limbs = vec![0u64; (width as usize) / 64 + 1];
        let last = limbs.len() - 1;
        limbs[last] = 1u64 << (width % 64);
        limbs
    }

    #[test]
    fn decimal_rendering_is_exact_past_u64() {
        assert_eq!(to_decimal(&BigNat::from_u64(0)), "0");
        assert_eq!(to_decimal(&BigNat::from_u64(1)), "1");
        assert_eq!(to_decimal(&BigNat::from_u64(u64::MAX)), "18446744073709551615");
        assert_eq!(to_decimal(&BigNat::from_limbs(vec![0, 1])), "18446744073709551616");
        // 2^128
        assert_eq!(
            to_decimal(&BigNat::from_limbs(vec![0, 0, 1])),
            "340282366920938463463374607431768211456"
        );
        assert_eq!(max_for_width(64), "18446744073709551615");
        assert_eq!(max_for_width(8), "255");
        assert_eq!(max_for_width(32), "4294967295");
    }

    // -- Signatures -------------------------------------------------------

    #[test]
    fn a_signature_is_rendered_the_way_a_user_writes_it() {
        assert_eq!(render_signature(&c("UInt64")), "UInt64");
        assert_eq!(render_signature(&Expr::arrow(c("UInt64"), c("Bool"))), "UInt64 -> Bool");
        assert_eq!(
            render_signature(&Expr::arrow(c("Nat"), Expr::arrow(c("Bool"), bitvec(32)))),
            "Nat -> Bool -> BitVec 32"
        );
        // A higher-order argument is parenthesized, so the refusal points at
        // the right thing.
        assert_eq!(
            render_signature(&Expr::arrow(Expr::arrow(c("UInt64"), c("Bool")), c("UInt64"))),
            "(UInt64 -> Bool) -> UInt64"
        );
    }

    #[test]
    fn the_signature_lane_agrees_with_the_base_lane_on_every_base_type() {
        // Not a new decision procedure: on a non-`Pi`, `carrier_signature_for`
        // IS `carrier_for`, and it must be for the I4 properties to be
        // inherited rather than re-derived.
        for name in [
            "Bool", "UInt8", "UInt16", "UInt32", "UInt64", "USize", "Nat", "Int", "Prop",
            "MyAlias", "Float",
        ] {
            let base = carrier_for(&c(name));
            let sig = carrier_signature_for(&c(name));
            match (base, sig) {
                (Ok(base), Ok(sig)) => {
                    assert_eq!(sig.arity(), 0, "`{name}` is not a function type");
                    assert_eq!(sig.result(), &base, "`{name}` must get the SAME carrier");
                }
                (Err(_), Err(_)) => {}
                (base, sig) => {
                    panic!("`{name}`: the two lanes disagree: base={base:?} signature={sig:?}")
                }
            }
        }
    }

    #[test]
    fn the_positional_refusal_carries_the_base_refusal_unmodified() {
        // Re-pinned on `Int` (I6 flipped `Nat` to a grant — asserted below):
        // the property under test is the positional lane's refusal fidelity,
        // and `Int` still has no carrier.
        let base = carrier_for(&c("Int")).expect_err("Int has no carrier");
        let err = carrier_signature_for(&Expr::arrow(c("Int"), c("UInt64")))
            .expect_err("nor does it in argument position");
        let CarrierRefused::SignatureComponent { cause, signature, arity, position } = err else {
            panic!("expected a positional refusal");
        };
        assert_eq!(*cause, base, "the reason must not soften on the way through");
        assert_eq!(signature, "Int -> UInt64");
        assert_eq!(arity, 1);
        assert_eq!(position, SignaturePosition::Argument(0));
    }

    /// The I6 ratchet flip, positive: `Nat`'s default carrier exists and is
    /// the bignum runtime — granted by the SAME decision procedure, witnessed
    /// through the same independent re-check as every fixed-width grant.
    #[test]
    fn nat_has_the_bignum_default_carrier() {
        use trust_symbols::CarrierWidth;

        let carrier = carrier_for(&c("Nat")).expect("I6: Nat carries at trust_bignum::Nat");
        assert_eq!(carrier.rust(), &Ty::BignumNat);
        assert_eq!(carrier.witness().clean_type(), "Nat");
        assert_eq!(carrier.witness().rust_carrier(), "trust_bignum::Nat");
        assert_eq!(carrier.witness().width(), CarrierWidth::UnboundedExact);
        assert_eq!(carrier.evidence(), CarrierEvidence::Total);

        // ... and the signature lane inherits it positionally: `Nat -> UInt64`
        // now carries in BOTH positions.
        let sig = carrier_signature_for(&Expr::arrow(c("Nat"), c("UInt64")))
            .expect("Nat -> UInt64 is carried positionally after I6");
        assert_eq!(sig.arity(), 1);
        assert_eq!(sig.arguments()[0].rust(), &Ty::BignumNat);

        // `Int` did NOT ride along, in either lane.
        assert!(carrier_for(&c("Int")).is_err(), "a Nat runtime is not an Int carrier");
        assert!(carrier_signature_for(&Expr::arrow(c("Int"), c("UInt64"))).is_err());
    }

    // -- The seam ---------------------------------------------------------

    #[test]
    fn a_granted_carrier_is_the_only_thing_that_records_total() {
        use trust_symbols::{Producer, SegmentPath, Sort, SymbolHeader};

        let carrier = carrier_for(&c("UInt64")).expect("UInt64 has an exact carrier");
        assert_eq!(carrier.evidence(), CarrierEvidence::Total);
        assert_eq!(carrier.witness().clean_type(), "UInt64");
        assert_eq!(carrier.witness().rust_carrier(), "u64");

        let header = SymbolHeader::new(
            SegmentPath::parse_rust("crate::f").expect("valid path"),
            Sort::Term,
            Producer::Clean,
        );
        let recorded = carrier.record_on(header);
        assert_eq!(recorded.carrier(), CarrierEvidence::Total);
        assert_eq!(
            recorded.carrier_witness().map(CarrierWitness::width),
            Some(trust_symbols::CarrierWidth::Bits(64))
        );
    }
}
